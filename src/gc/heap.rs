use std::any::{Any, TypeId};
use std::cell::{Cell, RefCell};
use std::mem::{self, needs_drop};
use std::ptr::{self, NonNull};
use std::slice;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use super::budget::Budget;
use super::host::Hosts;
use super::layout::{
    self, CARD, CARDS, FORWARDED, GRANULE, Header, InlineVTable, LINE, LINES, MAX_PAGES, MAX_SMALL, PAGE, PAGE_SHIFT,
    OFFSET_MASK, REGION, STAMP_SHIFT, STAMPS, SizedVTable, VTable, WORDS,
};
use super::region::{self, Region};
use super::root::{ROOT_COST, RootEntry};
use super::stack::StackRecord;
use super::table::Table;
use super::trace::Mode;
use super::{Inline, OutOfMemory, Phase, Plain, Trace, Tracer};

const MIN_THRESHOLD: usize = 64 * 1024;
const SWEEP_COST: usize = PAGE / 8;
const GRAY_CAPACITY: usize = 1024;
const TYPES: usize = 1 << 16;
/// The gray stack has a fixed size, charged when the arena is made.
pub(crate) const GRAY_BYTES: usize = GRAY_CAPACITY * size_of::<u32>();
/// What each page's metadata is charged.
pub(crate) const META: usize = size_of::<Page>();

static NEXT_ID: AtomicU64 = AtomicU64::new(1);

// All-zero is `Free`, so the page table can start out as zeroed memory.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u32)]
enum Kind {
    Free,
    /// Small objects, bump-allocated through free lines.
    Lines,
    /// The first page of a run holding one object.
    Large(u32),
    Tail(u32),
}

/// Holds objects allocated since the last collection.
const YOUNG: u8 = 1;
/// Already swept in this major cycle. Only read while sweeping.
const SWEPT: u8 = 2;
/// Being compacted in this major cycle.
const CANDIDATE: u8 = 4;
/// Holds marked objects that didn't fit on the gray stack and still need tracing.
const OVERFLOW: u8 = 8;
/// Holds an ephemeron whose key wasn't marked when it was traced.
const PENDING: u8 = 16;

const LINE_WORDS: usize = LINES / 64;

/// A bitmap in page metadata. Cells let the collector update a page while it traces
/// objects on it.
struct Bits<const N: usize>([Cell<u64>; N]);

impl<const N: usize> Bits<N> {
    fn get(&self, i: usize) -> bool {
        self.0[i / 64].get() >> (i % 64) & 1 != 0
    }

    fn set(&self, i: usize) {
        let word = &self.0[i / 64];
        word.set(word.get() | 1 << (i % 64));
    }

    fn clear(&self, i: usize) {
        let word = &self.0[i / 64];
        word.set(word.get() & !(1 << (i % 64)));
    }

    fn set_range(&self, from: usize, to: usize) {
        for i in from..to {
            self.set(i);
        }
    }

    fn clear_range(&self, from: usize, to: usize) {
        for i in from..to {
            self.clear(i);
        }
    }

    fn load(&self) -> [u64; N] {
        std::array::from_fn(|w| self.0[w].get())
    }

    fn store(&self, bits: [u64; N]) {
        for (word, bits) in self.0.iter().zip(bits) {
            word.set(bits);
        }
    }

    fn count(&self) -> usize {
        self.0.iter().map(|w| w.get().count_ones() as usize).sum()
    }

    fn is_empty(&self) -> bool {
        self.0.iter().all(|w| w.get() == 0)
    }

    fn is_full(&self) -> bool {
        self.0.iter().all(|w| w.get() == !0)
    }

    /// The highest set bit at or below `i`.
    fn prev(&self, i: usize) -> Option<usize> {
        let mut w = i / 64;
        let mut word = self.0[w].get() & (u64::MAX >> (63 - i % 64));
        loop {
            if word != 0 {
                return Some(w * 64 + 63 - word.leading_zeros() as usize);
            }
            w = w.checked_sub(1)?;
            word = self.0[w].get();
        }
    }
}

fn and<const N: usize>(a: [u64; N], b: [u64; N]) -> [u64; N] {
    std::array::from_fn(|w| a[w] & b[w])
}

/// Visits each set bit of `bits`.
fn each_bit(bits: &[u64], mut f: impl FnMut(usize)) {
    for (w, &word) in bits.iter().enumerate() {
        let mut word = word;
        while word != 0 {
            f(w * 64 + word.trailing_zeros() as usize);
            word &= word - 1;
        }
    }
}

/// Trusted per-page metadata. Lives outside the region, so heap corruption can't reach it.
struct Page {
    kind: Cell<Kind>,
    flags: Cell<u8>,
    /// Dirty 512-byte cards: slots written since the last collection.
    cards: Cell<u32>,
    /// An object starts at each set granule.
    start: Bits<WORDS>,
    mark: Bits<WORDS>,
    /// Lines the allocator must not hand out.
    used: Bits<LINE_WORDS>,
    /// Lines touched by marked objects.
    marked_lines: Bits<LINE_WORDS>,
}

impl Page {
    fn reset(&self) {
        self.kind.set(Kind::Free);
        self.flags.set(0);
        self.cards.set(0);
        self.start.store([0; WORDS]);
        self.mark.store([0; WORDS]);
        self.used.store([0; LINE_WORDS]);
        self.marked_lines.store([0; LINE_WORDS]);
    }

    fn has(&self, flag: u8) -> bool {
        self.flags.get() & flag != 0
    }

    fn add(&self, flag: u8) {
        self.flags.set(self.flags.get() | flag);
    }

    fn remove(&self, flag: u8) -> bool {
        let had = self.has(flag);
        self.flags.set(self.flags.get() & !flag);
        had
    }

    fn dirty(&self, in_page: usize) {
        self.cards.set(self.cards.get() | 1 << (in_page / CARD));
    }

    fn live(&self) -> [u64; WORDS] {
        and(self.start.load(), self.mark.load())
    }

    /// For a page run, the page holding the header.
    fn head(&self, page: usize) -> usize {
        match self.kind.get() {
            Kind::Tail(head) => head as usize,
            _ => page,
        }
    }
}

fn page_start(page: usize) -> usize {
    (page + 1) << PAGE_SHIFT
}

fn granule_offset(page: usize, granule: usize) -> u32 {
    (page_start(page) + granule * GRANULE) as u32
}

/// A validated object: its offset, page and granule, and how many bytes it may span.
#[derive(Clone, Copy)]
struct Obj {
    offset: u32,
    page: usize,
    granule: usize,
    room: usize,
}

pub(crate) struct Heap {
    pub(crate) budget: Budget,
    pub(crate) id: u64,
    pub(crate) base: NonNull<u8>,
    region: Region,
    // Index `i` is region page `i + 1`; page 0 is never used, so offset 0 is null. The table
    // has room for every page from the start, so it never moves; `page_count` are in use.
    pages: Box<[Page; MAX_PAGES]>,
    page_count: Cell<usize>,
    /// The current free-line run: next free byte and end, as region offsets.
    bump: Cell<(usize, usize)>,
    /// A separate run, on a fresh page, for objects bigger than a line that don't fit `bump`.
    overflow: Cell<(usize, usize)>,
    /// Where the allocator next looks for a page with free lines.
    scan: Cell<usize>,
    // Indexed by a header's `u16` type, so every lookup is in bounds.
    types: Box<[Cell<Option<&'static VTable>>; TYPES]>,
    type_count: Cell<usize>,
    stamp: Cell<u16>,
    type_cache: [Cell<(usize, u16)>; 64],
    gray: Box<[Cell<u32>; GRAY_CAPACITY]>,
    gray_len: Cell<usize>,
    gray_limit: Cell<usize>,
    overflowed: Cell<bool>,
    pub(crate) roots: RefCell<Table<Rc<dyn RootEntry>>>,
    pub(crate) stacks: RefCell<Table<Rc<StackRecord>>>,
    pub(crate) hosts: Hosts,
    phase: Cell<Phase>,
    cursor: Cell<usize>,
    evacuating: Cell<bool>,
    committed: Cell<usize>,
    free_pages: Cell<usize>,
    objects: Cell<usize>,
    marks: Cell<usize>,
    allocated: Cell<usize>,
    young: Cell<usize>,
    threshold: Cell<usize>,
    collections: Cell<u64>,
    minors: Cell<u64>,
    corrupted: Cell<bool>,
    pub(crate) stress: Cell<Option<usize>>,
    pub(crate) evacuate_all: Cell<bool>,
    #[cfg(test)]
    used_pages: RefCell<Vec<bool>>,
}

impl Heap {
    pub(crate) fn new(limit: usize) -> Option<Self> {
        let region = Region::new()?;
        let limit = limit.min(REGION);
        let budget = Budget::new(limit);
        budget.charge(GRAY_BYTES).ok()?;
        Some(Self {
            budget,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            base: region.base(),
            region,
            pages: zeroed(),
            page_count: Cell::new(0),
            bump: Cell::new((0, 0)),
            overflow: Cell::new((0, 0)),
            scan: Cell::new(0),
            types: zeroed(),
            type_count: Cell::new(0),
            stamp: Cell::new(0),
            type_cache: [const { Cell::new((0, 0)) }; 64],
            gray: Box::new([const { Cell::new(0) }; GRAY_CAPACITY]),
            gray_len: Cell::new(0),
            gray_limit: Cell::new(GRAY_CAPACITY),
            overflowed: Cell::new(false),
            roots: RefCell::new(Table::new()),
            stacks: RefCell::new(Table::new()),
            hosts: Hosts::new(),
            phase: Cell::new(Phase::Idle),
            cursor: Cell::new(0),
            evacuating: Cell::new(false),
            committed: Cell::new(0),
            free_pages: Cell::new(0),
            objects: Cell::new(0),
            marks: Cell::new(0),
            allocated: Cell::new(0),
            young: Cell::new(0),
            threshold: Cell::new(MIN_THRESHOLD.min(limit / 2)),
            collections: Cell::new(0),
            minors: Cell::new(0),
            corrupted: Cell::new(false),
            stress: Cell::new(None),
            evacuate_all: Cell::new(false),
            #[cfg(test)]
            used_pages: RefCell::new(vec![false; layout::RESERVE / PAGE]),
        })
    }

    pub(crate) fn objects(&self) -> usize {
        self.objects.get()
    }

    /// Bytes in lines and page runs the allocator can't hand out.
    pub(crate) fn live(&self) -> usize {
        self.pages()
            .iter()
            .map(|p| match p.kind.get() {
                Kind::Lines => p.used.count() * LINE,
                Kind::Large(n) => n as usize * PAGE,
                _ => 0,
            })
            .sum()
    }

    pub(crate) fn committed(&self) -> usize {
        self.committed.get()
    }

    pub(crate) fn threshold(&self) -> usize {
        self.threshold.get()
    }

    pub(crate) fn collections(&self) -> u64 {
        self.collections.get()
    }

    pub(crate) fn minor_collections(&self) -> u64 {
        self.minors.get()
    }

    pub(crate) fn young(&self) -> usize {
        self.young.get()
    }

    /// How much young allocation triggers a minor collection.
    pub(crate) fn nursery(&self) -> usize {
        (self.budget.limit() / 8).clamp(64 * 1024, 4 << 20)
    }

    pub(crate) fn phase(&self) -> Phase {
        self.phase.get()
    }

    #[inline]
    pub(crate) fn is_marking(&self) -> bool {
        self.phase.get() == Phase::Marking
    }

    pub(crate) fn corrupted(&self) -> bool {
        self.corrupted.get()
    }

    pub(crate) fn corrupt(&self) {
        self.corrupted.set(true);
    }

    pub(crate) fn take_allocated(&self) -> usize {
        self.allocated.replace(0)
    }

    fn pages(&self) -> &[Page] {
        &self.pages[..self.page_count.get()]
    }

    /// Any page of the table; callers keep to `page_count`.
    fn page(&self, page: usize) -> &Page {
        &self.pages[page]
    }

    fn page_count(&self) -> usize {
        self.page_count.get()
    }

    fn header_ptr(&self, offset: u32) -> *mut Header {
        self.base.as_ptr().wrapping_add(offset as usize).cast()
    }

    fn header(&self, obj: Obj) -> Header {
        self.header_at(obj.offset)
    }

    /// The header at `offset`, which only means something if an object starts there. Masked,
    /// the offset is aligned and below `REGION`, so the read stays inside the reservation, and
    /// every bit pattern is a valid `Header`.
    #[inline]
    fn header_at(&self, offset: u32) -> Header {
        unsafe { self.header_ptr(offset & OFFSET_MASK).read() }
    }

    pub(crate) fn in_region(&self, addr: usize) -> bool {
        addr.wrapping_sub(self.base.as_ptr().addr()) < REGION
    }

    /// The page holding region offset `offset`.
    fn page_of(&self, offset: usize) -> Option<usize> {
        let page = (offset >> PAGE_SHIFT).checked_sub(1)?;
        (page < self.page_count()).then_some(page)
    }

    fn type_index(&self, vtable: &'static VTable) -> Result<u16, OutOfMemory> {
        let addr = (vtable as *const VTable).addr();
        let cached = &self.type_cache[(addr >> 4) % 64];
        let (a, index) = cached.get();
        if a == addr {
            return Ok(index);
        }
        let count = self.type_count.get();
        let same = |t: &'static VTable| ptr::eq(t, vtable) || (t.type_id)() == (vtable.type_id)();
        let known = self.types[..count].iter().position(|t| t.get().is_some_and(same));
        let index = match known {
            Some(index) => index,
            None if count < TYPES => {
                self.types[count].set(Some(vtable));
                self.type_count.set(count + 1);
                count
            }
            None => return Err(self.budget.fail()),
        };
        cached.set((addr, index as u16));
        Ok(index as u16)
    }

    fn vtable(&self, ty: u16) -> Option<&'static VTable> {
        self.types[ty as usize].get()
    }

    /// Whether the object at `offset` is of the type `id` names. Offsets come from references
    /// the collector keeps valid, so only the header is checked.
    #[inline]
    pub(crate) fn has_type(&self, offset: u32, check: u32, id: fn() -> TypeId) -> bool {
        // Functions returning different ids can't be merged, so equal pointers mean equal
        // types. Unequal ones may still be copies of the same function.
        let vtable = self.vtable(check as u16);
        vtable.is_some_and(|vt| ptr::fn_addr_eq(vt.type_id, id) || (vt.type_id)() == id()) && self.checks_out(offset, check)
    }

    #[inline]
    pub(crate) fn has_type_index(&self, offset: u32, check: u32, ty: u16) -> bool {
        check as u16 == ty && self.checks_out(offset, check)
    }

    /// The items of the object at `offset`, if it's a `T`, for the collector.
    ///
    /// # Safety
    /// Nothing else may reference the object's memory while the slice is in use.
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn items_mut<T: Inline>(&self, offset: u32) -> Option<&mut [T::Item]> {
        let obj = self.object_at(offset)?;
        let (vtable, _) = self.size_of(obj)?;
        let id: fn() -> TypeId = layout::type_id::<T>;
        if !(ptr::fn_addr_eq(vtable.type_id, id) || (vtable.type_id)() == id()) {
            return None;
        }
        // The vtable is `T`'s, and `size_of` checked that `len` items fit in the object.
        unsafe {
            let header = self.header_ptr(offset);
            let len = ((*header).len as usize).min(layout::max_items::<T>());
            let items = layout::inline_items::<T>(layout::value_ptr::<T>(header));
            Some(slice::from_raw_parts_mut(items, len))
        }
    }

    /// The check bits for a reference to the object at `offset`.
    pub(crate) fn check_at(&self, offset: u32) -> u32 {
        layout::check_bits(self.header_at(offset))
    }

    /// Whether a reference's check bits match its object's header. A mismatch means the
    /// reference outlived its object or was damaged, and marks the arena corrupted. Stamps are
    /// never zero, so zeroed memory never checks out.
    #[inline]
    pub(crate) fn checks_out(&self, offset: u32, check: u32) -> bool {
        let ok = check >> 16 != 0 && self.check_at(offset) == check;
        if !ok {
            self.corrupt();
        }
        ok
    }

    /// The next allocation stamp, never zero.
    fn stamp(&self) -> u16 {
        let stamp = self.stamp.get() % (STAMPS - 1) + 1;
        self.stamp.set(stamp);
        stamp << STAMP_SHIFT
    }

    pub(crate) fn sized_type<T: Trace>(&self) -> Result<u16, OutOfMemory> {
        const { assert!(!T::INLINE, "inline types need an inline type tag") };
        self.type_index(&SizedVTable::<T>::VTABLE)
    }

    pub(crate) fn inline_type<T: Inline>(&self) -> Result<u16, OutOfMemory> {
        const { assert!(T::INLINE, "type implements Inline but INLINE is false") };
        self.type_index(&InlineVTable::<T>::VTABLE)
    }

    /// The allocated object whose header is exactly at `offset`.
    fn object_at(&self, offset: u32) -> Option<Obj> {
        let offset = offset as usize;
        if !offset.is_multiple_of(GRANULE) {
            return None;
        }
        let page = self.page_of(offset)?;
        let p = self.page(page);
        let in_page = offset % PAGE;
        let room = match p.kind.get() {
            Kind::Lines => PAGE - in_page,
            Kind::Large(n) if in_page == 0 => n as usize * PAGE,
            _ => return None,
        };
        let granule = in_page / GRANULE;
        p.start.get(granule).then_some(Obj { offset: offset as u32, page, granule, room })
    }

    /// The object's size, checked against its type and the space it can occupy.
    fn size_of(&self, obj: Obj) -> Option<(&'static VTable, usize)> {
        let header = self.header(obj);
        let vtable = self.vtable(header.ty)?;
        let size = (vtable.size)(header)?;
        (size <= obj.room).then_some((vtable, size))
    }

    fn is_marked(&self, obj: Obj) -> bool {
        self.page(obj.page).mark.get(obj.granule)
    }

    /// Whether `offset` is a marked object. A bad offset marks the arena corrupted and
    /// counts as live, so nothing is cleared because of it.
    pub(crate) fn is_live(&self, offset: u32) -> bool {
        match self.object_at(offset) {
            Some(obj) => self.is_marked(obj),
            None => {
                self.corrupt();
                true
            }
        }
    }

    fn mark_object(&self, obj: Obj, size: usize) {
        let p = self.page(obj.page);
        p.mark.set(obj.granule);
        if p.kind.get() == Kind::Lines {
            let at = obj.granule * GRANULE;
            p.marked_lines.set_range(at / LINE, (at + size).div_ceil(LINE));
        }
        self.marks.set(self.marks.get() + 1);
    }

    fn push_gray(&self, offset: u32, page: usize) {
        let len = self.gray_len.get();
        if len < self.gray_limit.get() {
            self.gray[len].set(offset);
            self.gray_len.set(len + 1);
        } else {
            self.page(page).add(OVERFLOW);
            self.overflowed.set(true);
        }
    }

    fn pop_gray(&self) -> Option<u32> {
        let len = self.gray_len.get().checked_sub(1)?;
        self.gray_len.set(len);
        Some(self.gray[len].get())
    }

    pub(crate) fn shade(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return self.corrupt() };
        if self.is_marked(obj) {
            return;
        }
        let Some((vtable, size)) = self.size_of(obj) else { return self.corrupt() };
        self.mark_object(obj, size);
        if vtable.needs_trace {
            self.push_gray(offset, obj.page);
        }
    }

    /// Remembers a slot pointing into a page being compacted, so it can be fixed up.
    pub(crate) fn note_slot(&self, target: u32, slot: usize) {
        if !self.evacuating.get() || !self.in_region(slot) {
            return;
        }
        if self.page_of(target as usize).is_some_and(|p| self.page(p).has(CANDIDATE)) {
            self.dirty(slot - self.base.as_ptr().addr());
        }
    }

    /// Flags the page holding the object with an ephemeron whose key isn't marked yet.
    pub(crate) fn pending(&self, slot: usize) {
        if let Some(page) = self.page_of(slot.wrapping_sub(self.base.as_ptr().addr())) {
            self.page(self.page(page).head(page)).add(PENDING);
        }
    }

    /// The new offset of an object compaction moved.
    pub(crate) fn forwarded(&self, offset: u32) -> Option<u32> {
        let Some(obj) = self.object_at(offset) else {
            self.corrupt();
            return None;
        };
        if !self.is_forwarded(obj) {
            return None;
        }
        let new = self.header(obj).len;
        if self.object_at(new).is_none() {
            self.corrupt();
            return None;
        }
        Some(new)
    }

    fn is_forwarded(&self, obj: Obj) -> bool {
        self.evacuating.get() && self.header(obj).flags & FORWARDED != 0
    }

    /// Whether the object starting at `offset`, which must have its start bit set, moved.
    fn moved(&self, offset: u32) -> bool {
        self.object_at(offset).is_some_and(|obj| self.is_forwarded(obj))
    }

    fn dirty(&self, offset: usize) {
        if let Some(page) = self.page_of(offset) {
            self.page(page).dirty(offset % PAGE);
        }
    }

    /// Whether the object holding the byte at `offset` is marked.
    fn owner_marked(&self, offset: usize, page: usize) -> bool {
        let p = self.page(page);
        match p.kind.get() {
            Kind::Lines => p.start.prev((offset % PAGE) / GRANULE).is_some_and(|g| p.mark.get(g)),
            Kind::Large(_) | Kind::Tail(_) => self.pages().get(p.head(page)).is_some_and(|h| h.mark.get(0)),
            Kind::Free => false,
        }
    }

    #[inline]
    pub(crate) fn write_barrier(&self, slot: usize, shade: impl FnOnce(&mut Tracer<'_>)) {
        if self.in_region(slot) {
            self.barrier_slow(slot - self.base.as_ptr().addr(), shade);
        }
    }

    #[inline(never)]
    fn barrier_slow(&self, offset: usize, shade: impl FnOnce(&mut Tracer<'_>)) {
        let Some(page) = self.page_of(offset) else { return };
        self.page(page).dirty(offset % PAGE);
        if self.is_marking() && self.owner_marked(offset, page) {
            let guard = CorruptOnUnwind(self);
            shade(&mut Tracer::new(self, Mode::Barrier));
            mem::forget(guard);
        }
    }

    /// Dirties the cards under `len` bytes at `addr`, so whatever was stored there gets
    /// traced by the next collection, like a write barrier for each slot.
    pub(crate) fn dirty_range(&self, addr: usize, len: usize) {
        if len == 0 || !self.in_region(addr) {
            return;
        }
        let mut at = addr - self.base.as_ptr().addr();
        let end = at + len;
        while at < end {
            let Some(page) = self.page_of(at) else { return };
            let to = end.min(page_start(page) + PAGE);
            let (first, last) = ((at % PAGE) / CARD, ((to - 1) % PAGE) / CARD);
            let p = self.page(page);
            p.cards.set(p.cards.get() | ((u64::MAX >> (63 - last)) & (u64::MAX << first)) as u32);
            at = to;
        }
    }

    /// Has the object traced again before the next collection finishes. While marking, a
    /// marked object goes back on the gray stack, so incremental slices do the work.
    pub(crate) fn retrace(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return };
        let Some((vtable, size)) = self.size_of(obj) else { return };
        self.dirty_range(self.base.as_ptr().addr() + offset as usize, size);
        if self.is_marking() && self.is_marked(obj) && vtable.needs_trace {
            self.push_gray(offset, obj.page);
        }
    }

    /// The barrier for a range of slots in one object: like a write barrier for each slot.
    pub(crate) fn barrier_range(&self, addr: usize, len: usize, shade: impl FnOnce(&mut Tracer<'_>)) {
        if len == 0 || !self.in_region(addr) {
            return;
        }
        self.dirty_range(addr, len);
        let offset = addr - self.base.as_ptr().addr();
        if self.is_marking() && self.page_of(offset).is_some_and(|page| self.owner_marked(offset, page)) {
            let guard = CorruptOnUnwind(self);
            shade(&mut Tracer::new(self, Mode::Barrier));
            mem::forget(guard);
        }
    }

    fn reset_allocators(&self) {
        self.retire(self.bump.replace((0, 0)));
        self.retire(self.overflow.replace((0, 0)));
        self.scan.set(0);
    }

    /// Frees the whole lines an allocation run didn't reach. Runs claim all their lines up
    /// front, so otherwise those lines would stay used until the page is swept.
    fn retire(&self, (next, end): (usize, usize)) {
        let first = next.next_multiple_of(LINE);
        if first >= end {
            return;
        }
        let Some(page) = self.page_of(first) else { return };
        let start = page_start(page);
        self.page(page).used.clear_range((first - start) / LINE, (end - start) / LINE);
    }

    /// Claims the first run of free lines at or after `from` in `page`.
    fn claim_hole(&self, page: usize, from: usize) -> Option<(usize, usize)> {
        let p = self.page(page);
        let first = (from..LINES).find(|&l| !p.used.get(l))?;
        let end = (first..LINES).find(|&l| p.used.get(l)).unwrap_or(LINES);
        p.used.set_range(first, end);
        p.add(YOUNG);
        Some((page_start(page) + first * LINE, page_start(page) + end * LINE))
    }

    /// The next page with free lines the allocator may use.
    fn reusable(&self) -> Option<usize> {
        let sweeping = self.phase.get() == Phase::Sweeping;
        while self.scan.get() < self.page_count() {
            let page = self.scan.get();
            self.scan.set(page + 1);
            let p = self.page(page);
            let ready = !sweeping || p.has(SWEPT);
            if p.kind.get() == Kind::Lines && ready && !p.has(CANDIDATE) && !p.used.is_full() {
                return Some(page);
            }
        }
        None
    }

    fn fresh_page(&self) -> Result<usize, OutOfMemory> {
        let page = self.new_pages(1)?;
        let p = self.page(page);
        p.kind.set(Kind::Lines);
        p.flags.set(YOUNG | SWEPT);
        p.used.store([!0; LINE_WORDS]);
        Ok(page)
    }

    fn reserve_small(&self, size: usize) -> Result<usize, OutOfMemory> {
        loop {
            let (next, end) = self.bump.get();
            if next + size <= end {
                self.bump.set((next + size, end));
                return Ok(next);
            }
            if size > LINE {
                let (next, end) = self.overflow.get();
                if next + size <= end {
                    self.overflow.set((next + size, end));
                    return Ok(next);
                }
                let page = self.fresh_page()?;
                self.retire(self.overflow.replace((page_start(page), page_start(page) + PAGE)));
                continue;
            }
            if end % PAGE != 0
                && let Some(hole) = self.claim_hole(end / PAGE - 1, end % PAGE / LINE)
            {
                self.retire(self.bump.replace(hole));
                continue;
            }
            let hole = match self.reusable() {
                Some(page) => self.claim_hole(page, 0).expect("page has a free line"),
                None => {
                    let page = self.fresh_page()?;
                    (page_start(page), page_start(page) + PAGE)
                }
            };
            self.retire(self.bump.replace(hole));
        }
    }

    fn reserve_large(&self, size: usize) -> Result<usize, OutOfMemory> {
        let n = size.div_ceil(PAGE);
        if n > MAX_PAGES {
            return Err(self.budget.fail());
        }
        let page = self.new_pages(n)?;
        let head = self.page(page);
        head.kind.set(Kind::Large(n as u32));
        head.flags.set(YOUNG | SWEPT);
        for p in &self.pages()[page + 1..page + n] {
            p.kind.set(Kind::Tail(page as u32));
        }
        Ok(page_start(page))
    }

    /// Reserves `size` bytes and records an object starting there.
    fn reserve(&self, size: usize) -> Result<u32, OutOfMemory> {
        let offset = if size <= MAX_SMALL { self.reserve_small(size)? } else { self.reserve_large(size)? };
        let page = self.page_of(offset).expect("reserved outside the page table");
        self.page(page).start.set(offset % PAGE / GRANULE);
        self.objects.set(self.objects.get() + 1);
        Ok(offset as u32)
    }

    /// Finds or appends a run of `n` free pages and charges for it.
    fn new_pages(&self, n: usize) -> Result<usize, OutOfMemory> {
        let pages = self.pages();
        let mut run = 0;
        let mut start = None;
        if self.free_pages.get() >= n {
            for (i, p) in pages.iter().enumerate() {
                if p.kind.get() != Kind::Free {
                    run = 0;
                    continue;
                }
                run += 1;
                if run == n {
                    start = Some(i + 1 - n);
                    break;
                }
            }
        } else {
            run = pages.iter().rev().take_while(|p| p.kind.get() == Kind::Free).count();
        }
        let start = start.unwrap_or(pages.len() - run);
        let len = (start + n).max(pages.len());
        if len > MAX_PAGES {
            return Err(self.budget.fail());
        }
        let grow = len - pages.len();
        self.budget.charge(n * PAGE + grow * META)?;
        self.page_count.set(len);
        #[cfg(test)]
        self.used_pages.borrow_mut()[start + 1..start + 1 + n].fill(true);
        self.committed.set(self.committed.get() + n);
        self.free_pages.set(self.free_pages.get() - (n - grow));
        Ok(start)
    }

    fn free_run(&self, page: usize, n: usize) {
        for run in [&self.bump, &self.overflow] {
            let (_, end) = run.get();
            if end != 0 && (page..page + n).contains(&((end - 1) / PAGE - 1)) {
                run.set((0, 0));
            }
        }
        for p in &self.pages()[page..page + n] {
            p.reset();
        }
        self.budget.refund(n * PAGE);
        self.committed.set(self.committed.get() - n);
        self.free_pages.set(self.free_pages.get() + n);
        self.decommit(page, n);
        self.trim();
    }

    fn trim(&self) {
        let before = self.page_count();
        let len = before - self.pages().iter().rev().take_while(|p| p.kind.get() == Kind::Free).count();
        self.page_count.set(len);
        self.budget.refund((before - len) * META);
        self.free_pages.set(self.free_pages.get() - (before - len));
        self.scan.set(self.scan.get().min(len));
        self.cursor.set(self.cursor.get().min(len));
    }

    /// Gives the OS pages of a freed run back. When OS pages are bigger than arena pages, the
    /// OS page at each end of the run goes too if the rest of it is already free.
    fn decommit(&self, page: usize, n: usize) {
        let Some(os_page) = region::os_page() else { return };
        let pages = self.pages();
        // Table index `i` is region page `i + 1`, and region page 0 is never used.
        let free = |from: usize, to: usize| {
            (from / PAGE..to.div_ceil(PAGE))
                .all(|r| r == 0 || pages.get(r - 1).is_none_or(|p| p.kind.get() == Kind::Free))
        };
        let (start, end) = (page_start(page), page_start(page + n));
        let mut lo = start / os_page * os_page;
        let mut hi = end.next_multiple_of(os_page);
        if !free(lo, start) {
            lo += os_page;
        }
        if !free(end, hi) {
            hi -= os_page;
        }
        if lo >= hi {
            return;
        }
        #[cfg(test)]
        self.check_decommit(lo, hi, os_page);
        self.region.decommit(lo, hi - lo);
    }

    /// Each OS page given back must be free and must have been used since it was last given back.
    #[cfg(test)]
    fn check_decommit(&self, lo: usize, hi: usize, os_page: usize) {
        let pages = self.pages();
        let mut used = self.used_pages.borrow_mut();
        for os in (lo..hi).step_by(os_page) {
            let region_pages = os / PAGE..(os + os_page).div_ceil(PAGE);
            assert!(region_pages.clone().any(|r| used[r]), "OS page at {os:#x} was already decommitted");
            for r in region_pages {
                let free = r == 0 || pages.get(r - 1).is_none_or(|p| p.kind.get() == Kind::Free);
                assert!(free, "decommitting live page {r}");
            }
        }
        used[lo / PAGE..hi.div_ceil(PAGE)].fill(false);
    }

    /// Undoes `reserve` for an object that was never finished.
    fn release(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return };
        let p = self.page(obj.page);
        p.start.clear(obj.granule);
        p.mark.clear(obj.granule);
        self.objects.set(self.objects.get() - 1);
        match p.kind.get() {
            Kind::Lines if p.start.is_empty() => self.free_run(obj.page, 1),
            Kind::Large(n) => self.free_run(obj.page, n as usize),
            _ => {}
        }
    }

    /// Objects allocated while marking are marked, since the mutator may already have stored
    /// them somewhere that was traced, and queued so their contents get traced.
    fn color(&self, offset: u32, size: usize, needs_trace: bool) {
        self.allocated.set(self.allocated.get() + size);
        if self.is_marking() {
            let obj = self.object_at(offset).expect("new object");
            self.mark_object(obj, size);
            if needs_trace {
                self.push_gray(offset, obj.page);
            }
        } else {
            self.young.set(self.young.get() + size);
        }
    }

    pub(crate) fn alloc<'gc, T: Trace + Plain<'gc>>(&self, value: T) -> Result<NonNull<T>, OutOfMemory> {
        const {
            let () = T::CHECK;
            assert!(!T::INLINE, "inline types must use alloc_inline");
            assert!(layout::fits::<T>(), "type is too large or too aligned for the arena");
            assert!(!needs_drop::<T>(), "arena objects can't need drop; hold host data through a HostRef");
        };
        let vtable = &SizedVTable::<T>::VTABLE;
        let ty = self.type_index(vtable)?;
        let size = const { layout::sized_size::<T>() };
        let offset = self.reserve(size)?;
        unsafe {
            let header = self.header_ptr(offset);
            header.write(Header { ty, flags: self.stamp(), len: 0 });
            let value_ptr = layout::value_ptr::<T>(header);
            value_ptr.write(value);
            self.color(offset, size, vtable.needs_trace);
            Ok(NonNull::new_unchecked(value_ptr))
        }
    }

    pub(crate) fn alloc_inline<'gc, T: Inline + Plain<'gc>>(
        &self,
        head: T,
        len: usize,
        mut fill: impl FnMut(usize) -> T::Item,
    ) -> Result<NonNull<T>, OutOfMemory>
    where
        T::Item: Plain<'gc>,
    {
        const {
            let () = T::CHECK;
            let () = <T::Item as Plain<'gc>>::CHECK;
            assert!(T::INLINE, "type implements Inline but INLINE is false");
            assert!(layout::fits_inline::<T>(), "type is too large or too aligned for the arena");
            assert!(!needs_drop::<T>() && !needs_drop::<T::Item>(), "arena objects can't need drop");
        };
        let size = layout::inline_size::<T>(len)
            .filter(|&size| size <= REGION - PAGE && len <= layout::max_items::<T>())
            .ok_or_else(|| self.budget.fail())?;
        let vtable = &InlineVTable::<T>::VTABLE;
        let ty = self.type_index(vtable)?;
        let offset = self.reserve(size)?;
        unsafe {
            let header = self.header_ptr(offset);
            header.write(Header { ty, flags: self.stamp(), len: len as u32 });
            let value = layout::value_ptr::<T>(header);
            let items = layout::inline_items::<T>(value);
            let guard = Release { heap: self, offset };
            for i in 0..len {
                items.add(i).write(fill(i));
            }
            mem::forget(guard);
            value.write(head);
            self.color(offset, size, vtable.needs_trace);
            Ok(NonNull::new_unchecked(value))
        }
    }

    /// Traces an object's contents, or only what overlaps `range` of it. Returns its size.
    fn trace_object(&self, offset: u32, mode: Mode, range: Option<(usize, usize)>) -> usize {
        let Some(obj) = self.object_at(offset) else {
            self.corrupt();
            return 0;
        };
        let Some((vtable, size)) = self.size_of(obj) else {
            self.corrupt();
            return 0;
        };
        self.trace_with(obj, vtable, range, &mut Tracer::new(self, mode));
        size
    }

    /// The vtable matches the object's header and its size fits where it sits. Collections
    /// only run between steps, when nothing borrows arena memory, so tracing may take `&mut`.
    fn trace_with(&self, obj: Obj, vtable: &VTable, range: Option<(usize, usize)>, t: &mut Tracer<'_>) {
        let header = self.header_ptr(obj.offset);
        match range {
            Some((from, to)) => unsafe { (vtable.trace_range)(header, from, to, t) },
            None => unsafe { (vtable.trace)(header, t) },
        }
    }

    /// Traces every marked object whose header is on `page`, whole.
    fn trace_marked(&self, page: usize, mode: Mode) -> usize {
        let mut work = 0;
        each_bit(&self.page(page).live(), |g| work += self.trace_object(granule_offset(page, g), mode, None));
        work.max(1)
    }

    /// Traces gray objects until about `budget` bytes are done. Returns what's left.
    fn drain(&self, budget: usize) -> usize {
        let mut left = budget;
        loop {
            while left > 0 && !self.corrupted.get() {
                let Some(offset) = self.pop_gray() else { break };
                left = left.saturating_sub(self.trace_object(offset, Mode::Mark, None).max(1));
            }
            if left == 0 || self.corrupted.get() || !self.overflowed.replace(false) {
                return left;
            }
            for page in 0..self.page_count() {
                if self.page(page).remove(OVERFLOW) {
                    left = left.saturating_sub(self.trace_marked(page, Mode::Mark));
                }
            }
        }
    }

    /// Traces the marked objects that overlap dirty cards.
    fn scan_cards(&self, mode: Mode) {
        for page in 0..self.page_count() {
            let p = self.page(page);
            let cards = p.cards.get();
            if cards == 0 || self.corrupted.get() {
                continue;
            }
            match p.kind.get() {
                Kind::Lines => {
                    // Granules before `next` belong to objects already traced.
                    let mut next = 0;
                    for card in (0..CARDS).filter(|c| cards >> c & 1 != 0) {
                        let (from, to) = (card * CARD / GRANULE, (card + 1) * CARD / GRANULE);
                        for g in p.start.prev(from).unwrap_or(from).max(next)..to {
                            if !p.start.get(g) || !p.mark.get(g) {
                                continue;
                            }
                            let offset = granule_offset(page, g);
                            if !self.moved(offset) {
                                let size = self.trace_object(offset, mode, None);
                                next = g + size.div_ceil(GRANULE).max(1);
                            }
                        }
                    }
                }
                Kind::Large(_) | Kind::Tail(_) => {
                    let head = p.head(page);
                    if !self.page(head).mark.get(0) {
                        continue;
                    }
                    for card in (0..CARDS).filter(|c| cards >> c & 1 != 0) {
                        let from = (page - head) * PAGE + card * CARD;
                        self.trace_object(page_start(head) as u32, mode, Some((from, from + CARD)));
                    }
                }
                Kind::Free => {}
            }
        }
    }

    fn clear_cards(&self) {
        for p in self.pages() {
            p.cards.set(0);
        }
    }

    /// Traces the values of ephemerons whose keys got marked, until nothing new is marked.
    fn settle_ephemerons(&self) {
        loop {
            let before = self.marks.get();
            let mut any = false;
            for page in 0..self.page_count() {
                if self.page(page).remove(PENDING) {
                    any = true;
                    self.trace_marked(page, Mode::Mark);
                }
            }
            self.drain(usize::MAX);
            if !any || self.marks.get() == before || self.corrupted.get() {
                return;
            }
        }
    }

    /// Clears ephemerons whose keys stayed unmarked.
    fn clear_dead_ephemerons(&self) {
        for page in 0..self.page_count() {
            if self.page(page).remove(PENDING) {
                self.trace_marked(page, Mode::Clear);
            }
        }
    }

    fn trace_roots<R: Trace>(&self, root: &mut R, mode: Mode) {
        let mut t = Tracer::new(self, mode);
        root.trace(&mut t);
        let mut roots = self.roots.borrow_mut();
        let before = roots.len();
        roots.retain(|entry| Rc::strong_count(entry) > 1);
        self.budget.refund((before - roots.len()) * ROOT_COST);
        roots.shrink(&self.budget);
        for entry in roots.iter() {
            entry.trace(&mut t);
        }
        let mut stacks = self.stacks.borrow_mut();
        for stack in stacks.iter() {
            stack.trace(self, &mut t);
        }
        // A dropped stack's frames were written without a barrier, so it's only let go after
        // this last trace.
        if mode == Mode::Mark {
            let before = stacks.len();
            stacks.retain(|stack| Rc::strong_count(stack) > 1);
            self.budget.refund((before - stacks.len()) * ROOT_COST);
            stacks.shrink(&self.budget);
        }
    }

    /// Marks everything reachable that isn't marked yet, and settles ephemerons.
    fn mark_all<R: Trace>(&self, root: &mut R) -> usize {
        self.trace_roots(root, Mode::Mark);
        self.scan_cards(Mode::Mark);
        let work = 1 + (usize::MAX - self.drain(usize::MAX));
        self.settle_ephemerons();
        #[cfg(any(test, feature = "gc-verify"))]
        self.verify(root);
        work
    }

    /// Collects young objects only. Survivors stay marked, which makes them old.
    pub(crate) fn minor<R: Trace>(&self, root: &mut R) {
        if self.phase.get() != Phase::Idle || self.corrupted.get() {
            return;
        }
        let guard = CorruptOnUnwind(self);
        self.reset_allocators();
        self.mark_all(root);
        if self.corrupted.get() {
            return mem::forget(guard);
        }
        self.clear_dead_ephemerons();
        self.clear_cards();
        let dropped = self.hosts.sweep(&self.budget);
        let mut page = 0;
        while page < self.page_count() {
            if self.page(page).has(YOUNG) {
                self.sweep_page(page);
            }
            page += 1;
        }
        self.young.set(0);
        self.scan.set(0);
        self.minors.set(self.minors.get() + 1);
        mem::forget(guard);
        drop(dropped);
    }

    pub(crate) fn start<R: Trace>(&self, root: &mut R) {
        if self.phase.get() != Phase::Idle || self.corrupted.get() {
            return;
        }
        let guard = CorruptOnUnwind(self);
        self.phase.set(Phase::Marking);
        self.reset_allocators();
        for p in self.pages() {
            p.mark.store([0; WORDS]);
            p.marked_lines.store([0; LINE_WORDS]);
        }
        self.hosts.clear_marks();
        // Cards dirtied since the last cycle only matter to minor collections; this one
        // traces everything from the roots.
        self.clear_cards();
        self.choose_candidates();
        self.trace_roots(root, Mode::Mark);
        mem::forget(guard);
    }

    /// Picks sparse pages to compact, while their used lines fit in half the free budget.
    /// A lone sparse page isn't worth it: its objects would only move to a page of their own.
    fn choose_candidates(&self) {
        let all = self.evacuate_all.get();
        let mut room = (self.budget.limit() - self.budget.used()) / 2;
        let mut count = 0;
        for p in self.pages().iter().filter(|p| p.kind.get() == Kind::Lines) {
            let used = p.used.count() * LINE;
            if all || (used <= PAGE / 4 && used <= room) {
                p.add(CANDIDATE);
                room = room.saturating_sub(used);
                count += 1;
            }
        }
        if count > 1 || all && count > 0 {
            self.evacuating.set(true);
        } else {
            for p in self.pages() {
                p.remove(CANDIDATE);
            }
        }
    }

    /// Advances the current cycle by about `budget` bytes of work.
    pub(crate) fn work<R: Trace>(&self, root: &mut R, budget: usize) {
        let mut left = budget;
        let mut dropped = Vec::new();
        let guard = CorruptOnUnwind(self);
        while !self.corrupted.get() {
            match self.phase.get() {
                Phase::Idle => break,
                Phase::Marking => {
                    left = self.drain(left);
                    if self.corrupted.get() || left == 0 {
                        break;
                    }
                    let (values, work) = self.atomic(root);
                    dropped = values;
                    left = left.saturating_sub(work);
                    if left == 0 {
                        break;
                    }
                }
                Phase::Sweeping => {
                    while left > 0 && self.cursor.get() < self.page_count() {
                        let page = self.cursor.get();
                        self.cursor.set(page + 1);
                        if !self.page(page).has(SWEPT) {
                            self.sweep_page(page);
                            left = left.saturating_sub(SWEEP_COST);
                        }
                    }
                    if self.cursor.get() >= self.page_count() {
                        self.finish_cycle();
                    }
                    break;
                }
            }
        }
        mem::forget(guard);
        drop(dropped);
    }

    fn atomic<R: Trace>(&self, root: &mut R) -> (Vec<Box<dyn Any>>, usize) {
        let work = self.mark_all(root);
        if self.corrupted.get() {
            return (Vec::new(), work);
        }
        self.clear_dead_ephemerons();
        if self.evacuating.get() {
            self.evacuate(root);
            #[cfg(any(test, feature = "gc-verify"))]
            self.verify(root);
            if self.corrupted.get() {
                return (Vec::new(), work);
            }
        }
        self.clear_cards();
        let dropped = self.hosts.sweep(&self.budget);
        for p in self.pages() {
            p.remove(SWEPT);
        }
        self.reset_allocators();
        self.young.set(0);
        self.cursor.set(0);
        self.phase.set(Phase::Sweeping);
        (dropped, work)
    }

    fn each_candidate(&self, mut f: impl FnMut(usize)) {
        let mut page = 0;
        while page < self.page_count() {
            if self.page(page).has(CANDIDATE) {
                f(page);
            }
            page += 1;
        }
    }

    /// Copies the marked objects off candidate pages while there's room, then rewrites every
    /// reference to them. Objects that don't fit stay where they are.
    fn evacuate<R: Trace>(&self, root: &mut R) {
        self.each_candidate(|page| {
            each_bit(&self.page(page).live(), |g| self.move_object(granule_offset(page, g)));
        });
        self.trace_roots(root, Mode::Fixup);
        self.scan_cards(Mode::Fixup);
        self.each_candidate(|page| {
            each_bit(&self.page(page).live(), |g| {
                if let Some(new) = self.forwarded(granule_offset(page, g)) {
                    self.trace_object(new, Mode::Fixup, None);
                }
            });
        });
        self.each_candidate(|page| {
            let p = self.page(page);
            p.remove(CANDIDATE);
            p.marked_lines.store([0; LINE_WORDS]);
            each_bit(&p.live(), |g| {
                let offset = granule_offset(page, g);
                if self.moved(offset) {
                    // References to the old copy were all rewritten, so one left over is stale.
                    self.clear_header(offset);
                    p.start.clear(g);
                    p.mark.clear(g);
                    self.objects.set(self.objects.get() - 1);
                } else if let Some(obj) = self.object_at(offset)
                    && let Some((_, size)) = self.size_of(obj)
                {
                    let at = g * GRANULE;
                    p.marked_lines.set_range(at / LINE, (at + size).div_ceil(LINE));
                }
            });
        });
        self.evacuating.set(false);
    }

    /// Wipes the header of an object that's gone, so stale references to it don't check out.
    fn clear_header(&self, offset: u32) {
        // Only called for an object that was allocated, so the header is in a committed page.
        unsafe { self.header_ptr(offset).write(Header { ty: 0, flags: 0, len: 0 }) }
    }

    fn move_object(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return self.corrupt() };
        let Some((_, size)) = self.size_of(obj) else { return self.corrupt() };
        let Ok(new) = self.budget.quiet(|| self.reserve(size)) else { return };
        let new_obj = self.object_at(new).expect("new object");
        // Both are validated objects of `size` bytes, and nothing borrows arena memory.
        unsafe {
            ptr::copy_nonoverlapping(self.header_ptr(offset).cast::<u8>(), self.header_ptr(new).cast::<u8>(), size);
            let old = self.header_ptr(offset);
            (*old).flags |= FORWARDED;
            (*old).len = new;
        }
        self.mark_object(new_obj, size);
    }

    fn sweep_page(&self, page: usize) {
        let p = self.page(page);
        match p.kind.get() {
            Kind::Lines => {
                let start = p.start.load();
                let live = p.live();
                let dead: [u64; WORDS] = std::array::from_fn(|i| start[i] & !live[i]);
                // Wiping every dead header costs about 5% of young allocation, so only checked
                // builds do it. Their stale references then always fail to check out.
                #[cfg(any(test, feature = "gc-verify"))]
                each_bit(&dead, |g| self.clear_header(granule_offset(page, g)));
                let dead = dead.iter().map(|d| d.count_ones() as usize).sum::<usize>();
                self.objects.set(self.objects.get() - dead);
                p.start.store(live);
                p.used.store(p.marked_lines.load());
                p.flags.set(p.flags.get() & !YOUNG | SWEPT);
                if p.used.is_empty() {
                    self.free_run(page, 1);
                }
            }
            Kind::Large(n) => {
                p.flags.set(p.flags.get() & !YOUNG | SWEPT);
                if !p.mark.get(0) {
                    self.clear_header(page_start(page) as u32);
                    self.objects.set(self.objects.get() - 1);
                    self.free_run(page, n as usize);
                }
            }
            Kind::Free | Kind::Tail(_) => {}
        }
    }

    fn finish_cycle(&self) {
        self.collections.set(self.collections.get() + 1);
        self.retarget();
        self.scan.set(0);
        self.phase.set(Phase::Idle);
    }

    #[cfg(any(test, feature = "gc-verify"))]
    fn verify<R: Trace>(&self, root: &mut R) {
        if self.corrupted.get() {
            return;
        }
        let words = (self.page_count() + 1) * PAGE / GRANULE / 64 + 1;
        let mut v = Verify { seen: vec![0; words], work: Vec::new() };
        root.trace(&mut Tracer::verifying(self, &mut v));
        for entry in self.roots.borrow().iter() {
            entry.trace(&mut Tracer::verifying(self, &mut v));
        }
        for stack in self.stacks.borrow().iter() {
            stack.trace(self, &mut Tracer::verifying(self, &mut v));
        }
        while let Some(offset) = v.work.pop() {
            if self.corrupted.get() {
                return;
            }
            let Some(obj) = self.object_at(offset) else { return self.corrupt() };
            assert!(self.is_marked(obj), "gc verify: reachable object {offset:#x} is not marked");
            assert!(!self.moved(offset), "gc verify: reachable object {offset:#x} was moved");
            let Some((vtable, _)) = self.size_of(obj) else { return self.corrupt() };
            self.trace_with(obj, vtable, None, &mut Tracer::verifying(self, &mut v));
        }
    }

    /// Checks every counter and bitmap against the pages. Panics on any mismatch.
    #[cfg(test)]
    pub(crate) fn check(&self) {
        let pages = self.pages();
        let idle = self.phase.get() == Phase::Idle;
        let (mut objects, mut committed, mut free) = (0, 0, 0);
        let mut i = 0;
        while i < pages.len() {
            let p = &pages[i];
            assert!(!p.has(OVERFLOW | PENDING | CANDIDATE) || self.is_marking(), "page {i} has marking flags");
            match p.kind.get() {
                Kind::Free => {
                    let empty = p.start.is_empty() && p.mark.is_empty() && p.used.is_empty() && p.marked_lines.is_empty();
                    assert!(p.flags.get() == 0 && p.cards.get() == 0 && empty, "free page {i} isn't reset");
                    free += 1;
                }
                Kind::Lines => {
                    committed += 1;
                    let mut end = 0;
                    each_bit(&p.start.load(), |g| {
                        let offset = granule_offset(i, g);
                        let obj = self.object_at(offset).unwrap();
                        let (_, size) = self.size_of(obj).unwrap_or_else(|| panic!("bad object {offset:#x}"));
                        assert!(g * GRANULE >= end, "objects overlap at {offset:#x}");
                        end = g * GRANULE + size;
                        for line in g * GRANULE / LINE..end.div_ceil(LINE) {
                            assert!(p.used.get(line), "object {offset:#x} sits on a free line");
                            if p.mark.get(g) {
                                assert!(p.marked_lines.get(line), "marked object {offset:#x} on an unmarked line");
                            }
                        }
                        objects += 1;
                    });
                    for line in 0..LINES {
                        assert!(!p.marked_lines.get(line) || p.used.get(line), "page {i} line {line} marked but free");
                    }
                    for (m, s) in p.mark.load().iter().zip(p.start.load()) {
                        assert_eq!(m & !s, 0, "page {i} marks a granule with no object");
                    }
                    if idle && !p.has(YOUNG) {
                        assert_eq!(p.start.load(), p.mark.load(), "page {i} has unmarked objects but isn't young");
                    }
                }
                Kind::Large(n) => {
                    let n = n as usize;
                    let mut first = [0; WORDS];
                    first[0] = 1;
                    assert_eq!(p.start.load(), first, "large page {i}");
                    for (j, tail) in pages[i + 1..i + n].iter().enumerate() {
                        assert_eq!(tail.kind.get(), Kind::Tail(i as u32), "page {} should be a tail of {i}", i + 1 + j);
                        assert!(tail.start.is_empty(), "tail page {} has object starts", i + 1 + j);
                    }
                    if idle && !p.has(YOUNG) {
                        assert!(p.mark.get(0), "large page {i} is unmarked but isn't young");
                    }
                    objects += 1;
                    committed += n;
                    i += n;
                    continue;
                }
                Kind::Tail(head) => panic!("page {i} is an orphan tail of {head}"),
            }
            i += 1;
        }
        for (next, end) in [self.bump.get(), self.overflow.get()] {
            if end != 0 {
                let page = self.page_of(end - 1).expect("allocation run outside the pages");
                assert_eq!(pages[page].kind.get(), Kind::Lines, "allocation run on a page that isn't for lines");
                assert!(!pages[page].has(CANDIDATE), "allocation run on a page being compacted");
                for line in next % PAGE / LINE..(end - 1) % PAGE / LINE + 1 {
                    assert!(pages[page].used.get(line), "allocation run on a free line");
                }
            }
        }
        assert_eq!(objects, self.objects.get(), "object count");
        assert_eq!(committed, self.committed.get(), "committed pages");
        assert_eq!(free, self.free_pages.get(), "free pages");
        let gray_empty = !self.overflowed.get() && self.gray_len.get() == 0;
        assert!(gray_empty || self.is_marking(), "gray objects outside marking");
        assert!(!self.evacuating.get() || self.is_marking(), "evacuating outside marking");
        let (roots, stacks) = (self.roots.borrow(), self.stacks.borrow());
        let tables = pages.len() * META + roots.charged() + stacks.charged() + self.hosts.charged();
        let expected = committed * PAGE + (roots.len() + stacks.len()) * ROOT_COST + tables + GRAY_BYTES;
        assert_eq!(self.budget.used(), expected, "budget");
        assert!(self.budget.used() <= self.budget.limit());
    }

    /// Sets when the next major cycle starts: once usage doubles, but never later than
    /// halfway from the current usage to the limit, so a cycle always has room to finish.
    fn retarget(&self) {
        let (used, limit) = (self.budget.used(), self.budget.limit());
        self.threshold.set((used * 2).max(MIN_THRESHOLD).min(used + (limit - used) / 2));
    }

    /// Counts bytes charged outside the region towards pacing.
    pub(crate) fn demand(&self, bytes: usize) {
        self.allocated.set(self.allocated.get() + bytes);
        self.young.set(self.young.get() + bytes);
    }

    pub(crate) fn clear_allocated(&self) {
        self.allocated.set(0);
    }

    #[cfg(test)]
    pub(crate) fn set_gray_limit(&self, limit: usize) {
        self.gray_limit.set(limit.min(GRAY_CAPACITY));
    }

    #[cfg(test)]
    pub(crate) fn dirty_cards(&self) -> u32 {
        self.pages().iter().map(|p| p.cards.get().count_ones()).sum()
    }

    #[cfg(test)]
    pub(crate) fn vtable_size(&self, offset: u32) -> Option<usize> {
        let header = self.header(self.object_at(offset)?);
        (self.vtable(header.ty)?.size)(header)
    }

    #[cfg(test)]
    pub(crate) fn header_of(&self, offset: u32) -> *mut Header {
        self.header_ptr(offset)
    }

    /// Whether the object is marked, which outside a major cycle means it survived a collection.
    #[cfg(test)]
    pub(crate) fn is_old(&self, offset: u32) -> bool {
        self.object_at(offset).is_some_and(|obj| self.is_marked(obj))
    }
}

/// Tables the heap fills in as it grows. Zeroed memory comes from the allocator untouched,
/// so the OS only commits the parts that get used.
///
/// # Safety
/// All-zero bytes must be a valid value of the type.
unsafe trait Zeroed {}

// `Kind` is `repr(u32)` with `Free` = 0, and the rest of a page is cells of integers.
unsafe impl Zeroed for [Page; MAX_PAGES] {}
unsafe impl Zeroed for [Cell<Option<&'static VTable>>; TYPES] {}

fn zeroed<T: Zeroed>() -> Box<T> {
    unsafe { Box::new_zeroed().assume_init() }
}

/// A panic in user `Trace` code would leave a collection half done, so the heap can't be trusted.
struct CorruptOnUnwind<'a>(&'a Heap);

impl Drop for CorruptOnUnwind<'_> {
    fn drop(&mut self) {
        self.0.corrupt();
    }
}

/// Gives a reserved object back if filling it panics.
struct Release<'a> {
    heap: &'a Heap,
    offset: u32,
}

impl Drop for Release<'_> {
    fn drop(&mut self) {
        self.heap.release(self.offset);
    }
}

#[cfg(any(test, feature = "gc-verify"))]
pub(crate) struct Verify {
    seen: Vec<u64>,
    work: Vec<u32>,
}

#[cfg(any(test, feature = "gc-verify"))]
impl Verify {
    pub(crate) fn visit(&mut self, heap: &Heap, offset: u32) {
        if heap.object_at(offset).is_none() {
            return heap.corrupt();
        }
        let bit = offset as usize / GRANULE;
        let (word, mask) = (bit / 64, 1u64 << (bit % 64));
        if self.seen[word] & mask == 0 {
            self.seen[word] |= mask;
            self.work.push(offset);
        }
    }
}
