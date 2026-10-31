//! A prototype garbage collector with no unsafe code, to measure what that costs against
//! `ragwort-gc`. The region is words in `Cell`s, references are word indices, and a type is
//! described by data the collector reads rather than code it runs. A wrong description or a
//! forged reference gives wrong results or a panic, never undefined behavior.
//!
//! It has `ragwort-gc`'s structure: 16 KiB pages of 128-byte lines, 512-byte cards, sticky mark
//! bits for minor collections, major cycles marked in incremental slices with the same pacing,
//! weak references and ephemerons, evacuation of fragmented pages through forwarding headers in
//! the atomic phase, and lazy sweeping. Free pages past a nursery's worth go back to the system
//! through `ragwort-gc-region`, which holds the only unsafe code. Memory is counted against a
//! budget with a reserve, as in `ragwort-gc`, and VM stacks have its segments, continuation
//! capture and parking.

use std::any::{Any, TypeId};
use std::cell::{Cell, OnceCell, Ref, RefCell};
use std::marker::PhantomData;
use std::ops::Range;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use ragwort_gc_region::Region;

mod budget;
mod stack;

use budget::Budget;
pub use budget::Charge;
use stack::{STACK_COST, StackRecord};
pub use stack::{Frame, Segment, Stack};

#[cfg(test)]
#[path = "tests/heap.rs"]
mod tests;
#[cfg(test)]
#[path = "tests/stack.rs"]
mod stack_tests;
#[cfg(test)]
#[path = "tests/budget.rs"]
mod budget_tests;

pub const REGION: usize = 64 << 20;
/// The region in words: twice `REGION`, so evacuation has fresh pages to copy into.
const WORDS: usize = 2 * REGION / 8;
/// Page, line and card sizes in words.
const PAGE: usize = 2048;
const LINE: usize = 16;
const CARD: usize = 64;
const PAGES: usize = WORDS / PAGE;
/// Unused words past the region, so `mask(index) + 1 + field` for a constant field needs no
/// bounds check.
const SLACK: usize = 128;
const LINES: usize = PAGE / LINE;
pub const WINDOW: usize = 256;

const TAG: u64 = 0b1111;
const OBJECT: u64 = 0b0001;
const CONSTANT: u64 = 0b1101;
/// Inline flonums end in 11: a double with two redundant exponent bits dropped.
const FLONUM: u64 = 0b11;
/// The special doubles take the words of the lowest few inline ones, ±1.7272337110188889e-77
/// and the two above, which are boxed instead. The NaNs are the defaults ARM and x86 make.
const SPECIALS: [u64; 6] = [0, 1 << 63, 0x7FF0 << 48, 0xFFF0 << 48, 0x7FF8 << 48, 0xFFF8 << 48];
/// The first special's word. Each next one is 4 above it.
const ZERO: u64 = 0x8000_0000_0000_0003;
const LAST_SPECIAL: u64 = 4 * (SPECIALS.len() as u64 - 1);

#[inline]
fn encode(f: f64) -> Option<u64> {
    let bits = f.to_bits();
    // Exponents starting 011 or 100: the second and third bits copy the inverse of the first.
    let top = bits >> 60 & 0b111;
    if top == 0b011 || top == 0b100 {
        let word = bits.rotate_left(3) | FLONUM;
        return (word.wrapping_sub(ZERO) > LAST_SPECIAL).then_some(word);
    }
    let i = SPECIALS.iter().position(|&s| s == bits)?;
    Some(ZERO + 4 * i as u64)
}

#[inline]
fn decode(word: u64) -> f64 {
    let special = word.wrapping_sub(ZERO);
    if special <= LAST_SPECIAL {
        return f64::from_bits(SPECIALS[special as usize / 4]);
    }
    let first = word >> 63;
    f64::from_bits((word & !FLONUM | (2 - first)).rotate_right(3))
}

/// A double that doesn't fit in a word: magnitudes beyond about 1e±77, and the NaNs not in
/// `SPECIALS`. Every arena registers it first, so it's type 0.
struct Boxed;

impl Object for Boxed {
    const DESC: Desc = Desc::of::<Boxed>(1);
}
/// A header is the type index, a flag, and the item count in the upper half. A forwarded one
/// has the new index there instead.
const TYPE_BITS: u64 = 0xFFFF;
const FORWARDED: u64 = 1 << 16;
const TYPES: usize = 1 << 16;
static NEXT_ARENA: AtomicU64 = AtomicU64::new(0);

type Brand<'gc> = PhantomData<Cell<&'gc ()>>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OutOfMemory;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Items {
    None,
    Values,
    Words,
    /// Pairs of a key and a value, held like `Desc::ephemerons`. The length counts words.
    Ephemerons,
}

/// How the collector sees a type: its fixed words, which of them hold references, and its items.
pub struct Desc {
    pub type_id: fn() -> TypeId,
    pub fields: u32,
    /// Fields holding a `Value`.
    pub values: u64,
    /// Fields holding an object index, 0 for none.
    pub members: u64,
    /// Fields holding a host id plus one, 0 for none.
    pub hosts: u64,
    /// Fields holding an object index that doesn't keep the object alive, 0 for none.
    pub weaks: u64,
    /// Fields holding an ephemeron's key, with its value in the next field. The value is kept
    /// alive only while the key is reachable some other way; once the key dies, both become
    /// `Value::BROKEN`. A key that isn't an object never dies.
    pub ephemerons: u64,
    pub items: Items,
}

impl Desc {
    pub const fn of<T: 'static>(fields: u32) -> Self {
        Self {
            type_id: TypeId::of::<T>,
            fields,
            values: 0,
            members: 0,
            hosts: 0,
            weaks: 0,
            ephemerons: 0,
            items: Items::None,
        }
    }

    pub const fn values(self, values: u64) -> Self {
        Self { values, ..self }
    }

    pub const fn members(self, members: u64) -> Self {
        Self { members, ..self }
    }

    pub const fn hosts(self, hosts: u64) -> Self {
        Self { hosts, ..self }
    }

    pub const fn weaks(self, weaks: u64) -> Self {
        Self { weaks, ..self }
    }

    pub const fn ephemerons(self, ephemerons: u64) -> Self {
        Self { ephemerons, ..self }
    }

    pub const fn items(self, items: Items) -> Self {
        Self { items, ..self }
    }

    const fn traces(&self) -> bool {
        self.values | self.members | self.hosts | self.weaks != 0 || self.has_ephemerons() || matches!(self.items, Items::Values)
    }

    const fn has_ephemerons(&self) -> bool {
        self.ephemerons != 0 || matches!(self.items, Items::Ephemerons)
    }

    fn size(&self, header: u64) -> usize {
        1 + self.fields as usize + if self.items == Items::None { 0 } else { (header >> 32) as usize }
    }
}

/// A type that lives in the arena. Implementing it is safe: a wrong `DESC` can only give wrong
/// results.
pub trait Object: 'static {
    const DESC: Desc;
}

/// A value in one word: a fixnum shifted left by one, an object's index and type, or a constant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Value<'gc> {
    word: u64,
    _brand: Brand<'gc>,
}

impl<'gc> Value<'gc> {
    pub const FALSE: Self = Self::constant(0);
    pub const TRUE: Self = Self::constant(1);
    pub const NIL: Self = Self::constant(2);
    /// What a stack slot above `top` becomes.
    pub const VOID: Self = Self::constant(3);
    /// What an ephemeron's key and value become once the key dies.
    pub const BROKEN: Self = Self::constant(7);

    const fn constant(id: u64) -> Self {
        Self::from_bits(id << 32 | CONSTANT)
    }

    /// Any word is a valid value. One that names no object reads as some other object or none.
    pub const fn from_bits(word: u64) -> Self {
        Self { word, _brand: PhantomData }
    }

    pub const fn to_bits(self) -> u64 {
        self.word
    }

    #[inline]
    pub fn fixnum(n: i64) -> Option<Self> {
        let word = (n as u64) << 1;
        ((word as i64) >> 1 == n).then_some(Self::from_bits(word))
    }

    #[inline]
    pub fn as_fixnum(self) -> Option<i64> {
        (self.word & 1 == 0).then_some(self.word as i64 >> 1)
    }

    #[inline]
    pub fn fixnum_add(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_add(other.word as i64).map(|w| Self::from_bits(w as u64))
    }

    /// Stores the double in the word when it fits, and boxes it otherwise.
    #[inline]
    pub fn flonum(mc: &Mutation<'gc>, f: f64) -> Result<Self, OutOfMemory> {
        match encode(f) {
            Some(word) => Ok(Self::from_bits(word)),
            None => Ok(Self::object(mc, mc.alloc::<Boxed, 1>([f.to_bits()])?)),
        }
    }

    /// The double as a value without allocating, if it fits in the word.
    #[inline]
    pub fn inline_flonum(f: f64) -> Option<Self> {
        encode(f).map(Self::from_bits)
    }

    /// Inline, or a reference to a boxed one: type 0 in every arena.
    #[inline]
    pub fn is_flonum(self) -> bool {
        self.word & FLONUM == FLONUM || self.word & (TYPE_BITS << 16 | TAG) == OBJECT
    }

    #[inline]
    pub fn as_flonum(self, mc: &Mutation<'gc>) -> Option<f64> {
        if self.word & FLONUM == FLONUM {
            Some(decode(self.word))
        } else if self.word & (TYPE_BITS << 16 | TAG) == OBJECT {
            let boxed: Gc<'gc, Boxed> = Gc::new((self.word >> 32) as u32);
            Some(f64::from_bits(boxed.word(mc, 0)))
        } else {
            None
        }
    }

    #[inline]
    pub fn object<T: Object>(mc: &Mutation<'gc>, gc: Gc<'gc, T>) -> Self {
        let ty = mc.heap.words[mask(gc.index as usize)].get() & TYPE_BITS;
        Self::from_bits(u64::from(gc.index) << 32 | ty << 16 | OBJECT)
    }

    #[inline]
    pub fn downcast<T: Object>(self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>> {
        self.downcast_tag(mc.type_tag::<T>()?)
    }

    /// Compares the type the reference carries, without reading the object.
    #[inline]
    pub fn downcast_tag<T: Object>(self, tag: TypeTag<'gc, T>) -> Option<Gc<'gc, T>> {
        (self.word & (TYPE_BITS << 16 | TAG) == u64::from(tag.ty) << 16 | OBJECT).then(|| Gc::new((self.word >> 32) as u32))
    }
}

pub struct TypeTag<'gc, T> {
    ty: u16,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for TypeTag<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for TypeTag<'_, T> {}

/// An object: its header's index in the region.
pub struct Gc<'gc, T> {
    index: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for Gc<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Gc<'_, T> {}

impl<T> PartialEq for Gc<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<'gc, T: Object> Gc<'gc, T> {
    const fn new(index: u32) -> Self {
        Self { index, _marker: PhantomData }
    }

    /// The word a field declared in `Desc::members` holds.
    pub fn to_word(self) -> u64 {
        u64::from(self.index)
    }

    /// The word of field `field`. Panics past the declared fields, so a write can't reach the
    /// next object; constant field numbers fold the check away.
    #[inline]
    fn slot(self, field: usize) -> usize {
        assert!(field < T::DESC.fields as usize, "field {field} of {}", T::DESC.fields);
        mask(self.index as usize) + 1 + field
    }

    /// Where the items start.
    #[inline]
    fn items_at(self) -> usize {
        mask(self.index as usize) + 1 + T::DESC.fields as usize
    }

    /// Indexes a view of the words shifted by the field, so for a constant field the masked
    /// index is the whole address computation, as a list walk's chain of loads wants.
    #[inline]
    pub fn word(self, mc: &Mutation<'gc>, field: usize) -> u64 {
        assert!(field < T::DESC.fields as usize, "field {field} of {}", T::DESC.fields);
        let words = mc.heap.words;
        match words.get(1 + field..).and_then(<[_]>::first_chunk::<WORDS>) {
            Some(shifted) => shifted[mask(self.index as usize)].get(),
            None => words[mask(self.index as usize) + 1 + field].get(),
        }
    }

    /// For fields that hold no reference: no barrier.
    #[inline]
    pub fn set_word(self, mc: &Mutation<'gc>, field: usize, word: u64) {
        mc.heap.words[self.slot(field)].set(word);
    }

    #[inline]
    pub fn value(self, mc: &Mutation<'gc>, field: usize) -> Value<'gc> {
        Value::from_bits(self.word(mc, field))
    }

    #[inline]
    pub fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>) {
        let slot = self.slot(field);
        mc.heap.words[slot].set(value.word);
        mc.heap.barrier(slot, self.index, value.word);
    }

    #[inline]
    pub fn member<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        let index = self.word(mc, field) as u32;
        (index != 0).then(|| Gc::new(index))
    }

    #[inline]
    pub fn set_member<U: Object>(self, mc: &Mutation<'gc>, field: usize, member: Option<Gc<'gc, U>>) {
        let slot = self.slot(field);
        let index = member.map_or(0, |m| m.index);
        mc.heap.words[slot].set(u64::from(index));
        if index != 0 {
            mc.heap.barrier_ref(slot, self.index, index);
        }
    }

    /// The target of a weak field, or `None` once it has died.
    #[inline]
    pub fn weak<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        self.member(mc, field)
    }

    /// Dirties the card, for minor collections to clear the field, but doesn't shade the target.
    #[inline]
    pub fn set_weak<U: Object>(self, mc: &Mutation<'gc>, field: usize, target: Option<Gc<'gc, U>>) {
        let slot = self.slot(field);
        mc.heap.words[slot].set(u64::from(target.map_or(0, |t| t.index)));
        mc.heap.dirty(slot);
    }

    pub fn set_host<U: Any>(self, mc: &Mutation<'gc>, field: usize, host: HostRef<'gc, U>) {
        mc.heap.words[self.slot(field)].set(host.to_word());
        if mc.heap.m.phase.get() == Phase::Marking && mc.heap.has_bit(self.index as usize, |p| &p.marks) {
            mc.heap.mark_host(host.to_word());
        }
    }

    #[inline]
    pub fn host<U: Any>(self, mc: &Mutation<'gc>, field: usize) -> Option<HostRef<'gc, U>> {
        let (id, generation) = host_parts(self.word(mc, field))?;
        Some(HostRef { id, generation, _marker: PhantomData })
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        if T::DESC.items == Items::None { 0 } else { (mc.heap.words[mask(self.index as usize)].get() >> 32) as usize }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// The object's first `N` fields. `N` past the declared fields doesn't compile.
    #[inline]
    pub fn fields<const N: usize>(self, mc: &Mutation<'gc>) -> Option<Fields<'gc, N>> {
        const { assert!(N <= T::DESC.fields as usize, "more fields than the type declares") };
        let at = mask(self.index as usize) + 1;
        let heap = mc.heap;
        let words = heap.words.get(at..)?.first_chunk()?;
        Some(Fields { words, at, owner: self.index, _brand: PhantomData })
    }

    /// The key and value of the ephemeron at `field`, one in `Desc::ephemerons`, or `None` once
    /// its key has died.
    #[inline]
    pub fn ephemeron(self, mc: &Mutation<'gc>, field: usize) -> Option<(Value<'gc>, Value<'gc>)> {
        assert!(field + 1 < T::DESC.fields as usize, "ephemeron at field {field} of {}", T::DESC.fields);
        mc.heap.ephemeron_at(self.slot(field))
    }

    /// Neither part is shaded while marking: the value is traced once the key is found live.
    /// The cards are dirtied, so a minor collection sees both.
    #[inline]
    pub fn set_ephemeron(self, mc: &Mutation<'gc>, field: usize, key: Value<'gc>, value: Value<'gc>) {
        assert!(field + 1 < T::DESC.fields as usize, "ephemeron at field {field} of {}", T::DESC.fields);
        mc.heap.set_ephemeron_at(self.slot(field), key, value);
    }

    /// Entry `i` of `Items::Ephemerons` items, or `None` once its key has died. Panics past
    /// the end.
    #[inline]
    pub fn entry(self, mc: &Mutation<'gc>, i: usize) -> Option<(Value<'gc>, Value<'gc>)> {
        assert!(2 * i + 1 < self.len(mc), "entry {i} out of bounds");
        mc.heap.ephemeron_at(mask(self.items_at() + 2 * i))
    }

    #[inline]
    pub fn set_entry(self, mc: &Mutation<'gc>, i: usize, key: Value<'gc>, value: Value<'gc>) {
        assert!(2 * i + 1 < self.len(mc), "entry {i} out of bounds");
        mc.heap.set_ephemeron_at(mask(self.items_at() + 2 * i), key, value);
    }

    #[inline]
    pub fn slots(self, mc: &Mutation<'gc>) -> Slots<'gc> {
        let at = self.items_at();
        let heap = mc.heap;
        let words = heap.words.get(at..at + self.len(mc)).unwrap_or(&[]);
        Slots { words, at, owner: self.index, _brand: PhantomData }
    }
}

/// An object's fields as a fixed array, so constant field numbers need no bounds check: the
/// safe counterpart of a `&'gc T`.
#[derive(Clone, Copy)]
pub struct Fields<'gc, const N: usize> {
    words: &'gc [Cell<u64>; N],
    at: usize,
    owner: u32,
    _brand: Brand<'gc>,
}

impl<'gc, const N: usize> Fields<'gc, N> {
    #[inline]
    pub fn value(self, field: usize) -> Value<'gc> {
        Value::from_bits(self.words[field].get())
    }

    #[inline]
    pub fn word(self, field: usize) -> u64 {
        self.words[field].get()
    }

    #[inline]
    pub fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>) {
        self.words[field].set(value.word);
        mc.heap.barrier(self.at + field, self.owner, value.word);
    }
}

/// An object's items, read and written as values.
#[derive(Clone, Copy)]
pub struct Slots<'gc> {
    words: &'gc [Cell<u64>],
    at: usize,
    owner: u32,
    _brand: Brand<'gc>,
}

impl<'gc> Slots<'gc> {
    pub fn len(self) -> usize {
        self.words.len()
    }

    pub fn is_empty(self) -> bool {
        self.words.is_empty()
    }

    #[inline]
    pub fn get(self, i: usize) -> Value<'gc> {
        Value::from_bits(self.words[i].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, i: usize, value: Value<'gc>) {
        self.words[i].set(value.word);
        mc.heap.barrier(self.at + i, self.owner, value.word);
    }

    /// Copies `src` in, which may overlap, with one barrier for the whole range. Panics if the
    /// lengths differ.
    pub fn copy_from(self, mc: &Mutation<'gc>, src: Slots<'gc>) {
        assert_eq!(self.len(), src.len(), "copy between slices of different lengths");
        let refs = src.words.iter().any(|s| s.get() & TAG == OBJECT);
        if self.at > src.at {
            for (d, s) in self.words.iter().zip(src.words).rev() {
                d.set(s.get());
            }
        } else {
            for (d, s) in self.words.iter().zip(src.words) {
                d.set(s.get());
            }
        }
        if refs {
            mc.heap.barrier_range(self.at, self.words, self.owner);
        }
    }

    pub fn fill(self, mc: &Mutation<'gc>, value: Value<'gc>) {
        for slot in self.words {
            slot.set(value.word);
        }
        if value.word & TAG == OBJECT {
            mc.heap.barrier_range(self.at, self.words, self.owner);
        }
    }

    /// The items in `range`, or `None` past the end.
    pub fn slice(self, range: Range<usize>) -> Option<Slots<'gc>> {
        let words = self.words.get(range.clone())?;
        Some(Slots { words, at: self.at + range.start, owner: self.owner, _brand: PhantomData })
    }

    /// The first `WINDOW` items, indexed by a byte so no access needs a bounds check.
    pub fn window(self) -> Option<Window<'gc>> {
        Some(Window { slots: self.words.first_chunk()?, at: self.at, owner: self.owner, _brand: PhantomData })
    }
}

#[derive(Clone, Copy)]
pub struct Window<'gc> {
    slots: &'gc [Cell<u64>; WINDOW],
    at: usize,
    owner: u32,
    _brand: Brand<'gc>,
}

impl<'gc> Window<'gc> {
    #[inline]
    pub fn get(self, r: u8) -> Value<'gc> {
        Value::from_bits(self.slots[r as usize].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, r: u8, value: Value<'gc>) {
        self.slots[r as usize].set(value.word);
        mc.heap.barrier(self.at + r as usize, self.owner, value.word);
    }
}

/// Host data, kept outside the region.
pub struct HostRef<'gc, T> {
    id: u32,
    generation: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for HostRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for HostRef<'_, T> {}

impl<'gc, T: Any> HostRef<'gc, T> {
    /// The value, or `None` once it's been freed: a stale reference never reads the value that
    /// took its slot. While the `Ref` is held, `Mutation::host` fails with `HostError::InUse`.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        let hosts = mc.heap.m.hosts.try_borrow().ok()?;
        Ref::filter_map(hosts, |hosts| {
            let slot = hosts.get(self.id as usize).filter(|s| s.generation == self.generation)?;
            slot.value.as_deref()?.downcast_ref::<T>()
        })
        .ok()
    }

    /// The word a field declared in `Desc::hosts` holds: the slot's generation, and its id plus
    /// one so that 0 is none.
    pub fn to_word(self) -> u64 {
        u64::from(self.generation) << 32 | (u64::from(self.id) + 1)
    }
}

fn host_parts(word: u64) -> Option<(u32, u32)> {
    Some(((word as u32).checked_sub(1)?, (word >> 32) as u32))
}

struct HostSlot {
    generation: u32,
    marked: bool,
    /// What the value is charged, refunded when it's freed.
    cost: usize,
    value: Option<Box<dyn Any>>,
}

/// What a host value is charged beyond its size: its slot, and the box's header.
const HOST_COST: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HostError {
    /// A `Ref` from `HostRef::get` is still held.
    InUse,
    OutOfMemory,
}

impl From<OutOfMemory> for HostError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

/// A table that grows a chunk at a time, so an arena pays only for the entries it uses.
/// `C * N` entries, the first `C` made up front and the rest a chunk at a time. Indexing with
/// a `u16` when that's 65536 needs no bounds check.
struct Chunked<T, const C: usize, const N: usize> {
    first: Box<[T; C]>,
    /// The chunks after the first; the slot for the first is unused.
    chunks: Box<[OnceCell<Box<[T; C]>>; N]>,
}

impl<T: Default, const C: usize, const N: usize> Chunked<T, C, N> {
    fn new() -> Self {
        let chunks: Box<[_]> = (0..N).map(|_| OnceCell::new()).collect();
        Self { first: Self::chunk(), chunks: chunks.try_into().ok().expect("N chunks") }
    }

    fn chunk() -> Box<[T; C]> {
        Box::new(std::array::from_fn(|_| T::default()))
    }

    #[inline]
    fn get(&self, i: usize) -> Option<&T> {
        if i < C {
            return Some(&self.first[i]);
        }
        Some(&self.chunks.get(i / C)?.get()?[i % C])
    }

    fn get_or_grow(&self, i: usize) -> Option<&T> {
        if i < C {
            return Some(&self.first[i]);
        }
        Some(&self.chunks.get(i / C)?.get_or_init(Self::chunk)[i % C])
    }
}

#[derive(Default)]
struct Page {
    starts: [Cell<u64>; PAGE / 64],
    marks: [Cell<u64>; PAGE / 64],
    /// Lines holding marked objects, built while marking.
    lines: Cell<u128>,
    /// Lines the allocator can't use: `lines` as of the last sweep.
    used: Cell<u128>,
    cards: Cell<u32>,
    evacuating: Cell<bool>,
    /// Swept since the last cycle's marking ended.
    swept: Cell<bool>,
    /// Holds part of an object larger than a page, which starts on this page: it isn't
    /// evacuated, and a dirty card finds the object's header without scanning back to it.
    large: Cell<Option<u32>>,
    /// Given back to the system while free.
    released: Cell<bool>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Idle,
    Marking,
    /// Marking is done; pages are swept in later slices, or before the allocator uses them.
    Sweeping,
}

/// A collection's work lists.
#[derive(Default)]
struct Work {
    gray: Vec<u32>,
    /// Slots that refer to objects on pages being evacuated, as (object, word in it).
    fixups: Vec<(u32, u32)>,
    /// Objects with weak fields that were traced.
    holders: Vec<u32>,
    /// Objects with ephemerons that were traced.
    ephemerons: Vec<u32>,
}

/// Everything but the words.
struct Meta {
    pages: Box<[Page]>,
    /// Pages handed out, from the start of the region. Those not released are charged.
    used: Cell<usize>,
    budget: Budget,
    /// The hole being allocated into. While failures are injected, `end` is kept at `cursor`
    /// so every allocation takes the slow path, which counts it.
    cursor: Cell<usize>,
    end: Cell<usize>,
    hole_end: Cell<usize>,
    /// The next line to look for a hole from, as `page * LINES + line`.
    scan: Cell<usize>,
    /// Where evacuation copies to.
    to_cursor: Cell<usize>,
    to_end: Cell<usize>,
    /// Bytes allocated since the last collection.
    young: Cell<usize>,
    /// Pages holding something as of the last sweep.
    occupied: Cell<usize>,
    /// Pages before this are swept.
    sweep_cursor: Cell<usize>,
    /// A collection swept everything since free pages were last given back.
    settle: Cell<bool>,
    nursery: usize,
    /// A major cycle starts once the pages in use reach this many bytes.
    threshold: Cell<usize>,
    phase: Cell<Phase>,
    /// Whether this cycle evacuates the pages flagged at its start.
    evacuating: Cell<bool>,
    evacuate_all: Cell<bool>,
    descs: Chunked<Cell<Option<&'static Desc>>, 256, { TYPES / 256 }>,
    count: Cell<usize>,
    cache: [Cell<(usize, u16)>; 64],
    roots: Box<[Cell<u64>]>,
    stacks: RefCell<Vec<Rc<StackRecord>>>,
    /// Tells arenas apart, for handles that live outside them.
    id: u64,
    hosts: RefCell<Vec<HostSlot>>,
    free_hosts: RefCell<Vec<u32>>,
    /// Freed by the last collection, dropped once it has returned.
    dead_hosts: RefCell<Vec<Box<dyn Any>>>,
    work: RefCell<Work>,
    /// What the work lists and tables outside the region were last charged.
    tables: Cell<usize>,
    /// A cycle slice of this many bytes after every step, for testing barriers.
    stress: Cell<Option<usize>>,
    collections: Cell<u64>,
    minors: Cell<u64>,
}

#[derive(Clone, Copy)]
struct Heap<'a> {
    words: &'a [Cell<u64>; WORDS + SLACK],
    m: &'a Meta,
}

/// Wraps an index into the region, so indexing it needs no bounds check: a bad index reads
/// some other word, as a forged one would anyway. Small offsets past it land in `SLACK`.
#[inline]
fn mask(i: usize) -> usize {
    i & (WORDS - 1)
}

const MIN_THRESHOLD: usize = 64 << 10;
/// What a committed page is charged: its words and its bookkeeping.
const PAGE_COST: usize = PAGE * 8 + size_of::<Page>();
/// A page's sweep counts as this many bytes of slice work.
const SWEEP_COST: usize = PAGE;
const MIN_SLICE: usize = 64 << 10;
const STEP_MUL: usize = 2;

pub struct Arena {
    memory: Region,
    meta: Meta,
}

impl Arena {
    /// An arena allowed `limit` bytes, with `roots` value slots. The table of pages, made up
    /// front for twice the limit, isn't charged; the roots are.
    pub fn new(limit: usize, roots: usize) -> Self {
        // Page 0 holds nothing, so index 0 can mean none. Twice the limit leaves evacuation room
        // to copy everything.
        let pages = (limit / (PAGE * 8)).clamp(1, PAGES / 2 - 1);
        let meta = Meta {
            pages: (0..2 * pages + 2).map(|_| Page::default()).collect(),
            used: Cell::new(1),
            budget: Budget::new(limit),
            cursor: Cell::new(0),
            end: Cell::new(0),
            hole_end: Cell::new(0),
            scan: Cell::new(LINES),
            to_cursor: Cell::new(0),
            to_end: Cell::new(0),
            young: Cell::new(0),
            occupied: Cell::new(0),
            sweep_cursor: Cell::new(0),
            settle: Cell::new(false),
            nursery: (limit / 8).clamp(64 << 10, 4 << 20),
            threshold: Cell::new(MIN_THRESHOLD.min(pages * PAGE * 8 / 2)),
            phase: Cell::new(Phase::Idle),
            evacuating: Cell::new(false),
            evacuate_all: Cell::new(false),
            descs: Chunked::new(),
            count: Cell::new(1),
            cache: [const { Cell::new((0, 0)) }; 64],
            roots: vec![Cell::new(Value::NIL.word); roots].into_boxed_slice(),
            stacks: RefCell::new(Vec::new()),
            id: NEXT_ARENA.fetch_add(1, Ordering::Relaxed),
            hosts: RefCell::new(Vec::new()),
            free_hosts: RefCell::new(Vec::new()),
            dead_hosts: RefCell::new(Vec::new()),
            work: RefCell::new(Work::default()),
            tables: Cell::new(0),
            stress: Cell::new(None),
            collections: Cell::new(0),
            minors: Cell::new(0),
        };
        if let Some(boxed) = meta.descs.get_or_grow(0) {
            boxed.set(Some(&Boxed::DESC));
        }
        meta.budget.force(roots * 8);
        Self { memory: Region::new(WORDS + SLACK).expect("reserve the arena's memory"), meta }
    }

    fn heap(&mut self) -> Heap<'_> {
        let words = self.memory.words().first_chunk().expect("the region is WORDS + SLACK long");
        Heap { words, m: &self.meta }
    }

    /// After every collection entry point: gives back free pages, and runs the destructors of
    /// hosts freed, outside the collector.
    fn finish(&mut self) {
        self.settle();
        let dead = std::mem::take(&mut *self.meta.dead_hosts.borrow_mut());
        drop(dead);
        self.charge_tables();
    }

    /// Charges the work lists and tables outside the region for what they hold now. They grow
    /// within collections, which can't fail, so they're charged after.
    fn charge_tables(&self) {
        let m = &self.meta;
        let work = m.work.borrow();
        let bytes = (work.gray.capacity() + work.holders.capacity() + work.ephemerons.capacity()) * size_of::<u32>()
            + work.fixups.capacity() * size_of::<(u32, u32)>()
            + m.hosts.borrow().capacity() * size_of::<HostSlot>()
            + m.free_hosts.borrow().capacity() * size_of::<u32>()
            + m.dead_hosts.borrow().capacity() * size_of::<Box<dyn Any>>()
            + m.stacks.borrow().capacity() * size_of::<Rc<StackRecord>>();
        let before = m.tables.replace(bytes);
        if bytes > before {
            m.budget.force(bytes - before);
        } else {
            m.budget.refund(before - bytes);
        }
    }

    /// Once a collection has swept everything: keeps a nursery's worth of free pages, which
    /// the next steps would fill again, gives the rest back to the system, and trims the pages
    /// handed out to the last one kept.
    fn settle(&mut self) {
        let m = &self.meta;
        if m.phase.get() != Phase::Idle || !m.settle.replace(false) {
            return;
        }
        let mut warm = m.nursery / (PAGE * 8);
        let mut kept = 0;
        let mut run: Option<usize> = None;
        for p in 1..=m.used.get() {
            let release = m.pages[..m.used.get()].get(p).is_some_and(|page| {
                if page.used.get() != 0 {
                    kept = p;
                    return false;
                }
                if page.released.get() {
                    return false;
                }
                if warm > 0 {
                    warm -= 1;
                    kept = p;
                    return false;
                }
                page.released.set(true);
                m.budget.refund(PAGE_COST);
                true
            });
            match (release, run) {
                (true, None) => run = Some(p),
                (false, Some(first)) => {
                    self.memory.release(first * PAGE..p * PAGE);
                    run = None;
                }
                _ => {}
            }
        }
        let used = (kept + 1).min(m.used.get());
        m.used.set(used);
        m.occupied.set(m.pages[..used].iter().filter(|p| p.used.get() != 0).count());
    }

    pub fn mutate<R>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> R {
        f(&Mutation { heap: self.heap(), _brand: PhantomData })
    }

    /// Like `mutate`, then paces collection: a minor collection once the nursery fills, a major
    /// cycle once the pages in use after a sweep reach the threshold, twice what the last
    /// cycle left, and a slice of it after each step, twice what the step allocated.
    ///
    /// If `f` drew on the reserve, a full collection runs instead. If an allocation failed,
    /// even one `f` went on without, the result is dropped, a full collection runs, and the
    /// step fails. Whatever `f` did before the failure stays done, so the caller picks up from
    /// there: an interpreter runs the failed instruction again.
    pub fn step<R>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> Result<R, OutOfMemory> {
        self.meta.budget.clear_failed();
        let before = self.meta.young.get();
        let result = self.mutate(f);
        if self.meta.budget.failed() {
            drop(result);
            self.collect();
            return Err(OutOfMemory);
        }
        if self.meta.budget.due() {
            self.collect();
            return Ok(result);
        }
        let allocated = self.meta.young.get().saturating_sub(before);
        if let Some(work) = self.meta.stress.get() {
            self.heap().minor();
            self.heap().start();
            self.heap().work(work);
            self.finish();
            return Ok(result);
        }
        let m = &self.meta;
        if m.phase.get() == Phase::Idle && m.young.get() >= m.nursery {
            self.collect_minor();
        }
        let m = &self.meta;
        if m.phase.get() == Phase::Idle && m.occupied.get() * PAGE * 8 >= m.threshold.get() {
            if m.young.get() > 0 {
                self.collect_minor();
            }
            self.heap().start();
        }
        if self.meta.phase.get() != Phase::Idle {
            self.heap().work(allocated.saturating_mul(STEP_MUL).max(MIN_SLICE));
        }
        self.finish();
        Ok(result)
    }

    /// Finishes any cycle in progress, then runs a full one.
    pub fn collect(&mut self) {
        self.heap().work(usize::MAX);
        self.heap().start();
        self.heap().work(usize::MAX);
        self.finish();
        self.meta.budget.clear_due();
    }

    /// Collects young objects only, if no major cycle is running.
    pub fn collect_minor(&mut self) {
        self.heap().minor();
        self.finish();
    }

    /// Starts a cycle if none is running, then does about `work` bytes of it.
    pub fn collect_slice(&mut self, work: usize) {
        self.heap().start();
        self.heap().work(work);
        self.finish();
    }

    pub fn phase(&self) -> Phase {
        self.meta.phase.get()
    }

    pub fn collections(&self) -> (u64, u64) {
        (self.meta.collections.get(), self.meta.minors.get())
    }

    /// Bytes of pages handed out so far: the most the arena has used at once.
    pub fn pages_bytes(&self) -> usize {
        (self.meta.used.get() - 1) * PAGE * 8
    }

    /// Bytes of pages handed out and not given back: about what the arena holds in memory.
    pub fn committed_bytes(&self) -> usize {
        let m = &self.meta;
        let pages = &m.pages[1..m.used.get()];
        (pages.len() - pages.iter().filter(|p| p.released.get()).count()) * PAGE * 8
    }

    /// Bytes of pages holding something, as of the last sweep.
    pub fn occupied_bytes(&self) -> usize {
        self.meta.occupied.get() * PAGE * 8
    }

    pub fn hosts(&self) -> usize {
        self.meta.hosts.borrow().len()
    }

    /// Bytes charged against the limit: committed pages, roots, stacks, host values, the
    /// collector's tables, and `Charge`s.
    pub fn used(&self) -> usize {
        self.meta.budget.used()
    }

    pub fn peak(&self) -> usize {
        self.meta.budget.peak()
    }

    pub fn limit(&self) -> usize {
        self.meta.budget.limit()
    }

    /// Keeps the last `bytes` under the limit for a step to finish in once the rest is used.
    /// Optional allocations don't draw on it. It starts at a sixteenth of the limit.
    pub fn set_reserve(&mut self, bytes: usize) {
        self.meta.budget.set_reserve(bytes);
    }

    /// Testing: lets `allocations` more allocations through, then fails the next one, once.
    /// Objects, host values and stacks count.
    pub fn fail_after(&mut self, allocations: Option<u64>) {
        let m = &self.meta;
        m.budget.fail_after(allocations);
        m.end.set(if m.budget.injecting() { m.cursor.get() } else { m.hole_end.get() });
    }

    /// Testing: a minor collection and a cycle slice of `work` bytes after every step.
    pub fn set_stress(&mut self, work: Option<usize>) {
        self.meta.stress.set(work);
    }

    pub fn set_evacuate_all(&mut self, on: bool) {
        self.meta.evacuate_all.set(on);
    }
}

pub struct Mutation<'gc> {
    heap: Heap<'gc>,
    _brand: Brand<'gc>,
}

impl<'gc> Mutation<'gc> {
    #[inline]
    pub fn alloc<T: Object, const N: usize>(&self, fields: [u64; N]) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc_fixed(&T::DESC, &fields).map(Gc::new)
    }

    pub fn alloc_items<T: Object, const N: usize>(
        &self,
        fields: [u64; N],
        len: usize,
        item: Value<'gc>,
    ) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc(&T::DESC, &fields, len, item.word).map(Gc::new)
    }

    #[inline]
    pub fn type_tag<T: Object>(&self) -> Option<TypeTag<'gc, T>> {
        Some(TypeTag { ty: self.heap.type_index(&T::DESC)?, _marker: PhantomData })
    }

    pub fn root(&self, i: usize) -> Value<'gc> {
        Value::from_bits(self.heap.m.roots[i].get())
    }

    pub fn set_root(&self, i: usize, value: Value<'gc>) {
        self.heap.m.roots[i].set(value.word);
    }

    /// Charged its size, plus `HOST_COST`. Memory the value owns elsewhere, such as a
    /// `String`'s bytes, can be counted with a `Charge`.
    pub fn host<T: Any>(&self, value: T) -> Result<HostRef<'gc, T>, HostError> {
        let m = self.heap.m;
        let mut hosts = m.hosts.try_borrow_mut().map_err(|_| HostError::InUse)?;
        m.budget.count_allocation()?;
        let cost = size_of::<T>() + HOST_COST;
        m.budget.ensure(cost)?;
        // Made while marking, it lives through the cycle, as objects do.
        let marked = m.phase.get() == Phase::Marking;
        let value: Box<dyn Any> = Box::new(value);
        let id = match m.free_hosts.borrow_mut().pop() {
            Some(id) => id,
            None => {
                let Some(id) = u32::try_from(hosts.len()).ok().filter(|&id| id < u32::MAX) else {
                    return Err(m.budget.fail().into());
                };
                hosts.push(HostSlot { generation: 0, marked: false, cost: 0, value: None });
                id
            }
        };
        m.budget.force(cost);
        let slot = &mut hosts[id as usize];
        slot.value = Some(value);
        slot.marked = marked;
        slot.cost = cost;
        Ok(HostRef { id, generation: slot.generation, _marker: PhantomData })
    }

    /// Runs allocations the caller can do without, such as growing a buffer by more than it
    /// needs: failing them doesn't fail the step, and they don't draw on the reserve.
    pub fn optional<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        self.heap.m.budget.quiet(f)
    }

    /// Fails the step as a failed allocation would, for a request too large to even size.
    pub fn out_of_memory(&self) -> OutOfMemory {
        self.heap.m.budget.fail()
    }

    /// Whether an allocation has drawn on the reserve, so a full collection is due. An
    /// interpreter checks it between instructions and ends the step, which collects.
    pub fn collection_due(&self) -> bool {
        self.heap.m.budget.due()
    }

    /// A charge of nothing yet against the budget, for memory kept outside the arena.
    pub fn charge(&self) -> Charge<'gc> {
        Charge::new(self)
    }

    /// Whether `bytes` more fit, as an allocation of them would check.
    pub fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        self.heap.m.budget.ensure(bytes)
    }

    pub fn used(&self) -> usize {
        self.heap.m.budget.used()
    }

    pub fn limit(&self) -> usize {
        self.heap.m.budget.limit()
    }
}

impl<'a> Heap<'a> {
    #[inline]
    fn type_index(self, desc: &'static Desc) -> Option<u16> {
        let addr = (desc as *const Desc).addr();
        let (a, ty) = self.m.cache[(addr >> 4) % 64].get();
        if a == addr { Some(ty) } else { self.type_index_slow(desc) }
    }

    #[inline(never)]
    fn type_index_slow(self, desc: &'static Desc) -> Option<u16> {
        let addr = (desc as *const Desc).addr();
        let count = self.m.count.get();
        let same = |d: &'static Desc| std::ptr::eq(d, desc) || (d.type_id)() == (desc.type_id)();
        let ty = match (0..count).find(|&i| self.m.descs.get(i).and_then(Cell::get).is_some_and(same)) {
            Some(ty) => ty,
            None => {
                self.m.descs.get_or_grow(count)?.set(Some(desc));
                self.m.count.set(count + 1);
                count
            }
        };
        self.m.cache[(addr >> 4) % 64].set((addr, ty as u16));
        Some(ty as u16)
    }

    fn desc(self, header: u64) -> Option<&'static Desc> {
        self.m.descs.get((header & TYPE_BITS) as usize)?.get()
    }

    #[inline]
    fn alloc(self, desc: &'static Desc, fields: &[u64], len: usize, item: u64) -> Result<u32, OutOfMemory> {
        let ty = self.type_index(desc).ok_or_else(|| self.m.budget.fail())?;
        let len = if desc.items == Items::None { 0 } else { len };
        if len > u32::MAX as usize {
            return Err(self.m.budget.fail());
        }
        let size = 1 + desc.fields as usize + len;
        let at = self.reserve(size)?;
        let object = &self.words[at..at + size];
        object[0].set(u64::from(ty) | (len as u64) << 32);
        let (head, items) = object[1..].split_at(desc.fields as usize);
        for (slot, &word) in head.iter().zip(fields.iter().chain(std::iter::repeat(&0))) {
            slot.set(word);
        }
        for slot in items {
            slot.set(item);
        }
        self.m.young.set(self.m.young.get() + size * 8);
        if self.m.phase.get() == Phase::Marking {
            self.color_marked(at);
        }
        Ok(at as u32)
    }

    /// `alloc` without items: the common case, small enough to inline at every call site,
    /// which LLVM stops doing for `alloc` once there are a few dozen.
    #[inline(always)]
    fn alloc_fixed(self, desc: &'static Desc, fields: &[u64]) -> Result<u32, OutOfMemory> {
        let ty = self.type_index(desc).ok_or_else(|| self.m.budget.fail())?;
        let size = 1 + desc.fields as usize;
        let at = self.reserve(size)?;
        let object = &self.words[at..at + size];
        object[0].set(u64::from(ty));
        for (slot, &word) in object[1..].iter().zip(fields.iter().chain(std::iter::repeat(&0))) {
            slot.set(word);
        }
        self.m.young.set(self.m.young.get() + size * 8);
        if self.m.phase.get() == Phase::Marking {
            self.color_marked(at);
        }
        Ok(at as u32)
    }

    /// Objects made while marking are marked, and traced in case they were stored somewhere
    /// already traced.
    #[cold]
    fn color_marked(self, at: usize) {
        self.mark(at as u32, &mut self.m.work.borrow_mut());
    }

    #[inline]
    fn reserve(self, size: usize) -> Result<usize, OutOfMemory> {
        let at = self.m.cursor.get();
        let at = if at + size <= self.m.end.get() {
            self.m.cursor.set(at + size);
            at
        } else {
            self.reserve_slow(size)?
        };
        self.set_bit(at, |p| &p.starts);
        Ok(at)
    }

    #[inline(never)]
    fn reserve_slow(self, size: usize) -> Result<usize, OutOfMemory> {
        let m = self.m;
        m.budget.count_allocation()?;
        // The hole still fits it if failures are injected, or just stopped being.
        let at = m.cursor.get();
        if at + size <= m.hole_end.get() {
            m.cursor.set(at + size);
            m.end.set(if m.budget.injecting() { at + size } else { m.hole_end.get() });
            return Ok(at);
        }
        if size > PAGE - LINE {
            // Its own run of free pages, its lines claimed so nothing else is put there.
            let n = size.div_ceil(PAGE);
            let first = match self.free_run(n, false)? {
                Some(first) => first,
                None => self.fresh_pages(n)?,
            };
            self.cover_lines(first * PAGE, size, |p| &p.used);
            self.m.pages[first..first + n].iter().for_each(|p| p.large.set(Some(first as u32)));
            return Ok(first * PAGE);
        }
        loop {
            let (start, end) = match self.next_hole()? {
                Some(hole) => hole,
                None => {
                    let page = self.fresh_pages(1)?;
                    m.pages[page].used.set(u128::MAX);
                    m.scan.set((page + 1) * LINES);
                    (page * PAGE, (page + 1) * PAGE)
                }
            };
            if end - start >= size {
                m.cursor.set(start + size);
                m.hole_end.set(end);
                m.end.set(if m.budget.injecting() { start + size } else { end });
                return Ok(start);
            }
        }
    }

    /// Claims the next run of free lines in the pages handed out.
    fn next_hole(self) -> Result<Option<(usize, usize)>, OutOfMemory> {
        let mut scan = self.m.scan.get();
        while scan < self.m.used.get() * LINES {
            let (page, line) = (scan / LINES, scan % LINES);
            self.sweep_before_use(page);
            let p = &self.m.pages[page];
            let used = p.used.get();
            let free = !used & (u128::MAX << line);
            // Filling pages chosen for evacuation would undo the compaction.
            if free == 0 || p.evacuating.get() {
                scan = (page + 1) * LINES;
                continue;
            }
            self.recommit(page..page + 1)?;
            let start = free.trailing_zeros() as usize;
            let end = (used & (u128::MAX << start)).trailing_zeros() as usize;
            p.used.set(used | (u128::MAX >> (LINES - end)) & (u128::MAX << start));
            self.m.scan.set(page * LINES + end);
            return Ok(Some((page * PAGE + start * LINE, page * PAGE + end * LINE)));
        }
        self.m.scan.set(scan);
        Ok(None)
    }

    /// Charges again for pages given back to the system, before they're used.
    fn recommit(self, pages: Range<usize>) -> Result<(), OutOfMemory> {
        let pages = &self.m.pages[pages];
        let released = pages.iter().filter(|p| p.released.get()).count();
        if released > 0 {
            self.m.budget.charge(released * PAGE_COST)?;
            pages.iter().for_each(|p| p.released.set(false));
        }
        Ok(())
    }

    /// The first of `n` free pages in a row among those handed out. Evacuation can't copy
    /// onto pages being evacuated.
    fn free_run(self, n: usize, evacuation: bool) -> Result<Option<usize>, OutOfMemory> {
        let mut run = 0;
        for p in 1..self.m.used.get() {
            self.sweep_before_use(p);
            let page = &self.m.pages[p];
            let free = page.used.get() == 0 && !(evacuation && page.evacuating.get());
            run = if free { run + 1 } else { 0 };
            if run == n {
                let first = p + 1 - n;
                self.recommit(first..p + 1)?;
                return Ok(Some(first));
            }
        }
        Ok(None)
    }

    fn fresh_pages(self, n: usize) -> Result<usize, OutOfMemory> {
        let first = self.m.used.get();
        if first + n > self.m.pages.len() {
            return Err(self.m.budget.fail());
        }
        self.m.budget.charge(n * PAGE_COST)?;
        self.m.used.set(first + n);
        // Nothing on them is from before the cycle, so a lazy sweep has nothing to do there.
        for p in &self.m.pages[first..first + n] {
            p.swept.set(true);
            p.released.set(false);
        }
        Ok(first)
    }

    /// Pages are swept before the allocator looks at them, so it never sees stale lines.
    #[inline]
    fn sweep_before_use(self, page: usize) {
        if self.m.phase.get() == Phase::Sweeping && !self.m.pages[page].swept.get() {
            self.sweep_page(page);
        }
    }

    fn reset_allocator(self) {
        self.m.cursor.set(0);
        self.m.end.set(0);
        self.m.hole_end.set(0);
        self.m.scan.set(LINES);
        self.m.young.set(0);
    }

    #[inline]
    fn set_bit(self, i: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) {
        let word = &bits(&self.m.pages[i / PAGE])[i % PAGE / 64];
        word.set(word.get() | 1 << (i % 64));
    }

    fn has_bit(self, i: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) -> bool {
        self.m.pages.get(i / PAGE).is_some_and(|p| bits(p)[i % PAGE / 64].get() & 1 << (i % 64) != 0)
    }

    /// Sets the lines under `size` words at `start` in one of a page's line maps.
    fn cover_lines(self, start: usize, size: usize, lines: impl Fn(&Page) -> &Cell<u128>) {
        let (mut at, end) = (start, start + size);
        while at < end {
            let Some(page) = self.m.pages.get(at / PAGE) else { return };
            let to = end.min((at / PAGE + 1) * PAGE);
            let (first, last) = (at % PAGE / LINE, (to - 1) % PAGE / LINE);
            let lines = lines(page);
            lines.set(lines.get() | (u128::MAX >> (127 - last)) & (u128::MAX << first));
            at = to;
        }
    }

    #[inline]
    fn dirty(self, slot: usize) {
        if let Some(page) = self.m.pages.get(slot / PAGE) {
            page.cards.set(page.cards.get() | 1 << (slot % PAGE / CARD));
        }
    }

    /// Marks the host a word names, if its generation still matches.
    fn mark_host(self, word: u64) {
        let Some((id, generation)) = host_parts(word) else { return };
        if let Some(host) = self.m.hosts.borrow_mut().get_mut(id as usize).filter(|h| h.generation == generation) {
            host.marked = true;
        }
    }

    #[inline]
    fn ephemeron_at(self, slot: usize) -> Option<(Value<'a>, Value<'a>)> {
        let key = Value::from_bits(self.words[slot].get());
        (key != Value::BROKEN).then(|| (key, Value::from_bits(self.words[slot + 1].get())))
    }

    /// Neither part is shaded while marking: the value is traced once the key is found live.
    /// The cards are dirtied, so a minor collection sees both.
    #[inline]
    fn set_ephemeron_at(self, slot: usize, key: Value<'_>, value: Value<'_>) {
        self.words[slot].set(key.word);
        self.words[slot + 1].set(value.word);
        self.dirty(slot);
        self.dirty(slot + 1);
    }

    #[inline]
    fn barrier(self, slot: usize, owner: u32, word: u64) {
        if word & TAG == OBJECT {
            self.barrier_ref(slot, owner, (word >> 32) as u32);
        }
    }

    #[inline]
    fn barrier_ref(self, slot: usize, owner: u32, target: u32) {
        self.dirty(slot);
        if self.m.phase.get() == Phase::Marking && self.has_bit(owner as usize, |p| &p.marks) {
            shade(self.words, self.m, slot, owner, target);
        }
    }

    /// While marking, a store into a marked object marks its target, and if the target is to
    /// move, notes the slot to fix.
    fn shade(self, slot: usize, owner: u32, target: u32) {
        if self.has_bit(owner as usize, |p| &p.marks) {
            self.shade_marked(slot, owner, target);
        }
    }

    fn shade_marked(self, slot: usize, owner: u32, target: u32) {
        let mut work = self.m.work.borrow_mut();
        self.mark(target, &mut work);
        if self.m.evacuating.get() && self.in_evacuation(target) {
            work.fixups.push((owner, (slot - owner as usize) as u32));
        }
    }

    fn barrier_range(self, at: usize, slots: &[Cell<u64>], owner: u32) {
        let (mut i, end) = (at, at + slots.len());
        while i < end {
            let Some(page) = self.m.pages.get(i / PAGE) else { return };
            let to = end.min((i / PAGE + 1) * PAGE);
            let (first, last) = (i % PAGE / CARD, (to - 1) % PAGE / CARD);
            page.cards.set(page.cards.get() | ((u64::MAX >> (63 - last)) & (u64::MAX << first)) as u32);
            i = to;
        }
        if self.m.phase.get() == Phase::Marking {
            for (k, slot) in slots.iter().enumerate() {
                let word = slot.get();
                if word & TAG == OBJECT {
                    self.shade(at + k, owner, (word >> 32) as u32);
                }
            }
        }
    }

    fn in_evacuation(self, index: u32) -> bool {
        self.m.pages.get(index as usize / PAGE).is_some_and(|p| p.evacuating.get())
    }

    // Collection.

    /// Collects young objects only. Survivors stay marked, which makes them old.
    fn minor(self) {
        if self.m.phase.get() != Phase::Idle {
            return;
        }
        let mut work = std::mem::take(&mut *self.m.work.borrow_mut());
        self.mark_roots(&mut work);
        self.scan_cards(&mut work);
        self.drain(&mut work, usize::MAX);
        self.trace_ephemerons(&mut work);
        self.clear_weaks(&mut work);
        work.holders.clear();
        work.ephemerons.clear();
        self.sweep();
        self.reset_allocator();
        self.m.settle.set(true);
        self.m.minors.set(self.m.minors.get() + 1);
        *self.m.work.borrow_mut() = work;
    }

    /// Starts a major cycle: clears the marks and marks the roots.
    fn start(self) {
        let m = self.m;
        if m.phase.get() != Phase::Idle {
            return;
        }
        // Pages at most a quarter in use are evacuated while half the free room covers them, as
        // in `ragwort-gc`. Pages of large objects stay.
        let pages = &m.pages[..m.used.get()];
        let all = m.evacuate_all.get();
        let occupied: usize = pages.iter().map(|p| p.used.get().count_ones() as usize * LINE).sum();
        let mut room = (m.budget.limit() / 8).saturating_sub(occupied) / 2;
        let mut count = 0;
        for page in pages {
            page.marks.iter().for_each(|w| w.set(0));
            page.lines.set(0);
            page.cards.set(0);
            let used = page.used.get().count_ones() as usize * LINE;
            let candidate = page.large.get().is_none() && used > 0 && (all || (used <= PAGE / 4 && used <= room));
            if candidate {
                room = room.saturating_sub(used);
                count += 1;
            }
            page.evacuating.set(candidate);
        }
        let evacuating = count > 1 || all && count > 0;
        if !evacuating {
            pages.iter().for_each(|p| p.evacuating.set(false));
        }
        m.hosts.borrow_mut().iter_mut().for_each(|h| h.marked = false);
        m.evacuating.set(evacuating);
        m.to_cursor.set(0);
        m.to_end.set(0);
        m.phase.set(Phase::Marking);
        let mut work = std::mem::take(&mut *m.work.borrow_mut());
        work.fixups.clear();
        work.holders.clear();
        work.ephemerons.clear();
        self.mark_roots(&mut work);
        *m.work.borrow_mut() = work;
    }

    /// Does about `budget` bytes of the cycle: marking, the atomic phase once nothing is left
    /// to mark, then sweeping.
    fn work(self, budget: usize) {
        let mut left = budget;
        if self.m.phase.get() == Phase::Marking {
            let mut work = std::mem::take(&mut *self.m.work.borrow_mut());
            match self.drain(&mut work, left) {
                Some(rest) => {
                    self.atomic(&mut work);
                    left = rest;
                }
                None => left = 0,
            }
            *self.m.work.borrow_mut() = work;
        }
        if self.m.phase.get() == Phase::Sweeping {
            let mut cursor = self.m.sweep_cursor.get();
            while left > 0 && cursor < self.m.used.get() {
                if !self.m.pages[cursor].swept.get() {
                    self.sweep_page(cursor);
                    left = left.saturating_sub(SWEEP_COST);
                }
                cursor += 1;
            }
            self.m.sweep_cursor.set(cursor);
            if cursor >= self.m.used.get() {
                self.finish_cycle();
            }
        }
    }

    /// Traces gray objects until `budget` bytes are done. Returns the budget left once none
    /// remain.
    fn drain(self, work: &mut Work, budget: usize) -> Option<usize> {
        let mut left = budget;
        while left > 0 {
            let Some(i) = work.gray.pop() else { return Some(left) };
            left = left.saturating_sub(self.trace(i as usize, work) * 8);
        }
        work.gray.is_empty().then_some(0)
    }

    /// Ends marking: rescans the roots, which take no barrier, clears dead weak references,
    /// moves the objects being evacuated, and frees dead hosts. Sweeping comes after.
    fn atomic(self, work: &mut Work) {
        let m = self.m;
        self.mark_roots(work);
        self.drain(work, usize::MAX);
        self.trace_ephemerons(work);
        self.clear_weaks(work);
        if m.evacuating.get() {
            self.evacuate(work);
        }
        let mut free = m.free_hosts.borrow_mut();
        let mut dead = m.dead_hosts.borrow_mut();
        for (id, host) in m.hosts.borrow_mut().iter_mut().enumerate() {
            if !host.marked && let Some(value) = host.value.take() {
                dead.push(value);
                m.budget.refund(std::mem::take(&mut host.cost));
                // A slot whose generation would wrap is retired instead.
                if let Some(next) = host.generation.checked_add(1) {
                    host.generation = next;
                    free.push(id as u32);
                }
            }
        }
        drop((free, dead));
        for page in &m.pages[..m.used.get()] {
            page.cards.set(0);
            page.evacuating.set(false);
            page.swept.set(false);
        }
        self.reset_allocator();
        m.evacuating.set(false);
        m.sweep_cursor.set(0);
        m.phase.set(Phase::Sweeping);
        work.fixups.clear();
        work.holders.clear();
        work.ephemerons.clear();
    }

    fn finish_cycle(self) {
        let m = self.m;
        self.count_occupied();
        let size = m.occupied.get() * PAGE * 8;
        let limit = m.budget.limit();
        m.threshold.set((size * 2).max(MIN_THRESHOLD).min(size + limit.saturating_sub(size) / 2));
        m.phase.set(Phase::Idle);
        m.settle.set(true);
        m.collections.set(m.collections.get() + 1);
    }

    fn count_occupied(self) {
        let pages = &self.m.pages[..self.m.used.get()];
        self.m.occupied.set(pages.iter().filter(|p| p.used.get() != 0).count());
    }

    fn mark_roots(self, work: &mut Work) {
        for root in &self.m.roots {
            self.visit(root, work);
        }
        let mut stacks = self.m.stacks.borrow_mut();
        for stack in stacks.iter() {
            stack.trace(self, work);
        }
        // A dropped stack, traced once more for what it wrote, is done with.
        let before = stacks.len();
        stacks.retain(|s| Rc::strong_count(s) > 1);
        self.m.budget.refund((before - stacks.len()) * STACK_COST);
    }

    /// Sweeps every page at once, for a minor collection.
    fn sweep(self) {
        for p in 0..self.m.used.get() {
            self.m.pages[p].cards.set(0);
            self.sweep_page(p);
        }
        self.count_occupied();
    }

    /// Frees what wasn't marked and gives the allocator the lines that were.
    fn sweep_page(self, p: usize) {
        let page = &self.m.pages[p];
        for (s, k) in page.starts.iter().zip(&page.marks) {
            s.set(s.get() & k.get());
        }
        let lines = page.lines.get();
        page.used.set(lines);
        // Its last page can hold small objects that outlive it.
        if lines == 0 || page.large.get().is_some_and(|first| !self.has_bit(first as usize * PAGE, |p| &p.marks)) {
            page.large.set(None);
        }
        page.swept.set(true);
    }

    /// Clears weak fields whose targets weren't marked.
    fn clear_weaks(self, work: &mut Work) {
        for &holder in &work.holders {
            let i = holder as usize;
            let Some(desc) = self.words.get(i).and_then(|h| self.desc(h.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(i + 1 + bits.trailing_zeros() as usize) {
                    let target = slot.get() as u32;
                    if target != 0 && !self.has_bit(target as usize, |p| &p.marks) {
                        slot.set(0);
                    }
                }
                bits &= bits - 1;
            }
        }
        for &holder in &work.ephemerons {
            self.each_ephemeron(holder as usize, |key, value| {
                if !self.key_live(key.get()) {
                    key.set(Value::BROKEN.word);
                    value.set(Value::BROKEN.word);
                }
            });
        }
    }

    /// Calls `f` with the key and value slots of each ephemeron in the object at `i`.
    fn each_ephemeron(self, i: usize, mut f: impl FnMut(&'a Cell<u64>, &'a Cell<u64>)) {
        let Some(header) = self.words.get(i).map(Cell::get) else { return };
        let Some(desc) = self.desc(header).filter(|d| d.has_ephemerons()) else { return };
        let fields = desc.fields as usize;
        let mut bits = desc.ephemerons;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if k + 1 < fields
                && let Some([key, value]) = self.words.get(i + 1 + k..i + 3 + k).and_then(|p| p.as_array())
            {
                f(key, value);
            }
            bits &= bits - 1;
        }
        if desc.items == Items::Ephemerons {
            let len = (header >> 32) as usize;
            for [key, value] in self.words.get(i + 1 + fields..i + 1 + fields + len).unwrap_or(&[]).as_chunks().0 {
                f(key, value);
            }
        }
    }

    /// Whether an ephemeron's key is reachable: marked, or not an object.
    fn key_live(self, word: u64) -> bool {
        word & TAG != OBJECT || self.has_bit((word >> 32) as usize, |p| &p.marks)
    }

    /// Marks the values of ephemerons whose keys are marked, and what they reach, until a pass
    /// finds no more.
    fn trace_ephemerons(self, work: &mut Work) {
        loop {
            let mut marked = false;
            let mut h = 0;
            while let Some(&holder) = work.ephemerons.get(h) {
                self.each_ephemeron(holder as usize, |key, value| {
                    let word = value.get();
                    if word & TAG == OBJECT && self.key_live(key.get()) {
                        marked |= self.mark((word >> 32) as u32, work);
                    }
                });
                h += 1;
            }
            if !marked {
                return;
            }
            self.drain(work, usize::MAX);
        }
    }

    #[inline]
    fn visit(self, slot: &Cell<u64>, work: &mut Work) {
        let word = slot.get();
        if word & TAG == OBJECT {
            self.mark((word >> 32) as u32, work);
        }
    }

    /// Marks the object at `index` and queues it to be traced. An index that isn't an
    /// object's is left alone.
    /// Returns whether it wasn't marked before.
    fn mark(self, index: u32, work: &mut Work) -> bool {
        let i = index as usize;
        let Some(page) = self.m.pages.get(i / PAGE) else { return false };
        let (marks, bit) = (&page.marks[i % PAGE / 64], 1 << (i % 64));
        if marks.get() & bit != 0 || page.starts[i % PAGE / 64].get() & bit == 0 {
            return false;
        }
        let Some(desc) = self.desc(self.words[i].get()) else { return false };
        marks.set(marks.get() | bit);
        self.cover_lines(i, desc.size(self.words[i].get()), |p| &p.lines);
        if desc.traces() {
            work.gray.push(index);
        }
        true
    }

    /// Marks what the object refers to. Returns its size in words.
    fn trace(self, i: usize, work: &mut Work) -> usize {
        self.trace_parts(i, work, true)
    }

    /// Traces the object's fields, and its items if `items`.
    #[inline(always)]
    fn trace_parts(self, i: usize, work: &mut Work, items: bool) -> usize {
        let Some(header) = self.words.get(i).map(Cell::get) else { return 1 };
        let Some(desc) = self.desc(header) else { return 1 };
        let evacuating = self.m.evacuating.get();
        let fields = self.words.get(i + 1..i + 1 + desc.fields as usize).unwrap_or(&[]);
        let note = |work: &mut Work, at: usize, target: u32| {
            if evacuating && self.in_evacuation(target) {
                work.fixups.push((i as u32, at as u32 + 1));
            }
        };
        let mut bits = desc.values;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(k) {
                let word = slot.get();
                if word & TAG == OBJECT {
                    self.mark((word >> 32) as u32, work);
                    note(work, k, (word >> 32) as u32);
                }
            }
            bits &= bits - 1;
        }
        let mut bits = desc.members;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(k) {
                let target = slot.get() as u32;
                if target != 0 {
                    self.mark(target, work);
                    note(work, k, target);
                }
            }
            bits &= bits - 1;
        }
        if desc.has_ephemerons() {
            work.ephemerons.push(i as u32);
            // Values whose keys are marked already; the rest wait for `trace_ephemerons`.
            self.each_ephemeron(i, |key, value| {
                if self.key_live(key.get()) {
                    self.visit(value, work);
                }
            });
        }
        if desc.weaks != 0 {
            work.holders.push(i as u32);
            let mut bits = desc.weaks;
            while bits != 0 {
                let k = bits.trailing_zeros() as usize;
                if let Some(target) = fields.get(k).map(|s| s.get() as u32).filter(|&t| t != 0) {
                    note(work, k, target);
                }
                bits &= bits - 1;
            }
        }
        let mut bits = desc.hosts;
        while bits != 0 {
            if let Some(slot) = fields.get(bits.trailing_zeros() as usize) {
                self.mark_host(slot.get());
            }
            bits &= bits - 1;
        }
        let mut size = 1 + desc.fields as usize;
        if desc.items != Items::None {
            let len = (header >> 32) as usize;
            size += len;
            if items && desc.items == Items::Values {
                let start = desc.fields as usize;
                for (j, slot) in self.words.get(i + 1 + start..i + 1 + start + len).unwrap_or(&[]).iter().enumerate() {
                    let word = slot.get();
                    if word & TAG == OBJECT {
                        self.mark((word >> 32) as u32, work);
                        note(work, start + j, (word >> 32) as u32);
                    }
                }
            }
        }
        size
    }

    /// Moves the marked objects off the pages being evacuated, then fixes every reference
    /// to them: the roots and stacks, which are rescanned, and the slots noted while marking.
    fn evacuate(self, work: &mut Work) {
        let used = self.m.used.get();
        for p in 0..used {
            let page = &self.m.pages[p];
            if !page.evacuating.get() {
                continue;
            }
            for (k, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    self.move_object(p * PAGE + k * 64 + live.trailing_zeros() as usize);
                    live &= live - 1;
                }
            }
        }
        for root in &self.m.roots {
            self.fix_value(root);
        }
        for stack in self.m.stacks.borrow().iter() {
            stack.fix(self);
        }
        for &(owner, at) in &work.fixups {
            let o = self.resolve(owner) as usize;
            let Some(desc) = self.words.get(o).and_then(|h| self.desc(h.get())) else { continue };
            let Some(slot) = self.words.get(o + at as usize) else { continue };
            let field = at as usize - 1;
            let bit = if field < 64 { 1 << field } else { 0 };
            if field >= desc.fields as usize || desc.values & bit != 0 {
                self.fix_value(slot);
            } else if (desc.members | desc.weaks) & bit != 0 {
                let target = slot.get() as u32;
                slot.set(slot.get() & !0xFFFF_FFFF | u64::from(self.resolve(target)));
            }
        }
        for &holder in &work.holders {
            let o = self.resolve(holder) as usize;
            let Some(desc) = self.words.get(o).and_then(|h| self.desc(h.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(o + 1 + bits.trailing_zeros() as usize) {
                    slot.set(slot.get() & !0xFFFF_FFFF | u64::from(self.resolve(slot.get() as u32)));
                }
                bits &= bits - 1;
            }
        }
        for &holder in &work.ephemerons {
            self.each_ephemeron(self.resolve(holder) as usize, |key, value| {
                self.fix_value(key);
                self.fix_value(value);
            });
        }
        // Objects that didn't fit in fresh pages stay, so their lines are found again.
        for page in &self.m.pages[..used] {
            if page.evacuating.get() {
                page.lines.set(0);
            }
        }
        for p in 0..used {
            let page = &self.m.pages[p];
            if !page.evacuating.get() {
                continue;
            }
            for (k, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    let i = p * PAGE + k * 64 + live.trailing_zeros() as usize;
                    if let Some(desc) = self.desc(self.words[i].get()) {
                        self.cover_lines(i, desc.size(self.words[i].get()), |p| &p.lines);
                    }
                    live &= live - 1;
                }
            }
        }
    }

    /// Copies a marked object to a fresh page and leaves a forwarding header. The copy is
    /// marked; the original isn't, so the sweep frees it.
    fn move_object(self, i: usize) {
        let header = self.words[i].get();
        let Some(desc) = self.desc(header) else { return };
        let size = desc.size(header);
        let Some(new) = self.to_reserve(size) else { return };
        let (Some(from), Some(to)) = (self.words.get(i..i + size), self.words.get(new..new + size)) else { return };
        for (d, s) in to.iter().zip(from) {
            d.set(s.get());
        }
        self.set_bit(new, |p| &p.starts);
        self.set_bit(new, |p| &p.marks);
        self.cover_lines(new, size, |p| &p.lines);
        self.words[i].set((new as u64) << 32 | FORWARDED | header & TYPE_BITS);
        let marks = &self.m.pages[i / PAGE].marks[i % PAGE / 64];
        marks.set(marks.get() & !(1 << (i % 64)));
    }

    fn to_reserve(self, size: usize) -> Option<usize> {
        let at = self.m.to_cursor.get();
        if at + size <= self.m.to_end.get() {
            self.m.to_cursor.set(at + size);
            return Some(at);
        }
        // An object that finds no room stays where it is.
        let n = size.div_ceil(PAGE);
        let first = self.m.budget.quiet(|| self.free_run(n, true)?.map_or_else(|| self.fresh_pages(n), Ok)).ok()?;
        // Claimed until the sweep sets them from what's marked.
        self.m.pages[first..first + n].iter().for_each(|p| p.used.set(u128::MAX));
        let start = first * PAGE;
        self.m.to_cursor.set(start + size);
        self.m.to_end.set(start + n * PAGE);
        Some(start)
    }

    /// Where the object at `index` is now.
    fn resolve(self, index: u32) -> u32 {
        let i = index as usize;
        match self.words.get(i).map(Cell::get) {
            Some(header) if header & FORWARDED != 0 && self.has_bit(i, |p| &p.starts) => (header >> 32) as u32,
            _ => index,
        }
    }

    fn fix_value(self, slot: &Cell<u64>) {
        let word = slot.get();
        if word & TAG == OBJECT {
            let new = self.resolve((word >> 32) as u32);
            slot.set(word & 0xFFFF_FFFF | u64::from(new) << 32);
        }
    }

    /// Traces the old objects that overlap dirty cards, for a minor collection.
    fn scan_cards(self, work: &mut Work) {
        let mut last = usize::MAX;
        for page in 0..self.m.used.get() {
            let mut cards = self.m.pages[page].cards.get();
            while cards != 0 {
                let card = cards.trailing_zeros() as usize;
                cards &= cards - 1;
                let (from, to) = (page * PAGE + card * CARD, page * PAGE + (card + 1) * CARD);
                let mut next = self.start_at_or_before(from).or_else(|| self.next_start(from, to));
                while let Some(object) = next.filter(|&o| o < to) {
                    if self.has_bit(object, |p| &p.marks) {
                        self.trace_card(object, from..to, object != last, work);
                        last = object;
                    }
                    // Nothing starts between the object found before the card and the card.
                    next = self.next_start((object + 1).max(from), to);
                }
            }
        }
    }

    /// Traces what an old object on a dirty card refers to: for items of values, only those on
    /// the card, so storing into a large vector doesn't rescan all of it. The rest of the
    /// object is traced once, for its first card.
    fn trace_card(self, i: usize, card: Range<usize>, first: bool, work: &mut Work) {
        let header = self.words[mask(i)].get();
        let Some(desc) = self.desc(header) else { return };
        if desc.items != Items::Values {
            if first {
                self.trace(i, work);
            }
            return;
        }
        if first {
            self.trace_parts(i, work, false);
        }
        let items = i + 1 + desc.fields as usize;
        let end = items + (header >> 32) as usize;
        for slot in self.words.get(card.start.max(items)..card.end.min(end)).unwrap_or(&[]) {
            self.visit(slot, work);
        }
    }

    fn start_at_or_before(self, i: usize) -> Option<usize> {
        let (mut page, mut word) = (i / PAGE, i % PAGE / 64);
        let mut mask = u64::MAX >> (63 - i % 64);
        loop {
            let starts = self.m.pages[page].starts[word].get() & mask;
            if starts != 0 {
                return Some(page * PAGE + word * 64 + 63 - starts.leading_zeros() as usize);
            }
            mask = u64::MAX;
            if word > 0 {
                word -= 1;
            } else if let Some(first) = self.m.pages[page].large.get().map(|f| f as usize).filter(|&f| f < page) {
                // Nothing starts between the large object's header and its pages' end.
                (page, word) = (first, 0);
            } else if page > 0 {
                (page, word) = (page - 1, PAGE / 64 - 1);
            } else {
                return None;
            }
        }
    }

    fn next_start(self, from: usize, to: usize) -> Option<usize> {
        let mut i = from;
        while i < to {
            let (page, word) = (i / PAGE, i % PAGE / 64);
            let starts = self.m.pages.get(page)?.starts[word].get() & (u64::MAX << (i % 64));
            if starts != 0 {
                return Some(page * PAGE + word * 64 + starts.trailing_zeros() as usize).filter(|&s| s < to);
            }
            i = (i / 64 + 1) * 64;
        }
        None
    }
}

/// The barrier's slow path. It takes the heap's parts rather than a `Heap`, which is too big to
/// pass in registers: the caller would copy it to the stack on every store, slow path or not.
#[cold]
#[inline(never)]
fn shade(words: &[Cell<u64>; WORDS + SLACK], m: &Meta, slot: usize, owner: u32, target: u32) {
    Heap { words, m }.shade_marked(slot, owner, target);
}
