//! Trusted page metadata, kept outside the region: what each page holds and its bitmaps.

use std::cell::Cell;

use crate::layout::{CARD, GRANULE, LINES, MAX_PAGES, PAGE, PAGE_SHIFT, WORDS};
use super::{Heap, Zeroed, zeroed};

/// The page table. It has room for every page from the start, so it never moves; `count`
/// are in use.
pub(super) struct Pages {
    table: Box<[Page; MAX_PAGES]>,
    count: Cell<usize>,
}

impl Pages {
    pub(super) fn new() -> Self {
        Self { table: zeroed(), count: Cell::new(0) }
    }

    /// Every page, in use or not.
    #[inline]
    pub(super) fn table(&self) -> &[Page; MAX_PAGES] {
        &self.table
    }

    #[inline]
    pub(super) fn set_count(&self, count: usize) {
        self.count.set(count);
    }
}

// SAFETY: `Kind` is `repr(u32)` with `Free` = 0, and the rest of a page is cells of integers.
unsafe impl Zeroed for [Page; MAX_PAGES] {}

/// What each page's metadata is charged.
pub(crate) const META: usize = size_of::<Page>();

// All-zero is `Free`, so the page table can start out as zeroed memory.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u32)]
pub(super) enum Kind {
    Free,
    /// Small objects, bump-allocated through free lines.
    Lines,
    /// The first page of a run holding one object.
    Large(u32),
    /// The other pages of a run, with the index of its first page.
    Tail(u32),
}

impl Kind {
    pub(super) const fn tail_of(head: PageIndex) -> Self {
        Self::Tail(head.0 as u32)
    }
}

/// A page's place in the page table. Region page 0 is never used, so offset 0 is null, and the
/// page at index `i` is region page `i + 1`. Only these methods convert between the two.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct PageIndex(usize);

impl PageIndex {
    pub(super) const FIRST: Self = Self(0);

    /// The page at `slot` in the table.
    #[inline]
    pub(super) const fn at(slot: usize) -> Self {
        Self(slot)
    }

    #[inline]
    pub(super) const fn slot(self) -> usize {
        self.0
    }

    /// The page holding region offset `offset`, unless that's page 0. It may be past the table.
    #[inline]
    pub(super) fn containing(offset: usize) -> Option<Self> {
        (offset >> PAGE_SHIFT).checked_sub(1).map(Self)
    }

    /// The pages that overlap region offsets `lo..hi`, as the first and the one past the last.
    pub(super) fn overlapping(lo: usize, hi: usize) -> (Self, Self) {
        let end = hi.div_ceil(PAGE).saturating_sub(1).min(MAX_PAGES);
        (Self::at((lo >> PAGE_SHIFT).saturating_sub(1).min(end)), Self::at(end))
    }

    #[inline]
    pub(super) const fn plus(self, n: usize) -> Self {
        Self(self.0 + n)
    }

    /// The region offset where the page starts.
    #[inline]
    pub(super) const fn start(self) -> usize {
        (self.0 + 1) << PAGE_SHIFT
    }

    /// The region offset of granule `granule` on the page.
    #[inline]
    pub(super) const fn granule(self, granule: usize) -> u32 {
        (self.start() + granule * GRANULE) as u32
    }

    /// The pages from this one up to, but not including, `end`.
    #[inline]
    pub(super) fn upto(self, end: Self) -> impl Iterator<Item = Self> + Clone {
        (self.0..end.0).map(Self)
    }
}

/// Holds objects allocated since the last collection.
pub(super) const YOUNG: u8 = 1;

/// Already swept in this major cycle. Only read while sweeping.
pub(super) const SWEPT: u8 = 2;

/// Being compacted in this major cycle.
pub(super) const CANDIDATE: u8 = 4;

/// Holds marked objects that didn't fit on the gray stack and still need tracing.
pub(super) const OVERFLOW: u8 = 8;

/// Holds an ephemeron whose key wasn't marked when it was traced.
pub(super) const PENDING: u8 = 16;

/// A free page whose memory wasn't given back to the OS, so reusing it doesn't fault. Pages
/// past the end of the table keep the flag, so growing the table back over them is warm too.
pub(super) const WARM: u8 = 32;

pub(super) const LINE_WORDS: usize = LINES / 64;

/// A bitmap in page metadata. Cells let the collector update a page while it traces
/// objects on it.
pub(super) struct Bits<const N: usize>([Cell<u64>; N]);

impl<const N: usize> Bits<N> {
    #[inline]
    pub(super) fn get(&self, i: usize) -> bool {
        self.from(i) & 1 != 0
    }

    /// The bits of `i`'s word from `i` up, with `i` as the lowest.
    #[inline]
    pub(super) fn from(&self, i: usize) -> u64 {
        self.0[i / 64].get() >> (i % 64)
    }

    #[inline]
    pub(super) fn set(&self, i: usize) {
        let word = &self.0[i / 64];
        word.set(word.get() | 1 << (i % 64));
    }

    #[inline]
    pub(super) fn clear(&self, i: usize) {
        let word = &self.0[i / 64];
        word.set(word.get() & !(1 << (i % 64)));
    }

    #[inline]
    pub(super) fn set_range(&self, from: usize, to: usize) {
        for i in from..to {
            self.set(i);
        }
    }

    #[inline]
    pub(super) fn clear_range(&self, from: usize, to: usize) {
        for i in from..to {
            self.clear(i);
        }
    }

    #[inline]
    pub(super) fn load(&self) -> [u64; N] {
        std::array::from_fn(|w| self.0[w].get())
    }

    #[inline]
    pub(super) fn store(&self, bits: [u64; N]) {
        for (word, bits) in self.0.iter().zip(bits) {
            word.set(bits);
        }
    }

    #[inline]
    pub(super) fn count(&self) -> usize {
        self.0.iter().map(|w| w.get().count_ones() as usize).sum()
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.0.iter().all(|w| w.get() == 0)
    }

    #[inline]
    pub(super) fn is_full(&self) -> bool {
        self.0.iter().all(|w| w.get() == !0)
    }

    /// Whether any bit in `from..to` is set. Both must be within the bitmap.
    #[inline]
    pub(super) fn any_in(&self, from: usize, to: usize) -> bool {
        if from >= to {
            return false;
        }
        let (first, last) = (from / 64, (to - 1) / 64);
        let low = u64::MAX << (from % 64);
        let high = u64::MAX >> (63 - (to - 1) % 64);
        if first == last {
            return self.0[first].get() & low & high != 0;
        }
        self.0[first].get() & low != 0
            || self.0[first + 1..last].iter().any(|w| w.get() != 0)
            || self.0[last].get() & high != 0
    }

    /// The highest set bit at or below `i`.
    #[inline]
    pub(super) fn prev(&self, i: usize) -> Option<usize> {
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

#[inline]
fn and<const N: usize>(a: [u64; N], b: [u64; N]) -> [u64; N] {
    std::array::from_fn(|w| a[w] & b[w])
}

/// Visits each set bit of `bits`.
#[inline]
pub(super) fn each_bit(bits: &[u64], mut f: impl FnMut(usize)) {
    for (w, &word) in bits.iter().enumerate() {
        let mut word = word;
        while word != 0 {
            f(w * 64 + word.trailing_zeros() as usize);
            word &= word - 1;
        }
    }
}

/// Trusted per-page metadata. Lives outside the region, so heap corruption can't reach it.
pub(super) struct Page {
    pub(super) kind: Cell<Kind>,
    pub(super) flags: Cell<u8>,
    /// Dirty 512-byte cards: slots written since the last collection.
    pub(super) cards: Cell<u32>,
    /// An object starts at each set granule.
    pub(super) start: Bits<WORDS>,
    pub(super) mark: Bits<WORDS>,
    /// Lines the allocator must not hand out.
    pub(super) used: Bits<LINE_WORDS>,
    /// Lines touched by marked objects.
    pub(super) marked_lines: Bits<LINE_WORDS>,
}

impl Page {
    pub(super) fn reset(&self) {
        self.kind.set(Kind::Free);
        self.flags.set(0);
        self.cards.set(0);
        self.start.store([0; WORDS]);
        self.mark.store([0; WORDS]);
        self.used.store([0; LINE_WORDS]);
        self.marked_lines.store([0; LINE_WORDS]);
    }

    #[inline]
    pub(super) fn has(&self, flag: u8) -> bool {
        self.flags.get() & flag != 0
    }

    #[inline]
    pub(super) fn add(&self, flag: u8) {
        self.flags.set(self.flags.get() | flag);
    }

    #[inline]
    pub(super) fn remove(&self, flag: u8) -> bool {
        let had = self.has(flag);
        self.flags.set(self.flags.get() & !flag);
        had
    }

    #[inline]
    pub(super) fn dirty(&self, in_page: usize) {
        self.cards.set(self.cards.get() | 1 << (in_page / CARD));
    }

    #[inline]
    pub(super) fn live(&self) -> [u64; WORDS] {
        and(self.start.load(), self.mark.load())
    }

    /// For a page run, the page holding the header.
    #[inline]
    pub(super) fn head(&self, page: PageIndex) -> PageIndex {
        match self.kind.get() {
            Kind::Tail(head) => PageIndex(head as usize),
            _ => page,
        }
    }
}

impl Heap {
    #[inline]
    pub(super) fn pages(&self) -> &[Page] {
        &self.pages.table[..self.pages.count.get()]
    }

    /// Any page of the table; callers keep to `page_count`.
    #[inline]
    pub(super) fn page(&self, page: PageIndex) -> &Page {
        &self.pages.table[page.slot()]
    }

    /// `n` pages in use, from `page`.
    #[inline]
    pub(super) fn run(&self, page: PageIndex, n: usize) -> &[Page] {
        &self.pages()[page.slot()..page.slot() + n]
    }

    /// The pages from `from` up to `to`, in use or not.
    pub(super) fn table_pages(&self, from: PageIndex, to: PageIndex) -> &[Page] {
        &self.pages.table[from.slot()..to.slot()]
    }

    #[inline]
    pub(crate) fn page_count(&self) -> usize {
        self.pages.count.get()
    }

    #[inline]
    pub(super) fn in_table(&self, page: PageIndex) -> bool {
        page.slot() < self.page_count()
    }

    /// The pages in use, as there are now.
    #[inline]
    pub(super) fn page_indexes(&self) -> impl Iterator<Item = PageIndex> + use<> {
        PageIndex::FIRST.upto(PageIndex::at(self.page_count()))
    }

    /// The page holding region offset `offset`.
    #[inline]
    pub(super) fn page_of(&self, offset: usize) -> Option<PageIndex> {
        let slot = (offset >> PAGE_SHIFT).checked_sub(1)?;
        (slot < self.page_count()).then_some(PageIndex(slot))
    }
}
