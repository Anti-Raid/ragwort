//! Write barriers and the dirty cards they leave for collections.

use std::mem;
use std::ops::Range;

use crate::layout::{Addr, CARD, CARDS, GRANULE, PAGE};
use crate::trace::Mode;
use crate::Tracer;
use super::pages::{Kind, PageIndex};
use super::{CorruptOnUnwind, Heap};

impl Heap {
    /// Whether the object holding the byte at `offset` is marked.
    #[inline]
    fn owner_marked(&self, offset: usize, page: PageIndex) -> bool {
        let p = self.page(page);
        match p.kind.get() {
            Kind::Lines => p.start.prev((offset % PAGE) / GRANULE).is_some_and(|g| p.mark.get(g)),
            Kind::Large(_) | Kind::Tail(_) => {
                let head = p.head(page);
                self.in_table(head) && self.page(head).mark.get(0)
            }
            Kind::Free => false,
        }
    }

    #[inline]
    pub(crate) fn write_barrier(&self, slot: Addr, shade: impl FnOnce(&mut Tracer<'_>)) {
        if let Some(offset) = self.offset_of(slot) {
            self.barrier_slow(offset, shade);
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

    /// Dirties the cards under `len` bytes at `offset`, so whatever was stored there gets
    /// traced by the next collection, like a write barrier for each slot.
    fn dirty_range(&self, offset: usize, len: usize) {
        let (mut at, end) = (offset, offset + len);
        while at < end {
            let Some(page) = self.page_of(at) else { return };
            let to = end.min(page.start() + PAGE);
            let (first, last) = ((at % PAGE) / CARD, ((to - 1) % PAGE) / CARD);
            let p = self.page(page);
            p.cards.set(p.cards.get() | ((u64::MAX >> (63 - last)) & (u64::MAX << first)) as u32);
            at = to;
        }
    }

    /// Has the object traced again before the next collection finishes. While marking, a
    /// marked object goes back on the gray stack, so incremental slices do the work.
    #[cfg(test)]
    pub(crate) fn retrace(&self, offset: u32) {
        if let Some(span) = self.object_span(offset) {
            self.retrace_part(offset, span);
        }
    }

    /// Like [`Heap::retrace`], but only `span`, region offsets inside the object, was written,
    /// so only the cards under it are dirtied.
    pub(crate) fn retrace_part(&self, offset: u32, span: Range<usize>) {
        let Some(obj) = self.object_at(offset) else { return };
        let Some((vtable, _)) = self.size_of(obj) else { return };
        self.dirty_range(span.start, span.len());
        if self.is_marking() && self.is_marked(obj) && vtable.needs_trace {
            self.push_gray(offset, obj.page);
        }
    }

    /// The barrier for a range of slots in one object: like a write barrier for each slot.
    pub(crate) fn barrier_range(&self, addr: Addr, len: usize, shade: impl FnOnce(&mut Tracer<'_>)) {
        let Some(offset) = self.offset_of(addr).filter(|_| len != 0) else { return };
        self.dirty_range(offset, len);
        if self.is_marking() && self.page_of(offset).is_some_and(|page| self.owner_marked(offset, page)) {
            let guard = CorruptOnUnwind(self);
            shade(&mut Tracer::new(self, Mode::Barrier));
            mem::forget(guard);
        }
    }

    #[inline]
    pub(super) fn dirty(&self, offset: usize) {
        if let Some(page) = self.page_of(offset) {
            self.page(page).dirty(offset % PAGE);
        }
    }

    /// Traces the marked objects that overlap dirty cards.
    pub(super) fn scan_cards(&self, mode: Mode) {
        for page in self.page_indexes() {
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
                            let offset = page.granule(g);
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
                        let from = page.start() - head.start() + card * CARD;
                        self.trace_object(head.start() as u32, mode, Some((from, from + CARD)));
                    }
                }
                Kind::Free => {}
            }
        }
    }

    pub(super) fn clear_cards(&self) {
        for p in self.pages() {
            p.cards.set(0);
        }
    }

    #[cfg(test)]
    pub(crate) fn dirty_cards(&self) -> u32 {
        self.pages().iter().map(|p| p.cards.get().count_ones()).sum()
    }
}
