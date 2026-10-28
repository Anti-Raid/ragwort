//! Compaction: moving objects off sparse pages and rewriting references to them.

use std::ptr;

use crate::layout::{Addr, FORWARDED, GRANULE, LINE, PAGE};
use crate::trace::Mode;
use crate::Trace;
use super::object::Obj;
use super::pages::{CANDIDATE, Kind, LINE_WORDS, PageIndex, each_bit};
use super::{Collecting, Heap};

impl Heap {
    /// Picks sparse pages to compact, while their used lines fit in half the free budget.
    /// A lone sparse page isn't worth it: its objects would only move to a page of their own.
    /// Returns whether any were picked.
    pub(super) fn choose_candidates(&self) -> bool {
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
        let evacuating = count > 1 || all && count > 0;
        if !evacuating {
            for p in self.pages() {
                p.remove(CANDIDATE);
            }
        }
        evacuating
    }

    fn each_candidate(&self, mut f: impl FnMut(PageIndex)) {
        let mut page = PageIndex::FIRST;
        while self.in_table(page) {
            if self.page(page).has(CANDIDATE) {
                f(page);
            }
            page = page.plus(1);
        }
    }

    /// Copies the marked objects off candidate pages while there's room, then rewrites every
    /// reference to them. Objects that don't fit stay where they are.
    pub(super) fn evacuate<R: Trace>(&self, root: &mut R, c: &Collecting) {
        self.each_candidate(|page| {
            each_bit(&self.page(page).live(), |g| self.move_object(page.granule(g)));
        });
        self.trace_roots(root, Mode::Fixup, c);
        self.scan_cards(Mode::Fixup);
        self.each_candidate(|page| {
            each_bit(&self.page(page).live(), |g| {
                if let Some(new) = self.forwarded(page.granule(g)) {
                    self.trace_object(new, Mode::Fixup, None);
                }
            });
        });
        self.each_candidate(|page| {
            let p = self.page(page);
            p.remove(CANDIDATE);
            p.marked_lines.store([0; LINE_WORDS]);
            each_bit(&p.live(), |g| {
                let offset = page.granule(g);
                if self.moved(offset) {
                    // References to the old copy were all rewritten, so one left over is stale.
                    self.clear_header(offset);
                    p.start.clear(g);
                    p.mark.clear(g);
                    self.stats.objects.set(self.stats.objects.get() - 1);
                } else if let Some(obj) = self.object_at(offset)
                    && let Some((_, size)) = self.size_of(obj)
                {
                    let at = g * GRANULE;
                    p.marked_lines.set_range(at / LINE, (at + size).div_ceil(LINE));
                }
            });
        });
        self.done_evacuating();
    }

    fn move_object(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return self.corrupt() };
        let Some((_, size)) = self.size_of(obj) else { return self.corrupt() };
        let Ok(new) = self.budget.quiet(|| self.reserve(size)) else { return };
        let new_obj = self.object_at(new).expect("new object");
        // SAFETY: both are validated objects of `size` bytes, distinct since `new` was just
        // reserved, and nothing borrows arena memory during a collection.
        unsafe {
            ptr::copy_nonoverlapping(self.header_ptr(offset).cast::<u8>(), self.header_ptr(new).cast::<u8>(), size);
            let old = self.header_ptr(offset);
            (*old).flags |= FORWARDED;
            (*old).len = new;
        }
        self.mark_object(new_obj, size);
    }

    /// Remembers a slot pointing into a page being compacted, so it can be fixed up.
    pub(crate) fn note_slot(&self, target: u32, slot: Addr) {
        if self.is_evacuating()
            && let Some(slot) = self.offset_of(slot)
            && self.page_of(target as usize).is_some_and(|p| self.page(p).has(CANDIDATE))
        {
            self.dirty(slot);
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
        self.is_evacuating() && self.header(obj).flags & FORWARDED != 0
    }

    /// Whether the object starting at `offset`, which must have its start bit set, moved.
    pub(super) fn moved(&self, offset: u32) -> bool {
        self.object_at(offset).is_some_and(|obj| self.is_forwarded(obj))
    }
}
