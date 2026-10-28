//! Collection cycles: minor collections, and major ones in incremental slices.

use std::any::Any;
use std::mem;

use crate::layout::{PAGE, WORDS};
use crate::trace::Mode;
use crate::{Phase, Trace};
use super::pages::{Kind, LINE_WORDS, PageIndex, SWEPT, YOUNG};
#[cfg(any(test, feature = "gc-verify"))]
use super::pages::each_bit;
use super::{Collecting, CorruptOnUnwind, Heap};

const SWEEP_COST: usize = PAGE / 8;

/// Where the heap is in a major cycle.
#[derive(Clone, Copy)]
pub(super) enum State {
    Idle,
    /// `evacuating` until the objects on pages being compacted have moved.
    Marking { evacuating: bool },
    /// Pages before `cursor` are swept.
    Sweeping { cursor: PageIndex },
}

impl Heap {
    /// Collects young objects only. Survivors stay marked, which makes them old.
    pub(crate) fn minor<R: Trace>(&mut self, root: &mut R) {
        if self.phase() != Phase::Idle || self.corrupted.get() {
            return;
        }
        let c = &Collecting(());
        let guard = CorruptOnUnwind(self);
        self.reset_allocators();
        self.mark_all(root, c);
        if self.corrupted.get() {
            return mem::forget(guard);
        }
        self.clear_dead_ephemerons();
        self.clear_cards();
        let dropped = self.hosts.sweep(&self.budget);
        let mut page = PageIndex::FIRST;
        while self.in_table(page) {
            if self.page(page).has(YOUNG) {
                self.sweep_page(page);
            }
            page = page.plus(1);
        }
        self.stats.young.set(0);
        self.rescan();
        self.stats.minors.set(self.stats.minors.get() + 1);
        mem::forget(guard);
        drop(dropped);
    }

    pub(crate) fn start<R: Trace>(&mut self, root: &mut R) {
        if self.phase() != Phase::Idle || self.corrupted.get() {
            return;
        }
        let c = &Collecting(());
        let guard = CorruptOnUnwind(self);
        self.state.set(State::Marking { evacuating: false });
        self.reset_allocators();
        for p in self.pages() {
            p.mark.store([0; WORDS]);
            p.marked_lines.store([0; LINE_WORDS]);
        }
        self.hosts.clear_marks();
        // Cards dirtied since the last cycle only matter to minor collections; this one
        // traces everything from the roots.
        self.clear_cards();
        self.state.set(State::Marking { evacuating: self.choose_candidates() });
        self.trace_roots(root, Mode::Mark, c);
        mem::forget(guard);
    }

    /// Advances the current cycle by about `budget` bytes of work.
    pub(crate) fn work<R: Trace>(&mut self, root: &mut R, budget: usize) {
        let c = &Collecting(());
        let mut left = budget;
        let mut dropped = Vec::new();
        let guard = CorruptOnUnwind(self);
        while !self.corrupted.get() {
            match self.phase() {
                Phase::Idle => break,
                Phase::Marking => {
                    left = self.drain(left);
                    if self.corrupted.get() || left == 0 {
                        break;
                    }
                    let (values, work) = self.atomic(root, c);
                    dropped = values;
                    left = left.saturating_sub(work);
                    if left == 0 {
                        break;
                    }
                }
                Phase::Sweeping => {
                    // Sweeping can shrink the page table, which pulls the cursor back with it.
                    while left > 0
                        && let State::Sweeping { cursor: page } = self.state.get()
                        && self.in_table(page)
                    {
                        self.state.set(State::Sweeping { cursor: page.plus(1) });
                        if !self.page(page).has(SWEPT) {
                            self.sweep_page(page);
                            left = left.saturating_sub(SWEEP_COST);
                        }
                    }
                    if let State::Sweeping { cursor } = self.state.get()
                        && !self.in_table(cursor)
                    {
                        self.finish_cycle();
                    }
                    break;
                }
            }
        }
        mem::forget(guard);
        drop(dropped);
    }

    fn atomic<R: Trace>(&self, root: &mut R, c: &Collecting) -> (Vec<Box<dyn Any>>, usize) {
        let work = self.mark_all(root, c);
        if self.corrupted.get() {
            return (Vec::new(), work);
        }
        self.clear_dead_ephemerons();
        if self.is_evacuating() {
            self.evacuate(root, c);
            #[cfg(any(test, feature = "gc-verify"))]
            self.verify(root, c);
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
        self.stats.young.set(0);
        self.state.set(State::Sweeping { cursor: PageIndex::FIRST });
        (dropped, work)
    }

    fn sweep_page(&self, page: PageIndex) {
        let p = self.page(page);
        match p.kind.get() {
            Kind::Lines => {
                let start = p.start.load();
                let live = p.live();
                let dead: [u64; WORDS] = std::array::from_fn(|i| start[i] & !live[i]);
                // Wiping every dead header costs about 5% of young allocation, so only checked
                // builds do it. Their stale references then always fail to check out.
                #[cfg(any(test, feature = "gc-verify"))]
                each_bit(&dead, |g| self.clear_header(page.granule(g)));
                let dead = dead.iter().map(|d| d.count_ones() as usize).sum::<usize>();
                self.stats.objects.set(self.stats.objects.get() - dead);
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
                    self.clear_header(page.start() as u32);
                    self.stats.objects.set(self.stats.objects.get() - 1);
                    self.free_run(page, n as usize);
                }
            }
            Kind::Free | Kind::Tail(_) => {}
        }
    }

    fn finish_cycle(&self) {
        self.stats.collections.set(self.stats.collections.get() + 1);
        self.retarget();
        self.rescan();
        self.state.set(State::Idle);
    }

    pub(crate) fn phase(&self) -> Phase {
        match self.state.get() {
            State::Idle => Phase::Idle,
            State::Marking { .. } => Phase::Marking,
            State::Sweeping { .. } => Phase::Sweeping,
        }
    }

    #[inline]
    pub(crate) fn is_marking(&self) -> bool {
        matches!(self.state.get(), State::Marking { .. })
    }

    /// Whether objects on pages being compacted are still to move or have moved, with
    /// references to them still to rewrite.
    #[inline]
    pub(super) fn is_evacuating(&self) -> bool {
        matches!(self.state.get(), State::Marking { evacuating: true })
    }

    pub(super) fn done_evacuating(&self) {
        self.state.set(State::Marking { evacuating: false });
    }

    #[inline]
    pub(super) fn is_sweeping(&self) -> bool {
        matches!(self.state.get(), State::Sweeping { .. })
    }

    /// Keeps the sweep cursor within the first `len` pages.
    pub(super) fn clamp_cursor(&self, len: usize) {
        if let State::Sweeping { cursor } = self.state.get() {
            self.state.set(State::Sweeping { cursor: cursor.min(PageIndex::at(len)) });
        }
    }
}
