//! Counts the heap keeps, and the threshold that paces major cycles.

use std::cell::Cell;

use crate::layout::{LINE, PAGE};
use super::pages::Kind;
use super::Heap;

const MIN_THRESHOLD: usize = 64 * 1024;

/// Counts the other parts of the heap keep up to date.
pub(super) struct Stats {
    pub(super) objects: Cell<usize>,
    pub(super) marks: Cell<usize>,
    pub(super) allocated: Cell<usize>,
    pub(super) young: Cell<usize>,
    pub(super) threshold: Cell<usize>,
    pub(super) collections: Cell<u64>,
    pub(super) minors: Cell<u64>,
}

impl Stats {
    pub(super) fn new(limit: usize) -> Self {
        let zero = || Cell::new(0);
        Self {
            objects: zero(),
            marks: zero(),
            allocated: zero(),
            young: zero(),
            threshold: Cell::new(MIN_THRESHOLD.min(limit / 2)),
            collections: Cell::new(0),
            minors: Cell::new(0),
        }
    }
}

impl Heap {
    pub(crate) fn objects(&self) -> usize {
        self.stats.objects.get()
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

    pub(crate) fn threshold(&self) -> usize {
        self.stats.threshold.get()
    }

    pub(crate) fn collections(&self) -> u64 {
        self.stats.collections.get()
    }

    pub(crate) fn minor_collections(&self) -> u64 {
        self.stats.minors.get()
    }

    pub(crate) fn young(&self) -> usize {
        self.stats.young.get()
    }

    /// How much young allocation triggers a minor collection.
    pub(crate) fn nursery(&self) -> usize {
        (self.budget.limit() / 8).clamp(64 * 1024, 4 << 20)
    }

    pub(crate) fn take_allocated(&self) -> usize {
        self.stats.allocated.replace(0)
    }

    /// Sets when the next major cycle starts: once usage doubles, but never later than
    /// halfway from the current usage to the limit, so a cycle always has room to finish.
    pub(super) fn retarget(&self) {
        let (used, limit) = (self.budget.used(), self.budget.limit());
        self.stats.threshold.set((used * 2).max(MIN_THRESHOLD).min(used + (limit - used) / 2));
    }

    /// Counts bytes charged outside the region towards pacing.
    pub(crate) fn demand(&self, bytes: usize) {
        self.stats.allocated.set(self.stats.allocated.get() + bytes);
        self.stats.young.set(self.stats.young.get() + bytes);
    }

    pub(crate) fn clear_allocated(&self) {
        self.stats.allocated.set(0);
    }
}
