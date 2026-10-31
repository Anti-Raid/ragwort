use std::cell::Cell;

use super::{Mutation, OutOfMemory};

/// What an arena holds against its limit: committed pages with their bookkeeping, roots,
/// stacks, host values, the collector's work lists, and what [`Charge`]s claim.
///
/// The last bytes under the limit are a reserve: an allocation that needs them succeeds, but
/// makes a full collection due at the end of the step, so a heap full of garbage doesn't fail
/// it. Past the limit, an allocation fails, and so does the step.
pub(crate) struct Budget {
    used: Cell<usize>,
    peak: Cell<usize>,
    limit: usize,
    reserve: Cell<usize>,
    due: Cell<bool>,
    /// Allocations that can be done without stay out of the reserve, and don't fail the step.
    optional: Cell<bool>,
    failed: Cell<bool>,
    /// Allocations to let through before failing one, for testing, or `u64::MAX` for none.
    fail_in: Cell<u64>,
}

impl Budget {
    pub(crate) fn new(limit: usize) -> Self {
        Self {
            used: Cell::new(0),
            peak: Cell::new(0),
            limit,
            reserve: Cell::new(limit / 16),
            due: Cell::new(false),
            optional: Cell::new(false),
            failed: Cell::new(false),
            fail_in: Cell::new(u64::MAX),
        }
    }

    pub(crate) fn used(&self) -> usize {
        self.used.get()
    }

    pub(crate) fn peak(&self) -> usize {
        self.peak.get()
    }

    pub(crate) fn limit(&self) -> usize {
        self.limit
    }

    pub(crate) fn set_reserve(&self, bytes: usize) {
        self.reserve.set(bytes.min(self.limit));
    }

    pub(crate) fn due(&self) -> bool {
        self.due.get()
    }

    pub(crate) fn clear_due(&self) {
        self.due.set(false);
    }

    pub(crate) fn failed(&self) -> bool {
        self.failed.get()
    }

    pub(crate) fn clear_failed(&self) {
        self.failed.set(false);
    }

    /// Fails the step, unless the allocation was optional.
    pub(crate) fn fail(&self) -> OutOfMemory {
        if !self.optional.get() {
            self.failed.set(true);
        }
        OutOfMemory
    }

    pub(crate) fn fail_after(&self, allocations: Option<u64>) {
        self.fail_in.set(allocations.unwrap_or(u64::MAX));
    }

    pub(crate) fn injecting(&self) -> bool {
        self.fail_in.get() != u64::MAX
    }

    /// Counts an allocation while failures are injected, and fails the one picked.
    pub(crate) fn count_allocation(&self) -> Result<(), OutOfMemory> {
        match self.fail_in.get() {
            u64::MAX => Ok(()),
            0 => {
                self.fail_in.set(u64::MAX);
                Err(self.fail())
            }
            left => {
                self.fail_in.set(left - 1);
                Ok(())
            }
        }
    }

    /// Whether `bytes` more fit, drawing on the reserve if they must.
    pub(crate) fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        let room = self.limit.saturating_sub(self.used.get());
        if bytes <= room.saturating_sub(self.reserve.get()) {
            return Ok(());
        }
        if bytes > room || self.optional.get() {
            return Err(self.fail());
        }
        self.due.set(true);
        Ok(())
    }

    pub(crate) fn charge(&self, bytes: usize) -> Result<(), OutOfMemory> {
        self.ensure(bytes)?;
        self.force(bytes);
        Ok(())
    }

    /// Charges memory the collector took, which it can't do without. It may go past the
    /// limit, and the allocations after fail until a collection gives some back.
    pub(crate) fn force(&self, bytes: usize) {
        let used = self.used.get() + bytes;
        self.used.set(used);
        self.peak.set(self.peak.get().max(used));
    }

    pub(crate) fn refund(&self, bytes: usize) {
        debug_assert!(bytes <= self.used.get());
        self.used.set(self.used.get().saturating_sub(bytes));
    }

    /// Runs allocations the caller can do without: failing them doesn't fail the step, and
    /// they don't draw on the reserve.
    pub(crate) fn quiet<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        let _optional = Restore(&self.optional, self.optional.replace(true));
        f()
    }
}

/// Bytes kept outside the arena, such as a buffer a host function builds, counted against the
/// budget while this lives. It gives back exactly what it took when dropped.
pub struct Charge<'gc> {
    bytes: usize,
    budget: &'gc Budget,
}

impl<'gc> Charge<'gc> {
    pub(crate) fn new(mc: &Mutation<'gc>) -> Self {
        Self { bytes: 0, budget: &mc.heap.m.budget }
    }

    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// Charges `more` bytes, failing as an allocation would if the budget can't cover them.
    pub fn grow(&mut self, more: usize) -> Result<(), OutOfMemory> {
        self.budget.charge(more)?;
        self.bytes += more;
        Ok(())
    }

    /// Gives back up to `less` bytes.
    pub fn shrink(&mut self, less: usize) {
        let less = less.min(self.bytes);
        self.budget.refund(less);
        self.bytes -= less;
    }
}

impl Drop for Charge<'_> {
    fn drop(&mut self) {
        self.budget.refund(self.bytes);
    }
}

/// Puts a flag back to what it was when dropped, so a panic in `quiet` can't leave it set.
struct Restore<'a>(&'a Cell<bool>, bool);

impl Drop for Restore<'_> {
    fn drop(&mut self) {
        self.0.set(self.1);
    }
}
