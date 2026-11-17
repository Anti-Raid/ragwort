use std::cell::Cell;

use super::{Mutation, OutOfMemory};

/// The bytes that an arena has charged against its limit: committed pages with their bookkeeping, roots,
/// stacks, host values, frozen values, the collector's work lists, and the bytes that [`Charge`]s hold.
///
/// The last bytes under the limit are a reserve. An allocation that needs the reserve succeeds, but
/// makes a full collection due at the end of the step. So a heap full of garbage does not fail
/// the step. An allocation that would pass the limit fails, and so does the step.
pub(crate) struct Budget {
    used: Cell<usize>,
    peak: Cell<usize>,
    limit: usize,
    reserve: Cell<usize>,
    due: Cell<bool>,
    /// Whether an optional allocation is running. An optional allocation does not draw on the reserve, and its failure does not fail the step.
    in_optional: Cell<bool>,
    failed: Cell<bool>,
    /// For testing: the number of allocations to let succeed before one is failed. `u64::MAX` means that no failure is injected.
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
            in_optional: Cell::new(false),
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

    /// Returns the bytes that could be allocated without drawing on the reserve if `used` bytes were charged.
    pub(crate) fn room_past(&self, used: usize) -> usize {
        self.limit.saturating_sub(self.reserve.get()).saturating_sub(used)
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

    /// Marks the step as failed, unless the allocation is optional. Returns the error.
    pub(crate) fn fail(&self) -> OutOfMemory {
        if !self.in_optional.get() {
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

    /// Counts one allocation while failures are injected, and fails the allocation that `fail_after` selected.
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

    /// Checks whether `bytes` more bytes fit under the limit. If they fit only by drawing on the reserve, a full collection becomes due. An optional allocation cannot draw on the reserve and fails instead.
    pub(crate) fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        let room = self.limit.saturating_sub(self.used.get());
        if bytes <= room.saturating_sub(self.reserve.get()) {
            return Ok(());
        }
        if bytes > room || self.in_optional.get() {
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

    pub(crate) fn force(&self, bytes: usize) {
        let used = self.used.get() + bytes;
        self.used.set(used);
        self.peak.set(self.peak.get().max(used));
    }

    pub(crate) fn refund(&self, bytes: usize) {
        debug_assert!(bytes <= self.used.get());
        self.used.set(self.used.get().saturating_sub(bytes));
    }

    pub(crate) fn optional<R>(&self, allocate: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        let _optional = Restore(&self.in_optional, self.in_optional.replace(true));
        allocate()
    }
}

/// A charge against the budget for bytes kept outside the arena, such as a buffer that a host function builds. The bytes stay charged
/// while the `Charge` lives. Dropping it refunds exactly the bytes it charged.
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

    /// Charges `more` bytes. Fails as an allocation does if the budget cannot cover them.
    pub fn grow(&mut self, more: usize) -> Result<(), OutOfMemory> {
        self.budget.charge(more)?;
        self.bytes += more;
        Ok(())
    }

    /// Refunds `less` bytes, or the whole charge if the charge is smaller.
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

/// Restores a flag to its earlier value when dropped, so a panic in `optional` cannot leave the flag set.
struct Restore<'a>(&'a Cell<bool>, bool);

impl Drop for Restore<'_> {
    fn drop(&mut self) {
        self.0.set(self.1);
    }
}
