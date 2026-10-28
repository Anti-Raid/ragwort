use std::cell::Cell;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutOfMemory;

impl fmt::Display for OutOfMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("out of memory")
    }
}

impl std::error::Error for OutOfMemory {}

pub(crate) struct Budget {
    used: Cell<usize>,
    peak: Cell<usize>,
    limit: usize,
    /// The last bytes under the limit, kept for a step to finish in once the rest is used.
    reserve: Cell<usize>,
    /// Set once the reserve is drawn on, until the collection it calls for.
    due: Cell<bool>,
    /// Allocations that can be done without stay out of the reserve.
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

    pub(crate) fn reserve(&self) -> usize {
        self.reserve.get()
    }

    pub(crate) fn collection_due(&self) -> bool {
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

    pub(crate) fn fail(&self) -> OutOfMemory {
        self.failed.set(true);
        OutOfMemory
    }

    pub(crate) fn fail_after(&self, allocations: Option<u64>) {
        self.fail_in.set(allocations.unwrap_or(u64::MAX));
    }

    /// Counts an allocation, and fails it if it's the one [`Self::fail_after`] picked.
    #[inline]
    pub(crate) fn count_allocation(&self) -> Result<(), OutOfMemory> {
        if self.fail_in.get() == u64::MAX { Ok(()) } else { self.count_injected() }
    }

    #[cold]
    fn count_injected(&self) -> Result<(), OutOfMemory> {
        match self.fail_in.get() {
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

    pub(crate) fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        let room = self.limit - self.used.get();
        if bytes <= room.saturating_sub(self.reserve.get()) {
            return Ok(());
        }
        if bytes > room || self.optional.get() {
            return Err(self.fail());
        }
        self.due.set(true);
        Ok(())
    }

    /// Runs an allocation that the caller can do without, so failing it doesn't fail the step,
    /// and it doesn't draw on the reserve.
    pub(crate) fn quiet<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        let failed = self.failed.get();
        let result = {
            // Restored on unwind too, so a panic in `f` doesn't leave later steps without the reserve.
            let _optional = Restore(&self.optional, self.optional.replace(true));
            f()
        };
        if result.is_err() {
            self.failed.set(failed);
        }
        result
    }

    pub(crate) fn charge(&self, bytes: usize) -> Result<(), OutOfMemory> {
        self.ensure(bytes)?;
        let used = self.used.get() + bytes;
        self.used.set(used);
        if used > self.peak.get() {
            self.peak.set(used);
        }
        Ok(())
    }

    pub(crate) fn refund(&self, bytes: usize) {
        debug_assert!(bytes <= self.used.get());
        self.used.set(self.used.get() - bytes);
    }
}

/// Puts a flag back to what it was when dropped.
struct Restore<'a>(&'a Cell<bool>, bool);

impl Drop for Restore<'_> {
    fn drop(&mut self) {
        self.0.set(self.1);
    }
}
