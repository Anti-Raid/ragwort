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
    failed: Cell<bool>,
}

impl Budget {
    pub(crate) fn new(limit: usize) -> Self {
        Self { used: Cell::new(0), peak: Cell::new(0), limit, failed: Cell::new(false) }
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

    pub(crate) fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        if bytes > self.limit - self.used.get() { Err(self.fail()) } else { Ok(()) }
    }

    /// Runs an allocation that the caller can do without, so failing it doesn't fail the step.
    pub(crate) fn quiet<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        let failed = self.failed.get();
        let result = f();
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
