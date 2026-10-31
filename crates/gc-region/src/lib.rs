//! The memory a word heap lives in: zeroed `u64` words, committed as they're first touched,
//! whose pages can be given back to the system.
//!
//! With the `mmap` feature on Unix, it's an anonymous mapping and [`Region::release`] gives
//! pages back with `madvise`. Otherwise it's a plain allocation and release does nothing.

use std::cell::Cell;
use std::ops::Range;

#[cfg(all(feature = "mmap", unix))]
mod mmap;
#[cfg(all(feature = "mmap", unix))]
use mmap::Backing;

#[cfg(not(all(feature = "mmap", unix)))]
mod boxed;
#[cfg(not(all(feature = "mmap", unix)))]
use boxed::Backing;

pub struct Region(Backing);

impl Region {
    /// `len` zeroed words, or `None` if the system won't reserve them.
    pub fn new(len: usize) -> Option<Self> {
        Backing::new(len).map(Self)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The words, as cells so they can be written through shared references.
    #[inline]
    pub fn words(&mut self) -> &[Cell<u64>] {
        self.0.words()
    }

    /// Lets the system take back the memory under `range`, rounded inward to whole OS pages.
    /// The words stay usable: afterwards they read as zero, or as what they held.
    pub fn release(&mut self, range: Range<usize>) {
        self.0.release(range);
    }

    /// Whether [`Region::release`] gives memory back at all.
    pub fn releases() -> bool {
        Backing::releases()
    }
}

#[cfg(test)]
#[path = "tests/region.rs"]
mod tests;
