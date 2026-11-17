//! The memory region that backs a word heap. It is an array of zeroed `u64` words. A page is
//! committed when it is first touched, and pages can be returned to the system.
//!
//! With the `mmap` feature on Unix, the region is an anonymous mapping, and [`Region::release`]
//! returns pages to the system. It uses `madvise` on Linux, and maps fresh pages over the old
//! pages elsewhere. Otherwise the region is a plain allocation, and `release` does nothing.

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
    /// Returns a region of `len` zeroed words, or `None` if the system cannot reserve the memory.
    pub fn new(len: usize) -> Option<Self> {
        Backing::new(len).map(Self)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the words. They are `Cell`s, so they can be written through a shared reference.
    #[inline]
    pub fn words(&mut self) -> &[Cell<u64>] {
        self.0.words()
    }

    /// Returns the memory of the words in `range` to the system. The range is rounded inward to
    /// whole OS pages. The words stay usable. Afterwards each word reads as zero or as its
    /// previous value. Returns the range of words that was released, which is empty if none were.
    /// So a caller can count only the memory that was actually released.
    pub fn release(&mut self, range: Range<usize>) -> Range<usize> {
        self.0.release(range)
    }

    /// Returns whether [`Region::release`] can return memory to the system at all.
    pub fn releases() -> bool {
        Backing::releases()
    }
}

#[cfg(test)]
#[path = "tests/region.rs"]
mod tests;
