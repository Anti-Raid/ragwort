use std::cell::Cell;
use std::ops::Range;

pub(crate) struct Backing(Box<[u64]>);

impl Backing {
    pub(crate) fn new(len: usize) -> Option<Self> {
        // Safe Rust has no fallible zeroed allocation, and zero-filling a reserved allocation
        // would commit all of its pages. So this first checks that an allocation of this size
        // succeeds, and then makes a zeroed allocation. The system supplies zeroed memory
        // untouched and commits it lazily. If another thread takes the memory between the two
        // steps, the second allocation can still abort the process.
        Vec::<u64>::new().try_reserve_exact(len).ok()?;
        Some(Self(vec![0; len].into_boxed_slice()))
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub(crate) fn words(&mut self) -> &[Cell<u64>] {
        Cell::from_mut(&mut self.0[..]).as_slice_of_cells()
    }

    pub(crate) fn release(&mut self, _range: Range<usize>) -> Range<usize> {
        0..0
    }

    pub(crate) fn releases() -> bool {
        false
    }
}
