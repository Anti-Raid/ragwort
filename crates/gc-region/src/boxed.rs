use std::cell::Cell;
use std::ops::Range;

pub(crate) struct Backing(Box<[u64]>);

impl Backing {
    pub(crate) fn new(len: usize) -> Option<Self> {
        // Safe Rust has no fallible zeroed allocation, and filling a reserved one would commit
        // all of it. So it checks the allocation can be made, then makes it zeroed, which
        // comes from the system untouched and commits lazily. Another thread taking the memory
        // in between can still abort it.
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
