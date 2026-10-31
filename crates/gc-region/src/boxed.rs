use std::cell::Cell;
use std::ops::Range;

pub(crate) struct Backing(Box<[u64]>);

impl Backing {
    pub(crate) fn new(len: usize) -> Option<Self> {
        // Zeroed, so large regions come from the system untouched and commit lazily.
        Some(Self(vec![0; len].into_boxed_slice()))
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub(crate) fn words(&mut self) -> &[Cell<u64>] {
        Cell::from_mut(&mut self.0[..]).as_slice_of_cells()
    }

    pub(crate) fn release(&mut self, _range: Range<usize>) {}

    pub(crate) fn releases() -> bool {
        false
    }
}
