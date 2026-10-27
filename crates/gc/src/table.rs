use std::mem::size_of;
use std::ops::{Deref, DerefMut};

use super::OutOfMemory;
use super::budget::Budget;

/// A vector of bookkeeping kept outside the region. Its whole capacity is charged to the
/// budget, and the only ways to grow it go through the budget.
pub(crate) struct Table<T>(Vec<T>);

impl<T> Table<T> {
    pub(crate) const fn new() -> Self {
        Self(Vec::new())
    }

    pub(crate) fn charged(&self) -> usize {
        self.0.capacity() * size_of::<T>()
    }

    /// What making room for `additional` more items would charge.
    pub(crate) fn growth_cost(&self, additional: usize) -> usize {
        self.grown(additional).map_or(0, |cap| (cap - self.0.capacity()) * size_of::<T>())
    }

    fn grown(&self, additional: usize) -> Option<usize> {
        let needed = self.0.len().saturating_add(additional);
        (needed > self.0.capacity()).then(|| needed.max(self.0.capacity() * 2))
    }

    pub(crate) fn reserve(&mut self, budget: &Budget, additional: usize) -> Result<(), OutOfMemory> {
        if let Some(cap) = self.grown(additional) {
            budget.charge((cap - self.0.capacity()) * size_of::<T>())?;
            self.0.reserve_exact(cap - self.0.len());
            debug_assert_eq!(self.0.capacity(), cap);
        }
        Ok(())
    }

    pub(crate) fn push(&mut self, budget: &Budget, value: T) -> Result<(), OutOfMemory> {
        self.reserve(budget, 1)?;
        self.0.push(value);
        Ok(())
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }

    pub(crate) fn retain(&mut self, f: impl FnMut(&T) -> bool) {
        self.0.retain(f);
    }

    /// Gives capacity back once no more than a quarter of it is in use.
    pub(crate) fn shrink(&mut self, budget: &Budget) {
        let before = self.charged();
        if self.0.len() <= self.0.capacity() / 4 {
            self.0.shrink_to(self.0.len() * 2);
            budget.refund(before - self.charged());
        }
    }
}

impl<T> Deref for Table<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for Table<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}
