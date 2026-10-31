use std::ops::{Deref, DerefMut};

use ragwort_gc::{Charge, Mutation, OutOfMemory};

#[cfg(test)]
#[path = "tests/scratch.rs"]
mod tests;

/// A vector outside the arena whose capacity counts against the arena's budget while it lives,
/// for a step's scratch space, such as a reader's open lists. It can't outlive the step, so it
/// can hold `'gc` values untraced: no collection runs during a step.
pub struct ScratchVec<'gc, T> {
    items: Vec<T>,
    charge: Charge<'gc>,
}

impl<'gc, T> ScratchVec<'gc, T> {
    pub fn new(mc: &Mutation<'gc>) -> Self {
        Self { items: Vec::new(), charge: mc.charge() }
    }

    /// Fails as an allocation would if the budget can't cover the growth.
    pub fn reserve(&mut self, additional: usize) -> Result<(), OutOfMemory> {
        let needed = self.items.len().saturating_add(additional);
        if needed > self.items.capacity() {
            self.grow(needed)?;
        }
        Ok(())
    }

    #[cold]
    fn grow(&mut self, needed: usize) -> Result<(), OutOfMemory> {
        let cap = needed.max(self.items.capacity() * 2).max(4);
        let bytes = cap.saturating_mul(size_of::<T>());
        self.charge.grow(bytes.saturating_sub(self.charge.bytes()))?;
        self.items.reserve_exact(cap - self.items.len());
        Ok(())
    }

    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), OutOfMemory> {
        if self.items.len() == self.items.capacity() {
            self.grow(self.items.len() + 1)?;
        }
        self.items.push(value);
        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }

    pub fn truncate(&mut self, len: usize) {
        self.items.truncate(len);
    }

    pub fn clear(&mut self) {
        self.items.clear();
    }
}

impl<T> Deref for ScratchVec<'_, T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.items
    }
}

impl<T> DerefMut for ScratchVec<'_, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.items
    }
}
