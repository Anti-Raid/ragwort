use std::marker::PhantomData;

use ragwort_gc::{Lock, Member, Mutation, OutOfMemory, Plain, Trace, max_items};

#[cfg(test)]
#[path = "tests/vec.rs"]
mod tests;

/// The slots behind a [`GcVec`], stored inline.
#[derive(Trace, Plain)]
#[gc(items = Lock<T>)]
pub struct Slots<T>(PhantomData<T>);

/// A growable array stored entirely in the arena. Slots past `len` hold `T::default()`.
#[derive(Trace, Plain)]
pub struct GcVec<'gc, T> {
    len: Lock<u32>,
    buf: Lock<Option<Member<'gc, Slots<T>>>>,
}

impl<'gc, T: Trace + Copy + Default + Plain<'gc> + 'gc> GcVec<'gc, T> {
    pub fn new() -> Self {
        Self { len: Lock::new(0), buf: Lock::new(None) }
    }

    /// The buffer and the length. The stored length can't be trusted, so it's capped here.
    fn parts(&self, mc: &Mutation<'gc>) -> (&'gc [Lock<T>], usize) {
        let slots = self.buf.load(mc).map_or(&[][..], |buf| buf.items());
        (slots, (self.len.get() as usize).min(slots.len()))
    }

    pub fn len(&self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).1
    }

    pub fn is_empty(&self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    pub fn capacity(&self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).0.len()
    }

    pub fn get(&self, mc: &Mutation<'gc>, index: usize) -> Option<T> {
        let (slots, len) = self.parts(mc);
        slots[..len].get(index).map(Lock::get)
    }

    /// Fixes the storage and initialized range; reads each value as iteration advances.
    pub fn iter(&self, mc: &Mutation<'gc>) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + Clone + 'gc {
        let (slots, len) = self.parts(mc);
        slots[..len].iter().map(Lock::get)
    }

    pub fn set(&self, mc: &Mutation<'gc>, index: usize, value: T) -> bool {
        let (slots, len) = self.parts(mc);
        let Some(slot) = slots[..len].get(index) else { return false };
        slot.set(mc, value);
        true
    }

    pub fn reserve(&self, mc: &Mutation<'gc>, additional: usize) -> Result<(), OutOfMemory> {
        let (slots, len) = self.parts(mc);
        let needed = len.checked_add(additional).ok_or_else(|| mc.out_of_memory())?;
        if needed <= slots.len() {
            return Ok(());
        }
        let copy = |i: usize| Lock::new(slots[..len].get(i).map_or_else(T::default, Lock::get));
        let grown = (slots.len() * 2).max(4).min(max_items::<Slots<T>>());
        let buf = match grown > needed {
            true => mc.optional(|| mc.alloc_inline(Slots(PhantomData), grown, copy)).ok(),
            false => None,
        };
        let buf = match buf {
            Some(buf) => buf,
            None => mc.alloc_inline(Slots(PhantomData), needed, copy)?,
        };
        self.buf.store(mc, Some(buf));
        self.len.set(mc, len as u32);
        Ok(())
    }

    pub fn push(&self, mc: &Mutation<'gc>, value: T) -> Result<(), OutOfMemory> {
        self.reserve(mc, 1)?;
        let (slots, len) = self.parts(mc);
        slots[len].set(mc, value);
        self.len.set(mc, len as u32 + 1);
        Ok(())
    }

    pub fn pop(&self, mc: &Mutation<'gc>) -> Option<T> {
        let (slots, len) = self.parts(mc);
        let last = len.checked_sub(1)?;
        let value = slots[last].get();
        slots[last].set(mc, T::default());
        self.len.set(mc, last as u32);
        Some(value)
    }

    pub fn truncate(&self, mc: &Mutation<'gc>, len: usize) {
        let (slots, old) = self.parts(mc);
        let len = len.min(old);
        for slot in &slots[len..old] {
            slot.set(mc, T::default());
        }
        self.len.set(mc, len as u32);
    }
}

impl<'gc, T: Trace + Copy + Default + Plain<'gc> + 'gc> Default for GcVec<'gc, T> {
    fn default() -> Self {
        Self::new()
    }
}

