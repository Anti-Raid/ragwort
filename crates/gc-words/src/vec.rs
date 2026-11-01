//! A growable array in the arena: a handle object holding the length and an array of `S`, which
//! growing replaces. Slots past the length hold the zero word, which reads as fixnum 0, none, or
//! 0, so they keep nothing alive.

use std::marker::PhantomData;

use crate::raw::Raw;
use crate::slot::{self, Item, Role};
use crate::{Desc, Field, Gc, Items, Mutation, Object, OutOfMemory, Slots, Value};

#[cfg(test)]
#[path = "tests/vec.rs"]
mod tests;

/// A [`GcVec`]'s handle object.
pub struct VecHead<S>(PhantomData<fn() -> S>);

/// A [`GcVec`]'s slots.
#[doc(hidden)]
pub struct VecSlots<S>(PhantomData<fn() -> S>);

impl<S: Item> Object for VecHead<S> {
    const DESC: Desc = Desc::layout::<Self>(&[Role::Word, Role::Member], Items::None);
}

impl<S: Item> Object for VecSlots<S> {
    const DESC: Desc = Desc::layout::<Self>(&[], S::ITEMS);
}

impl<S: Item> VecHead<S> {
    const LEN: Field<Self, slot::u64> = Field::new(0);
    const SLOTS: Field<Self, slot::Member<VecSlots<S>>> = Field::new(1);
}

/// A growable array of `S`, values by default.
pub struct GcVec<'gc, S = slot::Value> {
    head: Gc<'gc, VecHead<S>>,
}

impl<S> Clone for GcVec<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for GcVec<'_, S> {}

impl<'gc, S: Item> GcVec<'gc, S> {
    pub fn new(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self { head: mc.alloc::<VecHead<S>, 2>([0, 0])? })
    }

    pub fn with_capacity(mc: &Mutation<'gc>, capacity: usize) -> Result<Self, OutOfMemory> {
        let v = Self::new(mc)?;
        v.reserve(mc, capacity)?;
        Ok(v)
    }

    /// The vector `head` is the handle of.
    pub fn of(head: Gc<'gc, VecHead<S>>) -> Self {
        Self { head }
    }

    pub fn head(self) -> Gc<'gc, VecHead<S>> {
        self.head
    }

    /// All the slots, and the length. The stored length can't be trusted, so it's capped here.
    #[inline]
    fn parts(self, mc: &Mutation<'gc>) -> Option<(Slots<'gc, S>, usize)> {
        let slots = self.head.get(mc, VecHead::SLOTS)?.item_slots::<S>(mc);
        let len = (self.head.get(mc, VecHead::LEN) as usize).min(slots.len());
        Some((slots, len))
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).map_or(0, |(_, len)| len)
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    pub fn capacity(self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).map_or(0, |(slots, _)| slots.len())
    }

    /// The slots up to the length, for bulk reads and writes.
    pub fn items(self, mc: &Mutation<'gc>) -> Option<Slots<'gc, S>> {
        let (slots, len) = self.parts(mc)?;
        slots.slice(0..len)
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, i: usize) -> Option<S::Out<'gc>> {
        let (slots, len) = self.parts(mc)?;
        (i < len).then(|| slots.get(i))
    }

    /// Whether `i` is in bounds, and so was set.
    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, i: usize, value: S::In<'gc>) -> bool {
        let Some((slots, _)) = self.parts(mc).filter(|&(_, len)| i < len) else { return false };
        slots.set(mc, i, value);
        true
    }

    /// Room for `additional` more without growing. Grows to double when the budget allows, and
    /// to just what's needed when it doesn't.
    pub fn reserve(self, mc: &Mutation<'gc>, additional: usize) -> Result<(), OutOfMemory> {
        let (old, len) = self.parts(mc).unzip();
        let len = len.unwrap_or(0);
        let capacity = old.map_or(0, Slots::len);
        let needed = len.checked_add(additional).ok_or_else(|| mc.out_of_memory())?;
        if needed <= capacity {
            return Ok(());
        }
        let alloc = |n| mc.alloc_items::<VecSlots<S>, 0>([], n, Value::from_bits(0));
        let doubled = (capacity * 2).max(4);
        let slots = match doubled > needed {
            true => mc.optional(|| alloc(doubled)).ok(),
            false => None,
        };
        let slots = match slots {
            Some(slots) => slots,
            None => alloc(needed)?,
        };
        if let (Some(old), Some(new)) = (old.and_then(|o| o.slice(0..len)), slots.item_slots::<S>(mc).slice(0..len)) {
            new.copy_from(mc, old);
        }
        self.head.set(mc, VecHead::SLOTS, Some(slots));
        self.head.set(mc, VecHead::LEN, len as u64);
        Ok(())
    }

    pub fn push(self, mc: &Mutation<'gc>, value: S::In<'gc>) -> Result<(), OutOfMemory> {
        self.reserve(mc, 1)?;
        let (slots, len) = self.parts(mc).ok_or_else(|| mc.out_of_memory())?;
        slots.set(mc, len, value);
        self.head.set(mc, VecHead::LEN, len as u64 + 1);
        Ok(())
    }

    pub fn pop(self, mc: &Mutation<'gc>) -> Option<S::Out<'gc>> {
        let (slots, len) = self.parts(mc)?;
        let last = len.checked_sub(1)?;
        let value = slots.get(last);
        self.truncate(mc, last);
        Some(value)
    }

    pub fn truncate(self, mc: &Mutation<'gc>, len: usize) {
        let Some((_, old)) = self.parts(mc) else { return };
        let len = len.min(old);
        // Zero words, whatever `S` is, so the slots keep nothing alive.
        if let Some(gone) = self.head.get(mc, VecHead::SLOTS).and_then(|s| s.item_slots::<slot::u64>(mc).slice(len..old)) {
            gone.fill(mc, 0);
        }
        self.head.set(mc, VecHead::LEN, len as u64);
    }

    pub fn clear(self, mc: &Mutation<'gc>) {
        self.truncate(mc, 0);
    }

    /// Reads each item as iteration reaches it.
    pub fn iter<'m>(self, mc: &'m Mutation<'gc>) -> impl DoubleEndedIterator<Item = S::Out<'gc>> + ExactSizeIterator + use<'m, 'gc, S> {
        let parts = self.parts(mc);
        let len = parts.map_or(0, |(_, len)| len);
        (0..len).map(move |i| parts.map(|(slots, _)| slots.get(i)).expect("slots up to the length"))
    }
}
