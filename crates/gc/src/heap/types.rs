//! The type registry: each type's vtable, by the index headers store.

use std::cell::Cell;
use std::ptr;

use crate::layout::{InlineVTable, STAMPS, STAMP_SHIFT, SizedVTable, TypeIndex, VTable};
use crate::{Inline, OutOfMemory, Trace};
use super::{Heap, Zeroed, zeroed};

const TYPES: usize = 1 << 16;

pub(super) struct Types {
    // A slot for every `TypeIndex`, so every lookup is in bounds.
    vtables: Box<[Cell<Option<&'static VTable>>; TYPES]>,
    count: Cell<usize>,
    cache: [Cell<(usize, TypeIndex)>; 64],
    stamp: Cell<u16>,
}

impl Types {
    pub(super) fn new() -> Self {
        Self { vtables: zeroed(), count: Cell::new(0), cache: [const { Cell::new((0, TypeIndex::new(0))) }; 64], stamp: Cell::new(0) }
    }
}

// SAFETY: zero is `None`, since a reference is never null.
unsafe impl Zeroed for [Cell<Option<&'static VTable>>; TYPES] {}

impl Heap {
    #[inline]
    pub(super) fn type_index(&self, vtable: &'static VTable) -> Result<TypeIndex, OutOfMemory> {
        let addr = (vtable as *const VTable).addr();
        let (a, index) = self.types.cache[(addr >> 4) % 64].get();
        if a == addr { Ok(index) } else { self.type_index_slow(vtable) }
    }

    #[inline(never)]
    fn type_index_slow(&self, vtable: &'static VTable) -> Result<TypeIndex, OutOfMemory> {
        let addr = (vtable as *const VTable).addr();
        let cached = &self.types.cache[(addr >> 4) % 64];
        let count = self.types.count.get();
        let same = |t: &'static VTable| ptr::eq(t, vtable) || (t.type_id)() == (vtable.type_id)();
        let known = self.types.vtables[..count].iter().position(|t| t.get().is_some_and(same));
        let index = match known {
            Some(index) => index,
            None if count < TYPES => {
                self.types.vtables[count].set(Some(vtable));
                self.types.count.set(count + 1);
                count
            }
            None => return Err(self.budget.fail()),
        };
        let index = TypeIndex::new(index as u16);
        cached.set((addr, index));
        Ok(index)
    }

    #[inline]
    pub(super) fn vtable(&self, ty: TypeIndex) -> Option<&'static VTable> {
        self.types.vtables[ty.get()].get()
    }

    /// The next allocation stamp, never zero.
    #[inline]
    pub(super) fn stamp(&self) -> u16 {
        let stamp = self.types.stamp.get();
        let stamp = if stamp >= STAMPS - 1 { 1 } else { stamp + 1 };
        self.types.stamp.set(stamp);
        stamp << STAMP_SHIFT
    }

    pub(crate) fn sized_type<T: Trace>(&self) -> Result<TypeIndex, OutOfMemory> {
        const { assert!(!T::INLINE, "inline types need an inline type tag") };
        self.type_index(&SizedVTable::<T>::VTABLE)
    }

    pub(crate) fn inline_type<T: Inline>(&self) -> Result<TypeIndex, OutOfMemory> {
        const { assert!(T::INLINE, "type implements Inline but INLINE is false") };
        self.type_index(&InlineVTable::<T>::VTABLE)
    }
}
