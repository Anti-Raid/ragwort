//! Vectors, of fixed length, their elements stored inline. A [`Vector`] is mutable: write its
//! elements through [`Gc::items`], whose locks take the barrier, one with [`Lock::set`] or a
//! range with [`Lock::fill`] or [`Lock::copy`]. An [`ImmutableVector`], such as a literal,
//! holds plain values, so nothing can write to it.

use std::marker::PhantomData;

use ragwort_gc::{Gc, Lock, Mutation, OutOfMemory, Plain, Trace, TypeTag, Value};

#[cfg(test)]
mod tests;

#[derive(Trace, Plain)]
#[gc(items = Lock<Value<'gc>>)]
pub struct Vector<'gc>(PhantomData<&'gc ()>);

#[derive(Trace, Plain)]
#[gc(items = Value<'gc>)]
pub struct ImmutableVector<'gc>(PhantomData<&'gc ()>);

/// Either kind of vector, for reading.
#[derive(Clone, Copy)]
pub enum AnyVector<'gc> {
    Mutable(Gc<'gc, Vector<'gc>>),
    Immutable(Gc<'gc, ImmutableVector<'gc>>),
}

impl<'gc> AnyVector<'gc> {
    pub fn len(self) -> usize {
        match self {
            Self::Mutable(v) => v.items().len(),
            Self::Immutable(v) => v.items().len(),
        }
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub fn get(self, index: usize) -> Option<Value<'gc>> {
        match self {
            Self::Mutable(v) => v.items().get(index).map(Lock::get),
            Self::Immutable(v) => v.items().get(index).copied(),
        }
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(v) => Value::object(mc, v),
            Self::Immutable(v) => Value::object(mc, v),
        }
    }
}

/// Vector operations for one step.
#[derive(Clone, Copy)]
pub struct Vectors<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    mutable: TypeTag<'gc, Vector<'gc>>,
    immutable: TypeTag<'gc, ImmutableVector<'gc>>,
}

impl<'a, 'gc> Vectors<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self { mc, mutable: mc.inline_type_tag()?, immutable: mc.inline_type_tag()? })
    }

    pub fn vector(&self, v: Value<'gc>) -> Option<AnyVector<'gc>> {
        match self.mutable(v) {
            Some(v) => Some(AnyVector::Mutable(v)),
            None => v.downcast_tag(self.mc, self.immutable).map(AnyVector::Immutable),
        }
    }

    /// `v` if it's a vector that can be written to.
    pub fn mutable(&self, v: Value<'gc>) -> Option<Gc<'gc, Vector<'gc>>> {
        v.downcast_tag(self.mc, self.mutable)
    }

    /// A vector of `len` copies of `fill`.
    pub fn make(&self, len: usize, fill: Value<'gc>) -> Result<Gc<'gc, Vector<'gc>>, OutOfMemory> {
        self.mc.alloc_inline(Vector(PhantomData), len, |_| Lock::new(fill))
    }

    pub fn from_slice(&self, items: &[Value<'gc>]) -> Result<Gc<'gc, Vector<'gc>>, OutOfMemory> {
        self.mc.alloc_inline(Vector(PhantomData), items.len(), |i| Lock::new(items[i]))
    }

    pub fn immutable_from_slice(&self, items: &[Value<'gc>]) -> Result<Gc<'gc, ImmutableVector<'gc>>, OutOfMemory> {
        self.mc.alloc_inline_from(ImmutableVector(PhantomData), items)
    }

    /// `v`'s elements as they are now, in a vector that can't change: `v` itself if it's
    /// already immutable, otherwise a copy.
    pub fn freeze(&self, v: AnyVector<'gc>) -> Result<Gc<'gc, ImmutableVector<'gc>>, OutOfMemory> {
        match v {
            AnyVector::Immutable(v) => Ok(v),
            AnyVector::Mutable(v) => {
                let items = v.items();
                self.mc.alloc_inline(ImmutableVector(PhantomData), items.len(), |i| items[i].get())
            }
        }
    }
}
