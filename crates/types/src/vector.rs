//! Vectors, of fixed length. A [`Vector`] is mutable: write its elements through
//! [`Vector::items`], whose writes take the barrier. An [`ImmutableVector`], such as a literal,
//! can only be read.

use crate::gc::{Gc, Mutation, OutOfMemory, Slots, Value};
use crate::objects::{self, Data, ImmutableVectorFields, VectorFields};

#[cfg(test)]
#[path = "tests/vector.rs"]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Vector<'gc>(Gc<'gc, objects::Vector>);

impl<'gc> Vector<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Vector(v)) => Some(Self(v)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    #[inline]
    pub fn items(self, mc: &Mutation<'gc>) -> Slots<'gc> {
        self.0.items(mc)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ImmutableVector<'gc>(Gc<'gc, objects::ImmutableVector>);

impl<'gc> ImmutableVector<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::ImmutableVector(v)) => Some(Self(v)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.items(mc).len()
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let items = self.0.items(mc);
        (index < items.len()).then(|| items.get(index))
    }
}

/// Either kind of vector, for reading.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AnyVector<'gc> {
    Mutable(Vector<'gc>),
    Immutable(ImmutableVector<'gc>),
}

impl<'gc> AnyVector<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Vector(v)) => Some(Self::Mutable(Vector(v))),
            Some(Data::ImmutableVector(v)) => Some(Self::Immutable(ImmutableVector(v))),
            _ => None,
        }
    }

    fn items(self, mc: &Mutation<'gc>) -> Slots<'gc> {
        match self {
            Self::Mutable(v) => v.0.items(mc),
            Self::Immutable(v) => v.0.items(mc),
        }
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.items(mc).len()
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let items = self.items(mc);
        (index < items.len()).then(|| items.get(index))
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(v) => v.value(mc),
            Self::Immutable(v) => v.value(mc),
        }
    }
}

/// Vector operations for one step.
#[derive(Clone, Copy)]
pub struct Vectors<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Vectors<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    pub fn vector(&self, v: Value<'gc>) -> Option<AnyVector<'gc>> {
        AnyVector::of(v)
    }

    /// `v` if it's a vector that can be written to.
    pub fn mutable(&self, v: Value<'gc>) -> Option<Vector<'gc>> {
        Vector::of(v)
    }

    /// A vector of `len` copies of `fill`.
    pub fn make(&self, len: usize, fill: Value<'gc>) -> Result<Vector<'gc>, OutOfMemory> {
        objects::Vector::new(self.mc, len, fill).map(Vector)
    }

    pub fn from_slice(&self, items: &[Value<'gc>]) -> Result<Vector<'gc>, OutOfMemory> {
        let v = self.make(items.len(), Value::NIL)?;
        fill(self.mc, v.items(self.mc), items.iter().copied());
        Ok(v)
    }

    pub fn immutable_from_slice(&self, items: &[Value<'gc>]) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        self.immutable_with(items.len(), |i| items[i])
    }

    pub fn immutable_with(&self, len: usize, fill: impl FnMut(usize) -> Value<'gc>) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        let v = objects::ImmutableVector::new(self.mc, len, Value::NIL)?;
        self::fill(self.mc, v.items(self.mc), (0..len).map(fill));
        Ok(ImmutableVector(v))
    }

    /// `v`'s elements as they are now, in a vector that can't change: `v` itself if it's
    /// already immutable, otherwise a copy.
    pub fn freeze(&self, v: AnyVector<'gc>) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        match v {
            AnyVector::Immutable(v) => Ok(v),
            AnyVector::Mutable(v) => {
                let items = v.items(self.mc);
                let frozen = objects::ImmutableVector::new(self.mc, items.len(), Value::NIL)?;
                frozen.items(self.mc).copy_from(self.mc, items);
                Ok(ImmutableVector(frozen))
            }
        }
    }
}

fn fill<'gc>(mc: &Mutation<'gc>, slots: Slots<'gc>, items: impl Iterator<Item = Value<'gc>>) {
    for (i, item) in items.enumerate().take(slots.len()) {
        slots.set(mc, i, item);
    }
}
