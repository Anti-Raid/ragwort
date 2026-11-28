//! Fixed-length vectors. A [`Vector`] is mutable. Write its elements through
//! [`Vector::items`], which applies the write barrier. An [`ImmutableVector`], such as a literal,
//! can only be read.
//!
//! # External vectors
//!
//! A vector's elements can also be owned by the host, as an [`ExternalVector`]. An example is an
//! array in a payload that the host has decoded. A program uses it like any other vector. No
//! element is created in the arena until it is read.
//!
//! ```
//! use ragwort_types::Error;
//! use ragwort_types::gc::{Arena, Mutation, Value};
//! use ragwort_types::vector::{EveryVector, ExternalVector, Vectors};
//!
//! /// The ids that an event mentions. They are read in place from the host's `Vec`.
//! struct Mentions(Vec<i64>);
//!
//! impl ExternalVector for Mentions {
//!     fn len(&self) -> usize {
//!         self.0.len()
//!     }
//!
//!     fn get<'gc>(&self, _: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
//!         Ok(Value::fixnum(self.0[index]).expect("a small number"))
//!     }
//! }
//!
//! let mut arena = Arena::new(1 << 20, 0);
//! arena.mutate(|mc| {
//!     let vector = Vectors::new(mc).external(Mentions(vec![7, 8, 9]), 24).unwrap();
//!     let any = EveryVector::of(vector.value(mc)).unwrap();
//!     assert_eq!((any.len(mc), any.get(mc, 1), any.get(mc, 3)), (3, Ok(Value::fixnum(8)), Ok(None)));
//! });
//! ```
//!
//! What the arena does with an external vector:
//!
//! - It reads the length once, when the vector is created. A vector never changes its length.
//! - It caches each element it reads. A second read of an index returns the cached value without
//!   calling the host. So a table that the host created for an element stays the same object. A
//!   long vector caches its elements in chunks of 64, allocated on demand. So reading one element
//!   of ten thousand does not allocate room for all of them.
//! - It rejects a write to a vector whose type does not set [`ExternalVector::WRITABLE`].
//!
//! What the host promises. The arena relies on these promises and cannot check them:
//!
//! - The number of elements never changes.
//! - The value that `get` returns for an index never changes, except through the vector's own
//!   `set`. For a type that is not writable it never changes at all.
//! - No method calls back into the vector it is called on.
//!
//! A broken promise makes the vector return wrong or stale values. It cannot cause memory
//! unsafety: the arena never requests an index at or past the length it read.
//!
//! [`AnyVector`] is a vector stored in the arena. The arena's own data is built from such
//! vectors. [`EveryVector`] is any vector a program can hold, including an external one.

use std::any::Any;
use std::cell::{Ref, RefCell};

use crate::Error;
use crate::gc::{Gc, Mutation, OutOfMemory, Slots, Value};
use crate::objects::{self, Data, ExternVectorFields, ImmutableVectorFields, VectorFields};
pub use crate::table::Refused;

#[cfg(test)]
#[path = "tests/vector.rs"]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Vector<'gc>(Gc<'gc, objects::Vector>);

impl<'gc> Vector<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Vector(vector)) => Some(Self(vector)),
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
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::ImmutableVector(vector)) => Some(Self(vector)),
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
        if index < items.len() {
            Some(items.get(index))
        } else {
            None
        }
    }
}

/// A mutable or immutable vector in the arena, for reading.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AnyVector<'gc> {
    Mutable(Vector<'gc>),
    Immutable(ImmutableVector<'gc>),
}

impl<'gc> AnyVector<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Vector(vector)) => Some(Self::Mutable(Vector(vector))),
            Some(Data::ImmutableVector(vector)) => Some(Self::Immutable(ImmutableVector(vector))),
            _ => None,
        }
    }

    fn items(self, mc: &Mutation<'gc>) -> Slots<'gc> {
        match self {
            Self::Mutable(vector) => vector.0.items(mc),
            Self::Immutable(vector) => vector.0.items(mc),
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
        if index < items.len() {
            Some(items.get(index))
        } else {
            None
        }
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(vector) => vector.value(mc),
            Self::Immutable(vector) => vector.value(mc),
        }
    }
}

/// The error of a failed write to a vector.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VectorError {
    /// The vector is immutable, or it is an external vector that programs cannot modify.
    Immutable,
    /// The host rejected the value. See [`Refused`].
    Refused,
    /// The index is not below the vector's length.
    OutOfRange,
    Arena(Error),
}

impl From<Error> for VectorError {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

impl From<OutOfMemory> for VectorError {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

/// A vector whose elements are owned by the host. See the [module docs](self) for what the arena
/// does with an external vector and what the host promises.
///
/// A type is read-only unless it sets [`ExternalVector::WRITABLE`] and implements `set`.
pub trait ExternalVector: 'static {
    /// Whether programs can modify the vector. It is read once, when the vector is created.
    const WRITABLE: bool = false;

    /// Returns the number of elements. It is called once, when the vector is created.
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the element at `index`, allocated in the arena. `index` is always less than the
    /// length the vector was created with.
    fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error>;

    /// Sets the element at `index`. `index` is always less than the length the vector was created
    /// with. The host must copy the data it needs out of `value` during the call. It cannot keep
    /// `value` itself.
    fn set<'gc>(&mut self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Refused> {
        let _ = (mc, index, value);
        Err(Refused)
    }
}

/// A type-erased [`ExternalVector`], as stored in a vector object.
pub(crate) trait HostedVector: 'static {
    fn fetch<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error>;
    fn store<'gc>(&mut self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Refused>;
    fn as_any(&self) -> &dyn Any;
}

impl<T: ExternalVector> HostedVector for T {
    fn fetch<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
        self.get(mc, index)
    }

    fn store<'gc>(&mut self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Refused> {
        self.set(mc, index, value)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// The number of consecutive elements of a long external vector that one chunk caches. See
/// [`ExternVector::remembered`].
const CHUNK: usize = 64;

/// A vector whose elements are owned by the host.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExternVector<'gc>(Gc<'gc, objects::ExternVector>);

impl<'gc> ExternVector<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::ExternVector(vector)) => Some(Self(vector)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.count(mc) as usize
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// Returns whether programs can modify the vector.
    pub fn is_writable(self, mc: &Mutation<'gc>) -> bool {
        self.0.writable(mc)
    }

    /// Returns the host's value behind the vector, or `None` if it is not a `T`.
    pub fn host<T: ExternalVector>(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        Ref::filter_map(self.0.host(mc)?.try_borrow().ok()?, |host| host.as_any().downcast_ref::<T>()).ok()
    }

    /// Returns the element at `index`, or `None` if `index` is out of range. The element is read
    /// from the host on first access and cached.
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Result<Option<Value<'gc>>, Error> {
        if index >= self.len(mc) {
            return Ok(None);
        }
        if let Some(known) = self.remembered(mc, index) {
            return Ok(Some(known));
        }
        let Some(host) = self.0.host(mc).and_then(|host| host.try_borrow().ok()) else { return Ok(None) };
        let value = host.fetch(mc, index)?;
        drop(host);
        self.remember(mc, index, value)?;
        Ok(Some(value))
    }

    /// Sets the element at `index`, both in the host and in the cache of elements read.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), VectorError> {
        if !self.0.writable(mc) {
            return Err(VectorError::Immutable);
        }
        if index >= self.len(mc) {
            return Err(VectorError::OutOfRange);
        }
        let host = self.0.host(mc).ok_or(VectorError::Refused)?;
        host.try_borrow_mut().map_err(|_| VectorError::Refused)?.store(mc, index, value).map_err(|Refused| VectorError::Refused)?;
        // Cache the value that the program stored. A later read then returns that same value, as it does for a vector in the arena.
        self.remember(mc, index, value)?;
        Ok(())
    }

    /// Returns the cached element at `index`, or `None` if it has not been read yet. `index` must
    /// be less than the length.
    ///
    /// The elements read so far are cached in arena vectors that are allocated on demand.
    /// [`Value::BROKEN`] marks an element that has not been read yet:
    ///
    /// - An external vector of up to [`CHUNK`] elements has one cache vector, of its own length.
    /// - A longer external vector has a vector of chunks. Each chunk caches [`CHUNK`] consecutive
    ///   elements. A chunk is allocated when one of its elements is first read.
    ///
    /// So reading a few elements of a long vector allocates a few chunks, not a slot for every
    /// element. Reading all of them costs little more than one vector of the full length.
    fn remembered(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let memo = self.0.memo(mc)?.items(mc);
        let known = if self.len(mc) <= CHUNK {
            memo.get(index)
        } else {
            Vector::of(memo.get(index / CHUNK))?.items(mc).get(index % CHUNK)
        };
        if known != Value::BROKEN {
            Some(known)
        } else {
            None
        }
    }

    /// Caches `value` as the element at `index`. `index` must be less than the length. See [`ExternVector::remembered`].
    fn remember(self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Error> {
        let len = self.len(mc);
        let memo = match self.0.memo(mc) {
            Some(memo) => memo,
            None => {
                // Both layouts start filled with `Value::BROKEN`. In the vector of chunks, each slot holds a chunk's value, and `Value::BROKEN` marks a chunk that is not allocated yet.
                let slots = if len <= CHUNK {
                    len
                } else {
                    len.div_ceil(CHUNK)
                };
                let memo = objects::Vector::new(mc, slots, Value::BROKEN)?;
                self.0.set_memo(mc, Some(memo));
                memo
            }
        };
        if len <= CHUNK {
            memo.items(mc).set(mc, index, value);
            return Ok(());
        }
        let chunk = match Vector::of(memo.items(mc).get(index / CHUNK)) {
            Some(chunk) => chunk,
            None => {
                let chunk = Vector(objects::Vector::new(mc, CHUNK.min(len - index / CHUNK * CHUNK), Value::BROKEN)?);
                memo.items(mc).set(mc, index / CHUNK, chunk.value(mc));
                chunk
            }
        };
        chunk.items(mc).set(mc, index % CHUNK, value);
        Ok(())
    }
}

/// Any vector a program can hold: a vector in the arena, or an external vector whose elements are owned by the host.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EveryVector<'gc> {
    Arena(AnyVector<'gc>),
    External(ExternVector<'gc>),
}

impl<'gc> EveryVector<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Vector(vector)) => Some(Self::Arena(AnyVector::Mutable(Vector(vector)))),
            Some(Data::ImmutableVector(vector)) => Some(Self::Arena(AnyVector::Immutable(ImmutableVector(vector)))),
            Some(Data::ExternVector(vector)) => Some(Self::External(ExternVector(vector))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Arena(vector) => vector.value(mc),
            Self::External(vector) => vector.value(mc),
        }
    }

    #[inline]
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self {
            Self::Arena(vector) => vector.len(mc),
            Self::External(vector) => vector.len(mc),
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// Returns the element at `index`, or `None` if `index` is out of range. An external vector
    /// reads the element from its host on first access, which can fail if allocation fails.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Result<Option<Value<'gc>>, Error> {
        match self {
            Self::Arena(vector) => Ok(vector.get(mc, index)),
            Self::External(vector) => vector.fetch(mc, index),
        }
    }

    /// Returns whether the vector can be written to.
    pub fn is_writable(self, mc: &Mutation<'gc>) -> bool {
        match self {
            Self::Arena(vector) => vector.is_mutable(),
            Self::External(vector) => vector.is_writable(mc),
        }
    }

    /// Sets the element at `index`. See [`VectorError`] for the ways this can fail.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), VectorError> {
        match self {
            Self::Arena(AnyVector::Mutable(vector)) => {
                let items = vector.items(mc);
                if index >= items.len() {
                    return Err(VectorError::OutOfRange);
                }
                items.set(mc, index, value);
                Ok(())
            }
            Self::Arena(AnyVector::Immutable(_)) => Err(VectorError::Immutable),
            Self::External(vector) => vector.set(mc, index, value),
        }
    }
}

impl<'gc> ExternVector<'gc> {
    /// Calls [`ExternVector::get`]. It is kept out of line so that the code for reading a vector in the arena stays small.
    #[inline(never)]
    fn fetch(self, mc: &Mutation<'gc>, index: usize) -> Result<Option<Value<'gc>>, Error> {
        self.get(mc, index)
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

    pub fn vector(&self, value: Value<'gc>) -> Option<AnyVector<'gc>> {
        AnyVector::of(value)
    }

    /// Returns `value` as a mutable vector, or `None` if it is not one.
    pub fn mutable(&self, value: Value<'gc>) -> Option<Vector<'gc>> {
        Vector::of(value)
    }

    /// Returns a vector of `len` copies of `fill`.
    pub fn make(&self, len: usize, fill: Value<'gc>) -> Result<Vector<'gc>, OutOfMemory> {
        objects::Vector::new(self.mc, len, fill).map(Vector)
    }

    pub fn from_slice(&self, items: &[Value<'gc>]) -> Result<Vector<'gc>, OutOfMemory> {
        let vector = self.make(items.len(), Value::NULL)?;
        fill(self.mc, vector.items(self.mc), items.iter().copied());
        Ok(vector)
    }

    /// Returns a vector whose elements are owned by `host`. See the [module docs](self).
    ///
    /// `bytes` is the size of the memory that `host` owns. It is charged to the arena's budget
    /// until the vector is collected and `host` is dropped.
    pub fn external<T: ExternalVector>(&self, host: T, bytes: usize) -> Result<ExternVector<'gc>, OutOfMemory> {
        let len = host.len() as u64;
        let host: RefCell<Box<dyn HostedVector>> = RefCell::new(Box::new(host));
        objects::ExternVector::new(self.mc, len, T::WRITABLE, None, self.mc.frozen_owning(host, bytes)?).map(ExternVector)
    }

    pub fn immutable_from_slice(&self, items: &[Value<'gc>]) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        self.immutable_with(items.len(), |i| items[i])
    }

    pub fn immutable_with(&self, len: usize, fill: impl FnMut(usize) -> Value<'gc>) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        let vector = objects::ImmutableVector::new(self.mc, len, Value::NULL)?;
        self::fill(self.mc, vector.items(self.mc), (0..len).map(fill));
        Ok(ImmutableVector(vector))
    }

    /// Returns an immutable vector with the current elements of `vector`. This is `vector` itself
    /// if it is already immutable, and a copy otherwise.
    pub fn freeze(&self, vector: AnyVector<'gc>) -> Result<ImmutableVector<'gc>, OutOfMemory> {
        match vector {
            AnyVector::Immutable(immutable) => Ok(immutable),
            AnyVector::Mutable(mutable) => {
                let items = mutable.items(self.mc);
                let frozen = objects::ImmutableVector::new(self.mc, items.len(), Value::NULL)?;
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
