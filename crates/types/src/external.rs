//! External references: values of the host's own types that the arena holds for it.
//!
//! An [`ExternalRef`] wraps one value of a host type. A program can pass it around, store it and
//! hand it back to the host's functions, but cannot look inside. The arena drops the value once
//! nothing reaches the reference.
//!
//! # Kinds
//!
//! The host describes each of its types once, in a static [`ExternalKind`]:
//!
//! - A name, which the printer shows: a reference of the kind named `user-id` is written
//!   `#<user-id>`.
//! - How two values of the type are compared and hashed. Without that, a reference is equal
//!   only to itself.
//!
//! ```
//! use ragwort_types::external::{ExternalKind, ExternalRefs};
//! use ragwort_types::gc::{Arena, Value};
//!
//! struct UserId(u64);
//!
//! static USER_ID: ExternalKind<UserId> = ExternalKind::by_value("user-id", |first, second| first.0 == second.0, |id| id.0);
//!
//! let mut arena = Arena::new(1 << 20, 0);
//! arena.mutate(|mc| {
//!     let externals = ExternalRefs::new(mc);
//!     let ann = externals.make(&USER_ID, UserId(7), 0, Value::NIL).unwrap();
//!     let same = externals.make(&USER_ID, UserId(7), 0, Value::NIL).unwrap();
//!     assert!(ann != same && ann.same(mc, same));
//!     assert_eq!(ann.data::<UserId>(mc).map(|id| id.0), Some(7));
//!     assert_eq!(ann.name(mc), "user-id");
//! });
//! ```
//!
//! # What uses a kind's equality
//!
//! - `equal?` compares two references of a kind by its `equal`.
//! - A table takes such a reference as a key by its value: two references that are equal are
//!   one key.
//! - `eq?` and `eqv?` do not: for them a reference is the same as itself and nothing else.
//!
//! # What the host promises
//!
//! The arena relies on these and cannot check them:
//!
//! - `equal` is an equivalence: a value equals itself, and the order of the two does not matter.
//! - Values that are equal hash the same.
//! - Neither answer changes while the value lives.
//! - There is one kind for each type. References of two kinds are never equal.
//!
//! Both functions see only the two values. They cannot reach the arena or run a program. A
//! broken promise makes a table lose a key or `equal?` give a wrong answer. It cannot cause
//! memory unsafety.

use std::any::Any;

use crate::gc::{Gc, Mutation, OutOfMemory, Value};
use crate::objects::{self, Data, ExternalFields};

#[cfg(test)]
#[path = "tests/external.rs"]
mod tests;

/// What the host says of every value of type `T` it hands to the arena. See the
/// [module docs](self).
pub struct ExternalKind<T: 'static> {
    /// The name the printer shows for a reference of the kind.
    pub name: &'static str,
    /// How two values are compared and hashed, or `None` if a reference is equal only to itself.
    pub by_value: Option<ByValue<T>>,
}

/// How values of type `T` are compared and hashed. The two functions come together, because
/// a table needs both and they have to agree.
pub struct ByValue<T: 'static> {
    pub equal: fn(&T, &T) -> bool,
    pub hash: fn(&T) -> u64,
}

impl<T: 'static> ExternalKind<T> {
    /// A kind whose references are each equal only to themselves.
    pub const fn by_identity(name: &'static str) -> Self {
        Self { name, by_value: None }
    }

    /// A kind whose references are equal when `equal` says their values are.
    pub const fn by_value(name: &'static str, equal: fn(&T, &T) -> bool, hash: fn(&T) -> u64) -> Self {
        Self { name, by_value: Some(ByValue { equal, hash }) }
    }
}

/// A kind with its type forgotten, as a reference keeps it.
trait Kind: 'static {
    fn name(&self) -> &'static str;
    /// Whether the kind compares by value and says the two are equal. `false` if either is not
    /// a value of the kind's type.
    fn equal(&self, first: &dyn Any, second: &dyn Any) -> bool;
    /// The hash of `value`, or `None` if the kind compares by identity.
    fn hash(&self, value: &dyn Any) -> Option<u64>;
}

impl<T: 'static> Kind for ExternalKind<T> {
    fn name(&self) -> &'static str {
        self.name
    }

    fn equal(&self, first: &dyn Any, second: &dyn Any) -> bool {
        match (&self.by_value, first.downcast_ref::<T>(), second.downcast_ref::<T>()) {
            (Some(by_value), Some(first), Some(second)) => (by_value.equal)(first, second),
            _ => false,
        }
    }

    fn hash(&self, value: &dyn Any) -> Option<u64> {
        Some((self.by_value.as_ref()?.hash)(value.downcast_ref::<T>()?))
    }
}

/// What a reference keeps outside the arena: the host's value and its kind.
pub(crate) struct Held {
    kind: &'static dyn Kind,
    data: Box<dyn Any>,
}

/// A reference to a value of a host type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExternalRef<'gc>(Gc<'gc, objects::External>);

impl<'gc> ExternalRef<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::External(external)) => Some(Self(external)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// The name of the reference's kind.
    pub fn name(self, mc: &Mutation<'gc>) -> &'static str {
        self.0.payload(mc).map_or("external", |held| held.kind.name())
    }

    /// The host's value, if it is a `T`.
    pub fn data<T: Any>(self, mc: &Mutation<'gc>) -> Option<&'gc T> {
        self.0.payload(mc)?.data.downcast_ref()
    }

    /// The value the reference keeps alive in the arena.
    pub fn kept(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.kept(mc)
    }

    /// Whether the two are the same reference, or references of one kind that the kind says
    /// are equal.
    pub fn same(self, mc: &Mutation<'gc>, other: Self) -> bool {
        if self == other {
            return true;
        }
        match (self.0.payload(mc), other.0.payload(mc)) {
            (Some(first), Some(second)) => first.kind.equal(&*first.data, &*second.data),
            _ => false,
        }
    }

    /// The hash the kind gives the value, or `None` if the kind compares by identity.
    pub fn hash(self, mc: &Mutation<'gc>) -> Option<u64> {
        let held = self.0.payload(mc)?;
        held.kind.hash(&*held.data)
    }
}

/// External reference operations for one step.
#[derive(Clone, Copy)]
pub struct ExternalRefs<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> ExternalRefs<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    pub fn external(&self, value: Value<'gc>) -> Option<ExternalRef<'gc>> {
        ExternalRef::of(value)
    }

    /// A reference to `data`, of the kind `kind`.
    ///
    /// - `bytes` is charged to the arena's budget for what `data` owns outside it, until the
    ///   reference is collected.
    /// - `kept` is a value of the arena that stays alive as long as the reference does, for data
    ///   that goes with the host's value. Pass [`Value::NIL`] for none.
    pub fn make<T: Any>(&self, kind: &'static ExternalKind<T>, data: T, bytes: usize, kept: Value<'gc>) -> Result<ExternalRef<'gc>, OutOfMemory> {
        let held = Held { kind, data: Box::new(data) };
        Ok(ExternalRef(objects::External::new(self.mc, kept, self.mc.frozen_owning(held, bytes)?)?))
    }
}
