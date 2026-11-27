//! Static types for the high-level embedding API.
//!
//! A value of the arena carries the lifetime of a step, so it cannot be kept after the step ends. The types of this crate have no lifetime.
//! They can be stored in Rust data, kept between steps and passed around freely.
//!
//! # The types
//!
//! - [`Value`] is any value. A value that is not an object is held as plain Rust data, such as [`Value::Integer`]. An object is held as a handle of its kind.
//! - A handle, such as [`String`] or [`Table`], keeps one object alive. It is a [`Handle`](ragwort_types::gc::Handle) that is known to hold a value of one kind.
//! - [`Weak`] is a handle that does not keep its object alive.
//!
//! This crate holds data only. It runs no code of a program. Its types are made and read inside a step, with the arena's `Mutation`.
//!
//! # Example
//!
//! ```
//! use ragwort_static_types::Value;
//! use ragwort_types::gc::Arena;
//! use ragwort_types::pair::Pairs;
//!
//! let mut arena = Arena::new(1 << 20, 0);
//! // Made in one step, and kept after it.
//! let kept = arena.mutate(|mc| {
//!     let pair = Pairs::new(mc).cons(ragwort_types::gc::Value::fixnum(1).unwrap(), ragwort_types::gc::Value::NULL).unwrap();
//!     Value::from_gc(mc, pair.value(mc)).unwrap()
//! });
//! arena.collect();
//! // Read in a later step.
//! arena.mutate(|mc| {
//!     let Value::Pair(pair) = &kept else { panic!("a pair") };
//!     assert_eq!(pair.get(mc).unwrap().head(mc).as_fixnum(), Some(1));
//! });
//! ```
//!
//! # Equality
//!
//! Two handles are equal if they hold the same object. This is the comparison of `eq?`. Two strings with the same text are not always the same object.
//!
//! # Handles and cycles
//!
//! A handle keeps its object alive whatever else happens in the arena. Rust data that an arena object owns should hold a [`Weak`] instead.
//! See [`WeakHandle`](ragwort_types::gc::WeakHandle) for the reason.

mod handle;
mod value;

#[cfg(test)]
#[path = "tests/values.rs"]
mod tests;

pub use handle::{Bytevector, Coroutine, External, Keyword, Number, Other, Pair, Procedure, String, Struct, Symbol, Table, Vector, Weak};
pub use value::{Error, Value};
