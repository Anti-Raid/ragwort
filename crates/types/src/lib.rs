//! Ragwort's data in the arena: the collector, in [`gc`], and the types it holds: numbers,
//! strings, symbols, pairs, vectors and syntax, and the compiler's constant pools. Pairs,
//! symbols, vectors and syntax are views of objects only this crate can change.

extern crate self as ragwort_types;

pub use gc::Error;
pub use ragwort_derive::{Wire, named};
pub use wire::Wire;

/// A name none of an enum's variants has, from the `FromStr` that [`named!`] writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnknownName;

pub mod bytevector;
pub mod constant;
pub mod gc;
pub mod num;
mod objects;
pub mod pair;
pub mod string;
pub mod symbol;
pub mod syntax;
pub mod vector;
pub mod wire;
