//! Ragwort's data in the arena. The collector is in [`gc`]. The other modules define the types
//! that the arena holds: numbers, strings, symbols, pairs, vectors, tables, external references
//! and syntax, and the compiler's constant pools. Pairs, symbols, vectors, tables, external
//! references and syntax are views of objects that only this crate can modify.

extern crate self as ragwort_types;

pub use gc::Error;
pub use ragwort_derive::{Wire, named};
pub use wire::Wire;

/// The error for a name that no variant of an enum has. The `FromStr` implementation that [`named!`] generates returns it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnknownName;

pub mod bytevector;
pub mod constant;
pub mod external;
pub mod gc;
pub mod num;
mod objects;
pub mod pair;
pub mod string;
pub mod symbol;
pub mod syntax;
pub mod table;
pub mod vector;
pub mod wire;
