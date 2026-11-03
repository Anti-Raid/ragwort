//! Ragwort's data types in the arena: numbers, strings, symbols, pairs, vectors and syntax, and
//! the compiler's constant pools. The arena is `ragwort-gc-words`, which holds the strings and
//! numbers itself; this crate adds the rest, as views of objects only it can change.

pub use ragwort_gc_words as gc;
pub use ragwort_gc_words::Error;

pub mod constant;
pub mod num;
mod objects;
pub mod pair;
pub mod string;
pub mod symbol;
pub mod syntax;
pub mod vector;
