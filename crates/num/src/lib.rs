//! Racket's numeric tower over any heap: fixnums, bignums, exact rationals, flonums and
//! complex numbers. Each layer has a host trait the heap implements, [`Host`] for integers,
//! then [`RationalHost`], [`RealHost`] and [`ComplexHost`], and the library does the rest.

pub mod bigint;
mod cfloat;
pub mod complex;
pub mod int;
pub mod rational;
pub mod real;

#[cfg(test)]
#[path = "tests/complex.rs"]
mod complex_tests;
#[cfg(test)]
#[path = "tests/int.rs"]
mod int_tests;
#[cfg(test)]
#[path = "tests/rational.rs"]
mod rational_tests;
#[cfg(test)]
#[path = "tests/real.rs"]
mod real_tests;
#[cfg(test)]
mod testing;

pub use complex::{ComplexHost, ComplexView};
pub use int::{Host, IntView, NumError, Rounding};
pub use rational::{RationalHost, RationalView};
pub use real::{RealHost, RealView};
