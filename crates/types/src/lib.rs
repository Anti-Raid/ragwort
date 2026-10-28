//! Ragwort's data types in the arena: numbers, strings and symbols, with the arena as the
//! host that `ragwort-num` and `ragwort-string` work over.

pub use ragwort_gc as gc;

pub mod buffer;
pub mod num;
pub mod string;
pub mod symbol;

use ragwort_gc::OutOfMemory;
use ragwort_num::NumError;
use ragwort_string::StrError;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    OutOfMemory,
    Num(NumError),
    Str(StrError),
}

impl From<OutOfMemory> for Error {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<NumError> for Error {
    fn from(e: NumError) -> Self {
        Self::Num(e)
    }
}

impl From<StrError> for Error {
    fn from(e: StrError) -> Self {
        Self::Str(e)
    }
}
