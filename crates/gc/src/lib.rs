//! The arena: a garbage collected heap for one interpreter, with segmented stacks.
//!
//! `SOUNDNESS.md` explains why the unsafe code is sound, and the `SAFETY` comments cite its
//! invariants by name.

#![warn(clippy::undocumented_unsafe_blocks)]

extern crate self as ragwort_gc;

mod arena;
mod budget;
mod heap;
mod host;
mod layout;
mod lock;
mod ptr;
mod region;
mod root;
mod stack;
mod table;
mod weak;
mod trace;
mod value;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod value_tests;
#[cfg(test)]
mod stack_tests;

#[doc(hidden)]
pub mod compile_fail;

pub use arena::{Arena, Corrupted, Metrics, Mutation, Phase, Rootable, StepError, max_items};
pub use budget::OutOfMemory;
pub use host::{AnyHostRef, HostRef};
pub use layout::REGION;
pub use lock::{Batch, Lock};
pub use ptr::{AnyRef, Gc, Member, TypeTag};
pub use root::{ForeignRoot, Root, Rooted};
pub use stack::{Frame, Segment, Stack, WINDOW};
pub use trace::{Inline, Plain, Trace, Tracer};
pub use value::{Unpacked, Value};
pub use weak::{Ephemeron, Weak};

pub use ragwort_derive::{Plain, Trace};

pub(crate) type Invariant<'gc> = std::marker::PhantomData<std::cell::Cell<&'gc ()>>;
