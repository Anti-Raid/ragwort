mod arena;
mod budget;
mod heap;
mod host;
mod layout;
mod lock;
mod ptr;
mod region;
mod root;
mod table;
mod weak;
mod trace;
mod value;
mod vec;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod value_tests;

#[doc(hidden)]
pub mod compile_fail;

pub use arena::{Arena, Metrics, Mutation, Phase, Rootable, StepError};
pub use budget::OutOfMemory;
pub use host::{AnyHostRef, HostRef};
pub use layout::REGION;
pub use lock::{Lock, RefLock};
pub use ptr::{AnyRef, Gc, Member, TypeTag};
pub use root::{ForeignRoot, Root, Rooted};
pub use trace::{Inline, Plain, Trace, Tracer};
pub use value::{Unpacked, Value};
pub use vec::{Array, GcVec};
pub use weak::{Ephemeron, Weak};

pub use ragwort_derive::{Plain, Trace};

pub(crate) type Invariant<'gc> = std::marker::PhantomData<std::cell::Cell<&'gc ()>>;
