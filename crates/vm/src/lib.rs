//! Ragwort's virtual machine: register-based bytecode run over the arena's segmented stacks.

mod args;
mod coroutine;
mod equal;
pub mod frame;
mod intrinsic;
pub mod keyword;
mod machine;
pub mod module;
pub mod objects;
mod op;
mod prompts;
mod read;
mod request;
mod run;
mod segments;
mod syntax;
pub mod syntax_case;
mod wind;

pub use segments::CHUNK;
pub use intrinsic::Intrinsic;
pub use machine::{MIN_SEGMENT, Machine, Outcome, SEGMENT};
pub use module::{Deferred, HostArgs, HostContext, HostDef, HostFn, Purity, Reply};
pub use op::{Capture, Context, Control, Fault, Fuel, Op};
pub use read::Read;
pub use request::Request;
