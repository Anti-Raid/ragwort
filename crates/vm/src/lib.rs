//! Ragwort's virtual machine: executes register-based bytecode using segmented stacks allocated in the garbage-collected arena.

mod args;
mod coroutine;
mod equal;
pub mod image;
pub mod frame;
mod intrinsic;
pub mod keyword;
mod machine;
pub mod module;
pub mod objects;
mod op;
mod prompts;
pub mod report;
pub mod structs;
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
pub use request::Request;
