//! Ragwort's virtual machine: register-based bytecode run over the arena's segmented stacks.

mod equal;
pub mod frame;
mod intrinsic;
mod machine;
pub mod objects;
mod op;
mod prompts;
mod request;
mod run;
mod segments;

pub use segments::CHUNK;
pub use intrinsic::Intrinsic;
pub use machine::{MIN_SEGMENT, Machine, Outcome, SEGMENT};
pub use op::{Capture, Context, Control, Fault, Fuel, Op};
pub use request::Request;
