//! The VM's objects. Their type numbers follow ragwort-types' own.

use ragwort_types::gc::{Segment, objects};

use crate::{Capture, Fault, Op};

#[cfg(test)]
#[path = "tests/objects.rs"]
mod tests;

objects! {
    pub kind Vm;

    /// A function's code: its instructions, the module's constant table they index, where its
    /// closures' upvalues come from, one capture for each, and how many arguments it takes, as
    /// Chez encodes it: `n >= 0` for exactly `n`, `-(n + 1)` for at least `n`, the rest in a list.
    pub struct Bytecode {
        ops: Frozen<std::boxed::Box<[Op]>>,
        constants: Value,
        captures: Frozen<std::boxed::Box<[Capture]>>,
        arity: i64,
    }
    /// A procedure: its code, and the values it captured, which `LoadUpvalue` reads.
    pub struct Closure { code: Member<Bytecode> } items Value
    /// An assigned variable, shared by the closures that capture it.
    pub struct Box { value: Value }
    /// Frames handed to a continuation, as Chez's continuation objects hold them: slots
    /// `start..end` of `segment`, which the stack no longer writes. They end where the frame
    /// above them would start, and `link` is that frame's link, where the top one goes on.
    /// `next` is the record below, or `#f`.
    ///
    /// `attachments` are the marks to restore when they're resumed, so a mark set above them is
    /// gone once they return. A `one_shot` record no continuation holds, so it's resumed in place
    /// rather than copied: on the stack's own segment if it ends where the stack's frames start,
    /// or, if it `owns` the rest of its segment, as an overflow leaves it, by moving back onto it.
    pub struct Frames {
        segment: Member<Segment>,
        start: u32,
        end: u32,
        link: Value,
        attachments: Value,
        one_shot: bool,
        owns: bool,
        next: Value,
    }
    /// A prompt, as Racket CS keeps one: a frame of the metacontinuation. `chain` and
    /// `attachments` are the continuation the prompt returns to, which its body doesn't see: it
    /// runs on an empty one. An abort to `tag` calls `handler` there. A prompt a composable
    /// continuation pushes to return to where it's called has no tag, only void.
    pub struct Prompt { tag: Value, handler: Value, chain: Value, attachments: Value }
    /// A continuation prompt tag. `name` is what `make-continuation-prompt-tag` was given, or
    /// void.
    pub struct Tag { name: Value }
    /// A composable continuation, which is called like a procedure: the records of `chain` and
    /// the prompts in the list `prompts`, up to a prompt it doesn't include.
    pub struct Continuation { chain: Value, prompts: Value }
    /// An error object: `fault` says what went wrong, and for [`Fault::Error`], `message` and
    /// `irritants` are what `error` was called with.
    pub struct Condition { fault: Frozen<Fault>, message: Value, irritants: Value }
    /// What a [`crate::Machine`] keeps in the arena: the accumulator between runs, the chain
    /// of records under its stack, its marks, as a list of `(key . value)` pairs, the list of
    /// prompts the chain runs under, and the procedure VM faults are passed to. `spare` is a
    /// segment the stack left, which an overflow takes from `spare_base` up.
    pub struct Task {
        acc: Value,
        chain: Value,
        attachments: Value,
        prompts: Value,
        fault: Value,
        spare: Member<Segment>,
        spare_base: u32,
    }
    /// What `(values ...)` makes of other than one value: an object like any other, which the
    /// `values` intrinsics take apart.
    pub struct MultiValue {} items Value
}
