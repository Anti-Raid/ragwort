//! The VM's objects. Their type numbers follow ragwort-types' own.

use ragwort_types::gc::{Segment, objects};

use crate::{Capture, Fault, Op};

#[cfg(test)]
#[path = "tests/objects.rs"]
mod tests;

objects! {
    pub kind Vm;

    /// A function's code: its instructions, the constant table they index, shared by what was
    /// compiled with it, where its closures' upvalues come from, one capture for each, how many
    /// arguments it takes, as Chez encodes it: `n >= 0` for exactly `n`, `-(n + 1)` for at least
    /// `n`, the rest in a list, and the [`Module`] it's from, if any.
    pub struct Bytecode {
        ops: Frozen<std::boxed::Box<[Op]>>,
        constants: Value,
        captures: Frozen<std::boxed::Box<[Capture]>>,
        arity: i64,
        module: Member<Module>,
    }
    /// A `syntax-case` pattern, and the literals and data it refers to: see
    /// [`syntax_case`](crate::syntax_case).
    pub struct SyntaxPattern { shape: Frozen<std::boxed::Box<crate::syntax_case::PatternShape>> } items Value
    /// A `syntax` template, and the syntax it's made of.
    pub struct SyntaxTemplate { shape: Frozen<std::boxed::Box<crate::syntax_case::TemplateShape>> } items Value
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
    /// A prompt, as Racket CS keeps one: a frame of the metacontinuation. `chain`,
    /// `attachments` and `winders` are the continuation the prompt returns to, which its body
    /// doesn't see: it runs on an empty one. An abort to `tag` calls `handler` there. A prompt a
    /// composable continuation pushes to return to where it's called has no tag, only void.
    pub struct Prompt { tag: Value, handler: Value, chain: Value, attachments: Value, winders: Value }
    /// A continuation prompt tag. `name` is what `make-continuation-prompt-tag` was given, or
    /// void.
    pub struct Tag { name: Value }
    /// A continuation, which is called like a procedure: the records of `chain` and the prompts
    /// in the list `prompts`, up to a prompt it doesn't include. `attachments` are the marks
    /// where it was captured, with those of a frame it was captured in tail position of, whose
    /// continuation it is, and `winders` the task's there. A composable one goes on on top of
    /// the continuation it's called in; an `escape`, as `call/cc` makes, replaces that one up to
    /// the nearest default prompt.
    pub struct Continuation { chain: Value, attachments: Value, winders: Value, prompts: Value, escape: bool }
    /// An error object: `fault` says what went wrong, and for [`Fault::Error`], `message` and
    /// `irritants` are what `error` was called with.
    pub struct Condition { fault: Frozen<Fault>, message: Value, irritants: Value }
    /// What `dynamic-wind` runs on the way in and out: a task's `winders`, and a prompt's, hold
    /// a list of them for a prompt's part of the continuation, innermost first.
    pub struct Winder { before: Value, after: Value }
    /// What `guard` and `co/try-resume` put in the handlers mark: a raise that reaches it goes
    /// back to where it was set and calls `handler` there with what was raised, or if that's
    /// `#f`, returns `#f` and it, with the task's winders as `winders` were. It's kept where it
    /// goes back to: in the register under the frame of the thunk it was set for, or in a
    /// [`Native`] record the outer loop pushed.
    pub struct Guard { handler: Value, winders: Value }
    /// A record of a chain that the VM goes on from itself: once what's above it returns, its
    /// `kind` says what to do next, with `a` and `b`. `attachments` and
    /// `next` are as a [`Frames`] record's. It's never changed, so a continuation can go on from
    /// it any number of times.
    pub struct Native { kind: u32, a: Value, b: Value, attachments: Value, next: Value }
    /// A coroutine, and what a [`crate::Machine`] keeps of the one it runs in the arena: the
    /// accumulator between runs, the chain of records under its stack, its marks, as a list of
    /// `(key . value)` pairs, its [`Winder`]s, as `dynamic-wind` sets them, up to the nearest
    /// prompt, and the list of prompts the chain runs under. `spare` is a segment
    /// the stack left, which an overflow takes from `spare_base` up.
    ///
    /// `body` is the procedure it starts with, until it does. `resumer` is the task that resumed
    /// it, and `resumed` the one it's resuming, if any. While it's suspended, its frames are on
    /// `segment` from `base` up, or if it has none, its chain holds them all. `state` says
    /// whether it's pending, running, finished or failed.
    pub struct Task {
        acc: Value,
        chain: Value,
        attachments: Value,
        winders: Value,
        prompts: Value,
        spare: Member<Segment>,
        spare_base: u32,
        body: Value,
        resumer: Value,
        resumed: Value,
        segment: Member<Segment>,
        base: u32,
        state: u32,
    }
    /// A module, which ragwort code sees only as a whole: its variables, its items, each
    /// `UNDEFINED` until it's defined, which its code's slot instructions read and write, their
    /// names, for messages, in the immutable vector `names`, the host functions its native code
    /// calls, which [`Op::CallHost`] indexes, and what the compiler knows of what it exports,
    /// for the code that requires it.
    pub struct Module {
        name: Value,
        names: Value,
        hosts: Frozen<&'static [crate::module::HostDef]>,
        interface: Frozen<std::boxed::Box<dyn std::any::Any>>,
    } items Value
    /// Something of the host's, for its procedures to be passed, such as a machine's own state:
    /// `data` outside the arena, dropped once the object is collected, and `held`, which the
    /// collector traces, for what of the arena's the host keeps with it.
    pub struct ExternalRef { held: Value, data: Frozen<std::boxed::Box<dyn std::any::Any>> }
    /// What `(values ...)` makes of other than one value: an object like any other, which the
    /// `values` intrinsics take apart.
    pub struct MultiValue {} items Value
    /// What a `lambda` with keyword parameters makes: see [`crate::keyword`]. `keywords` are
    /// the ones it takes and `required` the ones it needs, as sorted lists.
    pub struct KeywordProcedure { plain: Value, core: Value, keywords: Value, required: Value }
    /// What a frame's code keeps past its registers, which `NewSpill` makes and `LoadSpill` and
    /// `StoreSpill` read and write. Each slot holds one value for one stretch of the code.
    pub struct Spill {} items Value
}
