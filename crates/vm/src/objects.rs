//! Garbage-collected object types used by the virtual machine. Type identifiers extend the base types in `ragwort-types`.

use ragwort_types::gc::{Segment, objects};

use crate::{Capture, Op};

#[cfg(test)]
#[path = "tests/objects.rs"]
mod tests;

/// The number of places that a hinted table instruction remembers. See [`Hints`].
pub const HINT_WAYS: usize = 4;
/// The number of slots that one hinted table instruction has in a [`Hints`] object: a shape and a position for each place, and the key.
pub const HINT_SLOTS: usize = 2 * HINT_WAYS + 1;
/// The slot that holds the key of a hinted table instruction, counted from the first slot of the instruction.
pub const HINT_KEY: usize = 2 * HINT_WAYS;

objects! {
    pub kind Vm;

    /// Compiled procedure bytecode. `ops` is the instruction array ([`Op`]). `constants` is the constant pool table, which is shared across code compiled together. `captures` describes the source of each upvalue of a closure created from the code. `arity` is the encoded parameter arity, which follows Chez Scheme conventions. `module` is an optional reference to the enclosing [`Module`].
    pub struct Bytecode {
        ops: Frozen<std::boxed::Box<[Op]>>,
        constants: Value,
        captures: Frozen<std::boxed::Box<[Capture]>>,
        arity: i64,
        module: Member<Module>,
        /// The procedure's name as a symbol, `#f` for an anonymous procedure, or void for the code of a top-level form.
        name: Value,
        /// The source that defines the procedure, as the value of a `SyntaxSource`, or `#f` when the source is unknown.
        source: Value,
        /// The byte offset in `source` where the procedure's definition starts.
        start: u32,
        /// The [`Sites`] object holding the position table of the code this function was compiled with, or `#f` if no positions were recorded.
        sites: Value,
        /// The first row of this function in that table, and the number of rows it owns.
        lines_start: u32,
        lines_len: u32,
        /// [`HINT_SLOTS`] slots for each hinted table instruction of the code, or none if it has no such instruction. See [`Hints`].
        hints: Member<Hints>,
    }
    /// The hints of the hinted table instructions of one [`Bytecode`]. Each instruction has [`HINT_WAYS`] places where it found its key before, the most recent first. A place is two slots:
    ///
    /// - The shape of the table in which the key was found, or `#f` if that table had no shape.
    /// - The position of the entry, as a fixnum. It is `#f` in a place that is not used yet.
    ///
    /// A table with a remembered shape has the key at the remembered position. See `Table::get_hinted`. Several places let one instruction read tables of several shapes in turn, such as events of different kinds, without searching each time.
    ///
    /// The slot after the places holds the key of the instruction, which is a constant. The compiler stores it when it makes the code. An instruction needs the key only when no place has the shape of its table, so the key is kept here and not loaded into a register.
    ///
    /// The instructions of the code are immutable and shared, so the hints are kept in this object and not in the instructions.
    pub struct Hints {} items Value
    /// The source positions of code compiled together (see [`crate::report::Table`]). The items are the sources and procedure names that the table's rows refer to by index.
    pub struct Sites { table: Frozen<crate::report::Table> } items Value
    /// A compiled `syntax-case` pattern descriptor along with the literal identifiers and pattern data it references (see [`crate::syntax_case`]).
    pub struct SyntaxPattern { shape: Frozen<std::boxed::Box<crate::syntax_case::PatternShape>> } items Value
    /// A compiled `syntax` template descriptor and its constituent syntax objects used for macro output expansion.
    pub struct SyntaxTemplate { shape: Frozen<std::boxed::Box<crate::syntax_case::TemplateShape>> } items Value
    /// A procedure closure: pairs a compiled [`Bytecode`] object with its captured upvalue environment, read by `LoadUpvalue`.
    pub struct Closure { code: Member<Bytecode> } items Value
    /// A mutable heap cell (indirection box) representing a mutated variable shared across multiple capturing closures.
    pub struct Box { value: Value }
    /// A slice of stack frames preserved for a continuation, modeled after Chez Scheme continuation records: occupies slots `start..end` within `segment` that are protected from stack overwrites. They end at the boundary where the overlying frame would begin, with `link` specifying the return link where the topmost frame resumes, and `next` referencing the next record down the continuation chain (or `#f`).
    ///
    /// `attachments` contains continuation marks restored upon resumption so that marks created above them disappear upon return. `one_shot` is true when no captured continuation holds the record. A one-shot record can be resumed in place, without copying its frames back onto the stack. This happens in two cases. If the frames are on the stack's current segment, directly below the active frames, the stack takes them back. If `owns` is true, as after a stack overflow, the stack moves back onto the record's segment.
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
    /// A delimited continuation prompt, represented as a frame in the metacontinuation (modeled after Racket CS). `chain`, `attachments`, and `winders` preserve the outer continuation to which the prompt eventually returns, isolating it from the prompt body. An abort targeting `tag` transfers control to `handler`. Prompts pushed by composable continuations to resume execution at their call site carry no prompt tag (storing void).
    pub struct Prompt { tag: Value, handler: Value, chain: Value, attachments: Value, winders: Value }
    /// A continuation prompt tag used for delimited control. `name` holds the optional name passed to `make-continuation-prompt-tag`, or void.
    pub struct Tag { name: Value }
    /// A first-class, callable continuation object: encapsulates the continuation record chain (`chain`) and delimited prompts (`prompts`) delimited by an enclosing prompt. `attachments` preserves continuation marks present at capture time (including any tail-position marks from the capturing frame), and `winders` records the dynamic-wind stack. A composable continuation splices on top of the calling continuation; an `escape` continuation (created by `call/cc`) aborts and replaces the current continuation up to the nearest default prompt.
    pub struct Continuation { chain: Value, attachments: Value, winders: Value, prompts: Value, escape: bool }
    /// An exception condition object: `failure` classifies the error type and names the operation that raised it, while `message` and `irritants` hold the error message and detail values passed to `error`. For a fault raised by the VM, `message` is void and `irritants` holds the values the failed operation was given. `trace` is `#f` until the condition is first raised, and then holds the call trace recorded by [`crate::report`].
    pub struct Condition { failure: Frozen<crate::report::Failure>, message: Value, irritants: Value, trace: Value }
    /// Represents a `dynamic-wind` guard holding `before` and `after` thunks executed when entering or exiting a dynamic extent. Maintained innermost-first in task and prompt winders lists.
    pub struct Winder { before: Value, after: Value }
    /// An exception handler record installed by `guard` or `co/try-resume` in continuation marks. When a raised value reaches this guard, execution unwinds to the point where the guard was installed and restores `winders`, the winders that were active at that point. It then calls `handler` with the raised value. If `handler` is `#f`, it returns `#f` and the value instead. `traced` is false for `guard/no-traceback`, and a condition that such a guard catches records no call trace. The guard is stored in a register beneath the protected thunk's frame, or in an outer [`Native`] continuation record.
    pub struct Guard { handler: Value, winders: Value, traced: bool }
    /// A continuation boundary record representing an internal VM control point on the stack chain. When overlying frames return, `kind` specifies the next VM action using operands `a` and `b`. `attachments` and `next` function like those in [`Frames`]. Immutable once constructed, allowing a continuation to resume from it repeatedly.
    pub struct Native { kind: u32, a: Value, b: Value, attachments: Value, next: Value }
    /// A coroutine task: the execution state of one coroutine, allocated in the arena and run by a [`crate::Machine`]. `acc` preserves the result accumulator between run steps. `chain` is the chain of continuation records. `attachments` holds the continuation marks as an association list of `(key . value)` pairs. `winders` lists the active [`Winder`]s, and `prompts` lists the enclosing delimited prompts. `spare` and `spare_base` hold a cached stack segment that is reused on stack overflow.
    ///
    /// `body` contains the initial entry procedure before execution begins. While `co/reset` is closing the coroutine, it holds the new body instead. `resumer` points to the task that resumed this one, while `resumed` points to any task currently resumed by it. While suspended, active stack frames reside on `segment` starting at `base` (or are preserved entirely within `chain`). `state` tracks whether the coroutine is pending, running, dead, failed, or being closed.
    ///
    /// `idle` of a machine's root task is a vector of the suspended coroutines whose frames stay on the segment they ran on, or `#f` before the first one. See `coroutine::idle`.
    ///
    /// `values` preserves the accumulator's list of values between run steps, as `acc` preserves the accumulator.
    ///
    /// A task that switched away at a `co/resume`, `co/try-resume` or `co/yield` is parked. Its frames from `base` up stay on its segment and are not in `chain`. `park_fp` is the frame that resumes, `park_pc` is the instruction where it resumes, and `park_base` is the register of the pending request or call in that frame. `park_base` is 0 for a task that is not parked. For `co/try-resume` it also has the flag `coroutine::TRIED` set.
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
        idle: Value,
        values: Value,
        segment: Member<Segment>,
        base: u32,
        state: u32,
        park_fp: u32,
        park_pc: u32,
        park_base: u32,
    }
    /// A runtime module instance. Its items are the top-level variable slots, which the slot instructions access. A slot holds `UNDEFINED` until its variable is defined. `names` is an immutable vector of the variable names, used in diagnostic messages. `hosts` is the host function table that [`Op::CallHost`] indexes. `interface` is an opaque value defined by the compiler. It describes the module's exports to importing modules.
    pub struct Module {
        name: Value,
        names: Value,
        hosts: Frozen<std::boxed::Box<[&'static crate::module::HostDef]>>,
        interface: Frozen<std::boxed::Box<dyn std::any::Any>>,
    } items Value
    /// A procedure accepting keyword arguments (see [`crate::keyword`]): wraps a `core` procedure and an optional `plain` procedure, accompanied by sorted lists of accepted `keywords` and `required` keywords.
    pub struct KeywordProcedure { plain: Value, core: Value, keywords: Value, required: Value }
    /// Descriptor for a record structure type (see [`crate::structs`]):
    ///
    /// - `name`: The structure type name (symbol).
    /// - `names`: An immutable vector of field name symbols, ordered supertype fields first.
    /// - `field_flags`: An immutable bytevector containing per-field [`FieldFlags`](crate::structs::FieldFlags) bits.
    /// - `fields`: Total number of fields across this type and its ancestors.
    /// - `flags`: Encoded [`TypeFlags`](crate::structs::TypeFlags) bitfield.
    /// - Trailing items store the ancestor supertypes, ordered outermost first.
    pub struct StructType { name: Value, names: Value, field_flags: Value, fields: u32, flags: u32 } items Value
    /// An instance of a record structure type: `kind` references its defining [`StructType`] descriptor, and trailing items store its field values.
    pub struct Struct { kind: Member<StructType> } items Value
    /// A register-spill buffer allocated by `NewSpill` for execution frames that require more local variable storage than the fixed register window provides, accessed via `LoadSpill` and `StoreSpill`.
    pub struct Spill {} items Value
}
