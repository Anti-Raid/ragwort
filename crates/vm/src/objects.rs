//! Garbage-collected object types used by the virtual machine. Type identifiers extend the base types in `ragwort-types`.

use ragwort_types::gc::{Segment, objects};

use crate::{Capture, Op};

#[cfg(test)]
#[path = "tests/objects.rs"]
mod tests;

objects! {
    pub kind Vm;

    /// Compiled procedure bytecode: contains the instruction array ([`Op`]), the constant pool table shared across co-compiled code, capture descriptors mapping upvalues for instantiated closures, encoded parameter arity (following Chez Scheme conventions), and an optional reference to the enclosing [`Module`].
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
    }
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
    /// `attachments` contains continuation marks restored upon resumption so that marks created above them disappear upon return. When `one_shot` is true (indicating no escaping continuation retains the record), the frames are resumed in place rather than copied to the heap—either directly on the stack segment if adjacent to active frames, or by transferring execution back onto the segment if `owns` is true (as when unwinding a stack overflow).
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
    /// An exception handler record installed by `guard` or `co/try-resume` in continuation marks. When an unhandled exception reaches this guard, execution unwinds to its installation site and invokes `handler` with the raised value (or, if `handler` is `#f`, returns `#f` and the value), restoring the dynamic `winders` in place when the guard was established. Stored in a register beneath the protected thunk's frame or within an outer [`Native`] continuation record.
    pub struct Guard { handler: Value, winders: Value, traced: bool }
    /// A continuation boundary record representing an internal VM control point on the stack chain. When overlying frames return, `kind` specifies the next VM action using operands `a` and `b`. `attachments` and `next` function like those in [`Frames`]. Immutable once constructed, allowing a continuation to resume from it repeatedly.
    pub struct Native { kind: u32, a: Value, b: Value, attachments: Value, next: Value }
    /// A coroutine task representing an arena-allocated execution state managed by a [`crate::Machine`]: preserves the result accumulator (`acc`) between run steps, the continuation record chain (`chain`), continuation marks (`attachments` as an association list of `(key . value)` pairs), active dynamic [`Winder`]s, and enclosing delimited prompts (`prompts`). `spare` and `spare_base` retain a cached stack segment reused during stack overflows.
    ///
    /// `body` contains the initial entry procedure before execution begins. `resumer` points to the task that resumed this one, while `resumed` points to any task currently resumed by it. While suspended, active stack frames reside on `segment` starting at `base` (or are preserved entirely within `chain`). `state` tracks whether the coroutine is pending, running, finished, or failed.
    ///
    /// The machine's primary root task also tracks `idle` (the most recently suspended coroutine whose frames remain resident on their segment until another task suspends) and pre-allocated singleton sentinel values in `none`.
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
        none: Value,
        segment: Member<Segment>,
        base: u32,
        state: u32,
    }
    /// A runtime module instance: holds top-level variable slots (initialized to `UNDEFINED` until defined) accessed by slot instructions, an immutable vector of variable `names` for diagnostic messages, a host function table indexed by [`Op::CallHost`], and an opaque compiler-defined `interface` describing exports for importing modules.
    pub struct Module {
        name: Value,
        names: Value,
        hosts: Frozen<std::boxed::Box<[&'static crate::module::HostDef]>>,
        interface: Frozen<std::boxed::Box<dyn std::any::Any>>,
    } items Value
    /// A host reference wrapper passed to host procedures: contains arbitrary host `data` allocated outside the arena (dropped upon GC finalization) and a `held` garbage-collected value traced by the GC to preserve associated arena objects.
    pub struct ExternalRef { held: Value, data: Frozen<std::boxed::Box<dyn std::any::Any>> }
    /// Represents multiple return values produced by `(values ...)` when returning zero or multiple (other than exactly one) values, unpacked by values intrinsics.
    pub struct MultiValue {} items Value
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
