//! Defines the virtual machine instruction set. Register operands are `u8` indices within the active frame window; jump offsets are relative to the instruction immediately following the jump.

use ragwort_types::{Error, Wire, named};
use ragwort_types::gc::{Frame, Gc, Mutation, OutOfMemory, Slots, Value, WINDOW};
use ragwort_types::constant::Constants;
use ragwort_types::num::NumError;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::StrError;
use ragwort_types::table::{Table, TableError};
use ragwort_types::vector::VectorError;

use crate::frame::CLOSURE;
use crate::objects::{self, BytecodeFields, ClosureFields, HINT_KEY, HINT_SLOTS, HintsFields, ModuleFields, SpillFields, Task};
use crate::{Intrinsic, Request, structs};

#[cfg(test)]
#[path = "tests/op.rs"]
mod tests;

named! {
    /// A virtual machine instruction. Each variant is packed into 8 bytes, comprising an opcode tag, register operands, and an optional 32-bit immediate index or jump offset.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
    pub enum Op {
        /// Copies the value from register `src` into register `dst`.
        Move { dst: u8, src: u8 } = "move",
        /// Performs a parallel copy of registers `(src1, src2)` into `(dst1, dst2)`.
        Move2 { dst1: u8, src1: u8, dst2: u8, src2: u8 } = "move2",
        /// Loads the constant value at index `index` from the module constant pool into register `dst`.
        LoadConst { dst: u8, index: u32 } = "load-const",
        /// Unconditionally jumps by `offset` instructions relative to the next instruction.
        Jump { offset: i32 } = "jump",
        /// Branches by `offset` instructions if register `test` contains a false value (see `Value::is_false`).
        JumpIfFalse { test: u8, offset: i32 } = "jump-if-false",
        /// Executes unary `intrinsic` on operand `a`, branching by `offset` if the boolean truthiness of the result matches `branch_if`.
        BranchIntrinsic1 { a: u8, intrinsic: Intrinsic, branch_if: bool, offset: i16 } = "branch-intrinsic1",
        /// Executes binary `intrinsic` on operands `(a, b)`, branching by `offset` if the boolean truthiness of the result matches `branch_if`.
        BranchIntrinsic2 { a: u8, b: u8, intrinsic: Intrinsic, branch_if: bool, offset: i16 } = "branch-intrinsic2",
        /// Invokes the procedure in register `base` with `args` arguments located in subsequent registers. The callee's frame begins at `base` and overlaps the caller's frame, placing arguments directly in the callee's argument registers without copying. Any caller-saved state must reside below `base`, which must be located beyond the caller's link slot.
        Call { base: u8, args: u8 } = "call",
        /// Performs a tail call to the procedure in register `base` with `args` arguments, shifting arguments down into the current frame window. The existing return link is preserved so the callee returns directly to the current caller.
        TailCall { base: u8, args: u8 } = "tail-call",
        /// Calls the procedure in register `base` with the values the last call returned, which are in the accumulator. One value becomes the only argument, in register `base + 1`. Emitted after the call to the producer of a `call-with-values`.
        CallReceived { base: u8 } = "call-received",
        /// Tail-call variant of `CallReceived`: the procedure returns directly to the current caller.
        TailCallReceived { base: u8 } = "tail-call-received",
        /// Copies register `src` into the accumulator and returns control to the caller.
        Return { src: u8 } = "return",
        /// Loads the return value currently in the accumulator into register `dst`. Fails with [`Fault::ValueCount`] unless the accumulator holds exactly one value.
        LoadAcc { dst: u8 } = "load-acc",
        /// Loads the values in the accumulator into register `dst` as a list, however many there are. Emitted after the call to the producer of a `collect`.
        LoadValues { dst: u8 } = "load-values",
        /// Returns to the caller and leaves the accumulator unchanged. The caller receives the values that the last call or operation returned, whatever their number.
        ReturnReceived = "return-received",
        /// Returns the values in `count` registers starting at `src` to the caller. This is `(values x ...)` in tail position. Any number of values other than one is returned as the marker [`Value::VALUES`] in the accumulator, with a list of the values. Only a receiving call or another return accepts the marker.
        ReturnValues { src: u8, count: u8 } = "return-values",
        /// Returns values as `ReturnValues` does, with the last operand spread as in `apply`. The values are those in the first `args - 1` registers starting at `base`, followed by the elements of the list in the last of the `args` registers.
        ReturnSpread { base: u8, args: u8 } = "return-spread",
        /// Loads upvalue `index` of the current closure into register `dst`. Upvalues are populated upon closure creation; mutable variables are captured within indirection boxes accessed via box intrinsics.
        LoadUpvalue { dst: u8, index: u32 } = "load-upvalue",
        /// Creates `count` closures from the bytecode objects at constant pool indices `code..code + count`, and stores them in registers `dst..dst + count`. Then initializes each closure's upvalues according to its capture list. All closures are allocated before any upvalue is initialized. So mutually recursive procedures (such as from `letrec`) can capture each other through the registers.
        NewClosure { dst: u8, count: u8, code: u32 } = "new-closure",
        /// Invokes `intrinsic` on `args` operand registers starting at `base`, storing the result in the accumulator. Emitted by the compiler for non-rebound primitive procedures, enabling optimized execution paths such as in-place fixnum arithmetic.
        CallIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "call-intrinsic",
        /// Executes unary `intrinsic` on register operand `a` and writes the result into register `dst`.
        CallIntrinsic1 { dst: u8, a: u8, intrinsic: Intrinsic } = "call-intrinsic1",
        /// Executes binary `intrinsic` on register operands `(a, b)` and writes the result into register `dst`.
        CallIntrinsic2 { dst: u8, a: u8, b: u8, intrinsic: Intrinsic } = "call-intrinsic2",
        /// Adds the immediate constant `imm` to register `a` and writes the result into register `dst`. Performs in-place fixnum addition if `a` is a fixnum and the sum does not overflow, falling back to generic addition (`+`) otherwise. Emitted for additions or subtractions with small integer literals without allocating a constant register.
        AddImm { dst: u8, a: u8, imm: i16 } = "add-imm",
        /// Reads field `k` from the structure in register `a` and stores it in `dst` (corresponding to `(struct-field a k)`). Emitted when static analysis confirms `a` is a struct containing field index `k`, avoiding a register for the field offset.
        StructField { dst: u8, a: u8, k: u16 } = "struct-field",
        /// Reads field `k` from the structure in register `a` and stores it in `dst`, as `(struct-ref a type k)` does. First verifies that `a` is an instance of the struct type at constant pool index `kind`. Neither the type descriptor nor the field index occupies a register.
        StructRef { dst: u8, a: u8, k: u8, kind: u32 } = "struct-ref",
        /// Executes ternary `intrinsic` on register operands `(a, b, c)` and writes the result into register `dst`.
        CallIntrinsic3 { dst: u8, a: u8, b: u8, c: u8, intrinsic: Intrinsic } = "call-intrinsic3",
        /// `(table-ref table key #f)` for a constant key of any kind. Writes the value of the key in the table in register `table` into `dst`. If the table has no such key, writes `#f`.
        ///
        /// A table with a remembered shape is read at the remembered position, and no key is compared. That holds for every kind of key, because the shape was remembered when this key was found in a table of that shape. A table without a shape is read at the remembered position only if the key there is the same value word as the constant. A key that is an object, such as a long string, can be an equal object with another word. The instruction then leaves the loop, and the key is compared by value there.
        ///
        /// Hint number `hint` of the code holds the key and the places where the key was last found. Those places are tried first. No register holds the key. See [`crate::objects::Hints`].
        TableRefHinted { dst: u8, table: u8, hint: u16 } = "table-ref-hinted",
        /// `(table-ref table key default)` for a key of the kind that `TableRefHinted` takes. Works like `TableRefHinted`. If the table has no such key, writes the value of register `default`.
        TableRefOrHinted { dst: u8, table: u8, default: u8, hint: u16 } = "table-ref-or-hinted",
        /// `(table-set! table key value)` for a key of the kind that `TableRefHinted` takes. Sets the value of the key in the table in register `table`, and writes `#<void>` into `dst`. The hint is used as in `TableRefHinted`.
        TableSetHinted { dst: u8, table: u8, value: u8, hint: u16 } = "table-set-hinted",
        /// Executes `intrinsic` on the argument registers and immediately returns the result to the caller. Built-in procedures referenced as first-class values compile to a closure wrapping this single instruction.
        TailCallIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "tail-call-intrinsic",
        /// Dispatches runtime control operation `request` to the execution loop with `args` argument registers starting at `base`. For requests that invoke procedures (such as `call/cc`), execution resumes after this instruction when the procedure returns. So `base` must be past the current frame's link slot.
        CallRequest { base: u8, args: u8, request: Request } = "call-request",
        /// Tail-call variant of `CallRequest`. Any procedure that the request invokes replaces the current frame and returns directly to the current frame's caller. An example is `(call/cc f)` in tail position.
        TailCallRequest { base: u8, args: u8, request: Request } = "tail-call-request",
        /// Executes `intrinsic` with its arguments spread as in `apply`. The registers before the last are passed as positional arguments. The last register holds a list of the remaining arguments.
        ApplyIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "apply-intrinsic",
        /// Executes runtime control operation `request` with `apply`-style argument spreading, where the final register among the `args` contains a list of trailing arguments.
        ApplyRequest { base: u8, args: u8, request: Request } = "apply-request",
        /// Tail-call variant of `ApplyRequest`, reusing the current frame so any invoked procedure returns directly to this frame's caller.
        TailApplyRequest { base: u8, args: u8, request: Request } = "tail-apply-request",
        /// Allocates a new [`crate::objects::Spill`] buffer initialized with `count` void slots and stores it in register `dst`. Emitted at procedure entry for frames whose local variables exceed available registers.
        NewSpill { dst: u8, count: u32 } = "new-spill",
        /// Loads the value at index `slot` from the spill buffer in register `spill` into register `dst`.
        LoadSpill { dst: u8, spill: u8, slot: u32 } = "load-spill",
        /// Stores the value in register `src` into index `slot` of the spill buffer in register `spill`.
        StoreSpill { src: u8, spill: u8, slot: u32 } = "store-spill",
        /// Loads top-level variable index `slot` from the enclosing [`crate::objects::Module`] into register `dst`, used when the compiler has proven the variable is already defined.
        LoadSlot { dst: u8, slot: u32 } = "load-slot",
        /// Loads top-level variable index `slot` from the enclosing [`crate::objects::Module`] into register `dst`, raising [`Fault::Unbound`] if the variable is still `UNDEFINED`.
        LoadSlotChecked { dst: u8, slot: u32 } = "load-slot-checked",
        /// Stores register `src` into top-level variable index `slot` of the enclosing [`crate::objects::Module`], used for initial variable definitions.
        StoreSlot { src: u8, slot: u32 } = "store-slot",
        /// Stores register `src` into top-level variable index `slot` of the enclosing [`crate::objects::Module`] (as in `set!`), raising [`Fault::Unbound`] if the variable is currently `UNDEFINED`.
        StoreSlotChecked { src: u8, slot: u32 } = "store-slot-checked",
        /// Invokes host function index `host` from the enclosing module's host table on `args` argument registers starting at `base`. Arguments are laid out like a procedure call, allowing a returned [`crate::Reply::Call`] to invoke a procedure in place.
        CallHost { base: u8, args: u8, host: u32 } = "call-host",
        TailCallHost { base: u8, args: u8, host: u32 } = "tail-call-host",
    }
}

const _: () = assert!(size_of::<Op>() == 8);

/// Specifies the source location from which a captured upvalue is loaded when creating a closure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub enum Capture {
    /// Captures the value from register `r` of the enclosing frame, read after all closures in a `NewClosure` instruction have been allocated.
    Register(u8),
    /// Captures upvalue index `u` from the enclosing closure.
    Upvalue(u32),
    /// Captures index `slot` from the spill buffer residing in register `spill` of the enclosing frame.
    Spill { spill: u8, slot: u32 },
}

/// Execution context provided to instruction execution, encapsulating VM registers, stack frame, constant pool, upvalues, and fuel.
pub struct Context<'s, 'gc> {
    pub mc: &'s Mutation<'gc>,
    /// The currently executing coroutine [`Task`], accessed by dynamic-wind and continuation intrinsics.
    pub task: Gc<'gc, Task>,
    pub frame: Frame<'s, 'gc>,
    /// The active module's constant pool table, indexed by `LoadConst` and struct instructions.
    pub constants: Constants<'gc>,
    /// The running code. A hinted table instruction reads its hint from it. See [`objects::Hints`].
    pub code: Gc<'gc, objects::Bytecode>,
    /// Captured upvalues belonging to the currently executing closure.
    pub upvalues: Slots<'gc>,
    pub acc: Value<'gc>,
    /// The list of values the last call returned, when `acc` is [`Value::VALUES`].
    pub values: Value<'gc>,
    pub fuel: Fuel,
}

impl<'gc> Context<'_, 'gc> {
    /// Returns the hint slots of the running code and the index of the first slot of hint `hint`. Returns `None` if the code has no such hint.
    #[inline(always)]
    pub(crate) fn hint(&self, hint: u16) -> Option<(Slots<'gc>, usize)> {
        let hints = self.code.hints(self.mc)?.items(self.mc);
        let slot = HINT_SLOTS * usize::from(hint);
        if slot + HINT_SLOTS <= hints.len() {
            Some((hints, slot))
        } else {
            None
        }
    }

    /// Reads the key of hint `hint` in the table in register `table`, at the first place that the hint remembers. That place has the key whenever the instruction reads tables of one shape, or one table, again and again.
    ///
    /// Returns `None` if the place does not have the key. It also returns `None` if the register holds no table, or if the code has no such hint. The instruction then leaves the loop, and `Run::table_ref` searches the table or reports the fault.
    #[inline(always)]
    fn read_hinted(&self, table: u8, hint: u16) -> Option<Value<'gc>> {
        let (hints, slot) = self.hint(hint)?;
        let table = Table::of(self.frame.get(table))?;
        table.get_hinted(self.mc, hints.get(slot + HINT_KEY), remembered(hints.get(slot + 1)), hints.get(slot))
    }

    /// Sets the value of the key of hint `hint` in the table in register `table`, at the first place that the hint remembers. Returns whether the value was set. If it was not, the instruction leaves the loop, as for [`Context::read_hinted`].
    #[inline(always)]
    fn write_hinted(&self, table: u8, value: u8, hint: u16) -> bool {
        let Some((hints, slot)) = self.hint(hint) else { return false };
        let Some(table) = Table::of(self.frame.get(table)) else { return false };
        table.set_hinted(self.mc, hints.get(slot + HINT_KEY), remembered(hints.get(slot + 1)), hints.get(slot), self.frame.get(value))
    }

    /// Loads the values in the accumulator into register `dst` as a list. Kept out of line, like [`Context::set_values`], so that the instruction loop stays small.
    #[inline(never)]
    fn load_values(&mut self, dst: u8) -> Result<(), Fault> {
        let mc = self.mc;
        let list = if self.acc == Value::VALUES {
            std::mem::replace(&mut self.values, Value::NULL)
        } else {
            Pairs::new(mc).cons(self.acc, Value::NULL)?.value(mc)
        };
        self.frame.set(dst, list);
        if mc.step_due() {
            self.fuel.pause();
        }
        Ok(())
    }

    /// Stores the values of `count` registers starting at `first`, followed by the elements of the proper list `rest`, in the accumulator. Exactly one value is stored as that value. Any other number of values is stored as the marker and a list.
    #[inline(never)]
    fn set_values(&mut self, first: u8, count: u8, rest: Value<'gc>) -> Result<(), Fault> {
        let (mc, frame) = (self.mc, self.frame);
        if count == 1 && rest == Value::NULL {
            self.acc = frame.get(first);
            return Ok(());
        }
        let pairs = Pairs::new(mc);
        let mut list = rest;
        for i in (0..count).rev() {
            list = pairs.cons(frame.get(first + i), list)?.value(mc);
        }
        match Pair::of(list) {
            Some(cell) if cell.tail(mc) == Value::NULL => self.acc = cell.head(mc),
            _ => (self.acc, self.values) = (Value::VALUES, list),
        }
        if mc.step_due() {
            self.fuel.pause();
        }
        Ok(())
    }
}

/// Tracks remaining execution fuel for cooperative multitasking and bounded execution: calls and branches consume one unit from `run`, pausing execution when exhausted. Computationally heavy intrinsics deduct from `run` and then `rest`. Pausing execution (e.g. for GC step cycles) transfers remaining `run` fuel to `rest`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fuel {
    pub run: u64,
    pub rest: u64,
}

impl Fuel {
    /// Returns the total remaining execution fuel (`run + rest`), saturating on overflow.
    pub fn left(self) -> u64 {
        self.run.saturating_add(self.rest)
    }

    /// Forces the virtual machine to pause at the next call or branch by moving all active `run` fuel into `rest`.
    pub fn pause(&mut self) {
        (self.run, self.rest) = (0, self.left());
    }

    /// Deducts `units` of fuel, consuming from `run` first and then `rest`. Returns [`Fault::OutOfFuel`] if the total remaining fuel is insufficient.
    pub fn spend(&mut self, units: u64) -> Result<(), Fault> {
        let past = units.saturating_sub(self.run);
        if past > self.rest {
            return Err(Fault::OutOfFuel);
        }
        (self.run, self.rest) = (self.run - (units - past), self.rest - past);
        Ok(())
    }
}

/// Specifies the control-flow action to be taken by the VM dispatch loop after executing an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Control {
    Next,
    /// Relative branch by `offset` instructions from the instruction following this one.
    Jump(i32),
    /// Transfers control to a procedure call starting at register `base` with `args` arguments.
    Call { base: u8, args: u8 },
    TailCall { base: u8, args: u8 },
    /// Calls the procedure in register `base` with the values in the accumulator, as a tail call if `tail` is set.
    CallReceived { base: u8, tail: bool },
    /// Dispatches a control operation `request` with `args` argument registers starting at `base`, unpacking trailing list elements if `spread` is true.
    CallRequest { base: u8, args: u8, request: Request, spread: bool },
    TailCallRequest { base: u8, args: u8, request: Request, spread: bool },
    /// Invokes host function index `host` from the active module with `args` registers starting at `base`.
    Host { base: u8, args: u8, host: u32, tail: bool },
    /// Returns from the current frame to the caller, passing the accumulator value.
    Return,
    /// Finishes a hinted table read whose first remembered place did not have the key. `default` is the register of the value for a missing key, or `None` if that value is `#f`. See [`Op::TableRefHinted`].
    TableRef { dst: u8, table: u8, default: Option<u8>, hint: u16 },
    /// Finishes a hinted table write whose first remembered place did not have the key. See [`Op::TableSetHinted`].
    TableSet { dst: u8, table: u8, value: u8, hint: u16 },
}

/// Represents virtual machine runtime faults and errors. Non-fatal faults are raised within the Scheme program as [`crate::objects::Condition`] objects and terminate execution only if unhandled.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub enum Fault {
    /// Indicates corrupt or invalid bytecode: an out-of-bounds constant or upvalue index, invalid register operand, or invalid arity passed to an intrinsic or request.
    Malformed,
    OutOfMemory,
    /// An intrinsic received an argument of an incompatible type (e.g. calling `car` on a non-pair value).
    WrongType,
    /// An index argument was negative or exceeded the valid bounds of the sequence.
    OutOfRange,
    /// Attempted mutation of an immutable object, such as a literal constant.
    Immutable,
    /// A procedure was called with an incorrect number of arguments.
    Arity,
    /// Attempted to invoke a value that is not a callable procedure.
    NotProcedure,
    /// An abort or continuation capture targeted a prompt tag with no matching active prompt on the continuation chain.
    NoPrompt,
    /// Attempted to reference or mutate an undefined top-level variable.
    Unbound,
    /// Attempted to resume or execute a virtual machine whose task has already terminated.
    Finished,
    /// The virtual machine exhausted its allocated execution fuel, terminating task execution.
    OutOfFuel,
    /// User-level exception raised via `error` or `make-error`.
    Error,
    /// Attempted to resume a coroutine that is not in a pending state (i.e. already running, dead, or failed).
    NotPending,
    /// Syntax error (as created by `make-syntax-error`), indicating malformed syntax such as a macro use unmatched by any `syntax-case` pattern.
    Syntax,
    /// Keyword argument error: an unsupported keyword was supplied or a required keyword parameter was omitted.
    Keyword,
    /// A place that takes exactly one value was given none or several, as in `(+ 1 (values 2 3))`.
    ValueCount,
    Num(NumError),
    Str(StrError),
}

impl Fault {
    /// String names corresponding to fault kind codes, matching Scheme's `error-object-kind`.
    pub const KINDS: [&str; 21] = [
        "malformed",
        "out-of-memory",
        "wrong-type",
        "out-of-range",
        "immutable",
        "arity",
        "not-procedure",
        "no-prompt",
        "unbound",
        "finished",
        "out-of-fuel",
        "error",
        "not-pending",
        "divide-by-zero",
        "no-exact-value",
        "not-integer",
        "too-long",
        "syntax",
        "keyword",
        "not-utf8",
        "value-count",
    ];

    /// A short description of each fault kind, indexed as [`Fault::KINDS`] is. An error report shows it after the name of the failed operation, as in `car: wrong type of argument: 5`.
    pub const MESSAGES: [&str; 21] = [
        "malformed bytecode",
        "out of memory",
        "wrong type of argument",
        "value out of range",
        "immutable object",
        "wrong number of arguments",
        "not a procedure",
        "no matching prompt",
        "undefined variable",
        "the program has finished",
        "out of fuel",
        "error",
        "coroutine is not suspended",
        "division by zero",
        "no exact value",
        "not an integer",
        "string too long",
        "bad syntax",
        "bad keyword argument",
        "invalid UTF-8",
        "wrong number of values",
    ];

    /// Returns the short description of this fault from [`Fault::MESSAGES`].
    pub fn message(self) -> &'static str {
        Self::MESSAGES[self.kind()]
    }

    /// Returns the integer index corresponding to this fault in [`Fault::KINDS`].
    pub fn kind(self) -> usize {
        match self {
            Fault::Malformed => 0,
            Fault::OutOfMemory => 1,
            Fault::WrongType => 2,
            Fault::OutOfRange | Fault::Str(StrError::OutOfRange) => 3,
            Fault::Immutable => 4,
            Fault::Arity => 5,
            Fault::NotProcedure => 6,
            Fault::NoPrompt => 7,
            Fault::Unbound => 8,
            Fault::Finished => 9,
            Fault::OutOfFuel => 10,
            Fault::Error => 11,
            Fault::NotPending => 12,
            Fault::Num(NumError::DivideByZero) => 13,
            Fault::Num(NumError::NoExactValue) => 14,
            Fault::Num(NumError::NotInteger) => 15,
            Fault::Str(StrError::TooLong) => 16,
            Fault::Syntax => 17,
            Fault::Keyword => 18,
            Fault::Str(StrError::NotUtf8) => 19,
            Fault::ValueCount => 20,
        }
    }

    /// Returns `true` if this fault is fatal. A fatal fault ends the run immediately and is not raised as a condition in the program. The fatal faults are corrupt bytecode, an exhausted heap, an already-finished task, and fuel exhaustion.
    pub fn is_fatal(self) -> bool {
        matches!(self, Fault::Malformed | Fault::OutOfMemory | Fault::Finished | Fault::OutOfFuel)
    }
}

impl From<OutOfMemory> for Fault {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<VectorError> for Fault {
    fn from(error: VectorError) -> Self {
        match error {
            VectorError::Immutable => Self::Immutable,
            // The host of an external vector rejected the value. The program sees a value of the wrong type.
            VectorError::Refused => Self::WrongType,
            VectorError::OutOfRange => Self::OutOfRange,
            VectorError::Arena(error) => error.into(),
        }
    }
}

impl From<TableError> for Fault {
    fn from(error: TableError) -> Self {
        match error {
            TableError::Immutable => Self::Immutable,
            // The host of an external table rejected the key or the value. The program sees a value of the wrong type.
            TableError::Refused => Self::WrongType,
            TableError::Arena(error) => error.into(),
        }
    }
}

impl From<Error> for Fault {
    fn from(error: Error) -> Self {
        match error {
            Error::OutOfMemory => Self::OutOfMemory,
            Error::Num(error) => Self::Num(error),
            Error::Str(error) => Self::Str(error),
        }
    }
}

impl Op {
    /// Executes the instruction against context `cx`, returning a [`Control`] directive indicating the next action for the dispatch loop.
    #[inline(always)]
    pub fn step<'gc>(self, cx: &mut Context<'_, 'gc>) -> Result<Control, Fault> {
        let (mc, frame) = (cx.mc, cx.frame);
        match self {
            Op::Move { dst, src } => frame.set(dst, frame.get(src)),
            Op::Move2 { dst1, src1, dst2, src2 } => {
                let (v1, v2) = (frame.get(src1), frame.get(src2));
                frame.set(dst1, v1);
                frame.set(dst2, v2);
            }
            Op::LoadConst { dst, index } => frame.set(dst, cx.constants.get(mc, index).ok_or(Fault::Malformed)?),
            Op::Jump { offset } => return Ok(Control::Jump(offset)),
            Op::JumpIfFalse { test, offset } => {
                if frame.get(test).is_false() {
                    return Ok(Control::Jump(offset));
                }
            }
            Op::BranchIntrinsic1 { a: operand, intrinsic, branch_if, offset } => {
                if intrinsic.arity().is_some_and(|arity| arity != 1) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec1(cx, operand)?;
                if val.is_true() == branch_if {
                    return Ok(Control::Jump(i32::from(offset)));
                }
            }
            Op::BranchIntrinsic2 { a: left, b: right, intrinsic, branch_if, offset } => {
                // A comparison of two small integers is done here. Everything else goes to the intrinsic.
                let holds = match intrinsic.small_test(frame.get(left), frame.get(right)) {
                    Some(holds) => holds,
                    None => {
                        if intrinsic.arity().is_some_and(|arity| arity != 2) {
                            return Err(Fault::Malformed);
                        }
                        intrinsic.exec2(cx, left, right)?.is_true()
                    }
                };
                if holds == branch_if {
                    return Ok(Control::Jump(i32::from(offset)));
                }
            }
            Op::Call { base, args } => return Ok(Control::Call { base, args }),
            Op::TailCall { base, args } => return Ok(Control::TailCall { base, args }),
            Op::CallReceived { base } => return Ok(Control::CallReceived { base, tail: false }),
            Op::TailCallReceived { base } => return Ok(Control::CallReceived { base, tail: true }),
            Op::Return { src } => {
                cx.acc = frame.get(src);
                return Ok(Control::Return);
            }
            Op::LoadAcc { dst } => {
                if cx.acc == Value::VALUES {
                    return Err(Fault::ValueCount);
                }
                frame.set(dst, cx.acc);
            }
            Op::LoadValues { dst } => cx.load_values(dst)?,
            Op::ReturnReceived => return Ok(Control::Return),
            Op::ReturnValues { src, count } => {
                if usize::from(src) + usize::from(count) > WINDOW {
                    return Err(Fault::Malformed);
                }
                cx.set_values(src, count, Value::NULL)?;
                return Ok(Control::Return);
            }
            Op::ReturnSpread { base, args } => {
                if args == 0 || usize::from(base) + usize::from(args) > WINDOW {
                    return Err(Fault::Malformed);
                }
                let rest = frame.get(base + args - 1);
                if !Pairs::new(mc).is_list(rest) {
                    return Err(Fault::WrongType);
                }
                cx.set_values(base, args - 1, rest)?;
                return Ok(Control::Return);
            }
            Op::LoadUpvalue { dst, index } => {
                let index = index as usize;
                if index >= cx.upvalues.len() {
                    return Err(Fault::Malformed);
                }
                frame.set(dst, cx.upvalues.get(index));
            }
            Op::NewClosure { dst, count, code } => {
                if usize::from(dst) + usize::from(count) > WINDOW {
                    return Err(Fault::Malformed);
                }
                for i in 0..count {
                    let index = code.checked_add(u32::from(i)).ok_or(Fault::Malformed)?;
                    let code = cx.constants.get(mc, index).and_then(|constant| constant.downcast::<objects::Bytecode>(mc)).ok_or(Fault::Malformed)?;
                    let captures = code.captures(mc).map_or(0, |slice| slice.len());
                    frame.set(dst + i, Value::object(mc, objects::Closure::new(mc, Some(code), captures, Value::VOID)?));
                }
                if mc.step_due() {
                    cx.fuel.pause();
                }
                for i in 0..count {
                    let closure = frame.get(dst + i).downcast::<objects::Closure>(mc).ok_or(Fault::Malformed)?;
                    let (code, upvalues) = (closure.code(mc).ok_or(Fault::Malformed)?, closure.items(mc));
                    for (j, capture) in code.captures(mc).map_or(&[][..], |slice| slice).iter().enumerate() {
                        let value = match *capture {
                            Capture::Register(register) => frame.get(register),
                            Capture::Upvalue(upvalue) => {
                                let upvalue = upvalue as usize;
                                if upvalue >= cx.upvalues.len() {
                                    return Err(Fault::Malformed);
                                }
                                cx.upvalues.get(upvalue)
                            }
                            Capture::Spill { spill, slot } => spilled(mc, frame, spill, slot)?.get(slot as usize),
                        };
                        upvalues.set(mc, j, value);
                    }
                }
            }
            Op::CallIntrinsic { base, args, intrinsic } | Op::TailCallIntrinsic { base, args, intrinsic } => {
                if usize::from(base) + usize::from(args) > WINDOW {
                    return Err(Fault::Malformed);
                }
                // Arithmetic and comparison of two small integers is done here, as in `Op::CallIntrinsic2`. A procedure whose body is `(+ a b)` ends with this instruction.
                let small = if args == 2 {
                    intrinsic.small(frame.get(base), frame.get(base + 1))
                } else {
                    None
                };
                cx.acc = match small {
                    Some(value) => value,
                    None => {
                        if intrinsic.arity().is_some_and(|arity| arity != args) {
                            return Err(Fault::Malformed);
                        }
                        intrinsic.exec(cx, base, args)?
                    }
                };
                if matches!(self, Op::TailCallIntrinsic { .. }) {
                    return Ok(Control::Return);
                }
            }
            Op::CallIntrinsic1 { dst, a: operand, intrinsic } => {
                if intrinsic.arity().is_some_and(|arity| arity != 1) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec1(cx, operand)?;
                frame.set(dst, val);
            }
            Op::CallIntrinsic2 { dst, a: left, b: right, intrinsic } => {
                // Arithmetic and comparison of two small integers is done here. Everything else goes to the intrinsic.
                let val = match intrinsic.small(frame.get(left), frame.get(right)) {
                    Some(val) => val,
                    None => {
                        if intrinsic.arity().is_some_and(|arity| arity != 2) {
                            return Err(Fault::Malformed);
                        }
                        intrinsic.exec2(cx, left, right)?
                    }
                };
                frame.set(dst, val);
            }
            Op::AddImm { dst, a: operand, imm } => {
                let (left, right) = (frame.get(operand), Value::fixnum(i64::from(imm)).ok_or(Fault::Malformed)?);
                let sum = match left.fixnum_add(right) {
                    Some(sum) => sum,
                    None => Intrinsic::Add.run(mc, &[left, right], &mut cx.fuel)?,
                };
                frame.set(dst, sum);
            }
            Op::StructField { dst, a: instance, k: index } => frame.set(dst, structs::field(mc, frame.get(instance), usize::from(index))?),
            Op::StructRef { dst, a: instance, k: index, kind } => {
                let kind = cx.constants.get(mc, kind).ok_or(Fault::Malformed)?;
                frame.set(dst, structs::field_of(mc, frame.get(instance), kind, usize::from(index))?);
            }
            Op::CallIntrinsic3 { dst, a: first, b: second, c: third, intrinsic } => {
                if intrinsic.arity().is_some_and(|arity| arity != 3) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec3(cx, first, second, third)?;
                frame.set(dst, val);
            }
            // A hinted table instruction is finished here if the first place of its hint has the key. Otherwise it leaves the loop.
            Op::TableRefHinted { dst, table, hint } => match cx.read_hinted(table, hint) {
                Some(value) => frame.set(dst, value),
                None => return Ok(Control::TableRef { dst, table, default: None, hint }),
            },
            Op::TableRefOrHinted { dst, table, default, hint } => match cx.read_hinted(table, hint) {
                Some(value) => frame.set(dst, value),
                None => return Ok(Control::TableRef { dst, table, default: Some(default), hint }),
            },
            Op::TableSetHinted { dst, table, value, hint } => {
                if !cx.write_hinted(table, value, hint) {
                    return Ok(Control::TableSet { dst, table, value, hint });
                }
                frame.set(dst, Value::VOID);
            }
            Op::CallRequest { base, args, request } | Op::TailCallRequest { base, args, request } => {
                if usize::from(base) + usize::from(args) > WINDOW || !request.takes(usize::from(args)) {
                    return Err(Fault::Malformed);
                }
                return Ok(match self {
                    Op::CallRequest { .. } => Control::CallRequest { base, args, request, spread: false },
                    _ => Control::TailCallRequest { base, args, request, spread: false },
                });
            }
            Op::CallHost { base, args, host } | Op::TailCallHost { base, args, host } => {
                if usize::from(base) + usize::from(args.max(1)) > WINDOW {
                    return Err(Fault::Malformed);
                }
                return Ok(Control::Host { base, args, host, tail: matches!(self, Op::TailCallHost { .. }) });
            }
            Op::ApplyIntrinsic { base, args, intrinsic } => {
                if args == 0 || usize::from(base) + usize::from(args) > WINDOW {
                    return Err(Fault::Malformed);
                }
                let mut values: Vec<_> = (0..args - 1).map(|i| frame.get(base + i)).collect();
                values.extend(list(mc, frame.get(base + args - 1))?);
                cx.acc = intrinsic.run_in(mc, Some(cx.task), &values, &mut cx.fuel)?;
            }
            Op::ApplyRequest { base, args, request } | Op::TailApplyRequest { base, args, request } => {
                if args == 0 || usize::from(base) + usize::from(args) > WINDOW {
                    return Err(Fault::Malformed);
                }
                return Ok(match self {
                    Op::ApplyRequest { .. } => Control::CallRequest { base, args, request, spread: true },
                    _ => Control::TailCallRequest { base, args, request, spread: true },
                });
            }
            Op::NewSpill { dst, count } => {
                frame.set(dst, Value::object(mc, objects::Spill::new(mc, count as usize, Value::VOID)?));
                if mc.step_due() {
                    cx.fuel.pause();
                }
            }
            Op::LoadSpill { dst, spill, slot } => frame.set(dst, spilled(mc, frame, spill, slot)?.get(slot as usize)),
            Op::StoreSpill { src, spill, slot } => spilled(mc, frame, spill, slot)?.set(mc, slot as usize, frame.get(src)),
            Op::LoadSlot { dst, slot } => frame.set(dst, variables(mc, frame, slot)?.get(slot as usize)),
            Op::LoadSlotChecked { dst, slot } => {
                let value = variables(mc, frame, slot)?.get(slot as usize);
                if value == Value::UNDEFINED {
                    return Err(Fault::Unbound);
                }
                frame.set(dst, value);
            }
            Op::StoreSlot { src, slot } => variables(mc, frame, slot)?.set(mc, slot as usize, frame.get(src)),
            Op::StoreSlotChecked { src, slot } => {
                let variables = variables(mc, frame, slot)?;
                if variables.get(slot as usize) == Value::UNDEFINED {
                    return Err(Fault::Unbound);
                }
                variables.set(mc, slot as usize, frame.get(src));
            }
        }
        Ok(Control::Next)
    }
}

/// Retrieves the spill buffer slots from register `spill`, verifying that `slot` is within bounds.
#[inline]
fn spilled<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, spill: u8, slot: u32) -> Result<Slots<'gc>, Fault> {
    let slots = frame.get(spill).downcast::<objects::Spill>(mc).ok_or(Fault::Malformed)?.items(mc);
    if slot as usize >= slots.len() {
        return Err(Fault::Malformed);
    }
    Ok(slots)
}

/// Retrieves the variable slots of the module enclosing the bytecode executing in `frame`, verifying that `slot` is within bounds.
#[inline]
fn variables<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, slot: u32) -> Result<Slots<'gc>, Fault> {
    let module = frame.get(CLOSURE).downcast::<objects::Closure>(mc).and_then(|closure| closure.code(mc)).and_then(|code| code.module(mc));
    module.map(|module| module.items(mc)).filter(|slots| (slot as usize) < slots.len()).ok_or(Fault::Malformed)
}

/// Unpacks the elements of a proper Scheme list into a `Vec<Value>`, returning [`Fault::WrongType`] if the list is improper or non-nil terminated.
fn list<'gc>(mc: &Mutation<'gc>, mut list: Value<'gc>) -> Result<Vec<Value<'gc>>, Fault> {
    let mut items = Vec::new();
    while let Some(pair) = Pair::of(list) {
        items.push(pair.head(mc));
        list = pair.tail(mc);
    }
    if list != Value::NULL {
        return Err(Fault::WrongType);
    }
    Ok(items)
}

/// Returns the position that a hint slot holds. A slot that is not used yet holds no fixnum. It reads as a position that no table has, so an unused place never has the key.
#[inline(always)]
pub(crate) fn remembered(slot: Value<'_>) -> usize {
    slot.as_fixnum().map_or(usize::MAX, |position| position as usize)
}
