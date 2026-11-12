//! Defines the virtual machine instruction set. Register operands are `u8` indices within the active frame window; jump offsets are relative to the instruction immediately following the jump.

use ragwort_types::{Error, Wire, named};
use ragwort_types::gc::{Frame, Gc, Mutation, OutOfMemory, Slots, Value, WINDOW};
use ragwort_types::constant::Constants;
use ragwort_types::num::NumError;
use ragwort_types::pair::Pair;
use ragwort_types::string::StrError;

use crate::frame::CLOSURE;
use crate::objects::{self, BytecodeFields, ClosureFields, ModuleFields, SpillFields, Task};
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
        /// Branches by `offset` instructions if register `test` contains `#f` (`Value::FALSE`).
        JumpIfFalse { test: u8, offset: i32 } = "jump-if-false",
        /// Executes unary `intrinsic` on operand `a`, branching by `offset` if the boolean truthiness of the result matches `branch_if`.
        BranchIntrinsic1 { a: u8, intrinsic: Intrinsic, branch_if: bool, offset: i16 } = "branch-intrinsic1",
        /// Executes binary `intrinsic` on operands `(a, b)`, branching by `offset` if the boolean truthiness of the result matches `branch_if`.
        BranchIntrinsic2 { a: u8, b: u8, intrinsic: Intrinsic, branch_if: bool, offset: i16 } = "branch-intrinsic2",
        /// Invokes the procedure in register `base` with `args` arguments located in subsequent registers. The callee's frame begins at `base` and overlaps the caller's frame, placing arguments directly in the callee's argument registers without copying. Any caller-saved state must reside below `base`, which must be located beyond the caller's link slot.
        Call { base: u8, args: u8 } = "call",
        /// Performs a tail call to the procedure in register `base` with `args` arguments, shifting arguments down into the current frame window. The existing return link is preserved so the callee returns directly to the current caller.
        TailCall { base: u8, args: u8 } = "tail-call",
        /// Copies register `src` into the accumulator and returns control to the caller.
        Return { src: u8 } = "return",
        /// Loads the return value currently in the accumulator into register `dst`.
        LoadAcc { dst: u8 } = "load-acc",
        /// Loads upvalue `index` of the current closure into register `dst`. Upvalues are populated upon closure creation; mutable variables are captured within indirection boxes accessed via box intrinsics.
        LoadUpvalue { dst: u8, index: u32 } = "load-upvalue",
        /// Instantiates `count` closures from bytecode objects in constant pool indices `code..code + count` into registers `dst..dst + count`, then initializes each closure's upvalues according to its capture list. All closures are allocated before initializing upvalues, allowing mutually recursive procedures (such as from `letrec`) to capture each other via register references.
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
        /// Reads field `k` from the structure in register `a` and stores it in `dst`, verifying that `a` is an instance of the struct type stored in constant pool index `kind` (corresponding to `(struct-ref a type k)`). Neither the type descriptor nor field index occupies a register.
        StructRef { dst: u8, a: u8, k: u8, kind: u32 } = "struct-ref",
        /// Executes ternary `intrinsic` on register operands `(a, b, c)` and writes the result into register `dst`.
        CallIntrinsic3 { dst: u8, a: u8, b: u8, c: u8, intrinsic: Intrinsic } = "call-intrinsic3",
        /// Executes `intrinsic` on the argument registers and immediately returns the result to the caller. Built-in procedures referenced as first-class values compile to a closure wrapping this single instruction.
        TailCallIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "tail-call-intrinsic",
        /// Dispatches runtime control operation `request` to the execution loop with `args` argument registers starting at `base`. For requests that invoke procedures (such as `call/cc`), execution resumes at this instruction upon return; `base` must therefore be positioned past the current frame's link slot.
        CallRequest { base: u8, args: u8, request: Request } = "call-request",
        /// Tail-call variant of `CallRequest`: any procedure invoked by the request replaces the current frame and returns directly to the caller of the current frame (e.g. for `(call/cc f)` in tail position).
        TailCallRequest { base: u8, args: u8, request: Request } = "tail-call-request",
        /// Executes `intrinsic` with variadic arguments like `apply`: preceding argument registers are passed positionally, and the final argument register provides a list containing the remaining arguments.
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
    /// Captured upvalues belonging to the currently executing closure.
    pub upvalues: Slots<'gc>,
    pub acc: Value<'gc>,
    pub fuel: Fuel,
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
    /// Dispatches a control operation `request` with `args` argument registers starting at `base`, unpacking trailing list elements if `spread` is true.
    CallRequest { base: u8, args: u8, request: Request, spread: bool },
    TailCallRequest { base: u8, args: u8, request: Request, spread: bool },
    /// Invokes host function index `host` from the active module with `args` registers starting at `base`.
    Host { base: u8, args: u8, host: u32, tail: bool },
    /// Returns from the current frame to the caller, passing the accumulator value.
    Return,
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
    /// Attempted to resume a coroutine that is not in a pending state (i.e. already running, finished, or failed).
    NotPending,
    /// Syntax error (as created by `make-syntax-error`), indicating malformed syntax such as a macro use unmatched by any `syntax-case` pattern.
    Syntax,
    /// Keyword argument error: an unsupported keyword was supplied or a required keyword parameter was omitted.
    Keyword,
    Num(NumError),
    Str(StrError),
}

impl Fault {
    /// String names corresponding to fault kind codes, matching Scheme's `error-object-kind`.
    pub const KINDS: [&str; 20] = [
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
    ];

    /// Returns the integer index corresponding to this fault in [`Fault::KINDS`].
    pub fn kind(self) -> usize {
        match self {
            Fault::Malformed | Fault::Str(StrError::NotNarrowest) => 0,
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
        }
    }

    /// Returns `true` if this fault is fatal (terminating the run immediately without raising an in-program condition), caused by corrupt bytecode, an exhausted heap, an already-finished task, or fuel exhaustion.
    pub fn is_fatal(self) -> bool {
        matches!(self, Fault::Malformed | Fault::OutOfMemory | Fault::Finished | Fault::OutOfFuel)
    }
}

impl From<OutOfMemory> for Fault {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<Error> for Fault {
    fn from(e: Error) -> Self {
        match e {
            Error::OutOfMemory => Self::OutOfMemory,
            Error::Num(e) => Self::Num(e),
            Error::Str(e) => Self::Str(e),
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
                if frame.get(test) == Value::FALSE {
                    return Ok(Control::Jump(offset));
                }
            }
            Op::BranchIntrinsic1 { a, intrinsic, branch_if, offset } => {
                if intrinsic.arity().is_some_and(|n| n != 1) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec1(cx, a)?;
                if (val != Value::FALSE) == branch_if {
                    return Ok(Control::Jump(i32::from(offset)));
                }
            }
            Op::BranchIntrinsic2 { a, b, intrinsic, branch_if, offset } => {
                if intrinsic.arity().is_some_and(|n| n != 2) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec2(cx, a, b)?;
                if (val != Value::FALSE) == branch_if {
                    return Ok(Control::Jump(i32::from(offset)));
                }
            }
            Op::Call { base, args } => return Ok(Control::Call { base, args }),
            Op::TailCall { base, args } => return Ok(Control::TailCall { base, args }),
            Op::Return { src } => {
                cx.acc = frame.get(src);
                return Ok(Control::Return);
            }
            Op::LoadAcc { dst } => frame.set(dst, cx.acc),
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
                    let code = cx.constants.get(mc, index).and_then(|c| c.downcast::<objects::Bytecode>(mc)).ok_or(Fault::Malformed)?;
                    let captures = code.captures(mc).map_or(0, |c| c.len());
                    frame.set(dst + i, Value::object(mc, objects::Closure::new(mc, Some(code), captures, Value::VOID)?));
                }
                if mc.step_due() {
                    cx.fuel.pause();
                }
                for i in 0..count {
                    let closure = frame.get(dst + i).downcast::<objects::Closure>(mc).ok_or(Fault::Malformed)?;
                    let (code, upvalues) = (closure.code(mc).ok_or(Fault::Malformed)?, closure.items(mc));
                    for (j, capture) in code.captures(mc).map_or(&[][..], |c| c).iter().enumerate() {
                        let value = match *capture {
                            Capture::Register(r) => frame.get(r),
                            Capture::Upvalue(u) => {
                                let u = u as usize;
                                if u >= cx.upvalues.len() {
                                    return Err(Fault::Malformed);
                                }
                                cx.upvalues.get(u)
                            }
                            Capture::Spill { spill, slot } => spilled(mc, frame, spill, slot)?.get(slot as usize),
                        };
                        upvalues.set(mc, j, value);
                    }
                }
            }
            Op::CallIntrinsic { base, args, intrinsic } | Op::TailCallIntrinsic { base, args, intrinsic } => {
                if usize::from(base) + usize::from(args) > WINDOW || intrinsic.arity().is_some_and(|n| n != args) {
                    return Err(Fault::Malformed);
                }
                cx.acc = intrinsic.exec(cx, base, args)?;
                if matches!(self, Op::TailCallIntrinsic { .. }) {
                    return Ok(Control::Return);
                }
            }
            Op::CallIntrinsic1 { dst, a, intrinsic } => {
                if intrinsic.arity().is_some_and(|n| n != 1) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec1(cx, a)?;
                frame.set(dst, val);
            }
            Op::CallIntrinsic2 { dst, a, b, intrinsic } => {
                if intrinsic.arity().is_some_and(|n| n != 2) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec2(cx, a, b)?;
                frame.set(dst, val);
            }
            Op::AddImm { dst, a, imm } => {
                let (x, k) = (frame.get(a), Value::fixnum(i64::from(imm)).ok_or(Fault::Malformed)?);
                let sum = match x.fixnum_add(k) {
                    Some(sum) => sum,
                    None => Intrinsic::Add.run(mc, &[x, k], &mut cx.fuel)?,
                };
                frame.set(dst, sum);
            }
            Op::StructField { dst, a, k } => frame.set(dst, structs::field(mc, frame.get(a), usize::from(k))?),
            Op::StructRef { dst, a, k, kind } => {
                let kind = cx.constants.get(mc, kind).ok_or(Fault::Malformed)?;
                frame.set(dst, structs::field_of(mc, frame.get(a), kind, usize::from(k))?);
            }
            Op::CallIntrinsic3 { dst, a, b, c, intrinsic } => {
                if intrinsic.arity().is_some_and(|n| n != 3) {
                    return Err(Fault::Malformed);
                }
                let val = intrinsic.exec3(cx, a, b, c)?;
                frame.set(dst, val);
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
    let module = frame.get(CLOSURE).downcast::<objects::Closure>(mc).and_then(|c| c.code(mc)).and_then(|code| code.module(mc));
    module.map(|m| m.items(mc)).filter(|slots| (slot as usize) < slots.len()).ok_or(Fault::Malformed)
}

/// Unpacks the elements of a proper Scheme list into a `Vec<Value>`, returning [`Fault::WrongType`] if the list is improper or non-nil terminated.
fn list<'gc>(mc: &Mutation<'gc>, mut list: Value<'gc>) -> Result<Vec<Value<'gc>>, Fault> {
    let mut items = Vec::new();
    while let Some(pair) = Pair::of(list) {
        items.push(pair.head(mc));
        list = pair.tail(mc);
    }
    if list != Value::NIL {
        return Err(Fault::WrongType);
    }
    Ok(items)
}
