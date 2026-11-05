//! The instruction set. Registers are `u8`s, slots of the current frame's window; jumps are
//! relative to the instruction after them.

use ragwort_types::{Error, named};
use ragwort_types::gc::{Frame, Mutation, OutOfMemory, Slots, Value};
use ragwort_types::constant::Constants;
use ragwort_types::num::NumError;
use ragwort_types::string::StrError;

use crate::objects::{self, BytecodeFields, ClosureFields, SpillFields};
use crate::machine::list;
use crate::{Intrinsic, Request};

#[cfg(test)]
#[path = "tests/op.rs"]
mod tests;

named! {
    /// One instruction. Every variant fits in 8 bytes: an opcode, registers, and up to a 32-bit
    /// index or offset.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Op {
        /// Move contents of register `src` to `dst`
        Move { dst: u8, src: u8 } = "move",
        /// Loads constant `index` of the constant pool
        LoadConst { dst: u8, index: u32 } = "load-const",
        /// Jump to offset `offset`
        Jump { offset: i32 } = "jump",
        /// Jumps to offset `offset` if register `test` holds `#f`.
        JumpIfFalse { test: u8, offset: i32 } = "jump-if-false",
        /// Calls the procedure in register `base` with the `args` registers after it, in a frame
        /// starting at `base`, as laid out in [`crate::frame`]: the callee's frame overlaps its
        /// caller's, so the arguments are already where it reads them. Anything the caller needs
        /// after the call is below `base`, which must be past the caller's link.
        Call { base: u8, args: u8 } = "call",
        /// Calls the procedure in register `base` with the `args` registers after it, moved down
        /// into the current frame. The frame's link stays, so the callee returns to this frame's
        /// caller.
        TailCall { base: u8, args: u8 } = "tail-call",
        /// Sets the accumulator to register `src` and returns it
        Return { src: u8 } = "return",
        /// Loads the accumulator, where a call leaves its result, into `dst`.
        LoadAcc { dst: u8 } = "load-acc",
        /// Loads upvalue `index` of the current closure. Upvalues are copied in when a closure is
        /// made, so an assigned variable is captured as a box, which the box intrinsics read and write.
        LoadUpvalue { dst: u8, index: u32 } = "load-upvalue",
        /// Makes `count` closures, of the code in constants `code..code + count`, into registers
        /// `dst..dst + count`, then fills each one's upvalues from its code's capture list. All are
        /// made before any is filled, so closures that refer to each other, as a `letrec` of lambdas
        /// makes, capture each other as registers.
        NewClosure { dst: u8, count: u8, code: u32 } = "new-closure",
        /// Runs `intrinsic` on the `args` registers from `base`, leaving its result in the
        /// accumulator as a call does, and goes on. The compiler emits it for a primitive that can't
        /// have been rebound, so an intrinsic can take fast paths, such as adding fixnums in place.
        CallIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "call-intrinsic",
        /// Runs `intrinsic` like `CallIntrinsic`, then returns its result. A built-in used as a value
        /// is a closure whose code is just this.
        TailCallIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "tail-call-intrinsic",
        /// Has the run loop carry out `request` on the `args` registers from `base`. One that calls a
        /// procedure, as `call/cc` does, goes on here when it returns, so `base` must be past the
        /// frame's link, as a call's is.
        CallRequest { base: u8, args: u8, request: Request } = "call-request",
        /// Like `CallRequest`, but a procedure the request calls takes this frame's place, so it
        /// returns to this frame's caller, as `(call/cc f)` in tail position needs.
        TailCallRequest { base: u8, args: u8, request: Request } = "tail-call-request",
        /// Runs `intrinsic` like `CallIntrinsic`, but the last of the `args` registers holds a list of
        /// the arguments after the others, as many as it takes, past the 255 registers can hold.
        ApplyIntrinsic { base: u8, args: u8, intrinsic: Intrinsic } = "apply-intrinsic",
        /// Carries out `request` like `CallRequest`, with the last of the `args` registers a list of
        /// the arguments after the others.
        ApplyRequest { base: u8, args: u8, request: Request } = "apply-request",
        /// `ApplyRequest` in tail position, as `TailCallRequest` is `CallRequest`'s.
        TailApplyRequest { base: u8, args: u8, request: Request } = "tail-apply-request",
        /// Makes a [`Spill`](crate::objects::Spill) of `count` slots, all void, in `dst`. Code that
        /// needs more registers than a frame has makes one as it starts.
        NewSpill { dst: u8, count: u32 } = "new-spill",
        /// Loads slot `slot` of the spill in register `spill`.
        LoadSpill { dst: u8, spill: u8, slot: u32 } = "load-spill",
        /// Stores register `src` in slot `slot` of the spill in register `spill`.
        StoreSpill { src: u8, spill: u8, slot: u32 } = "store-spill",
    }
}

const _: () = assert!(size_of::<Op>() == 8);

/// Where a new closure's upvalue comes from, in its code's capture list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capture {
    /// A register of the frame making the closure, read once all of a `NewClosure`'s closures
    /// are in theirs.
    Register(u8),
    /// An upvalue of the closure making it.
    Upvalue(u32),
    /// Slot `slot` of the spill in register `spill` of the frame making it.
    Spill { spill: u8, slot: u32 },
}

/// What an instruction runs against.
pub struct Context<'s, 'gc> {
    pub mc: &'s Mutation<'gc>,
    pub frame: Frame<'s, 'gc>,
    /// The module's constants, which `LoadConst` indexes.
    pub constants: Constants<'gc>,
    /// The current closure's upvalues.
    pub upvalues: Slots<'gc>,
    pub acc: Value<'gc>,
    pub fuel: Fuel,
}

/// What's left of a machine's fuel, as a run spends it. Calls and jumps spend a unit each of
/// `run`, and pause the run at the first of them once it's gone; an intrinsic that does a lot
/// of work spends from `run`, then `rest`. Pausing so the step can end, for a collection, moves
/// what's left of `run` to `rest`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fuel {
    pub run: u64,
    pub rest: u64,
}

impl Fuel {
    /// All that's left.
    pub fn left(self) -> u64 {
        self.run.saturating_add(self.rest)
    }

    /// Has the run pause at its next call or jump, keeping the fuel for the next run.
    pub fn pause(&mut self) {
        (self.run, self.rest) = (0, self.left());
    }

    /// Spends `units`, from `run` first, or faults with [`Fault::OutOfFuel`] if there aren't
    /// that many.
    pub fn spend(&mut self, units: u64) -> Result<(), Fault> {
        let past = units.saturating_sub(self.run);
        if past > self.rest {
            return Err(Fault::OutOfFuel);
        }
        (self.run, self.rest) = (self.run - (units - past), self.rest - past);
        Ok(())
    }
}

/// Where the run loop goes after an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Control {
    Next,
    /// `offset` instructions past the next one.
    Jump(i32),
    /// All the *many* Call insts
    Call { base: u8, args: u8 },
    TailCall { base: u8, args: u8 },
    /// A request on the `args` registers from `base`, the last of them a list of more if
    /// `spread`.
    CallRequest { base: u8, args: u8, request: Request, spread: bool },
    TailCallRequest { base: u8, args: u8, request: Request, spread: bool },
    /// Back to the caller, with the accumulator.
    Return,
}

/// Why an instruction couldn't run. All but the fatal ones are raised in the program, as a
/// `Condition`, and end the run only if no handler takes them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// The bytecode broke a rule the compiler keeps: a constant or upvalue that isn't there,
    /// registers past the frame, or an intrinsic or request passed a number of arguments it
    /// doesn't take.
    Malformed,
    OutOfMemory,
    /// An intrinsic got an argument it doesn't take, such as `car` of a non-pair.
    WrongType,
    /// An index past the end of what it indexes, or negative.
    OutOfRange,
    /// A write to something that can't change, such as a literal.
    Immutable,
    /// A procedure was called with a number of arguments it doesn't take.
    Arity,
    /// A call of something that isn't a procedure.
    NotProcedure,
    /// An abort or capture to a prompt tag with no prompt.
    NoPrompt,
    /// A reference to, or `set!` of, a global that isn't defined.
    Unbound,
    /// A run of a machine whose task already finished.
    Finished,
    /// The machine's fuel ran out, which finishes its task.
    OutOfFuel,
    /// What `make-error` makes a condition of.
    Error,
    Num(NumError),
    Str(StrError),
}

impl Fault {
    /// Whether it ends the run, rather than being raised: the bytecode or the machine is broken,
    /// or the arena is out of room, or the machine is out of fuel.
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
    /// Runs the instruction, or, for one that changes frames, says what the run loop should do.
    #[inline(always)]
    pub fn step<'gc>(self, cx: &mut Context<'_, 'gc>) -> Result<Control, Fault> {
        let (mc, frame) = (cx.mc, cx.frame);
        match self {
            Op::Move { dst, src } => frame.set(dst, frame.get(src)),
            Op::LoadConst { dst, index } => frame.set(dst, cx.constants.get(mc, index).ok_or(Fault::Malformed)?),
            Op::Jump { offset } => return Ok(Control::Jump(offset)),
            Op::JumpIfFalse { test, offset } => {
                if frame.get(test) == Value::FALSE {
                    return Ok(Control::Jump(offset));
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
                if usize::from(dst) + usize::from(count) > usize::from(u8::MAX) + 1 {
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
                if usize::from(base) + usize::from(args) > 256 || intrinsic.arity().is_some_and(|n| n != args) {
                    return Err(Fault::Malformed);
                }
                cx.acc = intrinsic.exec(mc, frame, base, args, &mut cx.fuel)?;
                if matches!(self, Op::TailCallIntrinsic { .. }) {
                    return Ok(Control::Return);
                }
            }
            Op::CallRequest { base, args, request } | Op::TailCallRequest { base, args, request } => {
                if usize::from(base) + usize::from(args) > 256 || !request.takes(usize::from(args)) {
                    return Err(Fault::Malformed);
                }
                return Ok(match self {
                    Op::CallRequest { .. } => Control::CallRequest { base, args, request, spread: false },
                    _ => Control::TailCallRequest { base, args, request, spread: false },
                });
            }
            Op::ApplyIntrinsic { base, args, intrinsic } => {
                if args == 0 || usize::from(base) + usize::from(args) > 256 {
                    return Err(Fault::Malformed);
                }
                let mut values: Vec<_> = (0..args - 1).map(|i| frame.get(base + i)).collect();
                values.extend(list(mc, frame.get(base + args - 1))?);
                cx.acc = intrinsic.run(mc, &values, &mut cx.fuel)?;
            }
            Op::ApplyRequest { base, args, request } | Op::TailApplyRequest { base, args, request } => {
                if args == 0 || usize::from(base) + usize::from(args) > 256 {
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
        }
        Ok(Control::Next)
    }
}

/// The slots of the spill in register `spill`, which has a slot `slot`.
#[inline]
fn spilled<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, spill: u8, slot: u32) -> Result<Slots<'gc>, Fault> {
    let slots = frame.get(spill).downcast::<objects::Spill>(mc).ok_or(Fault::Malformed)?.items(mc);
    if slot as usize >= slots.len() {
        return Err(Fault::Malformed);
    }
    Ok(slots)
}
