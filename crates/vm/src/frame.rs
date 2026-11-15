//! The calling convention: how a frame is laid out, how a call passes arguments, and how a
//! procedure returns values.
//!
//! # Frames
//!
//! A frame is a window of [`WINDOW`] registers on the stack segment, starting at its base.
//!
//! - Register [`CLOSURE`] (0) holds the closure that runs in the frame.
//! - Registers from [`ARGS`] (1) hold the parameters. A procedure has at most [`MAX_PARAMS`]
//!   parameter registers. See [`MAX_PARAMS`] for a procedure with more parameters.
//! - The register after the parameters holds the return [`Link`]. [`link_slot`] returns its index.
//! - The registers after the link are the procedure's locals and the staging area for its calls.
//!
//! A callee's frame overlaps its caller's. The caller puts the procedure in one of its registers,
//! `base`, and the arguments in the registers after it. The callee's frame starts at `base`, so the
//! procedure and the arguments are already where the callee expects them. `base` must be past the
//! caller's link, because everything from `base` up belongs to the callee during the call.
//!
//! ```text
//! caller:  [closure | params | link | locals ... | f | a | b | ...]
//! callee:                                        [f | a | b | link | locals ...]
//! ```
//!
//! A tail call moves the procedure and the arguments down to register 0 of the current frame and
//! keeps the frame's link, so the callee returns to the current frame's caller.
//!
//! # Links
//!
//! A [`Link`] says where a frame returns to: the caller resumes at instruction `pc`, in the frame
//! `base` registers below this one. A `base` of 0 marks the bottom frame of the segment. Returning
//! from it leaves the inner loop, and the outer loop continues with the next record of the
//! continuation chain.
//!
//! A link with `marks` set belongs to a call that changed the continuation marks. The caller's own
//! marks are saved [`SAVED_MARKS`] registers below the callee's base, and the return restores them.
//!
//! # Arguments
//!
//! A call passes a number of arguments in registers, optionally followed by the elements of one
//! list. Only `apply` and the calls that receive values pass a list.
//!
//! The callee's side checks the arguments, when the frame is entered:
//!
//! - The number of arguments must fit the procedure's [`Shape`], or the call fails with
//!   [`Fault::Arity`].
//! - A missing optional argument is bound to [`Value::UNSUPPLIED`].
//! - Arguments past the fixed parameters are gathered into the rest parameter's list.
//! - The list a call passes must be a proper list, or the call fails with [`Fault::WrongType`].
//!
//! The caller checks nothing. A call whose procedure is not a closure leaves the inner loop, and the
//! outer loop decides what calling that value means.
//!
//! # Returned values
//!
//! A procedure returns through the accumulator, which is not a register of any frame.
//!
//! - One value is the common case. The accumulator holds the value itself.
//! - No value, or several values, is the other case. The accumulator holds the marker
//!   [`Value::VALUES`], and the values are in a list beside it. Only the instructions for
//!   `(values x ...)` in tail position produce this.
//!
//! The side that takes the values checks how many there are:
//!
//! - A place that takes one value loads the accumulator into a register. That load fails with
//!   [`Fault::ValueCount`] when the accumulator holds the marker.
//! - A receiving call, as `call-with-values` compiles to, passes the values to its consumer as
//!   arguments. The consumer's shape is then checked as for any call.
//! - A return of what a call just returned passes the accumulator on unchanged.
//! - A result that nothing uses is not checked.
//!
//! For example, `(+ 1 (f))` loads the result of `(f)` and fails if `f` returned two values, while
//! `(call-with-values f list)` and a tail call `(f)` take whatever `f` returned.

use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Value, WINDOW};

use crate::Fault;
use crate::objects::{BytecodeFields, Closure, ClosureFields};

/// Register slot 0 of an execution frame, which holds the closure procedure being called (providing the bytecode, constant table, and captured upvalues).
pub const CLOSURE: u8 = 0;
/// Register index 1, where the first positional argument is placed in an execution frame.
pub const ARGS: u8 = 1;

/// The maximum number of parameter registers available in a frame starting at [`ARGS`]. If a procedure takes more parameters than this limit (counting any rest list as one parameter), the first `MAX_PARAMS - 1` arguments are passed in dedicated registers, and all subsequent arguments are collected into a list in the final parameter register, verified against the procedure's arity.
pub const MAX_PARAMS: u8 = (WINDOW / 4) as u8;

/// Computes the register slot index where the return [`Link`] is placed for a procedure with the given encoded `arity`, situated immediately after its parameter registers.
pub fn link_slot(arity: i64) -> u8 {
    ARGS + Shape::of(arity).slots().min(u64::from(MAX_PARAMS)) as u8
}

/// Describes the parameter arity of a procedure: the number of `required` positional parameters, up to `optional` additional parameters (defaulting to [`Value::UNSUPPLIED`] when omitted), and a boolean `rest` indicating whether further arguments are gathered into a rest list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub required: u64,
    pub optional: u64,
    pub rest: bool,
}

/// Bit flag (bit 48) marking an encoded arity integer that contains optional parameters, with parameter counts stored in the lower bits.
const OPTIONAL: i64 = 1 << 48;

impl Shape {
    /// Encodes this parameter shape as an `i64` arity representation stored in [`crate::objects::Bytecode`]. Without optional parameters, it follows Chez Scheme encoding: `n >= 0` for exactly `n` arguments, and `-(n + 1)` for at least `n` arguments with a rest list. With optional parameters, required and optional counts (16 bits each) and the rest flag are tagged with the high `OPTIONAL` bit, ensuring calls take the general arity-checking path. Returns `None` if counts exceed 16 bits.
    pub fn encode(self) -> Option<i64> {
        let required = i64::try_from(self.required).ok()?;
        Some(match (self.optional, self.rest) {
            (0, false) => required,
            (0, true) => -required - 1,
            (optional, rest) if self.required <= 0xFFFF && optional <= 0xFFFF => {
                OPTIONAL | required | (optional as i64) << 16 | i64::from(rest) << 32
            }
            _ => return None,
        })
    }

    pub fn of(arity: i64) -> Self {
        if arity < 0 {
            return Self { required: (-(arity + 1)) as u64, optional: 0, rest: true };
        }
        if arity & OPTIONAL == 0 {
            return Self { required: arity as u64, optional: 0, rest: false };
        }
        Self { required: (arity & 0xFFFF) as u64, optional: (arity >> 16 & 0xFFFF) as u64, rest: arity >> 32 & 1 == 1 }
    }

    /// Returns the total number of parameter slots bound by this shape, counting the rest list parameter as a single slot if present.
    pub fn slots(self) -> u64 {
        self.required + self.optional + u64::from(self.rest)
    }

    /// Returns `true` if this parameter shape accepts `count` positional arguments.
    pub fn takes(self, count: u64) -> bool {
        count >= self.required && (self.rest || count <= self.required + self.optional)
    }
}

/// Represents a frame's return address and restoration metadata: specifies that the caller resumes at instruction `pc` within its frame located `base` slots below this frame. If `marks` is true (set by a non-tail `with-mark`), returning restores the caller's continuation marks and guard, which are preserved [`SAVED_MARKS`] slots beneath the frame. Corresponds to the return address record in Chez Scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Link {
    pub pc: usize,
    pub base: u8,
    pub marks: bool,
}

/// The number of slots below a frame whose link has `marks` where the caller stores its own continuation marks, with any active [`crate::objects::Guard`] stored immediately above them.
pub const SAVED_MARKS: u8 = 2;

/// Slot offsets beneath a callee frame where a caller that established continuation marks saves its own marks and any exception [`Guard`](crate::objects::Guard) installed for the call.
#[derive(Clone, Copy)]
pub(crate) struct Kept {
    pub(crate) marks: usize,
    pub(crate) guard: usize,
}

impl Kept {
    /// Computes the slot locations for saved marks and guards stored below frame pointer `fp`, returning [`Fault::Malformed`] if the slots fall below `floor`.
    pub(crate) fn under(fp: usize, floor: usize) -> Result<Kept, Fault> {
        let marks = fp.checked_sub(usize::from(SAVED_MARKS)).filter(|&at| at >= floor).ok_or(Fault::Malformed)?;
        Ok(Kept { marks, guard: marks + 1 })
    }
}

impl Link {
    /// The return link for the bottommost frame on the current stack segment, whose caller resides in continuation records beneath it. Returning from this frame triggers stack underflow handling, analogous to Chez Scheme's `dounderflow`.
    pub const BOTTOM: Link = Link { pc: 0, base: 0, marks: false };

    /// Constructs a return [`Link`] resuming at instruction index `pc` in the caller frame at offset `base`, with `marks` set to `false`.
    pub fn to(pc: usize, base: u8) -> Link {
        Link { pc, base, marks: false }
    }

    pub fn is_bottom(self) -> bool {
        self.base == 0
    }

    /// Encodes the return link into an unboxed fixnum [`Value`] using the bit layout `(pc << 9) | ((marks as i64) << 8) | base` for storage in a frame slot.
    pub fn value<'gc>(self) -> Option<Value<'gc>> {
        Value::fixnum(i64::try_from(self.pc).ok()?.checked_mul(512)? | i64::from(self.marks) << 8 | i64::from(self.base))
    }

    pub fn of(value: Value<'_>) -> Option<Link> {
        let bits = u64::try_from(value.as_fixnum()?).ok()?;
        Some(Link { pc: usize::try_from(bits >> 9).ok()?, base: bits as u8, marks: bits & 256 != 0 })
    }
}

/// Computes the register slot index where the return link is located for a frame executing `closure`.
pub(crate) fn link_slot_of<'gc>(mc: &Mutation<'gc>, closure: Gc<'gc, Closure>) -> Result<u8, Fault> {
    closure.code(mc).map(|code| link_slot(code.arity(mc))).ok_or(Fault::Malformed)
}

/// Extracts and decodes the return [`Link`] for the frame located at offset `fp` within `slots`.
pub(crate) fn link_at<'gc>(mc: &Mutation<'gc>, slots: Slots<'gc>, fp: usize) -> Result<Link, Fault> {
    let closure = slots.get(fp).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    let at = fp + usize::from(link_slot_of(mc, closure)?);
    if at >= slots.len() {
        return Err(Fault::Malformed);
    }
    Link::of(slots.get(at)).ok_or(Fault::Malformed)
}

/// Returns the frames below the frame at `at`, which returns through `link`, nearest caller first. The walk stays within `slots` and at or above slot `floor`, and ends at a bottom frame.
pub(crate) fn callers<'m, 'gc>(mc: &'m Mutation<'gc>, slots: Slots<'gc>, floor: usize, at: usize, link: Link) -> Callers<'m, 'gc> {
    Callers { mc, slots, floor, at, link }
}

/// A frame that a walk down the links reached: its base, the instruction it resumes at, and the link it returns through itself.
pub(crate) struct Caller {
    pub(crate) at: usize,
    pub(crate) pc: usize,
    pub(crate) link: Link,
}

/// Walks down the links of the frames in one run of stack slots, as [`callers`] describes. A frame that cannot be read ends the walk with [`Fault::Malformed`].
pub(crate) struct Callers<'m, 'gc> {
    mc: &'m Mutation<'gc>,
    slots: Slots<'gc>,
    floor: usize,
    at: usize,
    link: Link,
}

impl Iterator for Callers<'_, '_> {
    type Item = Result<Caller, Fault>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.link.is_bottom() {
            return None;
        }
        let above = std::mem::replace(&mut self.link, Link::BOTTOM);
        let pc = above.pc;
        let Some(at) = self.at.checked_sub(usize::from(above.base)).filter(|&at| at >= self.floor && at < self.slots.len()) else { return Some(Err(Fault::Malformed)) };
        Some(link_at(self.mc, self.slots, at).map(|link| {
            (self.at, self.link) = (at, link);
            Caller { at, pc, link }
        }))
    }
}

/// Extracts and decodes the return [`Link`] stored in `frame`.
pub(crate) fn link_of<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>) -> Result<Link, Fault> {
    let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    Link::of(frame.get(link_slot_of(mc, closure)?)).ok_or(Fault::Malformed)
}

/// Encodes and writes the return [`Link`] into the designated link slot of `frame`.
pub(crate) fn set_link<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, link: Link) -> Result<(), Fault> {
    let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    frame.set(link_slot_of(mc, closure)?, link.value().ok_or(Fault::Malformed)?);
    Ok(())
}
