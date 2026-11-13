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
