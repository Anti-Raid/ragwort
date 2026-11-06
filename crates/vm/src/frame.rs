use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Value, WINDOW};

use crate::Fault;
use crate::objects::{BytecodeFields, Closure, ClosureFields};

/// The procedure being called, whose code, constants and upvalues the frame runs with.
pub const CLOSURE: u8 = 0;
/// The first argument.
pub const ARGS: u8 = 1;

/// How many registers a frame keeps its parameters in, from [`ARGS`]. Code that takes more, its
/// rest list counted as one, gets the first `MAX_PARAMS - 1` of its arguments in registers and
/// a list of the others in the last, which the VM checks has as many as it takes.
pub const MAX_PARAMS: u8 = (WINDOW / 4) as u8;

/// Where the link is in a frame of code that takes `arity`, as `Bytecode` encodes it: after its
/// parameters' registers.
pub fn link_slot(arity: i64) -> u8 {
    ARGS + arity.unsigned_abs().min(u64::from(MAX_PARAMS)) as u8
}

/// Where a frame returns to: its caller goes on at `pc`, in its frame `base` slots below this
/// one. It's what Chez keeps as a frame's return address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Link {
    pub pc: usize,
    pub base: u8,
}

impl Link {
    /// The link of the bottom frame of the stack, whose caller is in the continuation records
    /// under it: returning from it underflows, as returning to Chez's `dounderflow` does.
    pub const BOTTOM: Link = Link { pc: 0, base: 0 };

    pub fn is_bottom(self) -> bool {
        self.base == 0
    }

    /// The link as a fixnum, `pc << 8 | base`, as it's kept in a frame.
    pub fn value<'gc>(self) -> Option<Value<'gc>> {
        Value::fixnum(i64::try_from(self.pc).ok()?.checked_mul(256)? | i64::from(self.base))
    }

    pub fn of(value: Value<'_>) -> Option<Link> {
        let n = u64::try_from(value.as_fixnum()?).ok()?;
        Some(Link { pc: usize::try_from(n >> 8).ok()?, base: n as u8 })
    }
}

/// Where the link is in a frame of `closure`.
pub(crate) fn link_slot_of<'gc>(mc: &Mutation<'gc>, closure: Gc<'gc, Closure>) -> Result<u8, Fault> {
    closure.code(mc).map(|code| link_slot(code.arity(mc))).ok_or(Fault::Malformed)
}

/// The link of the frame at `fp` of a record's slots.
pub(crate) fn link_at<'gc>(mc: &Mutation<'gc>, slots: Slots<'gc>, fp: usize) -> Result<Link, Fault> {
    let closure = slots.get(fp).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    let at = fp + usize::from(link_slot_of(mc, closure)?);
    if at >= slots.len() {
        return Err(Fault::Malformed);
    }
    Link::of(slots.get(at)).ok_or(Fault::Malformed)
}

/// The link of `frame`.
pub(crate) fn link_of<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>) -> Result<Link, Fault> {
    let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    Link::of(frame.get(link_slot_of(mc, closure)?)).ok_or(Fault::Malformed)
}

/// Sets the link of `frame`, whose procedure is a closure.
pub(crate) fn set_link<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, link: Link) -> Result<(), Fault> {
    let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
    frame.set(link_slot_of(mc, closure)?, link.value().ok_or(Fault::Malformed)?);
    Ok(())
}
