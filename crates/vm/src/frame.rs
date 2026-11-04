use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Value};

use crate::Fault;
use crate::objects::{BytecodeFields, Closure, ClosureFields};

/// The procedure being called, whose code, constants and upvalues the frame runs with.
pub const CLOSURE: u8 = 0;
/// The first argument.
pub const ARGS: u8 = 1;

/// Where the link is in a frame of code that takes `arity`, as `Bytecode` encodes it, or `None`
/// if that's past the window.
pub fn link_slot(arity: i64) -> Option<u8> {
    u8::try_from(arity.unsigned_abs().checked_add(1)?).ok()
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
    closure.code(mc).and_then(|code| link_slot(code.arity(mc))).ok_or(Fault::Malformed)
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
