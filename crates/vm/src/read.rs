//! A [`Read`] runs on its arguments and the running task's dynamic state: its marks, prompts,
//! winders, and which task it is, which all but `set-winders!` only read. The inner loop runs it
//! as it does an intrinsic.
//!
//! A frame's code sees its marks and prompts change only across a request, but for the
//! winders, which `set-winders!` sets, for `dynamic-wind`: the compiler never moves a read, and
//! drops only those whose values go unused, never `set-winders!`.

use ragwort_types::gc::{Frame, Gc, Mutation, Value};
use ragwort_types::named;
use ragwort_types::pair::Pair;

use crate::intrinsic::made;
use crate::objects::{Task, TaskFields, Winder};
use crate::op::Fuel;
use crate::prompts::{self, tag_of};
use crate::Fault;

named! {
    #[repr(u8)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Read {
        /// `(mark-value key default)`: the value of the nearest mark for `key`, or `default`.
        MarkValue = "mark-value",
        /// `(frame-mark key default)`: the value of the nearest mark for `key` up to the nearest
        /// prompt, or `default`.
        FrameMark = "frame-mark",
        /// `(frame-marks key default tag)`: a list of the value of the nearest mark for `key` in
        /// each prompt's part of the continuation, innermost first, or `default` for a part with
        /// none, up to the nearest prompt for `tag`, or if `tag` is `#f`, all of them.
        FrameMarks = "frame-marks",
        /// `(co/running)`: the running coroutine, or in a machine's own task, that task, which
        /// is running until the machine finishes, and never pending, so nothing can resume it.
        Running = "co/running",
        /// `(winders)`: the task's winders, up to the nearest prompt, innermost first.
        Winders = "winders",
        /// `(set-winders! winders)`: sets them, to `()` or a list whose first is a winder.
        SetWinders = "set-winders!",
    }
}

impl Read {
    /// How many arguments it takes. Bytecode that passes another number is malformed.
    pub const fn arity(self) -> u8 {
        match self {
            Read::Running | Read::Winders => 0,
            Read::SetWinders => 1,
            Read::MarkValue | Read::FrameMark => 2,
            Read::FrameMarks => 3,
        }
    }

    /// Whether a call with valid arity cannot fault, so one whose value is unused can go.
    pub const fn is_discardable(self) -> bool {
        !matches!(self, Read::FrameMarks | Read::SetWinders)
    }

    /// Whether its value is never `#f`.
    pub const fn is_always_truthy(self) -> bool {
        matches!(self, Read::Running)
    }

    /// Runs it on the `args` registers from `base`.
    #[inline]
    pub(crate) fn exec<'gc>(self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, frame: Frame<'_, 'gc>, base: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, task, |i| frame.get(base + i), fuel)
    }

    /// Runs it on `arg(0)`, `arg(1)` and so on, as many as it takes.
    #[inline]
    pub(crate) fn apply<'gc>(
        self,
        mc: &Mutation<'gc>,
        task: Gc<'gc, Task>,
        arg: impl Fn(u8) -> Value<'gc>,
        fuel: &mut Fuel,
    ) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Read::MarkValue => prompts::mark(mc, task, arg(0), arg(1))?,
            Read::FrameMark => prompts::frame_mark(mc, task, arg(0), arg(1))?,
            Read::FrameMarks => {
                let tag = if arg(2) == Value::FALSE { None } else { Some(tag_of(mc, arg(2))?) };
                made(mc, fuel, prompts::part_marks(mc, task, arg(0), arg(1), tag)?)
            }
            Read::Running => Value::object(mc, task),
            Read::Winders => task.winders(mc),
            Read::SetWinders => {
                let winders = arg(0);
                if winders != Value::NIL && !Pair::of(winders).is_some_and(|cell| cell.head(mc).downcast::<Winder>(mc).is_some()) {
                    return Err(Fault::WrongType);
                }
                task.set_winders(mc, winders);
                Value::VOID
            }
        })
    }
}
