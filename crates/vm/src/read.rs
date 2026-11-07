//! A [`Read`] is a function of its arguments and the running task's dynamic state: its marks,
//! prompts, and which task it is. It changes nothing, so the inner loop runs it as it does an
//! intrinsic.
//!
//! What it reads only changes across a request, so its value is the same anywhere in a frame's
//! code, though not in a closure the frame makes, which can run under other marks: the compiler
//! may drop or reorder one, but never folds one or moves one into a lambda.

use ragwort_types::gc::{Frame, Gc, Mutation, Value};
use ragwort_types::named;

use crate::intrinsic::made;
use crate::objects::Task;
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
    }
}

impl Read {
    /// How many arguments it takes. Bytecode that passes another number is malformed.
    pub const fn arity(self) -> u8 {
        match self {
            Read::Running => 0,
            Read::MarkValue | Read::FrameMark => 2,
            Read::FrameMarks => 3,
        }
    }

    /// Whether a call with valid arity cannot fault, so one whose value is unused can go.
    pub const fn is_discardable(self) -> bool {
        !matches!(self, Read::FrameMarks)
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
        })
    }
}
