//! A [`Request`] calls a procedure or changes the continuation, so the outer loop carries it
//! out. It reads its arguments out of the frame, keeps the continuation it returns to, then
//! runs, and what it leads to is a [`Then`]. What only reads the continuation's marks is a
//! [`Read`](crate::Read), which the inner loop runs.
//!
//! These are marks, prompts and continuations, as Racket has them, exceptions and the jumps that
//! run `dynamic-wind`'s winders, which the VM runs between calls of Scheme code, and switching
//! coroutines. The default prompt tag's handler is the prelude's.

use ragwort_types::gc::Value;
use ragwort_types::named;

use crate::Fault;
use crate::args::Args;
use crate::machine::{Outer, Then};
use crate::objects::{Continuation, MultiValue};
use crate::prompts::{self, tag_of};

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Request {
        /// `(apply f x ... list)`: calls `f` with the `x`s, then the elements of `list`: as many as
        /// fill `f`'s required parameters, the rest as its rest list, so a list of any length fits.
        /// The inner loop makes it a call itself, as it's already laid out as one.
        Apply = "apply",
        /// `(apply-values f v)`: calls `f` with the values in `v` if it's a [`MultiValue`], or
        /// with `v` alone.
        ApplyValues = "apply-values",
        /// `(with-mark key value f arg ...)`: calls `f` with the `arg`s, with a mark of `value`
        /// for `key` on its continuation. In tail position, it replaces the frame's mark for
        /// `key`, if it has one, so a loop that sets a mark stays in constant space.
        WithMark = "with-mark",
        /// `(call-with-prompt tag handler f arg ...)`: calls `f` with the `arg`s under a prompt for
        /// `tag`, which an abort to it calls `handler` in place of.
        CallWithPrompt = "call-with-prompt",
        /// `(abort tag value ...)`: runs the `after`s of the winders up to the nearest prompt for
        /// `tag`, then drops the continuation up to it, and the prompt, and calls its handler with
        /// the values in their place, as `abort-current-continuation` does.
        Abort = "abort",
        /// `(capture tag f)`: calls `f` with the composable continuation up to the nearest prompt
        /// for `tag`, a procedure that goes on with it on top of the continuation it's called in.
        Capture = "capture",
        /// `(compose k v ...)`: goes on with the continuation `k` on top of this one, returning
        /// the `v`s to it, without the `before`s of its winders that calling it runs.
        Compose = "compose",
        /// `(call/cc f)`: calls `f` with the escape continuation up to the nearest default prompt,
        /// which goes on in place of the continuation it's called in, up to the nearest default
        /// prompt, once the winders it leaves and enters have run.
        CallCc = "call/cc",
        /// `(with-exception-handler handler thunk)`: calls `thunk` with `handler` innermost on
        /// the handler stack.
        WithHandler = "with-exception-handler",
        /// `(raise obj)`: calls the innermost handler with `obj` and the handler stack outside
        /// it. If it returns, an error is raised there in its place. A raise with no handler runs
        /// the task's `after`s: then a coroutine fails, and `obj` is raised again where it was
        /// resumed, and a machine's own task ends with [`Outcome::Raised`](crate::Outcome::Raised).
        Raise = "raise",
        /// `(raise-continuable obj)`: as `raise`, but returns what the handler does.
        RaiseContinuable = "raise-continuable",
        /// `(guard thunk handler)`: calls `thunk`, and if it raises, goes back here, running the
        /// `after`s on the way, and calls `handler` with what was raised in place of `thunk`.
        Guard = "guard",
        /// `(co/resume co arg ...)`: runs the pending coroutine `co` until it yields, finishes or
        /// fails. It starts by calling its procedure with the `arg`s, or goes on from its last
        /// yield, which returns them. Returns what it yields or returns; if it fails, the same
        /// condition is raised here.
        Resume = "co/resume",
        /// `(co/try-resume co arg ...)`: as `co/resume`, but returns `#t` and what that does, or
        /// `#f` and what it raises.
        TryResume = "co/try-resume",
        /// `(co/yield v ...)`: suspends the running coroutine, so the `co/resume` that ran it
        /// returns the `v`s. In a machine's own task, it ends the run with
        /// [`Outcome::Yielded`](crate::Outcome::Yielded). Returns the values it's resumed with.
        Yield = "co/yield",
        /// `(keyword-apply f kws vals arg ... list)`: calls `f` with keywords `kws`, a sorted
        /// list, each passed its value in the list `vals`, and the `arg`s, then the elements of
        /// `list`. See [`crate::keyword`].
        KeywordApply = "keyword-apply",
    }
}

impl Request {
    /// Whether it takes `args` arguments. Bytecode that passes another number is malformed.
    pub fn takes(self, args: usize) -> bool {
        let (least, most) = match self {
            Request::Apply => (2, None),
            Request::WithMark | Request::CallWithPrompt => (3, None),
            Request::ApplyValues | Request::Capture | Request::WithHandler | Request::Guard => (2, Some(2)),
            Request::CallCc | Request::Raise | Request::RaiseContinuable => (1, Some(1)),
            Request::Abort | Request::Resume | Request::TryResume | Request::Compose => (1, None),
            Request::Yield => (0, None),
            Request::KeywordApply => (4, None),
        };
        args >= least && most.is_none_or(|most| args <= most)
    }

    /// Runs it on `args`, as many as it [takes](Request::takes).
    pub(crate) fn run<'gc>(self, outer: &mut Outer<'_, 'gc>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (outer.mc(), outer.task());
        let arg = |i| args.get(mc, i);
        Ok(match self {
            Request::Apply => Then::Call(arg(0)?, args.tail(mc, 1)?.spread_last(mc)?),
            Request::ApplyValues => {
                let v = arg(1)?;
                Then::Call(arg(0)?, if v.downcast::<MultiValue>(mc).is_some() { Args::list(v) } else { Args::one(v) })
            }
            Request::WithMark => {
                outer.segments.set_mark(arg(0)?, arg(1)?)?;
                Then::Call(arg(2)?, args.tail(mc, 3)?)
            }
            Request::CallWithPrompt => {
                prompts::push(mc, task, tag_of(mc, arg(0)?)?, arg(1)?)?;
                Then::Call(arg(2)?, args.tail(mc, 3)?)
            }
            Request::Abort => outer.abort(tag_of(mc, arg(0)?)?, args.tail(mc, 1)?)?,
            Request::Capture => {
                let k = prompts::capture(mc, task, tag_of(mc, arg(0)?)?, false)?;
                Then::Call(arg(1)?, Args::one(k))
            }
            Request::CallCc => {
                let k = prompts::capture(mc, task, prompts::default_tag(), true)?;
                Then::Call(arg(0)?, Args::one(k))
            }
            Request::Compose => {
                prompts::compose(mc, task, arg(0)?.downcast::<Continuation>(mc).ok_or(Fault::WrongType)?)?;
                Then::Return(args.tail(mc, 1)?.values(mc)?)
            }
            Request::WithHandler => outer.with_handler(arg(0)?, arg(1)?)?,
            Request::Raise => Then::Raise(arg(0)?, false),
            Request::RaiseContinuable => Then::Raise(arg(0)?, true),
            Request::Guard => {
                outer.guard(arg(1)?, false)?;
                Then::Call(arg(0)?, Args::none())
            }
            Request::Resume => Then::Resume(arg(0)?, args.tail(mc, 1)?),
            Request::TryResume => {
                outer.guard(Value::FALSE, true)?;
                Then::Resume(arg(0)?, args.tail(mc, 1)?)
            }
            Request::Yield => Then::Yield(outer.values(args)?),
            Request::KeywordApply => crate::keyword::apply(mc, arg(0)?, arg(1)?, arg(2)?, args.tail(mc, 3)?.spread_last(mc)?)?,
        })
    }
}
