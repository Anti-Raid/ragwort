//! VM runtime requests that alter control flow, invoke procedures, or manipulate continuations,
//! requiring execution by the outer VM loop. A request reads argument registers from the caller's
//! frame, reifies the return continuation onto the chain, and executes, producing a [`Then`]
//! directive. Dynamic state queries that only inspect task state without modifying continuations (such
//! as `mark-value`) are handled directly by the inner loop as
//! [intrinsics](crate::Intrinsic::is_dynamic).
//!
//! Requests implement delimited control operations (prompts, marks, and continuations modeled after
//! Racket), exception handling, `dynamic-wind` unwind/rewind trampolines, and coroutine resumption and
//! yielding. The default prompt tag handler is provided by the prelude.

use ragwort_types::gc::Value;
use ragwort_types::{Wire, named};

use crate::Fault;
use crate::args::Args;
use crate::machine::{Outer, Then};
use crate::objects::{Continuation, MultiValue};
use crate::prompts::{self, tag_of};

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
    pub enum Request {
        /// `(apply f x ... list)`: invokes `f` with positional arguments `x ...` followed by the unpacked
        /// elements of `list`. Elements are bound to fixed parameters with any remaining elements collected
        /// into a rest list. Executed directly as a call in the inner loop when arguments are already laid out
        /// in registers.
        Apply = "apply",
        /// `(apply-values f v)`: calls `f` with the multiple values contained in `v` if `v` is a
        /// [`MultiValue`], or with `v` itself as a single argument.
        ApplyValues = "apply-values",
        /// `(with-mark key value f arg ...)`: invokes `f` with arguments `arg ...`, attaching a continuation
        /// mark pairing `key` with `value` to the call's continuation. In tail position, replaces any existing
        /// mark for `key` in the current frame to preserve constant stack space.
        WithMark = "with-mark",
        /// `(call-with-prompt tag handler f arg ...)`: evaluates `(f arg ...)` delimited by a continuation
        /// prompt for `tag`. Aborting to `tag` removes the delimited continuation and invokes `handler` in its
        /// place.
        CallWithPrompt = "call-with-prompt",
        /// `(abort tag value ...)`: unwinds `after` winders up to the nearest prompt matching `tag`, discards
        /// the delimited continuation and the prompt, and invokes the prompt's handler with `value ...`
        /// (implementing `abort-current-continuation`).
        Abort = "abort",
        /// `(capture tag f)`: captures the delimited continuation up to the nearest prompt matching `tag` and
        /// invokes `f` with it as a composable continuation procedure, which when called reinstates the
        /// captured frames atop the caller's continuation.
        Capture = "capture",
        /// `(compose k v ...)`: composes continuation `k` directly onto the current continuation and delivers
        /// values `v ...` to it, bypassing the `before` winders normally executed when invoking `k` as a
        /// procedure.
        Compose = "compose",
        /// `(call/cc f)`: captures the escape continuation up to the nearest default prompt and calls `(f
        /// k)`. Invoking `k` replaces the current continuation up to the default prompt after executing
        /// intervening `after` and `before` winders.
        CallCc = "call/cc",
        /// `(with-exception-handler handler thunk)`: executes `thunk` with `handler` pushed as the innermost
        /// exception handler on the continuation marks stack.
        WithHandler = "with-exception-handler",
        /// `(raise obj)`: raises a non-continuable exception, invoking the innermost handler with `obj` while
        /// masking that handler from nested raises. If the handler returns, a non-continuable error is raised
        /// at the return point. If unhandled, executes all dynamic-wind `after` thunks; for coroutines, fails
        /// the coroutine and reraises in its resumer; for the root task, terminates with
        /// [`Outcome::Raised`](crate::Outcome::Raised).
        Raise = "raise",
        /// `(raise-continuable obj)`: raises a continuable exception, behaving like `raise` but returning the
        /// value produced by the handler to the raise site if the handler returns.
        RaiseContinuable = "raise-continuable",
        /// `(guard thunk handler)`: executes `thunk`; if an exception is raised, unwinds the stack to this
        /// point (running intervening `after` winders) and calls `handler` with the raised condition in place
        /// of `thunk`.
        Guard = "guard",
        /// `(guard/no-traceback thunk handler)`: behaves as `guard`, but a condition that this guard catches does not record a call trace when it is raised. Intended for guards that use errors as control flow.
        GuardQuiet = "guard/no-traceback",
        /// `(co/resume co arg ...)`: resumes pending coroutine `co` until it yields, finishes, or raises an
        /// unhandled exception. Passes `arg ...` to initialize the coroutine procedure or as the return values
        /// of its suspended `co/yield`. Returns the yielded or returned values; if the coroutine fails,
        /// reraises the unhandled condition at the call site.
        Resume = "co/resume",
        /// `(co/try-resume co arg ...)`: protected coroutine resumption, behaving like `co/resume` but
        /// returning values `(#t . result)` on success or `(#f . condition)` if the coroutine raises an
        /// unhandled exception.
        TryResume = "co/try-resume",
        /// `(co/yield v ...)`: suspends the active coroutine and returns values `v ...` from the enclosing
        /// `co/resume`. If invoked in the root task, terminates execution with
        /// [`Outcome::Yielded`](crate::Outcome::Yielded). When resumed, returns the arguments passed to
        /// `co/resume`.
        Yield = "co/yield",
        /// `(keyword-apply f kws vals arg ... list)`: calls `f` with keyword arguments defined by sorted symbol
        /// list `kws` and matching value list `vals`, followed by positional arguments `arg ...` and the
        /// unpacked elements of `list`. See [`crate::keyword`].
        KeywordApply = "keyword-apply",
    }
}

impl Request {
    /// Returns whether the request accepts `args` arguments; bytecode supplying any other argument count
    /// is malformed.
    pub fn takes(self, args: usize) -> bool {
        let (least, most) = match self {
            Request::Apply => (2, None),
            Request::WithMark | Request::CallWithPrompt => (3, None),
            Request::ApplyValues | Request::Capture | Request::WithHandler | Request::Guard | Request::GuardQuiet => (2, Some(2)),
            Request::CallCc | Request::Raise | Request::RaiseContinuable => (1, Some(1)),
            Request::Abort | Request::Resume | Request::TryResume | Request::Compose => (1, None),
            Request::Yield => (0, None),
            Request::KeywordApply => (4, None),
        };
        args >= least && most.is_none_or(|most| args <= most)
    }

    /// Executes the request with `args`, which must satisfy [takes](Request::takes).
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
            Request::Guard | Request::GuardQuiet => {
                outer.guard(arg(1)?, false, self == Request::Guard)?;
                Then::Call(arg(0)?, Args::none())
            }
            Request::Resume => Then::Resume(arg(0)?, args.tail(mc, 1)?),
            Request::TryResume => {
                outer.guard(Value::FALSE, true, true)?;
                Then::Resume(arg(0)?, args.tail(mc, 1)?)
            }
            Request::Yield => Then::Yield(outer.values(args)?),
            Request::KeywordApply => crate::keyword::apply(mc, arg(0)?, arg(1)?, arg(2)?, args.tail(mc, 3)?.spread_last(mc)?)?,
        })
    }
}
