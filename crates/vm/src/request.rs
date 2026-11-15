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
use crate::passed::Passed;
use crate::machine::{Outer, Then};
use crate::objects::Continuation;
use crate::prompts::{self, tag_of};
use crate::wind::Kind;

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
    pub enum Request {
        /// `(apply f x ... list)`: invokes `f` with positional arguments `x ...` followed by the unpacked
        /// elements of `list`. Elements are bound to fixed parameters with any remaining elements collected
        /// into a rest list. Executed directly as a call in the inner loop when arguments are already laid out
        /// in registers.
        Apply = "apply",
        /// `(receive consumer producer arg ...)`: calls `producer` with `arg ...`, then calls `consumer`
        /// with the values it returned. The compiler emits a call followed by
        /// [`Op::CallReceived`](crate::Op::CallReceived) for it. The request itself runs only when its
        /// arguments are spread from a list.
        Receive = "receive",
        /// `(collect producer arg ...)`: calls `producer` with `arg ...` and returns the values it
        /// returned as one list. The compiler emits a call followed by
        /// [`Op::LoadValues`](crate::Op::LoadValues) for it, as it does for `receive`.
        Collect = "collect",
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
        /// `(co/resume-error co obj)`: resumes pending coroutine `co` by raising `obj` inside it, at the
        /// `co/yield` it is suspended in. If the coroutine catches `obj`, this returns as `co/resume` does.
        /// If it does not, the coroutine fails and `obj` is raised at the call site. A coroutine that has
        /// not started fails without running its body.
        ResumeError = "co/resume-error",
        /// `(co/close co)`: ends suspended coroutine `co` without running the rest of its body. The `after`
        /// thunks of the `dynamic-wind` calls it is suspended in run first, innermost first. Returns void.
        /// A coroutine that is already dead or failed is left as it is. An `after` thunk that raises with
        /// no handler fails the coroutine, and the value is raised at the call site. `co/yield` fails
        /// while a coroutine is being closed.
        Close = "co/close",
        /// `(co/reset co thunk)`: closes `co` as `co/close` does, then makes it pending again with
        /// procedure `thunk` as its body. Returns `co`. If an `after` thunk raises with no handler, the
        /// value is raised at the call site, and `co` is pending with the new body all the same.
        Reset = "co/reset",
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
            Request::Apply | Request::Receive => (2, None),
            Request::WithMark | Request::CallWithPrompt => (3, None),
            Request::Capture | Request::WithHandler | Request::Guard | Request::GuardQuiet => (2, Some(2)),
            Request::CallCc | Request::Raise | Request::RaiseContinuable | Request::Close => (1, Some(1)),
            Request::ResumeError | Request::Reset => (2, Some(2)),
            Request::Abort | Request::Resume | Request::TryResume | Request::Compose | Request::Collect => (1, None),
            Request::Yield => (0, None),
            Request::KeywordApply => (4, None),
        };
        args >= least && most.is_none_or(|most| args <= most)
    }

    /// Returns the number of leading operands the request reads itself. The operands after them are passed on to a procedure or returned.
    pub fn fixed(self) -> usize {
        match self {
            Request::Yield => 0,
            Request::Apply | Request::Collect | Request::Abort | Request::Compose | Request::CallCc | Request::Raise | Request::RaiseContinuable | Request::Resume | Request::TryResume | Request::Close => 1,
            Request::Receive | Request::Capture | Request::WithHandler | Request::Guard | Request::GuardQuiet | Request::ResumeError | Request::Reset => 2,
            Request::WithMark | Request::CallWithPrompt | Request::KeywordApply => 3,
        }
    }

    /// Executes the request with `args`, which must satisfy [takes](Request::takes). `base` and `tail` say where the request was made, as [`Outer::keep`] takes them.
    pub(crate) fn run<'gc>(self, outer: &mut Outer<'_, 'gc>, args: Passed<'gc>, base: u8, tail: bool) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (outer.mc(), outer.task());
        let arg = |index| args.get(mc, index);
        Ok(match self {
            Request::Apply => Then::Call(arg(0)?, args.skip(mc, 1)?.spread_last(mc)?),
            Request::Receive => {
                outer.push(Kind::Receive, arg(0)?, Value::VOID)?;
                Then::Call(arg(1)?, args.skip(mc, 2)?)
            }
            Request::Collect => {
                outer.push(Kind::Collect, Value::VOID, Value::VOID)?;
                Then::Call(arg(0)?, args.skip(mc, 1)?)
            }
            Request::WithMark => {
                outer.segments.set_mark(arg(0)?, arg(1)?)?;
                Then::Call(arg(2)?, args.skip(mc, 3)?)
            }
            Request::CallWithPrompt => {
                prompts::push(mc, task, tag_of(mc, arg(0)?)?, arg(1)?)?;
                Then::Call(arg(2)?, args.skip(mc, 3)?)
            }
            Request::Abort => outer.abort(arg(0)?, args.skip(mc, 1)?, base, tail)?,
            Request::Capture => {
                let continuation = prompts::capture(mc, task, tag_of(mc, arg(0)?)?, false)?;
                Then::Call(arg(1)?, outer.pass(&[continuation])?)
            }
            Request::CallCc => {
                let continuation = prompts::capture(mc, task, prompts::default_tag(), true)?;
                Then::Call(arg(0)?, outer.pass(&[continuation])?)
            }
            Request::Compose => {
                prompts::compose(mc, task, arg(0)?.downcast::<Continuation>(mc).ok_or(Fault::WrongType)?)?;
                args.skip(mc, 1)?.returned(mc)?
            }
            Request::WithHandler => outer.with_handler(arg(0)?, arg(1)?)?,
            Request::Raise => Then::Raise(arg(0)?, false),
            Request::RaiseContinuable => Then::Raise(arg(0)?, true),
            Request::Guard | Request::GuardQuiet => {
                outer.guard(arg(1)?, false, self == Request::Guard)?;
                Then::Call(arg(0)?, Passed::none())
            }
            // `Outer::request` makes these switches itself.
            Request::Resume | Request::TryResume | Request::Yield => return Err(Fault::Malformed),
            Request::ResumeError => Then::ResumeError(arg(0)?, arg(1)?),
            Request::Close => Then::Close(arg(0)?, Value::FALSE),
            Request::Reset => {
                let thunk = arg(1)?;
                if !crate::intrinsic::is_procedure(mc, thunk) {
                    return Err(Fault::WrongType);
                }
                Then::Close(arg(0)?, thunk)
            }
            Request::KeywordApply => crate::keyword::apply(mc, arg(0)?, arg(1)?, arg(2)?, args.skip(mc, 3)?.spread_last(mc)?)?,
        })
    }
}
