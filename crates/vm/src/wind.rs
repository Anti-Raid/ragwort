//! Inter-instruction VM operations: exception handling and non-local jump trampolines for
//! `dynamic-wind`. Similar to continuation handling in Lua, operations push a [`Native`] frame onto
//! the continuation chain before calling a procedure; upon return, the record's [`Kind`] determines
//! the subsequent action (such as executing additional thunks or completing an unwind).
//!
//! The handler stack is maintained in a continuation mark as an association list (innermost first)
//! containing handler procedures and [`Guard`] frames. Raising an exception invokes handlers with the
//! mark updated to reflect outer handlers, or unwinds to an enclosing guard. `dynamic-wind`
//! establishes [`Winder`](crate::objects::Winder) records around its thunk; non-local jumps out of its
//! dynamic extent run its `after` thunks, and jumps into its extent run its `before` thunks, each
//! executed with the task's active winders restricted to those enclosing the winder.

use ragwort_types::gc::{Gc, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};

use crate::{Fault, coroutine};
use crate::passed::Passed;
use crate::machine::{Outer, Then, condition};
use crate::objects::{Bytecode, Continuation, ContinuationFields, Guard, GuardFields, Native, NativeFields, PromptFields, TaskFields, WinderFields};
use crate::prompts::{self, Wind, default_tag, handler_key};
use crate::segments::{Cut, cut_at};

/// Specifies the action to execute when a [`Native`] continuation frame returns, parameterized by
/// stored values `a` and `b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// The exception handler invoked for `raise(a)` returned; raises a non-continuable exception error in
    /// its place.
    Handled,
    /// The guarded thunk for [`Guard`] `a` returned normally; returns its result, or returns `(#t .
    /// result)` if `b` indicates it was wrapped by `co/try-resume`.
    Guarded,
    /// Executes the first `(thunk . winders)` pair in list `a` with active winders set to `winders`, then
    /// processes the remaining pairs; once exhausted, completes the action specified by record `b`.
    Winds,
    /// Aborts to the nearest prompt matching tag `a`, passing the values in list `b`.
    Abort,
    /// Reinstates escape continuation `a` in place of the current continuation up to the nearest default
    /// prompt, passing values `b`.
    Escape,
    /// Composes continuation `a` on top of the current continuation, passing values `b`.
    Compose,
    /// Value `a` was raised without a handler, and all intervening `after` thunks have finished running.
    Uncaught,
    /// Value `b` was raised within [`Guard`] `a`; unwinds the stack to where the guard was established.
    Catch,
    /// The producer of a `receive` request returned. Calls consumer `a` with the values it returned.
    Receive,
    /// The producer of a `collect` request returned. Returns the list of the values it returned.
    Collect,
    /// The `after` winders of the coroutine that `co/close` or `co/reset` is closing have all run. Ends
    /// the coroutine and returns to the task that closed it. The new body for a reset is stored in
    /// the task's `body` field.
    Closed,
}

impl Kind {
    const ALL: [Kind; 11] = [
        Kind::Handled,
        Kind::Guarded,
        Kind::Winds,
        Kind::Abort,
        Kind::Escape,
        Kind::Compose,
        Kind::Uncaught,
        Kind::Catch,
        Kind::Receive,
        Kind::Collect,
        Kind::Closed,
    ];

    fn of(index: u32) -> Result<Kind, Fault> {
        Kind::ALL.get(index as usize).copied().ok_or(Fault::Malformed)
    }
}

impl<'gc> Outer<'_, 'gc> {
    /// Pushes a [`Native`] record of type `kind` onto the continuation chain as the return destination for
    /// the subsequent call.
    pub(crate) fn push(&self, kind: Kind, first: Value<'gc>, second: Value<'gc>) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let record = Native::new(mc, kind as u32, first, second, task.attachments(mc), task.chain(mc))?;
        task.set_chain(mc, Value::object(mc, record));
        Ok(())
    }

    /// Executes the action specified by [`Native`] record `native`, which has been popped from the head of
    /// the continuation chain.
    pub(crate) fn native(&mut self, native: Gc<'gc, Native>) -> Result<Then<'gc>, Fault> {
        self.step(Kind::of(native.kind(self.mc()))?, native.a(self.mc()), native.b(self.mc()))
    }

    fn step(&mut self, kind: Kind, first: Value<'gc>, second: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        Ok(match kind {
            Kind::Handled => {
                let message = string::from_str(&Strings::new(mc), "exception handler returned")?.value();
                Then::Raise(condition(mc, Fault::Error, message, Pairs::new(mc).cons(first, Value::NULL)?.value(mc))?, false)
            }
            Kind::Guarded if second == Value::FALSE => Then::Forward,
            Kind::Guarded => Then::ReturnValues(Pairs::new(mc).cons(Value::TRUE, self.regs.list(mc)?)?.value(mc)),
            Kind::Winds => match Pair::of(first) {
                Some(cell) => {
                    let wind = Pair::of(cell.head(mc)).ok_or(Fault::Malformed)?;
                    self.push(Kind::Winds, cell.tail(mc), second)?;
                    task.set_winders(mc, wind.tail(mc));
                    Then::Call(wind.head(mc), Passed::none())
                }
                None => self.native(second.downcast::<Native>(mc).ok_or(Fault::Malformed)?)?,
            },
            Kind::Abort => self.abort_now(first, Passed::list(second))?,
            Kind::Escape | Kind::Compose => self.go_now(first, kind == Kind::Escape, Passed::list(second))?,
            Kind::Uncaught => Then::Uncaught(first, true),
            Kind::Catch => {
                let guard = first.downcast::<Guard>(mc).ok_or(Fault::Malformed)?;
                let (part, Cut { chain, marks, free }, under) = self.back_to(first)?;
                let stack = &mut self.segments.stack;
                // `free` is set when the head record of the remaining chain is one-shot. The frames above the cut are discarded, so the stack takes back their slots from `at` up, if they are on its current segment.
                // This is done only when the guard was in the task's own chain (`part == 0`). In one chain, every record above a one-shot record is also one-shot, so no continuation holds those slots. A record in an enclosing prompt's chain can be one-shot while a captured continuation still holds frames above it.
                if let Some((segment, at)) = free
                    && part == 0
                    && segment == stack.segment(mc)
                    && !stack.reclaim(mc, at)
                {
                    return Err(Fault::Malformed);
                }
                task.set_prompts(mc, under);
                prompts::install(mc, task, chain, marks, guard.winders(mc));
                match guard.handler(mc) {
                    Value::FALSE => Then::ReturnValues(Pairs::new(mc).list(&[Value::FALSE, second])?),
                    handler => Then::Call(handler, self.pass(&[second])?),
                }
            }
            Kind::Receive => {
                let received = if self.regs.acc == Value::VALUES { Passed::list(self.regs.values) } else { self.pass(&[self.regs.acc])? };
                Then::Call(first, received)
            }
            Kind::Collect => Then::Return(self.regs.list(mc)?),
            Kind::Closed => {
                let (to, renew) = (coroutine::of(mc, task.resumer(mc)).ok_or(Fault::Malformed)?, task.body(mc));
                self.end(task, coroutine::DEAD, to)?;
                coroutine::closed(mc, task, renew)
            }
        })
    }

    /// Executes each `(thunk . winders)` entry in `todo`, then proceeds with action `kind` parameterized by
    /// `first` and `second`.
    fn unwind(&mut self, todo: Value<'gc>, kind: Kind, first: Value<'gc>, second: Value<'gc>) -> Result<Then<'gc>, Fault> {
        if todo == Value::NULL {
            return self.step(kind, first, second);
        }
        let mc = self.mc();
        let then = Native::new(mc, kind as u32, first, second, Value::NULL, Value::FALSE)?;
        self.step(Kind::Winds, todo, Value::object(mc, then))
    }

    /// Dispatches exception `obj`: invokes the innermost handler procedure (with active handlers updated
    /// to enclosing ones), unwinds to the innermost guard, or returns [`Then::Uncaught`] if no handler or
    /// guard exists.
    pub(crate) fn raising(&mut self, obj: Value<'gc>, continuable: bool, first: Option<(Gc<'gc, Bytecode>, usize)>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        let handlers = prompts::mark(mc, task, handler_key(), Value::NULL)?;
        let handler = Pair::of(handlers).map(|cell| cell.head(mc));
        // The call trace is recorded before any unwinding, unless the guard that catches the condition opted out of it.
        let quiet = handler.and_then(|handler| handler.downcast::<Guard>(mc)).is_some_and(|guard| !guard.traced(mc));
        if !quiet {
            self.record(obj, first)?;
        }
        let Some(cell) = Pair::of(handlers) else { return Ok(Then::Uncaught(obj, false)) };
        let handler = cell.head(mc);
        if let Some(guard) = handler.downcast::<Guard>(mc) {
            let winds = prompts::winds_above(mc, task, self.back_to(handler)?.0, guard.winders(mc))?;
            return self.unwind(winds_todo(mc, &winds, &[])?, Kind::Catch, handler, obj);
        }
        self.segments.set_mark(handler_key(), cell.tail(mc))?;
        if !continuable {
            self.push(Kind::Handled, obj, Value::VOID)?;
        }
        Ok(Then::Call(handler, self.pass(&[obj])?))
    }

    /// Executes all remaining `after` winders for an unhandled exception `obj`, then transitions to
    /// [`Then::Uncaught`].
    pub(crate) fn unwind_all(&mut self, obj: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let todo = winds_todo(mc, &prompts::winds(mc, self.task(), None)?, &[])?;
        self.unwind(todo, Kind::Uncaught, obj, Value::VOID)
    }

    /// Runs all the `after` winders of the running task, which is a coroutine being closed, and then
    /// finishes the close. See [`Kind::Closed`].
    ///
    /// An `after` thunk that raises with no handler is treated as any uncaught error. The remaining
    /// winders run, the coroutine fails, and the value is raised in the task that closed it.
    pub(crate) fn unwind_closing(&mut self) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let todo = winds_todo(mc, &prompts::winds(mc, self.task(), None)?, &[])?;
        self.unwind(todo, Kind::Closed, Value::VOID, Value::VOID)
    }

    /// Invokes `thunk` with `handler` installed as the innermost entry in the exception handlers
    /// continuation mark.
    pub(crate) fn with_handler(&mut self, handler: Value<'gc>, thunk: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        self.segments.set_mark(handler_key(), prompts::handlers_with(mc, task, handler)?)?;
        Ok(Then::Call(thunk, Passed::none()))
    }

    /// Pushes a new [`Guard`] record wrapping `handler` onto the chain (flagged as `co/try-resume` if
    /// `tried` is true) and installs it as the innermost handler mark for the subsequent call.
    pub(crate) fn guard(&mut self, handler: Value<'gc>, tried: bool, traced: bool) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let guard = Value::object(mc, Guard::new(mc, handler, task.winders(mc), traced)?);
        self.push(Kind::Guarded, guard, if tried { Value::TRUE } else { Value::FALSE })?;
        let pairs = Pairs::new(mc);
        let mark = pairs.cons(handler_key(), prompts::handlers_with(mc, task, guard)?)?.value(mc);
        task.set_attachments(mc, pairs.cons(mark, task.attachments(mc))?.value(mc));
        Ok(())
    }

    /// Locates the target return boundary for [`Guard`] `guard`: returns the prompt segment index
    /// (counting from the active segment), the continuation cut, and the underlying prompt list.
    fn back_to(&self, guard: Value<'gc>) -> Result<(usize, Cut<'gc>, Value<'gc>), Fault> {
        let (mc, task) = (self.mc(), self.task());
        if let Some(cut) = cut_at(mc, task.chain(mc), guard)? {
            return Ok((0, cut, task.prompts(mc)));
        }
        for (part, entry) in prompts::each(mc, task.prompts(mc)).enumerate() {
            let (prompt, under) = entry?;
            if let Some(cut) = cut_at(mc, prompt.chain(mc), guard)? {
                return Ok((part + 1, cut, under));
            }
        }
        Err(Fault::Malformed)
    }

    /// Aborts to the nearest prompt matching `tag` with `args`, after unwinding all `after` winders up to
    /// that prompt.
    ///
    /// `base` and `tail` give the position of the abort request, as for [`Outer::keep`]. An abort
    /// discards the frames up to the prompt, so the caller's frames are not saved first. They are
    /// saved in two cases. The first is when a winder has to run, because it runs on top of them.
    /// The second is when the abort fails, so that the error's trace includes the caller.
    pub(crate) fn abort(&mut self, tag: Value<'gc>, args: Passed<'gc>, base: u8, tail: bool) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let winds = prompts::tag_of(mc, tag).and_then(|tag| prompts::winds(mc, self.task(), Some(tag)));
        match winds.and_then(|winds| winds_todo(mc, &winds, &[])) {
            Ok(Value::NULL) => self.abort_now(tag, args),
            Ok(todo) => {
                self.keep(base, tail)?;
                self.unwind(todo, Kind::Abort, tag, args.to_list(mc)?)
            }
            Err(fault) => {
                self.keep(base, tail)?;
                Err(fault)
            }
        }
    }

    fn abort_now(&mut self, tag: Value<'gc>, args: Passed<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        Ok(match prompts::abort(mc, self.task(), tag)? {
            Some(handler) => Then::Call(handler, args),
            None => Then::Call(args.get(mc, 0)?, args.skip(mc, 1)?),
        })
    }

    /// Reinstates continuation `continuation` with `args` after executing necessary `before` and `after` winders:
    /// escape continuations unwind winders exited up to the common ancestor and rewind newly entered
    /// winders, while composable continuations rewind all of their own winders.
    pub(crate) fn go_to(&mut self, continuation: Gc<'gc, Continuation>, args: Passed<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let to = prompts::winds_of(mc, continuation)?;
        let (todo, kind) = if continuation.escape(mc) {
            let from = prompts::winds(mc, self.task(), Some(default_tag()))?;
            let same = from.iter().rev().zip(to.iter().rev()).take_while(|(left, right)| left.0 == right.0).count();
            (winds_todo(mc, &from[..from.len() - same], &to[..to.len() - same])?, Kind::Escape)
        } else {
            (winds_todo(mc, &[], &to)?, Kind::Compose)
        };
        if todo == Value::NULL {
            return self.go_now(Value::object(mc, continuation), kind == Kind::Escape, args);
        }
        self.unwind(todo, kind, Value::object(mc, continuation), args.to_list(mc)?)
    }

    /// Directly resumes continuation `continuation` with `args`, dispatching as either an escape continuation or a
    /// composable continuation.
    fn go_now(&mut self, continuation: Value<'gc>, escape: bool, args: Passed<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        if escape {
            prompts::clear_to_default(mc, task)?;
        }
        prompts::compose(mc, task, continuation.downcast::<Continuation>(mc).ok_or(Fault::Malformed)?)?;
        args.returned(mc)
    }
}

/// Builds a list of `(thunk . winders)` pairs containing the `after` thunks of `leaving` winders
/// (innermost first), followed by the `before` thunks of `entering` winders (outermost first).
fn winds_todo<'gc>(mc: &ragwort_types::gc::Mutation<'gc>, leaving: &[Wind<'gc>], entering: &[Wind<'gc>]) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut todo = Value::NULL;
    for &(winder, outside) in entering {
        todo = pairs.cons(pairs.cons(winder.before(mc), outside)?.value(mc), todo)?.value(mc);
    }
    for &(winder, outside) in leaving.iter().rev() {
        todo = pairs.cons(pairs.cons(winder.after(mc), outside)?.value(mc), todo)?.value(mc);
    }
    Ok(todo)
}
