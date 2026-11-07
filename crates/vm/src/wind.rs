//! What the VM runs between calls of Scheme code: `dynamic-wind`, exceptions and the jumps that
//! run winders, as Lua runs a C function's continuation. A request pushes a [`Native`] record on
//! the chain and calls a procedure; once that returns, the record's [`Kind`] says what comes
//! next, which may call another.
//!
//! The handlers mark holds the handler stack, as a list, innermost first: procedures, which a
//! raise calls with the mark set to those outside them, and [`Guard`]s, which it goes back to.
//! The winders mark holds each prompt's part of the continuation's [`Winder`]s. A jump out of
//! their extent runs their `after`s and one into it their `before`s, each with its part's mark
//! set to the winders outside it.

use ragwort_types::gc::{Gc, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};

use crate::Fault;
use crate::intrinsic::values;
use crate::args::Args;
use crate::machine::{Outer, Then, condition};
use crate::objects::{Continuation, ContinuationFields, Guard, GuardFields, MultiValue, Native, NativeFields, TaskFields, Winder, WinderFields};
use crate::prompts::{self, Wind, default_tag, handler_key, winders_key};

/// What a [`Native`] record does once what's above it returns, with its `a` and `b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// A `dynamic-wind`'s `before` returned: call its thunk, `b`, inside the winder `a`.
    WindIn,
    /// Its thunk returned: call the `after` of the winder `a`, then return what the thunk did.
    WindOut,
    /// Return `a`.
    Return,
    /// The handler of a `raise` of `a` returned: raise an error in its place.
    Handled,
    /// A `co/try-resume` returned: return `#t` and what it did.
    Tried,
    /// Call the thunk of the first `(thunk . winders)` of the list `a`, with the winders mark set
    /// to `winders`, then go on with the rest. Once there are none, go on as the record `b` does.
    Winds,
    /// Abort to the nearest prompt for the tag `a`, with the values of the list `b`.
    Abort,
    /// Go on with the escape continuation `a`, in place of the current one up to the nearest
    /// default prompt, with the values of the list `b`.
    Escape,
    /// Go on with the composable continuation `a` on top of the current one, with the values of
    /// the list `b`.
    Compose,
    /// `a` was raised with no handler, and the `after`s have run.
    Uncaught,
    /// `b` was raised to the [`Guard`] `a`: go back to its prompt.
    Catch,
}

impl Kind {
    const ALL: [Kind; 11] = [
        Kind::WindIn,
        Kind::WindOut,
        Kind::Return,
        Kind::Handled,
        Kind::Tried,
        Kind::Winds,
        Kind::Abort,
        Kind::Escape,
        Kind::Compose,
        Kind::Uncaught,
        Kind::Catch,
    ];

    fn of(n: u32) -> Result<Kind, Fault> {
        Kind::ALL.get(n as usize).copied().ok_or(Fault::Malformed)
    }
}

impl<'gc> Outer<'_, 'gc> {
    /// Pushes a record of `kind` on the chain, for what's called next to return to.
    pub(crate) fn push(&self, kind: Kind, a: Value<'gc>, b: Value<'gc>) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let record = Native::new(mc, kind as u32, a, b, task.attachments(mc), task.chain(mc))?;
        task.set_chain(mc, Value::object(mc, record));
        Ok(())
    }

    /// Goes on from `native`, the record on top of the chain, which it's already taken off.
    pub(crate) fn native(&mut self, native: Gc<'gc, Native>) -> Result<Then<'gc>, Fault> {
        self.step(Kind::of(native.kind(self.mc()))?, native.a(self.mc()), native.b(self.mc()))
    }

    fn step(&mut self, kind: Kind, a: Value<'gc>, b: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        Ok(match kind {
            Kind::WindIn => {
                self.push(Kind::WindOut, a, Value::VOID)?;
                let outside = prompts::frame_mark(mc, task, winders_key(), Value::NIL)?;
                self.segments.set_mark(winders_key(), Pairs::new(mc).cons(a, outside)?.value(mc))?;
                Then::Call(b, Args::none())
            }
            Kind::WindOut => {
                self.push(Kind::Return, self.regs.acc, Value::VOID)?;
                Then::Call(a.downcast::<Winder>(mc).ok_or(Fault::Malformed)?.after(mc), Args::none())
            }
            Kind::Return => Then::Return(a),
            Kind::Handled => {
                let message = string::from_str(&Strings::new(mc), "exception handler returned")?.value();
                Then::Raise(condition(mc, Fault::Error, message, Pairs::new(mc).cons(a, Value::NIL)?.value(mc))?, false)
            }
            Kind::Tried => {
                let acc = self.regs.acc;
                let all = if acc.downcast::<MultiValue>(mc).is_some() { Args::before(Value::TRUE, acc) } else { Args::two(Value::TRUE, acc) };
                Then::Return(all.values(mc)?)
            }
            Kind::Winds => match Pair::of(a) {
                Some(cell) => {
                    let wind = Pair::of(cell.head(mc)).ok_or(Fault::Malformed)?;
                    self.push(Kind::Winds, cell.tail(mc), b)?;
                    self.segments.set_mark(winders_key(), wind.tail(mc))?;
                    Then::Call(wind.head(mc), Args::none())
                }
                None => self.native(b.downcast::<Native>(mc).ok_or(Fault::Malformed)?)?,
            },
            Kind::Abort => self.abort_now(a, Args::list(b))?,
            Kind::Escape | Kind::Compose => self.go_now(a, kind == Kind::Escape, Args::list(b))?,
            Kind::Uncaught => Then::Uncaught(a, true),
            Kind::Catch => {
                prompts::abort(mc, task, a)?;
                match a.downcast::<Guard>(mc).ok_or(Fault::Malformed)?.handler(mc) {
                    Value::FALSE => Then::Return(values(mc, [Value::FALSE, b].into_iter())?),
                    handler => Then::Call(handler, Args::one(b)),
                }
            }
        })
    }

    /// Runs the thunks of `todo`, a list of `(thunk . winders)`, then goes on as `kind` does with
    /// `a` and `b`.
    fn unwind(&mut self, todo: Value<'gc>, kind: Kind, a: Value<'gc>, b: Value<'gc>) -> Result<Then<'gc>, Fault> {
        if todo == Value::NIL {
            return self.step(kind, a, b);
        }
        let mc = self.mc();
        let then = Native::new(mc, kind as u32, a, b, Value::NIL, Value::FALSE)?;
        self.step(Kind::Winds, todo, Value::object(mc, then))
    }

    /// What raising `obj` leads to: a call of the innermost handler, with the handlers mark set
    /// to those outside it, which a raise that isn't `continuable` doesn't return from, or a jump
    /// to the innermost guard, or if there's neither, [`Then::Uncaught`].
    pub(crate) fn raising(&mut self, obj: Value<'gc>, continuable: bool) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        let handlers = prompts::mark(mc, task, handler_key(), Value::NIL)?;
        let Some(cell) = Pair::of(handlers) else { return Ok(Then::Uncaught(obj, false)) };
        let handler = cell.head(mc);
        if handler.downcast::<Guard>(mc).is_some() {
            let todo = winds_todo(mc, &prompts::winds(mc, task, Some(handler))?, &[])?;
            return self.unwind(todo, Kind::Catch, handler, obj);
        }
        self.segments.set_mark(handler_key(), cell.tail(mc))?;
        if !continuable {
            self.push(Kind::Handled, obj, Value::VOID)?;
        }
        Ok(Then::Call(handler, Args::one(obj)))
    }

    /// Runs the task's `after`s, for `obj`, raised with no handler, then goes on as
    /// [`Then::Uncaught`] does once they have.
    pub(crate) fn unwind_all(&mut self, obj: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let todo = winds_todo(mc, &prompts::winds(mc, self.task(), None)?, &[])?;
        self.unwind(todo, Kind::Uncaught, obj, Value::VOID)
    }

    /// Calls `thunk` with `handler` innermost in the handlers mark.
    pub(crate) fn with_handler(&mut self, handler: Value<'gc>, thunk: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        let handlers = prompts::mark(mc, task, handler_key(), Value::NIL)?;
        self.segments.set_mark(handler_key(), Pairs::new(mc).cons(handler, handlers)?.value(mc))?;
        Ok(Then::Call(thunk, Args::none()))
    }

    /// Calls `before`, then `thunk` inside a winder of them, then `after`, and returns what
    /// `thunk` did.
    pub(crate) fn dynamic_wind(&mut self, before: Value<'gc>, thunk: Value<'gc>, after: Value<'gc>) -> Result<Then<'gc>, Fault> {
        let winder = Winder::new(self.mc(), before, after)?;
        self.push(Kind::WindIn, Value::object(self.mc(), winder), thunk)?;
        Ok(Then::Call(before, Args::none()))
    }

    /// Puts a prompt for a new [`Guard`] of `handler` on the continuation, and the guard
    /// innermost in the handlers mark, for what's called next.
    pub(crate) fn guard(&mut self, handler: Value<'gc>, tried: bool) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let guard = Value::object(mc, Guard::new(mc, handler)?);
        prompts::push(mc, task, guard, Value::VOID)?;
        if tried {
            self.push(Kind::Tried, Value::VOID, Value::VOID)?;
        }
        let handlers = prompts::mark(mc, task, handler_key(), Value::NIL)?;
        self.segments.set_mark(handler_key(), Pairs::new(mc).cons(guard, handlers)?.value(mc))
    }

    /// Aborts to the nearest prompt for `tag` with `args`, once the `after`s of the winders up to
    /// it have run.
    pub(crate) fn abort(&mut self, tag: Value<'gc>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let todo = winds_todo(mc, &prompts::winds(mc, self.task(), Some(tag))?, &[])?;
        if todo == Value::NIL {
            return self.abort_now(tag, args);
        }
        self.unwind(todo, Kind::Abort, tag, args.to_list(mc)?)
    }

    fn abort_now(&mut self, tag: Value<'gc>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        Ok(match prompts::abort(mc, self.task(), tag)? {
            Some(handler) => Then::Call(handler, args),
            None => Then::Call(args.get(mc, 0)?, args.tail(mc, 1)?),
        })
    }

    /// Goes on with `k` with `args`, once the winders it leaves and enters have run: an escape
    /// continuation leaves those up to the nearest default prompt that it doesn't hold, and
    /// enters those it holds that the current continuation doesn't; a composable one enters all
    /// of its own.
    pub(crate) fn go_to(&mut self, k: Gc<'gc, Continuation>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
        let mc = self.mc();
        let to = prompts::winds_of(mc, k)?;
        let (todo, kind) = if k.escape(mc) {
            let from = prompts::winds(mc, self.task(), Some(default_tag()))?;
            let same = from.iter().rev().zip(to.iter().rev()).take_while(|(f, t)| f.0 == t.0).count();
            (winds_todo(mc, &from[..from.len() - same], &to[..to.len() - same])?, Kind::Escape)
        } else {
            (winds_todo(mc, &[], &to)?, Kind::Compose)
        };
        if todo == Value::NIL {
            return self.go_now(Value::object(mc, k), kind == Kind::Escape, args);
        }
        self.unwind(todo, kind, Value::object(mc, k), args.to_list(mc)?)
    }

    /// Goes on with the continuation `k` with `args`, as an escape or composed.
    fn go_now(&mut self, k: Value<'gc>, escape: bool, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (self.mc(), self.task());
        if escape {
            prompts::clear_to_default(mc, task)?;
        }
        prompts::compose(mc, task, k.downcast::<Continuation>(mc).ok_or(Fault::Malformed)?)?;
        Ok(Then::Return(args.values(mc)?))
    }
}

/// The `after`s of `leaving`, innermost first, then the `before`s of `entering`, outermost first,
/// as a list of `(thunk . winders)`.
fn winds_todo<'gc>(mc: &ragwort_types::gc::Mutation<'gc>, leaving: &[Wind<'gc>], entering: &[Wind<'gc>]) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut todo = Value::NIL;
    for &(winder, outside) in entering {
        todo = pairs.cons(pairs.cons(winder.before(mc), outside)?.value(mc), todo)?.value(mc);
    }
    for &(winder, outside) in leaving.iter().rev() {
        todo = pairs.cons(pairs.cons(winder.after(mc), outside)?.value(mc), todo)?.value(mc);
    }
    Ok(todo)
}
