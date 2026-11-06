//! Coroutines, as Lua has them: each is a [`Task`] with a stack of its own, which `co/resume`
//! runs until it yields, finishes or fails. Each has its own marks, prompts and continuation, so
//! a yield doesn't leave what it's in: it's still there when the coroutine is resumed.
//!
//! Switching is a cut, as a call of a one-shot continuation is: the side that's switched away
//! from hands its frames to its chain, keeps where its stack's live part starts, and the stack
//! moves to the other side's segment, whose chain then goes on in place. Nothing is copied.
//!
//! A machine's own task is a coroutine too, which nothing in the arena resumed: a yield in it
//! ends the run, and the machine is resumed from the host.

use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Segment, Value, WINDOW};

use crate::intrinsic::values;
use crate::machine::{Outer, Step, Then};
use crate::objects::{MultiValue, MultiValueFields, Task, TaskFields};
use crate::{Fault, Outcome};

/// The slots of a coroutine's first segment: a frame's window, and room past it for calls from
/// it. Deeper calls move to a bigger segment, as any overflow does.
const FIRST_SEGMENT: usize = WINDOW + 64;

pub(crate) const PENDING: u32 = 0;
pub(crate) const RUNNING: u32 = 1;
pub(crate) const FINISHED: u32 = 2;
pub(crate) const FAILED: u32 = 3;

/// A pending coroutine that starts by calling `body`.
pub(crate) fn new<'gc>(mc: &Mutation<'gc>, body: Value<'gc>) -> Result<Gc<'gc, Task>, OutOfMemory> {
    task(mc, body, PENDING)
}

/// A machine's own task, running.
pub(crate) fn root<'gc>(mc: &Mutation<'gc>) -> Result<Gc<'gc, Task>, OutOfMemory> {
    task(mc, Value::FALSE, RUNNING)
}

fn task<'gc>(mc: &Mutation<'gc>, body: Value<'gc>, state: u32) -> Result<Gc<'gc, Task>, OutOfMemory> {
    let none = Value::FALSE;
    Task::new(mc, Value::VOID, none, Value::NIL, Value::NIL, none, None, 0, body, none, none, None, 0, state, false)
}

pub(crate) fn of<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<Gc<'gc, Task>> {
    v.downcast::<Task>(mc)
}

/// The task running in a machine whose own task is `root`: the innermost one it resumed.
pub(crate) fn current<'gc>(mc: &Mutation<'gc>, root: Gc<'gc, Task>) -> Gc<'gc, Task> {
    let mut task = root;
    while let Some(inner) = of(mc, task.resumed(mc)) {
        task = inner;
    }
    task
}

/// `flag`, then `values`, as one value: what `co/try-resume` returns.
pub(crate) fn flagged<'gc>(mc: &Mutation<'gc>, flag: Value<'gc>, values_: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut all = vec![flag];
    match values_.downcast::<MultiValue>(mc) {
        Some(mv) => {
            let items = mv.items(mc);
            all.extend((0..items.len()).map(|i| items.get(i)));
        }
        None => all.push(values_),
    }
    values(mc, all.into_iter())
}

impl<'gc> Outer<'_, 'gc> {
    /// Resumes the coroutine `co` with `args`, for `co/resume`, or if `protected`,
    /// `co/try-resume`. The caller's continuation is on its chain already.
    pub(crate) fn resume_coroutine(&mut self, co: Value<'gc>, args: &[Value<'gc>], protected: bool) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        if co.state(mc) != PENDING {
            return Err(Fault::NotPending);
        }
        let from = self.task();
        self.leave(from)?;
        from.set_resumed(mc, Value::object(mc, co));
        co.set_resumer(mc, Value::object(mc, from));
        co.set_state(mc, RUNNING);
        co.set_protected(mc, protected);
        let body = co.body(mc);
        if body == Value::FALSE {
            self.enter_task(co)?;
            return self.then(Then::Return(values(mc, args.iter().copied())?));
        }
        co.set_body(mc, Value::FALSE);
        self.segments.stack.switch(mc, Segment::new(mc, FIRST_SEGMENT)?);
        self.segments.task = co;
        self.then(Then::Call(body, args.to_vec()))
    }

    /// Suspends the running coroutine, for `co/yield`, so what resumed it goes on with
    /// `yielded`. The coroutine's continuation is on its chain already.
    pub(crate) fn yield_coroutine(&mut self, yielded: Value<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let from = self.task();
        let Some(to) = of(mc, from.resumer(mc)) else {
            self.regs.acc = values(mc, std::iter::empty())?;
            return Ok(Some(Outcome::Yielded(yielded)));
        };
        self.leave(from)?;
        // A suspended coroutine keeps only the segments its frames are on.
        from.set_spare(mc, None);
        from.set_state(mc, PENDING);
        from.set_resumer(mc, Value::FALSE);
        self.back(to)?;
        let yielded = if from.protected(mc) { flagged(mc, Value::TRUE, yielded)? } else { yielded };
        self.then(Then::Return(yielded))
    }

    /// Ends the running coroutine as `state`, finished or failed, and goes back to `to`, which
    /// resumed it, with nothing of it kept.
    pub(crate) fn end(&mut self, task: Gc<'gc, Task>, state: u32, to: Gc<'gc, Task>) -> Result<(), Fault> {
        let mc = self.mc();
        let stack = &self.segments.stack;
        stack.set_top(stack.base());
        task.set_state(mc, state);
        task.set_resumer(mc, Value::FALSE);
        task.set_chain(mc, Value::FALSE);
        task.set_attachments(mc, Value::NIL);
        task.set_prompts(mc, Value::NIL);
        task.set_spare(mc, None);
        self.back(to)
    }

    /// Keeps where the running task's frames are, for when it's resumed: none are live past
    /// the stack's base, as its continuation is on its chain.
    fn leave(&mut self, task: Gc<'gc, Task>) -> Result<(), Fault> {
        let (mc, stack) = (self.mc(), &self.segments.stack);
        let base = stack.base();
        stack.set_top(base);
        task.set_segment(mc, Some(stack.segment(mc)));
        task.set_base(mc, u32::try_from(base).map_err(|_| Fault::Malformed)?);
        Ok(())
    }

    /// Goes back to `to`, which resumed the running task.
    fn back(&mut self, to: Gc<'gc, Task>) -> Result<(), Fault> {
        to.set_resumed(self.mc(), Value::FALSE);
        self.enter_task(to)
    }

    /// Moves the stack to where `task` left its frames, and makes it the running task.
    fn enter_task(&mut self, task: Gc<'gc, Task>) -> Result<(), Fault> {
        let mc = self.mc();
        let segment = task.segment(mc).ok_or(Fault::Malformed)?;
        if !self.segments.stack.resume(mc, segment, task.base(mc) as usize) {
            return Err(Fault::Malformed);
        }
        task.set_segment(mc, None);
        self.segments.task = task;
        Ok(())
    }
}
