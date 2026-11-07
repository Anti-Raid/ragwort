//! Coroutines, as Lua has them: each is a [`Task`] with a stack of its own, which `co/resume`
//! runs until it yields, finishes or fails. Each has its own marks, prompts and continuation, so
//! a yield doesn't leave what it's in: it's still there when the coroutine is resumed.
//!
//! Switching is a cut, as a call of a one-shot continuation is: the side that's switched away
//! from hands its frames to its chain, keeps where its stack's live part starts, and the stack
//! moves to the other side's segment, whose chain then goes on in place. Nothing is copied.
//!
//! A suspended coroutine needs no room past its frames, so a yield copies them to a segment of
//! their own size when nothing else holds the segment they were on, which then goes to the
//! resumer as its spare: the next coroutine it resumes runs there, and the frames of one that
//! was copied are copied back as it returns into them.
//!
//! A machine's own task is a coroutine too, which nothing in the arena resumed: a yield in it
//! ends the run, and the machine is resumed from the host.

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Segment, Value, WINDOW};

use crate::args::Args;
use crate::intrinsic::values;
use crate::machine::{Outer, Step, Then};
use crate::objects::{Frames, FramesFields, Native, NativeFields, Task, TaskFields};
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
    Task::new(mc, Value::VOID, none, Value::NIL, Value::NIL, None, 0, body, none, none, None, 0, state)
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

/// Makes `segment`, which nothing holds, `task`'s spare, unless it has one.
fn give<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, segment: Gc<'gc, Segment>) {
    if task.spare(mc).is_none() {
        task.set_spare(mc, Some(segment));
        task.set_spare_base(mc, 0);
    }
}

impl<'gc> Outer<'_, 'gc> {
    /// Resumes the coroutine `co` with `args`, for `co/resume`. The caller's continuation is on
    /// its chain already.
    pub(crate) fn resume_coroutine(&mut self, co: Value<'gc>, args: Args<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        if co.state(mc) != PENDING {
            return Err(Fault::NotPending);
        }
        let args = args.detach(mc)?;
        let from = self.task();
        self.leave(from)?;
        from.set_resumed(mc, Value::object(mc, co));
        co.set_resumer(mc, Value::object(mc, from));
        co.set_state(mc, RUNNING);
        let body = co.body(mc);
        if body == Value::FALSE && co.segment(mc).is_some() {
            self.enter_task(co)?;
            return self.then(Then::Return(args.values(mc)?));
        }
        let segment = self.free_segment(from)?;
        self.segments.stack.switch(mc, segment);
        self.segments.task = co;
        if body == Value::FALSE {
            return self.then(Then::Return(args.values(mc)?));
        }
        co.set_body(mc, Value::FALSE);
        self.then(Then::Call(body, args))
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
        let freed = self.compact(from)?;
        self.back(to)?;
        if let Some(segment) = freed {
            give(mc, to, segment);
        }
        self.then(Then::Return(yielded))
    }

    /// Ends the running coroutine as `state`, finished or failed, and goes back to `to`, which
    /// resumed it, with nothing of it kept.
    pub(crate) fn end(&mut self, task: Gc<'gc, Task>, state: u32, to: Gc<'gc, Task>) -> Result<(), Fault> {
        let mc = self.mc();
        let stack = &self.segments.stack;
        let base = stack.base();
        stack.set_top(base);
        // With nothing below its base, nothing holds the segment.
        let freed = (base == 0).then(|| stack.segment(mc));
        task.set_state(mc, state);
        task.set_resumer(mc, Value::FALSE);
        task.set_chain(mc, Value::FALSE);
        task.set_attachments(mc, Value::NIL);
        task.set_prompts(mc, Value::NIL);
        task.set_spare(mc, None);
        self.back(to)?;
        if let Some(segment) = freed {
            give(mc, to, segment);
        }
        Ok(())
    }

    /// Copies the frames of `task`, which is suspending, to a segment of their own size, if its
    /// chain's records hold all the stack's segment has below its base and no continuation
    /// holds them, and returns that segment, which is then free. Only a few frames are copied,
    /// a window's worth, as a yield from deeper would copy them each time: their segment is
    /// mostly theirs anyway.
    fn compact(&mut self, task: Gc<'gc, Task>) -> Result<Option<Gc<'gc, Segment>>, Fault> {
        let mc = self.mc();
        let (segment, base) = (self.segments.stack.segment(mc), self.segments.stack.base());
        if base > WINDOW {
            return Ok(None);
        }
        let (mut run, mut chain, mut end) = (Vec::new(), task.chain(mc), base);
        while end > 0 {
            if let Some(native) = chain.downcast::<Native>(mc) {
                chain = native.next(mc);
                continue;
            }
            let Some(record) = chain.downcast::<Frames>(mc) else { return Ok(None) };
            if record.segment(mc) != Some(segment) || !record.one_shot(mc) || record.owns(mc) || record.end(mc) as usize != end {
                return Ok(None);
            }
            end = record.start(mc) as usize;
            chain = record.next(mc);
            run.push(record);
        }
        if base > 0 {
            let copy = Segment::new(mc, base)?;
            let frames = segment.slots(mc).slice(0..base).ok_or(Fault::Malformed)?;
            copy.slots(mc).copy_from(mc, frames);
            frames.fill(mc, Value::VOID);
            run.iter().for_each(|record| record.set_segment(mc, Some(copy)));
        }
        task.set_segment(mc, None);
        Ok(Some(segment))
    }

    /// A segment for a coroutine `from` resumes to run on: its spare, if that's free and big
    /// enough, or a new one.
    fn free_segment(&self, from: Gc<'gc, Task>) -> Result<Gc<'gc, Segment>, Fault> {
        let mc = self.mc();
        if let Some(spare) = from.spare(mc)
            && from.spare_base(mc) == 0
            && spare.len(mc) >= FIRST_SEGMENT
            && spare != self.segments.stack.segment(mc)
        {
            from.set_spare(mc, None);
            return Ok(spare);
        }
        Ok(Segment::new(mc, FIRST_SEGMENT)?)
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
