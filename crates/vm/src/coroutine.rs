//! Asymmetric coroutines modeled after Lua. Each coroutine is represented as a [`Task`] with its own
//! stack, executed via `co/resume` until it yields, terminates, or encounters an uncaught error.
//! Coroutines maintain independent continuation marks, prompts, and metacontinuations, preserving
//! delimited context across yields.
//!
//! Coroutine context switching is implemented as a stack cut (analogous to invoking a one-shot
//! continuation): the suspended task reifies its active frames into its continuation chain and
//! preserves its base offset, while the VM stack switches to the target task's segment to resume in
//! place without copying frames.
//!
//! Suspended coroutines require no stack headroom beyond their live frames. When a coroutine suspends
//! and another task runs, if its underlying segment is not referenced by any continuation, its live
//! frames are compacted into a tightly-sized segment and the original segment is recycled as the
//! active task's spare segment. Only the most recently suspended coroutine retains its full segment in
//! place, allowing generators that alternate execution with a consumer to switch without any frame
//! copying.
//!
//! The machine's root task is also structured as a coroutine; yielding from the root task suspends the
//! machine and returns control to the host.

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Segment, Value, WINDOW};
use ragwort_types::pair::Pairs;

use crate::passed::Passed;
use crate::machine::{Outer, Step, Then};
use crate::prompts;
use crate::segments::records;
use crate::objects::{Frames, FramesFields, Task, TaskFields};
use crate::{Fault, Outcome};

/// The initial capacity allocated for a coroutine's first stack segment: accommodates one frame window
/// plus 64 slots for immediate calls. Deeper calls trigger segment overflow and allocate larger
/// segments.
const FIRST_SEGMENT: usize = WINDOW + 64;

pub(crate) const PENDING: u32 = 0;
pub(crate) const RUNNING: u32 = 1;
pub(crate) const FINISHED: u32 = 2;
pub(crate) const FAILED: u32 = 3;

/// Creates a pending coroutine initialized to invoke procedure `body` upon its first resumption.
pub(crate) fn new<'gc>(mc: &Mutation<'gc>, body: Value<'gc>) -> Result<Gc<'gc, Task>, OutOfMemory> {
    task(mc, body, PENDING)
}

/// Creates the root task for a machine, initialized in the running state.
pub(crate) fn root<'gc>(mc: &Mutation<'gc>) -> Result<Gc<'gc, Task>, OutOfMemory> {
    task(mc, Value::FALSE, RUNNING)
}

fn task<'gc>(mc: &Mutation<'gc>, body: Value<'gc>, state: u32) -> Result<Gc<'gc, Task>, OutOfMemory> {
    let none = Value::FALSE;
    Task::new(mc, Value::VOID, none, Value::NIL, Value::NIL, Value::NIL, None, 0, body, none, none, none, none, None, 0, state)
}

pub(crate) fn of<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Option<Gc<'gc, Task>> {
    value.downcast::<Task>(mc)
}

/// Returns the currently active task in a machine rooted at `root` by traversing to the innermost
/// resumed coroutine.
pub(crate) fn current<'gc>(mc: &Mutation<'gc>, root: Gc<'gc, Task>) -> Gc<'gc, Task> {
    let mut task = root;
    while let Some(inner) = of(mc, task.resumed(mc)) {
        task = inner;
    }
    task
}

/// Assigns unreferenced `segment` as `task`'s spare segment if `task` does not already hold one.
fn give<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, segment: Gc<'gc, Segment>) {
    if task.spare(mc).is_none() {
        task.set_spare(mc, Some(segment));
        task.set_spare_base(mc, 0);
    }
}

impl<'gc> Outer<'_, 'gc> {
    /// Resumes coroutine `co` with arguments `args` (implementing `co/resume`), assuming the caller's
    /// continuation has already been saved to its chain.
    pub(crate) fn resume_coroutine(&mut self, co: Value<'gc>, args: Passed<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        if co.state(mc) != PENDING {
            return Err(Fault::NotPending);
        }
        // The values are taken off this task's stack before the stack moves to the coroutine's.
        let args = args.take(mc)?;
        let from = self.task();
        self.leave(from)?;
        if self.root.idle(mc) == Value::object(mc, co) {
            self.root.set_idle(mc, Value::FALSE);
        }
        from.set_resumed(mc, Value::object(mc, co));
        co.set_resumer(mc, Value::object(mc, from));
        co.set_state(mc, RUNNING);
        let body = co.body(mc);
        if body == Value::FALSE && co.segment(mc).is_some() {
            self.enter_task(co)?;
            return self.then(args.returned());
        }
        let segment = self.free_segment(from)?;
        self.segments.stack.switch(mc, segment);
        self.segments.task = co;
        if body == Value::FALSE {
            return self.then(args.returned());
        }
        co.set_body(mc, Value::FALSE);
        let args = self.repass(args)?;
        self.then(Then::Call(body, args))
    }

    /// Suspends the active coroutine (implementing `co/yield`), returning `yielded` to its resumer,
    /// assuming the coroutine's continuation is already preserved on its chain.
    pub(crate) fn yield_coroutine(&mut self, yielded: Passed<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let from = self.task();
        let Some(to) = of(mc, from.resumer(mc)) else {
            if !Pairs::new(mc).is_list(yielded.rest) {
                return Err(Fault::WrongType);
            }
            let yielded = yielded.to_list(mc)?;
            // A run that resumes without values resumes the yield with none.
            self.regs.set_values(mc, Value::NIL);
            return Ok(Some(Outcome::Yielded(yielded)));
        };
        // The values are taken off this task's stack before the stack moves back to the resumer's.
        let yielded = yielded.take(mc)?;
        self.leave(from)?;
        // Clear any cached spare segment so a suspended coroutine retains only segments holding live frames.
        from.set_spare(mc, None);
        from.set_state(mc, PENDING);
        from.set_resumer(mc, Value::FALSE);
        let last = of(mc, self.root.idle(mc)).filter(|&task| task != from);
        self.root.set_idle(mc, Value::object(mc, from));
        self.back(to)?;
        if let Some(task) = last
            && let Some(segment) = compact(mc, task)?
        {
            give(mc, to, segment);
        }
        self.then(yielded.returned())
    }

    /// Terminates the active coroutine with final status `state` (completed or failed) and switches back
    /// to its resumer `to`, releasing unheld stack segments.
    pub(crate) fn end(&mut self, task: Gc<'gc, Task>, state: u32, to: Gc<'gc, Task>) -> Result<(), Fault> {
        let mc = self.mc();
        let stack = &self.segments.stack;
        let base = stack.base();
        stack.set_top(base);
        // If base is 0, no continuation records hold frames on this segment, so the entire segment can be
        // reclaimed.
        let freed = (base == 0).then(|| stack.segment(mc));
        task.set_state(mc, state);
        task.set_resumer(mc, Value::FALSE);
        prompts::empty(mc, task);
        task.set_prompts(mc, Value::NIL);
        task.set_spare(mc, None);
        self.back(to)?;
        if let Some(segment) = freed {
            give(mc, to, segment);
        }
        Ok(())
    }

    /// Allocates a segment for coroutine resumption: reuses `from`'s spare segment if available and
    /// sufficiently sized, or allocates a new segment.
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

    /// Preserves the active task's base offset and compacts idle segments before switching away, since
    /// all live frames below base have been reified into its chain.
    fn leave(&mut self, task: Gc<'gc, Task>) -> Result<(), Fault> {
        let (mc, stack) = (self.mc(), &self.segments.stack);
        let base = stack.base();
        stack.set_top(base);
        task.set_segment(mc, Some(stack.segment(mc)));
        task.set_base(mc, u32::try_from(base).map_err(|_| Fault::Malformed)?);
        Ok(())
    }

    /// Switches execution context back to coroutine `to`, which originally resumed the active task.
    fn back(&mut self, to: Gc<'gc, Task>) -> Result<(), Fault> {
        to.set_resumed(self.mc(), Value::FALSE);
        self.enter_task(to)
    }

    /// Restores the stack segment and base pointer to where `task` suspended and sets it as the active
    /// running task.
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

/// Compacts a suspended task's frames into a tightly-sized segment if its continuation chain contains
/// all frames below base and no external continuation references them, freeing the original segment.
/// Only shallow stacks (within one frame window) are compacted to avoid repeated copying costs for
/// deep call stacks.
fn compact<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<Option<Gc<'gc, Segment>>, Fault> {
    let Some(segment) = task.segment(mc).filter(|_| task.state(mc) == PENDING) else { return Ok(None) };
    let (base, chain) = (task.base(mc) as usize, task.chain(mc));
    let Some(held) = held(mc, chain, segment, base).filter(|_| base <= WINDOW) else { return Ok(None) };
    if base > 0 {
        let copy = Segment::new(mc, base)?;
        let frames = segment.slots(mc).slice(0..base).ok_or(Fault::Malformed)?;
        copy.slots(mc).copy_from(mc, frames);
        frames.fill(mc, Value::VOID);
        held.iter().for_each(|record| record.set_segment(mc, Some(copy)));
    }
    task.set_segment(mc, None);
    Ok(Some(segment))
}

/// Returns the one-shot records at the head of `chain` that together hold all the frames of `segment` below `end`, without owning the segment. Returns `None` if the head of the chain is not such a run of records.
fn held<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>, segment: Gc<'gc, Segment>, mut end: usize) -> Option<Vec<Gc<'gc, Frames>>> {
    let mut held = Vec::new();
    let mut records = records(mc, chain);
    while end > 0 {
        let record = records.next()?;
        if record.segment(mc) != Some(segment) || !record.one_shot(mc) || record.owns(mc) || record.end(mc) as usize != end {
            return None;
        }
        held.push(record);
        end = record.start(mc) as usize;
    }
    Some(held)
}
