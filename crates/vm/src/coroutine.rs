//! Asymmetric coroutines modeled after Lua. Each coroutine is represented as a [`Task`] with its own
//! stack, executed via `co/resume` until it yields, terminates, or encounters an uncaught error.
//! Coroutines maintain independent continuation marks, prompts, and metacontinuations, preserving
//! delimited context across yields.
//!
//! A switch between coroutines moves the VM stack to the other task's segment. The task that switches
//! away is parked. It records the frame and the instruction where it resumes, and its frames stay in
//! place on its segment. When values are returned to it, it resumes there, and nothing is copied or
//! allocated. Its frames are saved to its continuation chain only if something else happens to the
//! task first, such as an error raised into it. See [`Outer::park`].
//!
//! Suspended coroutines require no stack headroom beyond their live frames. When a coroutine suspends
//! and another task runs, if its underlying segment is not referenced by any continuation, its live
//! frames are compacted into a tightly-sized segment and the original segment is recycled as the
//! active task's spare segment. A few suspended coroutines keep their segment, so coroutines that run
//! in turn switch without any frame copying. See [`idle`].
//!
//! The machine's root task is also structured as a coroutine; yielding from the root task suspends the
//! machine and returns control to the host.

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Segment, Stack, Value, WINDOW};
use ragwort_types::pair::Pairs;
use ragwort_types::vector::{Vector, Vectors};

use crate::passed::Passed;
use crate::machine::{Outer, Step, Then};
use crate::prompts;
use crate::segments::records;
use crate::frame::Link;
use crate::objects::{Frames, FramesFields, Task, TaskFields};
use crate::{Fault, Outcome};

/// The initial capacity allocated for a coroutine's first stack segment: accommodates one frame window
/// plus 64 slots for immediate calls. Deeper calls trigger segment overflow and allocate larger
/// segments.
const FIRST_SEGMENT: usize = WINDOW + 64;

/// The maximum number of suspended coroutines of a machine that keep the stack segment they ran on. See [`idle`].
const IDLE: usize = 4;

pub(crate) const PENDING: u32 = 0;
pub(crate) const RUNNING: u32 = 1;
pub(crate) const DEAD: u32 = 2;
pub(crate) const FAILED: u32 = 3;
/// The state of a coroutine while `co/close` or `co/reset` runs its `after` winders. It counts as running everywhere, except that it cannot yield.
pub(crate) const CLOSING: u32 = 4;

/// The maximum number of frame slots below the parked frame that a parked task leaves live on its
/// stack. See [`Outer::park`].
pub(crate) const PARKED: usize = WINDOW;

/// Flag bit in a task's `park_base`, above the register number. It is set for a task parked by
/// `co/try-resume`.
///
/// Such a task has a guard record on its chain. The record was pushed after the task parked, so it is
/// above the parked frames. Values returned to the task pass through the record first. The parked
/// frames are never saved to the chain, because the guard catches every value raised into the task.
pub(crate) const TRIED: u32 = 1 << 8;

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
    Task::new(mc, Value::VOID, none, Value::NULL, Value::NULL, Value::NULL, None, 0, body, none, none, none, none, None, 0, state, 0, 0, 0)
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
    /// frames are parked or its continuation has been saved to its chain.
    pub(crate) fn resume_coroutine(&mut self, co: Value<'gc>, args: Passed<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        if co.state(mc) != PENDING {
            return Err(Fault::NotPending);
        }
        // The values are taken off this task's stack before the stack moves to the coroutine's.
        let args = args.take(mc)?;
        let body = self.switch_to(co, RUNNING)?;
        if body == Value::FALSE {
            return self.returned(args);
        }
        let args = self.repass(args)?;
        self.then(Then::Call(body, args))
    }

    /// Resumes coroutine `co` by raising `raised` inside it (implementing `co/resume-error`). The
    /// `co/yield` it is suspended in raises the value instead of returning.
    ///
    /// A handler or guard in the coroutine can catch the value, and the coroutine then continues as
    /// after any resume. If nothing catches the value, the coroutine fails and the value is raised
    /// again in the resuming task, as when a resumed coroutine fails by itself. A coroutine that has
    /// not started fails without running its body.
    pub(crate) fn resume_error(&mut self, co: Value<'gc>, raised: Value<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        if co.state(mc) != PENDING {
            return Err(Fault::NotPending);
        }
        self.switch_to(co, RUNNING)?;
        // The value is raised on top of the coroutine's frames, so they are saved first.
        self.settle()?;
        self.then(Then::Raise(raised, false))
    }

    /// Closes coroutine `co` (implementing `co/close`). If `renew` is a procedure, the coroutine is then
    /// made pending again with `renew` as its body (implementing `co/reset`). `renew` is `#f` for a
    /// plain close.
    ///
    /// - A dead or failed coroutine has nothing to close.
    /// - A suspended coroutine with no winders is discarded. Nothing runs.
    /// - A suspended coroutine with winders becomes the running task, in state [`CLOSING`], until its
    ///   `after` thunks have run. They run innermost first, in the coroutine's own context. See
    ///   [`Kind::Closed`](crate::wind::Kind::Closed).
    ///
    /// An `after` thunk that raises with no handler fails the coroutine, and the value is raised in the
    /// task that closed it. A reset still installs the new body, so the coroutine can be used again.
    ///
    /// Fails with [`Fault::NotPending`] for a coroutine that is running or closing.
    pub(crate) fn close_coroutine(&mut self, co: Value<'gc>, renew: Value<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let co = of(mc, co).ok_or(Fault::WrongType)?;
        match co.state(mc) {
            PENDING => {
                if !prompts::winds(mc, co, None)?.is_empty() {
                    self.switch_to(co, CLOSING)?;
                    // The `after` thunks run on top of the coroutine's frames, so they are saved first.
                    self.settle()?;
                    // The new body of a reset is stored in `body` until the close ends. A started coroutine does not use that field. The new body is installed when the close ends, whether the `after` thunks return or one of them fails.
                    co.set_body(mc, renew);
                    let then = self.unwind_closing()?;
                    return self.then(then);
                }
                self.discard(co)?;
                co.set_state(mc, DEAD);
            }
            DEAD | FAILED => {}
            _ => return Err(Fault::NotPending),
        }
        self.then(closed(mc, co, renew))
    }

    /// Makes the suspended coroutine `co` the running task, in `state`, on its own stack. The caller's
    /// frames must already be parked, or its continuation saved to its chain.
    ///
    /// Returns the body of a coroutine that has not started. The caller then calls the body or drops
    /// it. Returns `#f` for a coroutine that has started.
    fn switch_to(&mut self, co: Gc<'gc, Task>, state: u32) -> Result<Value<'gc>, Fault> {
        let mc = self.mc();
        let from = self.task();
        leave(mc, self.segments.stack, from)?;
        resumed(mc, from, co, state);
        let body = co.body(mc);
        if body == Value::FALSE && co.segment(mc).is_some() {
            self.enter_task(co)?;
            return Ok(body);
        }
        let segment = self.free_segment(from)?;
        self.segments.stack.switch(mc, segment);
        self.segments.task = co;
        co.set_body(mc, Value::FALSE);
        Ok(body)
    }

    /// Drops everything the suspended coroutine `task` holds, without running anything: its body, its
    /// continuation, its marks, its winders and its prompts. Its stack segment becomes the running
    /// task's spare segment if nothing else holds the frames on it. [`compact`] makes the same check.
    fn discard(&mut self, task: Gc<'gc, Task>) -> Result<(), Fault> {
        let mc = self.mc();
        unlist(mc, self.root, task);
        if let Some(segment) = task.segment(mc) {
            let base = task.base(mc) as usize;
            if held(mc, task.chain(mc), segment, base).is_some() {
                // Parked frames lie above `base`. They are dropped with the rest.
                let top = parked_top(mc, task).unwrap_or(base);
                segment.slots(mc).slice(0..top).ok_or(Fault::Malformed)?.fill(mc, Value::VOID);
                give(mc, self.task(), segment);
            }
            task.set_segment(mc, None);
            task.set_base(mc, 0);
        }
        task.set_park_base(mc, 0);
        prompts::empty(mc, task);
        task.set_prompts(mc, Value::NULL);
        task.set_spare(mc, None);
        task.set_body(mc, Value::FALSE);
        Ok(())
    }

    /// Suspends the active coroutine (implementing `co/yield`), returning `yielded` to its resumer,
    /// assuming the coroutine's frames are parked or its continuation is preserved on its chain.
    pub(crate) fn yield_coroutine(&mut self, yielded: Passed<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let from = self.task();
        // A coroutine that is being closed runs only to unwind. The task that closed it is not waiting for a yield.
        if from.state(mc) == CLOSING {
            return Err(Fault::NotPending);
        }
        let Some(to) = of(mc, from.resumer(mc)) else {
            if !Pairs::new(mc).is_list(yielded.rest) {
                return Err(Fault::WrongType);
            }
            let yielded = yielded.to_list(mc)?;
            // If the next `Machine::run` resumes the machine without values, the yield returns no values.
            self.regs.set_values(mc, Value::NULL);
            return Ok(Some(Outcome::Yielded(yielded)));
        };
        // The values are taken off this task's stack before the stack moves back to the resumer's.
        let yielded = yielded.take(mc)?;
        leave(mc, self.segments.stack, from)?;
        suspended(mc, from, to);
        let evicted = idle(mc, self.root, from)?;
        self.enter_task(to)?;
        if let Some(task) = evicted
            && let Some(segment) = compact(mc, task)?
        {
            give(mc, to, segment);
        }
        self.returned(yielded)
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
        let freed = if base == 0 {
            Some(stack.segment(mc))
        } else {
            None
        };
        task.set_state(mc, state);
        task.set_resumer(mc, Value::FALSE);
        prompts::empty(mc, task);
        task.set_prompts(mc, Value::NULL);
        task.set_spare(mc, None);
        // A task that has ended has no frames, so it records no segment.
        task.set_segment(mc, None);
        unlist(mc, self.root, task);
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
        self.segments.task = task;
        Ok(())
    }
}

/// Records the position of the running task `task` on `stack`, before the stack moves to another
/// task. All frames of `task` below the base of the stack are already in its chain.
pub(crate) fn leave<'gc>(mc: &Mutation<'gc>, stack: &Stack, task: Gc<'gc, Task>) -> Result<(), Fault> {
    let base = stack.base();
    // The frames of a parked task stay live above `base`, up to the register of its request.
    stack.set_top(parked_top(mc, task).unwrap_or(base));
    // The `segment` field is written only when it changes. A task that keeps returning to the same segment skips the write.
    let segment = stack.segment(mc);
    if task.segment(mc) != Some(segment) {
        task.set_segment(mc, Some(segment));
    }
    task.set_base(mc, u32::try_from(base).map_err(|_| Fault::Malformed)?);
    Ok(())
}

/// Marks `co` as running in `state`, resumed by `from`.
pub(crate) fn resumed<'gc>(mc: &Mutation<'gc>, from: Gc<'gc, Task>, co: Gc<'gc, Task>, state: u32) {
    from.set_resumed(mc, Value::object(mc, co));
    co.set_resumer(mc, Value::object(mc, from));
    co.set_state(mc, state);
}

/// Marks `from` as suspended. `to` is the task that resumed `from`, and it runs next.
pub(crate) fn suspended<'gc>(mc: &Mutation<'gc>, from: Gc<'gc, Task>, to: Gc<'gc, Task>) {
    // Clear any cached spare segment so a suspended coroutine retains only segments holding live frames.
    if from.spare(mc).is_some() {
        from.set_spare(mc, None);
    }
    from.set_state(mc, PENDING);
    from.set_resumer(mc, Value::FALSE);
    to.set_resumed(mc, Value::FALSE);
}

/// Returns the frame that parks for a request, and the link where that frame resumes. The link holds
/// the instruction to resume at and the register of the pending request or call. The frame's
/// registers below that register stay live. The request is at register `base` of the frame at `fp`,
/// and `pc` is that frame's next instruction.
///
/// `caller` is the frame's own link if the request is in tail position, and `None` otherwise. A request
/// in tail position returns its result to the frame's caller. So the frame is dropped, as a return
/// would drop it, and the caller is the frame that parks.
///
/// Returns `None` in two cases, in which the frames have to be saved instead. The first is a bottom
/// frame, because its caller is on the chain. The second is a frame that was entered with marks,
/// because its marks and handlers stay in effect until the request is over.
pub(crate) fn place(fp: usize, pc: usize, base: u8, caller: Option<Link>) -> Option<(usize, Link)> {
    let Some(link) = caller else { return Some((fp, Link::to(pc, base))) };
    if link.is_bottom() || link.marks {
        return None;
    }
    Some((fp.checked_sub(usize::from(link.base))?, Link::to(link.pc, link.base)))
}

/// Records that `task` is parked in the frame at `fp` and resumes at the link `at`. `tried` is set for
/// `co/try-resume`. See [`TRIED`]. Returns `false` and records nothing if `fp` or the instruction
/// index does not fit in the task's 32-bit fields.
pub(crate) fn park<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, fp: usize, at: Link, tried: bool) -> bool {
    let (Ok(fp), Ok(pc)) = (u32::try_from(fp), u32::try_from(at.pc)) else { return false };
    task.set_park_fp(mc, fp);
    task.set_park_pc(mc, pc);
    task.set_park_base(mc, u32::from(at.base) | if tried {
        TRIED
    } else {
        0
    });
    true
}

/// Returns whether `task` switched away at a request without saving its frames to its chain. See
/// [`Outer::park`].
pub(crate) fn is_parked<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> bool {
    task.park_base(mc) != 0
}

/// Returns the slot where the parked frames of `task` end, or `None` if it is not parked.
pub(crate) fn parked_top<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Option<usize> {
    let park = task.park_base(mc);
    if park == 0 {
        None
    } else {
        Some((task.park_fp(mc) + (park & 0xFF)) as usize)
    }
}

/// Saves the parked frames of the suspended task `task` to its chain. The record is the same as the
/// record [`Outer::keep`] would have pushed when the task switched away. This is needed before code
/// reads the frames of a suspended task through its chain, as [`compact`] does.
pub(crate) fn unpark<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<(), Fault> {
    // This function is for suspended coroutines only. A task parked by `co/try-resume` is still running, so it stays parked.
    if !is_parked(mc, task) || task.park_base(mc) & TRIED != 0 {
        return Ok(());
    }
    let segment = task.segment(mc).ok_or(Fault::Malformed)?;
    let base = task.park_base(mc);
    let end = task.park_fp(mc).checked_add(base).ok_or(Fault::Malformed)?;
    let link = Link::to(task.park_pc(mc) as usize, base as u8).value().ok_or(Fault::Malformed)?;
    let record = Frames::new(mc, Some(segment), task.base(mc), end, link, task.attachments(mc), true, false, task.chain(mc))?;
    task.set_chain(mc, Value::object(mc, record));
    task.set_base(mc, end);
    task.set_park_base(mc, 0);
    Ok(())
}

/// Returns the action that completes a `co/close` or `co/reset` of `task`. `task` must have ended and
/// hold nothing. For a close, `renew` is `#f` and the action returns void. A reset first makes `task`
/// pending again with the procedure `renew` as its body, and then returns the coroutine.
pub(crate) fn closed<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, renew: Value<'gc>) -> Then<'gc> {
    if renew == Value::FALSE {
        return Then::Return(Value::VOID);
    }
    reset(mc, task, renew);
    Then::Return(Value::object(mc, task))
}

/// Makes `task`, which has ended and holds nothing, a pending coroutine again with the procedure `body`
/// as its body.
pub(crate) fn reset<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, body: Value<'gc>) {
    task.set_body(mc, body);
    task.set_acc(mc, Value::VOID);
    task.set_values(mc, Value::NULL);
    task.set_state(mc, PENDING);
}

/// Returns whether `task` is among the idle coroutines of the machine whose root task is `root`. See
/// [`idle`].
fn listed<'gc>(mc: &Mutation<'gc>, root: Gc<'gc, Task>, task: Gc<'gc, Task>) -> bool {
    let Some(list) = Vector::of(root.idle(mc)) else { return false };
    let (items, task) = (list.items(mc), Value::object(mc, task));
    for at in 0..items.len() {
        if items.get(at) == task {
            return true;
        }
    }
    false
}

/// Adds `from`, which is suspending, to the idle list of the machine whose root task is `root`.
/// Returns the coroutine that was evicted from the list to make room, if any. The caller compacts
/// the evicted coroutine.
///
/// An idle coroutine keeps its frames on the segment it ran on, so resuming it copies nothing. The
/// list limits the number of such coroutines to [`IDLE`]. The list is a vector in the `idle` field of
/// `root`, newest first. It is allocated when the first coroutine is added.
///
/// - A coroutine that is already in the list keeps its position. So a few coroutines that run in
///   turn all stay in the list, and none of them is copied out and back on each switch.
/// - A coroutine that is not in the list is inserted first. If the list is full, the oldest entry is
///   evicted.
/// - A coroutine that ends is removed from the list. See [`unlist`].
///
/// The list refers to tasks and does not own them in any other way. A coroutine that several machines
/// resume in turn can be in the list of each machine. That is safe, because [`compact`] checks the
/// state of the task it is given.
fn idle<'gc>(mc: &Mutation<'gc>, root: Gc<'gc, Task>, from: Gc<'gc, Task>) -> Result<Option<Gc<'gc, Task>>, OutOfMemory> {
    if listed(mc, root, from) {
        return Ok(None);
    }
    let list = match Vector::of(root.idle(mc)) {
        Some(list) => list,
        None => {
            let list = Vectors::new(mc).make(IDLE, Value::FALSE)?;
            root.set_idle(mc, list.value(mc));
            list
        }
    };
    let items = list.items(mc);
    // The new entry takes position 0. The entries before the first free position move down by one. If no position is free, the last entry is evicted.
    let mut free = items.len().saturating_sub(1);
    for at in 0..items.len() {
        if of(mc, items.get(at)).is_none() {
            free = at;
            break;
        }
    }
    let evicted = of(mc, items.get(free));
    for at in (0..free).rev() {
        items.set(mc, at + 1, items.get(at));
    }
    items.set(mc, 0, Value::object(mc, from));
    Ok(evicted)
}

/// Removes `task` from the idle list of `root`. `task` no longer keeps frames on a segment. See [`idle`].
fn unlist<'gc>(mc: &Mutation<'gc>, root: Gc<'gc, Task>, task: Gc<'gc, Task>) {
    let Some(list) = Vector::of(root.idle(mc)) else { return };
    let (items, task) = (list.items(mc), Value::object(mc, task));
    for at in 0..items.len() {
        if items.get(at) == task {
            items.set(mc, at, Value::FALSE);
        }
    }
}

/// Compacts a suspended task's frames into a tightly-sized segment if its continuation chain contains
/// all frames below base and no external continuation references them, freeing the original segment.
/// Only shallow stacks (within one frame window) are compacted to avoid repeated copying costs for
/// deep call stacks.
fn compact<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<Option<Gc<'gc, Segment>>, Fault> {
    let Some(segment) = task.segment(mc).filter(|_| task.state(mc) == PENDING) else { return Ok(None) };
    unpark(mc, task)?;
    let (base, chain) = (task.base(mc) as usize, task.chain(mc));
    let Some(count) = held(mc, chain, segment, base).filter(|_| base <= WINDOW) else { return Ok(None) };
    if base > 0 {
        let frames = segment.slots(mc).slice(0..base).ok_or(Fault::Malformed)?;
        let copy = Segment::holding(mc, frames)?;
        frames.fill(mc, Value::VOID);
        for record in records(mc, chain).take(count) {
            record.set_segment(mc, Some(copy));
        }
    }
    task.set_segment(mc, None);
    Ok(Some(segment))
}

/// Counts the one-shot records at the head of `chain` that together hold all the frames of `segment` below `end`, without owning the segment. Returns `None` if the head of the chain is not such a run of records. The count lets the caller walk the same records again, so nothing is allocated to remember them.
fn held<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>, segment: Gc<'gc, Segment>, mut end: usize) -> Option<usize> {
    let mut count = 0;
    let mut records = records(mc, chain);
    while end > 0 {
        let record = records.next()?;
        if record.segment(mc) != Some(segment) || !record.one_shot(mc) || record.owns(mc) || record.end(mc) as usize != end {
            return None;
        }
        count += 1;
        end = record.start(mc) as usize;
    }
    Some(count)
}
