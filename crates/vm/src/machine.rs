
use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, Root, Segment, Slots, Stack, Value, WINDOW};
use ragwort_types::pair::Pairs;

use crate::args::Args;
use crate::frame::{self, CLOSURE, Link};
use crate::intrinsic::values;
use crate::objects::{BytecodeFields, Closure, ClosureFields, Condition, Continuation, KeywordProcedure, Native, NativeFields, Task, TaskFields};
use crate::run::{self, Exit, HostThen, Regs, bind};
use crate::segments::{CHUNK, Resume, Segments};
use crate::module::Deferred;
use crate::{Fault, Fuel, Request, coroutine, keyword, prompts};

#[cfg(test)]
#[path = "tests/machine.rs"]
mod tests;

/// The smallest segment a machine takes: room for a chunk and a frame above it.
pub const MIN_SEGMENT: usize = CHUNK + 2 * WINDOW;
/// The segment size to use when there's no reason to pick another.
pub const SEGMENT: usize = 1 << 14;

/// How a run ended.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome<'gc> {
    /// The task returned this.
    Done(Value<'gc>),
    /// It made enough that the step should end, and goes on with the next run.
    Paused,
    /// What was raised with no handler to take it, once the task's `dynamic-wind` `after`s
    /// have run: for a VM fault, a `Condition`.
    Raised(Value<'gc>),
    /// The task yielded these values, as one: `co/yield` in it, not in a coroutine it resumed.
    /// [`Machine::resume`] goes on with it.
    Yielded(Value<'gc>),
    /// A host function's call replied [`Reply::Defer`](crate::Reply::Defer) with this.
    /// [`Machine::reply`] goes on with what the call returns, or [`Machine::raise`] raises from
    /// it.
    Deferred(Deferred),
}

/// What the next run goes on from, if not where the last one paused.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Waiting {
    No,
    /// The task yielded.
    Yield,
    /// A host function deferred.
    Host,
    /// The host raised from where the task waits on it.
    Raise,
}

/// A task: a procedure call run on its own stack. It holds no brand, so it lives outside the
/// arena.
pub struct Machine {
    stack: Stack,
    task: Root<Task>,
    fp: usize,
    pc: usize,
    segment: usize,
    fuel: u64,
    finished: bool,
    waiting: Waiting,
}

impl Machine {
    /// A task that calls `procedure` with `args`, on segments of `segment` slots, at least
    /// [`MIN_SEGMENT`].
    pub fn new<'gc>(mc: &Mutation<'gc>, segment: usize, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<Self, Fault> {
        let segment = segment.max(MIN_SEGMENT);
        let mut stack = mc.stack(Segment::new(mc, segment)?)?;
        let task = coroutine::root(mc)?;
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID };
        Outer::new(mc, &mut stack, task, &mut regs, segment).start(procedure, args_of(mc, args)?)?;
        let mut machine = Machine { stack, task: Root::new(mc, task)?, fp: 0, pc: 0, segment, fuel: u64::MAX, finished: false, waiting: Waiting::No };
        machine.save(mc, task, &regs);
        Ok(machine)
    }

    /// Starts a new task in a machine whose last one finished, calling `procedure` with `args`
    /// on the stack it left, from where continuations it made hold no more of it, so a host
    /// that runs one call after another doesn't make a stack for each. Its fuel is as it was.
    /// Faults with [`Fault::NotPending`] if the last task hasn't finished.
    pub fn restart<'gc>(&mut self, mc: &Mutation<'gc>, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<(), Fault> {
        if !self.finished {
            return Err(Fault::NotPending);
        }
        let task = coroutine::root(mc)?;
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID };
        Outer::new(mc, &mut self.stack, task, &mut regs, self.segment).start(procedure, args_of(mc, args)?)?;
        (self.task, self.finished, self.waiting) = (Root::new(mc, task)?, false, Waiting::No);
        self.save(mc, task, &regs);
        Ok(())
    }

    /// Sets how much fuel the task has left in all, unlimited at first. Calls and jumps spend
    /// a unit each, as do intrinsics for each stretch of work they do. Once it runs out, the
    /// task is finished, with [`Fault::OutOfFuel`].
    pub fn set_fuel(&mut self, fuel: u64) {
        self.fuel = fuel;
    }

    pub fn fuel(&self) -> u64 {
        self.fuel
    }

    /// Runs until the task finishes, yields or its fuel runs out, or until it has made enough
    /// that the step should end so the collector can keep up, as [`Mutation::step_due`] says:
    /// then it pauses at its next call or jump, and the next run goes on from there. After a
    /// yield, it goes on as [`Machine::resume`] with no values does, and after a deferred host
    /// call, as [`Machine::reply`] with void. Running it again once it's finished faults with
    /// [`Fault::Finished`].
    pub fn run<'gc>(&mut self, mc: &Mutation<'gc>) -> Result<Outcome<'gc>, Fault> {
        if self.finished {
            return Err(Fault::Finished);
        }
        let mut task = coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena"));
        let mut regs = Regs { fp: self.fp, pc: self.pc, acc: task.acc(mc) };
        let mut fuel = Fuel { run: self.fuel, rest: 0 };
        let outcome = match self.drive(mc, &mut task, &mut regs, &mut fuel) {
            Ok(Outcome::Paused) if fuel.left() == 0 => Err(Fault::OutOfFuel),
            outcome => outcome,
        };
        self.fuel = fuel.left();
        self.finished = matches!(outcome, Ok(Outcome::Done(_) | Outcome::Raised(_)) | Err(Fault::OutOfFuel));
        self.waiting = match outcome {
            Ok(Outcome::Yielded(_)) => Waiting::Yield,
            Ok(Outcome::Deferred(_)) => Waiting::Host,
            _ => Waiting::No,
        };
        if self.finished {
            let state = if matches!(outcome, Ok(Outcome::Done(_))) { coroutine::FINISHED } else { coroutine::FAILED };
            self.task.get(mc).expect("a machine runs in its own arena").set_state(mc, state);
        }
        self.save(mc, task, &regs);
        outcome
    }

    /// Goes on with a task that yielded, as [`Machine::run`] does, with its `co/yield` returning
    /// `args`. Faults with [`Fault::NotPending`] if it isn't waiting on a yield.
    pub fn resume<'gc>(&mut self, mc: &Mutation<'gc>, args: &[Value<'gc>]) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Yield, values(mc, args.iter().copied())?)?;
        self.run(mc)
    }

    /// Goes on with a task whose host function deferred, as [`Machine::run`] does, with that
    /// returning `answer`. Faults with [`Fault::NotPending`] if
    /// it isn't waiting on one.
    pub fn reply<'gc>(&mut self, mc: &Mutation<'gc>, answer: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Host, answer)?;
        self.run(mc)
    }

    /// Goes on with a task waiting as [`Machine::reply`] takes, raising `raised` from what it
    /// waits on, as `raise` does.
    pub fn raise<'gc>(&mut self, mc: &Mutation<'gc>, raised: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Host, raised)?;
        self.waiting = Waiting::Raise;
        self.run(mc)
    }

    /// Gives the task `value`, for the next run, if it's waiting `on` that.
    fn answer<'gc>(&mut self, mc: &Mutation<'gc>, on: Waiting, value: Value<'gc>) -> Result<(), Fault> {
        if self.waiting != on {
            return Err(if self.finished { Fault::Finished } else { Fault::NotPending });
        }
        coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena")).set_acc(mc, value);
        Ok(())
    }

    /// Keeps what the next run needs where a collection finds it.
    fn save<'gc>(&mut self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, regs: &Regs<'gc>) {
        (self.fp, self.pc) = (regs.fp, regs.pc);
        task.set_acc(mc, regs.acc);
        let len = self.stack.segment(mc).len(mc);
        self.stack.set_top((regs.fp + WINDOW).min(len));
    }

    /// Runs the inner loop, and carries out what it stops for, until the task ends or the run's
    /// fuel runs out. `task` is the running one, which switching coroutines changes.
    fn drive<'gc>(&mut self, mc: &Mutation<'gc>, task: &mut Gc<'gc, Task>, regs: &mut Regs<'gc>, fuel: &mut Fuel) -> Result<Outcome<'gc>, Fault> {
        let waiting = std::mem::replace(&mut self.waiting, Waiting::No);
        if waiting != Waiting::No {
            let mut outer = Outer::new(mc, &mut self.stack, *task, regs, self.segment);
            let step = if waiting == Waiting::Raise { outer.raise(outer.regs.acc, false) } else { outer.resume() };
            *task = outer.task();
            if let Some(outcome) = step? {
                return Ok(outcome);
            }
        }
        let mut deferred = None;
        loop {
            let exit = run::exec(mc, &self.stack, *task, regs, fuel, &mut deferred);
            let mut outer = Outer::new(mc, &mut self.stack, *task, regs, self.segment);
            let step = outer.exit(exit, &mut deferred);
            *task = outer.task();
            if let Some(outcome) = step? {
                return Ok(outcome);
            }
            if mc.step_due() {
                return Ok(Outcome::Paused);
            }
        }
    }
}

fn args_of<'gc>(mc: &Mutation<'gc>, args: &[Value<'gc>]) -> Result<Args<'gc>, Fault> {
    Ok(match *args {
        [] => Args::none(),
        [a] => Args::one(a),
        [a, b] => Args::two(a, b),
        _ => Args::list(Pairs::new(mc).list(args)?),
    })
}

/// What a step of the outer loop leads to: going on, or the end of the run.
pub(crate) type Step<'gc> = Result<Option<Outcome<'gc>>, Fault>;

/// What a request leads to, once it has done what it does to the continuation.
pub(crate) enum Then<'gc> {
    /// A call of the procedure with the arguments, which returns to the current continuation.
    Call(Value<'gc>, Args<'gc>),
    /// The value, returned to the current continuation.
    Return(Value<'gc>),
    /// A resume of the coroutine with the arguments.
    Resume(Value<'gc>, Args<'gc>),
    /// The value, raised, and whether the raise goes on with what the handler returns.
    Raise(Value<'gc>, bool),
    /// The value, raised with no handler to take it, and whether the `after`s have run.
    Uncaught(Value<'gc>, bool),
    /// A yield of the value, as one, from the running coroutine.
    Yield(Value<'gc>),
}

/// The outer loop's state, between two stretches of the inner loop: the stack, and the
/// registers the inner loop goes on with.
pub(crate) struct Outer<'a, 'gc> {
    pub(crate) segments: Segments<'a, 'gc>,
    pub(crate) regs: &'a mut Regs<'gc>,
}

impl<'a, 'gc> Outer<'a, 'gc> {
    fn new(mc: &'a Mutation<'gc>, stack: &'a mut Stack, task: Gc<'gc, Task>, regs: &'a mut Regs<'gc>, size: usize) -> Self {
        Outer { segments: Segments { mc, stack, task, size }, regs }
    }

    pub(crate) fn mc(&self) -> &'a Mutation<'gc> {
        self.segments.mc
    }

    pub(crate) fn task(&self) -> Gc<'gc, Task> {
        self.segments.task
    }

    /// Carries out what the inner loop stopped for. A fault that isn't fatal is raised, as a
    /// `Condition`, as is one in calling the handler, which is then outside the handlers.
    fn exit(&mut self, exit: Exit<'gc>, deferred: &mut Option<Deferred>) -> Step<'gc> {
        let mut step = match exit {
            Exit::Paused => return Ok(Some(Outcome::Paused)),
            Exit::Fault(fault) => Err(fault),
            Exit::Overflow { callee, argc, rest } => self.overflow(callee, argc, rest).map(|()| None),
            Exit::Underflow => self.resume(),
            Exit::Call { base, argc, rest, tail } => self.call(base, argc, rest, tail),
            Exit::Request { base, args, request, spread, tail } => self.request(base, args, request, spread, tail),
            Exit::Host { base, tail, then } => {
                // Taken first, so it doesn't outlive a call `keep` fails.
                let deferred = deferred.take();
                self.keep(base, tail).and_then(|()| self.host_then(then, deferred))
            }
        };
        while let Err(fault) = step
            && !fault.is_fatal()
        {
            step = self.fault(fault);
        }
        step
    }

    /// Raises a condition for `fault`, in place of the frame that faulted.
    fn fault(&mut self, fault: Fault) -> Step<'gc> {
        let mc = self.mc();
        let raised = condition(mc, fault, Value::VOID, Value::NIL)?;
        if self.regs.fp > self.segments.stack.base()
            && let Ok(frame) = self.segments.frame(self.regs.fp)
            && let Ok(link) = frame::link_of(mc, frame)
        {
            let _ = self.segments.reify(self.regs.fp, link);
        }
        self.raise(raised, false)
    }

    /// Raises `obj`, as `raise` does, or `raise-continuable` if it's `continuable`.
    fn raise(&mut self, obj: Value<'gc>, continuable: bool) -> Step<'gc> {
        let then = self.raising(obj, continuable)?;
        self.then(then)
    }

    /// What `obj`, raised with no handler, leads to: the task's `after`s run, unless `unwound`
    /// says they have, and then a coroutine fails, and `obj` is raised again where it was
    /// resumed, and a machine's own task ends with it.
    fn uncaught(&mut self, obj: Value<'gc>, unwound: bool) -> Step<'gc> {
        let mc = self.mc();
        let task = self.task();
        if !unwound {
            let then = self.unwind_all(obj)?;
            return self.then(then);
        }
        let Some(to) = coroutine::of(mc, task.resumer(mc)) else { return Ok(Some(Outcome::Raised(obj))) };
        self.end(task, coroutine::FAILED, to)?;
        self.raise(obj, false)
    }

    /// Carries out `request` on the `args` registers from `base`, the last a list of more if
    /// it's a `spread`. They stay where they are, past what's kept.
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Step<'gc> {
        let mut args = Args::slots(self.registers(base, args)?, Value::NIL);
        if spread {
            args = args.spread_last(self.mc())?;
            if !request.takes(args.len(self.mc())?) {
                return Err(Fault::Arity);
            }
        }
        self.keep(base, tail)?;
        let then = request.run(self, args)?;
        self.then(then)
    }

    /// Carries out a call of something other than a closure, in register `base`, with the
    /// `argc` registers after it and the elements of `rest` as its arguments.
    fn call(&mut self, base: u8, argc: u8, rest: Value<'gc>, tail: bool) -> Step<'gc> {
        let slots = self.registers(base, argc + 1)?;
        let args = Args::slots(slots.slice(1..slots.len()).ok_or(Fault::Malformed)?, rest);
        self.keep(base, tail)?;
        self.then(Then::Call(slots.get(0), args))
    }

    /// The `n` registers of the current frame from `base`.
    fn registers(&self, base: u8, n: u8) -> Result<Slots<'gc>, Fault> {
        let (mc, at) = (self.mc(), self.regs.fp + usize::from(base));
        if usize::from(base) + usize::from(n) > WINDOW {
            return Err(Fault::Malformed);
        }
        self.segments.stack.segment(mc).slots(mc).slice(at..at + usize::from(n)).ok_or(Fault::Malformed)
    }

    pub(crate) fn then(&mut self, then: Then<'gc>) -> Step<'gc> {
        match then {
            Then::Call(procedure, args) => self.apply(procedure, args),
            Then::Return(value) => {
                self.regs.acc = value;
                self.resume()
            }
            Then::Resume(co, args) => self.resume_coroutine(co, args),
            Then::Raise(obj, continuable) => self.raise(obj, continuable),
            Then::Uncaught(obj, unwound) => self.uncaught(obj, unwound),
            Then::Yield(values) => self.yield_coroutine(values),
        }
    }

    /// Calls `procedure` with `args`. A closure gets a frame at the bottom of the stack; a
    /// continuation goes on, and gets the values, once the winders it leaves and enters have
    /// run.
    fn apply(&mut self, procedure: Value<'gc>, args: Args<'gc>) -> Step<'gc> {
        if let Some(k) = procedure.downcast::<Continuation>(self.mc()) {
            let then = self.go_to(k, args)?;
            return self.then(then);
        }
        if let Some(f) = procedure.downcast::<KeywordProcedure>(self.mc()) {
            let then = keyword::positional(self.mc(), f, args)?;
            return self.then(then);
        }
        self.start(procedure, args)?;
        Ok(None)
    }

    /// Raises or defers from a host function's call, whose continuation is the current one.
    fn host_then(&mut self, then: HostThen<'gc>, deferred: Option<Deferred>) -> Step<'gc> {
        match then {
            HostThen::Raise(raised) => self.raise(raised, false),
            HostThen::Defer => {
                self.regs.acc = Value::VOID;
                Ok(Some(Outcome::Deferred(deferred.ok_or(Fault::Malformed)?)))
            }
        }
    }

    /// Hands the frames under the continuation of the current call or request to the chain. A
    /// tail call's continuation is the current frame's caller; any other's is the instruction
    /// after it, whose `base` must be past the frame's link, as a call's is.
    pub(crate) fn keep(&mut self, base: u8, tail: bool) -> Result<(), Fault> {
        let (mc, fp) = (self.mc(), self.regs.fp);
        let frame = self.segments.frame(fp)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        let at = frame::link_slot_of(mc, closure)?;
        let (end, link) = if tail {
            (fp, Link::of(frame.get(at)).ok_or(Fault::Malformed)?)
        } else if base > at {
            (fp + usize::from(base), Link::to(self.regs.pc, base))
        } else {
            return Err(Fault::Malformed);
        };
        self.segments.reify(end, link)
    }

    /// Makes the frame of a call that doesn't fit, with its caller's, on another segment.
    fn overflow(&mut self, callee: usize, argc: u8, rest: Value<'gc>) -> Result<(), Fault> {
        let base = callee - self.regs.fp;
        let link = Link::to(self.regs.pc, u8::try_from(base).map_err(|_| Fault::Malformed)?);
        let fp = self.segments.overflow(self.regs.fp, callee + 1 + usize::from(argc), base + WINDOW)?;
        self.regs.fp = fp;
        self.enter(fp + base, argc, rest, link)
    }

    /// Goes back to the continuation with the value in the accumulator: the records under the
    /// stack, then the prompts'. If none is left, the task is done, and that's its value: a
    /// coroutine's goes back to what resumed it. A [`Native`] record goes on as its kind says.
    pub(crate) fn resume(&mut self) -> Step<'gc> {
        let mc = self.mc();
        loop {
            let task = self.task();
            if let Some(native) = task.chain(mc).downcast::<Native>(mc) {
                task.set_chain(mc, native.next(mc));
                task.set_attachments(mc, native.attachments(mc));
                match self.native(native)? {
                    Then::Return(value) => {
                        self.regs.acc = value;
                        continue;
                    }
                    then => return self.then(then),
                }
            }
            if let Some(Resume { fp, pc }) = self.segments.underflow()? {
                (self.regs.fp, self.regs.pc) = (fp, pc);
                return Ok(None);
            }
            let task = self.task();
            if prompts::pop(mc, task)? {
                continue;
            }
            let Some(to) = coroutine::of(mc, task.resumer(mc)) else { return Ok(Some(Outcome::Done(self.regs.acc))) };
            self.end(task, coroutine::FINISHED, to)?;
        }
    }

    /// Calls the closure `procedure` with `args` in a frame at the bottom of the stack, which
    /// binding takes those past its held ones from.
    fn start(&mut self, procedure: Value<'gc>, mut args: Args<'gc>) -> Result<(), Fault> {
        let mc = self.mc();
        let fp = if self.segments.fits(0) {
            self.segments.stack.base()
        } else {
            args = args.detach(mc)?;
            self.segments.bottom(0)?
        };
        let (stack, frame) = (&*self.segments.stack, self.segments.frame(fp)?);
        let argc = args.write(mc, stack, frame, fp)?;
        frame.set(CLOSURE, procedure);
        self.enter(fp, argc, args.rest, Link::BOTTOM)
    }

    /// Enters the closure in the frame at `fp`, with `argc` arguments and the list `rest` after
    /// them, and `link`.
    fn enter(&mut self, fp: usize, argc: u8, rest: Value<'gc>, link: Link) -> Result<(), Fault> {
        let mc = self.mc();
        let frame = self.segments.frame(fp)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::NotProcedure)?;
        // The outer loop sees for itself when the step is due.
        let mut fuel = Fuel { run: 0, rest: 0 };
        bind(mc, frame, closure.code(mc).ok_or(Fault::Malformed)?.arity(mc), argc, rest, &mut fuel)?;
        frame::set_link(mc, frame, link)?;
        (self.regs.fp, self.regs.pc) = (fp, 0);
        Ok(())
    }
}

/// An error object for `fault`.
pub(crate) fn condition<'gc>(mc: &Mutation<'gc>, fault: Fault, message: Value<'gc>, irritants: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Value::object(mc, Condition::new(mc, mc.frozen(fault)?, message, irritants)?))
}
