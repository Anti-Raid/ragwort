
use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, Root, Segment, Slots, Stack, Value, WINDOW};
use ragwort_types::pair::Pairs;

use crate::args::Args;
use crate::frame::{self, CLOSURE, Link};
use crate::intrinsic::values;
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields, Continuation, KeywordProcedure, Native, NativeFields, Task, TaskFields};
use crate::run::{self, Exit, HostThen, Regs, bind};
use crate::segments::{CHUNK, Resume, Segments};
use crate::module::Deferred;
use crate::report::{self, Failure, Origin};
use crate::{Fault, Fuel, Request, coroutine, keyword, prompts};

#[cfg(test)]
#[path = "tests/machine.rs"]
mod tests;

/// The minimum stack segment capacity required by a machine: allocates enough space for a
/// continuation chunk (`CHUNK`) and two frame windows (`2 * WINDOW`).
pub const MIN_SEGMENT: usize = CHUNK + 2 * WINDOW;
/// The default stack segment capacity (16,384 slots), used when no custom segment size is
/// specified.
pub const SEGMENT: usize = 1 << 14;

/// The outcome of executing a VM task run.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome<'gc> {
    /// The task completed successfully and produced this return value.
    Done(Value<'gc>),
    /// The task paused because a GC step became due (or fuel was exhausted); execution can resume in a
    /// subsequent run.
    Paused,
    /// An unhandled exception or condition raised by the task, returned after executing all intervening
    /// `dynamic-wind` `after` thunks. For VM faults, this contains a `Condition` object.
    Raised(Value<'gc>),
    /// The root task yielded these values directly via `co/yield` (rather than an inner resumed
    /// coroutine). Can be resumed by calling [`Machine::resume`].
    Yielded(Value<'gc>),
    /// A host function returned [`Reply::Defer`](crate::Reply::Defer), suspending execution. Resumed by
    /// calling [`Machine::reply`] with the result or [`Machine::raise`] to raise an exception at the
    /// call site.
    Deferred(Deferred),
}

/// Tracks the state from which the next execution run should resume if the previous run did not
/// pause normally.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Waiting {
    No,
    /// The task suspended via a yield operation.
    Yield,
    /// The task suspended because a host function deferred completion.
    Host,
    /// The host requested that an exception be raised at the point where the task suspended.
    Raise,
}

/// An execution machine for running Scheme tasks on a segmented stack. Holds no GC lifetime
/// parameters, allowing it to exist outside the garbage-collected arena.
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
    /// Creates a new machine initialized to call `procedure` with `args`, allocating stack segments of
    /// at least `MIN_SEGMENT` slots (or `segment` if larger).
    pub fn new<'gc>(mc: &Mutation<'gc>, segment: usize, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<Self, Fault> {
        let segment = segment.max(MIN_SEGMENT);
        let mut stack = mc.stack(Segment::new(mc, segment)?)?;
        let task = coroutine::root(mc)?;
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID, code: None };
        Outer::new(mc, &mut stack, task, task, &mut regs, segment).start(procedure, args_of(mc, args)?)?;
        let mut machine = Machine { stack, task: Root::new(mc, task)?, fp: 0, pc: 0, segment, fuel: u64::MAX, finished: false, waiting: Waiting::No };
        machine.save(mc, task, &regs);
        Ok(machine)
    }

    /// Restarts a completed machine with a new procedure call and arguments, reusing the existing stack
    /// above any retained continuation frames to avoid reallocating stack segments across sequential
    /// runs. Preserves remaining fuel. Returns `Err(Fault::NotPending)` if the previous task has not
    /// finished.
    pub fn restart<'gc>(&mut self, mc: &Mutation<'gc>, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<(), Fault> {
        if !self.finished {
            return Err(Fault::NotPending);
        }
        let task = coroutine::root(mc)?;
        let last = self.task.get(mc).expect("a machine runs in its own arena");
        task.set_idle(mc, last.idle(mc));
        task.set_none(mc, last.none(mc));
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID, code: None };
        Outer::new(mc, &mut self.stack, task, task, &mut regs, self.segment).start(procedure, args_of(mc, args)?)?;
        (self.task, self.finished, self.waiting) = (Root::new(mc, task)?, false, Waiting::No);
        self.save(mc, task, &regs);
        Ok(())
    }

    /// Sets the total execution fuel available to the task. Each call, jump, and intrinsic execution
    /// unit consumes one unit of fuel; exhausting fuel terminates the task with [`Fault::OutOfFuel`].
    pub fn set_fuel(&mut self, fuel: u64) {
        self.fuel = fuel;
    }

    pub fn fuel(&self) -> u64 {
        self.fuel
    }

    /// Executes the task until it finishes, yields, exhausts its fuel, or pauses because a GC collection
    /// step is due ([`Mutation::step_due`]). If previously paused on a yield or a deferred host call, it
    /// automatically resumes (with an empty value list or void, respectively). Returns
    /// `Err(Fault::Finished)` if called on an already completed machine.
    pub fn run<'gc>(&mut self, mc: &Mutation<'gc>) -> Result<Outcome<'gc>, Fault> {
        if self.finished {
            return Err(Fault::Finished);
        }
        let mut task = coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena"));
        let mut regs = Regs { fp: self.fp, pc: self.pc, acc: task.acc(mc), code: None };
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

    /// Resumes a machine that suspended via `co/yield`, passing `args` as the return value of the yield
    /// expression. Returns `Err(Fault::NotPending)` if the machine is not waiting on a yield.
    pub fn resume<'gc>(&mut self, mc: &Mutation<'gc>, args: &[Value<'gc>]) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Yield, values(mc, args.iter().copied())?)?;
        self.run(mc)
    }

    /// Resumes a machine that suspended on a deferred host function call, supplying `answer` as the host
    /// function's return value. Returns `Err(Fault::NotPending)` if the machine is not waiting on a
    /// deferred host call.
    pub fn reply<'gc>(&mut self, mc: &Mutation<'gc>, answer: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Host, answer)?;
        self.run(mc)
    }

    /// Resumes a machine waiting on a deferred host function call by raising `raised` as an exception at
    /// the point of suspension.
    pub fn raise<'gc>(&mut self, mc: &Mutation<'gc>, raised: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        self.answer(mc, Waiting::Host, raised)?;
        self.waiting = Waiting::Raise;
        self.run(mc)
    }

    /// Delivers `value` to the suspended task if it is currently waiting on `on`, preparing it to resume
    /// on the next run.
    fn answer<'gc>(&mut self, mc: &Mutation<'gc>, on: Waiting, value: Value<'gc>) -> Result<(), Fault> {
        if self.waiting != on {
            return Err(if self.finished { Fault::Finished } else { Fault::NotPending });
        }
        coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena")).set_acc(mc, value);
        Ok(())
    }

    /// Persists the current execution registers (frame pointer, program counter, and fuel) into the
    /// root task object so GC tracing finds them between steps.
    fn save<'gc>(&mut self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, regs: &Regs<'gc>) {
        (self.fp, self.pc) = (regs.fp, regs.pc);
        task.set_acc(mc, regs.acc);
        let len = self.stack.segment(mc).len(mc);
        self.stack.set_top((regs.fp + WINDOW).min(len));
    }

    /// Drives the outer VM loop, dispatching inner loop execution and handling exit conditions (stack
    /// adjustments, requests, host calls, and coroutine context switches) until the task pauses or
    /// terminates.
    fn drive<'gc>(&mut self, mc: &Mutation<'gc>, task: &mut Gc<'gc, Task>, regs: &mut Regs<'gc>, fuel: &mut Fuel) -> Result<Outcome<'gc>, Fault> {
        let root = self.task.get(mc).expect("a machine runs in its own arena");
        let waiting = std::mem::replace(&mut self.waiting, Waiting::No);
        if waiting != Waiting::No {
            let mut outer = Outer::new(mc, &mut self.stack, root, *task, regs, self.segment);
            let step = if waiting == Waiting::Raise { outer.raise(outer.regs.acc, false) } else { outer.resume() };
            *task = outer.task();
            if let Some(outcome) = step? {
                return Ok(outcome);
            }
        }
        let mut deferred = None;
        loop {
            let exit = run::exec(mc, &self.stack, *task, regs, fuel, &mut deferred);
            let mut outer = Outer::new(mc, &mut self.stack, root, *task, regs, self.segment);
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
        [value] => Args::one(value),
        [first, second] => Args::two(first, second),
        _ => Args::list(Pairs::new(mc).list(args)?),
    })
}

/// What the outer loop holds responsible for a fault, which determines what the raised condition reports.
enum Blame<'gc> {
    /// The fault did not come from an identifiable operation.
    Nothing,
    /// The instruction the inner loop was executing when it exited: the one before the saved program counter.
    Instruction,
    /// The value that a call instruction tried to call.
    Callee(Value<'gc>),
}

/// The result of an outer loop step: returns `Ok(Some(outcome))` when execution finishes or pauses,
/// `Ok(None)` to continue running, or `Err(fault)` on error.
pub(crate) type Step<'gc> = Result<Option<Outcome<'gc>>, Fault>;

/// The next execution action to perform in the outer loop after a request has processed its
/// continuation modifications.
pub(crate) enum Then<'gc> {
    /// Calls the specified procedure with arguments, returning to the current continuation.
    Call(Value<'gc>, Args<'gc>),
    /// Returns the given value to the current continuation.
    Return(Value<'gc>),
    /// Resumes the specified coroutine with arguments.
    Resume(Value<'gc>, Args<'gc>),
    /// Raises an exception value, indicating whether execution resumes with the handler's return value
    /// (continuable).
    Raise(Value<'gc>, bool),
    /// An uncaught exception value, indicating whether all `dynamic-wind` `after` thunks have already
    /// run.
    Uncaught(Value<'gc>, bool),
    /// Yields the given value from the currently executing coroutine.
    Yield(Value<'gc>),
}

/// State for the outer execution loop between inner loop invocations, providing access to the stack,
/// current task, and VM registers.
pub(crate) struct Outer<'a, 'gc> {
    pub(crate) segments: Segments<'a, 'gc>,
    pub(crate) regs: &'a mut Regs<'gc>,
    /// The root task created by the machine.
    pub(crate) root: Gc<'gc, Task>,
}

impl<'a, 'gc> Outer<'a, 'gc> {
    fn new(mc: &'a Mutation<'gc>, stack: &'a mut Stack, root: Gc<'gc, Task>, task: Gc<'gc, Task>, regs: &'a mut Regs<'gc>, size: usize) -> Self {
        Outer { segments: Segments { mc, stack, task, size }, regs, root }
    }

    pub(crate) fn mc(&self) -> &'a Mutation<'gc> {
        self.segments.mc
    }

    pub(crate) fn task(&self) -> Gc<'gc, Task> {
        self.segments.task
    }

    /// Processes the exit condition that paused the inner loop. Non-fatal faults are raised as
    /// `Condition` objects, including faults that occur while invoking exception handlers.
    fn exit(&mut self, exit: Exit<'gc>, deferred: &mut Option<Deferred>) -> Step<'gc> {
        let mut blame = Blame::Nothing;
        let mut step = match exit {
            Exit::Paused => return Ok(Some(Outcome::Paused)),
            Exit::Fault(fault) => {
                blame = Blame::Instruction;
                Err(fault)
            }
            Exit::Overflow { callee, argc, rest } => self.overflow(callee, argc, rest).map(|()| None),
            Exit::Underflow => self.resume(),
            Exit::Call { base, argc, rest, tail } => {
                if let Ok(callee) = self.registers(base, 1) {
                    blame = Blame::Callee(callee.get(0));
                }
                self.call(base, argc, rest, tail)
            }
            Exit::Request { base, args, request, spread, tail } => self.request(base, args, request, spread, tail),
            Exit::Host { base, tail, then } => {
                // Take the deferred value beforehand so it is properly dropped if `keep` fails.
                let deferred = deferred.take();
                self.keep(base, tail).and_then(|()| self.host_then(then, deferred))
            }
        };
        while let Err(fault) = step
            && !fault.is_fatal()
        {
            step = self.fault(fault, std::mem::replace(&mut blame, Blame::Nothing));
        }
        step
    }

    /// Identifies the operation that raised `fault` and the values it was given, according to `blame`.
    fn origin(&self, fault: Fault, blame: Blame<'gc>) -> Result<Origin<'gc>, Fault> {
        let mc = self.mc();
        match blame {
            Blame::Instruction => {
                let (Some(code), Ok(frame)) = (self.regs.code, self.segments.frame(self.regs.fp)) else { return Ok(Origin { operation: None, irritants: Value::NIL }) };
                report::origin(mc, frame, code, self.regs.pc, fault)
            }
            Blame::Callee(callee) => Ok(Origin { operation: None, irritants: Pairs::new(mc).cons(callee, Value::NIL)?.value(mc) }),
            Blame::Nothing => Ok(Origin { operation: None, irritants: Value::NIL }),
        }
    }

    /// Creates and raises a `Condition` object for `fault`, replacing the frame where the fault
    /// occurred. `blame` selects what the condition reports as the failed operation.
    fn fault(&mut self, fault: Fault, blame: Blame<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let first = if matches!(blame, Blame::Instruction) { self.regs.code.map(|code| (code, self.regs.pc)) } else { None };
        let origin = self.origin(fault, blame)?;
        let failure = Failure { fault, operation: origin.operation };
        let raised = Value::object(mc, Condition::new(mc, mc.frozen(failure)?, Value::VOID, origin.irritants, Value::FALSE)?);
        if self.regs.fp > self.segments.stack.base()
            && let Ok(frame) = self.segments.frame(self.regs.fp)
            && let Ok(link) = frame::link_of(mc, frame)
        {
            let _ = self.segments.reify(self.regs.fp, link);
        }
        let then = self.raising(raised, false, first)?;
        self.then(then)
    }

    /// Records the call trace in `obj` if it is a condition that has not been raised before. `first` is the function that raised a fault, as [`report::capture`] takes it.
    pub(crate) fn record(&mut self, obj: Value<'gc>, first: Option<(Gc<'gc, Bytecode>, usize)>) -> Result<(), Fault> {
        let mc = self.mc();
        let Some(condition) = obj.downcast::<Condition>(mc).filter(|condition| condition.trace(mc) == Value::FALSE) else { return Ok(()) };
        condition.set_trace(mc, report::capture(mc, self.task(), first)?);
        Ok(())
    }

    /// Raises `obj`, behaving as `raise` (non-continuable) or `raise-continuable` depending on the
    /// `continuable` flag.
    fn raise(&mut self, obj: Value<'gc>, continuable: bool) -> Step<'gc> {
        let then = self.raising(obj, continuable, None)?;
        self.then(then)
    }

    /// Handles an uncaught exception: runs any remaining `dynamic-wind` `after` thunks (unless already
    /// unwound), then fails the coroutine and propagates the exception to its resumer, or terminates the
    /// root task with [`Outcome::Raised`].
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

    /// Executes `request` using arguments starting at register `base` (spreading the final argument as a
    /// list if `spread` is set), while preserving registers beyond the retained continuation.
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

    /// Invokes a non-closure procedure located in register `base`, passing `argc` following registers
    /// and elements of `rest` as arguments.
    fn call(&mut self, base: u8, argc: u8, rest: Value<'gc>, tail: bool) -> Step<'gc> {
        let slots = self.registers(base, argc + 1)?;
        let args = Args::slots(slots.slice(1..slots.len()).ok_or(Fault::Malformed)?, rest);
        self.keep(base, tail)?;
        self.then(Then::Call(slots.get(0), args))
    }

    /// Returns a slice of `count` registers starting at offset `base` within the current frame window.
    fn registers(&self, base: u8, count: u8) -> Result<Slots<'gc>, Fault> {
        let (mc, at) = (self.mc(), self.regs.fp + usize::from(base));
        if usize::from(base) + usize::from(count) > WINDOW {
            return Err(Fault::Malformed);
        }
        self.segments.stack.segment(mc).slots(mc).slice(at..at + usize::from(count)).ok_or(Fault::Malformed)
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

    /// Applies `procedure` to `args`. For a closure, establishes a new bottom frame; for a continuation,
    /// unwinds and rewinds intervening winders before resuming with the provided arguments.
    fn apply(&mut self, procedure: Value<'gc>, args: Args<'gc>) -> Step<'gc> {
        if let Some(continuation) = procedure.downcast::<Continuation>(self.mc()) {
            let then = self.go_to(continuation, args)?;
            return self.then(then);
        }
        if let Some(callee) = procedure.downcast::<KeywordProcedure>(self.mc()) {
            let then = keyword::positional(self.mc(), callee, args)?;
            return self.then(then);
        }
        self.start(procedure, args)?;
        Ok(None)
    }

    /// Handles a host function exit action (raising an exception or deferring completion) within the
    /// current continuation.
    fn host_then(&mut self, then: HostThen<'gc>, deferred: Option<Deferred>) -> Step<'gc> {
        match then {
            HostThen::Raise(raised) => self.raise(raised, false),
            HostThen::Defer => {
                self.regs.acc = Value::VOID;
                Ok(Some(Outcome::Deferred(deferred.ok_or(Fault::Malformed)?)))
            }
        }
    }

    /// Slices and saves active stack frames below the current call or request into the continuation
    /// chain. For tail calls, the continuation is the caller; for non-tail calls, it is the succeeding
    /// instruction.
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

    /// Transfers an overflowing call frame and its caller's linkage onto a new stack segment.
    fn overflow(&mut self, callee: usize, argc: u8, rest: Value<'gc>) -> Result<(), Fault> {
        let base = callee - self.regs.fp;
        let link = Link::to(self.regs.pc, u8::try_from(base).map_err(|_| Fault::Malformed)?);
        let fp = self.segments.overflow(self.regs.fp, callee + 1 + usize::from(argc), base + WINDOW)?;
        self.regs.fp = fp;
        self.enter(fp + base, argc, rest, link)
    }

    /// Returns the accumulator value to the current continuation, popping stack records, prompts, and
    /// native continuation frames. If no continuation frames remain, completes the task (returning to the
    /// resumer for coroutines).
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

    /// Sets up the initial stack frame at the base of the stack and binds `args` to enter closure
    /// `procedure`.
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

    /// Enters a closure in the frame at `fp`, binding `argc` register arguments and subsequent `rest`
    /// list arguments under `link`.
    fn enter(&mut self, fp: usize, argc: u8, rest: Value<'gc>, link: Link) -> Result<(), Fault> {
        let mc = self.mc();
        let frame = self.segments.frame(fp)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::NotProcedure)?;
        // The outer loop independently checks whether a GC step is due, so fuel tracking is omitted here.
        let mut fuel = Fuel { run: 0, rest: 0 };
        bind(mc, frame, closure.code(mc).ok_or(Fault::Malformed)?.arity(mc), argc, rest, &mut fuel)?;
        frame::set_link(mc, frame, link)?;
        (self.regs.fp, self.regs.pc) = (fp, 0);
        Ok(())
    }
}

/// Constructs a Scheme `Condition` object representing `fault`, with the specified message and
/// irritants.
pub(crate) fn condition<'gc>(mc: &Mutation<'gc>, fault: Fault, message: Value<'gc>, irritants: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Value::object(mc, Condition::new(mc, mc.frozen(Failure { fault, operation: None })?, message, irritants, Value::FALSE)?))
}
