
use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Gc, Mutation, Root, Segment, Slots, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::passed::{Passed, Taken};
use crate::frame::{self, ARGS, CLOSURE, Link};
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields, Continuation, KeywordProcedure, Native, NativeFields, Task, TaskFields};
use crate::run::{self, Exit, HostThen, MAX_ARGS, Regs, bind};
use crate::segments::{CHUNK, Resume, Segments};
use crate::wind::Kind;
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
    /// The task completed successfully and produced this return value. If it returned several values, this is the first. If it returned none, this is void.
    Done(Value<'gc>),
    /// The run stopped because a collection step is due. A later run continues the task. A run that
    /// stops with no fuel left fails with [`Fault::OutOfFuel`] instead.
    Paused,
    /// An unhandled exception or condition raised by the task, returned after executing all intervening
    /// `dynamic-wind` `after` thunks. For VM faults, this contains a `Condition` object.
    Raised(Value<'gc>),
    /// The root task yielded directly via `co/yield` (rather than an inner resumed coroutine). This is
    /// the list of the values it yielded. Can be resumed by calling [`Machine::resume`].
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
    /// Whether the last run returned [`Outcome::Paused`] without resuming the task. That happens when
    /// the machine is waiting for its host and a collection step is due. The next run resumes the
    /// task even if a step is still due.
    held: bool,
}

impl Machine {
    /// Creates a new machine initialized to call `procedure` with `args`, allocating stack segments of
    /// at least `MIN_SEGMENT` slots (or `segment` if larger).
    pub fn new<'gc>(mc: &Mutation<'gc>, segment: usize, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<Self, Fault> {
        let segment = segment.max(MIN_SEGMENT);
        let mut stack = mc.stack(Segment::new(mc, segment)?)?;
        let task = coroutine::root(mc)?;
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID, values: Value::NULL, code: None };
        Outer::new(mc, &mut stack, task, task, &mut regs, segment).begin(procedure, args)?;
        let mut machine = Machine { stack, task: Root::new(mc, task)?, fp: 0, pc: 0, segment, fuel: u64::MAX, finished: false, waiting: Waiting::No, held: false };
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
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID, values: Value::NULL, code: None };
        Outer::new(mc, &mut self.stack, task, task, &mut regs, self.segment).begin(procedure, args)?;
        (self.task, self.finished, self.waiting, self.held) = (Root::new(mc, task)?, false, Waiting::No, false);
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
    ///
    /// A machine that is waiting on a yield or a deferred host call does not resume while a
    /// collection step is due. The run returns [`Outcome::Paused`] immediately, and so do
    /// [`Machine::resume`], [`Machine::reply`] and [`Machine::raise`]. The value the host passed is
    /// kept, and the next run delivers it. So a host that answers a machine repeatedly within one
    /// step still lets the collector run, provided it ends the step when it sees [`Outcome::Paused`].
    /// The run after such a pause always resumes the task, so a machine is never paused this way
    /// twice in a row.
    pub fn run<'gc>(&mut self, mc: &Mutation<'gc>) -> Result<Outcome<'gc>, Fault> {
        if self.finished {
            return Err(Fault::Finished);
        }
        if self.waiting != Waiting::No {
            let held = std::mem::replace(&mut self.held, false);
            if !held && mc.step_due() {
                self.held = true;
                return Ok(Outcome::Paused);
            }
        }
        let mut task = coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena"));
        let mut regs = Regs { fp: self.fp, pc: self.pc, acc: task.acc(mc), values: task.values(mc), code: None };
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
            let state = if matches!(outcome, Ok(Outcome::Done(_))) {
                coroutine::DEAD
            } else {
                coroutine::FAILED
            };
            self.task.get(mc).expect("a machine runs in its own arena").set_state(mc, state);
        }
        self.save(mc, task, &regs);
        outcome
    }

    /// Resumes a machine that suspended via `co/yield`, passing `args` as the return value of the yield
    /// expression. Returns `Err(Fault::NotPending)` if the machine is not waiting on a yield.
    ///
    /// Returns [`Outcome::Paused`] without resuming if a collection step is due. The values are kept:
    /// call [`Machine::run`] in the next step. See [`Machine::run`].
    pub fn resume<'gc>(&mut self, mc: &Mutation<'gc>, args: &[Value<'gc>]) -> Result<Outcome<'gc>, Fault> {
        if args.contains(&Value::VALUES) {
            return Err(Fault::WrongType);
        }
        let (acc, values) = match *args {
            [value] => (value, Value::NULL),
            _ => (Value::VALUES, Pairs::new(mc).list(args)?),
        };
        self.answer(mc, Waiting::Yield, acc)?;
        coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena")).set_values(mc, values);
        self.run(mc)
    }

    /// Resumes a machine that suspended on a deferred host function call, supplying `answer` as the host
    /// function's return value. Returns `Err(Fault::NotPending)` if the machine is not waiting on a
    /// deferred host call.
    ///
    /// Returns [`Outcome::Paused`] without resuming if a collection step is due. The answer is kept:
    /// call [`Machine::run`] in the next step. See [`Machine::run`].
    pub fn reply<'gc>(&mut self, mc: &Mutation<'gc>, answer: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        if answer == Value::VALUES {
            return Err(Fault::WrongType);
        }
        self.answer(mc, Waiting::Host, answer)?;
        self.run(mc)
    }

    /// Resumes a machine waiting on a deferred host function call by raising `raised` as an exception at
    /// the point of suspension.
    ///
    /// Returns [`Outcome::Paused`] without resuming if a collection step is due. The value is kept:
    /// call [`Machine::run`] in the next step. See [`Machine::run`].
    pub fn raise<'gc>(&mut self, mc: &Mutation<'gc>, raised: Value<'gc>) -> Result<Outcome<'gc>, Fault> {
        // A raise that was postponed for the collector is still pending, and the host may request it again.
        let on = if self.waiting == Waiting::Raise {
            Waiting::Raise
        } else {
            Waiting::Host
        };
        self.answer(mc, on, raised)?;
        self.waiting = Waiting::Raise;
        self.run(mc)
    }

    /// Delivers `value` to the suspended task if it is currently waiting on `on`, preparing it to resume
    /// on the next run.
    fn answer<'gc>(&mut self, mc: &Mutation<'gc>, on: Waiting, value: Value<'gc>) -> Result<(), Fault> {
        if self.waiting != on {
            let fault = if self.finished {
                Fault::Finished
            } else {
                Fault::NotPending
            };
            return Err(fault);
        }
        coroutine::current(mc, self.task.get(mc).expect("a machine runs in its own arena")).set_acc(mc, value);
        Ok(())
    }

    /// Saves the registers at the end of a run. `fp` and `pc` are stored in the machine. The
    /// accumulator and its list of values are stored in `task`, where the collector traces them
    /// between steps. The top of the stack is set to the end of the current frame's window, so the
    /// frame's registers stay live.
    fn save<'gc>(&mut self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, regs: &Regs<'gc>) {
        (self.fp, self.pc) = (regs.fp, regs.pc);
        task.set_acc(mc, regs.acc);
        // The list is meaningful only when the accumulator holds the marker. A stale list is dropped here, so it does not stay alive past this run.
        let values = if regs.acc == Value::VALUES {
            regs.values
        } else {
            Value::NULL
        };
        task.set_values(mc, values);
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
            let step = if waiting == Waiting::Raise {
                outer.raise(outer.regs.acc, false)
            } else {
                outer.resume()
            };
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

/// The source the outer loop blames for a fault. It determines the operation and irritants that the raised condition reports.
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
    Call(Value<'gc>, Passed<'gc>),
    /// Returns the given value to the current continuation.
    Return(Value<'gc>),
    /// Returns the values in the given proper list to the current continuation.
    ReturnValues(Value<'gc>),
    /// Returns the current contents of the accumulator to the current continuation.
    Forward,
    /// Resumes the specified coroutine by raising the given value inside it.
    ResumeError(Value<'gc>, Value<'gc>),
    /// Closes the specified coroutine. Then, unless the second value is `#f`, makes it pending again with that procedure as its body.
    Close(Value<'gc>, Value<'gc>),
    /// Raises an exception value, indicating whether execution resumes with the handler's return value
    /// (continuable).
    Raise(Value<'gc>, bool),
    /// An uncaught exception value, indicating whether all `dynamic-wind` `after` thunks have already
    /// run.
    Uncaught(Value<'gc>, bool),
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
                let (Some(code), Ok(frame)) = (self.regs.code, self.segments.frame(self.regs.fp)) else { return Ok(Origin { operation: None, irritants: Value::NULL }) };
                // `received` is the number of values the accumulator held when the instruction failed. It held one value, or the marker and a list of values.
                let received = if self.regs.acc == Value::VALUES {
                    Pairs::new(mc).list_len(self.regs.values)
                } else {
                    Some(1)
                };
                let received = received.and_then(|received| i64::try_from(received).ok()).and_then(Value::fixnum).unwrap_or(Value::VOID);
                report::origin(mc, frame, code, self.regs.pc, received, fault)
            }
            Blame::Callee(callee) => Ok(Origin { operation: None, irritants: Pairs::new(mc).cons(callee, Value::NULL)?.value(mc) }),
            Blame::Nothing => Ok(Origin { operation: None, irritants: Value::NULL }),
        }
    }

    /// Creates and raises a `Condition` object for `fault`, replacing the frame where the fault
    /// occurred. `blame` selects the operation and irritants that the condition reports.
    fn fault(&mut self, fault: Fault, blame: Blame<'gc>) -> Step<'gc> {
        let mc = self.mc();
        let first = if matches!(blame, Blame::Instruction) {
            self.regs.code.map(|code| (code, self.regs.pc))
        } else {
            None
        };
        let origin = self.origin(fault, blame)?;
        let failure = Failure { fault, operation: origin.operation };
        let raised = Value::object(mc, Condition::new(mc, mc.frozen(failure)?, Value::VOID, origin.irritants, Value::FALSE)?);
        // A request can park its task and then fail. The condition is raised on top of the task's frames, so they are saved first.
        self.settle()?;
        let task = self.task();
        if coroutine::is_parked(mc, task) {
            // A `co/try-resume` that failed stays parked, and its guard catches the condition. The call trace reads the parked frames through the task's `segment` and `base` fields, as it does for a suspended task.
            task.set_segment(mc, Some(self.segments.stack.segment(mc)));
            task.set_base(mc, u32::try_from(self.segments.stack.base()).map_err(|_| Fault::Malformed)?);
        } else if self.regs.fp > self.segments.stack.base()
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
        // A coroutine that fails while a reset is closing it is still reset. The value is still raised in the task that requested the reset.
        let renew = if task.state(mc) == coroutine::CLOSING {
            task.body(mc)
        } else {
            Value::FALSE
        };
        self.end(task, coroutine::FAILED, to)?;
        if renew != Value::FALSE {
            coroutine::reset(mc, task, renew);
        }
        // The value is raised on top of the resumer's frames, so they are saved first.
        self.settle()?;
        self.raise(obj, false)
    }

    /// Executes `request` using arguments starting at register `base` (spreading the final argument as a
    /// list if `spread` is set), while preserving registers beyond the retained continuation.
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Step<'gc> {
        let mc = self.mc();
        let (mut count, mut rest) = (args, Value::NULL);
        if spread {
            // The last register holds a list of the operands that follow the operands in registers.
            count -= 1;
            rest = self.registers(base, args)?.get(usize::from(count));
            let listed = Pairs::new(mc).list_len(rest).ok_or(Fault::WrongType)?;
            if !usize::try_from(listed).is_ok_and(|listed| request.takes(usize::from(count) + listed)) {
                return Err(Fault::Arity);
            }
            // The request reads its own operands from registers. Any of those operands that are in the list are moved into registers.
            let frame = self.segments.frame(self.regs.fp)?;
            while usize::from(count) < request.fixed() {
                let cell = Pair::of(rest).ok_or(Fault::Malformed)?;
                if usize::from(base) + usize::from(count) >= WINDOW {
                    return Err(Fault::Malformed);
                }
                frame.set(base + count, cell.head(mc));
                (count, rest) = (count + 1, cell.tail(mc));
            }
        }
        let args = Passed::slots(self.registers(base, count)?, rest);
        // A switch to another coroutine, or a yield to the host, returns to this frame. So the frame is parked and not saved. The switch is made directly here, because it is the only work a coroutine does between two runs of the inner loop.
        if matches!(request, Request::Resume | Request::TryResume | Request::Yield) {
            self.park(base, tail, request == Request::TryResume)?;
            if request == Request::Yield {
                return self.yield_coroutine(args);
            }
            if request == Request::TryResume {
                self.guard(Value::FALSE, true, true)?;
            }
            return self.resume_coroutine(args.get(mc, 0)?, args.skip(mc, 1)?);
        } else if request != Request::Abort {
            // An abort saves the caller's frames itself, and only when it has to.
            self.keep(base, tail)?;
        }
        let then = request.run(self, args, base, tail)?;
        self.then(then)
    }

    /// Invokes a non-closure procedure located in register `base`, passing `argc` following registers
    /// and elements of `rest` as arguments.
    fn call(&mut self, base: u8, argc: u8, rest: Value<'gc>, tail: bool) -> Step<'gc> {
        let slots = self.registers(base, argc + 1)?;
        let args = Passed::slots(slots.slice(1..slots.len()).ok_or(Fault::Malformed)?, rest);
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

    /// Returns `taken` to the current continuation.
    pub(crate) fn returned(&mut self, taken: Taken<'gc>) -> Step<'gc> {
        match taken {
            Taken::One(value) => self.regs.acc = value,
            Taken::List(list) => self.regs.set_values(self.mc(), list),
        }
        self.resume()
    }

    pub(crate) fn then(&mut self, then: Then<'gc>) -> Step<'gc> {
        match then {
            Then::Call(procedure, args) => self.apply(procedure, args),
            Then::Return(value) => {
                self.regs.acc = value;
                self.resume()
            }
            Then::ReturnValues(list) => {
                self.regs.set_values(self.mc(), list);
                self.resume()
            }
            Then::Forward => self.resume(),
            Then::ResumeError(co, raised) => self.resume_error(co, raised),
            Then::Close(co, renew) => self.close_coroutine(co, renew),
            Then::Raise(obj, continuable) => self.raise(obj, continuable),
            Then::Uncaught(obj, unwound) => self.uncaught(obj, unwound),
        }
    }

    /// Applies `procedure` to `args`. For a closure, establishes a new bottom frame; for a continuation,
    /// unwinds and rewinds intervening winders before resuming with the provided arguments.
    fn apply(&mut self, procedure: Value<'gc>, args: Passed<'gc>) -> Step<'gc> {
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

    /// Prepares the running task to switch away at the request in register `base`, without saving its
    /// frames to its chain as [`Outer::keep`] does.
    ///
    /// The task records the frame and the instruction where it resumes. When values are returned to
    /// it, [`Outer::resume`] continues there directly. Anything else that happens to the task first
    /// calls [`Outer::settle`] or [`coroutine::unpark`], which save the frames to the chain.
    ///
    /// - A request in tail position (`tail`) parks the frame's caller. Some frames cannot be parked
    ///   that way, and [`Outer::keep`] saves them instead. See [`coroutine::place`].
    /// - `tried` is set for `co/try-resume`, which pushes a guard record after this call. See
    ///   [`coroutine::TRIED`].
    ///
    /// The frames on the stack stay live while the task is suspended, and each switch hands them over
    /// to the collector. So if more than [`coroutine::PARKED`] slots lie below the parked frame, those
    /// slots are saved to the chain here, once, and the parked frame becomes the bottom frame.
    fn park(&mut self, base: u8, tail: bool, tried: bool) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let caller = if tail {
            Some(frame::link_of(mc, self.segments.frame(self.regs.fp)?)?)
        } else {
            None
        };
        let Some((fp, parked)) = coroutine::place(self.regs.fp, self.regs.pc, base, caller) else { return self.keep(base, tail) };
        if fp - self.segments.stack.base() > coroutine::PARKED {
            let link = frame::link_of(mc, self.segments.frame(fp)?)?;
            self.segments.reify(fp, link)?;
            frame::set_link(mc, self.segments.frame(fp)?, Link::BOTTOM)?;
        }
        if !coroutine::park(mc, task, fp, parked, tried) {
            return self.keep(base, tail);
        }
        Ok(())
    }

    /// Returns whether the record at the head of `task`'s chain is the guard of a `co/try-resume`.
    fn tried_guard(&self, task: Gc<'gc, Task>) -> bool {
        let mc = self.mc();
        task.chain(mc).downcast::<Native>(mc).is_some_and(|native| native.kind(mc) == Kind::Guarded as u32 && native.b(mc) == Value::TRUE)
    }

    /// Saves the parked frames of the running task to its chain, as [`Outer::keep`] would have done
    /// when the task switched away. Does nothing for a task that is not parked.
    ///
    /// Call this while the task may still be parked, before any operation that starts a frame at the
    /// base of the stack or reads the task's chain. Such operations are a raise into the task, its
    /// unwinding, and a fault.
    ///
    /// A task parked by `co/try-resume` stays parked. Its guard record is already on the chain, above
    /// the position where the frames would go. That guard catches every value raised into the task,
    /// so no frame starts on top of the parked frames.
    pub(crate) fn settle(&mut self) -> Result<(), Fault> {
        let (mc, task) = (self.mc(), self.task());
        let base = task.park_base(mc);
        if base == 0 || base & coroutine::TRIED != 0 {
            return Ok(());
        }
        task.set_park_base(mc, 0);
        let (fp, pc) = (task.park_fp(mc) as usize, task.park_pc(mc) as usize);
        // As in `keep`: the request's registers must lie past the frame's link.
        let closure = self.segments.frame(fp)?.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        if base <= u32::from(frame::link_slot_of(mc, closure)?) {
            return Err(Fault::Malformed);
        }
        self.segments.reify(fp + base as usize, Link::to(pc, base as u8))
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
            // A parked task resumes in the frame it switched away from. Its frames are above every record on its chain, except the guard record of a `co/try-resume`. That record is handled first.
            let park = task.park_base(mc);
            if park != 0 && (park & coroutine::TRIED == 0 || !self.tried_guard(task)) {
                task.set_park_base(mc, 0);
                (self.regs.fp, self.regs.pc) = (task.park_fp(mc) as usize, task.park_pc(mc) as usize);
                return Ok(None);
            }
            if let Some(native) = task.chain(mc).downcast::<Native>(mc) {
                task.set_chain(mc, native.next(mc));
                task.set_attachments(mc, native.attachments(mc));
                match self.native(native)? {
                    Then::Return(value) => self.regs.acc = value,
                    Then::ReturnValues(list) => self.regs.set_values(mc, list),
                    Then::Forward => {}
                    then => return self.then(then),
                }
                continue;
            }
            if let Some(Resume { fp, pc }) = self.segments.underflow()? {
                (self.regs.fp, self.regs.pc) = (fp, pc);
                return Ok(None);
            }
            let task = self.task();
            if prompts::pop(mc, task)? {
                continue;
            }
            let Some(to) = coroutine::of(mc, task.resumer(mc)) else { return Ok(Some(Outcome::Done(self.regs.first(mc)))) };
            self.end(task, coroutine::DEAD, to)?;
        }
    }

    /// Starts a machine's first call: `procedure` with `args`.
    fn begin(&mut self, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<(), Fault> {
        if args.contains(&Value::VALUES) {
            return Err(Fault::WrongType);
        }
        let passed = if args.len() <= MAX_ARGS {
            self.pass(args)?
        } else {
            Passed::list(Pairs::new(self.mc()).list(args)?)
        };
        self.start(procedure, passed)
    }

    /// Sets up the initial stack frame at the base of the stack and binds `args` to enter closure
    /// `procedure`.
    fn start(&mut self, procedure: Value<'gc>, args: Passed<'gc>) -> Result<(), Fault> {
        let mc = self.mc();
        let held = args.held();
        let argc = u8::try_from(held.map_or(0, Slots::len)).ok().filter(|&count| usize::from(count) <= MAX_ARGS).ok_or(Fault::Malformed)?;
        let fp = if args.placed {
            self.segments.stack.base()
        } else if self.segments.fits(0) {
            let fp = self.segments.stack.base();
            if let Some(slots) = held
                && !self.segments.stack.write(mc, fp + usize::from(ARGS), slots)
            {
                return Err(Fault::Malformed);
            }
            fp
        } else {
            // The slots are cleared when the stack moves to a new segment, so the values are copied out first.
            let saved: Vec<Value<'gc>> = held.map_or(Vec::new(), |slots| (0..slots.len()).map(|i| slots.get(i)).collect());
            let fp = self.segments.bottom(0)?;
            let frame = self.segments.frame(fp)?;
            for (register, value) in (ARGS..).zip(saved) {
                frame.set(register, value);
            }
            fp
        };
        self.segments.frame(fp)?.set(CLOSURE, procedure);
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
