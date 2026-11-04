
use ragwort_types::gc::{Gc, Mutation, Root, Segment, Stack, Value, WINDOW};
use ragwort_types::pair::Pair;

use crate::frame::{self, ARGS, CLOSURE, Link};
use crate::intrinsic::values;
use crate::objects::{BytecodeFields, Closure, ClosureFields, Condition, Continuation, Task, TaskFields};
use crate::run::{self, Exit, MAX_ARGS, Regs, bind};
use crate::segments::{CHUNK, Resume, Segments};
use crate::{Fault, Fuel, Request, prompts};

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
    /// A VM fault, as a `Condition`, with no fault procedure to take it, or one that couldn't
    /// be called.
    Raised(Value<'gc>),
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
}

impl Machine {
    /// A task that calls `procedure` with `args`, on segments of `segment` slots, at least
    /// [`MIN_SEGMENT`].
    pub fn new<'gc>(mc: &Mutation<'gc>, segment: usize, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<Self, Fault> {
        let segment = segment.max(MIN_SEGMENT);
        let mut stack = mc.stack(Segment::new(mc, segment)?)?;
        let task = Task::new(mc, Value::VOID, Value::FALSE, Value::NIL, Value::NIL, Value::FALSE, None, 0)?;
        let mut regs = Regs { fp: 0, pc: 0, acc: Value::VOID };
        Outer::new(mc, &mut stack, task, &mut regs, segment).start(procedure, args)?;
        let mut machine = Machine { stack, task: Root::new(mc, task)?, fp: 0, pc: 0, segment, fuel: u64::MAX, finished: false };
        machine.save(mc, task, &regs);
        Ok(machine)
    }

    /// Has VM faults call `procedure` with a `Condition`, in place of the frames that faulted,
    /// as the prelude's `raise` would be. Without one, a fault ends the run with
    /// [`Outcome::Raised`].
    pub fn set_fault<'gc>(&self, mc: &Mutation<'gc>, procedure: Value<'gc>) {
        self.task.get(mc).expect("a machine runs in its own arena").set_fault(mc, procedure);
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

    /// Runs until the task finishes or its fuel runs out, or until it has made enough that the
    /// step should end so the collector can keep up, as [`Mutation::step_due`] says: then it
    /// pauses at its next call or jump, and the next run goes on from there. Running it again
    /// once it's finished faults with [`Fault::Finished`].
    pub fn run<'gc>(&mut self, mc: &Mutation<'gc>) -> Result<Outcome<'gc>, Fault> {
        if self.finished {
            return Err(Fault::Finished);
        }
        let task = self.task.get(mc).expect("a machine runs in its own arena");
        let mut regs = Regs { fp: self.fp, pc: self.pc, acc: task.acc(mc) };
        let mut fuel = Fuel { run: self.fuel, rest: 0 };
        let outcome = match self.drive(mc, task, &mut regs, &mut fuel) {
            Ok(Outcome::Paused) if fuel.left() == 0 => Err(Fault::OutOfFuel),
            outcome => outcome,
        };
        self.fuel = fuel.left();
        self.finished = matches!(outcome, Ok(Outcome::Done(_) | Outcome::Raised(_)) | Err(Fault::OutOfFuel));
        self.save(mc, task, &regs);
        outcome
    }

    /// Keeps what the next run needs where a collection finds it.
    fn save<'gc>(&mut self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, regs: &Regs<'gc>) {
        (self.fp, self.pc) = (regs.fp, regs.pc);
        task.set_acc(mc, regs.acc);
        let len = self.stack.segment(mc).len(mc);
        self.stack.set_top((regs.fp + WINDOW).min(len));
    }

    /// Runs the inner loop, and carries out what it stops for, until the task ends or the run's
    /// fuel runs out.
    fn drive<'gc>(&mut self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, regs: &mut Regs<'gc>, fuel: &mut Fuel) -> Result<Outcome<'gc>, Fault> {
        loop {
            let exit = run::exec(mc, &self.stack, regs, fuel);
            if let Some(outcome) = Outer::new(mc, &mut self.stack, task, regs, self.segment).exit(exit)? {
                return Ok(outcome);
            }
            if mc.step_due() {
                return Ok(Outcome::Paused);
            }
        }
    }
}

/// What a step of the outer loop leads to: going on, or the end of the run.
pub(crate) type Step<'gc> = Result<Option<Outcome<'gc>>, Fault>;

/// What a request leads to, once it has done what it does to the continuation.
pub(crate) enum Then<'gc> {
    /// A call of the procedure with the values, which returns to the current continuation.
    Call(Value<'gc>, Vec<Value<'gc>>),
    /// The value, returned to the current continuation.
    Return(Value<'gc>),
}

/// The outer loop's state, between two stretches of the inner loop: the stack, and the
/// registers the inner loop goes on with.
pub(crate) struct Outer<'a, 'gc> {
    pub(crate) segments: Segments<'a, 'gc>,
    regs: &'a mut Regs<'gc>,
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

    /// Carries out what the inner loop stopped for. A fault that isn't fatal goes to the fault
    /// procedure, as a `Condition`.
    fn exit(&mut self, exit: Exit<'gc>) -> Step<'gc> {
        let step = match exit {
            Exit::Paused => return Ok(Some(Outcome::Paused)),
            Exit::Fault(fault) => Err(fault),
            Exit::Overflow { callee, argc, rest } => self.overflow(callee, argc, rest).map(|()| None),
            Exit::Underflow => self.resume(),
            Exit::Call { base, argc, rest, tail } => self.call(base, argc, rest, tail),
            Exit::Request { base, args, request, tail } => self.request(base, args, request, tail),
        };
        match step {
            Err(fault) if !fault.is_fatal() => self.fault(fault),
            step => step,
        }
    }

    /// Calls the fault procedure with a condition for `fault`, in place of the frames above the
    /// chain. A fault in calling it ends the run.
    fn fault(&mut self, fault: Fault) -> Step<'gc> {
        let mc = self.mc();
        let (handler, raised) = (self.task().fault(mc), condition(mc, fault, Value::VOID, Value::NIL)?);
        if handler == Value::FALSE {
            return Ok(Some(Outcome::Raised(raised)));
        }
        match self.then(Then::Call(handler, vec![raised])) {
            Err(fault) if !fault.is_fatal() => Ok(Some(Outcome::Raised(condition(mc, fault, Value::VOID, Value::NIL)?))),
            step => step,
        }
    }

    /// Carries out `request` on the `args` registers from `base`.
    fn request(&mut self, base: u8, args: u8, request: Request, tail: bool) -> Step<'gc> {
        let frame = self.segments.frame(self.regs.fp)?;
        let args: Vec<_> = (0..args).map(|i| frame.get(base + i)).collect();
        if request.keeps() {
            self.keep(base, tail)?;
        }
        let then = request.run(self, &args)?;
        self.then(then)
    }

    /// Carries out a call of something other than a closure, in register `base`, with the
    /// `argc` registers after it and the elements of the list `rest` as its arguments.
    fn call(&mut self, base: u8, argc: u8, rest: Value<'gc>, tail: bool) -> Step<'gc> {
        let frame = self.segments.frame(self.regs.fp)?;
        let procedure = frame.get(base);
        let mut args: Vec<_> = (1..=argc).map(|i| frame.get(base + i)).collect();
        args.extend(list(self.mc(), rest)?);
        self.keep(base, tail)?;
        self.then(Then::Call(procedure, args))
    }

    fn then(&mut self, then: Then<'gc>) -> Step<'gc> {
        match then {
            Then::Call(procedure, args) => self.apply(procedure, &args),
            Then::Return(value) => {
                self.regs.acc = value;
                self.resume()
            }
        }
    }

    /// Calls `procedure` with `args`. A closure gets a frame at the bottom of the stack; a
    /// continuation goes on on top of the current one, and gets the values.
    fn apply(&mut self, procedure: Value<'gc>, args: &[Value<'gc>]) -> Step<'gc> {
        let (mc, task) = (self.mc(), self.task());
        if let Some(k) = procedure.downcast::<Continuation>(mc) {
            prompts::compose(mc, task, k)?;
            return self.then(Then::Return(values(mc, args.iter().copied())?));
        }
        self.start(procedure, args)?;
        Ok(None)
    }

    /// Hands the frames under the continuation of the current call or request to the chain. A
    /// tail call's continuation is the current frame's caller; any other's is the instruction
    /// after it, whose `base` must be past the frame's link, as a call's is.
    fn keep(&mut self, base: u8, tail: bool) -> Result<(), Fault> {
        let (mc, fp) = (self.mc(), self.regs.fp);
        let frame = self.segments.frame(fp)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        let at = frame::link_slot_of(mc, closure)?;
        let (end, link) = if tail {
            (fp, Link::of(frame.get(at)).ok_or(Fault::Malformed)?)
        } else if base > at {
            (fp + usize::from(base), Link { pc: self.regs.pc, base })
        } else {
            return Err(Fault::Malformed);
        };
        self.segments.reify(end, link)
    }

    /// Makes the frame of a call that doesn't fit, with its caller's, on another segment.
    fn overflow(&mut self, callee: usize, argc: u8, rest: Value<'gc>) -> Result<(), Fault> {
        let base = callee - self.regs.fp;
        let link = Link { pc: self.regs.pc, base: u8::try_from(base).map_err(|_| Fault::Malformed)? };
        let fp = self.segments.overflow(self.regs.fp, callee + 1 + usize::from(argc), base + WINDOW)?;
        self.enter(fp + base, argc, rest, link)
    }

    /// Goes back to the continuation with the value in the accumulator: the records under the
    /// stack, then the prompts'. If none is left, the task is done, and that's its value.
    fn resume(&mut self) -> Step<'gc> {
        let (mc, task) = (self.mc(), self.task());
        loop {
            if let Some(Resume { fp, pc }) = self.segments.underflow()? {
                (self.regs.fp, self.regs.pc) = (fp, pc);
                return Ok(None);
            }
            if !prompts::pop(mc, task)? {
                return Ok(Some(Outcome::Done(self.regs.acc)));
            }
        }
    }

    /// Calls the closure `procedure` with `args` in a frame at the bottom of the stack.
    fn start(&mut self, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<(), Fault> {
        let argc = u8::try_from(args.len()).ok().filter(|&n| usize::from(n) <= MAX_ARGS).ok_or(Fault::Arity)?;
        let fp = self.segments.bottom(0)?;
        let frame = self.segments.frame(fp)?;
        frame.set(CLOSURE, procedure);
        (ARGS..).zip(args).for_each(|(r, &arg)| frame.set(r, arg));
        self.enter(fp, argc, Value::NIL, Link::BOTTOM)
    }

    /// Enters the closure in the frame at `fp`, with `argc` arguments and the list `rest` after
    /// them, and `link`.
    fn enter(&mut self, fp: usize, argc: u8, rest: Value<'gc>, link: Link) -> Result<(), Fault> {
        let mc = self.mc();
        let frame = self.segments.frame(fp)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::NotProcedure)?;
        bind(mc, frame, closure.code(mc).ok_or(Fault::Malformed)?.arity(mc), argc, rest)?;
        frame::set_link(mc, frame, link)?;
        (self.regs.fp, self.regs.pc) = (fp, 0);
        Ok(())
    }
}

/// An error object for `fault`.
pub(crate) fn condition<'gc>(mc: &Mutation<'gc>, fault: Fault, message: Value<'gc>, irritants: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Value::object(mc, Condition::new(mc, mc.frozen(fault)?, message, irritants)?))
}

/// The elements of the proper list `list`.
pub(crate) fn list<'gc>(mc: &Mutation<'gc>, mut list: Value<'gc>) -> Result<Vec<Value<'gc>>, Fault> {
    let mut items = Vec::new();
    while let Some(pair) = Pair::of(list) {
        items.push(pair.head(mc));
        list = pair.tail(mc);
    }
    if list != Value::NIL {
        return Err(Fault::WrongType);
    }
    Ok(items)
}
