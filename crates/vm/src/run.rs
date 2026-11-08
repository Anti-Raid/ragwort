//! The inner loop: runs instructions against a frame of the stack, which it borrows, so it
//! hands anything that changes the stack to the outer loop in `machine.rs`.

use std::convert::Infallible;

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::frame::{self, ARGS, CLOSURE, Kept, Link, MAX_PARAMS, SAVED_MARKS, Shape};
use crate::op::Fuel;
use crate::module::{Deferred, HostArgs, HostContext, Reply};
use crate::objects::{BytecodeFields, Closure, ClosureFields, Guard, ModuleFields, MultiValue, MultiValueFields, Task, TaskFields};
use crate::prompts::{self, handler_key};
use crate::{Context, Control, Fault, Op, Request};

/// The most arguments a call passes: they and the link after them fill the frame.
pub(crate) const MAX_ARGS: usize = WINDOW - 2;

/// The registers the inner loop leaves for the next stretch of it.
pub(crate) struct Regs<'gc> {
    pub(crate) fp: usize,
    pub(crate) pc: usize,
    pub(crate) acc: Value<'gc>,
}

/// Why the inner loop stopped.
pub(crate) enum Exit<'gc> {
    Paused,
    Fault(Fault),
    /// A call, of a closure, whose frame, at `callee`, doesn't fit in the segment.
    Overflow { callee: usize, argc: u8, rest: Value<'gc> },
    Underflow,
    /// A call of something other than a closure, in register `base`, with the `argc`
    /// registers after it and the elements of `rest` as its arguments.
    Call { base: u8, argc: u8, rest: Value<'gc>, tail: bool },
    /// A request on the `args` registers from `base`, the last a list of more if `spread`.
    Request { base: u8, args: u8, request: Request, spread: bool, tail: bool },
    /// What a host function called with a call laid out at `base` asked for that the loop
    /// can't do.
    Host { base: u8, tail: bool, then: HostThen<'gc> },
}

/// What a host function's call leaves the loop for.
pub(crate) enum HostThen<'gc> {
    Raise(Value<'gc>),
    Defer(Deferred),
}

impl From<Fault> for Exit<'_> {
    fn from(fault: Fault) -> Self {
        Exit::Fault(fault)
    }
}

/// Runs instructions until one needs the stack changed, the run's fuel runs out, or one faults.
///
/// It and [`Run::go`] are inlined into the machine's loop: compiled as a function of their own,
/// the loop's registers spilled on every instruction, and calls took twice as long.
#[inline(always)]
pub(crate) fn exec<'s, 'gc>(mc: &'s Mutation<'gc>, stack: &'s Stack, task: Gc<'gc, Task>, regs: &mut Regs<'gc>, fuel: &mut Fuel) -> Exit<'gc> {
    let mut run = match Run::new(mc, stack, task, regs, *fuel) {
        Ok(run) => run,
        Err(fault) => return Exit::Fault(fault),
    };
    let Err(exit) = run.go();
    (regs.fp, regs.pc, regs.acc, *fuel) = (run.fp, run.pc, run.cx.acc, run.cx.fuel);
    exit
}

/// A call of the procedure in register `base`, with the `argc` registers after it as its
/// arguments, then the elements of the list `rest`.
#[derive(Clone, Copy)]
struct Call<'gc> {
    base: u8,
    argc: u8,
    rest: Value<'gc>,
}

impl<'gc> Call<'gc> {
    fn new(base: u8, argc: u8) -> Self {
        Call { base, argc, rest: Value::NIL }
    }
}

/// The inner loop's state. Every step returns `Err` to leave the loop, so `?` does it.
struct Run<'s, 'gc> {
    cx: Context<'s, 'gc>,
    stack: &'s Stack,
    /// The current closure's code, and the instruction to run next.
    ops: &'gc [Op],
    pc: usize,
    /// Where the current frame starts, and where its link is in it.
    fp: usize,
    link: u8,
    /// The highest `fp` a frame fits at in this segment.
    limit: usize,
}

impl<'s, 'gc> Run<'s, 'gc> {
    fn new(mc: &'s Mutation<'gc>, stack: &'s Stack, task: Gc<'gc, Task>, regs: &Regs<'gc>, fuel: Fuel) -> Result<Self, Fault> {
        let frame = stack.frame(mc, regs.fp).ok_or(Fault::Malformed)?;
        let (ops, constants, upvalues, link) = load(mc, frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?)?;
        Ok(Run {
            cx: Context { mc, task, frame, constants, upvalues, acc: regs.acc, fuel },
            stack,
            ops,
            pc: regs.pc,
            fp: regs.fp,
            link,
            limit: stack.segment(mc).len(mc).saturating_sub(WINDOW),
        })
    }

    #[inline(always)]
    fn go(&mut self) -> Result<Infallible, Exit<'gc>> {
        loop {
            let op = *self.ops.get(self.pc).ok_or(Fault::Malformed)?;
            self.pc += 1;
            match op.step(&mut self.cx)? {
                Control::Next => {}
                Control::Jump(offset) => {
                    self.charge()?;
                    self.pc = self.pc.checked_add_signed(offset as isize).ok_or(Fault::Malformed)?;
                }
                Control::Return => self.ret()?,
                Control::Call { base, args } => {
                    self.charge()?;
                    self.call(Call::new(base, args), false)?;
                }
                Control::TailCall { base, args } => {
                    self.charge()?;
                    self.tail_call(Call::new(base, args))?;
                }
                Control::CallRequest { base, args, request, spread } => {
                    self.charge()?;
                    self.request(base, args, request, spread, false)?;
                }
                Control::TailCallRequest { base, args, request, spread } => {
                    self.charge()?;
                    self.request(base, args, request, spread, true)?;
                }
                Control::Host { base, args, host, tail } => {
                    self.charge()?;
                    self.host(base, args, host, tail)?;
                }
            }
        }
    }

    /// Spends a unit of fuel on the call or jump just fetched. With none left, it stops before
    /// the instruction, which hasn't done anything yet, so the next run starts with it.
    #[inline(always)]
    fn charge(&mut self) -> Result<(), Exit<'gc>> {
        if self.cx.fuel.run == 0 {
            self.pc -= 1;
            return Err(Exit::Paused);
        }
        self.cx.fuel.run -= 1;
        Ok(())
    }

    /// Calls in a new frame at `call.base`, which returns here, putting back this frame's marks
    /// if it set `marks` for it. The frame must start past this one's link, so it overwrites
    /// nothing this frame keeps.
    #[inline(always)]
    fn call(&mut self, call: Call<'gc>, marks: bool) -> Result<(), Exit<'gc>> {
        fits(call)?;
        if call.base <= self.link {
            return Err(Fault::Malformed.into());
        }
        let closure = self.closure(call, false)?;
        let callee = self.fp + usize::from(call.base);
        if callee > self.limit {
            return Err(Exit::Overflow { callee, argc: call.argc, rest: call.rest });
        }
        let frame = self.stack.frame(self.cx.mc, callee).ok_or(Fault::Malformed)?;
        let link = Link { pc: self.pc, base: call.base, marks }.value().ok_or(Fault::Malformed)?;
        self.enter(frame, callee, closure, call, link)
    }

    /// Calls in place of the current frame, so the callee returns to this frame's caller.
    #[inline(always)]
    fn tail_call(&mut self, call: Call<'gc>) -> Result<(), Exit<'gc>> {
        fits(call)?;
        let closure = self.closure(call, true)?;
        let frame = self.cx.frame;
        let link = frame.get(self.link);
        (0..=call.argc).for_each(|i| frame.set(CLOSURE + i, frame.get(call.base + i)));
        self.enter(frame, self.fp, closure, call, link)
    }

    /// The closure `call` calls. Anything else is called by the outer loop.
    #[inline(always)]
    fn closure(&self, call: Call<'gc>, tail: bool) -> Result<Gc<'gc, Closure>, Exit<'gc>> {
        let (base, argc, rest) = (call.base, call.argc, call.rest);
        self.cx.frame.get(base).downcast::<Closure>(self.cx.mc).ok_or(Exit::Call { base, argc, rest, tail })
    }

    /// Binds the arguments of `closure`, in `frame`, at `fp`, writes its `link`, and starts its
    /// code.
    #[inline(always)]
    fn enter(&mut self, frame: Frame<'s, 'gc>, fp: usize, closure: Gc<'gc, Closure>, call: Call<'gc>, link: Value<'gc>) -> Result<(), Exit<'gc>> {
        let mc = self.cx.mc;
        let arity = closure.code(mc).ok_or(Fault::Malformed)?.arity(mc);
        if let Err(fault) = bind(mc, frame, arity, call.argc, call.rest, &mut self.cx.fuel) {
            // A tail call's frame is the callee's now, so a fault finds its link where it looks.
            frame.set(frame::link_slot(arity), link);
            return Err(fault.into());
        }
        (self.ops, self.cx.constants, self.cx.upvalues, self.link) = load(mc, closure)?;
        frame.set(self.link, link);
        (self.cx.frame, self.fp, self.pc) = (frame, fp, 0);
        Ok(())
    }

    /// Goes back to the caller the frame's link names, or out of the loop if it's the bottom
    /// frame.
    #[inline(always)]
    fn ret(&mut self) -> Result<(), Exit<'gc>> {
        let mc = self.cx.mc;
        let Link { pc, base, marks } = Link::of(self.cx.frame.get(self.link)).ok_or(Fault::Malformed)?;
        if base == 0 {
            return Err(Exit::Underflow);
        }
        self.fp = self.fp.checked_sub(usize::from(base)).ok_or(Fault::Malformed)?;
        let frame = self.stack.frame(mc, self.fp).ok_or(Fault::Malformed)?;
        if marks {
            self.cx.task.set_attachments(mc, frame.get(Kept::under(usize::from(base), 0)?.marks as u8));
        }
        let caller = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        (self.ops, self.cx.constants, self.cx.upvalues, self.link) = load(mc, caller)?;
        (self.cx.frame, self.pc) = (frame, pc);
        Ok(())
    }

    /// Calls host function `host` of the code's module on the `args` registers from `base`, and
    /// goes on as it replies. Out of line, as the call through its function is the most of what
    /// it costs.
    #[inline(never)]
    fn host(&mut self, base: u8, args: u8, host: u32, tail: bool) -> Result<(), Exit<'gc>> {
        let mc = self.cx.mc;
        let module = self.cx.frame.get(CLOSURE).downcast::<Closure>(mc).and_then(|c| c.code(mc)).and_then(|code| code.module(mc));
        let def = module.and_then(|m| m.hosts(mc)).and_then(|hosts| hosts.get(host as usize)).ok_or(Fault::Malformed)?;
        if !def.takes(usize::from(args)) {
            return Err(Fault::Arity.into());
        }
        let reply = (def.function)(&mut HostContext { mc, fuel: &mut self.cx.fuel }, HostArgs::registers(self.cx.frame, base, args))?;
        if mc.step_due() {
            self.cx.fuel.pause();
        }
        match reply {
            Reply::Value(value) => {
                self.cx.acc = value;
                if tail { self.ret() } else { Ok(()) }
            }
            Reply::Call(procedure, args) => {
                let call = Call { base, argc: 0, rest: args };
                fits(call)?;
                self.cx.frame.set(base, procedure);
                if tail { self.tail_call(call) } else { self.call(call, false) }
            }
            Reply::Raise(raised) => Err(Exit::Host { base, tail, then: HostThen::Raise(raised) }),
            Reply::Defer(data) => Err(Exit::Host { base, tail, then: HostThen::Defer(Deferred::new(data)) }),
        }
    }

    /// Makes `apply` or `apply-values` a call, as it's laid out as one, with the list or
    /// [`MultiValue`] to spread last, and a `with-mark`, `with-exception-handler` or `guard` of a
    /// closure that isn't in tail position one that sets the mark, as Chez sets an attachment for
    /// a call: the frame keeps its marks under the callee's frame, for the return to put back.
    /// The outer loop carries out the other requests.
    #[inline(always)]
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Result<(), Exit<'gc>> {
        let frame = self.cx.frame;
        let call = match request {
            // (apply f x ... list) is already laid out as a call at `base`, with the list spread.
            Request::Apply if !spread => {
                let rest = frame.get(base + args - 1);
                if rest.downcast::<MultiValue>(self.cx.mc).is_some() {
                    return Err(Fault::WrongType.into());
                }
                Call { base, argc: args - 2, rest }
            }
            Request::ApplyValues if !spread => {
                let v = frame.get(base + 1);
                if v.downcast::<MultiValue>(self.cx.mc).is_some() {
                    Call { base, argc: 0, rest: v }
                } else {
                    Call { base, argc: 1, rest: Value::NIL }
                }
            }
            Request::WithMark if !spread && !tail && args >= 3 => return self.marked_call(base, args, request),
            Request::WithHandler | Request::Guard if !spread && !tail && args == 2 => return self.marked_call(base, args, request),
            _ => return Err(Exit::Request { base, args, request, spread, tail }),
        };
        if tail { self.tail_call(call) } else { self.call(call, false) }
    }

    /// Calls the closure of a `with-mark`, or the thunk of a `with-exception-handler` or a
    /// `guard`, which isn't in tail position, with the mark set, in a frame [`SAVED_MARKS`] past
    /// `base`, if it takes the arguments as they are; a guard is kept in the register under the
    /// frame. Out of line, as it's rare next to calls, and inlined, it slowed them.
    #[inline(never)]
    fn marked_call(&mut self, base: u8, args: u8, request: Request) -> Result<(), Exit<'gc>> {
        let (mc, frame, task) = (self.cx.mc, self.cx.frame, self.cx.task);
        let (procedure, argc) = match request {
            Request::WithMark => (frame.get(base + 2), args - 3),
            Request::Guard => (frame.get(base), 0),
            _ => (frame.get(base + 1), 0),
        };
        let call = Call { base: base + SAVED_MARKS, argc, rest: Value::NIL };
        fits(call)?;
        let takes = procedure.downcast::<Closure>(mc).and_then(|c| c.code(mc)).is_some_and(|code| code.arity(mc) == i64::from(argc));
        if !takes || self.fp + usize::from(call.base) > self.limit {
            return Err(Exit::Request { base, args, request, spread: false, tail: false });
        }
        let (pairs, saved) = (Pairs::new(mc), task.attachments(mc));
        let (key, value, guard) = match request {
            Request::WithMark => (frame.get(base), frame.get(base + 1), None),
            _ => {
                let handler = if request == Request::Guard {
                    Value::object(mc, Guard::new(mc, frame.get(base + 1), task.winders(mc)).map_err(Fault::from)?)
                } else {
                    frame.get(base)
                };
                let handlers = prompts::mark(mc, task, handler_key(), Value::NIL)?;
                let guard = (request == Request::Guard).then_some(handler);
                (handler_key(), pairs.cons(handler, handlers).map_err(Fault::from)?.value(mc), guard)
            }
        };
        let mark = pairs.cons(key, value).map_err(Fault::from)?.value(mc);
        let marks = pairs.cons(mark, saved).map_err(Fault::from)?.value(mc);
        let kept = Kept::under(usize::from(call.base), 0)?;
        frame.set(call.base, procedure);
        frame.set(kept.marks as u8, saved);
        if let Some(guard) = guard {
            frame.set(kept.guard as u8, guard);
        }
        task.set_attachments(mc, marks);
        if mc.step_due() {
            self.cx.fuel.pause();
        }
        self.call(call, true)
    }
}

/// Faults unless a call's procedure and arguments are all in the frame.
#[inline(always)]
fn fits(call: Call<'_>) -> Result<(), Fault> {
    if usize::from(call.base) + usize::from(ARGS) + usize::from(call.argc) > WINDOW {
        return Err(Fault::Malformed);
    }
    Ok(())
}

/// A closure's instructions, constants and upvalues, and where its frame's link is.
#[inline(always)]
fn load<'gc>(mc: &Mutation<'gc>, closure: Gc<'gc, Closure>) -> Result<(&'gc [Op], Constants<'gc>, Slots<'gc>, u8), Fault> {
    let code = closure.code(mc).ok_or(Fault::Malformed)?;
    let ops = code.ops(mc).ok_or(Fault::Malformed)?;
    let link = frame::link_slot(code.arity(mc));
    Ok((ops, Constants::of(code.constants(mc)).ok_or(Fault::Malformed)?, closure.items(mc), link))
}

/// Binds `argc` arguments, in the registers from [`ARGS`], then the elements of the list `rest`,
/// to the parameters of code that takes `arity`. If the list it makes of the rest makes the step
/// due, the run pauses at its next call or jump.
#[inline(always)]
pub(crate) fn bind<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, arity: i64, argc: u8, rest: Value<'gc>, fuel: &mut Fuel) -> Result<(), Fault> {
    if arity == i64::from(argc) && argc <= MAX_PARAMS && rest == Value::NIL {
        return Ok(());
    }
    bind_slow(mc, frame, arity, argc, rest)?;
    if mc.step_due() {
        fuel.pause();
    }
    Ok(())
}

#[inline(never)]
fn bind_slow<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, arity: i64, mut argc: u8, mut rest: Value<'gc>) -> Result<(), Fault> {
    if let Some(mv) = rest.downcast::<MultiValue>(mc) {
        return bind_values(mc, frame, arity, argc, mv);
    }
    let shape = Shape::of(arity);
    if shape.slots() > u64::from(MAX_PARAMS) {
        return bind_spread(mc, frame, shape, argc, rest);
    }
    let (required, fixed) = counts(shape)?;
    while argc < fixed {
        let item = match Pair::of(rest) {
            Some(pair) => {
                rest = pair.tail(mc);
                pair.head(mc)
            }
            None if rest != Value::NIL => return Err(Fault::WrongType),
            None if argc < required => return Err(Fault::Arity),
            None => Value::UNSUPPLIED,
        };
        frame.set(ARGS + argc, item);
        argc += 1;
    }
    if !shape.rest {
        return match () {
            () if argc > fixed || Pair::of(rest).is_some() => Err(Fault::Arity),
            () if rest != Value::NIL => Err(Fault::WrongType),
            () => Ok(()),
        };
    }
    let pairs = Pairs::new(mc);
    for i in (fixed..argc).rev() {
        rest = pairs.cons(frame.get(ARGS + i), rest)?.value(mc);
    }
    frame.set(ARGS + fixed, rest);
    Ok(())
}

/// The parameters of `shape` that must have arguments, and those before its rest list, which
/// fit in registers.
fn counts(shape: Shape) -> Result<(u8, u8), Fault> {
    let fixed = u8::try_from(shape.required + shape.optional)
        .ok()
        .filter(|&n| usize::from(n) + usize::from(shape.rest) <= MAX_ARGS)
        .ok_or(Fault::Malformed)?;
    Ok((shape.required as u8, fixed))
}

/// Binds as [`bind`] does, for code with more parameters than [`MAX_PARAMS`]: the first
/// `MAX_PARAMS - 1` arguments in their registers, then a list of the others in the last.
#[inline(never)]
fn bind_spread<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, shape: Shape, mut argc: u8, mut rest: Value<'gc>) -> Result<(), Fault> {
    // The compiler keeps optional parameters to code that takes few enough.
    if shape.optional > 0 {
        return Err(Fault::Malformed);
    }
    let (variadic, slots) = (shape.rest, shape.slots());
    let keep = MAX_PARAMS - 1;
    while argc < keep {
        let pair = Pair::of(rest).ok_or(if rest == Value::NIL { Fault::Arity } else { Fault::WrongType })?;
        frame.set(ARGS + argc, pair.head(mc));
        (rest, argc) = (pair.tail(mc), argc + 1);
    }
    let pairs = Pairs::new(mc);
    for i in (keep..argc).rev() {
        rest = pairs.cons(frame.get(ARGS + i), rest)?.value(mc);
    }
    let (mut count, mut tail) = (0u64, rest);
    while let Some(pair) = Pair::of(tail) {
        (count, tail) = (count + 1, pair.tail(mc));
    }
    if tail != Value::NIL {
        return Err(Fault::WrongType);
    }
    let required = slots - u64::from(variadic) - u64::from(keep);
    if count < required || (!variadic && count > required) {
        return Err(Fault::Arity);
    }
    frame.set(ARGS + keep, rest);
    Ok(())
}

/// Binds as [`bind`] does when `rest` is a [`MultiValue`] from `apply-values`.
fn bind_values<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, arity: i64, mut argc: u8, mv: Gc<'gc, MultiValue>) -> Result<(), Fault> {
    let items = mv.items(mc);
    let shape = Shape::of(arity);
    if shape.slots() > u64::from(MAX_PARAMS) {
        let rest = Pairs::new(mc).list_with_tail((0..items.len()).map(|i| items.get(i)), Value::NIL)?;
        return bind_spread(mc, frame, shape, argc, rest);
    }
    let (required, fixed) = counts(shape)?;
    let mut idx = 0;
    while argc < fixed {
        let item = match () {
            () if idx < items.len() => items.get(idx),
            () if argc < required => return Err(Fault::Arity),
            () => Value::UNSUPPLIED,
        };
        frame.set(ARGS + argc, item);
        (idx, argc) = (idx + 1, argc + 1);
    }
    if !shape.rest {
        if argc > fixed || idx < items.len() {
            return Err(Fault::Arity);
        }
        return Ok(());
    }
    let pairs = Pairs::new(mc);
    let mut rest = pairs.list_with_tail((idx.min(items.len())..items.len()).map(|i| items.get(i)), Value::NIL)?;
    for i in (fixed..argc).rev() {
        rest = pairs.cons(frame.get(ARGS + i), rest)?.value(mc);
    }
    frame.set(ARGS + fixed, rest);
    Ok(())
}
