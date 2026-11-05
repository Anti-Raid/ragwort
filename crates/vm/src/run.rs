//! The inner loop: runs instructions against a frame of the stack, which it borrows, so it
//! hands anything that changes the stack to the outer loop in `machine.rs`.

use std::convert::Infallible;

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::frame::{self, ARGS, CLOSURE, Link, MAX_PARAMS};
use crate::op::Fuel;
use crate::objects::{BytecodeFields, Closure, ClosureFields};
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
pub(crate) fn exec<'s, 'gc>(mc: &'s Mutation<'gc>, stack: &'s Stack, regs: &mut Regs<'gc>, fuel: &mut Fuel) -> Exit<'gc> {
    let mut run = match Run::new(mc, stack, regs, *fuel) {
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
    fn new(mc: &'s Mutation<'gc>, stack: &'s Stack, regs: &Regs<'gc>, fuel: Fuel) -> Result<Self, Fault> {
        let frame = stack.frame(mc, regs.fp).ok_or(Fault::Malformed)?;
        let (ops, constants, upvalues, link) = load(mc, frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?)?;
        Ok(Run {
            cx: Context { mc, frame, constants, upvalues, acc: regs.acc, fuel },
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
                    self.call(Call::new(base, args))?;
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

    /// Calls in a new frame at `call.base`, which returns here. The frame must start past this
    /// one's link, so it overwrites nothing this frame keeps.
    #[inline(always)]
    fn call(&mut self, call: Call<'gc>) -> Result<(), Exit<'gc>> {
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
        let link = Link { pc: self.pc, base: call.base }.value().ok_or(Fault::Malformed)?;
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
        bind(mc, frame, closure.code(mc).ok_or(Fault::Malformed)?.arity(mc), call.argc, call.rest, &mut self.cx.fuel)?;
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
        let Link { pc, base } = Link::of(self.cx.frame.get(self.link)).ok_or(Fault::Malformed)?;
        if base == 0 {
            return Err(Exit::Underflow);
        }
        self.fp = self.fp.checked_sub(usize::from(base)).ok_or(Fault::Malformed)?;
        let frame = self.stack.frame(mc, self.fp).ok_or(Fault::Malformed)?;
        let caller = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        (self.ops, self.cx.constants, self.cx.upvalues, self.link) = load(mc, caller)?;
        (self.cx.frame, self.pc) = (frame, pc);
        Ok(())
    }

    /// Makes `apply` a call, as it's laid out as one, with the list to spread last. The outer
    /// loop carries out the other requests.
    #[inline(always)]
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Result<(), Exit<'gc>> {
        let frame = self.cx.frame;
        let call = match request {
            // (apply f x ... list) is already laid out as a call at `base`, with the list spread.
            Request::Apply if !spread => Call { base, argc: args - 2, rest: frame.get(base + args - 1) },
            _ => return Err(Exit::Request { base, args, request, spread, tail }),
        };
        if tail { self.tail_call(call) } else { self.call(call) }
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
    if arity.unsigned_abs() > u64::from(MAX_PARAMS) {
        return bind_spread(mc, frame, arity, argc, rest);
    }
    let variadic = arity < 0;
    let required = if variadic { -(arity + 1) } else { arity };
    let required = u8::try_from(required)
        .ok()
        .filter(|&n| usize::from(n) + usize::from(variadic) <= MAX_ARGS)
        .ok_or(Fault::Malformed)?;
    while argc < required {
        let pair = Pair::of(rest).ok_or(if rest == Value::NIL { Fault::Arity } else { Fault::WrongType })?;
        frame.set(ARGS + argc, pair.head(mc));
        (rest, argc) = (pair.tail(mc), argc + 1);
    }
    if !variadic {
        return match () {
            () if argc > required || Pair::of(rest).is_some() => Err(Fault::Arity),
            () if rest != Value::NIL => Err(Fault::WrongType),
            () => Ok(()),
        };
    }
    let pairs = Pairs::new(mc);
    for i in (required..argc).rev() {
        rest = pairs.cons(frame.get(ARGS + i), rest)?.value(mc);
    }
    frame.set(ARGS + required, rest);
    Ok(())
}

/// Binds as [`bind`] does, for code with more parameters than [`MAX_PARAMS`]: the first
/// `MAX_PARAMS - 1` arguments in their registers, then a list of the others in the last.
#[inline(never)]
fn bind_spread<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, arity: i64, mut argc: u8, mut rest: Value<'gc>) -> Result<(), Fault> {
    let variadic = arity < 0;
    let slots = arity.unsigned_abs();
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
