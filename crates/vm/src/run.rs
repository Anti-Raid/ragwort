//! The bytecode execution inner loop. Executes instructions within a borrowed stack frame,
//! delegating any operation that modifies stack segments or continuations to the outer loop in
//! `machine.rs`.

use std::convert::Infallible;

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Frame, Gc, Mutation, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::frame::{self, ARGS, CLOSURE, Kept, Link, MAX_PARAMS, SAVED_MARKS, Shape};
use crate::op::Fuel;
use crate::module::{Deferred, HostArgs, HostContext, HostDef, Reply};
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Guard, ModuleFields, MultiValue, MultiValueFields, Task, TaskFields};
use crate::prompts::{self, handler_key};
use crate::{Context, Control, Fault, Op, Request};

/// The maximum number of arguments a call can pass directly in registers; arguments and the
/// subsequent frame link occupy the remainder of the frame window.
pub(crate) const MAX_ARGS: usize = WINDOW - 2;

/// Virtual machine registers preserved between invocations of the inner execution loop (frame
/// pointer, program counter, and accumulator).
pub(crate) struct Regs<'gc> {
    pub(crate) fp: usize,
    pub(crate) pc: usize,
    pub(crate) acc: Value<'gc>,
}

/// The reason the inner execution loop suspended or exited.
pub(crate) enum Exit<'gc> {
    Paused,
    Fault(Fault),
    /// A closure call whose target frame at `callee` exceeds the remaining capacity of the current stack
    /// segment.
    Overflow { callee: usize, argc: u8, rest: Value<'gc> },
    Underflow,
    /// An invocation of a non-closure procedure located in register `base`, passing `argc` following
    /// registers and elements of `rest` as arguments.
    Call { base: u8, argc: u8, rest: Value<'gc>, tail: bool },
    /// A runtime request operation with `args` register arguments starting at `base` (with the last
    /// argument spread as a list if `spread` is true).
    Request { base: u8, args: u8, request: Request, spread: bool, tail: bool },
    /// A host function call initiated at register `base` that requested an operation requiring outer
    /// loop handling (such as raising or deferring).
    Host { base: u8, tail: bool, then: HostThen<'gc> },
}

/// The deferred action or exception requested by a host function. Deferral payload data is stored in
/// the slot provided to [`exec`], keeping [`Exit`] lightweight and avoiding drop overhead on every
/// call.
pub(crate) enum HostThen<'gc> {
    Raise(Value<'gc>),
    Defer,
}

impl From<Fault> for Exit<'_> {
    fn from(fault: Fault) -> Self {
        Exit::Fault(fault)
    }
}

/// Executes bytecode instructions until stack reconfiguration is required, fuel is exhausted, or a
/// fault occurs.
///
/// Both this function and [`Run::go`] are marked `#[inline(always)]` into the machine's loop to
/// avoid spilling register state across instructions and doubling call dispatch overhead.
#[inline(always)]
pub(crate) fn exec<'s, 'gc>(mc: &'s Mutation<'gc>, stack: &'s Stack, task: Gc<'gc, Task>, regs: &mut Regs<'gc>, fuel: &mut Fuel, deferred: &'s mut Option<Deferred>) -> Exit<'gc> {
    let mut run = match Run::new(mc, stack, task, regs, *fuel, deferred) {
        Ok(run) => run,
        Err(fault) => return Exit::Fault(fault),
    };
    let Err(exit) = run.go();
    (regs.fp, regs.pc, regs.acc, *fuel) = (run.fp, run.pc, run.cx.acc, run.cx.fuel);
    exit
}

/// Represents an invocation of the procedure at register `base`, passing `argc` consecutive
/// registers and the `rest` list as arguments.
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

/// State of the inner execution loop. Step methods return `Err(Exit)` to break out of the instruction
/// loop via `?`.
struct Run<'s, 'gc> {
    cx: Context<'s, 'gc>,
    stack: &'s Stack,
    /// The active closure's bytecode object, instruction slice, lazily loaded module host functions
    /// table, and next program counter.
    code: Gc<'gc, Bytecode>,
    ops: &'gc [Op],
    hosts: Option<&'gc [&'static HostDef]>,
    /// Mutable reference where a deferred host function stores its suspension data.
    deferred: &'s mut Option<Deferred>,
    pc: usize,
    /// The base offset of the active frame on the segment, and the slot offset of its return link.
    fp: usize,
    link: u8,
    /// The maximum frame pointer offset that can fit within the current stack segment.
    limit: usize,
}

impl<'s, 'gc> Run<'s, 'gc> {
    fn new(mc: &'s Mutation<'gc>, stack: &'s Stack, task: Gc<'gc, Task>, regs: &Regs<'gc>, fuel: Fuel, deferred: &'s mut Option<Deferred>) -> Result<Self, Fault> {
        let frame = stack.frame(mc, regs.fp).ok_or(Fault::Malformed)?;
        let closure = frame.get(CLOSURE).downcast::<Closure>(mc).ok_or(Fault::Malformed)?;
        let code = closure.code(mc).ok_or(Fault::Malformed)?;
        let (ops, constants, link) = load(mc, code)?;
        Ok(Run {
            cx: Context { mc, task, frame, constants, upvalues: closure.items(mc), acc: regs.acc, fuel },
            stack,
            code,
            ops,
            hosts: None,
            deferred,
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
                    self.pc = self.pc.checked_add_signed(offset as isize).ok_or(Fault::Malformed)?;
                    // Advance the program counter past the jump before pausing so branch condition intrinsics (which
                    // may trigger GC steps) are not re-evaluated upon resuming.
                    if self.cx.fuel.run == 0 {
                        self.cx.fuel.rest = self.cx.fuel.rest.saturating_sub(1);
                        return Err(Exit::Paused);
                    }
                    self.cx.fuel.run -= 1;
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

    /// Deducts a unit of fuel for the fetched call or jump instruction. If fuel is exhausted, pauses
    /// before executing the instruction so subsequent runs resume directly from it.
    #[inline(always)]
    fn charge(&mut self) -> Result<(), Exit<'gc>> {
        if self.cx.fuel.run == 0 {
            self.pc -= 1;
            return Err(Exit::Paused);
        }
        self.cx.fuel.run -= 1;
        Ok(())
    }

    /// Allocates a new non-tail frame at `call.base` that returns to this point, restoring active
    /// continuation marks if specified. The new frame starts past the current frame's link to prevent
    /// overwriting preserved caller state.
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

    /// Executes a tail call in place of the current frame, causing the callee to return directly to this
    /// frame's caller.
    #[inline(always)]
    fn tail_call(&mut self, call: Call<'gc>) -> Result<(), Exit<'gc>> {
        fits(call)?;
        let closure = self.closure(call, true)?;
        let frame = self.cx.frame;
        let link = frame.get(self.link);
        (0..=call.argc).for_each(|i| frame.set(CLOSURE + i, frame.get(call.base + i)));
        self.enter(frame, self.fp, closure, call, link)
    }

    /// Resolves the target closure of `call`; any non-closure target exits to the outer loop for
    /// invocation.
    #[inline(always)]
    fn closure(&self, call: Call<'gc>, tail: bool) -> Result<Gc<'gc, Closure>, Exit<'gc>> {
        let (base, argc, rest) = (call.base, call.argc, call.rest);
        self.cx.frame.get(base).downcast::<Closure>(self.cx.mc).ok_or(Exit::Call { base, argc, rest, tail })
    }

    /// Binds arguments for `closure` in `frame` at `fp`, records its return `link`, and begins executing
    /// its bytecode.
    #[inline(always)]
    fn enter(&mut self, frame: Frame<'s, 'gc>, fp: usize, closure: Gc<'gc, Closure>, call: Call<'gc>, link: Value<'gc>) -> Result<(), Exit<'gc>> {
        let mc = self.cx.mc;
        let code = closure.code(mc).ok_or(Fault::Malformed)?;
        let arity = code.arity(mc);
        if let Err(fault) = bind(mc, frame, arity, call.argc, call.rest, &mut self.cx.fuel) {
            // Because a tail call overwrites the current frame with the callee, write the return link
            // immediately so fault unwinding finds a valid linkage.
            frame.set(frame::link_slot(arity), link);
            return Err(fault.into());
        }
        self.switch(closure, code)?;
        frame.set(self.link, link);
        (self.cx.frame, self.fp, self.pc) = (frame, fp, 0);
        Ok(())
    }

    /// Switches execution context to `closure` with bytecode `code`. Avoids reloading bytecode metadata
    /// when entering the same code (such as during self-recursive calls).
    #[inline(always)]
    fn switch(&mut self, closure: Gc<'gc, Closure>, code: Gc<'gc, Bytecode>) -> Result<(), Fault> {
        if code != self.code {
            (self.ops, self.cx.constants, self.link) = load(self.cx.mc, code)?;
            (self.code, self.hosts) = (code, None);
        }
        self.cx.upvalues = closure.items(self.cx.mc);
        Ok(())
    }

    /// Returns to the caller designated by the frame's link, or exits the inner loop with
    /// `Exit::Underflow` if returning from the bottom frame.
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
        self.switch(caller, caller.code(mc).ok_or(Fault::Malformed)?)?;
        (self.cx.frame, self.pc) = (frame, pc);
        Ok(())
    }

    /// Invokes module host function `host` using `args` registers starting at `base`, handling its reply.
    /// Marked `#[inline(never)]` because the indirect function call dominates execution cost.
    #[inline(never)]
    fn host(&mut self, base: u8, args: u8, host: u32, tail: bool) -> Result<(), Exit<'gc>> {
        let mc = self.cx.mc;
        let hosts = match self.hosts {
            Some(hosts) => hosts,
            None => *self.hosts.insert(self.code.module(mc).and_then(|m| m.hosts(mc)).map_or(&[][..], |h| &h[..])),
        };
        let def = *hosts.get(host as usize).ok_or(Fault::Malformed)?;
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
            Reply::Defer(data) => {
                *self.deferred = Some(Deferred::new(data));
                Err(Exit::Host { base, tail, then: HostThen::Defer })
            }
        }
    }

    /// Optimizes `apply` and `apply-values` directly into calls by spreading the final list or
    /// [`MultiValue`]. Non-tail invocations of `with-mark`, `with-exception-handler`, or `guard` set
    /// continuation marks in the callee's frame window (preserving previous marks beneath it for return
    /// restoration). All other requests exit to the outer loop.
    #[inline(always)]
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Result<(), Exit<'gc>> {
        let frame = self.cx.frame;
        let call = match request {
            // An unspread `(apply f x ... list)` call is already laid out as a call frame starting at `base`, with
            // the trailing list ready to spread.
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

    /// Performs a non-tail marked call for `with-mark`, `with-exception-handler`, or `guard`. Sets the
    /// active mark, offsets the new frame by `SAVED_MARKS` past `base` to save previous marks, and stores
    /// guard state below the frame. Marked `#[inline(never)]` to prevent bloat in the common call path.
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

/// Validates that a call's procedure slot and arguments fit within the current frame window,
/// returning `Fault::Malformed` otherwise.
#[inline(always)]
fn fits(call: Call<'_>) -> Result<(), Fault> {
    if usize::from(call.base) + usize::from(ARGS) + usize::from(call.argc) > WINDOW {
        return Err(Fault::Malformed);
    }
    Ok(())
}

/// Loads a closure's instruction slice, constant table, and return link slot offset from its
/// bytecode.
#[inline(always)]
fn load<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>) -> Result<(&'gc [Op], Constants<'gc>, u8), Fault> {
    let ops = code.ops(mc).ok_or(Fault::Malformed)?;
    let link = frame::link_slot(code.arity(mc));
    Ok((ops, Constants::of(code.constants(mc)).ok_or(Fault::Malformed)?, link))
}

/// Binds `argc` register arguments starting at `ARGS` followed by elements of `rest` to match `arity`.
/// If allocating the rest list triggers a GC step threshold, the run will pause at the next call or
/// jump.
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

/// Calculates the count of required parameters and the total number of fixed register parameters
/// before the rest argument list.
fn counts(shape: Shape) -> Result<(u8, u8), Fault> {
    let fixed = u8::try_from(shape.required + shape.optional)
        .ok()
        .filter(|&n| usize::from(n) + usize::from(shape.rest) <= MAX_ARGS)
        .ok_or(Fault::Malformed)?;
    Ok((shape.required as u8, fixed))
}

/// Binds arguments for procedures with more parameters than `MAX_PARAMS`: places the first `MAX_PARAMS
/// - 1` arguments into registers and collects remaining arguments into a rest list in the final
/// register.
#[inline(never)]
fn bind_spread<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, shape: Shape, mut argc: u8, mut rest: Value<'gc>) -> Result<(), Fault> {
    // Procedures with optional parameters are constrained by the compiler to fit within `MAX_PARAMS`, so
    // optional parameters here indicate malformed bytecode.
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

/// Binds arguments when trailing arguments are provided as a [`MultiValue`] object from
/// `apply-values`.
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
