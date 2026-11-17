//! The bytecode execution inner loop. Executes instructions within a borrowed stack frame,
//! delegating any operation that modifies stack segments or continuations to the outer loop in
//! `machine.rs`.

use std::convert::Infallible;

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Stack, Value, WINDOW, slot};
use ragwort_types::table::Table;
use ragwort_types::pair::{Pair, Pairs};

use crate::frame::{self, ARGS, CLOSURE, Kept, Link, MAX_PARAMS, SAVED_MARKS, Shape};
use crate::op::Fuel;
use crate::module::{Deferred, HostArgs, HostContext, HostDef, Reply};
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Guard, HintsFields, KeywordProcedure, KeywordProcedureFields, ModuleFields, Task, TaskFields};
use crate::prompts::{self, handler_key};
use crate::segments;
use crate::{Context, Control, Fault, Op, Request, coroutine};

/// The maximum number of arguments a call can pass directly in registers; arguments and the
/// subsequent frame link occupy the remainder of the frame window.
pub(crate) const MAX_ARGS: usize = WINDOW - 2;

/// Virtual machine registers preserved between invocations of the inner execution loop (frame
/// pointer, program counter, and accumulator).
pub(crate) struct Regs<'gc> {
    pub(crate) fp: usize,
    pub(crate) pc: usize,
    pub(crate) acc: Value<'gc>,
    /// The list of values a call returned, when `acc` is [`Value::VALUES`]. It is not meaningful otherwise.
    pub(crate) values: Value<'gc>,
    /// The bytecode the inner loop was executing when it last exited, used to find the instruction that raised a fault.
    pub(crate) code: Option<Gc<'gc, Bytecode>>,
}

impl<'gc> Regs<'gc> {
    /// Stores the values in the proper list `list` in the accumulator. A list of one element is stored as that single value.
    pub(crate) fn set_values(&mut self, mc: &Mutation<'gc>, list: Value<'gc>) {
        match Pair::of(list) {
            Some(cell) if cell.tail(mc) == Value::NULL => self.acc = cell.head(mc),
            _ => (self.acc, self.values) = (Value::VALUES, list),
        }
    }

    /// Returns the values in the accumulator as a list.
    pub(crate) fn list(&self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Fault> {
        if self.acc == Value::VALUES {
            return Ok(self.values);
        }
        Ok(Pairs::new(mc).cons(self.acc, Value::NULL)?.value(mc))
    }

    /// Returns the first value in the accumulator, or void if it holds none.
    pub(crate) fn first(&self, mc: &Mutation<'gc>) -> Value<'gc> {
        if self.acc != Value::VALUES {
            return self.acc;
        }
        Pair::of(self.values).map_or(Value::VOID, |cell| cell.head(mc))
    }
}

/// The maximum number of leading arguments for which the inner loop lays out a first-class `apply` as a call.
const LEADING: usize = 4;

/// The maximum number of keywords a procedure can accept for the inner loop to lay out a `keyword-apply` to it as a call.
const KEYWORDS: usize = 8;

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
    (regs.fp, regs.pc, regs.acc, regs.values, *fuel) = (run.fp, run.pc, run.cx.acc, run.cx.values, run.cx.fuel);
    regs.code = Some(run.code);
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
        Call { base, argc, rest: Value::NULL }
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
            cx: Context { mc, task, frame, constants, upvalues: closure.items(mc), acc: regs.acc, values: regs.values, fuel },
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
                Control::CallReceived { base, tail } => {
                    self.charge()?;
                    self.received(base, tail)?;
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
                Control::TableRef { dst, table, key, default, hint } => self.table_ref(dst, table, key, default, hint)?,
                Control::TableSet { dst, table, key, value, hint } => self.table_set(dst, table, key, value, hint)?,
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

    /// Resolves the target closure of `call`. A keyword procedure called without keywords resolves
    /// to its plain closure. Any other non-closure target exits to the outer loop for invocation.
    #[inline(always)]
    fn closure(&self, call: Call<'gc>, tail: bool) -> Result<Gc<'gc, Closure>, Exit<'gc>> {
        match self.cx.frame.get(call.base).downcast::<Closure>(self.cx.mc) {
            Some(closure) => Ok(closure),
            None => self.plain(call, tail),
        }
    }

    /// Resolves a `call` whose target is a keyword procedure to the procedure's plain closure. The
    /// plain closure replaces the keyword procedure in the frame, because a frame's closure register
    /// must hold the closure that runs in it.
    ///
    /// Two calls exit to the outer loop instead, which raises the error and names the keyword
    /// procedure in it. One is a call to a procedure with a required keyword, which has no plain
    /// closure. The other is a call with a number of arguments the plain closure does not take.
    #[inline(never)]
    fn plain(&self, call: Call<'gc>, tail: bool) -> Result<Gc<'gc, Closure>, Exit<'gc>> {
        let (mc, frame) = (self.cx.mc, self.cx.frame);
        let (base, argc, rest) = (call.base, call.argc, call.rest);
        let exit = Exit::Call { base, argc, rest, tail };
        let Some(keyed) = frame.get(base).downcast::<KeywordProcedure>(mc) else { return Err(exit) };
        let plain = keyed.plain(mc);
        let Some(closure) = plain.downcast::<Closure>(mc) else { return Err(exit) };
        let given = Pairs::new(mc).list_len(rest).map(|listed| listed + u64::from(argc));
        let takes = closure.code(mc).zip(given).is_some_and(|(code, given)| Shape::of(code.arity(mc)).takes(given));
        if !takes {
            return Err(exit);
        }
        frame.set(base, plain);
        Ok(closure)
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
            None => *self.hosts.insert(self.code.module(mc).and_then(|module| module.hosts(mc)).map_or(&[][..], |defs| &defs[..])),
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
            // `Value::VALUES` is the multiple-values marker, not a value. If a host returned it, the accumulator would claim a list of values that does not exist.
            Reply::Value(Value::VALUES) => Err(Fault::WrongType.into()),
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

    /// Handles the requests that the inner loop can complete by itself. Every other request exits to
    /// the outer loop.
    ///
    /// - `apply` and `keyword-apply` are laid out as a direct call.
    /// - A non-tail `with-mark`, `with-exception-handler` or `guard` sets its continuation mark and
    ///   calls its procedure in a frame above the saved marks. The return restores the saved marks.
    /// - A `with-mark` or `with-exception-handler` in tail position sets its mark on the current
    ///   frame, if that frame can hold marks.
    /// - A close or reset of a coroutine that has ended completes here.
    ///
    /// Kept out of line. Inlined into the instruction loop, it made every plain call measurably slower.
    #[inline(never)]
    fn request(&mut self, base: u8, args: u8, request: Request, spread: bool, tail: bool) -> Result<(), Exit<'gc>> {
        let frame = self.cx.frame;
        let call = match request {
            // An unspread `(apply f x ... list)` call is already laid out as a call frame starting at `base`, with
            // the trailing list ready to spread.
            Request::Apply if !spread => Call { base, argc: args - 2, rest: frame.get(base + args - 1) },
            // The first-class `apply` procedure passes `f` and the list of its other arguments. In `(apply f list)`
            // that list holds only `list`, so the call is `f` with `list` spread. Leading arguments are put in
            // front of it. A last argument that is not a proper list exits to the outer loop.
            Request::Apply if spread && args == 2 => match self.applied(frame.get(base + 1))? {
                Some(rest) => Call { base, argc: 0, rest },
                None => return Err(Exit::Request { base, args, request, spread, tail }),
            },
            Request::KeywordApply if !spread => match self.keyword_call(base, args) {
                Some(call) => call,
                None => return Err(Exit::Request { base, args, request, spread, tail }),
            },
            Request::WithMark if !spread && !tail && args >= 3 => return self.marked_call(base, args, request),
            Request::WithMark | Request::WithHandler if !spread && tail => match self.tail_mark(base, args, request)? {
                Some(call) => call,
                None => return Err(Exit::Request { base, args, request, spread, tail }),
            },
            Request::WithHandler | Request::Guard | Request::GuardQuiet if !spread && !tail && args == 2 => return self.marked_call(base, args, request),
            Request::Close | Request::Reset if !spread => match self.ended(base, args, request) {
                Some(value) => {
                    self.cx.acc = value;
                    return if tail { self.ret() } else { Ok(()) };
                }
                None => return Err(Exit::Request { base, args, request, spread, tail }),
            },
            _ => return Err(Exit::Request { base, args, request, spread, tail }),
        };
        if tail { self.tail_call(call) } else { self.call(call, false) }
    }

    /// Returns the hint words of the running code and the index of word `hint` in them. Fails with [`Fault::Malformed`] if the code has no such word.
    fn hints(&self, hint: u16) -> Result<(Slots<'gc, slot::u64>, usize), Fault> {
        let hints = self.code.hints(self.cx.mc).ok_or(Fault::Malformed)?.items(self.cx.mc);
        if usize::from(hint) < hints.len() { Ok((hints, usize::from(hint))) } else { Err(Fault::Malformed) }
    }

    /// Reads a table entry for [`Op::TableRefHinted`]. The entry position stored in the hint word is
    /// tried first. If the key is not at that position, the table is searched, and the hint word is
    /// set to the position where the key was found.
    #[inline(never)]
    fn table_ref(&mut self, dst: u8, table: u8, key: u8, default: u8, hint: u16) -> Result<(), Fault> {
        let (mc, frame) = (self.cx.mc, self.cx.frame);
        let (table, key) = (Table::of(frame.get(table)).ok_or(Fault::WrongType)?, frame.get(key));
        let (hints, slot) = self.hints(hint)?;
        if let Some(value) = table.get_at(mc, key, hints.get(slot) as usize) {
            frame.set(dst, value);
            return Ok(());
        }
        self.charge_rebuild(table)?;
        let value = match table.find(mc, key)? {
            Some((position, value)) => {
                hints.set(mc, slot, position as u64);
                value
            }
            None => frame.get(default),
        };
        // The search can allocate. A table rebuilds a stale index, and an external table caches each value it reads from its host.
        if mc.step_due() {
            self.cx.fuel.pause();
        }
        frame.set(dst, value);
        Ok(())
    }

    /// Writes a table entry for [`Op::TableSetHinted`]. The hint word is used as in [`Run::table_ref`].
    #[inline(never)]
    fn table_set(&mut self, dst: u8, table: u8, key: u8, value: u8, hint: u16) -> Result<(), Fault> {
        let (mc, frame) = (self.cx.mc, self.cx.frame);
        let (table, key, value) = (Table::of(frame.get(table)).ok_or(Fault::WrongType)?, frame.get(key), frame.get(value));
        let (hints, slot) = self.hints(hint)?;
        if !table.set_at(mc, key, hints.get(slot) as usize, value) {
            self.charge_rebuild(table)?;
            // A table in the arena keeps each entry at a fixed position, so the next write finds this entry through the hint. An external table returns no position.
            if let Some(position) = table.set_finding(mc, key, value)? {
                hints.set(mc, slot, position as u64);
            }
            if mc.step_due() {
                self.cx.fuel.pause();
            }
        }
        frame.set(dst, Value::VOID);
        Ok(())
    }

    /// Spends the fuel for rebuilding the index of `table`, if the next access will rebuild it. See `Table::is_stale`.
    fn charge_rebuild(&mut self, table: Table<'gc>) -> Result<(), Fault> {
        if table.is_stale(self.cx.mc) {
            self.cx.fuel.spend(table.len(self.cx.mc) as u64 / crate::equal::PER_FUEL)?;
        }
        Ok(())
    }

    /// Closes or resets the coroutine in register `base` if it has ended. Such a coroutine holds nothing,
    /// so there is nothing to unwind and no task to switch to. Returns the result of the request, which
    /// is void for a close and the coroutine for a reset. Returns `None` if the outer loop has to
    /// handle the request.
    #[inline(never)]
    fn ended(&mut self, base: u8, args: u8, request: Request) -> Option<Value<'gc>> {
        let (mc, frame) = (self.cx.mc, self.cx.frame);
        let coroutine = frame.get(base);
        let task = coroutine::of(mc, coroutine)?;
        if !matches!(task.state(mc), coroutine::DEAD | coroutine::FAILED) {
            return None;
        }
        if request == Request::Close {
            return if args == 1 { Some(Value::VOID) } else { None };
        }
        let thunk = frame.get(base + 1);
        if args != 2 || !crate::intrinsic::is_procedure(mc, thunk) {
            return None;
        }
        coroutine::reset(mc, task, thunk);
        Some(coroutine)
    }

    /// Calls the procedure in register `base` with the values in the accumulator, which the last call
    /// returned. One value is moved into the first argument register. A list of values becomes the
    /// call's rest list, and argument binding spreads it.
    #[inline(never)]
    fn received(&mut self, base: u8, tail: bool) -> Result<(), Exit<'gc>> {
        let acc = self.cx.acc;
        let call = if acc == Value::VALUES {
            Call { base, argc: 0, rest: self.cx.values }
        } else {
            let call = Call { base, argc: 1, rest: Value::NULL };
            fits(call)?;
            self.cx.frame.set(base + ARGS, acc);
            call
        };
        if tail { self.tail_call(call) } else { self.call(call, false) }
    }

    /// Sets the mark of a `with-mark` or `with-exception-handler` in tail position on the current frame. Returns the call that replaces the request.
    ///
    /// The frame must be able to hold marks of its own. Two kinds of frame can:
    ///
    /// - The bottom frame. Its caller's marks are the marks that the head record of the chain restores.
    /// - A frame whose link has `marks` set. Its caller's marks are saved below it.
    ///
    /// Returns `None` for any other frame. The outer loop then saves the caller's frames, which makes this frame the bottom frame.
    #[inline(never)]
    fn tail_mark(&mut self, base: u8, args: u8, request: Request) -> Result<Option<Call<'gc>>, Fault> {
        let (mc, frame, task) = (self.cx.mc, self.cx.frame, self.cx.task);
        let link = Link::of(frame.get(self.link)).ok_or(Fault::Malformed)?;
        let under = if link.is_bottom() {
            segments::restored(mc, task.chain(mc))
        } else if link.marks {
            let caller = self.fp.checked_sub(usize::from(link.base)).and_then(|caller| self.stack.frame(mc, caller)).ok_or(Fault::Malformed)?;
            caller.get(Kept::under(usize::from(link.base), 0)?.marks as u8)
        } else {
            return Ok(None);
        };
        let (key, value, call) = match request {
            Request::WithMark => (frame.get(base), frame.get(base + 1), Call { base: base + 2, argc: args - 3, rest: Value::NULL }),
            _ => (handler_key(), prompts::handlers_with(mc, task, frame.get(base))?, Call { base: base + 1, argc: 0, rest: Value::NULL }),
        };
        task.set_attachments(mc, segments::marked(mc, task.attachments(mc), under, key, value)?);
        if mc.step_due() {
            self.cx.fuel.pause();
        }
        Ok(Some(call))
    }

    /// Lays out a `keyword-apply` in registers `base..base + args` as a call to the core of its keyword procedure. Returns that call.
    ///
    /// The core takes one argument for each keyword the procedure accepts, in the procedure's order, and then the positional arguments. An accepted keyword that the call does not supply is passed as [`Value::UNSUPPLIED`].
    ///
    /// Returns `None` and leaves the registers unchanged for a call that this function does not handle. The outer loop then runs the request and reports any error. The cases are:
    ///
    /// - The callee is not a keyword procedure, or its core is not a closure.
    /// - The call supplies a keyword that the procedure does not accept.
    /// - A required keyword is missing.
    /// - The keywords are out of order.
    /// - The procedure accepts more than [`KEYWORDS`] keywords.
    /// - The laid-out call does not fit in the frame window.
    #[inline(never)]
    fn keyword_call(&mut self, base: u8, args: u8) -> Option<Call<'gc>> {
        let (mc, frame) = (self.cx.mc, self.cx.frame);
        let callee = frame.get(base).downcast::<KeywordProcedure>(mc)?;
        let core = callee.core(mc);
        core.downcast::<Closure>(mc)?;
        let pairs = Pairs::new(mc);
        let (mut given, mut values) = (frame.get(base + 1), frame.get(base + 2));
        let mut passed = [Value::UNSUPPLIED; KEYWORDS];
        let mut count = 0;
        for accepted in pairs.elements(callee.keywords(mc)) {
            if count == KEYWORDS {
                return None;
            }
            match (Pair::of(given), Pair::of(values)) {
                (Some(keyword), Some(value)) if keyword.head(mc) == accepted => {
                    passed[count] = value.head(mc);
                    (given, values) = (keyword.tail(mc), value.tail(mc));
                }
                _ if pairs.elements(callee.required(mc)).any(|required| required == accepted) => return None,
                _ => {}
            }
            count += 1;
        }
        // Keywords that are left over are unknown to the procedure or out of order.
        if given != Value::NULL || values != Value::NULL {
            return None;
        }
        // The positional arguments are in the registers after the three operands, and the last register holds the list of the rest.
        let positional = usize::from(args) - 4;
        let rest = frame.get(base + args - 1);
        // The core is placed in the register just below its first argument. Up to two keyword values fit in the registers of the `keyword-apply` operands. Each further keyword value shifts the positional arguments up by one register.
        let shift = count.saturating_sub(2);
        let core_at = usize::from(base) + 2 + shift - count;
        if core_at + 1 + count + positional > WINDOW {
            return None;
        }
        let first = usize::from(base) + 3;
        if shift > 0 {
            for i in (0..positional).rev() {
                frame.set((first + shift + i) as u8, frame.get((first + i) as u8));
            }
        }
        frame.set(core_at as u8, core);
        for (i, &value) in passed[..count].iter().enumerate() {
            frame.set((core_at + 1 + i) as u8, value);
        }
        Some(Call { base: core_at as u8, argc: (count + positional) as u8, rest })
    }

    /// Returns the arguments that the first-class `apply` passes on, as one list. `operands` is the list of its arguments after the procedure: some leading arguments, then a proper list. The result is the leading arguments followed by the elements of that list.
    ///
    /// Returns `None` for operands of any other shape, and for more than [`LEADING`] leading arguments. The outer loop then runs the request and reports any error.
    #[inline(never)]
    fn applied(&mut self, operands: Value<'gc>) -> Result<Option<Value<'gc>>, Fault> {
        let (mc, pairs) = (self.cx.mc, Pairs::new(self.cx.mc));
        let Some(mut cell) = Pair::of(operands) else { return Ok(None) };
        let mut leading = [Value::VOID; LEADING];
        let mut count = 0;
        while let Some(next) = Pair::of(cell.tail(mc)) {
            if count == LEADING {
                return Ok(None);
            }
            leading[count] = cell.head(mc);
            count += 1;
            cell = next;
        }
        let mut rest = cell.head(mc);
        if cell.tail(mc) != Value::NULL || !pairs.is_list(rest) {
            return Ok(None);
        }
        for &value in leading[..count].iter().rev() {
            rest = pairs.cons(value, rest)?.value(mc);
        }
        if count > 0 && mc.step_due() {
            self.cx.fuel.pause();
        }
        Ok(Some(rest))
    }

    /// Performs a non-tail marked call for `with-mark`, `with-exception-handler`, or `guard`. Sets the
    /// active mark, offsets the new frame by `SAVED_MARKS` past `base` to save previous marks, and stores
    /// guard state below the frame. Marked `#[inline(never)]` to prevent bloat in the common call path.
    #[inline(never)]
    fn marked_call(&mut self, base: u8, args: u8, request: Request) -> Result<(), Exit<'gc>> {
        let (mc, frame, task) = (self.cx.mc, self.cx.frame, self.cx.task);
        let (procedure, argc) = match request {
            Request::WithMark => (frame.get(base + 2), args - 3),
            Request::Guard | Request::GuardQuiet => (frame.get(base), 0),
            _ => (frame.get(base + 1), 0),
        };
        let call = Call { base: base + SAVED_MARKS, argc, rest: Value::NULL };
        fits(call)?;
        let takes = procedure.downcast::<Closure>(mc).and_then(|closure| closure.code(mc)).is_some_and(|code| code.arity(mc) == i64::from(argc));
        if !takes || self.fp + usize::from(call.base) > self.limit {
            return Err(Exit::Request { base, args, request, spread: false, tail: false });
        }
        let (pairs, saved) = (Pairs::new(mc), task.attachments(mc));
        let (key, value, guard) = match request {
            Request::WithMark => (frame.get(base), frame.get(base + 1), None),
            _ => {
                let guarding = matches!(request, Request::Guard | Request::GuardQuiet);
                let handler = if guarding {
                    Value::object(mc, Guard::new(mc, frame.get(base + 1), task.winders(mc), request == Request::Guard).map_err(Fault::from)?)
                } else {
                    frame.get(base)
                };
                let guard = guarding.then_some(handler);
                (handler_key(), prompts::handlers_with(mc, task, handler)?, guard)
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
    if arity == i64::from(argc) && argc <= MAX_PARAMS && rest == Value::NULL {
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
            None if rest != Value::NULL => return Err(Fault::WrongType),
            None if argc < required => return Err(Fault::Arity),
            None => Value::UNSUPPLIED,
        };
        frame.set(ARGS + argc, item);
        argc += 1;
    }
    if !shape.rest {
        return if argc > fixed || Pair::of(rest).is_some() {
            Err(Fault::Arity)
        } else if rest != Value::NULL {
            Err(Fault::WrongType)
        } else {
            Ok(())
        };
    }
    // The remaining arguments become the tail of the rest parameter, so they must form a proper list. A pair stores whether it starts a proper list, so this check does not walk the list.
    let pairs = Pairs::new(mc);
    if !pairs.is_list(rest) {
        return Err(Fault::WrongType);
    }
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
        .filter(|&count| usize::from(count) + usize::from(shape.rest) <= MAX_ARGS)
        .ok_or(Fault::Malformed)?;
    Ok((shape.required as u8, fixed))
}

/// Binds arguments for procedures with more parameters than `MAX_PARAMS`: places the first
/// `MAX_PARAMS - 1` arguments into registers and collects remaining arguments into a rest list in
/// the final register.
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
        let pair = Pair::of(rest).ok_or(if rest == Value::NULL { Fault::Arity } else { Fault::WrongType })?;
        frame.set(ARGS + argc, pair.head(mc));
        (rest, argc) = (pair.tail(mc), argc + 1);
    }
    let pairs = Pairs::new(mc);
    for i in (keep..argc).rev() {
        rest = pairs.cons(frame.get(ARGS + i), rest)?.value(mc);
    }
    let count = pairs.list_len(rest).ok_or(Fault::WrongType)?;
    let required = slots - u64::from(variadic) - u64::from(keep);
    if count < required || (!variadic && count > required) {
        return Err(Fault::Arity);
    }
    frame.set(ARGS + keep, rest);
    Ok(())
}
