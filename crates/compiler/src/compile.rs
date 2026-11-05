//! The code generator. Each lambda is a [`Function`]: its frame's registers are the closure,
//! its parameters and its link, as `ragwort_vm::frame` lays them out, then its variables and
//! temporaries, allocated as a stack of virtual registers. A call is made at the top of the
//! stack, so the callee's frame starts past anything the caller still needs.
//!
//! The virtual registers below [`LIMIT`] are the frame's own. A function that needs more is
//! compiled again with a spill, in the register after its link, and those past [`LIMIT`] are its
//! slots: each one a new slot, so a continuation that's resumed again finds the values it saw.
//! The registers from [`LIMIT`] up are scratch, which spilled values pass through, and where a
//! call of spilled values is made. A call with more arguments than that holds is made with a
//! list of them, through `apply`.

use std::collections::{HashMap, HashSet};

use ragwort_types::Error;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::vector::Vectors;
use ragwort_vm::frame::{self, ARGS, MAX_PARAMS};
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure};
use ragwort_vm::{Capture, Intrinsic, Op, Request};

use crate::analyze::{Analysis, analyze};
use crate::{Core, Lambda, Place, Prim, Var};

/// How deeply forms can nest before compiling them would take too much of the native stack.
pub(crate) const MAX_DEPTH: usize = 256;

/// The first scratch register: those below are a function's own.
const LIMIT: u32 = 224;
const SCRATCH: u8 = LIMIT as u8;
/// How many scratch registers there are, so how many values a call made in them can take.
const STAGE: usize = 256 - LIMIT as usize;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompileError {
    /// A reference to, or `%set!` of, a local variable outside the scope of its binding.
    Unbound(Var),
    /// A variable bound twice, which lowering never does.
    Rebound(Var),
    /// Two lambdas with the same id, which lowering never makes.
    SameLambda(u32),
    /// A call of a built-in with a number of arguments it doesn't take.
    Arity(Prim),
    /// A function needing more spill slots than a spill can index.
    TooManyRegisters,
    /// More than a module's constants can index.
    TooManyConstants,
    /// Forms nested more than `MAX_DEPTH` deep.
    TooDeep,
    OutOfMemory,
}

impl From<OutOfMemory> for CompileError {
    fn from(_: OutOfMemory) -> Self {
        CompileError::OutOfMemory
    }
}

impl From<Error> for CompileError {
    fn from(_: Error) -> Self {
        CompileError::OutOfMemory
    }
}

/// Why compiling a function stopped: an error, or that it ran out of registers without a spill.
enum Stop {
    Error(CompileError),
    Spill,
}

impl<E: Into<CompileError>> From<E> for Stop {
    fn from(e: E) -> Self {
        Stop::Error(e.into())
    }
}

/// Compiles `body` as the body of a procedure of no arguments, and returns a closure of it,
/// which a `Machine` runs.
pub fn compile<'gc>(mc: &Mutation<'gc>, body: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
    let analysis = analyze(body)?;
    let mut module = Module { mc, analysis: &analysis, constants: Vec::new(), index: HashMap::new(), codes: Vec::new(), spills: HashSet::new() };
    let code = module.function(None, &[], None, &[], &[], body)?;
    let table = Vectors::new(mc).immutable_from_slice(&module.constants)?.value(mc);
    module.codes.iter().for_each(|code| code.set_constants(mc, table));
    Ok(Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID)?))
}

/// What the functions of one compilation share: its constants, one table for all of them.
struct Module<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    analysis: &'a Analysis,
    constants: Vec<Value<'gc>>,
    /// Each constant's index, by its word, so a value is in the table once.
    index: HashMap<u64, u32>,
    codes: Vec<Gc<'gc, Bytecode>>,
    /// The lambdas found to need a spill, so compiling one again starts with it.
    spills: HashSet<u32>,
}

impl<'gc> Module<'_, 'gc> {
    fn constant(&mut self, value: Value<'gc>) -> Result<u32, CompileError> {
        if let Some(&i) = self.index.get(&value.to_bits()) {
            return Ok(i);
        }
        let i = u32::try_from(self.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
        self.constants.push(value);
        self.index.insert(value.to_bits(), i);
        Ok(i)
    }

    /// Compiles the function `lambda`, or the module's body if it's `None`, of `params` and
    /// `rest`, whose closures keep the boxes of `free` as their upvalues, taken from where
    /// `captures` says, and returns its code. Its constants are filled in once the module's done.
    fn function(&mut self, lambda: Option<u32>, params: &[Var], rest: Option<Var>, free: &[Var], captures: &[Capture], body: &Core<'gc>) -> Result<Gc<'gc, Bytecode>, CompileError> {
        let spill = lambda.is_some_and(|id| self.spills.contains(&id));
        let (constants, codes) = (self.constants.len(), self.codes.len());
        match self.attempt(spill, params, rest, free, captures, body) {
            Ok(code) => return Ok(code),
            Err(Stop::Error(e)) => return Err(e),
            Err(Stop::Spill) => {}
        }
        for constant in self.constants.drain(constants..) {
            self.index.remove(&constant.to_bits());
        }
        self.codes.truncate(codes);
        self.spills.extend(lambda);
        match self.attempt(true, params, rest, free, captures, body) {
            Ok(code) => Ok(code),
            Err(Stop::Error(e)) => Err(e),
            Err(Stop::Spill) => unreachable!("a function with a spill never runs out of registers"),
        }
    }

    fn attempt(&mut self, spill: bool, params: &[Var], rest: Option<Var>, free: &[Var], captures: &[Capture], body: &Core<'gc>) -> Result<Gc<'gc, Bytecode>, Stop> {
        let n = i64::try_from(params.len()).map_err(|_| CompileError::TooManyRegisters)?;
        let arity = if rest.is_some() { -(n + 1) } else { n };
        let link = frame::link_slot(arity);
        let mut f = Function { module: self, ops: Vec::new(), env: HashMap::new(), next: u32::from(link) + 1, spill: None, slots: Vec::new(), spilled: 0, depth: 0 };
        if spill {
            f.spill = Some(link + 1);
            f.next += 1;
            f.ops.push(Op::NewSpill { dst: link + 1, count: 0 });
        }
        f.env.extend(free.iter().zip(0..).map(|(&v, u)| (v, Loc::Upvalue(u))));
        let all: Vec<Var> = params.iter().chain(&rest).copied().collect();
        if all.len() <= usize::from(MAX_PARAMS) {
            f.env.extend(all.iter().zip(u32::from(ARGS)..).map(|(&v, r)| (v, Loc::Reg(r))));
        } else {
            // The VM binds the parameters past the registers' as a list in the last of them.
            let keep = usize::from(MAX_PARAMS - 1);
            f.env.extend(params[..keep].iter().zip(u32::from(ARGS)..).map(|(&v, r)| (v, Loc::Reg(r))));
            let list = ARGS + MAX_PARAMS - 1;
            for &v in &params[keep..] {
                let r = f.reg()?;
                f.emit_intrinsic(Intrinsic::Car, list, 1, Want::Reg(r));
                f.emit_intrinsic(Intrinsic::Cdr, list, 1, Want::Reg(u32::from(list)));
                f.env.insert(v, Loc::Reg(r));
            }
            f.env.extend(rest.map(|v| (v, Loc::Reg(u32::from(list)))));
        }
        for v in all {
            if f.module.analysis.captured.contains(&v) {
                f.make_box(v)?;
            }
        }
        f.expr(body, Want::Tail)?;
        if let Some(Op::NewSpill { count, .. }) = f.spill.and(f.ops.first_mut()) {
            *count = f.spilled;
        }
        let ops = f.ops;
        let mc = self.mc;
        let code = Bytecode::new(mc, mc.frozen(Box::from(ops))?, Value::VOID, mc.frozen(Box::from(captures))?, arity)?;
        self.codes.push(code);
        Ok(code)
    }
}

/// A virtual register: a register of the frame below [`LIMIT`], a spill slot from there.
type VReg = u32;

/// Where a virtual register is.
#[derive(Clone, Copy)]
enum Spot {
    Reg(u8),
    Slot(u32),
}

/// Where a variable is in a function.
#[derive(Clone, Copy)]
enum Loc {
    /// In a register, not captured.
    Reg(VReg),
    /// Boxed, with the box in a register.
    Boxed(VReg),
    /// Boxed, with the box in an upvalue.
    Upvalue(u32),
}

/// Where an expression's value goes: a register, or back to the caller, from tail position.
#[derive(Clone, Copy)]
enum Want {
    Reg(VReg),
    Tail,
}

struct Function<'m, 'a, 'gc> {
    module: &'m mut Module<'a, 'gc>,
    ops: Vec<Op>,
    env: HashMap<Var, Loc>,
    /// The first virtual register not in use.
    next: VReg,
    /// The register the spill is in, if the function has one.
    spill: Option<u8>,
    /// The slot of each virtual register from [`LIMIT`], as it was last taken.
    slots: Vec<u32>,
    /// How many slots the spill needs.
    spilled: u32,
    depth: usize,
}

impl<'gc> Function<'_, '_, 'gc> {
    fn expr(&mut self, e: &Core<'gc>, want: Want) -> Result<(), Stop> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(CompileError::TooDeep.into());
        }
        let mark = self.next;
        match e {
            Core::Quote(value) => self.quote(*value, want)?,
            Core::Ref(Place::Local(v)) => match self.loc(*v)? {
                Loc::Reg(r) => self.done(r, want),
                Loc::Boxed(r) => self.intrinsic(Intrinsic::Unbox, r, 1, want)?,
                Loc::Upvalue(u) => {
                    let t = self.into(want)?;
                    self.write(t, |dst| Op::LoadUpvalue { dst, index: u });
                    self.intrinsic(Intrinsic::Unbox, t, 1, want)?;
                }
            },
            Core::Ref(Place::Global(g)) => {
                let t = self.into(want)?;
                self.load(t, Value::object(self.module.mc, *g))?;
                self.intrinsic(Intrinsic::GlobalRef, t, 1, want)?;
            }
            Core::If(test, then, other) => {
                let t = self.reg()?;
                self.expr(test, Want::Reg(t))?;
                self.next = mark;
                let test = self.read(t);
                let to_else = self.jump(Op::JumpIfFalse { test, offset: 0 });
                self.expr(then, want)?;
                let to_end = matches!(want, Want::Reg(_)).then(|| self.jump(Op::Jump { offset: 0 }));
                self.land(to_else);
                self.expr(other, want)?;
                to_end.into_iter().for_each(|j| self.land(j));
            }
            Core::Let(binds, body) => {
                let mut regs = Vec::with_capacity(binds.len());
                for (_, init) in binds {
                    let r = self.reg()?;
                    self.expr(init, Want::Reg(r))?;
                    regs.push(r);
                }
                for (&(v, _), r) in binds.iter().zip(regs) {
                    self.env.insert(v, Loc::Reg(r));
                    if self.module.analysis.captured.contains(&v) {
                        self.make_box(v)?;
                    }
                }
                self.expr(body, want)?;
            }
            Core::Letrec(binds, body) => {
                for &(v, _) in binds {
                    let r = self.reg()?;
                    self.load(r, Value::VOID)?;
                    self.env.insert(v, Loc::Reg(r));
                    if self.module.analysis.captured.contains(&v) {
                        self.make_box(v)?;
                    }
                }
                let t = self.reg()?;
                for (v, init) in binds {
                    self.set(Place::Local(*v), init, Want::Reg(t))?;
                }
                self.next -= 1;
                self.expr(body, want)?;
            }
            Core::Set(place, value) => self.set(*place, value, want)?,
            Core::DefineGlobal(g, value) => {
                let b = self.reg()?;
                self.load(b, Value::object(self.module.mc, *g))?;
                let v = self.reg()?;
                self.expr(value, Want::Reg(v))?;
                self.intrinsic(Intrinsic::DefineGlobal, b, 2, want)?;
            }
            Core::App(f, args) => {
                let base = self.reg()?;
                self.expr(f, Want::Reg(base))?;
                let argc = self.args(args)?;
                self.call(base, argc, want)?;
            }
            Core::Lambda(lambda) => self.lambda(lambda, want)?,
            Core::Intrinsic(prim, args) => {
                let base = self.next;
                let argc = self.args(args)?;
                match *prim {
                    Prim::Intrinsic(i) if i.arity().is_none_or(|n| usize::from(n) == argc) => self.intrinsic(i, base, argc, want)?,
                    Prim::Request(request) if request.takes(argc) => self.request(request, base, argc, want)?,
                    _ => return Err(CompileError::Arity(*prim).into()),
                }
            }
            Core::ApplyIntrinsic(prim, args) => {
                if args.is_empty() {
                    return Err(CompileError::Arity(*prim).into());
                }
                let base = self.next;
                let argc = self.args(args)?;
                self.spread(*prim, base, argc, want)?;
            }
        }
        self.next = mark;
        self.depth -= 1;
        Ok(())
    }

    /// Assigns `value` to `place`, which leaves void.
    fn set(&mut self, place: Place<'gc>, value: &Core<'gc>, want: Want) -> Result<(), Stop> {
        let mark = self.next;
        self.assign(place, value, want)?;
        self.next = mark;
        Ok(())
    }

    fn assign(&mut self, place: Place<'gc>, value: &Core<'gc>, want: Want) -> Result<(), Stop> {
        let b = self.reg()?;
        match place {
            Place::Local(v) => match self.loc(v)? {
                Loc::Reg(r) => {
                    self.expr(value, Want::Reg(b))?;
                    self.copy(r, b);
                    return self.quote(Value::VOID, want);
                }
                Loc::Boxed(r) => self.copy(b, r),
                Loc::Upvalue(u) => self.write(b, |dst| Op::LoadUpvalue { dst, index: u }),
            },
            Place::Global(g) => self.load(b, Value::object(self.module.mc, g))?,
        }
        let v = self.reg()?;
        self.expr(value, Want::Reg(v))?;
        let intrinsic = if matches!(place, Place::Global(_)) { Intrinsic::GlobalSet } else { Intrinsic::SetBox };
        self.intrinsic(intrinsic, b, 2, want)?;
        Ok(())
    }

    /// Makes a closure of `lambda`, capturing the boxes of its free variables.
    fn lambda(&mut self, lambda: &Lambda<'gc>, want: Want) -> Result<(), Stop> {
        let free = self.module.analysis.free(lambda).to_vec();
        let mut captures = Vec::with_capacity(free.len());
        for &v in &free {
            captures.push(match self.loc(v)? {
                Loc::Boxed(r) => match self.spot(r) {
                    Spot::Reg(r) => Capture::Register(r),
                    Spot::Slot(slot) => Capture::Spill { spill: self.spill_reg(), slot },
                },
                Loc::Upvalue(u) => Capture::Upvalue(u),
                Loc::Reg(_) => unreachable!("captured variables are boxed"),
            });
        }
        let code = self.module.function(Some(lambda.id), &lambda.params, lambda.rest, &free, &captures, &lambda.body)?;
        let index = self.module.constant(Value::object(self.module.mc, code))?;
        let t = self.into(want)?;
        self.write(t, |dst| Op::NewClosure { dst, count: 1, code: index });
        self.done(t, want);
        Ok(())
    }

    /// Compiles `args` into the registers from the top of the stack, and returns how many.
    fn args(&mut self, args: &[Core<'gc>]) -> Result<usize, Stop> {
        for arg in args {
            let r = self.reg()?;
            self.expr(arg, Want::Reg(r))?;
        }
        Ok(args.len())
    }

    /// Calls the procedure in `base` with the `argc` registers after it, for `want`.
    fn call(&mut self, base: VReg, argc: usize, want: Want) -> Result<(), Stop> {
        if !self.fits(base, 1 + argc) {
            self.list(base + 1, argc, None)?;
            self.fetch(base, SCRATCH);
            self.emit_request(Request::Apply, SCRATCH, 2, false, want);
            return Ok(());
        }
        let (base, args) = (self.stage(base, 1 + argc), argc as u8);
        match want {
            Want::Tail => self.ops.push(Op::TailCall { base, args }),
            Want::Reg(dst) => {
                self.ops.push(Op::Call { base, args });
                self.take(dst);
            }
        }
        Ok(())
    }

    /// Runs `intrinsic` on the `args` registers from `base`, for `want`.
    fn intrinsic(&mut self, intrinsic: Intrinsic, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        if self.fits(base, args) {
            let base = self.stage(base, args);
            self.emit_intrinsic(intrinsic, base, args as u8, want);
            return Ok(());
        }
        let list = self.list(base, args, None)?;
        self.ops.push(Op::ApplyIntrinsic { base: list, args: 1, intrinsic });
        match want {
            Want::Tail => self.ops.extend([Op::MoveAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]),
            Want::Reg(dst) => self.take(dst),
        }
        Ok(())
    }

    /// Carries out `request` on the `args` registers from `base`, for `want`.
    fn request(&mut self, request: Request, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        if self.fits(base, args) {
            let base = self.stage(base, args);
            self.emit_request(request, base, args as u8, false, want);
        } else {
            let list = self.list(base, args, None)?;
            self.emit_request(request, list, 1, true, want);
        }
        Ok(())
    }

    /// Runs `prim` on the `args` registers from `base`, the last a list of more, for `want`.
    fn spread(&mut self, prim: Prim, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        let (base, args) = match self.fits(base, args) {
            true => (self.stage(base, args), args as u8),
            false => (self.list(base, args - 1, Some(base + args as VReg - 1))?, 1),
        };
        match prim {
            Prim::Intrinsic(intrinsic) => {
                self.ops.push(Op::ApplyIntrinsic { base, args, intrinsic });
                match want {
                    Want::Tail => self.ops.extend([Op::MoveAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]),
                    Want::Reg(dst) => self.take(dst),
                }
            }
            Prim::Request(request) => self.emit_request(request, base, args, true, want),
        }
        Ok(())
    }

    fn emit_intrinsic(&mut self, intrinsic: Intrinsic, base: u8, args: u8, want: Want) {
        match want {
            Want::Tail => self.ops.push(Op::TailCallIntrinsic { base, args, intrinsic }),
            Want::Reg(dst) => {
                self.ops.push(Op::CallIntrinsic { base, args, intrinsic });
                self.take(dst);
            }
        }
    }

    /// Carries out `request` on the `args` registers from `base`, the last a list of more if
    /// `spread`.
    fn emit_request(&mut self, request: Request, base: u8, args: u8, spread: bool, want: Want) {
        self.ops.push(match (want, spread) {
            (Want::Tail, false) => Op::TailCallRequest { base, args, request },
            (Want::Tail, true) => Op::TailApplyRequest { base, args, request },
            (Want::Reg(_), false) => Op::CallRequest { base, args, request },
            (Want::Reg(_), true) => Op::ApplyRequest { base, args, request },
        });
        if let Want::Reg(dst) = want {
            self.take(dst);
        }
    }

    /// Whether `n` values from `base` can be passed in registers: where they are, or moved to
    /// the scratch registers.
    fn fits(&self, base: VReg, n: usize) -> bool {
        base as usize + n <= LIMIT as usize || n <= STAGE
    }

    /// The register `n` values from `base` are in for a call: `base`'s, if they're all in
    /// registers, or the first scratch register, where they're moved.
    fn stage(&mut self, base: VReg, n: usize) -> u8 {
        if base as usize + n <= LIMIT as usize {
            return base as u8;
        }
        for (i, to) in (0..n as u32).zip(SCRATCH..) {
            self.fetch(base + i, to);
        }
        SCRATCH
    }

    /// Makes a list of the `n` values from `base`, ending in `tail`'s value or else `()`, in the
    /// second scratch register, and returns it.
    fn list(&mut self, base: VReg, n: usize, tail: Option<VReg>) -> Result<u8, Stop> {
        let list = SCRATCH + 1;
        match tail {
            Some(tail) => self.fetch(tail, list),
            None => {
                let nil = self.module.constant(Value::NIL)?;
                self.ops.push(Op::LoadConst { dst: list, index: nil });
            }
        }
        for i in (0..n as u32).rev() {
            self.fetch(base + i, SCRATCH);
            self.ops.extend([Op::CallIntrinsic { base: SCRATCH, args: 2, intrinsic: Intrinsic::Cons }, Op::MoveAcc { dst: list }]);
        }
        Ok(list)
    }

    fn quote(&mut self, value: Value<'gc>, want: Want) -> Result<(), Stop> {
        let t = self.into(want)?;
        self.load(t, value)?;
        self.done(t, want);
        Ok(())
    }

    fn load(&mut self, dst: VReg, value: Value<'gc>) -> Result<(), Stop> {
        let index = self.module.constant(value)?;
        self.write(dst, |dst| Op::LoadConst { dst, index });
        Ok(())
    }

    /// Boxes the value of `v`, a variable in a register, in place.
    fn make_box(&mut self, v: Var) -> Result<(), Stop> {
        let Loc::Reg(r) = self.loc(v)? else { unreachable!("only unboxed variables are boxed") };
        self.intrinsic(Intrinsic::MakeBox, r, 1, Want::Reg(r))?;
        self.env.insert(v, Loc::Boxed(r));
        Ok(())
    }

    /// Hands the value in `src` to `want`.
    fn done(&mut self, src: VReg, want: Want) {
        match want {
            Want::Reg(dst) => self.copy(dst, src),
            Want::Tail => {
                let src = self.read(src);
                self.ops.push(Op::Return { src });
            }
        }
    }

    /// Copies `src` to `dst`.
    fn copy(&mut self, dst: VReg, src: VReg) {
        if dst == src {
            return;
        }
        match self.spot(src) {
            Spot::Reg(src) => self.write(dst, |dst| Op::Move { dst, src }),
            Spot::Slot(slot) => {
                let spill = self.spill_reg();
                self.write(dst, |dst| Op::LoadSpill { dst, spill, slot });
            }
        }
    }

    /// The accumulator, to `dst`.
    fn take(&mut self, dst: VReg) {
        self.write(dst, |dst| Op::MoveAcc { dst });
    }

    /// Emits `op`, given the register to write, so that it writes `v`: its own, or a scratch
    /// register stored to its slot.
    fn write(&mut self, v: VReg, op: impl FnOnce(u8) -> Op) {
        match self.spot(v) {
            Spot::Reg(r) => self.ops.push(op(r)),
            Spot::Slot(slot) => {
                let spill = self.spill_reg();
                self.ops.extend([op(SCRATCH), Op::StoreSpill { src: SCRATCH, spill, slot }]);
            }
        }
    }

    /// The register with `v`'s value: its own, or a scratch register loaded from its slot.
    fn read(&mut self, v: VReg) -> u8 {
        match self.spot(v) {
            Spot::Reg(r) => r,
            Spot::Slot(_) => {
                self.fetch(v, SCRATCH);
                SCRATCH
            }
        }
    }

    /// Copies `v` to the register `to`.
    fn fetch(&mut self, v: VReg, to: u8) {
        match self.spot(v) {
            Spot::Reg(r) if r == to => {}
            Spot::Reg(r) => self.ops.push(Op::Move { dst: to, src: r }),
            Spot::Slot(slot) => {
                let spill = self.spill_reg();
                self.ops.push(Op::LoadSpill { dst: to, spill, slot });
            }
        }
    }

    fn spot(&self, v: VReg) -> Spot {
        match v.checked_sub(LIMIT) {
            None => Spot::Reg(v as u8),
            Some(i) => Spot::Slot(self.slots[i as usize]),
        }
    }

    fn spill_reg(&self) -> u8 {
        self.spill.expect("only a function with a spill has slots")
    }

    /// The register `want` names, or a new one if it's the tail.
    fn into(&mut self, want: Want) -> Result<VReg, Stop> {
        match want {
            Want::Reg(r) => Ok(r),
            Want::Tail => self.reg(),
        }
    }

    fn loc(&self, v: Var) -> Result<Loc, CompileError> {
        self.env.get(&v).copied().ok_or(CompileError::Unbound(v))
    }

    /// Takes the first virtual register not in use: past the frame's own, a new slot of the
    /// spill, or the signal to compile the function again with one.
    fn reg(&mut self) -> Result<VReg, Stop> {
        let v = self.next;
        if let Some(i) = v.checked_sub(LIMIT) {
            if self.spill.is_none() {
                return Err(Stop::Spill);
            }
            let slot = self.spilled;
            self.spilled = slot.checked_add(1).ok_or(CompileError::TooManyRegisters)?;
            match self.slots.get_mut(i as usize) {
                Some(s) => *s = slot,
                None => self.slots.push(slot),
            }
        }
        self.next = v.checked_add(1).ok_or(CompileError::TooManyRegisters)?;
        Ok(v)
    }

    /// Emits a jump to be landed later, and returns where it is.
    fn jump(&mut self, op: Op) -> usize {
        self.ops.push(op);
        self.ops.len() - 1
    }

    /// Points the jump at `at` here.
    fn land(&mut self, at: usize) {
        let offset = i32::try_from(self.ops.len() - at - 1).expect("functions are shorter than 2^31 ops");
        match &mut self.ops[at] {
            Op::Jump { offset: o } | Op::JumpIfFalse { offset: o, .. } => *o = offset,
            _ => unreachable!("only jumps are landed"),
        }
    }
}
