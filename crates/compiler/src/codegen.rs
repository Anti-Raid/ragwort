//! Pass 6 (`L4 -> Closure`): register allocation and bytecode emission.
//!
//! Translates closure-converted [`L4`] into VM [`Bytecode`] and returns the top-level thunk
//! [`Closure`]. Virtual registers (`VReg`) are allocated lexically and recycled at the end of
//! each `Seq`, `Let`, `Fix`, `If` test, and call argument block; functions whose simultaneous
//! live variables exceed [`LIMIT`] automatically spill to a [`Spill`](ragwort_vm::objects::Spill)
//! vector.

use std::collections::{HashMap, HashSet};

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::vector::Vectors;
use ragwort_vm::frame::{self, ARGS, CLOSURE, MAX_PARAMS};
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure};
use ragwort_vm::{Capture, Intrinsic, Op, Request};

use crate::ir::{Closure as IrClosure, L4, UpvalSource, VarRef};
use crate::{CompileError, Prim, Var};

/// A virtual register: `0..LIMIT` are physical frame registers, `LIMIT..` are slots of the
/// frame's spill object.
type VReg = u32;

/// The first scratch register: those below are a function's own.
const LIMIT: VReg = 224;
const SCRATCH: u8 = LIMIT as u8;
/// How many scratch registers there are, so how many values a call made in them can take.
const STAGE: usize = 256 - LIMIT as usize;

pub(crate) fn emit<'gc>(mc: &Mutation<'gc>, l4: &L4<'gc>) -> Result<Value<'gc>, CompileError> {
    let mut module = Module {
        mc,
        constants: Vec::new(),
        index: HashMap::new(),
        codes: Vec::new(),
        spills: HashSet::new(),
    };
    let code = module.compile_function(None, &[], None, &[], l4)?;
    let table = Vectors::new(mc).immutable_from_slice(&module.constants)?.value(mc);
    for &c in &module.codes {
        c.set_constants(mc, table);
    }
    Ok(Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID)?))
}

/// Why compiling a function stopped: a real [`CompileError`], or `Spill` when `reg()` first
/// crosses [`LIMIT`] so the function is recompiled once with a spill register reserved.
enum Stop {
    Spill,
    Error(CompileError),
}

impl<E: Into<CompileError>> From<E> for Stop {
    fn from(e: E) -> Self {
        Self::Error(e.into())
    }
}

#[derive(Clone, Copy)]
enum Spot {
    Reg(u8),
    Slot(u32),
}

#[derive(Clone, Copy)]
enum Want {
    Reg(VReg),
    Tail,
}

struct Module<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    constants: Vec<Value<'gc>>,
    index: HashMap<u64, u32>,
    codes: Vec<Gc<'gc, Bytecode>>,
    spills: HashSet<u32>,
}

impl<'a, 'gc> Module<'a, 'gc> {
    fn constant(&mut self, value: Value<'gc>) -> Result<u32, CompileError> {
        if let Some(&i) = self.index.get(&value.to_bits()) {
            return Ok(i);
        }
        let i = u32::try_from(self.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
        self.constants.push(value);
        self.index.insert(value.to_bits(), i);
        Ok(i)
    }

    fn compile_function(
        &mut self,
        lambda: Option<u32>,
        params: &[Var],
        rest: Option<Var>,
        captures: &[Capture],
        body: &L4<'gc>,
    ) -> Result<Gc<'gc, Bytecode>, CompileError> {
        let spill = lambda.is_some_and(|id| self.spills.contains(&id));
        let (constants, codes) = (self.constants.len(), self.codes.len());
        match self.attempt(spill, params, rest, captures, body) {
            Ok(code) => return Ok(code),
            Err(Stop::Error(e)) => return Err(e),
            Err(Stop::Spill) => {}
        }
        for constant in self.constants.drain(constants..) {
            self.index.remove(&constant.to_bits());
        }
        self.codes.truncate(codes);
        self.spills.extend(lambda);
        match self.attempt(true, params, rest, captures, body) {
            Ok(code) => Ok(code),
            Err(Stop::Error(e)) => Err(e),
            Err(Stop::Spill) => unreachable!("a function with a spill never runs out of registers"),
        }
    }

    fn attempt(
        &mut self,
        spill: bool,
        params: &[Var],
        rest: Option<Var>,
        captures: &[Capture],
        body: &L4<'gc>,
    ) -> Result<Gc<'gc, Bytecode>, Stop> {
        let n = i64::try_from(params.len()).map_err(|_| CompileError::TooManyRegisters)?;
        let arity = if rest.is_some() { -(n + 1) } else { n };
        let link = frame::link_slot(arity);
        let mut f = Compiler {
            module: self,
            ops: Vec::new(),
            env: HashMap::new(),
            loops: HashMap::new(),
            next: u32::from(link) + 1,
            spill: None,
            slots: Vec::new(),
            spilled: 0,
        };
        if spill {
            f.spill = Some(link + 1);
            f.next += 1;
            f.ops.push(Op::NewSpill { dst: link + 1, count: 0 });
        }
        let all: Vec<Var> = params.iter().chain(&rest).copied().collect();
        if all.len() <= usize::from(MAX_PARAMS) {
            f.env.extend(all.iter().zip(u32::from(ARGS)..).map(|(&v, r)| (v, r)));
        } else {
            let keep = usize::from(MAX_PARAMS - 1);
            f.env.extend(params[..keep].iter().zip(u32::from(ARGS)..).map(|(&v, r)| (v, r)));
            let list = ARGS + MAX_PARAMS - 1;
            for &v in &params[keep..] {
                let r = f.reg()?;
                f.emit_intrinsic(Intrinsic::Car, list, 1, Want::Reg(r));
                f.emit_intrinsic(Intrinsic::Cdr, list, 1, Want::Reg(u32::from(list)));
                f.env.insert(v, r);
            }
            f.env.extend(rest.map(|v| (v, u32::from(list))));
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

struct Compiler<'m, 'a, 'gc> {
    module: &'m mut Module<'a, 'gc>,
    ops: Vec<Op>,
    env: HashMap<Var, VReg>,
    loops: HashMap<Var, (usize, Vec<(Var, VReg)>)>,
    next: VReg,
    spill: Option<u8>,
    slots: Vec<u32>,
    spilled: u32,
}

impl<'m, 'a, 'gc> Compiler<'m, 'a, 'gc> {
    fn expr(&mut self, expr: &L4<'gc>, want: Want) -> Result<(), Stop> {
        let mark = self.next;
        match expr {
            L4::Quote(v) => {
                let t = self.into(want)?;
                self.load(t, *v)?;
                self.done(t, want);
            }
            L4::Ref(VarRef::Local(v)) => {
                let r = self.loc(*v)?;
                self.done(r, want);
            }
            L4::Ref(VarRef::Upvalue(index)) => {
                let t = self.into(want)?;
                self.write(t, |dst| Op::LoadUpvalue { dst, index: *index });
                self.done(t, want);
            }
            L4::Ref(VarRef::SelfClosure) => {
                self.done(u32::from(CLOSURE), want);
            }
            L4::If(test, then, other) => {
                let t = self.reg()?;
                self.expr(test, Want::Reg(t))?;
                self.next = mark;
                let test_reg = self.read(t);

                let to_other = self.jump(Op::JumpIfFalse { test: test_reg, offset: 0 });
                self.expr(then, want)?;
                let to_end = matches!(want, Want::Reg(_)).then(|| self.jump(Op::Jump { offset: 0 }));
                self.land(to_other);
                self.expr(other, want)?;
                to_end.into_iter().for_each(|j| self.land(j));
            }
            L4::Seq(a, b) => {
                let t = self.reg()?;
                self.expr(a, Want::Reg(t))?;
                self.next = mark;
                self.expr(b, want)?;
            }
            L4::Let(binds, body) => {
                let mut bound = Vec::with_capacity(binds.len());
                for &(v, ref init) in binds {
                    let r = self.reg()?;
                    self.expr(init, Want::Reg(r))?;
                    bound.push((v, r));
                }
                for &(v, r) in &bound {
                    self.env.insert(v, r);
                }
                self.expr(body, want)?;
                for &(v, _) in &bound {
                    self.env.remove(&v);
                }
            }
            L4::Fix(binds, body) => {
                // A single-binding `Fix` with 0 captures (using `SelfClosure` for self-calls) is a
                // compile-time constant `Closure` and needs no runtime `NewClosure`.
                if let [(v, clos)] = binds.as_slice()
                    && clos.captures.is_empty()
                {
                    let r = self.reg()?;
                    let bytecode = self.compile_closure(clos, &[])?;
                    let closure = Closure::new(self.module.mc, Some(bytecode), 0, Value::VOID)?;
                    self.load(r, Value::object(self.module.mc, closure))?;
                    self.env.insert(*v, r);
                    self.expr(body, want)?;
                    self.env.remove(v);
                } else {
                    let count = binds.len();
                    let base = self.next;
                    for _ in 0..count {
                        self.reg()?;
                    }
                    for (i, &(v, _)) in binds.iter().enumerate() {
                        self.env.insert(v, base + i as VReg);
                    }

                    if base as usize + count <= LIMIT as usize {
                        let mut bytecodes = Vec::with_capacity(count);
                        for (_, clos) in binds {
                            bytecodes.push(self.compile_closure(clos, &[])?);
                        }
                        let code = self.push_contiguous_bytecodes(&bytecodes)?;
                        self.ops.push(Op::NewClosure { dst: base as u8, count: count as u8, code });
                    } else {
                        let peers: Vec<(Var, u8)> = binds
                            .iter()
                            .enumerate()
                            .map(|(i, &(v, _))| (v, SCRATCH + i as u8))
                            .collect();
                        let mut bytecodes = Vec::with_capacity(count);
                        for (_, clos) in binds {
                            bytecodes.push(self.compile_closure(clos, &peers)?);
                        }
                        let code = self.push_contiguous_bytecodes(&bytecodes)?;
                        self.ops.push(Op::NewClosure { dst: SCRATCH, count: count as u8, code });
                        for i in 0..count {
                            let src = SCRATCH + i as u8;
                            match self.spot(base + i as VReg) {
                                Spot::Reg(dst) => self.ops.push(Op::Move { dst, src }),
                                Spot::Slot(slot) => {
                                    let spill = self.spill_reg();
                                    self.ops.push(Op::StoreSpill { src, spill, slot });
                                }
                            }
                        }
                    }

                    self.expr(body, want)?;
                    for &(v, _) in binds {
                        self.env.remove(&v);
                    }
                }
            }
            L4::Loop { id, params, body } => {
                let mut bound = Vec::with_capacity(params.len());
                for &(v, ref init) in params {
                    let r = self.reg()?;
                    self.expr(init, Want::Reg(r))?;
                    bound.push((v, r));
                }
                for &(v, r) in &bound {
                    self.env.insert(v, r);
                }
                let loop_pc = self.ops.len();
                self.loops.insert(*id, (loop_pc, bound.clone()));
                self.expr(body, want)?;
                self.loops.remove(id);
                for &(v, _) in &bound {
                    self.env.remove(&v);
                }
            }
            L4::Recur(id, args) => {
                let (loop_pc, params) = self.loops.get(id).cloned().ok_or(CompileError::Unbound(*id))?;
                let mut pending = Vec::new();
                for (i, arg) in args.iter().enumerate() {
                    let (param_var, param_reg) = params[i];
                    if *arg == L4::Ref(VarRef::Local(param_var)) {
                        continue;
                    }
                    let read_later = args[i + 1..].iter().any(|later| l4_reads_local(later, param_var));
                    let clobbers_self = l4_reads_local(arg, param_var)
                        && !matches!(arg, L4::Intrinsic(_, _) | L4::ApplyIntrinsic(_, _) | L4::App(_, _));
                    if !read_later && !clobbers_self {
                        self.expr(arg, Want::Reg(param_reg))?;
                    } else {
                        let t = self.reg()?;
                        self.expr(arg, Want::Reg(t))?;
                        pending.push((param_reg, t));
                    }
                }
                for (dst, src) in pending {
                    self.copy(dst, src);
                }
                let next_pc = self.ops.len() + 1;
                let offset = i32::try_from(loop_pc as isize - next_pc as isize)
                    .expect("functions are shorter than 2^31 ops");
                self.ops.push(Op::Jump { offset });
            }
            L4::Lambda(clos) => {
                // `Op::NewClosure` writes the new closure to `dst` before reading its captures, so if
                // `want` is a local register that `clos` itself captures, allocate a fresh register first.
                let captures_dst = matches!(want, Want::Reg(dst) if clos.captures.iter().any(|c| {
                    matches!(c, UpvalSource::Local(v) if self.env.get(v) == Some(&dst))
                }));
                let t = if captures_dst { self.reg()? } else { self.into(want)? };
                let bytecode = self.compile_closure(clos, &[])?;
                if clos.captures.is_empty() {
                    let closure = Closure::new(self.module.mc, Some(bytecode), 0, Value::VOID)?;
                    self.load(t, Value::object(self.module.mc, closure))?;
                } else {
                    let code = self.module.constant(Value::object(self.module.mc, bytecode))?;
                    self.write(t, |dst| Op::NewClosure { dst, count: 1, code });
                }
                self.done(t, want);
            }
            L4::App(f, args) => {
                // In a tail call, if `f` already sits at `self.next - 1` (`< LIMIT`), we can place
                // `args` right after it at `self.next..` without moving `f`.
                let base = match (want, f.as_ref()) {
                    (Want::Tail, L4::Ref(VarRef::Local(v)))
                        if self.next > 0
                            && self.env.get(v) == Some(&(self.next - 1))
                            && (self.next - 1) as usize + 1 + args.len() <= LIMIT as usize =>
                    {
                        self.next - 1
                    }
                    _ => {
                        let b = self.reg()?;
                        self.expr(f, Want::Reg(b))?;
                        b
                    }
                };
                let argc = self.args(args)?;
                self.call(base, argc, want)?;
            }
            L4::Intrinsic(prim, args) => {
                let argc = args.len();
                let base = self.layout_prim_args(*prim, args)?;
                match *prim {
                    Prim::Intrinsic(i) => self.intrinsic(i, base, argc, want)?,
                    Prim::Request(r) => self.request(r, base, argc, want)?,
                }
            }
            L4::ApplyIntrinsic(prim, args) => {
                let argc = args.len();
                let base = self.layout_prim_args(*prim, args)?;
                self.spread(*prim, base, argc, want)?;
            }
        }
        self.next = mark;
        Ok(())
    }

    fn compile_closure(&mut self, clos: &IrClosure<'gc>, peers: &[(Var, u8)]) -> Result<Gc<'gc, Bytecode>, Stop> {
        let mut captures = Vec::with_capacity(clos.captures.len());
        for &src in &clos.captures {
            let cap = match src {
                UpvalSource::Upvalue(u) => Capture::Upvalue(u),
                UpvalSource::SelfClosure => Capture::Register(CLOSURE),
                UpvalSource::Local(v) => {
                    if let Some(&(_, reg)) = peers.iter().find(|&&(peer, _)| peer == v) {
                        Capture::Register(reg)
                    } else {
                        match self.spot(self.loc(v)?) {
                            Spot::Reg(r) => Capture::Register(r),
                            Spot::Slot(slot) => Capture::Spill { spill: self.spill_reg(), slot },
                        }
                    }
                }
            };
            captures.push(cap);
        }
        Ok(self.module.compile_function(Some(clos.id), &clos.params, clos.rest, &captures, &clos.body)?)
    }

    fn push_contiguous_bytecodes(&mut self, bytecodes: &[Gc<'gc, Bytecode>]) -> Result<u32, CompileError> {
        let first = u32::try_from(self.module.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
        for &bc in bytecodes {
            let i = u32::try_from(self.module.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
            let val = Value::object(self.module.mc, bc);
            self.module.constants.push(val);
            self.module.index.insert(val.to_bits(), i);
        }
        Ok(first)
    }

    /// Lays out `args` for an intrinsic/request call, avoiding `Move`s when all or a prefix of
    /// `args` already sit in contiguous local registers.
    fn layout_prim_args(&mut self, prim: Prim, args: &[L4<'gc>]) -> Result<VReg, Stop> {
        if let Prim::Intrinsic(intrinsic) = prim {
            if let Some(b) = self.contiguous_locals(intrinsic, args) {
                return Ok(b);
            }
            if let Some((base, prefix_len)) = self.top_prefix_locals(args) {
                self.args(&args[prefix_len..])?;
                return Ok(base);
            }
        }
        let b = self.next;
        self.args(args)?;
        Ok(b)
    }

    /// If `args` are non-empty and already sit in contiguous physical registers `base..base + k`
    /// (`< LIMIT`), or in reversed adjacent registers for a 2-arg commutative intrinsic, returns
    /// `Some(base)` so the intrinsic can read them in place without `Move`s.
    fn contiguous_locals(&self, intrinsic: Intrinsic, args: &[L4<'gc>]) -> Option<VReg> {
        let first = match args.first()? {
            L4::Ref(VarRef::Local(v)) => *self.env.get(v)?,
            _ => return None,
        };
        if args.len() == 2
            && intrinsic.is_commutative_binary()
            && let L4::Ref(VarRef::Local(v1)) = args[1]
            && let Some(&second) = self.env.get(&v1)
            && first == second + 1
            && second as usize + 2 <= LIMIT as usize
        {
            return Some(second);
        }
        if first as usize + args.len() > LIMIT as usize {
            return None;
        }
        for (i, arg) in args.iter().enumerate().skip(1) {
            let L4::Ref(VarRef::Local(v)) = arg else { return None };
            if *self.env.get(v)? != first + i as VReg {
                return None;
            }
        }
        Some(first)
    }

    /// If a non-empty prefix `args[0..p]` sits in the top allocated registers `self.next - p .. self.next`,
    /// returns `Some((self.next - p, p))` so only `args[p..]` need to be evaluated into `self.next..`.
    fn top_prefix_locals(&self, args: &[L4<'gc>]) -> Option<(VReg, usize)> {
        let first = match args.first()? {
            L4::Ref(VarRef::Local(v)) => *self.env.get(v)?,
            _ => return None,
        };
        if first >= self.next || first as usize + args.len() > LIMIT as usize {
            return None;
        }
        let prefix_len = (self.next - first) as usize;
        if prefix_len == 0 || prefix_len >= args.len() {
            return None;
        }
        for (i, arg) in args[..prefix_len].iter().enumerate() {
            let L4::Ref(VarRef::Local(v)) = arg else { return None };
            if *self.env.get(v)? != first + i as VReg {
                return None;
            }
        }
        Some((first, prefix_len))
    }

    fn args(&mut self, args: &[L4<'gc>]) -> Result<usize, Stop> {
        for arg in args {
            let r = self.reg()?;
            self.expr(arg, Want::Reg(r))?;
        }
        Ok(args.len())
    }

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

    fn intrinsic(&mut self, intrinsic: Intrinsic, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        if self.fits(base, args) {
            let base = self.stage(base, args);
            self.emit_intrinsic(intrinsic, base, args as u8, want);
            return Ok(());
        }
        let list = self.list(base, args, None)?;
        self.ops.push(Op::ApplyIntrinsic { base: list, args: 1, intrinsic });
        match want {
            Want::Tail => self.ops.extend([Op::LoadAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]),
            Want::Reg(dst) => self.take(dst),
        }
        Ok(())
    }

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

    fn spread(&mut self, prim: Prim, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        let (base, args) = match self.fits(base, args) {
            true => (self.stage(base, args), args as u8),
            false => (self.list(base, args - 1, Some(base + args as VReg - 1))?, 1),
        };
        match prim {
            Prim::Intrinsic(intrinsic) => {
                self.ops.push(Op::ApplyIntrinsic { base, args, intrinsic });
                match want {
                    Want::Tail => self.ops.extend([Op::LoadAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]),
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

    fn fits(&self, base: VReg, n: usize) -> bool {
        base as usize + n <= LIMIT as usize || n <= STAGE
    }

    fn stage(&mut self, base: VReg, n: usize) -> u8 {
        if base as usize + n <= LIMIT as usize {
            return base as u8;
        }
        for (i, to) in (0..n as u32).zip(SCRATCH..) {
            self.fetch(base + i, to);
        }
        SCRATCH
    }

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
            self.ops.extend([
                Op::CallIntrinsic { base: SCRATCH, args: 2, intrinsic: Intrinsic::Cons },
                Op::LoadAcc { dst: list },
            ]);
        }
        Ok(list)
    }

    fn load(&mut self, dst: VReg, value: Value<'gc>) -> Result<(), Stop> {
        let index = self.module.constant(value)?;
        self.write(dst, |dst| Op::LoadConst { dst, index });
        Ok(())
    }

    fn done(&mut self, src: VReg, want: Want) {
        match want {
            Want::Reg(dst) => self.copy(dst, src),
            Want::Tail => {
                let src = self.read(src);
                self.ops.push(Op::Return { src });
            }
        }
    }

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

    fn take(&mut self, dst: VReg) {
        self.write(dst, |dst| Op::LoadAcc { dst });
    }

    fn write(&mut self, v: VReg, op: impl FnOnce(u8) -> Op) {
        match self.spot(v) {
            Spot::Reg(r) => self.ops.push(op(r)),
            Spot::Slot(slot) => {
                let spill = self.spill_reg();
                self.ops.extend([op(SCRATCH), Op::StoreSpill { src: SCRATCH, spill, slot }]);
            }
        }
    }

    fn read(&mut self, v: VReg) -> u8 {
        match self.spot(v) {
            Spot::Reg(r) => r,
            Spot::Slot(_) => {
                self.fetch(v, SCRATCH);
                SCRATCH
            }
        }
    }

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

    fn into(&mut self, want: Want) -> Result<VReg, Stop> {
        match want {
            Want::Reg(r) => Ok(r),
            Want::Tail => self.reg(),
        }
    }

    fn loc(&self, v: Var) -> Result<VReg, CompileError> {
        self.env.get(&v).copied().ok_or(CompileError::Unbound(v))
    }

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

    fn jump(&mut self, op: Op) -> usize {
        self.ops.push(op);
        self.ops.len() - 1
    }

    fn land(&mut self, at: usize) {
        let offset = i32::try_from(self.ops.len() - at - 1).expect("functions are shorter than 2^31 ops");
        match &mut self.ops[at] {
            Op::Jump { offset: o } | Op::JumpIfFalse { offset: o, .. } => *o = offset,
            _ => unreachable!("only jumps are landed"),
        }
    }
}

fn l4_reads_local<'gc>(expr: &L4<'gc>, target: Var) -> bool {
    match expr {
        L4::Quote(_) => false,
        L4::Ref(VarRef::Local(v)) => *v == target,
        L4::Ref(_) => false,
        L4::If(a, b, c) => l4_reads_local(a, target) || l4_reads_local(b, target) || l4_reads_local(c, target),
        L4::Seq(a, b) => l4_reads_local(a, target) || l4_reads_local(b, target),
        L4::Let(binds, body) | L4::Loop { params: binds, body, .. } => {
            binds.iter().any(|(_, init)| l4_reads_local(init, target)) || l4_reads_local(body, target)
        }
        L4::Fix(binds, body) => {
            binds
                .iter()
                .any(|(_, clos)| clos.captures.contains(&UpvalSource::Local(target)))
                || l4_reads_local(body, target)
        }
        L4::Recur(_, args) | L4::Intrinsic(_, args) | L4::ApplyIntrinsic(_, args) => {
            args.iter().any(|a| l4_reads_local(a, target))
        }
        L4::App(f, args) => l4_reads_local(f, target) || args.iter().any(|a| l4_reads_local(a, target)),
        L4::Lambda(clos) => clos.captures.contains(&UpvalSource::Local(target)),
    }
}
