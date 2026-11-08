//! Pass 6 (`L4 -> Closure`): register allocation and bytecode emission.
//!
//! Translates closure-converted [`L4`] into VM [`Bytecode`] and returns the top-level thunk
//! [`Closure`]. Virtual registers (`VReg`) are allocated lexically and recycled at the end of
//! each `Seq`, `Let`, `Fix`, `If` test, and call argument block; functions whose simultaneous
//! live variables exceed [`LIMIT`] automatically spill to a [`Spill`](ragwort_vm::objects::Spill)
//! vector.

use std::collections::{HashMap, HashSet};

use ragwort_types::gc::{Gc, Mutation, Value, WINDOW};
use ragwort_types::vector::Vectors;
use ragwort_vm::frame::{self, ARGS, CLOSURE, MAX_PARAMS};
use ragwort_vm::objects::{self, Bytecode, BytecodeFields, Closure, ModuleFields};
use ragwort_vm::{Capture, HostDef, Intrinsic, Op, Purity, Read, Request};

use crate::ir::{Closure as IrClosure, L4, UpvalSource, VarRef};
use crate::{CompileError, Prim, Var};

/// A virtual register: `0..LIMIT` are physical frame registers, `LIMIT..` are slots of the
/// frame's spill object.
type VReg = u32;

/// How many scratch registers there are, the last of a frame's, so how many values a call made
/// in them can take.
const STAGE: usize = WINDOW / 4;
/// The first scratch register: those below are a function's own.
const LIMIT: VReg = (WINDOW - STAGE) as VReg;
const SCRATCH: u8 = LIMIT as u8;

pub(crate) fn emit<'gc>(mc: &Mutation<'gc>, owner: Option<Gc<'gc, objects::Module>>, l4: &L4<'gc>) -> Result<Value<'gc>, CompileError> {
    let mut module = Module { mc, owner, constants: Vec::new(), index: HashMap::new(), codes: Vec::new(), spills: HashSet::new() };
    let code = module.compile_function(None, &[], None, &[], l4)?;
    let table = Vectors::new(mc).immutable_from_slice(&module.constants)?.value(mc);
    for &c in &module.codes {
        c.set_constants(mc, table);
    }
    Ok(Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID)?))
}

/// Why compiling a function stopped: a real [`CompileError`], `Spill` when `reg()` first
/// crosses [`LIMIT`] so the function is recompiled once with a spill register reserved, or
/// `FarBranch` when a fused branch's target is past an `i16` offset, so the function is
/// recompiled with plain `JumpIfFalse`s.
enum Stop {
    Spill,
    FarBranch,
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
    /// The module the code is from, whose variables and host functions it uses.
    owner: Option<Gc<'gc, objects::Module>>,
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

    /// Where `def` is in the module's host functions.
    fn host(&self, def: &'static HostDef) -> Result<u32, CompileError> {
        let hosts = self.owner.and_then(|m| m.hosts(self.mc)).map_or(&[][..], |h| *h);
        let i = hosts.iter().position(|h| h == def).ok_or(CompileError::UnknownHost(def))?;
        u32::try_from(i).map_err(|_| CompileError::TooManyConstants)
    }

    fn compile_function(
        &mut self,
        lambda: Option<u32>,
        params: &[Var],
        rest: Option<Var>,
        captures: &[Capture],
        body: &L4<'gc>,
    ) -> Result<Gc<'gc, Bytecode>, CompileError> {
        let mut spill = lambda.is_some_and(|id| self.spills.contains(&id));
        let mut near = true;
        let (constants, codes) = (self.constants.len(), self.codes.len());
        loop {
            match self.attempt(spill, near, params, rest, captures, body) {
                Ok(code) => return Ok(code),
                Err(Stop::Error(e)) => return Err(e),
                Err(Stop::Spill) if !spill => {
                    spill = true;
                    self.spills.extend(lambda);
                }
                Err(Stop::Spill) => unreachable!("a function with a spill never runs out of registers"),
                Err(Stop::FarBranch) if near => near = false,
                Err(Stop::FarBranch) => unreachable!("without fused branches every jump has an i32 offset"),
            }
            for constant in self.constants.drain(constants..) {
                self.index.remove(&constant.to_bits());
            }
            self.codes.truncate(codes);
        }
    }

    fn attempt(
        &mut self,
        spill: bool,
        near: bool,
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
            near,
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
                f.write(r, |dst| Op::CallIntrinsic1 { dst, a: list, intrinsic: Intrinsic::Car });
                f.ops.push(Op::CallIntrinsic1 { dst: list, a: list, intrinsic: Intrinsic::Cdr });
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
        let code = Bytecode::new(mc, mc.frozen(Box::from(ops))?, Value::VOID, mc.frozen(Box::from(captures))?, arity, self.owner)?;
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
    /// Whether to fuse 1- and 2-argument intrinsic tests into `BranchIntrinsic*`, whose offsets
    /// are `i16`s.
    near: bool,
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
                // If `other` is the loop back-edge (`L4::Recur`) and `then` is the loop exit,
                // invert a 1- or 2-arg intrinsic branch so the hot loop body falls through and
                // the exit sits after the backward jump.
                let invert = self.near
                    && l4_always_recurs(other)
                    && !l4_always_recurs(then)
                    && matches!(
                        test.as_ref(),
                        L4::Intrinsic(Prim::Intrinsic(_), args) if (1..=2).contains(&args.len())
                    );
                let (fallthrough, target) = if invert {
                    (other.as_ref(), then.as_ref())
                } else {
                    (then.as_ref(), other.as_ref())
                };
                let to_target = self.branch(test, invert, mark)?;
                self.expr(fallthrough, want)?;
                let to_end = (matches!(want, Want::Reg(_)) && !l4_always_recurs(fallthrough))
                    .then(|| self.jump(Op::Jump { offset: 0 }));
                self.land(to_target)?;
                self.expr(target, want)?;
                if let Some(j) = to_end {
                    self.land(j)?;
                }
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
                self.emit_recur(&params, args)?;
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
            L4::Intrinsic(Prim::Intrinsic(Intrinsic::Add), args)
                if let [x, L4::Quote(k)] = args.as_slice()
                    && let Some(imm) = k.as_fixnum().and_then(|k| i16::try_from(k).ok()) =>
            {
                let v = self.arg_vreg(x)?;
                let a = self.arg_reg(v, 0);
                let t = self.into(want)?;
                self.write(t, |dst| Op::AddImm { dst, a, imm });
                if let Want::Tail = want {
                    let src = self.read(t);
                    self.ops.push(Op::Return { src });
                }
            }
            L4::Intrinsic(Prim::Read(read), args) if matches!(want, Want::Reg(_)) && (1..=2).contains(&args.len()) => {
                let Want::Reg(dst) = want else { unreachable!() };
                let v0 = self.arg_vreg(&args[0])?;
                let a = self.arg_reg(v0, 0);
                if let [_, a1] = args.as_slice() {
                    let v1 = self.arg_vreg(a1)?;
                    let b = self.arg_reg(v1, 1);
                    self.write(dst, |dst| Op::Read2 { dst, a, b, read: *read });
                } else {
                    self.write(dst, |dst| Op::Read1 { dst, a, read: *read });
                }
            }
            L4::Intrinsic(prim, args) => {
                if let (Prim::Intrinsic(intrinsic), Want::Reg(dst)) = (*prim, want) {
                    match args.as_slice() {
                        [a0] => {
                            let v0 = self.arg_vreg(a0)?;
                            let a = self.arg_reg(v0, 0);
                            self.write(dst, |dst| Op::CallIntrinsic1 { dst, a, intrinsic });
                            self.next = mark;
                            return Ok(());
                        }
                        [a0, a1] => {
                            let v0 = self.arg_vreg(a0)?;
                            let v1 = self.arg_vreg(a1)?;
                            let a = self.arg_reg(v0, 0);
                            let b = self.arg_reg(v1, 1);
                            self.write(dst, |dst| Op::CallIntrinsic2 { dst, a, b, intrinsic });
                            self.next = mark;
                            return Ok(());
                        }
                        [a0, a1, a2] => {
                            let v0 = self.arg_vreg(a0)?;
                            let v1 = self.arg_vreg(a1)?;
                            let v2 = self.arg_vreg(a2)?;
                            let a = self.arg_reg(v0, 0);
                            let b = self.arg_reg(v1, 1);
                            let c = self.arg_reg(v2, 2);
                            self.write(dst, |dst| Op::CallIntrinsic3 { dst, a, b, c, intrinsic });
                            self.next = mark;
                            return Ok(());
                        }
                        _ => {}
                    }
                }
                let argc = args.len();
                let base = self.layout_prim_args(*prim, args)?;
                match *prim {
                    Prim::Intrinsic(i) => self.intrinsic(i, base, argc, want)?,
                    Prim::Read(r) => self.read_op(r, base, argc, want),
                    Prim::Request(r) => self.request(r, base, argc, want)?,
                    Prim::Host(h) => self.host(h, base, argc, want)?,
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

    /// A call of a host function, laid out as a request is, as what it replies can call a
    /// procedure at `base`. Its arguments must fit the frame, as nothing else can call it.
    fn host(&mut self, def: &'static HostDef, base: VReg, args: usize, want: Want) -> Result<(), Stop> {
        let host = self.module.host(def)?;
        if !self.fits(base, args) {
            return Err(Stop::Error(CompileError::TooManyArguments));
        }
        let (base, args) = (self.stage(base, args), args as u8);
        match want {
            Want::Tail => self.ops.push(Op::TailCallHost { base, args, host }),
            Want::Reg(dst) => {
                self.ops.push(Op::CallHost { base, args, host });
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

    /// A read takes at most 3 arguments, so they always fit.
    fn read_op(&mut self, read: Read, base: VReg, args: usize, want: Want) {
        let base = self.stage(base, args);
        let args = args as u8;
        match want {
            Want::Tail => self.ops.push(Op::TailCallRead { base, args, read }),
            Want::Reg(dst) => {
                self.ops.push(Op::CallRead { base, args, read });
                self.take(dst);
            }
        }
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
            Prim::Read(_) | Prim::Host(_) => unreachable!("lowering spreads no read or host function"),
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
        // A guard holds the frame it's called from anyway, and called from it, the VM keeps its
        // handler there, with no prompt.
        if let (Request::Guard, Want::Tail, false) = (request, want, spread) {
            self.ops.extend([Op::CallRequest { base, args, request }, Op::LoadAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]);
            return;
        }
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
        for (i, to) in (0..n as u32).zip(SCRATCH..=u8::MAX) {
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
            self.ops.push(Op::CallIntrinsic2 { dst: list, a: SCRATCH, b: list, intrinsic: Intrinsic::Cons });
        }
        Ok(list)
    }

    fn branch(&mut self, test: &L4<'gc>, branch_if: bool, mark: VReg) -> Result<usize, Stop> {
        if self.near
            && let L4::Intrinsic(Prim::Intrinsic(intrinsic), args) = test
        {
            match args.as_slice() {
                [a0] => {
                    let v0 = self.arg_vreg(a0)?;
                    let a = self.arg_reg(v0, 0);
                    self.next = mark;
                    return Ok(self.jump(Op::BranchIntrinsic1 { a, intrinsic: *intrinsic, branch_if, offset: 0 }));
                }
                [a0, a1] => {
                    let v0 = self.arg_vreg(a0)?;
                    let v1 = self.arg_vreg(a1)?;
                    let a = self.arg_reg(v0, 0);
                    let b = self.arg_reg(v1, 1);
                    self.next = mark;
                    return Ok(self.jump(Op::BranchIntrinsic2 { a, b, intrinsic: *intrinsic, branch_if, offset: 0 }));
                }
                _ => {}
            }
        }
        debug_assert!(!branch_if, "JumpIfFalse only branches on false");
        let t = self.reg()?;
        self.expr(test, Want::Reg(t))?;
        self.next = mark;
        let test_reg = self.read(t);
        Ok(self.jump(Op::JumpIfFalse { test: test_reg, offset: 0 }))
    }

    fn arg_vreg(&mut self, arg: &L4<'gc>) -> Result<VReg, Stop> {
        match arg {
            L4::Ref(VarRef::Local(v)) => Ok(self.loc(*v)?),
            L4::Ref(VarRef::SelfClosure) => Ok(u32::from(CLOSURE)),
            _ => {
                let r = self.reg()?;
                self.expr(arg, Want::Reg(r))?;
                Ok(r)
            }
        }
    }

    fn arg_reg(&mut self, v: VReg, scratch_offset: u8) -> u8 {
        match self.spot(v) {
            Spot::Reg(r) => r,
            Spot::Slot(slot) => {
                let dst = SCRATCH + scratch_offset;
                let spill = self.spill_reg();
                self.ops.push(Op::LoadSpill { dst, spill, slot });
                dst
            }
        }
    }

    fn emit_recur(&mut self, params: &[(Var, VReg)], args: &[L4<'gc>]) -> Result<(), Stop> {
        let n = args.len();
        let mut pending: Vec<(VReg, VReg)> = Vec::new();
        let mut can_fuse = false;

        if args.iter().all(l4_is_reorderable) {
            let mut done = vec![false; n];
            for i in 0..n {
                if args[i] == L4::Ref(VarRef::Local(params[i].0)) {
                    done[i] = true;
                }
            }
            loop {
                // 1. Evaluate any argument whose target parameter is not read by any remaining
                //    undone argument directly into its parameter register.
                let mut progressed = false;
                for i in 0..n {
                    if done[i] {
                        continue;
                    }
                    let (param_var, param_reg) = params[i];
                    let read_by_other = (0..n).any(|j| !done[j] && j != i && l4_reads_local(&args[j], param_var));
                    if !read_by_other && !l4_clobbers_self(&args[i], param_var) {
                        if let L4::Ref(VarRef::Local(src_var)) = args[i] {
                            let src_reg = self.loc(src_var)?;
                            self.copy_fused(param_reg, src_reg, &mut can_fuse);
                        } else {
                            self.expr(&args[i], Want::Reg(param_reg))?;
                            can_fuse = false;
                        }
                        done[i] = true;
                        progressed = true;
                    }
                }
                if progressed {
                    continue;
                }
                if done.iter().all(|&d| d) {
                    break;
                }
                // 2. Direct 2-register swap cycle `(p_i <- p_j, p_j <- p_i)` with no temp register.
                let mut swapped = false;
                for i in 0..n {
                    if done[i] {
                        continue;
                    }
                    if let L4::Ref(VarRef::Local(vj)) = args[i]
                        && let Some(j) = (i + 1..n).find(|&j| !done[j] && params[j].0 == vj)
                        && args[j] == L4::Ref(VarRef::Local(params[i].0))
                        && !(0..n).any(|k| !done[k] && k != i && k != j && (l4_reads_local(&args[k], params[i].0) || l4_reads_local(&args[k], params[j].0)))
                        && let (Spot::Reg(ri), Spot::Reg(rj)) = (self.spot(params[i].1), self.spot(params[j].1))
                    {
                        self.ops.push(Op::Move2 { dst1: ri, src1: rj, dst2: rj, src2: ri });
                        can_fuse = false;
                        done[i] = true;
                        done[j] = true;
                        swapped = true;
                        break;
                    }
                }
                if swapped {
                    continue;
                }
                // 3. Break a dependency cycle by evaluating one undone argument into a fresh temp
                //    register (preferring a non-`Ref` expression so no extra `Move` is needed).
                let pick = (0..n)
                    .find(|&i| !done[i] && !matches!(args[i], L4::Ref(VarRef::Local(_))))
                    .or_else(|| (0..n).find(|&i| !done[i]))
                    .expect("checked at least one undone arg");
                let t = self.reg()?;
                self.expr(&args[pick], Want::Reg(t))?;
                can_fuse = false;
                pending.push((params[pick].1, t));
                done[pick] = true;
            }
        } else {
            for (i, arg) in args.iter().enumerate() {
                let (param_var, param_reg) = params[i];
                if *arg == L4::Ref(VarRef::Local(param_var)) {
                    continue;
                }
                let read_later = args[i + 1..].iter().any(|later| l4_reads_local(later, param_var));
                if !read_later && !l4_clobbers_self(arg, param_var) {
                    if let L4::Ref(VarRef::Local(src_var)) = *arg {
                        let src_reg = self.loc(src_var)?;
                        self.copy_fused(param_reg, src_reg, &mut can_fuse);
                    } else {
                        self.expr(arg, Want::Reg(param_reg))?;
                        can_fuse = false;
                    }
                } else {
                    let t = self.reg()?;
                    self.expr(arg, Want::Reg(t))?;
                    can_fuse = false;
                    pending.push((param_reg, t));
                }
            }
        }

        for (dst, src) in pending {
            self.copy_fused(dst, src, &mut can_fuse);
        }
        Ok(())
    }

    fn copy_fused(&mut self, dst: VReg, src: VReg, can_fuse: &mut bool) {
        if dst == src {
            return;
        }
        if *can_fuse
            && let (Spot::Reg(d2), Spot::Reg(s2)) = (self.spot(dst), self.spot(src))
            && let Some(Op::Move { dst: d1, src: s1 }) = self.ops.last().copied()
            && d1 != d2
            && s2 != d1
        {
            if let Some(last) = self.ops.last_mut() {
                *last = Op::Move2 { dst1: d1, src1: s1, dst2: d2, src2: s2 };
            }
            *can_fuse = false;
            return;
        }
        self.copy(dst, src);
        *can_fuse = matches!((self.spot(dst), self.spot(src)), (Spot::Reg(_), Spot::Reg(_)));
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

    fn land(&mut self, at: usize) -> Result<(), Stop> {
        let rel = self.ops.len() - at - 1;
        match &mut self.ops[at] {
            Op::Jump { offset: o } | Op::JumpIfFalse { offset: o, .. } => {
                *o = i32::try_from(rel).expect("functions are shorter than 2^31 ops");
            }
            Op::BranchIntrinsic1 { offset: o, .. } | Op::BranchIntrinsic2 { offset: o, .. } => {
                *o = i16::try_from(rel).map_err(|_| Stop::FarBranch)?;
            }
            _ => unreachable!("only jumps are landed"),
        }
        Ok(())
    }
}

fn l4_always_recurs<'gc>(expr: &L4<'gc>) -> bool {
    match expr {
        L4::Recur(_, _) => true,
        L4::Seq(_, b) | L4::Let(_, b) | L4::Fix(_, b) => l4_always_recurs(b),
        L4::If(_, then, other) => l4_always_recurs(then) && l4_always_recurs(other),
        _ => false,
    }
}

fn l4_clobbers_self<'gc>(arg: &L4<'gc>, param_var: Var) -> bool {
    l4_reads_local(arg, param_var)
        && !matches!(arg, L4::Intrinsic(_, _) | L4::ApplyIntrinsic(_, _) | L4::App(_, _))
}

fn l4_is_reorderable<'gc>(expr: &L4<'gc>) -> bool {
    match expr {
        L4::Quote(_) | L4::Ref(_) | L4::Lambda(_) => true,
        L4::If(a, b, c) => l4_is_reorderable(a) && l4_is_reorderable(b) && l4_is_reorderable(c),
        L4::Seq(a, b) => l4_is_reorderable(a) && l4_is_reorderable(b),
        L4::Let(binds, body) => {
            binds.iter().all(|(_, init)| l4_is_reorderable(init)) && l4_is_reorderable(body)
        }
        L4::Intrinsic(Prim::Host(h), args) => h.purity != Purity::Impure && args.iter().all(l4_is_reorderable),
        L4::Intrinsic(Prim::Intrinsic(i), args) => {
            (i.is_discardable()
                || matches!(
                    i,
                    Intrinsic::Add
                        | Intrinsic::Sub
                        | Intrinsic::Mul
                        | Intrinsic::Car
                        | Intrinsic::Cdr
                        | Intrinsic::Caar
                        | Intrinsic::Cadr
                        | Intrinsic::Cdar
                        | Intrinsic::Cddr
                        | Intrinsic::Unbox
                ))
                && args.iter().all(l4_is_reorderable)
        }
        _ => false,
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
