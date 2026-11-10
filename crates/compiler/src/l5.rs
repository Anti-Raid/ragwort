//! Pass 8 (`L4 -> L5`): each function as a graph of basic blocks in SSA form.
//!
//! Every [`Val`] is defined once: by the function's entry, a block's parameters or an
//! instruction. Where paths meet, a block takes parameters, which jumps to it pass, as Cranelift
//! takes them. An unboxed `set!` gives its variable a new value; contified joins become blocks,
//! taking the variables assigned in their group as more parameters. Only a jump passes values: a
//! branch goes to blocks without parameters.
//!
//! An end that calls something that can capture the frame's continuation or set its marks, a
//! call, a request or a host call, stays a tail call in tail position. Intrinsics and reads don't,
//! so in tail position they're an instruction and a [`End::Return`].

use std::fmt;
use std::iter;

use ragwort_alloc::{Arena, CollectIn, Vec};
use ragwort_types::gc::Value;
use ragwort_vm::{Intrinsic, Purity};

use crate::hash::{HashMap, HashSet};

use crate::ir::{Bind, Bind4, Closure, JoinCode, L4, UpvalSource, VarRef};
use crate::{CompileError, Prim, SlotOp, Var};

#[cfg(test)]
#[path = "tests/l5.rs"]
mod tests;

/// A value of a function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Val(pub(crate) u32);

/// A block of a function, an index of its [`Function::blocks`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Block(pub(crate) u32);

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Function<'a, 'gc> {
    /// The lambda it's from, or `None` for the code compiled.
    pub(crate) id: Option<u32>,
    /// The closure being run.
    pub(crate) this: Val,
    /// The last `optional` of which a call can leave out.
    pub(crate) params: Vec<'a, Val>,
    pub(crate) optional: u32,
    /// The arguments past `params`, as a list.
    pub(crate) rest: Option<Val>,
    /// How many upvalues the function's closures have.
    pub(crate) upvalues: u32,
    /// The first is where it starts, which takes no parameters and nothing jumps to.
    pub(crate) blocks: Vec<'a, BlockData<'a, 'gc>>,
    /// How many values there are, all below this.
    pub(crate) values: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct BlockData<'a, 'gc> {
    pub(crate) params: Vec<'a, Val>,
    pub(crate) insts: Vec<'a, Inst<'a, 'gc>>,
    pub(crate) end: End<'a>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Inst<'a, 'gc> {
    Const(Val, Value<'gc>),
    Upvalue(Val, u32),
    /// `prim` on `args`; if `spread`, the last is a list of the rest. A store of a module variable
    /// is void.
    Prim { dst: Val, prim: Prim, args: Vec<'a, Val>, spread: bool },
    Call { dst: Val, f: Val, args: Vec<'a, Val> },
    /// A closure of each of `codes`, all made before any captures anything, so they can capture
    /// each other.
    Closures { dsts: Vec<'a, Val>, codes: Vec<'a, Code<'a, 'gc>> },
}

/// A closure's code and what it captures, in the order its upvalues are.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Code<'a, 'gc> {
    pub(crate) function: Function<'a, 'gc>,
    pub(crate) captures: Vec<'a, Captured>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Captured {
    Val(Val),
    Upvalue(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum End<'a> {
    Jump(Block, Vec<'a, Val>),
    /// To `other` if `test` is `#f`, else to `then`.
    Branch { test: Val, then: Block, other: Block },
    Return(Val),
    TailCall { f: Val, args: Vec<'a, Val> },
    /// A request or host call in tail position.
    TailPrim { prim: Prim, args: Vec<'a, Val>, spread: bool },
}

impl Inst<'_, '_> {
    pub(crate) fn defs(&self) -> &[Val] {
        match self {
            Inst::Const(dst, _) | Inst::Upvalue(dst, _) | Inst::Prim { dst, .. } | Inst::Call { dst, .. } => std::slice::from_ref(dst),
            Inst::Closures { dsts, .. } => dsts,
        }
    }

    #[cfg(any(debug_assertions, test))]
    pub(crate) fn uses(&self) -> std::vec::Vec<Val> {
        let mut uses = std::vec::Vec::new();
        self.each_use(|v| uses.push(v));
        uses
    }

    pub(crate) fn each_use(&self, mut f: impl FnMut(Val)) {
        match self {
            Inst::Const(..) | Inst::Upvalue(..) => {}
            Inst::Prim { args, .. } => args.iter().for_each(|&v| f(v)),
            Inst::Call { f: callee, args, .. } => iter::once(callee).chain(args).for_each(|&v| f(v)),
            Inst::Closures { codes, .. } => {
                for c in codes.iter().flat_map(|code| &code.captures) {
                    if let Captured::Val(v) = c {
                        f(*v);
                    }
                }
            }
        }
    }
}

impl End<'_> {
    pub(crate) fn successors(&self) -> impl Iterator<Item = Block> + use<> {
        let to = match self {
            End::Jump(to, _) => [Some(*to), None],
            End::Branch { then, other, .. } => [Some(*then), Some(*other)],
            End::Return(_) | End::TailCall { .. } | End::TailPrim { .. } => [None, None],
        };
        to.into_iter().flatten()
    }

    #[cfg(any(debug_assertions, test))]
    pub(crate) fn uses(&self) -> std::vec::Vec<Val> {
        let mut uses = std::vec::Vec::new();
        self.each_use(|v| uses.push(v));
        uses
    }

    pub(crate) fn each_use(&self, mut f: impl FnMut(Val)) {
        match self {
            End::Jump(_, args) | End::TailPrim { args, .. } => args.iter().for_each(|&v| f(v)),
            End::Branch { test, .. } | End::Return(test) => f(*test),
            End::TailCall { f: callee, args } => iter::once(callee).chain(args).for_each(|&v| f(v)),
        }
    }
}

/// The code compiled, of no parameters, as [`L5`](self).
pub(crate) fn lower<'a, 'gc>(arena: &'a Arena, l4: &L4<'_, 'gc>) -> Result<Function<'a, 'gc>, CompileError> {
    function(arena, None, Formals { params: &[], optional: 0, rest: None }, 0, l4)
}

/// Panics if `f` isn't well-formed, as a debug build checks.
#[cfg(debug_assertions)]
pub(crate) fn check(f: &Function<'_, '_>) {
    if let Err(e) = verify(f) {
        panic!("malformed L5: {e}\n{f}");
    }
}

#[derive(Clone, Copy)]
struct Formals<'a> {
    params: &'a [Var],
    optional: u32,
    rest: Option<Var>,
}

fn function<'a, 'gc>(
    arena: &'a Arena,
    id: Option<u32>,
    formals: Formals<'_>,
    upvalues: u32,
    body: &L4<'_, 'gc>,
) -> Result<Function<'a, 'gc>, CompileError> {
    let mut sets = HashSet::default();
    sets_in(body, &mut sets);
    let mut b = Builder {
        arena,
        blocks: vec![Building { params: arena.vec(), insts: arena.vec(), end: None }],
        cur: Block(0),
        next: 0,
        env: HashMap::default(),
        voids: HashSet::default(),
        assigned: std::vec::Vec::new(),
        sets,
        joins: HashMap::default(),
        groups: std::vec::Vec::new(),
        this: Val(0),
    };
    let this = b.fresh();
    b.this = this;
    let params = formals.params.iter().map(|&v| b.bind(v)).collect_in(arena);
    let rest = formals.rest.map(|v| b.bind(v));
    b.expr(body, Ctx::Tail)?;
    let blocks = b.blocks.into_iter().map(|block| BlockData {
        params: block.params,
        insts: block.insts,
        end: block.end.expect("every block made ends"),
    });
    Ok(Function { id, this, params, optional: formals.optional, rest, upvalues, blocks: blocks.collect_in(arena), values: b.next })
}

/// Adds the locals `expr` assigns in its frame to `sets`.
fn sets_in(expr: &L4<'_, '_>, sets: &mut HashSet<Var>) {
    match expr {
        L4::Quote(_) | L4::Ref(_) | L4::Lambda(_) => {}
        L4::Set(v, value) => {
            sets.insert(*v);
            sets_in(value, sets);
        }
        L4::If(a, b, c) => [a, b, c].into_iter().for_each(|e| sets_in(e, sets)),
        L4::Seq(a, b) => {
            sets_in(a, sets);
            sets_in(b, sets);
        }
        L4::Let(binds, body) => {
            for bind in binds {
                if let Bind::Val(_, init) = bind {
                    sets_in(init, sets);
                }
            }
            sets_in(body, sets);
        }
        L4::Join { group, scope } => {
            group.iter().for_each(|code| sets_in(&code.body, sets));
            sets_in(scope, sets);
        }
        L4::App(f, args) => {
            sets_in(f, sets);
            args.iter().for_each(|a| sets_in(a, sets));
        }
        L4::Jump(_, args) | L4::Intrinsic(_, args) | L4::ApplyIntrinsic(_, args) => args.iter().for_each(|a| sets_in(a, sets)),
    }
}

struct Building<'a, 'gc> {
    params: Vec<'a, Val>,
    insts: Vec<'a, Inst<'a, 'gc>>,
    end: Option<End<'a>>,
}

/// Where an expression's value goes: on in the block, or returned from the function.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Value,
    Tail,
}

/// A join of a group being lowered: its block once something jumps to it, how many parameters
/// its jumps pass, and its group, whose assigned variables they pass too.
struct Join<'a> {
    block: Option<Block>,
    params: Vec<'a, Var>,
    group: usize,
}

struct Builder<'a, 'gc> {
    arena: &'a Arena,
    blocks: std::vec::Vec<Building<'a, 'gc>>,
    /// Where code goes.
    cur: Block,
    next: u32,
    env: HashMap<Var, Val>,
    /// Variables bound to what an assignment returns, made only where they're read.
    voids: HashSet<Var>,
    /// The variables in `sets` in scope, innermost last.
    assigned: std::vec::Vec<Var>,
    /// The function's locals it assigns.
    sets: HashSet<Var>,
    joins: HashMap<Var, Join<'a>>,
    /// For each join group, the variables in scope it assigns.
    groups: std::vec::Vec<std::vec::Vec<Var>>,
    this: Val,
}

impl<'a, 'gc> Builder<'a, 'gc> {
    fn fresh(&mut self) -> Val {
        let v = Val(self.next);
        self.next = self.next.checked_add(1).expect("fewer than 2^32 values");
        v
    }

    fn block(&mut self, params: Vec<'a, Val>) -> Block {
        let b = Block(u32::try_from(self.blocks.len()).expect("fewer than 2^32 blocks"));
        self.blocks.push(Building { params, insts: self.arena.vec(), end: None });
        b
    }

    fn building(&mut self) -> &mut Building<'a, 'gc> {
        &mut self.blocks[self.cur.0 as usize]
    }

    fn push(&mut self, inst: Inst<'a, 'gc>) {
        self.building().insts.push(inst);
    }

    fn def(&mut self, inst: impl FnOnce(Val) -> Inst<'a, 'gc>) -> Val {
        let dst = self.fresh();
        self.push(inst(dst));
        dst
    }

    fn end(&mut self, end: End<'a>) {
        let block = self.building();
        debug_assert!(block.end.is_none(), "a block ends once");
        block.end = Some(end);
    }

    fn bind(&mut self, v: Var) -> Val {
        let val = self.fresh();
        self.bind_to(v, val);
        val
    }

    fn bind_to(&mut self, v: Var, val: Val) {
        self.env.insert(v, val);
        if self.sets.contains(&v) {
            self.assigned.push(v);
        }
    }

    fn lookup(&mut self, v: Var) -> Result<Val, CompileError> {
        if self.voids.contains(&v) {
            return Ok(self.def(|dst| Inst::Const(dst, Value::VOID)));
        }
        self.env.get(&v).copied().ok_or(CompileError::Unbound(v))
    }

    /// The values of the first `n` of `assigned`.
    fn snapshot(&self, n: usize) -> std::vec::Vec<Val> {
        self.assigned[..n].iter().map(|v| self.env[v]).collect()
    }

    fn restore(&mut self, vars: &[Var], vals: &[Val]) {
        for (&v, &val) in vars.iter().zip(vals) {
            self.env.insert(v, val);
        }
    }

    /// Lowers `expr`, and returns its value if `ctx` is a value and control goes on past it.
    fn expr(&mut self, expr: &L4<'_, 'gc>, ctx: Ctx) -> Result<Option<Val>, CompileError> {
        match (expr, ctx) {
            (L4::If(test, then, other), _) => self.branch(test, then, other, ctx),
            (L4::Seq(a, b), _) => {
                if self.effect(a)? {
                    self.expr(b, ctx)
                } else {
                    Ok(None)
                }
            }
            (L4::Let(binds, body), _) => {
                let n = self.assigned.len();
                let out = if self.binds(binds)? { self.expr(body, ctx)? } else { None };
                self.unbind(binds.iter().flat_map(Bind::vars), n);
                Ok(out)
            }
            (L4::Join { group, scope }, _) => self.join(group, scope, ctx),
            (L4::Jump(id, args), _) => {
                self.jump(*id, args)?;
                Ok(None)
            }
            (L4::App(f, args), Ctx::Tail) => {
                let Some(f) = self.expr(f, Ctx::Value)? else { return Ok(None) };
                let Some(args) = self.args(args)? else { return Ok(None) };
                self.end(End::TailCall { f, args });
                Ok(None)
            }
            (L4::Intrinsic(prim @ (Prim::Request(_) | Prim::Host(_)), args), Ctx::Tail) => self.tail_prim(*prim, args, false),
            (L4::ApplyIntrinsic(prim @ Prim::Request(_), args), Ctx::Tail) => self.tail_prim(*prim, args, true),
            (_, Ctx::Tail) => {
                if let Some(v) = self.expr(expr, Ctx::Value)? {
                    self.end(End::Return(v));
                }
                Ok(None)
            }
            (L4::Quote(value), Ctx::Value) => Ok(Some(self.def(|dst| Inst::Const(dst, *value)))),
            (L4::Ref(VarRef::Local(v)), Ctx::Value) => Ok(Some(self.lookup(*v)?)),
            (L4::Ref(VarRef::Upvalue(index)), Ctx::Value) => Ok(Some(self.def(|dst| Inst::Upvalue(dst, *index)))),
            (L4::Ref(VarRef::SelfClosure), Ctx::Value) => Ok(Some(self.this)),
            (L4::Set(v, value), Ctx::Value) => {
                if !self.assign(*v, value)? {
                    return Ok(None);
                }
                Ok(Some(self.def(|dst| Inst::Const(dst, Value::VOID))))
            }
            (L4::Lambda(clos), Ctx::Value) => Ok(self.closures(&[clos], &[])?.first().copied()),
            (L4::App(f, args), Ctx::Value) => {
                let Some(f) = self.expr(f, Ctx::Value)? else { return Ok(None) };
                let Some(args) = self.args(args)? else { return Ok(None) };
                Ok(Some(self.def(|dst| Inst::Call { dst, f, args })))
            }
            (L4::Intrinsic(prim, args), Ctx::Value) => self.prim(*prim, args, false),
            (L4::ApplyIntrinsic(prim, args), Ctx::Value) => self.prim(*prim, args, true),
        }
    }

    /// Lowers `expr` for what it does, and returns whether control goes on past it.
    fn effect(&mut self, expr: &L4<'_, 'gc>) -> Result<bool, CompileError> {
        if let L4::Set(v, value) = expr {
            return self.assign(*v, value);
        }
        Ok(self.expr(expr, Ctx::Value)?.is_some())
    }

    /// Binds each of `binds` in turn, and returns whether control goes on past them.
    #[inline(never)]
    fn binds(&mut self, binds: &[Bind4<'_, 'gc>]) -> Result<bool, CompileError> {
        for bind in binds {
            match bind {
                // A body's forms before its last are bound to what they return, as often an
                // assignment's, which is void.
                Bind::Val(v, L4::Set(target, value)) if !self.sets.contains(v) => {
                    if !self.assign(*target, value)? {
                        return Ok(false);
                    }
                    self.voids.insert(*v);
                }
                Bind::Val(v, init) => {
                    let Some(val) = self.expr(init, Ctx::Value)? else { return Ok(false) };
                    self.bind_to(*v, val);
                }
                Bind::Fix(group) => {
                    let codes: std::vec::Vec<&Closure<'_, 'gc>> = group.iter().map(|(_, c)| c).collect();
                    let vars: std::vec::Vec<Var> = group.iter().map(|(v, _)| *v).collect();
                    self.closures(&codes, &vars)?;
                }
            }
        }
        Ok(true)
    }

    fn assign(&mut self, v: Var, value: &L4<'_, 'gc>) -> Result<bool, CompileError> {
        let Some(val) = self.expr(value, Ctx::Value)? else { return Ok(false) };
        self.lookup(v)?;
        self.env.insert(v, val);
        Ok(true)
    }

    fn unbind(&mut self, vars: impl IntoIterator<Item = Var>, assigned: usize) {
        for v in vars {
            self.env.remove(&v);
            self.voids.remove(&v);
        }
        self.assigned.truncate(assigned);
    }

    fn args(&mut self, args: &[L4<'_, 'gc>]) -> Result<Option<Vec<'a, Val>>, CompileError> {
        let mut vals = Vec::with_capacity_in(args.len(), self.arena);
        for arg in args {
            let Some(val) = self.expr(arg, Ctx::Value)? else { return Ok(None) };
            vals.push(val);
        }
        Ok(Some(vals))
    }

    /// `args`' values, evaluated in `order`.
    fn args_in(&mut self, args: &[L4<'_, 'gc>], order: &[usize]) -> Result<Option<Vec<'a, Val>>, CompileError> {
        let mut vals = self.arena.vec_of(self.this, args.len());
        for &i in order {
            let Some(val) = self.expr(&args[i], Ctx::Value)? else { return Ok(None) };
            vals[i] = val;
        }
        Ok(Some(vals))
    }

    fn prim(&mut self, prim: Prim, args: &[L4<'_, 'gc>], spread: bool) -> Result<Option<Val>, CompileError> {
        let Some(args) = self.args(args)? else { return Ok(None) };
        Ok(Some(self.def(|dst| Inst::Prim { dst, prim, args, spread })))
    }

    fn tail_prim(&mut self, prim: Prim, args: &[L4<'_, 'gc>], spread: bool) -> Result<Option<Val>, CompileError> {
        let Some(args) = self.args(args)? else { return Ok(None) };
        self.end(End::TailPrim { prim, args, spread });
        Ok(None)
    }

    #[inline(never)]
    fn branch(&mut self, test: &L4<'_, 'gc>, then: &L4<'_, 'gc>, other: &L4<'_, 'gc>, ctx: Ctx) -> Result<Option<Val>, CompileError> {
        let Some(test) = self.expr(test, Ctx::Value)? else { return Ok(None) };
        let (a, b) = (self.block(self.arena.vec()), self.block(self.arena.vec()));
        self.end(End::Branch { test, then: a, other: b });
        let n = self.assigned.len();
        let vars = self.assigned.clone();
        let before = self.snapshot(n);
        self.cur = a;
        let x = self.expr(then, ctx)?;
        let (end_a, env_a) = (self.cur, self.snapshot(n));
        self.restore(&vars, &before);
        self.cur = b;
        let y = self.expr(other, ctx)?;
        let (end_b, env_b) = (self.cur, self.snapshot(n));
        let (x, y) = match (x, y) {
            (None, None) => return Ok(None),
            (Some(x), None) => {
                self.cur = end_a;
                self.restore(&vars, &env_a);
                return Ok(Some(x));
            }
            (None, Some(y)) => return Ok(Some(y)),
            (Some(x), Some(y)) => (x, y),
        };
        let mut params = self.arena.vec();
        let (mut from_a, mut from_b) = (self.arena.vec(), self.arena.vec());
        let result = if x == y { x } else { self.fresh() };
        if x != y {
            params.push(result);
            from_a.push(x);
            from_b.push(y);
        }
        let mut merged = std::vec::Vec::new();
        for (i, (&va, &vb)) in env_a.iter().zip(&env_b).enumerate() {
            if va != vb {
                let p = self.fresh();
                params.push(p);
                from_a.push(va);
                from_b.push(vb);
                merged.push((vars[i], p));
            }
        }
        let join = self.block(params);
        self.cur = end_a;
        self.end(End::Jump(join, from_a));
        self.cur = end_b;
        self.end(End::Jump(join, from_b));
        self.cur = join;
        for (v, p) in merged {
            self.env.insert(v, p);
        }
        Ok(Some(result))
    }

    /// `scope`, then the code of each join of `group` something jumps to. In a value's place, they
    /// all go on to one block, taking the value and the group's assigned variables.
    #[inline(never)]
    fn join(&mut self, group: &[JoinCode<'_, 'gc>], scope: &L4<'_, 'gc>, ctx: Ctx) -> Result<Option<Val>, CompileError> {
        let carried: std::vec::Vec<Var> = if self.assigned.is_empty() {
            std::vec::Vec::new()
        } else {
            let mut sets = HashSet::default();
            sets_in(scope, &mut sets);
            group.iter().for_each(|code| sets_in(&code.body, &mut sets));
            self.assigned.iter().copied().filter(|v| sets.contains(v)).collect()
        };
        let index = self.groups.len();
        self.groups.push(carried.clone());
        for code in group {
            let params = code.params.iter().copied().collect_in(self.arena);
            self.joins.insert(code.id, Join { block: None, params, group: index });
        }
        let mut rest = None;
        let out = self.expr(scope, ctx)?;
        self.go_on(out, &carried, &mut rest);
        let mut lowered = vec![false; group.len()];
        while let Some(i) = (0..group.len()).find(|&i| !lowered[i] && self.joins[&group[i].id].block.is_some()) {
            lowered[i] = true;
            let code = &group[i];
            let block = self.joins[&code.id].block.expect("found jumped to");
            self.cur = block;
            let params = self.blocks[block.0 as usize].params.to_vec();
            let (declared, assigned) = params.split_at(code.params.len());
            let n = self.assigned.len();
            self.restore(&carried, assigned);
            for (&v, &p) in code.params.iter().zip(declared) {
                self.bind_to(v, p);
            }
            let out = self.expr(&code.body, ctx)?;
            self.unbind(code.params.iter().copied(), n);
            self.go_on(out, &carried, &mut rest);
        }
        for code in group {
            self.joins.remove(&code.id);
        }
        let Some(rest) = rest else { return Ok(None) };
        self.cur = rest;
        let params = self.blocks[rest.0 as usize].params.to_vec();
        self.restore(&carried, &params[1..]);
        Ok(Some(params[0]))
    }

    /// Jumps from where control is, with `out`, if it goes on, to `rest`, made if it isn't yet.
    fn go_on(&mut self, out: Option<Val>, carried: &[Var], rest: &mut Option<Block>) {
        let Some(out) = out else { return };
        let to = match *rest {
            Some(to) => to,
            None => {
                let arena = self.arena;
                let params = (0..=carried.len()).map(|_| self.fresh()).collect_in(arena);
                let to = self.block(params);
                *rest = Some(to);
                to
            }
        };
        let args = iter::once(out).chain(carried.iter().map(|v| self.env[v])).collect_in(self.arena);
        self.end(End::Jump(to, args));
    }

    #[inline(never)]
    fn jump(&mut self, id: Var, args: &[L4<'_, 'gc>]) -> Result<(), CompileError> {
        let join = self.joins.get(&id).ok_or(CompileError::Unbound(id))?;
        let order = order(self.arena, args, &join.params);
        let Some(mut vals) = (match order {
            Some(order) => self.args_in(args, &order)?,
            None => self.args(args)?,
        }) else {
            return Ok(());
        };
        let join = self.joins.get(&id).ok_or(CompileError::Unbound(id))?;
        let (block, params, group) = (join.block, join.params.len(), join.group);
        let carried = &self.groups[group];
        vals.extend(carried.iter().map(|v| self.env[v]));
        let to = match block {
            Some(to) => to,
            None => {
                let arena = self.arena;
                let params = (0..params + self.groups[group].len()).map(|_| self.fresh()).collect_in(arena);
                let to = self.block(params);
                self.joins.get_mut(&id).expect("looked up").block = Some(to);
                to
            }
        };
        self.end(End::Jump(to, vals));
        Ok(())
    }

    /// Closures of `codes`, bound to `vars` if they're a group's, before they capture them.
    #[inline(never)]
    fn closures(&mut self, codes: &[&Closure<'_, 'gc>], vars: &[Var]) -> Result<Vec<'a, Val>, CompileError> {
        let arena = self.arena;
        let dsts: Vec<'a, Val> = codes.iter().map(|_| self.fresh()).collect_in(arena);
        for (&v, &dst) in vars.iter().zip(&dsts) {
            self.bind_to(v, dst);
        }
        let mut lowered = Vec::with_capacity_in(codes.len(), arena);
        for clos in codes {
            let mut captures = Vec::with_capacity_in(clos.captures.len(), arena);
            for &src in &clos.captures {
                captures.push(match src {
                    UpvalSource::Local(v) => Captured::Val(self.lookup(v)?),
                    UpvalSource::Upvalue(u) => Captured::Upvalue(u),
                    UpvalSource::SelfClosure => Captured::Val(self.this),
                });
            }
            let upvalues = u32::try_from(captures.len()).map_err(|_| CompileError::TooManyConstants)?;
            let formals = Formals { params: &clos.params, optional: clos.optional, rest: clos.rest };
            lowered.push(Code { function: function(arena, Some(clos.id), formals, upvalues, &clos.body)?, captures });
        }
        self.push(Inst::Closures { dsts: dsts.clone(), codes: lowered });
        Ok(dsts)
    }
}

/// The order to evaluate a jump's `args` to `params` in, if they can go in any: each after the
/// others that read the parameter it's for where it can be, so the value it replaces is dead by
/// the time it's made, and can make way for it.
fn order<'a>(arena: &'a Arena, args: &[L4<'_, '_>], params: &[Var]) -> Option<Vec<'a, usize>> {
    let n = args.len();
    if !(2..=16).contains(&n) || n != params.len() || !args.iter().all(reorderable) {
        return None;
    }
    let mut done = arena.vec_of(false, n);
    let mut order = Vec::with_capacity_in(n, arena);
    while order.len() < n {
        let ready = |i: usize| !done[i] && !(0..n).any(|j| j != i && !done[j] && reads_local(&args[j], params[i]));
        let i = (0..n).find(|&i| ready(i)).or_else(|| (0..n).find(|&i| !done[i])).expect("one is left");
        done[i] = true;
        order.push(i);
    }
    Some(order)
}

/// Whether `expr` can be evaluated before or after others like it, doing nothing but make a value.
pub(crate) fn reorderable<'gc>(expr: &L4<'_, 'gc>) -> bool {
    match expr {
        L4::Quote(_) | L4::Ref(_) | L4::Lambda(_) => true,
        L4::If(a, b, c) => reorderable(a) && reorderable(b) && reorderable(c),
        L4::Seq(a, b) => reorderable(a) && reorderable(b),
        L4::Let(binds, body) => binds.iter().all(|b| matches!(b, Bind::Val(_, init) if reorderable(init))) && reorderable(body),
        L4::Intrinsic(Prim::Host(h), args) => h.purity != Purity::Impure && args.iter().all(reorderable),
        L4::Intrinsic(Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, _), _) => true,
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
                && args.iter().all(reorderable)
        }
        _ => false,
    }
}

/// Whether `expr` reads or assigns local `target`, or captures it.
pub(crate) fn reads_local<'gc>(expr: &L4<'_, 'gc>, target: Var) -> bool {
    match expr {
        L4::Quote(_) => false,
        L4::Ref(VarRef::Local(v)) => *v == target,
        L4::Set(v, value) => *v == target || reads_local(value, target),
        L4::Ref(_) => false,
        L4::If(a, b, c) => reads_local(a, target) || reads_local(b, target) || reads_local(c, target),
        L4::Seq(a, b) => reads_local(a, target) || reads_local(b, target),
        L4::Let(binds, body) => {
            binds.iter().any(|b| match b {
                Bind::Val(_, init) => reads_local(init, target),
                Bind::Fix(group) => group.iter().any(|(_, clos)| clos.captures.contains(&UpvalSource::Local(target))),
            }) || reads_local(body, target)
        }
        L4::Jump(_, args) | L4::Intrinsic(_, args) | L4::ApplyIntrinsic(_, args) => {
            args.iter().any(|a| reads_local(a, target))
        }
        L4::Join { group, scope } => reads_local(scope, target) || group.iter().any(|code| reads_local(&code.body, target)),
        L4::App(f, args) => reads_local(f, target) || args.iter().any(|a| reads_local(a, target)),
        L4::Lambda(clos) => clos.captures.contains(&UpvalSource::Local(target)),
    }
}

/// Where a value is defined: its block, and 0 for the block's start or 1 past the instruction.
#[cfg(any(debug_assertions, test))]
#[derive(Clone, Copy)]
struct Def {
    block: usize,
    after: usize,
}

/// Where each of a function's `values` is defined.
#[cfg(any(debug_assertions, test))]
struct Defs {
    values: u32,
    at: HashMap<Val, Def>,
}

#[cfg(any(debug_assertions, test))]
impl Defs {
    fn define(&mut self, v: Val, def: Def) -> Result<(), String> {
        if v.0 >= self.values {
            return Err(format!("{v} is past the function's values"));
        }
        if self.at.insert(v, def).is_some() {
            return Err(format!("{v} is defined twice"));
        }
        Ok(())
    }

    /// Whether `v` is defined on every way to position `at` of block `b`, with `idom` its
    /// blocks' immediate dominators.
    fn check(&self, idom: &[usize], v: Val, b: usize, at: usize) -> Result<(), String> {
        let def = self.at.get(&v).ok_or_else(|| format!("{v}, used in b{b}, isn't defined"))?;
        let ok = if def.block == b { def.after < at } else { dominates(idom, def.block, b) };
        if ok { Ok(()) } else { Err(format!("{v}, used in b{b}, isn't defined on every way there")) }
    }
}

/// Checks that `f` and the functions of its closures are well-formed: each value defined once,
/// where it's used, and every block reached, jumped to with as many values as it takes.
#[cfg(any(debug_assertions, test))]
pub(crate) fn verify(f: &Function<'_, '_>) -> Result<(), String> {
    let n = f.blocks.len();
    if n == 0 {
        return Err("no blocks".into());
    }
    if !f.blocks[0].params.is_empty() {
        return Err("the entry takes parameters".into());
    }
    let mut defs = Defs { values: f.values, at: HashMap::default() };
    for &v in iter::once(&f.this).chain(&f.params).chain(&f.rest) {
        defs.define(v, Def { block: 0, after: 0 })?;
    }
    for (b, block) in f.blocks.iter().enumerate() {
        for &p in &block.params {
            defs.define(p, Def { block: b, after: 0 })?;
        }
        for (i, inst) in block.insts.iter().enumerate() {
            for &d in inst.defs() {
                defs.define(d, Def { block: b, after: i + 1 })?;
            }
        }
    }
    let mut preds = vec![std::vec::Vec::new(); n];
    for (b, block) in f.blocks.iter().enumerate() {
        for to in block.end.successors() {
            let target = f.blocks.get(to.0 as usize).ok_or_else(|| format!("b{b} goes to {to}, which isn't a block"))?;
            if to.0 == 0 {
                return Err(format!("b{b} goes to the entry"));
            }
            preds[to.0 as usize].push(b);
            match &block.end {
                End::Jump(_, args) if args.len() != target.params.len() => {
                    return Err(format!("b{b} jumps to {to} with {} values, not {}", args.len(), target.params.len()));
                }
                End::Branch { .. } if !target.params.is_empty() => return Err(format!("b{b} branches to {to}, which takes parameters")),
                _ => {}
            }
        }
    }
    let idom = dominators(&f.blocks, &preds)?;
    // The emitter colours blocks in order, so each comes after those it's only reached through.
    if let Some(b) = (1..n).find(|&b| idom[b] >= b) {
        return Err(format!("b{b} comes before b{}, which it's only reached through", idom[b]));
    }
    let check = |v: Val, b: usize, at: usize| defs.check(&idom, v, b, at);
    for (b, block) in f.blocks.iter().enumerate() {
        for (i, inst) in block.insts.iter().enumerate() {
            // A group's closures capture each other.
            let at = if let Inst::Closures { .. } = inst { i + 2 } else { i + 1 };
            for v in inst.uses() {
                check(v, b, at)?;
            }
            match inst {
                Inst::Upvalue(_, index) if *index >= f.upvalues => return Err(format!("b{b} loads upvalue {index} of {}", f.upvalues)),
                Inst::Closures { dsts, codes } => {
                    if dsts.len() != codes.len() {
                        return Err(format!("b{b} makes {} closures into {} values", codes.len(), dsts.len()));
                    }
                    for code in codes {
                        if let Some(&Captured::Upvalue(u)) = code.captures.iter().find(|c| matches!(c, Captured::Upvalue(u) if *u >= f.upvalues)) {
                            return Err(format!("b{b} captures upvalue {u} of {}", f.upvalues));
                        }
                        if code.function.upvalues as usize != code.captures.len() {
                            return Err(format!("a closure in b{b} captures {} values for {} upvalues", code.captures.len(), code.function.upvalues));
                        }
                        verify(&code.function)?;
                    }
                }
                _ => {}
            }
        }
        for v in block.end.uses() {
            check(v, b, block.insts.len() + 1)?;
        }
    }
    Ok(())
}

/// Each block's immediate dominator, the entry its own, by Cooper, Harvey and Kennedy's
/// iteration, or an error if a block can't be reached.
pub(crate) fn dominators(blocks: &[BlockData<'_, '_>], preds: &[impl AsRef<[usize]>]) -> Result<std::vec::Vec<usize>, String> {
    let n = blocks.len();
    let mut order = std::vec::Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut stack = vec![(0, 0)];
    seen[0] = true;
    while let Some(&mut (b, ref mut next)) = stack.last_mut() {
        if let Some(to) = blocks[b].end.successors().nth(*next) {
            *next += 1;
            let to = to.0 as usize;
            if !seen[to] {
                seen[to] = true;
                stack.push((to, 0));
            }
        } else {
            order.push(b);
            stack.pop();
        }
    }
    if let Some(b) = seen.iter().position(|&s| !s) {
        return Err(format!("b{b} can't be reached"));
    }
    order.reverse();
    let mut number = vec![0; n];
    for (i, &b) in order.iter().enumerate() {
        number[b] = i;
    }
    let mut idom: std::vec::Vec<Option<usize>> = vec![None; n];
    idom[0] = Some(0);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order[1..] {
            let mut new = None;
            for &p in preds[b].as_ref() {
                if idom[p].is_none() {
                    continue;
                }
                new = Some(match new {
                    None => p,
                    Some(mut q) => {
                        let mut p = p;
                        while p != q {
                            while number[p] > number[q] {
                                p = idom[p].expect("processed");
                            }
                            while number[q] > number[p] {
                                q = idom[q].expect("processed");
                            }
                        }
                        p
                    }
                });
            }
            if new.is_some() && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    Ok(idom.into_iter().map(|d| d.expect("every block reached")).collect())
}

#[cfg(any(debug_assertions, test))]
fn dominates(idom: &[usize], a: usize, mut b: usize) -> bool {
    loop {
        if a == b {
            return true;
        }
        if b == 0 {
            return false;
        }
        b = idom[b];
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

struct Vals<'a>(&'a [Val]);

impl fmt::Display for Vals<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, v) in self.0.iter().enumerate() {
            write!(f, "{}{v}", if i == 0 { "" } else { " " })?;
        }
        Ok(())
    }
}

struct Constant<'a, 'gc>(&'a Value<'gc>);

impl fmt::Display for Constant<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v = *self.0;
        if let Some(n) = v.as_fixnum() {
            return write!(f, "{n}");
        }
        let name = [
            (Value::TRUE, "#t"),
            (Value::FALSE, "#f"),
            (Value::NIL, "()"),
            (Value::VOID, "#<void>"),
            (Value::UNDEFINED, "#<undefined>"),
            (Value::UNSUPPLIED, "#<unsupplied>"),
        ];
        f.write_str(name.iter().find(|(c, _)| *c == v).map_or("#<object>", |(_, name)| name))
    }
}

struct PrimName(Prim);

impl fmt::Display for PrimName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Prim::Intrinsic(i) => f.write_str(i.name()),
            Prim::Read(r) => f.write_str(r.name()),
            Prim::Request(r) => f.write_str(r.name()),
            Prim::Host(h) => write!(f, "host {}", h.name),
            Prim::Slot(op, slot) => {
                let name = match op {
                    SlotOp::Load => "load-slot",
                    SlotOp::LoadChecked => "load-slot-checked",
                    SlotOp::Store => "store-slot",
                    SlotOp::StoreChecked => "store-slot-checked",
                };
                write!(f, "{name} {slot}")
            }
        }
    }
}

fn spread(spread: bool) -> &'static str {
    if spread { "apply " } else { "" }
}

fn args(args: &[Val]) -> String {
    if args.is_empty() { String::new() } else { format!(" {}", Vals(args)) }
}

/// Prints the function, then those of its closures.
impl fmt::Display for Function<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.id {
            Some(id) => write!(f, "function {id}")?,
            None => write!(f, "function")?,
        }
        let required = self.params.len() - self.optional as usize;
        write!(f, " ({}", Vals(&self.params[..required]))?;
        for p in &self.params[required..] {
            write!(f, " [{p}]")?;
        }
        if let Some(rest) = self.rest {
            write!(f, " . {rest}")?;
        }
        writeln!(f, ") closure {}:", self.this)?;
        let mut nested = std::vec::Vec::new();
        for (b, block) in self.blocks.iter().enumerate() {
            if block.params.is_empty() {
                writeln!(f, "b{b}:")?;
            } else {
                writeln!(f, "b{b}({}):", Vals(&block.params))?;
            }
            for inst in &block.insts {
                match inst {
                    Inst::Const(dst, value) => writeln!(f, "  {dst} = {}", Constant(value))?,
                    Inst::Upvalue(dst, index) => writeln!(f, "  {dst} = upvalue {index}")?,
                    Inst::Prim { dst, prim, args: a, spread: s } => writeln!(f, "  {dst} = {}{}{}", spread(*s), PrimName(*prim), args(a))?,
                    Inst::Call { dst, f: callee, args: a } => writeln!(f, "  {dst} = call {callee}{}", args(a))?,
                    Inst::Closures { dsts, codes } => {
                        write!(f, "  {} = closures", Vals(dsts))?;
                        for code in codes {
                            write!(f, " [{}", code.function.id.unwrap_or(0))?;
                            for c in &code.captures {
                                match c {
                                    Captured::Val(v) => write!(f, " {v}")?,
                                    Captured::Upvalue(u) => write!(f, " upvalue {u}")?,
                                }
                            }
                            write!(f, "]")?;
                            nested.push(&code.function);
                        }
                        writeln!(f)?;
                    }
                }
            }
            match &block.end {
                End::Jump(to, a) => writeln!(f, "  jump {to}({})", Vals(a))?,
                End::Branch { test, then, other } => writeln!(f, "  branch {test} {then} {other}")?,
                End::Return(v) => writeln!(f, "  return {v}")?,
                End::TailCall { f: callee, args: a } => writeln!(f, "  tail-call {callee}{}", args(a))?,
                End::TailPrim { prim, args: a, spread: s } => writeln!(f, "  tail {}{}{}", spread(*s), PrimName(*prim), args(a))?,
            }
        }
        for function in nested {
            write!(f, "{function}")?;
        }
        Ok(())
    }
}
