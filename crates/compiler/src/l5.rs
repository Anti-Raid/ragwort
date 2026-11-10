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

use crate::hash::{HashMap, HashSet};

use crate::ir::l4::{Bind, Fun, Id, JoinCode, L4, Node, Span};
use crate::ir::{UpvalSource, VarRef};
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

/// The code compiled, as its functions: the last the code's own, and each other one the code of
/// closures a function after it makes, which refer to it by its index.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Program<'a, 'gc> {
    pub(crate) functions: Vec<'a, Function<'a, 'gc>>,
}

impl<'a, 'gc> Program<'a, 'gc> {
    pub(crate) fn root(&self) -> &Function<'a, 'gc> {
        self.functions.last().expect("a program has the code's own function")
    }
}

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
    Closures { dsts: Vec<'a, Val>, codes: Vec<'a, Code<'a>> },
}

/// A closure's code, the index of its function in the [`Program`], and what it captures, in the
/// order its upvalues are.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Code<'a> {
    pub(crate) function: u32,
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

/// The code compiled, of no parameters, from `root` of `tree`, as [`L5`](self). Each function
/// is lowered by a [`Builder`] of its own, those of closures being made on a stack above theirs.
pub(crate) fn lower<'a, 'id, 'gc>(arena: &'a Arena, tree: &L4<'id, 'gc>, root: Id<'id>) -> Result<Program<'a, 'gc>, CompileError> {
    let top = Formals { params: &[], optional: 0, rest: None };
    let mut stack = vec![Builder::new(arena, tree, None, top, 0, root)];
    let mut functions = std::vec::Vec::new();
    loop {
        let builder = stack.last_mut().expect("lowering until the code is done");
        if let Some((fun, upvalues)) = builder.run()? {
            let clos = tree[fun];
            let formals = Formals { params: &tree[clos.params], optional: clos.optional, rest: clos.rest };
            stack.push(Builder::new(arena, tree, Some(clos.id), formals, upvalues, clos.body));
            continue;
        }
        let index = u32::try_from(functions.len()).map_err(|_| CompileError::TooManyConstants)?;
        functions.push(stack.pop().expect("lowered").finish());
        match stack.last_mut() {
            Some(parent) => parent.give(index),
            None => return Ok(Program { functions: functions.into_iter().collect_in(arena) }),
        }
    }
}

/// Panics if `program` isn't well-formed, as a debug build checks.
#[cfg(debug_assertions)]
pub(crate) fn check(program: &Program<'_, '_>) {
    if let Err(e) = verify(program) {
        panic!("malformed L5: {e}\n{program}");
    }
}

#[derive(Clone, Copy)]
struct Formals<'a> {
    params: &'a [Var],
    optional: u32,
    rest: Option<Var>,
}

/// Adds the locals the frame from `root` assigns to `sets`.
fn sets_in<'id>(tree: &L4<'id, '_>, root: Id<'id>, sets: &mut HashSet<Var>) {
    sets.extend(tree.frame(root).filter_map(|id| if let Node::Set(v, _) = tree[id] { Some(v) } else { None }));
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

struct Builder<'a, 't, 'id, 'gc> {
    arena: &'a Arena,
    tree: &'t L4<'id, 'gc>,
    id: Option<u32>,
    params: Vec<'a, Val>,
    optional: u32,
    rest: Option<Val>,
    upvalues: u32,
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
    /// What's left to do, the next last.
    todo: std::vec::Vec<Task<'a, 'id>>,
    /// The value of the expression lowered last, if control goes on past it, which the task after
    /// it takes.
    ret: Option<Val>,
}

/// What lowering a function does next: an expression, or going on from one with its [`Builder::ret`].
enum Task<'a, 'id> {
    Expr(Id<'id>, Ctx),
    /// An `if`'s arms, after its test.
    Test { then: Id<'id>, other: Id<'id>, ctx: Ctx },
    /// The other arm, from `other`, after the first, with the assigned variables' values before it.
    Then { other: Id<'id>, ctx: Ctx, b: Block, vars: std::vec::Vec<Var>, before: std::vec::Vec<Val> },
    /// Where the arms meet: the first's value, where it ended and the assigned variables there.
    Else { x: Option<Val>, end_a: Block, env_a: std::vec::Vec<Val>, vars: std::vec::Vec<Var> },
    /// A `Seq`'s second, after its first.
    Seq(Id<'id>, Ctx),
    Bind(Rest<'id>),
    /// `v` bound to the value made, or as void to what an assignment made, then the next.
    Bound { v: Var, void: bool, next: Rest<'id> },
    /// A `Let`'s variables out of scope.
    Unbind { binds: Span<'id, Bind<'id>>, assigned: usize },
    Assign(Var),
    /// Void, as an assignment's value.
    Void,
    Return,
    /// A join group's scope or one of its codes, the `code`th with `n` assigned variables, done.
    Join { codes: Span<'id, JoinCode<'id>>, carried: std::vec::Vec<Var>, rest: Option<Block>, lowered: std::vec::Vec<bool>, ctx: Ctx, code: Option<(usize, usize)> },
    /// A call's arguments, after its callee.
    Callee { args: Span<'id, Id<'id>>, tail: bool },
    /// The `at`th of `args`, in `order` if any, after those before, whose values `vals` has.
    Args { args: Span<'id, Id<'id>>, order: Option<Vec<'a, usize>>, at: usize, vals: Vec<'a, Val>, then: Use },
    /// Closures of `funs`, bound to `dsts`, as many of whose codes as are lowered, and the
    /// captures of the one being lowered.
    Closures { funs: std::vec::Vec<Fun<'id>>, dsts: Vec<'a, Val>, codes: Vec<'a, Code<'a>>, captures: Option<Vec<'a, Captured>> },
}

/// A `Let`'s bindings from the `i`th, then its body.
#[derive(Clone, Copy)]
struct Rest<'id> {
    binds: Span<'id, Bind<'id>>,
    i: usize,
    body: Id<'id>,
    ctx: Ctx,
}

/// What arguments' values are for.
#[derive(Clone, Copy)]
enum Use {
    Call(Val),
    TailCall(Val),
    Prim(Prim, bool),
    TailPrim(Prim, bool),
    Jump(Var),
}

impl<'a, 't, 'id, 'gc> Builder<'a, 't, 'id, 'gc> {
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

    fn new(arena: &'a Arena, tree: &'t L4<'id, 'gc>, id: Option<u32>, formals: Formals<'_>, upvalues: u32, body: Id<'id>) -> Self {
        let mut sets = HashSet::default();
        sets_in(tree, body, &mut sets);
        let mut b = Builder {
            arena,
            tree,
            id,
            params: arena.vec(),
            optional: formals.optional,
            rest: None,
            upvalues,
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
            todo: vec![Task::Expr(body, Ctx::Tail)],
            ret: None,
        };
        b.this = b.fresh();
        b.params = formals.params.iter().map(|&v| b.bind(v)).collect_in(arena);
        b.rest = formals.rest.map(|v| b.bind(v));
        b
    }

    fn finish(self) -> Function<'a, 'gc> {
        let blocks = self.blocks.into_iter().map(|block| BlockData {
            params: block.params,
            insts: block.insts,
            end: block.end.expect("every block made ends"),
        });
        let (id, this, params, optional, rest, upvalues) = (self.id, self.this, self.params, self.optional, self.rest, self.upvalues);
        Function { id, this, params, optional, rest, upvalues, blocks: blocks.collect_in(self.arena), values: self.next }
    }

    /// Lowers until the function is done, or until the code of one of its closures is wanted,
    /// which [`Builder::give`] gives it.
    fn run(&mut self) -> Result<Option<(Fun<'id>, u32)>, CompileError> {
        let (arena, tree) = (self.arena, self.tree);
        while let Some(task) = self.todo.pop() {
            match task {
                Task::Expr(expr, ctx) => self.start(expr, ctx)?,
                Task::Test { then, other, ctx } => {
                    let Some(test) = self.ret else { continue };
                    let (a, b) = (self.block(arena.vec()), self.block(arena.vec()));
                    self.end(End::Branch { test, then: a, other: b });
                    let vars = self.assigned.clone();
                    let before = self.snapshot(vars.len());
                    self.cur = a;
                    self.todo.push(Task::Then { other, ctx, b, vars, before });
                    self.todo.push(Task::Expr(then, ctx));
                }
                Task::Then { other, ctx, b, vars, before } => {
                    let (x, end_a, env_a) = (self.ret, self.cur, self.snapshot(vars.len()));
                    self.restore(&vars, &before);
                    self.cur = b;
                    self.todo.push(Task::Else { x, end_a, env_a, vars });
                    self.todo.push(Task::Expr(other, ctx));
                }
                Task::Else { x, end_a, env_a, vars } => self.meet(x, end_a, &env_a, &vars),
                Task::Seq(b, ctx) => {
                    if self.ret.is_some() {
                        self.todo.push(Task::Expr(b, ctx));
                    }
                }
                Task::Bind(rest) => self.bind_next(rest),
                Task::Bound { v, void, next } => {
                    let Some(val) = self.ret else { continue };
                    if void {
                        self.voids.insert(v);
                    } else {
                        self.bind_to(v, val);
                    }
                    self.todo.push(Task::Bind(next));
                }
                Task::Unbind { binds, assigned } => self.unbind(tree[binds].iter().flat_map(|&bind| tree.vars(bind)), assigned),
                Task::Assign(v) => {
                    let Some(val) = self.ret else { continue };
                    self.lookup(v)?;
                    self.env.insert(v, val);
                }
                Task::Void => {
                    if self.ret.is_some() {
                        self.ret = Some(self.def(|dst| Inst::Const(dst, Value::VOID)));
                    }
                }
                Task::Return => {
                    if let Some(v) = self.ret.take() {
                        self.end(End::Return(v));
                    }
                }
                Task::Join { codes, carried, rest, lowered, ctx, code } => self.join_next(codes, carried, rest, lowered, ctx, code),
                Task::Callee { args, tail } => {
                    let Some(f) = self.ret else { continue };
                    self.args(args, None, if tail { Use::TailCall(f) } else { Use::Call(f) });
                }
                Task::Args { args, order, at, mut vals, then } => {
                    if at > 0 {
                        let Some(val) = self.ret else { continue };
                        match &order {
                            Some(order) => vals[order[at - 1]] = val,
                            None => vals.push(val),
                        }
                    }
                    let list = &tree[args];
                    if at == list.len() {
                        self.finish_args(then, vals)?;
                        continue;
                    }
                    let next = order.as_ref().map_or(at, |order| order[at]);
                    self.todo.push(Task::Args { args, order, at: at + 1, vals, then });
                    self.todo.push(Task::Expr(list[next], Ctx::Value));
                }
                Task::Closures { funs, dsts, codes, captures } => {
                    debug_assert!(captures.is_none(), "the code of a closure is given before going on");
                    let Some(&fun) = funs.get(codes.len()) else {
                        self.ret = dsts.first().copied();
                        self.push(Inst::Closures { dsts, codes });
                        continue;
                    };
                    let clos = tree[fun];
                    let mut captures = Vec::with_capacity_in(tree[clos.captures].len(), arena);
                    for &src in &tree[clos.captures] {
                        captures.push(match src {
                            UpvalSource::Local(v) => Captured::Val(self.lookup(v)?),
                            UpvalSource::Upvalue(u) => Captured::Upvalue(u),
                            UpvalSource::SelfClosure => Captured::Val(self.this),
                        });
                    }
                    let upvalues = u32::try_from(captures.len()).map_err(|_| CompileError::TooManyConstants)?;
                    self.todo.push(Task::Closures { funs, dsts, codes, captures: Some(captures) });
                    return Ok(Some((fun, upvalues)));
                }
            }
        }
        Ok(None)
    }

    /// The code of the closure [`Builder::run`] wanted last, by its index in the program.
    fn give(&mut self, function: u32) {
        let Some(Task::Closures { codes, captures, .. }) = self.todo.last_mut() else {
            unreachable!("a closure's code is lowered when its closures want it")
        };
        codes.push(Code { function, captures: captures.take().expect("captured before its code was lowered") });
    }

    /// Starts lowering `expr`, whose value, if `ctx` is a value and control goes on past it, the
    /// task after its own takes.
    fn start(&mut self, expr: Id<'id>, ctx: Ctx) -> Result<(), CompileError> {
        self.ret = None;
        match (self.tree[expr], ctx) {
            (Node::If(test, then, other), _) => {
                self.todo.push(Task::Test { then, other, ctx });
                self.todo.push(Task::Expr(test, Ctx::Value));
            }
            (Node::Seq(a, b), _) => {
                self.todo.push(Task::Seq(b, ctx));
                self.effect(a);
            }
            (Node::Let(binds, body), _) => {
                self.todo.push(Task::Unbind { binds, assigned: self.assigned.len() });
                self.todo.push(Task::Bind(Rest { binds, i: 0, body, ctx }));
            }
            (Node::Join(scope, codes), _) => self.join(codes, scope, ctx),
            (Node::Jump(id, args), _) => self.jump(id, args)?,
            (Node::App(f, args), _) => {
                self.todo.push(Task::Callee { args, tail: ctx == Ctx::Tail });
                self.todo.push(Task::Expr(f, Ctx::Value));
            }
            (Node::Intrinsic(prim @ (Prim::Request(_) | Prim::Host(_)), args), Ctx::Tail) => self.args(args, None, Use::TailPrim(prim, false)),
            (Node::ApplyIntrinsic(prim @ Prim::Request(_), args), Ctx::Tail) => self.args(args, None, Use::TailPrim(prim, true)),
            (_, Ctx::Tail) => {
                self.todo.push(Task::Return);
                self.todo.push(Task::Expr(expr, Ctx::Value));
            }
            (Node::Quote(value), Ctx::Value) => self.ret = Some(self.def(|dst| Inst::Const(dst, value))),
            (Node::Ref(VarRef::Local(v)), Ctx::Value) => self.ret = Some(self.lookup(v)?),
            (Node::Ref(VarRef::Upvalue(index)), Ctx::Value) => self.ret = Some(self.def(|dst| Inst::Upvalue(dst, index))),
            (Node::Ref(VarRef::SelfClosure), Ctx::Value) => self.ret = Some(self.this),
            (Node::Set(v, value), Ctx::Value) => {
                self.todo.push(Task::Void);
                self.todo.push(Task::Assign(v));
                self.todo.push(Task::Expr(value, Ctx::Value));
            }
            (Node::Lambda(fun), Ctx::Value) => self.closures(vec![fun], &[]),
            (Node::Intrinsic(prim, args), Ctx::Value) => self.args(args, None, Use::Prim(prim, false)),
            (Node::ApplyIntrinsic(prim, args), Ctx::Value) => self.args(args, None, Use::Prim(prim, true)),
        }
        Ok(())
    }

    /// Starts lowering `expr` for what it does, after which control goes on if the value the next
    /// task takes is something.
    fn effect(&mut self, expr: Id<'id>) {
        if let Node::Set(v, value) = self.tree[expr] {
            self.todo.push(Task::Assign(v));
            self.todo.push(Task::Expr(value, Ctx::Value));
        } else {
            self.todo.push(Task::Expr(expr, Ctx::Value));
        }
    }

    /// The `rest.i`th binding, control having gone on past those before, or the body after the last.
    fn bind_next(&mut self, rest: Rest<'id>) {
        let tree = self.tree;
        let Some(&bind) = tree[rest.binds].get(rest.i) else {
            self.todo.push(Task::Expr(rest.body, rest.ctx));
            return;
        };
        let next = Rest { i: rest.i + 1, ..rest };
        match bind {
            Bind::Val(v, init) => match tree[init] {
                // A body's forms before its last are bound to what they return, as often an
                // assignment's, which is void.
                Node::Set(target, value) if !self.sets.contains(&v) => {
                    self.todo.push(Task::Bound { v, void: true, next });
                    self.todo.push(Task::Assign(target));
                    self.todo.push(Task::Expr(value, Ctx::Value));
                }
                _ => {
                    self.todo.push(Task::Bound { v, void: false, next });
                    self.todo.push(Task::Expr(init, Ctx::Value));
                }
            },
            Bind::Fix(group) => {
                self.todo.push(Task::Bind(next));
                let vars: std::vec::Vec<Var> = tree[group].iter().map(|&(v, _)| v).collect();
                self.closures(tree[group].iter().map(|&(_, fun)| fun).collect(), &vars);
            }
        }
    }

    fn unbind(&mut self, vars: impl IntoIterator<Item = Var>, assigned: usize) {
        for v in vars {
            self.env.remove(&v);
            self.voids.remove(&v);
        }
        self.assigned.truncate(assigned);
    }

    /// Starts lowering `args`, in `order` if any, for `then`.
    fn args(&mut self, args: Span<'id, Id<'id>>, order: Option<Vec<'a, usize>>, then: Use) {
        let n = self.tree[args].len();
        let vals = if order.is_some() { self.arena.vec_of(self.this, n) } else { Vec::with_capacity_in(n, self.arena) };
        self.todo.push(Task::Args { args, order, at: 0, vals, then });
    }

    fn finish_args(&mut self, then: Use, args: Vec<'a, Val>) -> Result<(), CompileError> {
        self.ret = match then {
            Use::Call(f) => Some(self.def(|dst| Inst::Call { dst, f, args })),
            Use::TailCall(f) => {
                self.end(End::TailCall { f, args });
                None
            }
            Use::Prim(prim, spread) => Some(self.def(|dst| Inst::Prim { dst, prim, args, spread })),
            Use::TailPrim(prim, spread) => {
                self.end(End::TailPrim { prim, args, spread });
                None
            }
            Use::Jump(id) => {
                self.jump_with(id, args)?;
                None
            }
        };
        Ok(())
    }

    /// Where an `if`'s arms meet, the first having ended in `end_a` with `x` and `env_a` the values
    /// of `vars`, the second where control is.
    fn meet(&mut self, x: Option<Val>, end_a: Block, env_a: &[Val], vars: &[Var]) {
        let y = self.ret;
        let (end_b, env_b) = (self.cur, self.snapshot(vars.len()));
        let (x, y) = match (x, y) {
            (None, None) => return,
            (Some(x), None) => {
                self.cur = end_a;
                self.restore(vars, env_a);
                self.ret = Some(x);
                return;
            }
            (None, Some(_)) => return,
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
        self.ret = Some(result);
    }

    /// Starts on `scope`, then the code of each join of `codes` something jumps to. In a value's
    /// place, they all go on to one block, taking the value and the group's assigned variables.
    fn join(&mut self, codes: Span<'id, JoinCode<'id>>, scope: Id<'id>, ctx: Ctx) {
        let tree = self.tree;
        let group = &tree[codes];
        let carried: std::vec::Vec<Var> = if self.assigned.is_empty() {
            std::vec::Vec::new()
        } else {
            let mut sets = HashSet::default();
            sets_in(tree, scope, &mut sets);
            group.iter().for_each(|code| sets_in(tree, code.body, &mut sets));
            self.assigned.iter().copied().filter(|v| sets.contains(v)).collect()
        };
        let index = self.groups.len();
        self.groups.push(carried.clone());
        for code in group {
            let params = tree[code.params].iter().copied().collect_in(self.arena);
            self.joins.insert(code.id, Join { block: None, params, group: index });
        }
        let lowered = vec![false; group.len()];
        self.todo.push(Task::Join { codes, carried, rest: None, lowered, ctx, code: None });
        self.todo.push(Task::Expr(scope, ctx));
    }

    /// After a join group's scope or one of its codes: the next code something jumps to, or what
    /// they go on to.
    fn join_next(&mut self, codes: Span<'id, JoinCode<'id>>, carried: std::vec::Vec<Var>, mut rest: Option<Block>, mut lowered: std::vec::Vec<bool>, ctx: Ctx, code: Option<(usize, usize)>) {
        let tree = self.tree;
        let group = &tree[codes];
        if let Some((i, n)) = code {
            self.unbind(tree[group[i].params].iter().copied(), n);
        }
        self.go_on(self.ret, &carried, &mut rest);
        if let Some(i) = (0..group.len()).find(|&i| !lowered[i] && self.joins[&group[i].id].block.is_some()) {
            lowered[i] = true;
            let code = group[i];
            let block = self.joins[&code.id].block.expect("found jumped to");
            self.cur = block;
            let params = self.blocks[block.0 as usize].params.to_vec();
            let (declared, assigned) = params.split_at(tree[code.params].len());
            let n = self.assigned.len();
            self.restore(&carried, assigned);
            for (&v, &p) in tree[code.params].iter().zip(declared) {
                self.bind_to(v, p);
            }
            self.todo.push(Task::Join { codes, carried, rest, lowered, ctx, code: Some((i, n)) });
            self.todo.push(Task::Expr(code.body, ctx));
            return;
        }
        for code in group {
            self.joins.remove(&code.id);
        }
        self.ret = rest.map(|rest| {
            self.cur = rest;
            let params = self.blocks[rest.0 as usize].params.to_vec();
            self.restore(&carried, &params[1..]);
            params[0]
        });
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

    fn jump(&mut self, id: Var, args: Span<'id, Id<'id>>) -> Result<(), CompileError> {
        let tree = self.tree;
        let join = self.joins.get(&id).ok_or(CompileError::Unbound(id))?;
        let order = order(self.arena, tree, &tree[args], &join.params);
        self.args(args, order, Use::Jump(id));
        Ok(())
    }

    /// A jump to join `id` with `vals` for its parameters.
    fn jump_with(&mut self, id: Var, mut vals: Vec<'a, Val>) -> Result<(), CompileError> {
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

    /// Starts on closures of `funs`, bound to `vars` if they're a group's, before they capture them.
    fn closures(&mut self, funs: std::vec::Vec<Fun<'id>>, vars: &[Var]) {
        let arena = self.arena;
        let dsts: Vec<'a, Val> = funs.iter().map(|_| self.fresh()).collect_in(arena);
        for (&v, &dst) in vars.iter().zip(&dsts) {
            self.bind_to(v, dst);
        }
        let codes = Vec::with_capacity_in(funs.len(), arena);
        self.todo.push(Task::Closures { funs, dsts, codes, captures: None });
    }
}

/// The order to evaluate a jump's `args` to `params` in, if they can go in any: each after the
/// others that read the parameter it's for where it can be, so the value it replaces is dead by
/// the time it's made, and can make way for it.
fn order<'a, 'id>(arena: &'a Arena, tree: &L4<'id, '_>, args: &[Id<'id>], params: &[Var]) -> Option<Vec<'a, usize>> {
    let n = args.len();
    if !(2..=16).contains(&n) || n != params.len() || !args.iter().all(|&arg| reorderable(tree, arg)) {
        return None;
    }
    let mut done = arena.vec_of(false, n);
    let mut order = Vec::with_capacity_in(n, arena);
    while order.len() < n {
        let ready = |i: usize| !done[i] && !(0..n).any(|j| j != i && !done[j] && reads_local(tree, args[j], params[i]));
        let i = (0..n).find(|&i| ready(i)).or_else(|| (0..n).find(|&i| !done[i])).expect("one is left");
        done[i] = true;
        order.push(i);
    }
    Some(order)
}

/// Whether `expr` can be evaluated before or after others like it, doing nothing but make a value.
pub(crate) fn reorderable<'id>(tree: &L4<'id, '_>, expr: Id<'id>) -> bool {
    tree.frame(expr).all(|id| match tree[id] {
        Node::Quote(_) | Node::Ref(_) | Node::Lambda(_) | Node::If(..) | Node::Seq(..) => true,
        Node::Let(binds, _) => tree[binds].iter().all(|bind| matches!(bind, Bind::Val(..))),
        Node::Intrinsic(Prim::Host(h), _) => h.purity.is_reorderable(),
        Node::Intrinsic(Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, _), _) => true,
        Node::Intrinsic(Prim::Intrinsic(i), _) => i.is_reorderable(),
        _ => false,
    })
}

/// Whether `expr` reads or assigns local `target`, or captures it.
pub(crate) fn reads_local<'id>(tree: &L4<'id, '_>, expr: Id<'id>, target: Var) -> bool {
    let captures = |fun: Fun<'id>| tree[tree[fun].captures].contains(&UpvalSource::Local(target));
    tree.frame(expr).any(|id| match tree[id] {
        Node::Ref(VarRef::Local(v)) | Node::Set(v, _) => v == target,
        Node::Lambda(fun) => captures(fun),
        Node::Let(binds, _) => tree[binds].iter().any(|&bind| matches!(bind, Bind::Fix(group) if tree[group].iter().any(|&(_, fun)| captures(fun)))),
        _ => false,
    })
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
/// Whether each of `program`'s functions is well-formed, and is the code of closures of one
/// function after it, but the last.
#[cfg(any(debug_assertions, test))]
pub(crate) fn verify(program: &Program<'_, '_>) -> Result<(), String> {
    let functions = &program.functions;
    if functions.is_empty() {
        return Err("no functions".into());
    }
    let mut made = vec![0usize; functions.len()];
    for (i, f) in functions.iter().enumerate() {
        verify_function(f, &functions[..i]).map_err(|e| format!("function {i}: {e}"))?;
        for block in &f.blocks {
            for inst in &block.insts {
                if let Inst::Closures { codes, .. } = inst {
                    codes.iter().for_each(|code| made[code.function as usize] += 1);
                }
            }
        }
    }
    let last = functions.len() - 1;
    match made.iter().enumerate().find(|&(i, &n)| n != usize::from(i < last)) {
        Some((i, n)) => Err(format!("function {i} is the code of closures {n} functions make")),
        None => Ok(()),
    }
}

/// Whether `f` is well-formed, its closures' codes among `before`.
#[cfg(any(debug_assertions, test))]
pub(crate) fn verify_function(f: &Function<'_, '_>, before: &[Function<'_, '_>]) -> Result<(), String> {
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
                        let Some(function) = before.get(code.function as usize) else {
                            return Err(format!("a closure in b{b} has the code of function {}, which isn't before it", code.function));
                        };
                        if function.upvalues as usize != code.captures.len() {
                            return Err(format!("a closure in b{b} captures {} values for {} upvalues", code.captures.len(), function.upvalues));
                        }
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

/// Prints the code's function, then those of its closures, each before those of its own.
impl fmt::Display for Program<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut todo = vec![self.root()];
        while let Some(function) = todo.pop() {
            let at = todo.len();
            function.print(f, &self.functions, &mut todo)?;
            todo[at..].reverse();
        }
        Ok(())
    }
}

impl<'a, 'gc> Function<'a, 'gc> {
    /// Prints the function, adding those of its closures, among `functions`, to `nested`.
    fn print<'p>(&self, f: &mut fmt::Formatter<'_>, functions: &'p [Function<'a, 'gc>], nested: &mut std::vec::Vec<&'p Function<'a, 'gc>>) -> fmt::Result {
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
                            let function = &functions[code.function as usize];
                            write!(f, " [{}", function.id.unwrap_or(0))?;
                            for c in &code.captures {
                                match c {
                                    Captured::Val(v) => write!(f, " {v}")?,
                                    Captured::Upvalue(u) => write!(f, " upvalue {u}")?,
                                }
                            }
                            write!(f, "]")?;
                            nested.push(function);
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
        Ok(())
    }
}
