//! Pass 8 (`L4 -> L5`): transforms each function into a control-flow graph of basic blocks in SSA form.
//!
//! Every SSA value ([`Val`]) is defined exactly once: at function entry, as a basic block parameter,
//! or as the destination of an instruction. Control-flow merges are represented using block parameters
//! passed by jump terminators (following Cranelift-style block arguments rather than traditional φ-nodes).
//! An unboxed `set!` assigns a fresh SSA value to its variable. Contified joins are lowered into basic
//! blocks that accept any variables mutated within their group as additional block parameters. Only jumps
//! can pass arguments to basic blocks; conditional branches target blocks without parameters.
//!
//! A block terminator that performs an operation capable of capturing the current continuation or modifying
//! continuation marks (such as a function call, VM request, or host call) remains a tail call when in tail
//! position. In contrast, intrinsics and memory reads cannot capture continuations; in tail position, they
//! are lowered into an instruction followed by an explicit [`End::Return`].

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

/// An SSA value identifier within a function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Val(pub(crate) u32);

/// A basic block identifier, representing an index into [`Function::blocks`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Block(pub(crate) u32);

/// A compiled program consisting of a sequence of lowered functions.
///
/// The final function in the list represents the top-level program entry point. Earlier functions
/// define the bodies of closures created by subsequent functions, which reference them by their index.
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
    /// The source lambda ID from which this function was derived, or `None` for top-level code.
    pub(crate) id: Option<u32>,
    /// The SSA value representing the currently executing closure object (`self`).
    pub(crate) this: Val,
    /// The formal parameter values. The caller may omit up to the last `optional` parameters.
    pub(crate) params: Vec<'a, Val>,
    pub(crate) optional: u32,
    /// The rest parameter holding any surplus arguments as a Scheme list, or `None` if absent.
    pub(crate) rest: Option<Val>,
    /// The number of upvalues captured by closures of this function.
    pub(crate) upvalues: u32,
    /// The basic blocks forming the function's control flow graph.
    ///
    /// The first block (`blocks[0]`) is the entry block; it takes no parameters and has no incoming predecessors.
    pub(crate) blocks: Vec<'a, BlockData<'a, 'gc>>,
    /// The total number of SSA values allocated in this function. All valid `Val` IDs are strictly less than this.
    pub(crate) values: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct BlockData<'a, 'gc> {
    pub(crate) params: Vec<'a, Val>,
    pub(crate) insts: Vec<'a, Inst<'a, 'gc>>,
    /// The source site of each instruction, parallel to `insts`: a site number of the compilation's `Sites`, or 0.
    pub(crate) sites: std::vec::Vec<u32>,
    pub(crate) end: End<'a>,
    /// The source site of `end`.
    pub(crate) end_site: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Inst<'a, 'gc> {
    Const(Val, Value<'gc>),
    Upvalue(Val, u32),
    /// Applies primitive `prim` to `args`. If `spread` is true, the final argument is a list whose
    /// elements are unpacked. Storing into a module variable yields a void value.
    Prim { dst: Val, prim: Prim, args: Vec<'a, Val>, spread: bool },
    Call { dst: Val, f: Val, args: Vec<'a, Val> },
    /// Instantiates closures for each entry in `codes` and binds them to `dsts`. All closure objects
    /// are allocated before environment captures are resolved, enabling mutual recursion.
    Closures { dsts: Vec<'a, Val>, codes: Vec<'a, Code<'a>> },
}

/// The specification for instantiating a closure: the index of its underlying [`Function`] in the
/// [`Program`], followed by its captured values in upvalue index order.
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
    /// Branches conditionally: jumps to `other` if `test` evaluates to `#f`, otherwise jumps to `then`.
    Branch { test: Val, then: Block, other: Block },
    Return(Val),
    TailCall { f: Val, args: Vec<'a, Val> },
    /// A VM request or host function invocation occurring in tail position.
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

    /// Invokes `f` with a mutable reference to each SSA value read (used) by this instruction.
    pub(crate) fn each_use_mut(&mut self, mut f: impl FnMut(&mut Val)) {
        match self {
            Inst::Const(..) | Inst::Upvalue(..) => {}
            Inst::Prim { args, .. } => args.iter_mut().for_each(f),
            Inst::Call { f: callee, args, .. } => iter::once(callee).chain(args).for_each(f),
            Inst::Closures { codes, .. } => {
                for c in codes.iter_mut().flat_map(|code| &mut code.captures) {
                    if let Captured::Val(v) = c {
                        f(v);
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

    /// Invokes `f` with a mutable reference to each SSA value read (used) by this terminator.
    pub(crate) fn each_use_mut(&mut self, mut f: impl FnMut(&mut Val)) {
        match self {
            End::Jump(_, args) | End::TailPrim { args, .. } => args.iter_mut().for_each(f),
            End::Branch { test, .. } | End::Return(test) => f(test),
            End::TailCall { f: callee, args } => iter::once(callee).chain(args).for_each(f),
        }
    }
}

/// Lowers the L4 AST from `root` in `tree` into an [`L5`](self) SSA program.
///
/// Each function is lowered independently by its own [`Builder`]. Closures are lowered in a stack-oriented,
/// bottom-up order, with nested closure functions emitted ahead of the functions enclosing them.
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

/// Validates that `program` is well-formed, panicking on verification failure in debug builds.
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

/// Collects all local variables mutated (via `set!`) within the frame rooted at `root` into `sets`.
fn sets_in<'id>(tree: &L4<'id, '_>, root: Id<'id>, sets: &mut HashSet<Var>) {
    sets.extend(tree.frame(root).filter_map(|id| if let Node::Set(v, _) = tree[id] { Some(v) } else { None }));
}

struct Building<'a, 'gc> {
    params: Vec<'a, Val>,
    insts: Vec<'a, Inst<'a, 'gc>>,
    sites: std::vec::Vec<u32>,
    end: Option<End<'a>>,
    end_site: u32,
}

/// The continuation context for an expression's result: either continuing sequentially within the
/// current basic block (`Ctx::Val`), or returning from the function (`Ctx::Tail`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Value,
    Tail,
}

/// Represents a join point within an active contification group: its target basic block (allocated
/// on the first incoming jump), the count of explicit jump arguments, and the group index tracking
/// mutated in-scope variables that must be passed along as extra arguments.
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
    /// The basic block currently being constructed.
    cur: Block,
    next: u32,
    env: HashMap<Var, Val>,
    /// Local variables bound to the result of an assignment statement; they evaluate to void and
    /// are materialized as SSA values only if subsequently read.
    voids: HashSet<Var>,
    /// The mutated local variables (`sets`) currently in scope, ordered from outermost to innermost.
    assigned: std::vec::Vec<Var>,
    /// The set of local variables that are mutated via `set!` anywhere within this function.
    sets: HashSet<Var>,
    joins: HashMap<Var, Join<'a>>,
    /// For each active join group, the list of in-scope mutated variables assigned within that group.
    groups: std::vec::Vec<std::vec::Vec<Var>>,
    this: Val,
    /// The stack of remaining lowering tasks to execute, processed in LIFO order (next task at the top).
    todo: std::vec::Vec<Task<'a, 'id>>,
    /// The source site of the expression being lowered, which the instructions built for it receive.
    site: u32,
    /// The SSA value produced by the most recently lowered expression, or `None` if control diverged
    /// (e.g. jumped or returned). This value is consumed by the subsequent task on the work stack.
    ret: Option<Val>,
}

/// A step in lowering a function: either initiating lowering of an expression or continuing execution
/// using the result left in [`Builder::ret`].
enum Task<'a, 'id> {
    Expr(Id<'id>, Ctx),
    /// Lowers the branches of an `if` expression after its condition test has been evaluated.
    Test { then: Id<'id>, other: Id<'id>, ctx: Ctx },
    /// Lowers the `else` branch (`other`) after the `then` branch has been lowered, restoring the
    /// mutated variable bindings to their state before the conditional.
    Then { other: Id<'id>, ctx: Ctx, b: Block, vars: std::vec::Vec<Var>, before: std::vec::Vec<Val> },
    /// Merges the control flow of both arms of an `if` expression, reconciling their return values
    /// and any updated local variable bindings.
    Else { x: Option<Val>, end_a: Block, env_a: std::vec::Vec<Val>, vars: std::vec::Vec<Var> },
    /// Lowers the trailing expression of a sequence (`Seq`) after evaluating the leading expression.
    Seq(Id<'id>, Ctx),
    Bind(Rest<'id>),
    /// Binds variable `v` to the newly produced value (or marks it void if bound to an assignment),
    /// then proceeds with lowering `next`.
    Bound { v: Var, void: bool, next: Rest<'id> },
    /// Pops a `let` expression's bindings and resets the mutated variable tracking to restore the enclosing scope.
    Unbind { binds: Span<'id, Bind<'id>>, assigned: usize },
    Assign(Var),
    /// Produces a void value to represent the result of an assignment expression.
    Void,
    Return,
    /// Finalizes the scope or the `code`th join definition in a join group, having preserved `n`
    /// mutated variables across the join boundary.
    Join { codes: Span<'id, JoinCode<'id>>, carried: std::vec::Vec<Var>, rest: Option<Block>, lowered: std::vec::Vec<bool>, ctx: Ctx, code: Option<(usize, usize)> },
    /// Evaluates function call arguments after the callee expression has been evaluated.
    Callee { args: Span<'id, Id<'id>>, tail: bool, site: u32 },
    /// Evaluates argument index `at` from `args` (following evaluation sequence `order`, if specified),
    /// accumulating results into `vals`.
    /// Evaluates the arguments of the operation `then`, which reports the source site `site`.
    Args { args: Span<'id, Id<'id>>, order: Option<Vec<'a, usize>>, at: usize, vals: Vec<'a, Val>, then: Use, site: u32 },
    /// Manages mutually recursive closures for `funs` bound to `dsts`, tracking compiled function
    /// codes and environment captures as each closure is lowered.
    Closures { funs: std::vec::Vec<Fun<'id>>, dsts: Vec<'a, Val>, codes: Vec<'a, Code<'a>>, captures: Option<Vec<'a, Captured>> },
}

/// Tracks the remaining bindings of a `let` expression starting at index `i`, followed by its body.
#[derive(Clone, Copy)]
struct Rest<'id> {
    binds: Span<'id, Bind<'id>>,
    i: usize,
    body: Id<'id>,
    ctx: Ctx,
}

/// Indicates the destination or calling convention for an evaluated argument list (e.g. primitive, call, or join jump).
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
        self.blocks.push(Building { params, insts: self.arena.vec(), sites: std::vec::Vec::new(), end: None, end_site: 0 });
        b
    }

    fn building(&mut self) -> &mut Building<'a, 'gc> {
        &mut self.blocks[self.cur.0 as usize]
    }

    fn push(&mut self, inst: Inst<'a, 'gc>) {
        let site = self.site;
        let block = self.building();
        block.insts.push(inst);
        block.sites.push(site);
    }

    fn def(&mut self, inst: impl FnOnce(Val) -> Inst<'a, 'gc>) -> Val {
        let dst = self.fresh();
        self.push(inst(dst));
        dst
    }

    fn end(&mut self, end: End<'a>) {
        let site = self.site;
        let block = self.building();
        debug_assert!(block.end.is_none(), "a block ends once");
        block.end = Some(end);
        block.end_site = site;
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

    /// Captures a snapshot of the current SSA values of the first `n` mutated local variables in `assigned`.
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
            blocks: vec![Building { params: arena.vec(), insts: arena.vec(), sites: std::vec::Vec::new(), end: None, end_site: 0 }],
            site: 0,
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
            sites: block.sites,
            end: block.end.expect("every block made ends"),
            end_site: block.end_site,
        });
        let (id, this, params, optional, rest, upvalues) = (self.id, self.this, self.params, self.optional, self.rest, self.upvalues);
        Function { id, this, params, optional, rest, upvalues, blocks: blocks.collect_in(self.arena), values: self.next }
    }

    /// Drives lowering until the function is complete, or until compilation pauses because the code
    /// for a nested closure is required (subsequently supplied via [`Builder::give`]).
    fn run(&mut self) -> Result<Option<(Fun<'id>, u32)>, CompileError> {
        let (arena, tree) = (self.arena, self.tree);
        while let Some(task) = self.todo.pop() {
            match task {
                Task::Expr(expr, ctx) => {
                    self.site = tree.site(expr);
                    self.start(expr, ctx)?
                }
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
                Task::Callee { args, tail, site } => {
                    let Some(f) = self.ret else { continue };
                    self.site = site;
                    self.args(args, None, if tail { Use::TailCall(f) } else { Use::Call(f) });
                }
                Task::Args { args, order, at, mut vals, then, site } => {
                    if at > 0 {
                        let Some(val) = self.ret else { continue };
                        match &order {
                            Some(order) => vals[order[at - 1]] = val,
                            None => vals.push(val),
                        }
                    }
                    let list = &tree[args];
                    if at == list.len() {
                        self.site = site;
                        self.finish_args(then, vals)?;
                        continue;
                    }
                    let next = order.as_ref().map_or(at, |order| order[at]);
                    self.todo.push(Task::Args { args, order, at: at + 1, vals, then, site });
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

    /// Supplies the lowered function index for the nested closure requested during the last invocation of [`Builder::run`].
    fn give(&mut self, function: u32) {
        let Some(Task::Closures { codes, captures, .. }) = self.todo.last_mut() else {
            unreachable!("a closure's code is lowered when its closures want it")
        };
        codes.push(Code { function, captures: captures.take().expect("captured before its code was lowered") });
    }

    /// Initiates lowering of `expr`. If `ctx` requests a value and control flows through, the resulting
    /// SSA value will be delivered to the subsequent task on the work stack.
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
                self.todo.push(Task::Callee { args, tail: ctx == Ctx::Tail, site: self.site });
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

    /// Lowers `expr` strictly for its side effects, discarding its value before continuing with the next task.
    fn effect(&mut self, expr: Id<'id>) {
        if let Node::Set(v, value) = self.tree[expr] {
            self.todo.push(Task::Assign(v));
            self.todo.push(Task::Expr(value, Ctx::Value));
        } else {
            self.todo.push(Task::Expr(expr, Ctx::Value));
        }
    }

    /// Lowers the binding at index `rest.i`, continuing past previously lowered bindings, or transitions
    /// to lowering the body once all bindings are processed.
    fn bind_next(&mut self, rest: Rest<'id>) {
        let tree = self.tree;
        let Some(&bind) = tree[rest.binds].get(rest.i) else {
            self.todo.push(Task::Expr(rest.body, rest.ctx));
            return;
        };
        let next = Rest { i: rest.i + 1, ..rest };
        match bind {
            Bind::Val(v, init) => match tree[init] {
                // Non-terminal statements in a sequence evaluate for side effects. For assignments
                // that mutate an unmonitored variable, record them as void without generating redundant bindings.
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

    /// Initiates lowering for arguments in `args`, following permutation `order` if provided, to feed into `then`.
    fn args(&mut self, args: Span<'id, Id<'id>>, order: Option<Vec<'a, usize>>, then: Use) {
        let n = self.tree[args].len();
        let vals = if order.is_some() { self.arena.vec_of(self.this, n) } else { Vec::with_capacity_in(n, self.arena) };
        self.todo.push(Task::Args { args, order, at: 0, vals, then, site: self.site });
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

    /// Emits a join block where both branches of an `if` converge: `end_a` is the exit block of the `then` branch
    /// (with result `x` and environment `env_a`), and the current block is the exit of the `else` branch.
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

    /// Lowers the enclosing `scope` followed by the bodies of all referenced join procedures in `codes`.
    /// When evaluated in value context, all branches jump to a shared exit block passing their result
    /// and mutated local variables.
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

    /// Continues processing a join group after compiling the scope or a join body: lowers the next
    /// reachable join routine or transitions to the join group's exit block.
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

    /// If the current block does not diverge, emits a jump passing `out` and `carried` variables to `rest`
    /// (allocating `rest` if not already created).
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

    /// Emits a jump to the join point identified by `id`, passing `vals` as block parameters along with any carried variables.
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

    /// Lowers a set of mutually recursive closures (`funs`) bound to `vars`, initializing closure allocations
    /// prior to capturing upvalues.
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

/// Determines a safe evaluation ordering for arguments passed in a jump to prevent an argument expression
/// from overwriting a parameter register while that register's previous value is still required by a subsequent argument.
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

/// Determines whether `expr` is pure and side-effect free, allowing its evaluation order to be reordered
/// relative to other pure expressions.
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

/// Determines whether `expr` references local variable `target` via read, mutation (`set!`), or closure capture.
pub(crate) fn reads_local<'id>(tree: &L4<'id, '_>, expr: Id<'id>, target: Var) -> bool {
    let captures = |fun: Fun<'id>| tree[tree[fun].captures].contains(&UpvalSource::Local(target));
    tree.frame(expr).any(|id| match tree[id] {
        Node::Ref(VarRef::Local(v)) | Node::Set(v, _) => v == target,
        Node::Lambda(fun) => captures(fun),
        Node::Let(binds, _) => tree[binds].iter().any(|&bind| matches!(bind, Bind::Fix(group) if tree[group].iter().any(|&(_, fun)| captures(fun)))),
        _ => false,
    })
}

/// The definition site of an SSA value: identifies its basic block, along with an offset (0 for block parameters,
/// or `instruction_index + 1` for instructions).
#[cfg(any(debug_assertions, test))]
#[derive(Clone, Copy)]
struct Def {
    block: usize,
    after: usize,
}

/// A mapping tracking the definition site of every SSA value allocated within a function.
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

    /// Verifies that value `v` dominates position `at` in block `b`, ensuring it is defined on all paths
    /// reaching this point using the immediate dominator tree `idom`.
    fn check(&self, idom: &[usize], v: Val, b: usize, at: usize) -> Result<(), String> {
        let def = self.at.get(&v).ok_or_else(|| format!("{v}, used in b{b}, isn't defined"))?;
        let ok = if def.block == b { def.after < at } else { dominates(idom, def.block, b) };
        if ok { Ok(()) } else { Err(format!("{v}, used in b{b}, isn't defined on every way there")) }
    }
}

#[cfg(any(debug_assertions, test))]
/// Verifies that every function in `program` is well-formed and that each function (except the top-level entry
/// at the end) is referenced by a closure in a subsequent function.
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

/// Verifies that function `f` is well-formed and that any closures it instantiates reference functions
/// located within the preceding slice `before`.
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
    // The register allocator processes blocks in topological/dominator order; every block must appear
    // after its immediate dominator (`idom[b] < b`).
    if let Some(b) = (1..n).find(|&b| idom[b] >= b) {
        return Err(format!("b{b} comes before b{}, which it's only reached through", idom[b]));
    }
    let check = |v: Val, b: usize, at: usize| defs.check(&idom, v, b, at);
    for (b, block) in f.blocks.iter().enumerate() {
        for (i, inst) in block.insts.iter().enumerate() {
            // Closures within a mutually recursive group may capture each other's allocated instances.
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

/// Computes the immediate dominator of each basic block using the iterative algorithm of Cooper, Harvey,
/// and Kennedy. Returns an error if any block is unreachable from the entry block.
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

/// Formats the program for display by printing the top-level function followed by each nested closure
/// function in hierarchical order.
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
    /// Formats the function as human-readable SSA text and appends references to its nested closure functions
    /// to `nested` for subsequent printing.
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
