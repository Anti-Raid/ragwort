//! Pass 6 (`L3 -> L4`): Closure conversion (runs after [`contify`](crate::contify)).
//!
//! - Converts contification join points (including loops among them) into `Join` nodes,
//!   and turns calls to them into intra-frame `Jump` nodes without allocating closures or stack frames.
//! - Resolves self-references inside single-binding recursive closures to [`VarRef::SelfClosure`]
//!   (register `0`, `frame::CLOSURE`), avoiding self-captured upvalues.
//! - Computes free variables bottom-up, classifies variable references into [`VarRef::Local`],
//!   [`VarRef::Upvalue`], and [`VarRef::SelfClosure`], and attaches an explicit [`UpvalSource`]
//!   capture table to each closure.
//!
//! The pass is implemented iteratively using an explicit task stack and a value stack for converted
//! nodes, preventing call-stack overflow regardless of AST depth. Variable references are resolved in
//! preorder traversal order (processing join bodies before join scopes), which consistently assigns
//! upvalue indices for each closure.

use crate::hash::HashSet;

use crate::ir::l3::{self, L3};
use crate::ir::l4::{self, Fun, Id, JoinCode, L4, Node};
use crate::ir::{UpvalSource, VarRef};
use crate::{Prim, Var};

/// Lowers the L3 expression rooted at `root` in `from` into closure-converted L4 form in `tree`,
/// returning the new root expression ID.
pub(crate) fn closure_convert<'s, 'id, 'gc>(tree: &mut L4<'id, 'gc>, from: &L3<'s, 'gc>, root: l3::Id<'s>) -> Id<'id> {
    let mut pass = Convert { from, tree, envs: vec![Env::new(HashSet::default(), None)], vals: Vec::new(), funs: Vec::new(), binds: Vec::new(), codes: Vec::new() };
    let mut todo = vec![Task::Expr(root)];
    while let Some(task) = todo.pop() {
        pass.run(task, &mut todo);
    }
    debug_assert!(pass.envs[0].upvalues.is_empty(), "top-level expression has no free variables");
    pass.vals.pop().expect("the root's converted")
}

/// A deferred task in the iterative closure-conversion worklist: either an L3 expression to visit,
/// or an action to assemble previously converted child expressions into an L4 node.
enum Task<'s> {
    Expr(l3::Id<'s>),
    /// Sets the source site that the nodes built by the following task receive.
    At(u32),
    If,
    Seq,
    Set(Var),
    App(usize),
    Jump(Var, usize),
    Intrinsic(Prim, usize),
    ApplyIntrinsic(Prim, usize),
    Lambda,
    /// Enters a function body, pushing a new lexical environment for its parameters;
    /// `self_closure` specifies the variable that refers to the closure itself for recursive calls.
    Enter(l3::Fun<'s>, Option<Var>),
    Leave(l3::Fun<'s>),
    Val(Var),
    /// Brings a group of mutually recursive functions into scope before converting their bodies.
    Group(l3::Span<'s, (Var, l3::Fun<'s>)>),
    /// Binds a single recursive function to `Var` and brings it into scope after converting its body.
    One(Var),
    Fix(l3::Span<'s, (Var, l3::Fun<'s>)>),
    Let(l3::Span<'s, l3::Bind<'s>>),
    Code(l3::JoinCode<'s>),
    Coded(l3::JoinCode<'s>),
    Join(usize),
}

/// Lexical scope tracking local variables, captured upvalues, and optional self-closure references
/// for a function during conversion.
struct Env {
    locals: HashSet<Var>,
    upvalues: Vec<Var>,
    self_closure: Option<Var>,
}

impl Env {
    fn new(locals: HashSet<Var>, self_closure: Option<Var>) -> Env {
        Env { locals, upvalues: Vec::new(), self_closure }
    }

    fn resolve(&mut self, var: Var) -> VarRef {
        if self.locals.contains(&var) {
            return VarRef::Local(var);
        }
        if self.self_closure == Some(var) {
            return VarRef::SelfClosure;
        }
        if let Some(idx) = self.upvalues.iter().position(|&upvalue| upvalue == var) {
            return VarRef::Upvalue(idx as u32);
        }
        let idx = self.upvalues.len() as u32;
        self.upvalues.push(var);
        VarRef::Upvalue(idx)
    }
}

/// State of the closure-conversion pass, maintaining references to the input L3 AST, output L4
/// AST, lexical environment stack, and intermediate converted sub-expressions.
struct Convert<'r, 's, 'id, 'gc> {
    from: &'r L3<'s, 'gc>,
    tree: &'r mut L4<'id, 'gc>,
    envs: Vec<Env>,
    vals: Vec<Id<'id>>,
    funs: Vec<Fun<'id>>,
    binds: Vec<l4::Bind<'id>>,
    codes: Vec<JoinCode<'id>>,
}

impl<'s, 'id, 'gc> Convert<'_, 's, 'id, 'gc> {
    fn env(&mut self) -> &mut Env {
        self.envs.last_mut().expect("the root's function is never left")
    }

    fn pop(&mut self) -> Id<'id> {
        self.vals.pop().expect("a converted node")
    }

    /// Drains the last `count` converted node IDs from `self.vals` and stores them as an L4 span.
    fn last(&mut self, count: usize) -> l4::Span<'id, Id<'id>> {
        let at = self.vals.len() - count;
        self.tree.list(self.vals.drain(at..))
    }

    fn make(&mut self, node: Node<'id, 'gc>) {
        let id = self.tree.add(node);
        self.vals.push(id);
    }

    fn run(&mut self, task: Task<'s>, todo: &mut Vec<Task<'s>>) {
        let from = self.from;
        match task {
            Task::Expr(id) => self.expr(id, todo),
            Task::At(site) => self.tree.at(site),
            Task::If => {
                let (other, then, test) = (self.pop(), self.pop(), self.pop());
                self.make(Node::If(test, then, other));
            }
            Task::Seq => {
                let (second, first) = (self.pop(), self.pop());
                self.make(Node::Seq(first, second));
            }
            Task::Set(var) => {
                let value = self.pop();
                self.make(Node::Set(var, value));
            }
            Task::App(count) => {
                let args = self.last(count);
                let function = self.pop();
                self.make(Node::App(function, args));
            }
            Task::Jump(join, count) => {
                let args = self.last(count);
                self.make(Node::Jump(join, args));
            }
            Task::Intrinsic(prim, count) => {
                let args = self.last(count);
                self.make(Node::Intrinsic(prim, args));
            }
            Task::ApplyIntrinsic(prim, count) => {
                let args = self.last(count);
                self.make(Node::ApplyIntrinsic(prim, args));
            }
            Task::Lambda => {
                let fun = self.funs.pop().expect("a converted closure");
                self.make(Node::Lambda(fun));
            }
            Task::Enter(fun, self_closure) => self.envs.push(Env::new(from.params(fun).collect(), self_closure)),
            Task::Leave(fun) => {
                let env = self.envs.pop().expect("a function's own");
                let body = self.pop();
                let parent = self.env();
                let captures: Vec<UpvalSource> = env
                    .upvalues
                    .into_iter()
                    .map(|var| match parent.resolve(var) {
                        VarRef::Local(local) => UpvalSource::Local(local),
                        VarRef::Upvalue(idx) => UpvalSource::Upvalue(idx),
                        VarRef::SelfClosure => UpvalSource::SelfClosure,
                    })
                    .collect();
                let closure = from[fun];
                let (captures, params) = (self.tree.list(captures), self.tree.list(from[closure.params].iter().copied()));
                let fun = self.tree.closure(l4::Closure { id: closure.id, optional: closure.optional, params, rest: closure.rest, captures, body });
                self.funs.push(fun);
            }
            Task::Val(var) => {
                let init = self.pop();
                self.env().locals.insert(var);
                self.binds.push(l4::Bind::Val(var, init));
            }
            Task::Group(group) => self.env().locals.extend(from[group].iter().map(|&(var, _)| var)),
            Task::One(var) => {
                self.env().locals.insert(var);
                let fun = self.funs.pop().expect("a converted closure");
                let group = self.tree.list([(var, fun)]);
                self.binds.push(l4::Bind::Fix(group));
            }
            Task::Fix(group) => {
                let at = self.funs.len() - from[group].len();
                let funs = from[group].iter().map(|&(var, _)| var).zip(self.funs.drain(at..));
                let group = self.tree.list(funs);
                self.binds.push(l4::Bind::Fix(group));
            }
            Task::Let(binds) => {
                let body = self.pop();
                let env = self.envs.last_mut().expect("the root's function is never left");
                for &bind in &from[binds] {
                    for var in from.vars(bind) {
                        env.locals.remove(&var);
                    }
                }
                let at = self.binds.len() - from[binds].len();
                let binds = self.tree.list(self.binds.drain(at..));
                self.make(Node::Let(binds, body));
            }
            Task::Code(code) => self.env().locals.extend(from.params(code.fun)),
            Task::Coded(code) => {
                let body = self.pop();
                let env = self.envs.last_mut().expect("the root's function is never left");
                for param in from.params(code.fun) {
                    env.locals.remove(&param);
                }
                let params = self.tree.list(from[from[code.fun].params].iter().copied());
                self.codes.push(JoinCode { id: code.id, params, body });
            }
            Task::Join(count) => {
                let scope = self.pop();
                let at = self.codes.len() - count;
                let codes = self.tree.list(self.codes.drain(at..));
                self.make(Node::Join(scope, codes));
            }
        }
    }

    /// Directly converts leaf expressions or pushes child expression tasks onto the worklist
    /// in reverse order to ensure left-to-right evaluation.
    fn expr(&mut self, id: l3::Id<'s>, todo: &mut Vec<Task<'s>>) {
        let from = self.from;
        let at = todo.len();
        let all = |args: l3::Span<'s, l3::Id<'s>>, todo: &mut Vec<Task<'s>>| todo.extend(from[args].iter().map(|&arg| Task::Expr(arg)));
        let site = from.site(id);
        self.tree.at(site);
        match from[id] {
            l3::Node::Quote(value) => self.make(Node::Quote(value)),
            l3::Node::Ref(variable) => {
                let var = self.env().resolve(variable);
                self.make(Node::Ref(var));
            }
            l3::Node::If(test, then, other) => todo.extend([Task::Expr(test), Task::Expr(then), Task::Expr(other), Task::If]),
            l3::Node::Seq(first, second) => todo.extend([Task::Expr(first), Task::Expr(second), Task::Seq]),
            l3::Node::Set(var, value) => {
                let VarRef::Local(var) = self.env().resolve(var) else {
                    unreachable!("assignment conversion boxes what closures assign")
                };
                todo.extend([Task::Expr(value), Task::Set(var)]);
            }
            l3::Node::App(function, args) => {
                todo.push(Task::Expr(function));
                all(args, todo);
                todo.extend([Task::At(site), Task::App(from[args].len())]);
            }
            l3::Node::Jump(join, args) => {
                all(args, todo);
                todo.extend([Task::At(site), Task::Jump(join, from[args].len())]);
            }
            l3::Node::Intrinsic(prim, args) => {
                all(args, todo);
                todo.extend([Task::At(site), Task::Intrinsic(prim, from[args].len())]);
            }
            l3::Node::ApplyIntrinsic(prim, args) => {
                all(args, todo);
                todo.extend([Task::At(site), Task::ApplyIntrinsic(prim, from[args].len())]);
            }
            l3::Node::Lambda(fun) => todo.extend([Task::Enter(fun, None), Task::Expr(from[fun].body), Task::Leave(fun), Task::Lambda]),
            l3::Node::Let(binds, body) => {
                for &bind in &from[binds] {
                    match bind {
                        l3::Bind::Val(var, init) => todo.extend([Task::Expr(init), Task::Val(var)]),
                        l3::Bind::Fix(group) => match from[group] {
                            [(var, fun)] => todo.extend([Task::Enter(fun, Some(var)), Task::Expr(from[fun].body), Task::Leave(fun), Task::One(var)]),
                            _ => {
                                todo.push(Task::Group(group));
                                for &(_, fun) in &from[group] {
                                    todo.extend([Task::Enter(fun, None), Task::Expr(from[fun].body), Task::Leave(fun)]);
                                }
                                todo.push(Task::Fix(group));
                            }
                        },
                    }
                }
                todo.extend([Task::Expr(body), Task::Let(binds)]);
            }
            l3::Node::Join(scope, codes) => {
                for &code in &from[codes] {
                    todo.extend([Task::Code(code), Task::Expr(from[code.fun].body), Task::Coded(code)]);
                }
                todo.extend([Task::Expr(scope), Task::Join(from[codes].len())]);
            }
        }
        todo[at..].reverse();
    }
}
