//! `L4`, after closure conversion, as a table of nodes that refer to their children by [`Id`].
//!
//! Nothing in a node owns anything: the table is a few flat vectors, which drop without
//! recursion however deep the tree in them. Each table is made by [`scope`] under a lifetime of
//! its own, which its ids carry, so an id of one table can't index another. Only the table makes
//! ids and spans, and it only grows, so they're always in bounds.

use ragwort_types::gc::Value;

use crate::ir::{UpvalSource, VarRef};
use crate::{Prim, Var};

#[cfg(test)]
#[path = "../tests/l4.rs"]
mod tests;

language! {
    table L4;
    node Node {
        Quote(value: Value<'gc>),
        Ref(var: VarRef),
        If(test: Id<'id>, then: Id<'id>, other: Id<'id>),
        Seq(first: Id<'id>, second: Id<'id>),
        Let(binds: Span<'id, Bind<'id>>, body: Id<'id>),
        /// Its scope, in which [`Node::Jump`]s to one of its codes go to it, as they do in the
        /// codes.
        Join(scope: Id<'id>, codes: Span<'id, JoinCode<'id>>),
        /// A jump to a join of an enclosing [`Node::Join`] with values for its parameters.
        Jump(join: Var, args: Span<'id, Id<'id>>),
        /// An assignment of a local of the frame, which evaluates to void.
        Set(var: Var, value: Id<'id>),
        App(callee: Id<'id>, args: Span<'id, Id<'id>>),
        Lambda(fun: Fun<'id>),
        Intrinsic(prim: Prim, args: Span<'id, Id<'id>>),
        ApplyIntrinsic(prim: Prim, args: Span<'id, Id<'id>>),
    }
    functions closures: Closure<'id>, Fun, closure, body body;
    lists { ids: Id<'id>, binds: Bind<'id>, joins: JoinCode<'id>, groups: (Var, Fun<'id>), vars: Var, captures: UpvalSource }
    leaves { Value<'gc>, VarRef, Var, Prim }
}

/// One of a [`Node::Let`]'s bindings, in scope for those after it and its body.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Bind<'id> {
    Val(Var, Id<'id>),
    /// Closures, in scope in each other's code too.
    Fix(Span<'id, (Var, Fun<'id>)>),
}

impl<'id, 'gc> Children<'id, 'gc> for Bind<'id> {
    fn each(self, _: &L4<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Val(_, init) = self {
            f(init);
        }
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for Bind<'id> {
    fn bodies(self, tree: &L4<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Fix(group) = self {
            tree[group].iter().for_each(|&(_, fun)| f(tree[fun].body));
        }
    }
}

/// A join's code: `body`, with `params` bound to the values a jump to `id` has.
#[derive(Clone, Copy, Debug)]
pub(crate) struct JoinCode<'id> {
    pub(crate) id: Var,
    pub(crate) params: Span<'id, Var>,
    pub(crate) body: Id<'id>,
}

impl<'id, 'gc> Children<'id, 'gc> for JoinCode<'id> {
    fn each(self, _: &L4<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        f(self.body);
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for JoinCode<'id> {
    fn bodies(self, _: &L4<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
}

/// A closure with an explicit capture list and no implicit free variables.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Closure<'id> {
    pub(crate) id: u32,
    pub(crate) optional: u32,
    pub(crate) params: Span<'id, Var>,
    pub(crate) rest: Option<Var>,
    pub(crate) captures: Span<'id, UpvalSource>,
    pub(crate) body: Id<'id>,
}

impl<'id, 'gc> L4<'id, 'gc> {
    /// The variables `bind` binds.
    pub(crate) fn vars(&self, bind: Bind<'id>) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match bind {
            Bind::Val(v, _) => (Some(v), &[][..]),
            Bind::Fix(group) => (None, &self[group]),
        };
        one.into_iter().chain(group.iter().map(|&(v, _)| v))
    }

    /// Panics if the tree from `root` isn't well-formed, as a debug build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(e) = self.verify(root) {
            panic!("malformed L4: {e}");
        }
    }

    /// Whether the tree from `root`, and the code of each closure in it, is well-formed: each node
    /// and closure has one parent, each variable is bound once and used only in scope, each jump
    /// is to a join in scope in its function with as many values as the join takes, and each
    /// upvalue and capture is one the function has. Nodes nothing reaches aren't checked.
    #[cfg(any(debug_assertions, test))]
    pub(crate) fn verify(&self, root: Id<'id>) -> Result<(), String> {
        use crate::hash::{HashMap, HashSet};

        enum Task<'id> {
            Expr(Id<'id>),
            Closure(Fun<'id>),
            Bind(Var),
            Unbind(Var),
            Joins(Span<'id, JoinCode<'id>>),
            Unjoin(Span<'id, JoinCode<'id>>),
            Leave,
        }
        /// What's in scope in a function.
        #[derive(Default)]
        struct Scope {
            locals: HashSet<Var>,
            joins: HashMap<Var, usize>,
            upvalues: u32,
            closure: bool,
        }
        let mut owned = vec![false; self.nodes.len()];
        let mut funs = vec![false; self.closures.len()];
        let mut bound = HashSet::default();
        let mut scopes = vec![Scope::default()];
        let mut todo = vec![Task::Expr(root)];
        let mut then = Vec::new();
        while let Some(task) = todo.pop() {
            let scope = scopes.last_mut().expect("the code's scope is never left");
            match task {
                Task::Bind(v) => {
                    if !bound.insert(v) {
                        return Err(format!("{v:?} is bound twice"));
                    }
                    scope.locals.insert(v);
                }
                Task::Unbind(v) => _ = scope.locals.remove(&v),
                Task::Joins(codes) => {
                    for code in &self[codes] {
                        if scope.joins.insert(code.id, self[code.params].len()).is_some() {
                            return Err(format!("join {:?} is in scope twice", code.id));
                        }
                    }
                }
                Task::Unjoin(codes) => self[codes].iter().for_each(|code| _ = scope.joins.remove(&code.id)),
                Task::Leave => _ = scopes.pop(),
                Task::Closure(fun) => {
                    if std::mem::replace(&mut funs[fun.0 as usize], true) {
                        return Err(format!("{fun:?} has two parents"));
                    }
                    let clos = self[fun];
                    for &src in &self[clos.captures] {
                        let ok = match src {
                            UpvalSource::Local(v) => scope.locals.contains(&v),
                            UpvalSource::Upvalue(u) => u < scope.upvalues,
                            UpvalSource::SelfClosure => scope.closure,
                        };
                        if !ok {
                            return Err(format!("{fun:?} captures {src:?}, which isn't in scope"));
                        }
                    }
                    let params = &self[clos.params];
                    if clos.optional as usize > params.len() {
                        return Err(format!("{fun:?} has more optional parameters than parameters"));
                    }
                    let mut inner = Scope { upvalues: count(self[clos.captures].len()), closure: true, ..Scope::default() };
                    for &v in params.iter().chain(&clos.rest) {
                        if !bound.insert(v) {
                            return Err(format!("{v:?} is bound twice"));
                        }
                        inner.locals.insert(v);
                    }
                    scopes.push(inner);
                    todo.extend([Task::Leave, Task::Expr(clos.body)]);
                }
                Task::Expr(id) => {
                    if std::mem::replace(&mut owned[id.0 as usize], true) {
                        return Err(format!("{id:?} has two parents"));
                    }
                    let in_scope = match self[id] {
                        Node::Ref(VarRef::Local(v)) | Node::Set(v, _) => scope.locals.contains(&v),
                        Node::Ref(VarRef::Upvalue(u)) => u < scope.upvalues,
                        Node::Ref(VarRef::SelfClosure) => scope.closure,
                        Node::Jump(join, args) => scope.joins.get(&join) == Some(&self[args].len()),
                        _ => true,
                    };
                    if !in_scope {
                        return Err(format!("{id:?}, {:?}, refers to what isn't in scope", self[id]));
                    }
                    match self[id] {
                        Node::Let(binds, body) => {
                            for &bind in &self[binds] {
                                match bind {
                                    Bind::Val(v, init) => then.extend([Task::Expr(init), Task::Bind(v)]),
                                    Bind::Fix(group) => {
                                        then.extend(self[group].iter().map(|&(v, _)| Task::Bind(v)));
                                        then.extend(self[group].iter().map(|&(_, fun)| Task::Closure(fun)));
                                    }
                                }
                            }
                            then.push(Task::Expr(body));
                            for &bind in &self[binds] {
                                then.extend(self.vars(bind).map(Task::Unbind));
                            }
                        }
                        Node::Join(body, codes) => {
                            then.extend([Task::Joins(codes), Task::Expr(body)]);
                            for code in &self[codes] {
                                then.extend(self[code.params].iter().map(|&v| Task::Bind(v)));
                                then.push(Task::Expr(code.body));
                                then.extend(self[code.params].iter().map(|&v| Task::Unbind(v)));
                            }
                            then.push(Task::Unjoin(codes));
                        }
                        Node::Lambda(fun) => then.push(Task::Closure(fun)),
                        _ => self.children(id, |child| then.push(Task::Expr(child))),
                    }
                    todo.extend(then.drain(..).rev());
                }
            }
        }
        Ok(())
    }
}
