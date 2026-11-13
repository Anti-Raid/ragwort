//! `L4`: closure-converted nodes whose children are referenced by [`Id`].
//!
//! Nodes do not own subtrees. Flat vectors own the data, so destruction does not recurse through
//! the tree. [`scope`] gives each table a fresh lifetime brand, preventing IDs from different
//! tables from being mixed. Only the table constructs IDs and spans; append-only storage keeps
//! those indices valid.

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
        /// A scope and its join definitions. [`Node::Jump`] can target these joins from the scope or from
        /// any join body in the group.
        Join(scope: Id<'id>, codes: Span<'id, JoinCode<'id>>),
        /// A jump to a join of an enclosing [`Node::Join`] with values for its parameters.
        Jump(join: Var, args: Span<'id, Id<'id>>),
        /// Assigns a local variable in the current frame and evaluates to void.
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

/// A [`Node::Let`] binding, visible to subsequent bindings and the body.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Bind<'id> {
    Val(Var, Id<'id>),
    /// A mutually recursive closure group, with every closure visible in every body.
    Fix(Span<'id, (Var, Fun<'id>)>),
}

impl<'id, 'gc> Children<'id, 'gc> for Bind<'id> {
    fn each(self, _: &L4<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        if let Bind::Val(_, init) = self {
            visit(init);
        }
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for Bind<'id> {
    fn bodies(self, tree: &L4<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        if let Bind::Fix(group) = self {
            tree[group].iter().for_each(|&(_, fun)| visit(tree[fun].body));
        }
    }
}

/// Join body `body`, with `params` bound to the values supplied by a jump to `id`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct JoinCode<'id> {
    pub(crate) id: Var,
    pub(crate) params: Span<'id, Var>,
    pub(crate) body: Id<'id>,
}

impl<'id, 'gc> Children<'id, 'gc> for JoinCode<'id> {
    fn each(self, _: &L4<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        visit(self.body);
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
    /// Returns the variables introduced by `bind`.
    pub(crate) fn vars(&self, bind: Bind<'id>) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match bind {
            Bind::Val(var, _) => (Some(var), &[][..]),
            Bind::Fix(group) => (None, &self[group]),
        };
        one.into_iter().chain(group.iter().map(|&(var, _)| var))
    }

    /// Panics if the tree rooted at `root` is malformed. Used by debug-build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(error) = self.verify(root) {
            panic!("malformed L4: {error}");
        }
    }

    /// Checks the tree and closure bodies reachable from `root`. Nodes and closures must have one
    /// parent; variables must be uniquely bound and used within scope. Jumps must target an in-scope
    /// join in the same function with matching arity. Upvalue and capture references must be valid for
    /// their functions. Unreachable nodes are ignored.
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
        /// The lexical bindings and joins in scope within a function.
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
                Task::Bind(var) => {
                    if !bound.insert(var) {
                        return Err(format!("{var:?} is bound twice"));
                    }
                    scope.locals.insert(var);
                }
                Task::Unbind(var) => _ = scope.locals.remove(&var),
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
                            UpvalSource::Local(var) => scope.locals.contains(&var),
                            UpvalSource::Upvalue(index) => index < scope.upvalues,
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
                    for &var in params.iter().chain(&clos.rest) {
                        if !bound.insert(var) {
                            return Err(format!("{var:?} is bound twice"));
                        }
                        inner.locals.insert(var);
                    }
                    scopes.push(inner);
                    todo.extend([Task::Leave, Task::Expr(clos.body)]);
                }
                Task::Expr(id) => {
                    if std::mem::replace(&mut owned[id.0 as usize], true) {
                        return Err(format!("{id:?} has two parents"));
                    }
                    let in_scope = match self[id] {
                        Node::Ref(VarRef::Local(var)) | Node::Set(var, _) => scope.locals.contains(&var),
                        Node::Ref(VarRef::Upvalue(index)) => index < scope.upvalues,
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
                                    Bind::Val(var, init) => then.extend([Task::Expr(init), Task::Bind(var)]),
                                    Bind::Fix(group) => {
                                        then.extend(self[group].iter().map(|&(var, _)| Task::Bind(var)));
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
                                then.extend(self[code.params].iter().map(|&var| Task::Bind(var)));
                                then.push(Task::Expr(code.body));
                                then.extend(self[code.params].iter().map(|&var| Task::Unbind(var)));
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
