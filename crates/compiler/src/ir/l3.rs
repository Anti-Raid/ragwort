//! `L3`: the node-table IR used by assignment conversion and contification before closure
//! conversion. References remain lexical. [`Node::Lambda`] and [`Bind::Fix`] refer to function
//! records that execute in separate frames; [`JoinCode`] refers to code executed in the current
//! frame.

use ragwort_types::gc::Value;

use crate::{Prim, Var};

#[cfg(test)]
#[path = "../tests/l3.rs"]
mod tests;

language! {
    table L3;
    node Node {
        Quote(value: Value<'gc>),
        Ref(var: Var),
        If(test: Id<'id>, then: Id<'id>, other: Id<'id>),
        Seq(first: Id<'id>, second: Id<'id>),
        Let(binds: Span<'id, Bind<'id>>, body: Id<'id>),
        /// A scope and its join definitions. [`Node::Jump`] can target these joins from the scope or from
        /// any join body in the group.
        Join(scope: Id<'id>, codes: Span<'id, JoinCode<'id>>),
        /// A jump to a join of an enclosing [`Node::Join`] with values for its parameters.
        Jump(join: Var, args: Span<'id, Id<'id>>),
        /// Assigns a variable and evaluates to void.
        Set(var: Var, value: Id<'id>),
        App(callee: Id<'id>, args: Span<'id, Id<'id>>),
        Lambda(fun: Fun<'id>),
        Intrinsic(prim: Prim, args: Span<'id, Id<'id>>),
        ApplyIntrinsic(prim: Prim, args: Span<'id, Id<'id>>),
    }
    functions functions: Function<'id>, Fun, function, body body;
    lists { ids: Id<'id>, binds: Bind<'id>, joins: JoinCode<'id>, groups: (Var, Fun<'id>), vars: Var }
    leaves { Value<'gc>, Var, Prim }
}

/// A [`Node::Let`] binding, visible to subsequent bindings and the body.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Bind<'id> {
    Val(Var, Id<'id>),
    /// A mutually recursive function group, with every function visible in every body.
    Fix(Span<'id, (Var, Fun<'id>)>),
}

impl<'id, 'gc> Children<'id, 'gc> for Bind<'id> {
    fn each(self, _: &L3<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Val(_, init) = self {
            f(init);
        }
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for Bind<'id> {
    fn bodies(self, tree: &L3<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Fix(group) = self {
            tree[group].iter().for_each(|&(_, fun)| f(tree[fun].body));
        }
    }
}

/// Join code executed in the current frame. A jump to `id` supplies values for the function's
/// parameters.
#[derive(Clone, Copy, Debug)]
pub(crate) struct JoinCode<'id> {
    pub(crate) id: Var,
    pub(crate) fun: Fun<'id>,
}

impl<'id, 'gc> Children<'id, 'gc> for JoinCode<'id> {
    fn each(self, tree: &L3<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        f(tree[self.fun].body);
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for JoinCode<'id> {
    fn bodies(self, _: &L3<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
}

/// A function record used by either a lambda or a join.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Function<'id> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub(crate) id: u32,
    /// Number of trailing entries in `params` that a call may omit.
    pub(crate) optional: u32,
    pub(crate) params: Span<'id, Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub(crate) rest: Option<Var>,
    pub(crate) body: Id<'id>,
}

impl<'id, 'gc> L3<'id, 'gc> {
    /// Returns the variables introduced by `bind`.
    pub(crate) fn vars(&self, bind: Bind<'id>) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match bind {
            Bind::Val(v, _) => (Some(v), &[][..]),
            Bind::Fix(group) => (None, &self[group]),
        };
        one.into_iter().chain(group.iter().map(|&(v, _)| v))
    }

    /// Returns `fun`'s positional parameters and optional rest parameter.
    pub(crate) fn params(&self, fun: Fun<'id>) -> impl Iterator<Item = Var> + '_ {
        self[self[fun].params].iter().copied().chain(self[fun].rest)
    }

    /// Panics if the tree rooted at `root` is malformed. Used by debug-build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(e) = self.verify(root) {
            panic!("malformed L3: {e}");
        }
    }

    /// Checks the tree and function bodies reachable from `root`. Nodes and functions must have one
    /// parent; variables must be uniquely bound and used within scope. Jumps must target an in-scope
    /// join in the same frame with matching arity. Joins cannot have optional or rest parameters.
    /// Unreachable nodes are ignored.
    #[cfg(any(debug_assertions, test))]
    pub(crate) fn verify(&self, root: Id<'id>) -> Result<(), String> {
        use crate::hash::{HashMap, HashSet};

        enum Task<'id> {
            Expr(Id<'id>),
            Function(Fun<'id>),
            Bind(Var),
            Unbind(Var),
            Joins(Span<'id, JoinCode<'id>>),
            Unjoin(Span<'id, JoinCode<'id>>),
            Leave,
        }
        let mut owned = vec![false; self.nodes.len()];
        let mut funs = vec![false; self.functions.len()];
        let mut bound = HashSet::default();
        let mut locals = HashSet::default();
        // Maps each frame's in-scope joins to their arities.
        let mut frames: Vec<HashMap<Var, usize>> = vec![HashMap::default()];
        let mut todo = vec![Task::Expr(root)];
        let mut then = Vec::new();
        let mut own = |fun: Fun<'id>| {
            if std::mem::replace(&mut funs[fun.0 as usize], true) {
                return Err(format!("{fun:?} has two parents"));
            }
            if self[fun].optional as usize > self[self[fun].params].len() {
                return Err(format!("{fun:?} has more optional parameters than parameters"));
            }
            Ok(())
        };
        while let Some(task) = todo.pop() {
            let joins = frames.last_mut().expect("the code's frame is never left");
            match task {
                Task::Bind(v) => {
                    if !bound.insert(v) {
                        return Err(format!("{v:?} is bound twice"));
                    }
                    locals.insert(v);
                }
                Task::Unbind(v) => _ = locals.remove(&v),
                Task::Joins(codes) => {
                    for code in &self[codes] {
                        own(code.fun)?;
                        let fun = self[code.fun];
                        if fun.optional != 0 || fun.rest.is_some() {
                            return Err(format!("join {:?} takes optional or rest values", code.id));
                        }
                        if joins.insert(code.id, self[fun.params].len()).is_some() {
                            return Err(format!("join {:?} is in scope twice", code.id));
                        }
                    }
                }
                Task::Unjoin(codes) => self[codes].iter().for_each(|code| _ = joins.remove(&code.id)),
                Task::Leave => _ = frames.pop(),
                Task::Function(fun) => {
                    own(fun)?;
                    frames.push(HashMap::default());
                    todo.push(Task::Leave);
                    todo.extend(self.params(fun).map(Task::Unbind));
                    todo.push(Task::Expr(self[fun].body));
                    todo.extend(self.params(fun).map(Task::Bind));
                }
                Task::Expr(id) => {
                    if std::mem::replace(&mut owned[id.0 as usize], true) {
                        return Err(format!("{id:?} has two parents"));
                    }
                    let in_scope = match self[id] {
                        Node::Ref(v) | Node::Set(v, _) => locals.contains(&v),
                        Node::Jump(join, args) => joins.get(&join) == Some(&self[args].len()),
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
                                        then.extend(self[group].iter().map(|&(_, fun)| Task::Function(fun)));
                                    }
                                }
                            }
                            then.push(Task::Expr(body));
                            for &bind in &self[binds] {
                                then.extend(self.vars(bind).map(Task::Unbind));
                            }
                        }
                        Node::Join(scope, codes) => {
                            then.extend([Task::Joins(codes), Task::Expr(scope)]);
                            for code in &self[codes] {
                                then.extend(self.params(code.fun).map(Task::Bind));
                                then.push(Task::Expr(self[code.fun].body));
                                then.extend(self.params(code.fun).map(Task::Unbind));
                            }
                            then.push(Task::Unjoin(codes));
                        }
                        Node::Lambda(fun) => then.push(Task::Function(fun)),
                        _ => self.children(id, |child| then.push(Task::Expr(child))),
                    }
                    todo.extend(then.drain(..).rev());
                }
            }
        }
        Ok(())
    }
}
