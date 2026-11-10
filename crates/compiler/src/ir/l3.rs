//! `L3`, between assignment conversion and closure conversion, as a table of nodes like
//! [`L4`](super::l4)'s: variables are still lexical, and functions are records the table keeps,
//! which a [`Node::Lambda`] or [`Bind::Fix`] refers to as another frame, and a [`JoinCode`] as
//! code of its own frame.

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
        /// Its scope, in which [`Node::Jump`]s to one of its codes go to it, as they do in the
        /// codes.
        Join(scope: Id<'id>, codes: Span<'id, JoinCode<'id>>),
        /// A jump to a join of an enclosing [`Node::Join`] with values for its parameters.
        Jump(join: Var, args: Span<'id, Id<'id>>),
        /// An assignment of a variable, which evaluates to void.
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

/// One of a [`Node::Let`]'s bindings, in scope for those after it and its body.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Bind<'id> {
    Val(Var, Id<'id>),
    /// Functions, in scope in each other's code too.
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

/// A join's code: its function's body, in the frame, with its parameters bound to the values a
/// jump to `id` has.
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

/// A function: a lambda's, or a join's code.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Function<'id> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub(crate) id: u32,
    /// How many of the last of `params` a call can leave out.
    pub(crate) optional: u32,
    pub(crate) params: Span<'id, Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub(crate) rest: Option<Var>,
    pub(crate) body: Id<'id>,
}

impl<'id, 'gc> L3<'id, 'gc> {
    /// The variables `bind` binds.
    pub(crate) fn vars(&self, bind: Bind<'id>) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match bind {
            Bind::Val(v, _) => (Some(v), &[][..]),
            Bind::Fix(group) => (None, &self[group]),
        };
        one.into_iter().chain(group.iter().map(|&(v, _)| v))
    }

    /// The variables `fun` binds as it's called: its parameters, and its rest one.
    pub(crate) fn params(&self, fun: Fun<'id>) -> impl Iterator<Item = Var> + '_ {
        self[self[fun].params].iter().copied().chain(self[fun].rest)
    }

    /// Panics if the tree from `root` isn't well-formed, as a debug build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(e) = self.verify(root) {
            panic!("malformed L3: {e}");
        }
    }

    /// Whether the tree from `root`, and the code of each function in it, is well-formed: each
    /// node and function has one parent, each variable is bound once and used only in its scope,
    /// which a function's body is in, and each jump is to a join in scope in its frame with as
    /// many values as the join takes, which takes no optional or rest ones. Nodes nothing reaches
    /// aren't checked.
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
        // The joins in scope in each frame, by how many values they take.
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
