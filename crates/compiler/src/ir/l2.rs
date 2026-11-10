//! `L2`, after `letrec` fixing, as a table of nodes like [`L3`](super::l3)'s, without joins: what
//! cp0 optimizes and assignment conversion lowers.

use ragwort_types::gc::Value;
use ragwort_vm::Purity;

use crate::{Prim, SlotOp, Var};

language! {
    table L2;
    node Node {
        Quote(value: Value<'gc>),
        Ref(var: Var),
        If(test: Id<'id>, then: Id<'id>, other: Id<'id>),
        Seq(first: Id<'id>, second: Id<'id>),
        Let(binds: Span<'id, Bind<'id>>, body: Id<'id>),
        /// An assignment of a variable, which evaluates to void.
        Set(var: Var, value: Id<'id>),
        App(callee: Id<'id>, args: Span<'id, Id<'id>>),
        Lambda(fun: Fun<'id>),
        Intrinsic(prim: Prim, args: Span<'id, Id<'id>>),
        ApplyIntrinsic(prim: Prim, args: Span<'id, Id<'id>>),
    }
    functions functions: Function<'id>, Fun, function, body body;
    lists { ids: Id<'id>, binds: Bind<'id>, groups: (Var, Fun<'id>), vars: Var }
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
    fn each(self, _: &L2<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Val(_, init) = self {
            f(init);
        }
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for Bind<'id> {
    fn bodies(self, tree: &L2<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
        if let Bind::Fix(group) = self {
            tree[group].iter().for_each(|&(_, fun)| f(tree[fun].body));
        }
    }
}

/// A lambda's function.
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

impl<'id, 'gc> L2<'id, 'gc> {
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

    /// Whether evaluating `id` cannot fault or cause side effects.
    pub(crate) fn is_pure(&self, id: Id<'id>) -> bool {
        let mut todo = vec![id];
        while let Some(id) = todo.pop() {
            let args = match self[id] {
                Node::Quote(_) | Node::Ref(_) | Node::Lambda(_) | Node::Intrinsic(Prim::Slot(SlotOp::Load, _), _) => continue,
                Node::Seq(a, b) => {
                    todo.extend([a, b]);
                    continue;
                }
                Node::If(a, b, c) => {
                    todo.extend([a, b, c]);
                    continue;
                }
                Node::Let(..) => {
                    self.children(id, |child| todo.push(child));
                    continue;
                }
                Node::Intrinsic(Prim::Intrinsic(i), args) if i.is_discardable() => args,
                Node::Intrinsic(Prim::Read(r), args) if r.is_discardable() => args,
                Node::Intrinsic(Prim::Host(h), args) if h.purity == Purity::Discardable => args,
                Node::Set(..) | Node::App(..) | Node::Intrinsic(..) | Node::ApplyIntrinsic(..) => return false,
            };
            todo.extend(&self[args]);
        }
        true
    }

    /// Whether any normal return value of `id` is guaranteed not to be `#f`.
    pub(crate) fn is_always_truthy(&self, id: Id<'id>) -> bool {
        let mut todo = vec![id];
        while let Some(id) = todo.pop() {
            let truthy = match self[id] {
                Node::Quote(v) => v != Value::FALSE,
                Node::Lambda(_) | Node::Set(..) => true,
                Node::Intrinsic(Prim::Intrinsic(i), _) => i.is_always_truthy(),
                Node::Intrinsic(Prim::Read(r), _) => r.is_always_truthy(),
                Node::Seq(_, b) | Node::Let(_, b) => {
                    todo.push(b);
                    true
                }
                Node::If(_, b, c) => {
                    todo.extend([b, c]);
                    true
                }
                Node::Ref(_) | Node::App(..) | Node::Intrinsic(..) | Node::ApplyIntrinsic(..) => false,
            };
            if !truthy {
                return false;
            }
        }
        true
    }

    /// Panics if the tree from `root` isn't well-formed, as a debug build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(e) = self.verify(root) {
            panic!("malformed L2: {e}");
        }
    }

    /// Whether the tree from `root`, and the code of each function in it, is well-formed: each
    /// node and function has one parent, and each variable is bound once and used only in its
    /// scope, which a function's body is in. Nodes nothing reaches aren't checked.
    #[cfg(any(debug_assertions, test))]
    pub(crate) fn verify(&self, root: Id<'id>) -> Result<(), String> {
        use crate::hash::HashSet;

        enum Task<'id> {
            Expr(Id<'id>),
            Function(Fun<'id>),
            Bind(Var),
            Unbind(Var),
        }
        let mut owned = vec![false; self.nodes.len()];
        let mut funs = vec![false; self.functions.len()];
        let mut bound = HashSet::default();
        let mut locals = HashSet::default();
        let mut todo = vec![Task::Expr(root)];
        let mut then = Vec::new();
        while let Some(task) = todo.pop() {
            match task {
                Task::Bind(v) => {
                    if !bound.insert(v) {
                        return Err(format!("{v:?} is bound twice"));
                    }
                    locals.insert(v);
                }
                Task::Unbind(v) => _ = locals.remove(&v),
                Task::Function(fun) => {
                    if std::mem::replace(&mut funs[fun.0 as usize], true) {
                        return Err(format!("{fun:?} has two parents"));
                    }
                    if self[fun].optional as usize > self[self[fun].params].len() {
                        return Err(format!("{fun:?} has more optional parameters than parameters"));
                    }
                    todo.extend(self.params(fun).map(Task::Unbind));
                    todo.push(Task::Expr(self[fun].body));
                    todo.extend(self.params(fun).map(Task::Bind));
                }
                Task::Expr(id) => {
                    if std::mem::replace(&mut owned[id.0 as usize], true) {
                        return Err(format!("{id:?} has two parents"));
                    }
                    if let Node::Ref(v) | Node::Set(v, _) = self[id]
                        && !locals.contains(&v)
                    {
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
