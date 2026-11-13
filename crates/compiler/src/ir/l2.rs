//! `L2`: the node-table IR produced by `letrec` fixing and optimized by cp0. Similar to
//! [`L3`](super::l3), but without joins; assignment lowering converts it to L3.

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Intrinsic, Purity};

use crate::{Prim, SlotOp, Var};

language! {
    table L2;
    node Node {
        Quote(value: Value<'gc>),
        Ref(var: Var),
        If(test: Id<'id>, then: Id<'id>, other: Id<'id>),
        Seq(first: Id<'id>, second: Id<'id>),
        Let(binds: Span<'id, Bind<'id>>, body: Id<'id>),
        /// Assigns a variable and evaluates to void.
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

/// A [`Node::Let`] binding, visible to subsequent bindings and the body.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Bind<'id> {
    Val(Var, Id<'id>),
    /// A mutually recursive function group, with every function visible in every body.
    Fix(Span<'id, (Var, Fun<'id>)>),
}

impl<'id, 'gc> Children<'id, 'gc> for Bind<'id> {
    fn each(self, _: &L2<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        if let Bind::Val(_, init) = self {
            visit(init);
        }
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for Bind<'id> {
    fn bodies(self, tree: &L2<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        if let Bind::Fix(group) = self {
            tree[group].iter().for_each(|&(_, fun)| visit(tree[fun].body));
        }
    }
}

/// A lambda's function record.
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

impl<'id, 'gc> L2<'id, 'gc> {
    /// Returns the variables introduced by `bind`.
    pub(crate) fn vars(&self, bind: Bind<'id>) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match bind {
            Bind::Val(var, _) => (Some(var), &[][..]),
            Bind::Fix(group) => (None, &self[group]),
        };
        one.into_iter().chain(group.iter().map(|&(var, _)| var))
    }

    /// Returns `fun`'s positional parameters and optional rest parameter.
    pub(crate) fn params(&self, fun: Fun<'id>) -> impl Iterator<Item = Var> + '_ {
        self[self[fun].params].iter().copied().chain(self[fun].rest)
    }

    /// Recognizes `(make-struct 'type v ...)` with a constant struct type and the correct field count.
    /// Returns the type and arguments, including the type argument, when the call cannot fault.
    pub(crate) fn made_struct(&self, mc: &Mutation<'gc>, id: Id<'id>) -> Option<(Gc<'gc, StructType>, Span<'id, Id<'id>>)> {
        let Node::Intrinsic(Prim::Intrinsic(Intrinsic::MakeStruct), args) = self[id] else { return None };
        let (&kind, values) = self[args].split_first()?;
        let Node::Quote(kind) = self[kind] else { return None };
        let kind = kind.downcast::<StructType>(mc)?;
        (kind.fields(mc) as usize == values.len()).then_some((kind, args))
    }

    /// Whether evaluating `id` cannot fault or cause side effects.
    pub(crate) fn is_pure(&self, mc: &Mutation<'gc>, id: Id<'id>) -> bool {
        let mut todo = vec![id];
        while let Some(id) = todo.pop() {
            let args = match self[id] {
                Node::Quote(_) | Node::Ref(_) | Node::Lambda(_) | Node::Intrinsic(Prim::Slot(SlotOp::Load, _), _) => continue,
                Node::Seq(first, second) => {
                    todo.extend([first, second]);
                    continue;
                }
                Node::If(test, then, other) => {
                    todo.extend([test, then, other]);
                    continue;
                }
                Node::Let(..) => {
                    self.children(id, |child| todo.push(child));
                    continue;
                }
                Node::Intrinsic(Prim::Intrinsic(intrinsic), args) if intrinsic.is_discardable() => args,
                Node::Intrinsic(Prim::Host(host), args) if host.purity == Purity::Discardable => args,
                Node::Intrinsic(_, args) if self.made_struct(mc, id).is_some() => args,
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
                Node::Quote(value) => value != Value::FALSE,
                Node::Lambda(_) | Node::Set(..) => true,
                Node::Intrinsic(Prim::Intrinsic(intrinsic), _) => intrinsic.is_always_truthy(),
                Node::Seq(_, last) | Node::Let(_, last) => {
                    todo.push(last);
                    true
                }
                Node::If(_, then, other) => {
                    todo.extend([then, other]);
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

    /// Panics if the tree rooted at `root` is malformed. Used by debug-build checks.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, root: Id<'id>) {
        if let Err(error) = self.verify(root) {
            panic!("malformed L2: {error}");
        }
    }

    /// Checks the tree and function bodies reachable from `root`. Each reachable node and function must
    /// have one parent; each variable must have one binding and be referenced only within its lexical
    /// scope. Unreachable nodes are ignored.
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
                Task::Bind(var) => {
                    if !bound.insert(var) {
                        return Err(format!("{var:?} is bound twice"));
                    }
                    locals.insert(var);
                }
                Task::Unbind(var) => _ = locals.remove(&var),
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
                    if let Node::Ref(var) | Node::Set(var, _) = self[id]
                        && !locals.contains(&var)
                    {
                        return Err(format!("{id:?}, {:?}, refers to what isn't in scope", self[id]));
                    }
                    match self[id] {
                        Node::Let(binds, body) => {
                            for &bind in &self[binds] {
                                match bind {
                                    Bind::Val(var, init) => then.extend([Task::Expr(init), Task::Bind(var)]),
                                    Bind::Fix(group) => {
                                        then.extend(self[group].iter().map(|&(var, _)| Task::Bind(var)));
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
