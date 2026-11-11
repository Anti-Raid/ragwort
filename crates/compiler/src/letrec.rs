//! Pass 2 (`L1 -> L2`): Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing.
//!
//! Eliminates `L1`'s `Letrec` in favor of one [`l2::Node::Let`], in order, of:
//! - [`Bind::Val`] for non-recursive bindings, non-self-recursive lambdas, and unreferenced
//!   side-effecting bindings,
//! - [`Bind::Fix`] for strongly connected components of unassigned mutually recursive lambdas,
//! - [`Bind::Val`]s of `#<void>` and of [`l2::Node::Set`]s only for complex bindings with true
//!   forward value dependencies.
//!
//! It's a loop over a stack of tasks, what each node uses on a stack of its own.

use ragwort_types::gc::{Mutation, Value};

use crate::Var;
use crate::hash::{HashMap, HashSet};
use crate::ir::l1::{self, L1};
use crate::ir::l2::{self, Bind, Fun, Id, L2, Node};
use crate::ir::Supply;

/// Maximum number of closures in a single `Fix` group (must fit in `STAGE` scratch registers).
const MAX_FIX_GROUP: usize = 30;

/// `root` of `from` into `tree`, `letrec`s fixed, and its root there.
pub(crate) fn fix_letrec<'s, 'id, 'gc>(mc: &Mutation<'gc>, from: &L1<'s, 'gc>, root: l1::Id<'s>, tree: &mut L2<'id, 'gc>, mut supply: Supply) -> (Id<'id>, Supply) {
    /// A node to fix, or what to make of what its children fixed to.
    enum Task<'s> {
        Expr(l1::Id<'s>),
        /// Into what has a usage of its own: a binding's init, a binding form's body, or a
        /// function's.
        Open,
        /// A binding's init fixed, which keeps its usage.
        Keep,
        Make(l1::Id<'s>),
    }
    let mut cx = Cx { mc, tree, supply: &mut supply };
    let mut usages = vec![Usage::default()];
    let mut vals: Vec<Id<'id>> = Vec::new();
    // The inits fixed of each binding form the walk is in, with what they use.
    let mut inits: Vec<(Id<'id>, Usage)> = Vec::new();
    let mut todo = vec![Task::Expr(root)];
    let mut then = Vec::new();
    while let Some(task) = todo.pop() {
        let usage = usages.last_mut().expect("the root's usage is never closed");
        match task {
            Task::Open => usages.push(Usage::default()),
            Task::Keep => {
                let u = usages.pop().expect("opened");
                inits.push((vals.pop().expect("a fixed init"), u));
            }
            Task::Expr(id) => match from[id] {
                l1::Node::Quote(v) => vals.push(cx.tree.add(Node::Quote(v))),
                l1::Node::Ref(v) => {
                    usage.used.insert(v);
                    vals.push(cx.tree.add(Node::Ref(v)));
                }
                l1::Node::Set(v, value) => {
                    usage.assigned.insert(v);
                    then.extend([Task::Expr(value), Task::Make(id)]);
                }
                l1::Node::Lambda(fun) => then.extend([Task::Open, Task::Expr(from[fun].body), Task::Make(id)]),
                l1::Node::Let(binds, body) | l1::Node::Letrec(binds, body) => {
                    for &(_, init) in &from[binds] {
                        then.extend([Task::Open, Task::Expr(init), Task::Keep]);
                    }
                    then.extend([Task::Open, Task::Expr(body), Task::Make(id)]);
                }
                _ => {
                    from.children(id, |child| then.push(Task::Expr(child)));
                    then.push(Task::Make(id));
                }
            },
            Task::Make(id) => {
                let mut last = |n: usize| vals.split_off(vals.len() - n);
                let node = match from[id] {
                    l1::Node::If(..) => {
                        let [test, t, other] = last(3)[..] else { unreachable!() };
                        Node::If(test, t, other)
                    }
                    l1::Node::Set(v, _) => Node::Set(v, last(1)[0]),
                    l1::Node::App(_, args) => {
                        let mut all = last(from[args].len() + 1);
                        let args = all.split_off(1);
                        Node::App(all[0], cx.tree.list(args))
                    }
                    l1::Node::Intrinsic(prim, args) => Node::Intrinsic(prim, cx.tree.list(last(from[args].len()))),
                    l1::Node::ApplyIntrinsic(prim, args) => Node::ApplyIntrinsic(prim, cx.tree.list(last(from[args].len()))),
                    l1::Node::Lambda(fun) => {
                        let body = last(1)[0];
                        let inner = usages.pop().expect("opened");
                        let f = from[fun];
                        let params = &from[f.params];
                        usages.last_mut().expect("the root's usage is never closed").absorb(inner.bind(params.iter().copied().chain(f.rest)));
                        let params = cx.tree.list(params.iter().copied());
                        Node::Lambda(cx.tree.function(l2::Function { id: f.id, optional: f.optional, params, rest: f.rest, body }))
                    }
                    l1::Node::Let(binds, _) | l1::Node::Letrec(binds, _) => {
                        let body = last(1)[0];
                        let body_usage = usages.pop().expect("opened");
                        let fixed = inits.split_off(inits.len() - from[binds].len());
                        let binds: Vec<(Var, Id<'id>, Usage)> = from[binds].iter().zip(fixed).map(|(&(v, _), (e, u))| (v, e, u)).collect();
                        let (expr, u) = if matches!(from[id], l1::Node::Letrec(..)) { cx.fix_block(binds, body, body_usage) } else { cx.simplify_let_with(binds, body, body_usage) };
                        usages.last_mut().expect("the root's usage is never closed").absorb(u);
                        vals.push(expr);
                        continue;
                    }
                    l1::Node::Quote(_) | l1::Node::Ref(_) => unreachable!("leaves are made as they're reached"),
                };
                vals.push(cx.tree.add(node));
            }
        }
        todo.extend(then.drain(..).rev());
    }
    (vals.pop().expect("the root's fixed"), supply)
}

struct Cx<'t, 's, 'id, 'gc> {
    mc: &'t Mutation<'gc>,
    tree: &'t mut L2<'id, 'gc>,
    /// For the variables the results of a fallback's assignments are bound to.
    supply: &'s mut Supply,
}

/// The variables an expression refers to and assigns, outside the binding forms within it.
#[derive(Default)]
pub(crate) struct Usage {
    used: HashSet<Var>,
    assigned: HashSet<Var>,
}

impl Usage {
    /// Takes in `other`, the smaller poured into the larger, so merging up a whole tree costs
    /// `n log n`.
    fn absorb(&mut self, mut other: Self) {
        if self.used.len() < other.used.len() {
            std::mem::swap(&mut self.used, &mut other.used);
        }
        if self.assigned.len() < other.assigned.len() {
            std::mem::swap(&mut self.assigned, &mut other.assigned);
        }
        self.used.extend(other.used);
        self.assigned.extend(other.assigned);
    }

    fn mentions(&self, v: Var) -> bool {
        self.used.contains(&v) || self.assigned.contains(&v)
    }

    /// What's left outside a form binding `vars`.
    fn bind(mut self, vars: impl IntoIterator<Item = Var>) -> Self {
        for v in vars {
            self.forget(v);
        }
        self
    }

    fn forget(&mut self, v: Var) {
        self.used.remove(&v);
        self.assigned.remove(&v);
    }

    /// Those of `vars` this uses, and those it assigns.
    fn among(&self, vars: &HashSet<Var>) -> (HashSet<Var>, HashSet<Var>) {
        let among = |set: &HashSet<Var>| -> HashSet<Var> {
            if set.len() < vars.len() {
                set.iter().copied().filter(|v| vars.contains(v)).collect()
            } else {
                vars.iter().copied().filter(|v| set.contains(v)).collect()
            }
        };
        (among(&self.used), among(&self.assigned))
    }
}

/// Drops the bindings from `root` nothing uses, as `simplify_let_with` does for one `let`, for
/// a whole tree in one walk: inside out, so a binding only a dropped one used goes too. A `let`
/// left with none takes its body's place.
pub(crate) fn prune<'id, 'gc>(mc: &Mutation<'gc>, tree: &mut l2::L2<'id, 'gc>, root: l2::Id<'id>) {
    /// What's left of the walk, which takes what each node uses in on the top of `usages`.
    enum Task<'id> {
        Expr(l2::Id<'id>),
        /// Into a `let`'s body, or a function's, which has a usage of its own.
        Open,
        /// Out of a function's body, its parameters bound.
        Function(l2::Fun<'id>),
        /// The `let`'s binding `i`, once those after it are walked: it stays if what's after it
        /// mentions it, or it's not pure.
        Bind(l2::Id<'id>, usize),
        /// Its group's variables, once its functions are walked.
        Forget(l2::Span<'id, (Var, l2::Fun<'id>)>),
        Let(l2::Id<'id>),
    }
    let mut usages = vec![Usage::default()];
    // The bindings kept of each `let` the walk is in, last first.
    let mut kept: Vec<Vec<l2::Bind<'id>>> = Vec::new();
    let mut todo = vec![Task::Expr(root)];
    let mut then = Vec::new();
    while let Some(task) = todo.pop() {
        let usage = usages.last_mut().expect("the root's usage is never closed");
        match task {
            Task::Open => usages.push(Usage::default()),
            Task::Function(fun) => {
                let inner = usages.pop().expect("opened");
                let outer = usages.last_mut().expect("the root's usage is never closed");
                outer.absorb(inner.bind(tree.params(fun)));
            }
            Task::Forget(group) => tree[group].iter().for_each(|&(v, _)| usage.forget(v)),
            Task::Bind(at, i) => {
                let l2::Node::Let(binds, _) = tree[at] else { unreachable!("a let's binding") };
                match tree[binds][i] {
                    l2::Bind::Val(v, e) => {
                        if usage.mentions(v) || !tree.is_pure(mc, e) {
                            usage.forget(v);
                            kept.last_mut().expect("in a let").push(l2::Bind::Val(v, e));
                            then.push(Task::Expr(e));
                        }
                    }
                    l2::Bind::Fix(group) => {
                        if tree[group].iter().any(|&(v, _)| usage.mentions(v)) {
                            for &(_, fun) in &tree[group] {
                                then.extend([Task::Open, Task::Expr(tree[fun].body), Task::Function(fun)]);
                            }
                            then.push(Task::Forget(group));
                            kept.last_mut().expect("in a let").push(l2::Bind::Fix(group));
                        }
                    }
                }
                if i > 0 {
                    then.push(Task::Bind(at, i - 1));
                }
            }
            Task::Let(at) => {
                let l2::Node::Let(_, body) = tree[at] else { unreachable!("a let") };
                let inner = usages.pop().expect("opened");
                usages.last_mut().expect("the root's usage is never closed").absorb(inner);
                let mut binds = kept.pop().expect("in a let");
                binds.reverse();
                let node = if binds.is_empty() { tree[body] } else { l2::Node::Let(tree.list(binds), body) };
                tree.set(at, node);
            }
            Task::Expr(id) => match tree[id] {
                l2::Node::Ref(v) => _ = usage.used.insert(v),
                l2::Node::Set(v, value) => {
                    usage.assigned.insert(v);
                    then.push(Task::Expr(value));
                }
                l2::Node::Lambda(fun) => then.extend([Task::Open, Task::Expr(tree[fun].body), Task::Function(fun)]),
                l2::Node::Let(binds, body) => {
                    kept.push(Vec::new());
                    then.extend([Task::Open, Task::Expr(body)]);
                    if !tree[binds].is_empty() {
                        then.push(Task::Bind(id, tree[binds].len() - 1));
                    }
                    then.push(Task::Let(id));
                }
                _ => tree.children(id, |child| then.push(Task::Expr(child))),
            },
        }
        todo.extend(then.drain(..).rev());
    }
}

/// A binding still to be fixed, with its place among them.
type Pending<'id> = (usize, Var, Id<'id>);

impl<'id> Cx<'_, '_, 'id, '_> {
    /// Drops the pure bindings of a `Let` unused in `body`, given what `body` and each init use,
    /// and says what the result uses. The rest stay in it, in order, so a body of many forms, a
    /// `Let` of results unused, stays as flat as it was.
    fn simplify_let_with(&mut self, binds: Vec<(Var, Id<'id>, Usage)>, body: Id<'id>, body_usage: Usage) -> (Id<'id>, Usage) {
        let mut usage = body_usage;
        let mut kept = Vec::with_capacity(binds.len());
        for (v, init, init_usage) in binds.into_iter().rev() {
            if usage.mentions(v) || !self.tree.is_pure(self.mc, init) {
                usage.forget(v);
                usage.absorb(init_usage);
                kept.push(Bind::Val(v, init));
            }
        }
        kept.reverse();
        (self.with(kept, body), usage)
    }

    /// `body` in the scope of `binds`, if there are any.
    fn with(&mut self, binds: Vec<Bind<'id>>, body: Id<'id>) -> Id<'id> {
        if binds.is_empty() {
            return body;
        }
        let binds = self.tree.list(binds);
        self.tree.add(Node::Let(binds, body))
    }

    fn fun(&self, lambda: Id<'id>) -> Fun<'id> {
        let Node::Lambda(fun) = self.tree[lambda] else { unreachable!("a lambda") };
        fun
    }

    fn fix_block(&mut self, binds: Vec<(Var, Id<'id>, Usage)>, body: Id<'id>, body_usage: Usage) -> (Id<'id>, Usage) {
        if binds.is_empty() {
            return (body, body_usage);
        }
        let letrec_vars: HashSet<Var> = binds.iter().map(|&(v, _, _)| v).collect();
        let mut used = HashSet::default();
        let mut assigned = HashSet::default();
        let mut fv: HashMap<Var, HashSet<Var>> = HashMap::with_capacity_and_hasher(binds.len(), Default::default());

        for (v, _, usage) in &binds {
            let (init_used, init_assigned) = usage.among(&letrec_vars);
            used.extend(init_used.iter().copied());
            assigned.extend(init_assigned.iter().copied());
            fv.insert(*v, init_used.into_iter().chain(init_assigned).collect());
        }
        let (body_used, body_assigned) = body_usage.among(&letrec_vars);
        used.extend(body_used);
        assigned.extend(body_assigned);

        // Filter out completely unused pure bindings; what's left is all the block uses.
        let mut usage = body_usage;
        let mut indexed: Vec<Pending<'id>> = Vec::with_capacity(binds.len());
        for (i, (v, init, u)) in binds.into_iter().enumerate() {
            if used.contains(&v) || !self.tree.is_pure(self.mc, init) {
                usage.absorb(u);
                indexed.push((i, v, init));
            }
        }
        let usage = usage.bind(letrec_vars.iter().copied());

        let mut bound: HashSet<Var> = HashSet::default();
        let mut pending_fix: Vec<Pending<'id>> = Vec::new();
        let mut out = Vec::with_capacity(indexed.len());
        let mut iter = indexed.into_iter().peekable();

        while let Some((idx, v, init)) = iter.next() {
            if !assigned.contains(&v) && used.contains(&v) && matches!(self.tree[init], Node::Lambda(_)) {
                pending_fix.push((idx, v, init));
                continue;
            }

            self.flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut out);

            if fv[&v].is_subset(&bound) {
                if used.contains(&v) {
                    bound.insert(v);
                }
                out.push(Bind::Val(v, init));
            } else {
                // Forward reference to an uninitialized variable: fall back to `<void>` + `Set` for
                // the remaining bindings in their original lexical order.
                let mut rest: Vec<Pending<'id>> = std::mem::take(&mut pending_fix);
                rest.push((idx, v, init));
                rest.extend(iter);
                rest.sort_by_key(|&(i, _, _)| i);
                self.fallback(rest.into_iter().map(|(_, v, init)| (v, init)), &used, &mut out);
                break;
            }
        }

        if !pending_fix.is_empty() {
            self.flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut out);
            if !pending_fix.is_empty() {
                let mut rest = std::mem::take(&mut pending_fix);
                rest.sort_by_key(|&(i, _, _)| i);
                self.fallback(rest.into_iter().map(|(_, v, init)| (v, init)), &used, &mut out);
            }
        }

        (self.with(out, body), usage)
    }

    /// Binds those of `rest` used to `#<void>`, then assigns each its init, or evaluates it if
    /// it's unused, in order.
    fn fallback(&mut self, rest: impl IntoIterator<Item = (Var, Id<'id>)>, used: &HashSet<Var>, out: &mut Vec<Bind<'id>>) {
        let rest: Vec<(Var, Id<'id>)> = rest.into_iter().collect();
        for &(v, _) in rest.iter().filter(|(v, _)| used.contains(v)) {
            out.push(Bind::Val(v, self.tree.add(Node::Quote(Value::VOID))));
        }
        for (v, init) in rest {
            if used.contains(&v) {
                let set = self.tree.add(Node::Set(v, init));
                out.push(Bind::Val(self.supply.fresh_var(), set));
            } else if !self.tree.is_pure(self.mc, init) {
                out.push(Bind::Val(v, init));
            }
        }
    }

    /// Flushes all functions in `pending_fix` whose transitive dependencies in `letrec_vars` are
    /// satisfied by `bound` and other ready functions in `pending_fix`.
    fn flush_ready_fix(&mut self, pending_fix: &mut Vec<Pending<'id>>, bound: &mut HashSet<Var>, fv: &HashMap<Var, HashSet<Var>>, out: &mut Vec<Bind<'id>>) {
        if pending_fix.is_empty() {
            return;
        }
        let mut cand: HashSet<Var> = pending_fix.iter().map(|&(_, v, _)| v).collect();
        loop {
            let next: HashSet<Var> = cand.iter().copied().filter(|v| fv[v].iter().all(|dep| bound.contains(dep) || cand.contains(dep))).collect();
            if next.len() == cand.len() {
                break;
            }
            cand = next;
        }
        if cand.is_empty() {
            return;
        }

        let mut ready = Vec::with_capacity(cand.len());
        let mut kept = Vec::new();
        for item in pending_fix.drain(..) {
            if cand.contains(&item.1) {
                ready.push((item.1, item.2));
            } else {
                kept.push(item);
            }
        }
        *pending_fix = kept;

        // Decompose `ready` into Tarjan strongly-connected components in topological order.
        for scc in tarjan_sccs(ready, fv) {
            for &(v, _) in &scc {
                bound.insert(v);
            }
            if scc.len() == 1 {
                let (v, lambda) = scc[0];
                if fv[&v].contains(&v) {
                    let group = self.tree.list([(v, self.fun(lambda))]);
                    out.push(Bind::Fix(group));
                } else {
                    out.push(Bind::Val(v, lambda));
                }
            } else if scc.len() <= MAX_FIX_GROUP {
                let group: Vec<(Var, Fun<'id>)> = scc.iter().map(|&(v, lambda)| (v, self.fun(lambda))).collect();
                let group = self.tree.list(group);
                out.push(Bind::Fix(group));
            } else {
                // Very large mutually recursive SCC (> 30 functions): fall back to boxed assignment.
                let members: HashSet<Var> = scc.iter().map(|&(v, _)| v).collect();
                self.fallback(scc, &members, out);
            }
        }
    }
}

/// Computes strongly connected components of `nodes` in dependency order (callees before callers).
fn tarjan_sccs<T: Copy>(nodes: Vec<(Var, T)>, fv: &HashMap<Var, HashSet<Var>>) -> Vec<Vec<(Var, T)>> {
    let n = nodes.len();
    let index_of: HashMap<Var, usize> = nodes.iter().enumerate().map(|(i, &(v, _))| (v, i)).collect();
    let edges: Vec<Vec<usize>> = nodes
        .iter()
        .map(|&(v, _)| {
            let mut deps: Vec<usize> = fv[&v].iter().filter_map(|dep| index_of.get(dep).copied()).collect();
            deps.sort_unstable();
            deps
        })
        .collect();

    struct Tarjan<'a> {
        edges: &'a [Vec<usize>],
        index: u32,
        indices: Vec<Option<u32>>,
        lowlink: Vec<u32>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        sccs: Vec<Vec<usize>>,
    }

    impl Tarjan<'_> {
        /// Visits `root` and what it reaches, with a stack of where each visit is in its edges
        /// in place of recursion, as a long chain of definitions would go deep.
        fn visit(&mut self, root: usize) {
            let mut calls = vec![(root, 0)];
            self.enter(root);
            while let Some(&mut (v, ref mut next)) = calls.last_mut() {
                if let Some(&w) = self.edges[v].get(*next) {
                    *next += 1;
                    match self.indices[w] {
                        Some(w_idx) if self.on_stack[w] => self.lowlink[v] = self.lowlink[v].min(w_idx),
                        Some(_) => {}
                        None => {
                            self.enter(w);
                            calls.push((w, 0));
                        }
                    }
                    continue;
                }
                calls.pop();
                if let Some(&(parent, _)) = calls.last() {
                    self.lowlink[parent] = self.lowlink[parent].min(self.lowlink[v]);
                }
                if Some(self.lowlink[v]) == self.indices[v] {
                    let mut scc = Vec::new();
                    while let Some(w) = self.stack.pop() {
                        self.on_stack[w] = false;
                        scc.push(w);
                        if w == v {
                            break;
                        }
                    }
                    scc.sort_unstable();
                    self.sccs.push(scc);
                }
            }
        }

        fn enter(&mut self, v: usize) {
            let idx = self.index;
            self.index += 1;
            self.indices[v] = Some(idx);
            self.lowlink[v] = idx;
            self.stack.push(v);
            self.on_stack[v] = true;
        }
    }

    let mut state = Tarjan {
        edges: &edges,
        index: 0,
        indices: vec![None; n],
        lowlink: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::with_capacity(n),
        sccs: Vec::new(),
    };
    for i in 0..n {
        if state.indices[i].is_none() {
            state.visit(i);
        }
    }

    state.sccs.into_iter().map(|scc| scc.into_iter().map(|i| nodes[i]).collect()).collect()
}
