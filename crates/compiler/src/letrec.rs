//! Pass 2 (`L1 -> L2`): Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing.
//!
//! Eliminates `L1` `Letrec` forms, transforming each block into an ordered [`l2::Node::Let`] comprising:
//! - [`Bind::Val`] for non-recursive values, non-self-recursive lambdas, and unreferenced
//!   effectful expressions,
//! - [`Bind::Fix`] for strongly connected components of unassigned, mutually recursive lambdas,
//! - Initial [`Bind::Val`] bindings to `#<void>` followed by [`l2::Node::Set`] assignments only for
//!   complex bindings exhibiting true forward value dependencies.
//!
//! Traversal is performed iteratively via an explicit task stack, tracking free variable usages on a companion stack.

use ragwort_types::gc::{Mutation, Value};

use crate::Var;
use crate::hash::{HashMap, HashSet};
use crate::ir::l1::{self, L1};
use crate::ir::l2::{self, Bind, Fun, Id, L2, Node};
use crate::ir::Supply;

/// Maximum number of mutually recursive closures in a single `Fix` group. The emitter stages each closure of a group in one of its `STAGE` scratch registers, so a group cannot be larger than that.
const MAX_FIX_GROUP: usize = crate::emit::STAGE;

/// Lowers `root` from `from` into `tree` with all `letrec` bindings fixed, returning the new root node ID and updated `Supply`.
pub(crate) fn fix_letrec<'s, 'id, 'gc>(mc: &Mutation<'gc>, from: &L1<'s, 'gc>, root: l1::Id<'s>, tree: &mut L2<'id, 'gc>, mut supply: Supply) -> (Id<'id>, Supply) {
    /// A transformation task: an unvisited node, a usage scope boundary, or a deferred node assembly operation.
    enum Task<'s> {
        Expr(l1::Id<'s>),
        /// Pushes a fresh variable usage tracking context when entering a subexpression with isolated usage (a binding initializer, let body, or lambda body).
        Open,
        /// Finalizes processing of a binding initializer, recording the lowered node and its associated free variable usage.
        Keep,
        Make(l1::Id<'s>),
    }
    let mut cx = Cx { mc, tree, supply: &mut supply };
    let mut usages = vec![Usage::default()];
    let mut vals: Vec<Id<'id>> = Vec::new();
    // Stack of lowered initializers and their free variable usages for active enclosing binding forms.
    let mut inits: Vec<(Id<'id>, Usage)> = Vec::new();
    let mut todo = vec![Task::Expr(root)];
    let mut then = Vec::new();
    while let Some(task) = todo.pop() {
        let usage = usages.last_mut().expect("the root's usage is never closed");
        match task {
            Task::Open => usages.push(Usage::default()),
            Task::Keep => {
                let init_usage = usages.pop().expect("opened");
                inits.push((vals.pop().expect("a fixed init"), init_usage));
            }
            Task::Expr(id) => {
                cx.tree.at(from.site(id));
                match from[id] {
                l1::Node::Quote(value) => vals.push(cx.tree.add(Node::Quote(value))),
                l1::Node::Ref(var) => {
                    usage.used.insert(var);
                    vals.push(cx.tree.add(Node::Ref(var)));
                }
                l1::Node::Set(var, value) => {
                    usage.assigned.insert(var);
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
                }
            }
            Task::Make(id) => {
                cx.tree.at(from.site(id));
                let mut last = |count: usize| vals.split_off(vals.len() - count);
                let node = match from[id] {
                    l1::Node::If(..) => {
                        let [test, consequent, other] = last(3)[..] else { unreachable!() };
                        Node::If(test, consequent, other)
                    }
                    l1::Node::Set(var, _) => Node::Set(var, last(1)[0]),
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
                        let function = from[fun];
                        let params = &from[function.params];
                        usages.last_mut().expect("the root's usage is never closed").absorb(inner.bind(params.iter().copied().chain(function.rest)));
                        let params = cx.tree.list(params.iter().copied());
                        Node::Lambda(cx.tree.function(l2::Function { id: function.id, optional: function.optional, params, rest: function.rest, body }))
                    }
                    l1::Node::Let(binds, _) | l1::Node::Letrec(binds, _) => {
                        let body = last(1)[0];
                        let body_usage = usages.pop().expect("opened");
                        let fixed = inits.split_off(inits.len() - from[binds].len());
                        let binds: Vec<(Var, Id<'id>, Usage)> = from[binds].iter().zip(fixed).map(|(&(var, _), (init, init_usage))| (var, init, init_usage)).collect();
                        let (expr, combined) = if matches!(from[id], l1::Node::Letrec(..)) { cx.fix_block(binds, body, body_usage) } else { cx.simplify_let_with(binds, body, body_usage) };
                        usages.last_mut().expect("the root's usage is never closed").absorb(combined);
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
    /// Identifier generator for variables bound to the results of assignment expressions during fallback desugaring.
    supply: &'s mut Supply,
}

/// Tracks variables referenced and mutated within an expression, excluding those bound locally within it.
#[derive(Default)]
pub(crate) struct Usage {
    used: HashSet<Var>,
    assigned: HashSet<Var>,
}

impl Usage {
    /// Merges `other` into `self` using small-into-large set merging to maintain O(n log n) total complexity across AST traversal.
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

    fn mentions(&self, var: Var) -> bool {
        self.used.contains(&var) || self.assigned.contains(&var)
    }

    /// Returns the remaining free variable usage after removing the variables bound by `vars`.
    fn bind(mut self, vars: impl IntoIterator<Item = Var>) -> Self {
        for var in vars {
            self.forget(var);
        }
        self
    }

    fn forget(&mut self, var: Var) {
        self.used.remove(&var);
        self.assigned.remove(&var);
    }

    /// Computes the intersection of `self`'s used and assigned variables with `vars`, returning `(used_in_vars, assigned_in_vars)`.
    fn among(&self, vars: &HashSet<Var>) -> (HashSet<Var>, HashSet<Var>) {
        let among = |set: &HashSet<Var>| -> HashSet<Var> {
            if set.len() < vars.len() {
                set.iter().copied().filter(|var| vars.contains(var)).collect()
            } else {
                vars.iter().copied().filter(|var| set.contains(var)).collect()
            }
        };
        (among(&self.used), among(&self.assigned))
    }
}

/// Traverses `root` bottom-up in a single pass to eliminate unused pure bindings across the entire expression tree.
/// Bindings referenced solely by other dead bindings are transitively removed. If all bindings in a `let` are pruned,
/// the node is replaced by its body.
pub(crate) fn prune<'id, 'gc>(mc: &Mutation<'gc>, tree: &mut l2::L2<'id, 'gc>, root: l2::Id<'id>) {
    /// A pending traversal task in the pruning pass, tracking variable usage at the top of the `usages` stack.
    enum Task<'id> {
        Expr(l2::Id<'id>),
        /// Pushes a new variable usage tracking context upon entering a lambda body or `let` body.
        Open,
        /// Finalizes traversal of a function body, removes its formal parameters from the tracked usage, and merges remaining free variables into the outer scope.
        Function(l2::Fun<'id>),
        /// Evaluates `let` binding `index` after all subsequent bindings and the body have been processed: retains the binding if it is impure or referenced downstream.
        Bind(l2::Id<'id>, usize),
        /// Removes all variables bound by a mutually recursive `Fix` group from the active usage set after analyzing its member functions.
        Forget(l2::Span<'id, (Var, l2::Fun<'id>)>),
        Let(l2::Id<'id>),
    }
    let mut usages = vec![Usage::default()];
    // Stack of retained bindings for each active enclosing `let` expression, accumulated in reverse order.
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
            Task::Forget(group) => tree[group].iter().for_each(|&(var, _)| usage.forget(var)),
            Task::Bind(at, index) => {
                let l2::Node::Let(binds, _) = tree[at] else { unreachable!("a let's binding") };
                match tree[binds][index] {
                    l2::Bind::Val(var, init) => {
                        if usage.mentions(var) || !tree.is_pure(mc, init) {
                            usage.forget(var);
                            kept.last_mut().expect("in a let").push(l2::Bind::Val(var, init));
                            then.push(Task::Expr(init));
                        }
                    }
                    l2::Bind::Fix(group) => {
                        if tree[group].iter().any(|&(var, _)| usage.mentions(var)) {
                            for &(_, fun) in &tree[group] {
                                then.extend([Task::Open, Task::Expr(tree[fun].body), Task::Function(fun)]);
                            }
                            then.push(Task::Forget(group));
                            kept.last_mut().expect("in a let").push(l2::Bind::Fix(group));
                        }
                    }
                }
                if index > 0 {
                    then.push(Task::Bind(at, index - 1));
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
                l2::Node::Ref(var) => _ = usage.used.insert(var),
                l2::Node::Set(var, value) => {
                    usage.assigned.insert(var);
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

/// A letrec binding awaiting resolution, represented as `(original_index, variable, initializer_id)`.
type Pending<'id> = (usize, Var, Id<'id>);

impl<'id> Cx<'_, '_, 'id, '_> {
    /// Eliminates unused pure bindings from a `Let` given the usage profiles of its body and initializers, returning
    /// the simplified expression and combined variable usage. Preserves active bindings in original order to maintain flat expression bodies.
    fn simplify_let_with(&mut self, binds: Vec<(Var, Id<'id>, Usage)>, body: Id<'id>, body_usage: Usage) -> (Id<'id>, Usage) {
        let mut usage = body_usage;
        let mut kept = Vec::with_capacity(binds.len());
        for (var, init, init_usage) in binds.into_iter().rev() {
            if usage.mentions(var) || !self.tree.is_pure(self.mc, init) {
                usage.forget(var);
                usage.absorb(init_usage);
                kept.push(Bind::Val(var, init));
            }
        }
        kept.reverse();
        (self.with(kept, body), usage)
    }

    /// Wraps `body` in a `Let` node containing `binds`, or returns `body` directly if `binds` is empty.
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
        let letrec_vars: HashSet<Var> = binds.iter().map(|&(var, _, _)| var).collect();
        let mut used = HashSet::default();
        let mut assigned = HashSet::default();
        let mut fv: HashMap<Var, HashSet<Var>> = HashMap::with_capacity_and_hasher(binds.len(), Default::default());

        for (var, _, usage) in &binds {
            let (init_used, init_assigned) = usage.among(&letrec_vars);
            used.extend(init_used.iter().copied());
            assigned.extend(init_assigned.iter().copied());
            fv.insert(*var, init_used.into_iter().chain(init_assigned).collect());
        }
        let (body_used, body_assigned) = body_usage.among(&letrec_vars);
        used.extend(body_used);
        assigned.extend(body_assigned);

        // Discard completely unreferenced pure bindings; remaining bindings represent all active dependencies of the block.
        let mut usage = body_usage;
        let mut indexed: Vec<Pending<'id>> = Vec::with_capacity(binds.len());
        for (i, (var, init, init_usage)) in binds.into_iter().enumerate() {
            if used.contains(&var) || !self.tree.is_pure(self.mc, init) {
                usage.absorb(init_usage);
                indexed.push((i, var, init));
            }
        }
        let usage = usage.bind(letrec_vars.iter().copied());

        let mut bound: HashSet<Var> = HashSet::default();
        let mut pending_fix: Vec<Pending<'id>> = Vec::new();
        let mut out = Vec::with_capacity(indexed.len());
        let mut iter = indexed.into_iter().peekable();

        while let Some((idx, var, init)) = iter.next() {
            if !assigned.contains(&var) && used.contains(&var) && matches!(self.tree[init], Node::Lambda(_)) {
                pending_fix.push((idx, var, init));
                continue;
            }

            self.flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut out);

            if fv[&var].is_subset(&bound) {
                if used.contains(&var) {
                    bound.insert(var);
                }
                out.push(Bind::Val(var, init));
            } else {
                // Detected forward reference to an uninitialized variable: desugar remaining bindings into `#<void>` initialization followed by `Set` assignments in original source order.
                let mut rest: Vec<Pending<'id>> = std::mem::take(&mut pending_fix);
                rest.push((idx, var, init));
                rest.extend(iter);
                rest.sort_by_key(|&(original, _, _)| original);
                self.fallback(rest.into_iter().map(|(_, var, init)| (var, init)), &used, &mut out);
                break;
            }
        }

        if !pending_fix.is_empty() {
            self.flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut out);
            if !pending_fix.is_empty() {
                let mut rest = std::mem::take(&mut pending_fix);
                rest.sort_by_key(|&(original, _, _)| original);
                self.fallback(rest.into_iter().map(|(_, var, init)| (var, init)), &used, &mut out);
            }
        }

        (self.with(out, body), usage)
    }

    /// Desugars `rest` using the general fallback strategy: binds referenced variables to `#<void>`, then sequentially assigns each initializer or evaluates impure unused initializers for their side effects.
    fn fallback(&mut self, rest: impl IntoIterator<Item = (Var, Id<'id>)>, used: &HashSet<Var>, out: &mut Vec<Bind<'id>>) {
        let rest: Vec<(Var, Id<'id>)> = rest.into_iter().collect();
        for &(var, _) in rest.iter().filter(|(var, _)| used.contains(var)) {
            out.push(Bind::Val(var, self.tree.add(Node::Quote(Value::VOID))));
        }
        for (var, init) in rest {
            if used.contains(&var) {
                let set = self.tree.add(Node::Set(var, init));
                out.push(Bind::Val(self.supply.fresh_var(), set));
            } else if !self.tree.is_pure(self.mc, init) {
                out.push(Bind::Val(var, init));
            }
        }
    }

    /// Emits all functions in `pending_fix` whose transitive dependencies within the `letrec` block have been satisfied by already-bound variables or mutually dependent functions within `pending_fix`.
    fn flush_ready_fix(&mut self, pending_fix: &mut Vec<Pending<'id>>, bound: &mut HashSet<Var>, fv: &HashMap<Var, HashSet<Var>>, out: &mut Vec<Bind<'id>>) {
        if pending_fix.is_empty() {
            return;
        }
        let mut cand: HashSet<Var> = pending_fix.iter().map(|&(_, var, _)| var).collect();
        loop {
            let next: HashSet<Var> = cand.iter().copied().filter(|var| fv[var].iter().all(|dep| bound.contains(dep) || cand.contains(dep))).collect();
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

        // Decompose the dependency graph of `ready` functions into strongly connected components in topological order using Tarjan's algorithm.
        for scc in tarjan_sccs(ready, fv) {
            for &(var, _) in &scc {
                bound.insert(var);
            }
            if scc.len() == 1 {
                let (var, lambda) = scc[0];
                if fv[&var].contains(&var) {
                    let group = self.tree.list([(var, self.fun(lambda))]);
                    out.push(Bind::Fix(group));
                } else {
                    out.push(Bind::Val(var, lambda));
                }
            } else if scc.len() <= MAX_FIX_GROUP {
                let group: Vec<(Var, Fun<'id>)> = scc.iter().map(|&(var, lambda)| (var, self.fun(lambda))).collect();
                let group = self.tree.list(group);
                out.push(Bind::Fix(group));
            } else {
                // Fall back to desugared assignment for mutually recursive SCCs exceeding MAX_FIX_GROUP, which exceed available staging registers.
                let members: HashSet<Var> = scc.iter().map(|&(var, _)| var).collect();
                self.fallback(scc, &members, out);
            }
        }
    }
}

/// Computes the strongly connected components of `nodes` in topological dependency order (callees preceding callers) via Tarjan's algorithm.
fn tarjan_sccs<T: Copy>(nodes: Vec<(Var, T)>, fv: &HashMap<Var, HashSet<Var>>) -> Vec<Vec<(Var, T)>> {
    let count = nodes.len();
    let index_of: HashMap<Var, usize> = nodes.iter().enumerate().map(|(i, &(var, _))| (var, i)).collect();
    let edges: Vec<Vec<usize>> = nodes
        .iter()
        .map(|&(var, _)| {
            let mut deps: Vec<usize> = fv[&var].iter().filter_map(|dep| index_of.get(dep).copied()).collect();
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
        /// Iteratively explores `root` and reachable nodes using an explicit call stack to avoid machine stack overflow on deep dependency chains.
        fn visit(&mut self, root: usize) {
            let mut calls = vec![(root, 0)];
            self.enter(root);
            while let Some(&mut (node, ref mut next)) = calls.last_mut() {
                if let Some(&successor) = self.edges[node].get(*next) {
                    *next += 1;
                    match self.indices[successor] {
                        Some(w_idx) if self.on_stack[successor] => self.lowlink[node] = self.lowlink[node].min(w_idx),
                        Some(_) => {}
                        None => {
                            self.enter(successor);
                            calls.push((successor, 0));
                        }
                    }
                    continue;
                }
                calls.pop();
                if let Some(&(parent, _)) = calls.last() {
                    self.lowlink[parent] = self.lowlink[parent].min(self.lowlink[node]);
                }
                if Some(self.lowlink[node]) == self.indices[node] {
                    let mut scc = Vec::new();
                    while let Some(member) = self.stack.pop() {
                        self.on_stack[member] = false;
                        scc.push(member);
                        if member == node {
                            break;
                        }
                    }
                    scc.sort_unstable();
                    self.sccs.push(scc);
                }
            }
        }

        fn enter(&mut self, node: usize) {
            let idx = self.index;
            self.index += 1;
            self.indices[node] = Some(idx);
            self.lowlink[node] = idx;
            self.stack.push(node);
            self.on_stack[node] = true;
        }
    }

    let mut state = Tarjan {
        edges: &edges,
        index: 0,
        indices: vec![None; count],
        lowlink: vec![0; count],
        on_stack: vec![false; count],
        stack: Vec::with_capacity(count),
        sccs: Vec::new(),
    };
    for i in 0..count {
        if state.indices[i].is_none() {
            state.visit(i);
        }
    }

    state.sccs.into_iter().map(|scc| scc.into_iter().map(|i| nodes[i]).collect()).collect()
}
