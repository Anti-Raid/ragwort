//! Pass 2 (`L1 -> L2`): Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing.
//!
//! Eliminates [`L1::Letrec`] in favor of one [`L2::Let`], in order, of:
//! - [`Bind::Val`] for non-recursive bindings, non-self-recursive lambdas, and unreferenced
//!   side-effecting bindings,
//! - [`Bind::Fix`] for strongly connected components of unassigned mutually recursive lambdas,
//! - [`Bind::Val`]s of `#<void>` and of [`L2::Set`]s only for complex bindings with true forward
//!   value dependencies.

use ragwort_alloc::{Arena, Box, CollectIn, Vec as AVec, vec_in};
use ragwort_types::gc::Value;

use crate::Var;
use crate::hash::{HashMap, HashSet};
use crate::ir::{Bind, Bind2, Func, L1, L2, Supply};


/// Maximum number of closures in a single `Fix` group (must fit in `STAGE` scratch registers).
const MAX_FIX_GROUP: usize = 30;

pub(crate) fn fix_letrec<'a, 'gc>(arena: &'a Arena, l1: L1<'a, 'gc>, mut supply: Supply) -> (L2<'a, 'gc>, Supply) {
    let mut cx = Cx { arena, supply: &mut supply };
    let out = cx.transform(l1, &mut Usage::default());
    (out, supply)
}

struct Cx<'a, 's> {
    arena: &'a Arena,
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

// The walks below recurse once per level of nesting, so they keep their frames small: binding
// forms, which need more, are handled out of line.

impl<'a> Cx<'a, '_> {
    /// `expr` as `L2`, with what it uses added to `usage`.
    fn transform<'gc>(&mut self, expr: L1<'a, 'gc>, usage: &mut Usage) -> L2<'a, 'gc> {
        let arena = self.arena;
        match expr {
            L1::Quote(v) => L2::Quote(v),
            L1::Ref(v) => {
                usage.used.insert(v);
                L2::Ref(v)
            }
            L1::If(test, then, other) => {
                let test = self.transform(Box::into_inner(test), usage);
                let then = self.transform(Box::into_inner(then), usage);
                L2::If(arena.boxed(test), arena.boxed(then), arena.boxed(self.transform(Box::into_inner(other), usage)))
            }
            L1::Let(binds, body) => self.binding(binds, Box::into_inner(body), false, usage),
            L1::Letrec(binds, body) => self.binding(binds, Box::into_inner(body), true, usage),
            L1::Set(v, value) => {
                usage.assigned.insert(v);
                L2::Set(v, arena.boxed(self.transform(Box::into_inner(value), usage)))
            }
            L1::App(f, args) => {
                let f = self.transform(Box::into_inner(f), usage);
                L2::App(arena.boxed(f), self.all(args, usage))
            }
            L1::Lambda(f) => {
                let mut inner = Usage::default();
                let body = self.transform(Box::into_inner(f.body), &mut inner);
                usage.absorb(inner.bind(f.params.iter().copied().chain(f.rest)));
                L2::Lambda(Func { id: f.id, params: f.params, optional: f.optional, rest: f.rest, body: arena.boxed(body) })
            }
            L1::Intrinsic(prim, args) => L2::Intrinsic(prim, self.all(args, usage)),
            L1::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(prim, self.all(args, usage)),
        }
    }

    fn all<'gc>(&mut self, exprs: AVec<'a, L1<'a, 'gc>>, usage: &mut Usage) -> AVec<'a, L2<'a, 'gc>> {
        let mut out = AVec::with_capacity_in(exprs.len(), self.arena);
        for e in exprs {
            out.push(self.transform(e, usage));
        }
        out
    }

    #[inline(never)]
    fn binding<'gc>(&mut self, binds: AVec<'a, (Var, L1<'a, 'gc>)>, body: L1<'a, 'gc>, rec: bool, usage: &mut Usage) -> L2<'a, 'gc> {
        let mut out = Vec::with_capacity(binds.len());
        for (v, e) in binds {
            let mut u = Usage::default();
            let e = self.transform(e, &mut u);
            out.push((v, e, u));
        }
        let mut body_usage = Usage::default();
        let body = self.transform(body, &mut body_usage);
        let (expr, u) = if rec { self.fix_block(out, body, body_usage) } else { simplify_let_with(self.arena, out, body, body_usage) };
        usage.absorb(u);
        expr
    }
}

/// Drops the bindings in `expr` nothing uses, as [`simplify_let_with`] does for one `let`, for a
/// whole tree in one walk: inside out, so a binding only a dropped one used goes too.
pub(crate) fn prune<'a, 'gc>(arena: &'a Arena, mut expr: L2<'a, 'gc>) -> L2<'a, 'gc> {
    prune_into(arena, &mut expr, &mut Usage::default());
    expr
}

/// Prunes `expr` in place, adding what's left of it uses to `usage`.
fn prune_into<'a, 'gc>(arena: &'a Arena, expr: &mut L2<'a, 'gc>, usage: &mut Usage) {
    match expr {
        L2::Quote(_) => {}
        L2::Ref(v) => _ = usage.used.insert(*v),
        L2::If(a, b, c) => {
            prune_into(arena, a, usage);
            prune_into(arena, b, usage);
            prune_into(arena, c, usage);
        }
        L2::Seq(a, b) => {
            prune_into(arena, a, usage);
            prune_into(arena, b, usage);
        }
        L2::Let(..) => prune_binding(arena, expr, usage),
        L2::Set(v, value) => {
            usage.assigned.insert(*v);
            prune_into(arena, value, usage);
        }
        L2::App(f, args) => {
            prune_into(arena, f, usage);
            for a in args {
                prune_into(arena, a, usage);
            }
        }
        L2::Lambda(f) => prune_func(arena, f, usage),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => {
            for a in args {
                prune_into(arena, a, usage);
            }
        }
    }
}

fn prune_func<'a, 'gc>(arena: &'a Arena, f: &mut Func<'a, L2<'a, 'gc>>, usage: &mut Usage) {
    let mut inner = Usage::default();
    prune_into(arena, &mut f.body, &mut inner);
    usage.absorb(inner.bind(f.params.iter().copied().chain(f.rest)));
}

#[inline(never)]
fn prune_binding<'a, 'gc>(arena: &'a Arena, expr: &mut L2<'a, 'gc>, usage: &mut Usage) {
    let L2::Let(binds, mut body) = expr.take() else { return };
    let mut u = Usage::default();
    prune_into(arena, &mut body, &mut u);
    // Last first, as each binding is in scope in those after it.
    let mut kept = Vec::with_capacity(binds.len());
    for bind in binds.into_iter().rev() {
        match bind {
            Bind::Val(v, mut e) => {
                if u.mentions(v) || !e.is_pure() {
                    u.forget(v);
                    prune_into(arena, &mut e, &mut u);
                    kept.push(Bind::Val(v, e));
                }
            }
            Bind::Fix(mut group) => {
                if group.iter().any(|&(v, _)| u.mentions(v)) {
                    for (_, f) in &mut group {
                        prune_func(arena, f, &mut u);
                    }
                    for &(v, _) in &group {
                        u.forget(v);
                    }
                    kept.push(Bind::Fix(group));
                }
            }
        }
    }
    usage.absorb(u);
    *expr = if kept.is_empty() { Box::into_inner(body) } else { L2::Let(kept.into_iter().rev().collect_in(arena), body) };
}

/// Drops the pure bindings of a `Let` unused in `body`, given what `body` and each init use, and
/// says what the result uses. The rest stay in it, in order, so a body of many forms, a `Let` of
/// results unused, stays as flat as it was.
fn simplify_let_with<'a, 'gc>(arena: &'a Arena, binds: Vec<(Var, L2<'a, 'gc>, Usage)>, body: L2<'a, 'gc>, body_usage: Usage) -> (L2<'a, 'gc>, Usage) {
    let mut usage = body_usage;
    let mut kept = Vec::with_capacity(binds.len());
    for (v, init, init_usage) in binds.into_iter().rev() {
        if usage.mentions(v) || !init.is_pure() {
            usage.forget(v);
            usage.absorb(init_usage);
            kept.push(Bind::Val(v, init));
        }
    }
    let out = if kept.is_empty() { body } else { L2::Let(kept.into_iter().rev().collect_in(arena), arena.boxed(body)) };
    (out, usage)
}

/// A binding still to be fixed, with its place among them.
type Pending<'a, 'gc> = (usize, Var, L2<'a, 'gc>);

impl<'a> Cx<'a, '_> {
    fn fix_block<'gc>(&mut self, binds: Vec<(Var, L2<'a, 'gc>, Usage)>, body: L2<'a, 'gc>, body_usage: Usage) -> (L2<'a, 'gc>, Usage) {
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
        let indexed: Vec<Pending<'a, 'gc>> = binds
            .into_iter()
            .enumerate()
            .filter(|&(_, (v, ref init, _))| used.contains(&v) || !init.is_pure())
            .map(|(i, (v, init, u))| {
                usage.absorb(u);
                (i, v, init)
            })
            .collect();
        let usage = usage.bind(letrec_vars.iter().copied());

        let mut bound: HashSet<Var> = HashSet::default();
        let mut pending_fix: Vec<(usize, Var, Func<'a, L2<'a, 'gc>>)> = Vec::new();
        let mut out = AVec::with_capacity_in(indexed.len(), self.arena);
        let mut iter = indexed.into_iter().peekable();

        while let Some((idx, v, init)) = iter.next() {
            if !assigned.contains(&v)
                && used.contains(&v)
                && let L2::Lambda(func) = init
            {
                pending_fix.push((idx, v, func));
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
                let mut rest: Vec<Pending<'a, 'gc>> = pending_fix.drain(..).map(|(i, var, f)| (i, var, L2::Lambda(f))).collect();
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
                let mut rest: Vec<Pending<'a, 'gc>> = pending_fix.drain(..).map(|(i, var, f)| (i, var, L2::Lambda(f))).collect();
                rest.sort_by_key(|&(i, _, _)| i);
                self.fallback(rest.into_iter().map(|(_, v, init)| (v, init)), &used, &mut out);
            }
        }

        let expr = if out.is_empty() { body } else { L2::Let(out, self.arena.boxed(body)) };
        (expr, usage)
    }

    /// Binds those of `rest` used to `#<void>`, then assigns each its init, or evaluates it if
    /// it's unused, in order.
    fn fallback<'gc>(&mut self, rest: impl IntoIterator<Item = (Var, L2<'a, 'gc>)>, used: &HashSet<Var>, out: &mut AVec<'a, Bind2<'a, 'gc>>) {
        let rest: Vec<(Var, L2<'a, 'gc>)> = rest.into_iter().collect();
        out.extend(rest.iter().filter(|(v, _)| used.contains(v)).map(|&(v, _)| Bind::Val(v, L2::Quote(Value::VOID))));
        for (v, init) in rest {
            if used.contains(&v) {
                out.push(Bind::Val(self.supply.fresh_var(), L2::Set(v, self.arena.boxed(init))));
            } else if !init.is_pure() {
                out.push(Bind::Val(v, init));
            }
        }
    }

    /// Flushes all functions in `pending_fix` whose transitive dependencies in `letrec_vars` are
    /// satisfied by `bound` and other ready functions in `pending_fix`.
    fn flush_ready_fix<'gc>(
        &mut self,
        pending_fix: &mut Vec<(usize, Var, Func<'a, L2<'a, 'gc>>)>,
        bound: &mut HashSet<Var>,
        fv: &HashMap<Var, HashSet<Var>>,
        out: &mut AVec<'a, Bind2<'a, 'gc>>,
    ) {
        if pending_fix.is_empty() {
            return;
        }
        let mut cand: HashSet<Var> = pending_fix.iter().map(|&(_, v, _)| v).collect();
        loop {
            let next: HashSet<Var> = cand
                .iter()
                .copied()
                .filter(|v| fv[v].iter().all(|dep| bound.contains(dep) || cand.contains(dep)))
                .collect();
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
        for scc in tarjan_sccs(self.arena, ready, fv) {
            for &(v, _) in &scc {
                bound.insert(v);
            }
            if scc.len() == 1 {
                let (v, func) = scc.into_iter().next().expect("single-element SCC");
                if fv[&v].contains(&v) {
                    out.push(Bind::Fix(vec_in![self.arena; (v, func)]));
                } else {
                    out.push(Bind::Val(v, L2::Lambda(func)));
                }
            } else if scc.len() <= MAX_FIX_GROUP {
                out.push(Bind::Fix(scc));
            } else {
                // Very large mutually recursive SCC (> 30 functions): fall back to boxed assignment.
                let members: HashSet<Var> = scc.iter().map(|&(v, _)| v).collect();
                self.fallback(scc.into_iter().map(|(v, func)| (v, L2::Lambda(func))), &members, out);
            }
        }
    }
}

/// Computes strongly connected components of `nodes` in dependency order (callees before callers).
fn tarjan_sccs<'a, 'gc>(arena: &'a Arena, nodes: Vec<(Var, Func<'a, L2<'a, 'gc>>)>, fv: &HashMap<Var, HashSet<Var>>) -> Vec<AVec<'a, (Var, Func<'a, L2<'a, 'gc>>)>> {
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

    let mut opt_nodes: Vec<Option<(Var, Func<'a, L2<'a, 'gc>>)>> = nodes.into_iter().map(Some).collect();
    state
        .sccs
        .into_iter()
        .map(|scc| scc.into_iter().map(|i| opt_nodes[i].take().expect("each node belongs to one SCC")).collect_in(arena))
        .collect()
}

pub(crate) fn collect_usage(expr: &L2<'_, '_>, used: &mut HashSet<Var>, assigned: &mut HashSet<Var>) {
    match expr {
        L2::Quote(_) => {}
        L2::Ref(v) => {
            used.insert(*v);
        }
        L2::If(test, then, other) => {
            collect_usage(test, used, assigned);
            collect_usage(then, used, assigned);
            collect_usage(other, used, assigned);
        }
        L2::Seq(a, b) => {
            collect_usage(a, used, assigned);
            collect_usage(b, used, assigned);
        }
        L2::Let(binds, body) => {
            for bind in binds {
                match bind {
                    Bind::Val(_, init) => collect_usage(init, used, assigned),
                    Bind::Fix(group) => group.iter().for_each(|(_, f)| collect_usage(&f.body, used, assigned)),
                }
            }
            collect_usage(body, used, assigned);
        }
        L2::Set(v, value) => {
            assigned.insert(*v);
            collect_usage(value, used, assigned);
        }
        L2::App(f, args) => {
            collect_usage(f, used, assigned);
            for arg in args {
                collect_usage(arg, used, assigned);
            }
        }
        L2::Lambda(f) => collect_usage(&f.body, used, assigned),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => {
            for arg in args {
                collect_usage(arg, used, assigned);
            }
        }
    }
}
