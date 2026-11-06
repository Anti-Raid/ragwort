//! Pass 2 (`L1 -> L2`): Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing.
//!
//! Eliminates [`L1::Letrec`] in favor of:
//! - [`L2::Seq`] for unreferenced side-effecting bindings,
//! - [`L2::Let`] for non-recursive bindings and non-self-recursive lambdas,
//! - [`L2::Fix`] for strongly connected components of unassigned mutually recursive lambdas,
//! - [`L2::Let`] (`#<void>`) + [`L2::Set`] only for complex bindings with true forward value
//!   dependencies.

use std::collections::{HashMap, HashSet};

use ragwort_types::gc::Value;

use crate::Func;
use crate:: Var;
use crate::ir::{L1, L2, Supply};

/// Maximum number of closures in a single `Fix` group (must fit in `STAGE` scratch registers).
const MAX_FIX_GROUP: usize = 30;

pub(crate) fn fix_letrec<'gc>(l1: L1<'gc>, supply: Supply) -> (L2<'gc>, Supply) {
    (transform(l1, &mut Usage::default()), supply)
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
            self.used.remove(&v);
            self.assigned.remove(&v);
        }
        self
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

/// `expr` as `L2`, with what it uses added to `usage`.
fn transform<'gc>(expr: L1<'gc>, usage: &mut Usage) -> L2<'gc> {
    match expr {
        L1::Quote(v) => L2::Quote(v),
        L1::Ref(v) => {
            usage.used.insert(v);
            L2::Ref(v)
        }
        L1::If(test, then, other) => {
            let test = transform(*test, usage);
            let then = transform(*then, usage);
            L2::If(Box::new(test), Box::new(then), Box::new(transform(*other, usage)))
        }
        L1::Let(binds, body) => transform_binding(binds, *body, false, usage),
        L1::Letrec(binds, body) => transform_binding(binds, *body, true, usage),
        L1::Set(v, value) => {
            usage.assigned.insert(v);
            L2::Set(v, Box::new(transform(*value, usage)))
        }
        L1::App(f, args) => {
            let f = transform(*f, usage);
            L2::App(Box::new(f), transform_all(args, usage))
        }
        L1::Lambda(f) => {
            let mut inner = Usage::default();
            let body = transform(*f.body, &mut inner);
            usage.absorb(inner.bind(f.params.iter().copied().chain(f.rest)));
            L2::Lambda(Func { id: f.id, params: f.params, rest: f.rest, body: Box::new(body) })
        }
        L1::Intrinsic(prim, args) => L2::Intrinsic(prim, transform_all(args, usage)),
        L1::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(prim, transform_all(args, usage)),
    }
}

fn transform_all<'gc>(exprs: Vec<L1<'gc>>, usage: &mut Usage) -> Vec<L2<'gc>> {
    let mut out = Vec::with_capacity(exprs.len());
    for e in exprs {
        out.push(transform(e, usage));
    }
    out
}

#[inline(never)]
fn transform_binding<'gc>(binds: Vec<(Var, L1<'gc>)>, body: L1<'gc>, rec: bool, usage: &mut Usage) -> L2<'gc> {
    let mut out = Vec::with_capacity(binds.len());
    for (v, e) in binds {
        let mut u = Usage::default();
        let e = transform(e, &mut u);
        out.push((v, e, u));
    }
    let mut body_usage = Usage::default();
    let body = transform(body, &mut body_usage);
    let (expr, u) = if rec { fix_block(out, body, body_usage) } else { simplify_let_with(out, body, body_usage) };
    usage.absorb(u);
    expr
}

/// Drops the bindings in `expr` nothing uses, as [`simplify_let_with`] does for one `let`, for a
/// whole tree in one walk: inside out, so a binding only a dropped one used goes too.
pub(crate) fn prune<'gc>(mut expr: L2<'gc>) -> L2<'gc> {
    prune_into(&mut expr, &mut Usage::default());
    expr
}

/// Prunes `expr` in place, adding what's left of it uses to `usage`.
fn prune_into<'gc>(expr: &mut L2<'gc>, usage: &mut Usage) {
    match expr {
        L2::Quote(_) => {}
        L2::Ref(v) => _ = usage.used.insert(*v),
        L2::If(a, b, c) => {
            prune_into(a, usage);
            prune_into(b, usage);
            prune_into(c, usage);
        }
        L2::Seq(a, b) => {
            prune_into(a, usage);
            prune_into(b, usage);
        }
        L2::Let(..) | L2::Fix(..) => prune_binding(expr, usage),
        L2::Set(v, value) => {
            usage.assigned.insert(*v);
            prune_into(value, usage);
        }
        L2::App(f, args) => {
            prune_into(f, usage);
            for a in args {
                prune_into(a, usage);
            }
        }
        L2::Lambda(f) => prune_func(f, usage),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => {
            for a in args {
                prune_into(a, usage);
            }
        }
    }
}

fn prune_func<'gc>(f: &mut Func<L2<'gc>>, usage: &mut Usage) {
    let mut inner = Usage::default();
    prune_into(&mut f.body, &mut inner);
    usage.absorb(inner.bind(f.params.iter().copied().chain(f.rest)));
}

#[inline(never)]
fn prune_binding<'gc>(expr: &mut L2<'gc>, usage: &mut Usage) {
    let pruned = match std::mem::replace(expr, L2::Quote(Value::VOID)) {
        L2::Let(binds, mut body) => {
            let mut out = Vec::with_capacity(binds.len());
            for (v, mut e) in binds {
                let mut u = Usage::default();
                prune_into(&mut e, &mut u);
                out.push((v, e, u));
            }
            let mut body_usage = Usage::default();
            prune_into(&mut body, &mut body_usage);
            let (pruned, u) = simplify_let_with(out, *body, body_usage);
            usage.absorb(u);
            pruned
        }
        L2::Fix(mut binds, mut body) => {
            let mut body_usage = Usage::default();
            prune_into(&mut body, &mut body_usage);
            if binds.iter().any(|&(v, _)| body_usage.mentions(v)) {
                for (_, f) in &mut binds {
                    prune_func(f, &mut body_usage);
                }
                usage.absorb(body_usage.bind(binds.iter().map(|&(v, _)| v)));
                L2::Fix(binds, body)
            } else {
                usage.absorb(body_usage);
                *body
            }
        }
        other => other,
    };
    *expr = pruned;
}

/// Converts a `Let` whose bindings may be unused in `body` into `Seq`s and smaller `Let`s while
/// strictly preserving left-to-right binding evaluation order, given what `body` and each init
/// use, and says what the result uses.
fn simplify_let_with<'gc>(binds: Vec<(Var, L2<'gc>, Usage)>, body: L2<'gc>, body_usage: Usage) -> (L2<'gc>, Usage) {
    if binds.is_empty() {
        return (body, body_usage);
    }
    let vars: Vec<Var> = binds.iter().map(|&(v, _, _)| v).collect();
    let mut kept = Vec::new();
    let mut acc = body;
    let mut pending_let: Vec<(Var, L2<'gc>)> = Vec::new();
    for (v, init, usage) in binds.into_iter().rev() {
        if body_usage.mentions(v) {
            pending_let.push((v, init));
            kept.push(usage);
        } else if !init.is_pure() {
            if !pending_let.is_empty() {
                pending_let.reverse();
                acc = L2::Let(std::mem::take(&mut pending_let), Box::new(acc));
            }
            acc = L2::seq(init, acc);
            kept.push(usage);
        }
    }
    if !pending_let.is_empty() {
        pending_let.reverse();
        acc = L2::Let(pending_let, Box::new(acc));
    }
    let mut usage = body_usage;
    for u in kept {
        usage.absorb(u);
    }
    (acc, usage.bind(vars))
}

enum Step<'gc> {
    Seq(L2<'gc>),
    Let(Var, L2<'gc>),
    Fix(Vec<(Var, Func<L2<'gc>>)>),
    Boxed { vars: Vec<Var>, inits: Vec<L2<'gc>> },
}

fn fix_block<'gc>(binds: Vec<(Var, L2<'gc>, Usage)>, body: L2<'gc>, body_usage: Usage) -> (L2<'gc>, Usage) {
    if binds.is_empty() {
        return (body, body_usage);
    }
    let letrec_vars: HashSet<Var> = binds.iter().map(|&(v, _, _)| v).collect();
    let mut used = HashSet::new();
    let mut assigned = HashSet::new();
    let mut fv: HashMap<Var, HashSet<Var>> = HashMap::with_capacity(binds.len());

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
    let indexed: Vec<(usize, Var, L2<'gc>)> = binds
        .into_iter()
        .enumerate()
        .filter(|&(_, (v, ref init, _))| used.contains(&v) || !init.is_pure())
        .map(|(i, (v, init, u))| {
            usage.absorb(u);
            (i, v, init)
        })
        .collect();
    let usage = usage.bind(letrec_vars.iter().copied());

    let mut bound: HashSet<Var> = HashSet::new();
    let mut pending_fix: Vec<(usize, Var, Func<L2<'gc>>)> = Vec::new();
    let mut steps: Vec<Step<'gc>> = Vec::new();
    let mut iter = indexed.into_iter().peekable();

    while let Some((idx, v, init)) = iter.next() {
        if !assigned.contains(&v)
            && used.contains(&v)
            && let L2::Lambda(func) = init
        {
            pending_fix.push((idx, v, func));
            continue;
        }

        flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut steps);

        if fv[&v].is_subset(&bound) {
            if used.contains(&v) {
                bound.insert(v);
                steps.push(Step::Let(v, init));
            } else {
                steps.push(Step::Seq(init));
            }
        } else {
            // Forward reference to an uninitialized variable: fall back to `<void>` + `Set` for
            // the remaining bindings in their original lexical order.
            let mut rest: Vec<(usize, Var, L2<'gc>)> =
                pending_fix.drain(..).map(|(i, var, f)| (i, var, L2::Lambda(f))).collect();
            rest.push((idx, v, init));
            rest.extend(iter);
            rest.sort_by_key(|&(i, _, _)| i);
            emit_fallback(rest, &used, &mut steps);
            break;
        }
    }

    if !pending_fix.is_empty() {
        flush_ready_fix(&mut pending_fix, &mut bound, &fv, &mut steps);
        if !pending_fix.is_empty() {
            let mut rest: Vec<(usize, Var, L2<'gc>)> =
                pending_fix.drain(..).map(|(i, var, f)| (i, var, L2::Lambda(f))).collect();
            rest.sort_by_key(|&(i, _, _)| i);
            emit_fallback(rest, &used, &mut steps);
        }
    }

    let out = steps.into_iter().rfold(body, |acc, step| match step {
        Step::Seq(e) => L2::seq(e, acc),
        Step::Let(v, e) => L2::Let(vec![(v, e)], Box::new(acc)),
        Step::Fix(group) => L2::Fix(group, Box::new(acc)),
        Step::Boxed { vars, inits } => {
            let body = inits.into_iter().rfold(acc, |acc, e| L2::seq(e, acc));
            if vars.is_empty() {
                body
            } else {
                let binds = vars.into_iter().map(|v| (v, L2::Quote(Value::VOID))).collect();
                L2::Let(binds, Box::new(body))
            }
        }
    });
    (out, usage)
}

fn emit_fallback<'gc>(rest: Vec<(usize, Var, L2<'gc>)>, used: &HashSet<Var>, steps: &mut Vec<Step<'gc>>) {
    let mut vars = Vec::new();
    let mut inits = Vec::new();
    for (_, v, init) in rest {
        if used.contains(&v) {
            vars.push(v);
            inits.push(L2::Set(v, Box::new(init)));
        } else if !init.is_pure() {
            inits.push(init);
        }
    }
    steps.push(Step::Boxed { vars, inits });
}

/// Flushes all functions in `pending_fix` whose transitive dependencies in `letrec_vars` are
/// satisfied by `bound` and other ready functions in `pending_fix`.
fn flush_ready_fix<'gc>(
    pending_fix: &mut Vec<(usize, Var, Func<L2<'gc>>)>,
    bound: &mut HashSet<Var>,
    fv: &HashMap<Var, HashSet<Var>>,
    steps: &mut Vec<Step<'gc>>,
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
    for scc in tarjan_sccs(ready, fv) {
        if scc.len() == 1 {
            let (v, func) = scc.into_iter().next().expect("single-element SCC");
            bound.insert(v);
            if fv[&v].contains(&v) {
                steps.push(Step::Fix(vec![(v, func)]));
            } else {
                steps.push(Step::Let(v, L2::Lambda(func)));
            }
        } else if scc.len() <= MAX_FIX_GROUP {
            for &(v, _) in &scc {
                bound.insert(v);
            }
            steps.push(Step::Fix(scc));
        } else {
            // Very large mutually recursive SCC (> 30 functions): fall back to boxed assignment.
            let mut vars = Vec::with_capacity(scc.len());
            let mut inits = Vec::with_capacity(scc.len());
            for (v, func) in scc {
                bound.insert(v);
                vars.push(v);
                inits.push(L2::Set(v, Box::new(L2::Lambda(func))));
            }
            steps.push(Step::Boxed { vars, inits });
        }
    }
}

/// Computes strongly connected components of `nodes` in dependency order (callees before callers).
fn tarjan_sccs<'gc>(nodes: Vec<(Var, Func<L2<'gc>>)>, fv: &HashMap<Var, HashSet<Var>>) -> Vec<Vec<(Var, Func<L2<'gc>>)>> {
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
        fn visit(&mut self, v: usize) {
            let idx = self.index;
            self.index += 1;
            self.indices[v] = Some(idx);
            self.lowlink[v] = idx;
            self.stack.push(v);
            self.on_stack[v] = true;

            for &w in &self.edges[v] {
                if let Some(w_idx) = self.indices[w] {
                    if self.on_stack[w] {
                        self.lowlink[v] = self.lowlink[v].min(w_idx);
                    }
                } else {
                    self.visit(w);
                    self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                }
            }

            if self.lowlink[v] == idx {
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

    let mut opt_nodes: Vec<Option<(Var, Func<L2<'gc>>)>> = nodes.into_iter().map(Some).collect();
    state
        .sccs
        .into_iter()
        .map(|scc| scc.into_iter().map(|i| opt_nodes[i].take().expect("each node belongs to one SCC")).collect())
        .collect()
}

pub(crate) fn collect_usage<'gc>(expr: &L2<'gc>, used: &mut HashSet<Var>, assigned: &mut HashSet<Var>) {
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
            for (_, init) in binds {
                collect_usage(init, used, assigned);
            }
            collect_usage(body, used, assigned);
        }
        L2::Fix(binds, body) => {
            for (_, f) in binds {
                collect_usage(&f.body, used, assigned);
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
