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
    let out = transform(l1);
    (out, supply)
}

fn transform<'gc>(expr: L1<'gc>) -> L2<'gc> {
    match expr {
        L1::Quote(v) => L2::Quote(v),
        L1::Ref(v) => L2::Ref(v),
        L1::If(test, then, other) => L2::If(Box::new(transform(*test)), Box::new(transform(*then)), Box::new(transform(*other))),
        L1::Let(binds, body) => {
            let binds: Vec<(Var, L2<'gc>)> = binds.into_iter().map(|(v, e)| (v, transform(e))).collect();
            let body = transform(*body);
            simplify_let(binds, body)
        }
        L1::Letrec(binds, body) => {
            let binds: Vec<(Var, L2<'gc>)> = binds.into_iter().map(|(v, e)| (v, transform(e))).collect();
            let body = transform(*body);
            fix_block(binds, body)
        }
        L1::Set(v, value) => L2::Set(v, Box::new(transform(*value))),
        L1::App(f, args) => L2::App(Box::new(transform(*f)), args.into_iter().map(transform).collect()),
        L1::Lambda(f) => L2::Lambda(Func { id: f.id, params: f.params, rest: f.rest, body: Box::new(transform(*f.body)) }),
        L1::Intrinsic(prim, args) => L2::Intrinsic(prim, args.into_iter().map(transform).collect()),
        L1::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(prim, args.into_iter().map(transform).collect()),
    }
}

/// Converts a `Let` whose bindings may be unused in `body` into `Seq`s and smaller `Let`s while
/// strictly preserving left-to-right binding evaluation order.
pub(crate) fn simplify_let<'gc>(binds: Vec<(Var, L2<'gc>)>, body: L2<'gc>) -> L2<'gc> {
    if binds.is_empty() {
        return body;
    }
    let mut used = HashSet::new();
    let mut assigned = HashSet::new();
    collect_usage(&body, &mut used, &mut assigned);

    if binds.iter().all(|(v, _)| used.contains(v) || assigned.contains(v)) {
        return L2::Let(binds, Box::new(body));
    }

    let mut acc = body;
    let mut pending_let: Vec<(Var, L2<'gc>)> = Vec::new();
    for (v, init) in binds.into_iter().rev() {
        if used.contains(&v) || assigned.contains(&v) {
            pending_let.push((v, init));
        } else if !init.is_pure() {
            if !pending_let.is_empty() {
                pending_let.reverse();
                acc = L2::Let(std::mem::take(&mut pending_let), Box::new(acc));
            }
            acc = L2::seq(init, acc);
        }
    }
    if !pending_let.is_empty() {
        pending_let.reverse();
        acc = L2::Let(pending_let, Box::new(acc));
    }
    acc
}

enum Step<'gc> {
    Seq(L2<'gc>),
    Let(Var, L2<'gc>),
    Fix(Vec<(Var, Func<L2<'gc>>)>),
    Boxed { vars: Vec<Var>, inits: Vec<L2<'gc>> },
}

fn fix_block<'gc>(binds: Vec<(Var, L2<'gc>)>, body: L2<'gc>) -> L2<'gc> {
    if binds.is_empty() {
        return body;
    }
    let letrec_vars: HashSet<Var> = binds.iter().map(|&(v, _)| v).collect();
    let mut used = HashSet::new();
    let mut assigned = HashSet::new();
    let mut fv: HashMap<Var, HashSet<Var>> = HashMap::with_capacity(binds.len());

    for &(v, ref init) in &binds {
        let mut init_used = HashSet::new();
        let mut init_assigned = HashSet::new();
        collect_usage(init, &mut init_used, &mut init_assigned);
        used.extend(init_used.iter().copied().filter(|u| letrec_vars.contains(u)));
        assigned.extend(init_assigned.iter().copied().filter(|u| letrec_vars.contains(u)));
        let deps: HashSet<Var> = init_used.into_iter().chain(init_assigned).filter(|u| letrec_vars.contains(u)).collect();
        fv.insert(v, deps);
    }
    {
        let mut body_used = HashSet::new();
        let mut body_assigned = HashSet::new();
        collect_usage(&body, &mut body_used, &mut body_assigned);
        used.extend(body_used.into_iter().filter(|u| letrec_vars.contains(u)));
        assigned.extend(body_assigned.into_iter().filter(|u| letrec_vars.contains(u)));
    }

    // Filter out completely unused pure bindings.
    let indexed: Vec<(usize, Var, L2<'gc>)> = binds
        .into_iter()
        .enumerate()
        .filter(|&(_, (v, ref init))| used.contains(&v) || !init.is_pure())
        .map(|(i, (v, init))| (i, v, init))
        .collect();

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

    steps.into_iter().rfold(body, |acc, step| match step {
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
    })
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
