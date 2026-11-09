//! Pass 5 (`L3 -> L4`): closure conversion and tail-loop contification.
//!
//! - Contifies single-binding tail-recursive local `Fix` forms into in-frame [`L4::Loop`] /
//!   [`L4::Recur`] loops (zero closure allocation, zero call frames).
//! - Contifies `Let`-bound lambdas only ever called in tail position into [`L4::Join`]s, the
//!   calls into [`L4::Jump`]s within the frame.
//! - Resolves self-references inside single-binding recursive closures to [`VarRef::SelfClosure`]
//!   (register `0`, `frame::CLOSURE`), avoiding self-captured upvalues.
//! - Computes free variables bottom-up, splits variable references into [`VarRef::Local`],
//!   [`VarRef::Upvalue`], and [`VarRef::SelfClosure`], and attaches an explicit [`UpvalSource`]
//!   capture table to every [`Closure`].

use std::collections::{HashMap, HashSet};

use crate::ir::{Closure, L3, L4, UpvalSource, VarRef};
use crate::{Func, Var};

/// Maximum number of parameters for an in-frame contified loop (matches `codegen::STAGE`).
const MAX_LOOP_PARAMS: usize = 32;

pub(crate) fn closure_convert<'gc>(expr: &L3<'gc>) -> L4<'gc> {
    let mut env = Env {
        locals: HashSet::new(),
        upvalues: Vec::new(),
        self_closure: None,
        active_loops: HashSet::new(),
        active_joins: HashSet::new(),
        contified: HashMap::new(),
    };
    let out = convert_expr(expr, &mut env);
    debug_assert!(env.upvalues.is_empty(), "top-level expression has no free variables");
    out
}

struct Env {
    locals: HashSet<Var>,
    upvalues: Vec<Var>,
    self_closure: Option<Var>,
    active_loops: HashSet<Var>,
    active_joins: HashSet<Var>,
    /// Whether each loop or join variable decided on so far is contified.
    contified: HashMap<Var, bool>,
}

fn convert_expr<'gc>(expr: &L3<'gc>, env: &mut Env) -> L4<'gc> {
    match expr {
        L3::Quote(v) => L4::Quote(*v),
        L3::Ref(v) => L4::Ref(resolve_var(*v, env)),
        L3::If(test, then, other) => L4::If(
            Box::new(convert_expr(test, env)),
            Box::new(convert_expr(then, env)),
            Box::new(convert_expr(other, env)),
        ),
        L3::Seq(a, b) => L4::Seq(
            Box::new(convert_expr(a, env)),
            Box::new(convert_expr(b, env)),
        ),
        L3::Let(binds, body) => convert_let(binds, body, env),
        L3::Fix(binds, body) => {
            // 1. Check if a single-binding `Fix` can be contified into an in-frame `L4::Loop`.
            if let Some((loop_var, func, init_args)) = loop_of(binds, body, &mut env.contified) {
                let converted_inits: Vec<L4<'gc>> = init_args.iter().map(|a| convert_expr(a, env)).collect();
                for &p in &func.params {
                    env.locals.insert(p);
                }
                env.active_loops.insert(loop_var);
                let loop_body = convert_expr(&func.body, env);
                env.active_loops.remove(&loop_var);
                for &p in &func.params {
                    env.locals.remove(&p);
                }
                let params = func.params.iter().copied().zip(converted_inits).collect();
                return L4::Loop { id: loop_var, params, body: Box::new(loop_body) };
            }

            // 2. A single-binding `Fix` closure can reference itself via `VarRef::SelfClosure`
            //    (register 0) instead of capturing itself as an upvalue.
            if let [(self_var, func)] = binds.as_slice() {
                let clos = convert_closure(func, Some(*self_var), env);
                env.locals.insert(*self_var);
                let body = convert_expr(body, env);
                env.locals.remove(self_var);
                return L4::Fix(vec![(*self_var, clos)], Box::new(body));
            }

            // 3. General mutually recursive `Fix` SCC.
            for &(v, _) in binds {
                env.locals.insert(v);
            }
            let converted_binds: Vec<(Var, Closure<'gc>)> = binds
                .iter()
                .map(|&(v, ref f)| (v, convert_closure(f, None, env)))
                .collect();
            let body = convert_expr(body, env);
            for &(v, _) in binds {
                env.locals.remove(&v);
            }
            L4::Fix(converted_binds, Box::new(body))
        }
        L3::App(f, args) => {
            if let L3::Ref(v) = **f
                && env.active_loops.contains(&v)
            {
                let converted_args = args.iter().map(|a| convert_expr(a, env)).collect();
                return L4::Recur(v, converted_args);
            }
            if let L3::Ref(v) = **f
                && env.active_joins.contains(&v)
            {
                return L4::Jump(v, args.iter().map(|a| convert_expr(a, env)).collect());
            }
            L4::App(
                Box::new(convert_expr(f, env)),
                args.iter().map(|a| convert_expr(a, env)).collect(),
            )
        }
        L3::Lambda(f) => L4::Lambda(convert_closure(f, None, env)),
        L3::Intrinsic(prim, args) => {
            L4::Intrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect())
        }
        L3::ApplyIntrinsic(prim, args) => {
            L4::ApplyIntrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect())
        }
    }
}

/// A `Let`, its lambdas that are joins as [`L4::Join`]s around its body. Out of line, as it
/// takes more stack than [`convert_expr`]'s other cases, which deep expressions recurse through.
#[inline(never)]
fn convert_let<'gc>(binds: &[(Var, L3<'gc>)], body: &L3<'gc>, env: &mut Env) -> L4<'gc> {
    let mut converted_binds = Vec::with_capacity(binds.len());
    let mut joins = Vec::new();
    for &(v, ref init) in binds {
        match init {
            L3::Lambda(func) if is_join(v, func, body, &mut env.contified) => joins.push((v, func)),
            _ => converted_binds.push((v, convert_expr(init, env))),
        }
    }
    for &(v, _) in &converted_binds {
        env.locals.insert(v);
    }
    let mut converted_joins = Vec::with_capacity(joins.len());
    for &(v, func) in &joins {
        env.locals.extend(&func.params);
        converted_joins.push((v, func.params.clone(), convert_expr(&func.body, env)));
        for p in &func.params {
            env.locals.remove(p);
        }
    }
    env.active_joins.extend(joins.iter().map(|&(v, _)| v));
    let mut body = convert_expr(body, env);
    for (id, params, code) in converted_joins.into_iter().rev() {
        env.active_joins.remove(&id);
        body = L4::Join { id, params, body: Box::new(code), scope: Box::new(body) };
    }
    for &(v, _) in &converted_binds {
        env.locals.remove(&v);
    }
    if converted_binds.is_empty() { body } else { L4::Let(converted_binds, Box::new(body)) }
}

fn convert_closure<'gc>(
    func: &Func<L3<'gc>>,
    self_closure: Option<Var>,
    parent_env: &mut Env,
) -> Closure<'gc> {
    let mut child_env = Env {
        locals: func.params.iter().chain(&func.rest).copied().collect(),
        upvalues: Vec::new(),
        self_closure,
        active_loops: HashSet::new(),
        active_joins: HashSet::new(),
        contified: std::mem::take(&mut parent_env.contified),
    };
    let body = convert_expr(&func.body, &mut child_env);
    parent_env.contified = std::mem::take(&mut child_env.contified);
    let captures = child_env
        .upvalues
        .into_iter()
        .map(|v| match resolve_var(v, parent_env) {
            VarRef::Local(local) => UpvalSource::Local(local),
            VarRef::Upvalue(idx) => UpvalSource::Upvalue(idx),
            VarRef::SelfClosure => UpvalSource::SelfClosure,
        })
        .collect();
    Closure {
        id: func.id,
        params: func.params.clone(),
        optional: func.optional,
        rest: func.rest,
        captures,
        body: Box::new(body),
    }
}

fn resolve_var(v: Var, env: &mut Env) -> VarRef {
    if env.locals.contains(&v) {
        return VarRef::Local(v);
    }
    if env.self_closure == Some(v) {
        return VarRef::SelfClosure;
    }
    if let Some(idx) = env.upvalues.iter().position(|&u| u == v) {
        return VarRef::Upvalue(idx as u32);
    }
    let idx = env.upvalues.len() as u32;
    env.upvalues.push(v);
    VarRef::Upvalue(idx)
}

fn references_var<'gc>(expr: &L3<'gc>, target: Var) -> bool {
    match expr {
        L3::Quote(_) => false,
        L3::Ref(v) => *v == target,
        L3::If(a, b, c) => references_var(a, target) || references_var(b, target) || references_var(c, target),
        L3::Seq(a, b) => references_var(a, target) || references_var(b, target),
        L3::Let(binds, body) => binds.iter().any(|(_, init)| references_var(init, target)) || references_var(body, target),
        L3::Fix(binds, body) => binds.iter().any(|(_, f)| references_var(&f.body, target)) || references_var(body, target),
        L3::App(f, args) => references_var(f, target) || args.iter().any(|a| references_var(a, target)),
        L3::Lambda(f) => references_var(&f.body, target),
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) => args.iter().any(|a| references_var(a, target)),
    }
}

/// The loop a single-binding `Fix` is, if it's one: its variable, function and first arguments.
fn loop_of<'a, 'gc>(
    binds: &'a [(Var, Func<L3<'gc>>)],
    body: &'a L3<'gc>,
    contified: &mut HashMap<Var, bool>,
) -> Option<(Var, &'a Func<L3<'gc>>, &'a [L3<'gc>])> {
    let [(loop_var, func)] = binds else { return None };
    let L3::App(op, init_args) = body else { return None };
    let fits = **op == L3::Ref(*loop_var)
        && func.rest.is_none()
        && func.optional == 0
        && func.params.len() == init_args.len()
        && func.params.len() <= MAX_LOOP_PARAMS
        && !init_args.iter().any(|a| references_var(a, *loop_var));
    let decided = match contified.get(loop_var) {
        Some(&known) => known,
        None => {
            let known = fits && references_var(&func.body, *loop_var) && tail_calls_only(&func.body, *loop_var, func.params.len(), contified);
            contified.insert(*loop_var, known);
            known
        }
    };
    decided.then_some((*loop_var, func, init_args.as_slice()))
}

/// Whether `func`, bound to `var` by a `Let` whose body is `scope`, is a join: called there, only
/// in tail position, so jumps within the frame can take the place of the calls.
fn is_join<'gc>(var: Var, func: &Func<L3<'gc>>, scope: &L3<'gc>, contified: &mut HashMap<Var, bool>) -> bool {
    if let Some(&known) = contified.get(&var) {
        return known;
    }
    let known = func.rest.is_none()
        && func.optional == 0
        && func.params.len() <= MAX_LOOP_PARAMS
        && references_var(scope, var)
        && tail_calls_only(scope, var, func.params.len(), contified);
    contified.insert(var, known);
    known
}

/// Whether every occurrence of `var` in `expr` is a call of `arity` arguments in tail position
/// in the current frame: not in a lambda, unless it's a loop's or a join's, which are in-frame.
fn tail_calls_only<'gc>(expr: &L3<'gc>, var: Var, arity: usize, contified: &mut HashMap<Var, bool>) -> bool {
    match expr {
        L3::If(test, then, other) => {
            !references_var(test, var) && tail_calls_only(then, var, arity, contified) && tail_calls_only(other, var, arity, contified)
        }
        L3::Seq(a, b) => !references_var(a, var) && tail_calls_only(b, var, arity, contified),
        L3::Let(binds, body) => {
            for &(v, ref init) in binds {
                let fine = match init {
                    L3::Lambda(func) if is_join(v, func, body, contified) => tail_calls_only(&func.body, var, arity, contified),
                    _ => !references_var(init, var),
                };
                if !fine {
                    return false;
                }
            }
            tail_calls_only(body, var, arity, contified)
        }
        L3::Fix(binds, body) => match loop_of(binds, body, contified) {
            Some((_, func, inits)) => !inits.iter().any(|a| references_var(a, var)) && tail_calls_only(&func.body, var, arity, contified),
            None => !binds.iter().any(|(_, f)| references_var(&f.body, var)) && tail_calls_only(body, var, arity, contified),
        },
        L3::App(f, args) if **f == L3::Ref(var) => args.len() == arity && !args.iter().any(|a| references_var(a, var)),
        other => !references_var(other, var),
    }
}
