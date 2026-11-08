//! Pass 5 (`L3 -> L4`): closure conversion and tail-loop contification.
//!
//! - Contifies single-binding tail-recursive local `Fix` forms into in-frame [`L4::Loop`] /
//!   [`L4::Recur`] loops (zero closure allocation, zero call frames).
//! - Resolves self-references inside single-binding recursive closures to [`VarRef::SelfClosure`]
//!   (register `0`, `frame::CLOSURE`), avoiding self-captured upvalues.
//! - Computes free variables bottom-up, splits variable references into [`VarRef::Local`],
//!   [`VarRef::Upvalue`], and [`VarRef::SelfClosure`], and attaches an explicit [`UpvalSource`]
//!   capture table to every [`Closure`].

use std::collections::HashSet;

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
        L3::Let(binds, body) => {
            let converted_binds: Vec<(Var, L4<'gc>)> = binds
                .iter()
                .map(|&(v, ref init)| (v, convert_expr(init, env)))
                .collect();
            for &(v, _) in &converted_binds {
                env.locals.insert(v);
            }
            let body = convert_expr(body, env);
            for &(v, _) in &converted_binds {
                env.locals.remove(&v);
            }
            L4::Let(converted_binds, Box::new(body))
        }
        L3::Fix(binds, body) => {
            // 1. Check if a single-binding `Fix` can be contified into an in-frame `L4::Loop`.
            if let [(loop_var, func)] = binds.as_slice()
                && let L3::App(op, init_args) = body.as_ref()
                && **op == L3::Ref(*loop_var)
                && func.rest.is_none()
                && func.optional == 0
                && func.params.len() == init_args.len()
                && func.params.len() <= MAX_LOOP_PARAMS
                && !init_args.iter().any(|a| references_var(a, *loop_var))
                && references_var(&func.body, *loop_var)
                && is_tail_loop_body(&func.body, *loop_var, func.params.len())
            {
                let converted_inits: Vec<L4<'gc>> = init_args.iter().map(|a| convert_expr(a, env)).collect();
                for &p in &func.params {
                    env.locals.insert(p);
                }
                env.active_loops.insert(*loop_var);
                let loop_body = convert_expr(&func.body, env);
                env.active_loops.remove(loop_var);
                for &p in &func.params {
                    env.locals.remove(&p);
                }
                let params = func.params.iter().copied().zip(converted_inits).collect();
                return L4::Loop { id: *loop_var, params, body: Box::new(loop_body) };
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
    };
    let body = convert_expr(&func.body, &mut child_env);
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

/// Checks that every occurrence of `loop_var` in `expr` is a direct tail call of `arity` arguments
/// in the current function frame (not inside a nested `Lambda` or `Fix` body).
fn is_tail_loop_body<'gc>(expr: &L3<'gc>, loop_var: Var, arity: usize) -> bool {
    match expr {
        L3::If(test, then, other) => {
            !references_var(test, loop_var)
                && is_tail_loop_body(then, loop_var, arity)
                && is_tail_loop_body(other, loop_var, arity)
        }
        L3::Seq(a, b) => !references_var(a, loop_var) && is_tail_loop_body(b, loop_var, arity),
        L3::Let(binds, body) => {
            !binds.iter().any(|(_, init)| references_var(init, loop_var))
                && is_tail_loop_body(body, loop_var, arity)
        }
        L3::Fix(binds, body) => {
            !binds.iter().any(|(_, f)| references_var(&f.body, loop_var))
                && is_tail_loop_body(body, loop_var, arity)
        }
        L3::App(f, args) if **f == L3::Ref(loop_var) => {
            args.len() == arity && !args.iter().any(|a| references_var(a, loop_var))
        }
        other => !references_var(other, loop_var),
    }
}
