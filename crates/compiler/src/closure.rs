//! Pass 6 (`L3 -> L4`): closure conversion, after [`contify`](crate::contify).
//!
//! - Converts contification's joins, loops among them, into [`L4::Join`]s, and calls of them into
//!   [`L4::Jump`]s within the frame: no closures, no frames.
//! - Resolves self-references inside single-binding recursive closures to [`VarRef::SelfClosure`]
//!   (register `0`, `frame::CLOSURE`), avoiding self-captured upvalues.
//! - Computes free variables bottom-up, splits variable references into [`VarRef::Local`],
//!   [`VarRef::Upvalue`], and [`VarRef::SelfClosure`], and attaches an explicit [`UpvalSource`]
//!   capture table to every [`Closure`].

use std::collections::HashSet;

use crate::ir::{Closure, JoinCode, L3, L4, UpvalSource, VarRef};
use crate::{Func, Var};

pub(crate) fn closure_convert<'gc>(expr: &L3<'gc>) -> L4<'gc> {
    let mut env = Env { locals: HashSet::new(), upvalues: Vec::new(), self_closure: None };
    let out = convert_expr(expr, &mut env);
    debug_assert!(env.upvalues.is_empty(), "top-level expression has no free variables");
    out
}

struct Env {
    locals: HashSet<Var>,
    upvalues: Vec<Var>,
    self_closure: Option<Var>,
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
        L3::Fix(binds, body) => convert_fix(binds, body, env),
        L3::Join { group, scope } => convert_join(group, scope, env),
        L3::Jump(v, args) => L4::Jump(*v, args.iter().map(|a| convert_expr(a, env)).collect()),
        L3::App(f, args) => L4::App(
            Box::new(convert_expr(f, env)),
            args.iter().map(|a| convert_expr(a, env)).collect(),
        ),
        L3::Lambda(f) => L4::Lambda(convert_closure(f, None, env)),
        L3::Intrinsic(prim, args) => {
            L4::Intrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect())
        }
        L3::ApplyIntrinsic(prim, args) => {
            L4::ApplyIntrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect())
        }
    }
}

/// A group of joins, their code in the frame. Out of line, as are the other cases that take more
/// stack than [`convert_expr`]'s others, which deep expressions recurse through.
#[inline(never)]
fn convert_join<'gc>(group: &[(Var, Func<L3<'gc>>)], scope: &L3<'gc>, env: &mut Env) -> L4<'gc> {
    let mut code = Vec::with_capacity(group.len());
    for (id, func) in group {
        env.locals.extend(&func.params);
        code.push(JoinCode { id: *id, params: func.params.clone(), body: convert_expr(&func.body, env) });
        for p in &func.params {
            env.locals.remove(p);
        }
    }
    L4::Join { group: code, scope: Box::new(convert_expr(scope, env)) }
}

#[inline(never)]
fn convert_let<'gc>(binds: &[(Var, L3<'gc>)], body: &L3<'gc>, env: &mut Env) -> L4<'gc> {
    let converted_binds: Vec<_> = binds.iter().map(|&(v, ref init)| (v, convert_expr(init, env))).collect();
    for &(v, _) in &converted_binds {
        env.locals.insert(v);
    }
    let body = convert_expr(body, env);
    for &(v, _) in &converted_binds {
        env.locals.remove(&v);
    }
    L4::Let(converted_binds, Box::new(body))
}

#[inline(never)]
fn convert_fix<'gc>(binds: &[(Var, Func<L3<'gc>>)], body: &L3<'gc>, env: &mut Env) -> L4<'gc> {
    // 1. A single-binding `Fix` closure can reference itself via `VarRef::SelfClosure`
    //    (register 0) instead of capturing itself as an upvalue.
    if let [(self_var, func)] = binds {
        let clos = convert_closure(func, Some(*self_var), env);
        env.locals.insert(*self_var);
        let body = convert_expr(body, env);
        env.locals.remove(self_var);
        return L4::Fix(vec![(*self_var, clos)], Box::new(body));
    }

    // 2. General mutually recursive `Fix` SCC.
    for &(v, _) in binds {
        env.locals.insert(v);
    }
    let converted_binds: Vec<(Var, Closure<'gc>)> = binds.iter().map(|&(v, ref f)| (v, convert_closure(f, None, env))).collect();
    let body = convert_expr(body, env);
    for &(v, _) in binds {
        env.locals.remove(&v);
    }
    L4::Fix(converted_binds, Box::new(body))
}

fn convert_closure<'gc>(func: &Func<L3<'gc>>, self_closure: Option<Var>, parent_env: &mut Env) -> Closure<'gc> {
    let mut child_env = Env {
        locals: func.params.iter().chain(&func.rest).copied().collect(),
        upvalues: Vec::new(),
        self_closure,
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
