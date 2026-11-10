//! Pass 6 (`L3 -> L4`): closure conversion, after [`contify`](crate::contify).
//!
//! - Converts contification's joins, loops among them, into [`L4::Join`]s, and calls of them into
//!   [`L4::Jump`]s within the frame: no closures, no frames.
//! - Resolves self-references inside single-binding recursive closures to [`VarRef::SelfClosure`]
//!   (register `0`, `frame::CLOSURE`), avoiding self-captured upvalues.
//! - Computes free variables bottom-up, splits variable references into [`VarRef::Local`],
//!   [`VarRef::Upvalue`], and [`VarRef::SelfClosure`], and attaches an explicit [`UpvalSource`]
//!   capture table to every [`Closure`].

use crate::hash::HashSet;

use ragwort_alloc::{Arena, CollectIn, Vec, vec_in};

use crate::Var;
use crate::ir::{Bind, Bind3, Closure, Func, JoinCode, L3, L4, UpvalSource, VarRef};

pub(crate) fn closure_convert<'a, 'gc>(arena: &'a Arena, expr: &L3<'a, 'gc>) -> L4<'a, 'gc> {
    let mut env = Env { arena, locals: HashSet::default(), upvalues: std::vec::Vec::new(), self_closure: None };
    let out = convert_expr(expr, &mut env);
    debug_assert!(env.upvalues.is_empty(), "top-level expression has no free variables");
    out
}

struct Env<'a> {
    arena: &'a Arena,
    locals: HashSet<Var>,
    upvalues: std::vec::Vec<Var>,
    self_closure: Option<Var>,
}

fn convert_expr<'a, 'gc>(expr: &L3<'a, 'gc>, env: &mut Env<'a>) -> L4<'a, 'gc> {
    let arena = env.arena;
    match expr {
        L3::Quote(v) => L4::Quote(*v),
        L3::Ref(v) => L4::Ref(resolve_var(*v, env)),
        L3::If(test, then, other) => L4::If(
            env.arena.boxed(convert_expr(test, env)),
            env.arena.boxed(convert_expr(then, env)),
            env.arena.boxed(convert_expr(other, env)),
        ),
        L3::Seq(a, b) => L4::Seq(
            env.arena.boxed(convert_expr(a, env)),
            env.arena.boxed(convert_expr(b, env)),
        ),
        L3::Let(binds, body) => convert_let(binds, body, env),
        L3::Join { group, scope } => convert_join(group, scope, env),
        L3::Jump(v, args) => L4::Jump(*v, args.iter().map(|a| convert_expr(a, env)).collect_in(arena)),
        L3::Set(v, value) => {
            let VarRef::Local(v) = resolve_var(*v, env) else {
                unreachable!("assignment conversion boxes what closures assign")
            };
            L4::Set(v, env.arena.boxed(convert_expr(value, env)))
        }
        L3::App(f, args) => L4::App(
            env.arena.boxed(convert_expr(f, env)),
            args.iter().map(|a| convert_expr(a, env)).collect_in(arena),
        ),
        L3::Lambda(f) => L4::Lambda(convert_closure(f, None, env)),
        L3::Intrinsic(prim, args) => {
            L4::Intrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect_in(arena))
        }
        L3::ApplyIntrinsic(prim, args) => {
            L4::ApplyIntrinsic(*prim, args.iter().map(|a| convert_expr(a, env)).collect_in(arena))
        }
    }
}

/// A group of joins, their code in the frame. Out of line, as are the other cases that take more
/// stack than [`convert_expr`]'s others, which deep expressions recurse through.
#[inline(never)]
fn convert_join<'a, 'gc>(group: &[(Var, Func<'a, L3<'a, 'gc>>)], scope: &L3<'a, 'gc>, env: &mut Env<'a>) -> L4<'a, 'gc> {
    let mut code = Vec::with_capacity_in(group.len(), env.arena);
    for (id, func) in group {
        env.locals.extend(&func.params);
        let params = func.params.clone();
        code.push(JoinCode { id: *id, params, body: convert_expr(&func.body, env) });
        for p in &func.params {
            env.locals.remove(p);
        }
    }
    L4::Join { group: code, scope: env.arena.boxed(convert_expr(scope, env)) }
}

#[inline(never)]
fn convert_let<'a, 'gc>(binds: &[Bind3<'a, 'gc>], body: &L3<'a, 'gc>, env: &mut Env<'a>) -> L4<'a, 'gc> {
    let mut out = Vec::with_capacity_in(binds.len(), env.arena);
    for bind in binds {
        match bind {
            Bind::Val(v, init) => {
                let init = convert_expr(init, env);
                env.locals.insert(*v);
                out.push(Bind::Val(*v, init));
            }
            Bind::Fix(group) => out.push(Bind::Fix(convert_fix(group, env))),
        }
    }
    let body = convert_expr(body, env);
    for bind in &out {
        for v in bind.vars() {
            env.locals.remove(&v);
        }
    }
    L4::Let(out, env.arena.boxed(body))
}

/// A group of closures, which binds them as locals of the frame.
fn convert_fix<'a, 'gc>(group: &[(Var, Func<'a, L3<'a, 'gc>>)], env: &mut Env<'a>) -> Vec<'a, (Var, Closure<'a, 'gc>)> {
    // 1. A single-binding `Fix` closure can reference itself via `VarRef::SelfClosure`
    //    (register 0) instead of capturing itself as an upvalue.
    if let [(self_var, func)] = group {
        let clos = convert_closure(func, Some(*self_var), env);
        env.locals.insert(*self_var);
        return vec_in![env.arena; (*self_var, clos)];
    }

    // 2. General mutually recursive `Fix` SCC.
    for &(v, _) in group {
        env.locals.insert(v);
    }
    let arena = env.arena;
    group.iter().map(|&(v, ref f)| (v, convert_closure(f, None, env))).collect_in(arena)
}

fn convert_closure<'a, 'gc>(func: &Func<'a, L3<'a, 'gc>>, self_closure: Option<Var>, parent_env: &mut Env<'a>) -> Closure<'a, 'gc> {
    let arena = parent_env.arena;
    let mut child_env = Env {
        arena,
        locals: func.params.iter().chain(&func.rest).copied().collect(),
        upvalues: std::vec::Vec::new(),
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
        .collect_in(arena);
    Closure {
        id: func.id,
        params: func.params.clone(),
        optional: func.optional,
        rest: func.rest,
        captures,
        body: arena.boxed(body),
    }
}

fn resolve_var(v: Var, env: &mut Env<'_>) -> VarRef {
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
