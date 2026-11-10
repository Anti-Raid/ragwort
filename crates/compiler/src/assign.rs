//! Pass 4: assignment conversion, in two parts around [`contify`](crate::contify).
//!
//! [`lower`] (`L2 -> L3`) keeps each `Set` as an [`L3::Set`], so contification sees loops as they
//! are. After it, [`convert`] puts an assigned variable in a box (`MakeBox`, `Unbox`, `SetBox`)
//! only where its frame's register can't hold it:
//! - a closure uses it. A join's code doesn't count, as it runs in the frame.
//! - it can be assigned after a continuation is captured, since it was bound. A continuation
//!   that's re-entered copies the frame as it was when captured, where a box would be shared.
//! - an argument reads it and a later one of the same call assigns it. The bytecode backend
//!   before L5 read a variable's register in place; L5's values already keep the read apart.
//!
//! The rest are assigned in their registers.

use crate::hash::{HashMap, HashSet};

use ragwort_vm::Intrinsic;

use ragwort_alloc::{Arena, Box, CollectIn, Vec, vec_in};

use crate::ir::{Bind, Bind3, Func, L2, L3, Supply};
use crate::{Prim, Var};

/// `expr` as [`L3`], its assignments kept, and the variables they assign.
pub(crate) fn lower<'a, 'gc>(arena: &'a Arena, expr: L2<'a, 'gc>) -> (L3<'a, 'gc>, HashSet<Var>) {
    let mut assigned = HashSet::default();
    let out = lower_expr(arena, expr, &mut assigned);
    (out, assigned)
}

fn lower_expr<'a, 'gc>(arena: &'a Arena, expr: L2<'a, 'gc>, assigned: &mut HashSet<Var>) -> L3<'a, 'gc> {
    let one = |e: Box<'a, L2<'a, 'gc>>, assigned: &mut HashSet<Var>| arena.boxed(lower_expr(arena, Box::into_inner(e), assigned));
    let all = |exprs: Vec<'a, L2<'a, 'gc>>, assigned: &mut HashSet<Var>| {
        exprs.into_iter().map(|e| lower_expr(arena, e, assigned)).collect_in(arena)
    };
    match expr {
        L2::Quote(v) => L3::Quote(v),
        L2::Ref(v) => L3::Ref(v),
        L2::If(test, then, other) => {
            let (test, then) = (one(test, assigned), one(then, assigned));
            L3::If(test, then, one(other, assigned))
        }
        L2::Seq(a, b) => {
            let a = one(a, assigned);
            L3::Seq(a, one(b, assigned))
        }
        L2::Let(binds, body) => {
            let bind = |b, assigned: &mut HashSet<Var>| match b {
                Bind::Val(v, init) => Bind::Val(v, lower_expr(arena, init, assigned)),
                Bind::Fix(group) => Bind::Fix(group.into_iter().map(|(v, f)| (v, lower_func(arena, f, assigned))).collect_in(arena)),
            };
            let binds = binds.into_iter().map(|b| bind(b, assigned)).collect_in(arena);
            L3::Let(binds, one(body, assigned))
        }
        L2::Set(v, value) => {
            assigned.insert(v);
            L3::Set(v, one(value, assigned))
        }
        L2::App(f, args) => {
            let f = one(f, assigned);
            L3::App(f, all(args, assigned))
        }
        L2::Lambda(f) => L3::Lambda(lower_func(arena, f, assigned)),
        L2::Intrinsic(prim, args) => L3::Intrinsic(prim, all(args, assigned)),
        L2::ApplyIntrinsic(prim, args) => L3::ApplyIntrinsic(prim, all(args, assigned)),
    }
}

fn lower_func<'a, 'gc>(arena: &'a Arena, f: Func<'a, L2<'a, 'gc>>, assigned: &mut HashSet<Var>) -> Func<'a, L3<'a, 'gc>> {
    let body = arena.boxed(lower_expr(arena, Box::into_inner(f.body), assigned));
    Func { id: f.id, params: f.params, optional: f.optional, rest: f.rest, body }
}

/// Boxes those of the `assigned` variables of `expr` its frames' registers can't hold.
pub(crate) fn convert<'a, 'gc>(arena: &'a Arena, expr: &mut L3<'a, 'gc>, assigned: &HashSet<Var>, supply: &mut Supply) {
    if assigned.is_empty() {
        return;
    }
    let mut survey = Survey { assigned, bound: HashMap::default(), frame: 0, frames: 0, captures: 0, boxed: HashSet::default() };
    survey.expr(expr, true);
    let boxed = survey.boxed;
    if !boxed.is_empty() {
        rewrite(arena, expr, &boxed, supply);
    }
}

/// Which assigned variables need boxes, walking each frame in the order it runs.
struct Survey<'s> {
    assigned: &'s HashSet<Var>,
    bound: HashMap<Var, Bound>,
    frame: u32,
    frames: u32,
    /// The points where a continuation could be captured, so far on the way the walk follows.
    captures: u32,
    boxed: HashSet<Var>,
}

/// Where an assigned variable is bound: in which frame, and how many capture points the walk had
/// passed.
#[derive(Clone, Copy)]
struct Bound {
    frame: u32,
    captures: u32,
}

impl Survey<'_> {
    fn bind(&mut self, v: Var) {
        if self.assigned.contains(&v) {
            self.bound.insert(v, Bound { frame: self.frame, captures: self.captures });
        }
    }

    fn uses(&mut self, v: Var) {
        if let Some(bound) = self.bound.get(&v)
            && bound.frame != self.frame
        {
            self.boxed.insert(v);
        }
    }

    /// `e`, which ends the frame if it's in `tail` position.
    fn expr<'gc>(&mut self, e: &L3<'_, 'gc>, tail: bool) {
        match e {
            L3::Quote(_) => {}
            L3::Ref(v) => self.uses(*v),
            L3::Set(v, value) => {
                self.expr(value, false);
                self.uses(*v);
                if let Some(bound) = self.bound.get(v)
                    && self.captures > bound.captures
                {
                    self.boxed.insert(*v);
                }
            }
            L3::If(test, then, other) => {
                self.expr(test, false);
                let start = self.captures;
                self.expr(then, tail);
                let after_then = std::mem::replace(&mut self.captures, start);
                self.expr(other, tail);
                self.captures = self.captures.max(after_then);
            }
            L3::Seq(a, b) => {
                self.expr(a, false);
                self.expr(b, tail);
            }
            L3::Let(binds, body) => {
                for bind in binds {
                    match bind {
                        Bind::Val(v, init) => {
                            self.expr(init, false);
                            self.bind(*v);
                        }
                        Bind::Fix(group) => group.iter().for_each(|(_, func)| self.func(func)),
                    }
                }
                self.expr(body, tail);
            }
            L3::Lambda(func) => self.func(func),
            L3::App(f, args) => {
                self.arguments(std::iter::once(&**f).chain(args));
                self.expr(f, false);
                self.all(args);
                if !tail {
                    self.captures += 1;
                }
            }
            L3::Intrinsic(prim, args) | L3::ApplyIntrinsic(prim, args) => {
                self.arguments(args.iter());
                self.all(args);
                if !tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..)) {
                    self.captures += 1;
                }
            }
            L3::Jump(_, args) => {
                self.arguments(args.iter());
                self.all(args);
            }
            L3::Join { group, scope } => {
                self.expr(scope, tail);
                // A join's code runs after any jump to it, and loops go round again, so it's walked
                // as if any capture point in it had come before all of it. Once, not twice, as
                // joins nest in joins' code.
                let again = group.iter().any(|(_, func)| captures(&func.body, tail));
                let start = self.captures + u32::from(again);
                let mut end = start;
                for (_, func) in group {
                    self.captures = start;
                    for &p in func.params.iter().chain(&func.rest) {
                        self.bind(p);
                    }
                    self.expr(&func.body, tail);
                    end = end.max(self.captures);
                }
                self.captures = end;
            }
        }
    }

    fn all<'gc>(&mut self, exprs: &[L3<'_, 'gc>]) {
        for e in exprs {
            self.expr(e, false);
        }
    }

    /// The body of a closure, a frame of its own.
    fn func<'gc>(&mut self, func: &Func<'_, L3<'_, 'gc>>) {
        self.frames += 1;
        let outer = (std::mem::replace(&mut self.frame, self.frames), std::mem::replace(&mut self.captures, 0));
        for &p in func.params.iter().chain(&func.rest) {
            self.bind(p);
        }
        self.expr(&func.body, true);
        (self.frame, self.captures) = outer;
    }

    /// Boxes each variable an argument assigns that one before it reads.
    fn arguments<'r, 't: 'r, 'gc: 't>(&mut self, args: impl Iterator<Item = &'r L3<'t, 'gc>> + Clone) {
        for (j, arg) in args.clone().enumerate() {
            let mut sets = std::vec::Vec::new();
            assigns(arg, &mut sets);
            for v in sets {
                if args.clone().take(j).any(|before| reads(before, v)) {
                    self.boxed.insert(v);
                }
            }
        }
    }
}

/// Whether `e`, which ends the frame if it's in `tail` position, has a point a continuation could
/// be captured at, as [`Survey`] counts them.
fn captures(e: &L3<'_, '_>, tail: bool) -> bool {
    match e {
        L3::Quote(_) | L3::Ref(_) | L3::Lambda(_) => false,
        L3::Set(_, value) => captures(value, false),
        L3::If(test, then, other) => captures(test, false) || captures(then, tail) || captures(other, tail),
        L3::Seq(a, b) => captures(a, false) || captures(b, tail),
        L3::Let(binds, body) => binds.iter().any(|b| matches!(b, Bind::Val(_, init) if captures(init, false))) || captures(body, tail),
        L3::App(f, args) => !tail || captures(f, false) || args.iter().any(|a| captures(a, false)),
        L3::Intrinsic(prim, args) | L3::ApplyIntrinsic(prim, args) => {
            (!tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..))) || args.iter().any(|a| captures(a, false))
        }
        L3::Jump(_, args) => args.iter().any(|a| captures(a, false)),
        L3::Join { group, scope } => captures(scope, tail) || group.iter().any(|(_, func)| captures(&func.body, tail)),
    }
}

/// Adds the variables `e` assigns to `out`.
fn assigns(e: &L3<'_, '_>, out: &mut std::vec::Vec<Var>) {
    if let L3::Set(v, _) = e {
        out.push(*v);
    }
    any_child(e, |c| {
        assigns(c, out);
        false
    });
}

/// Whether `e` reads `v`.
fn reads<'gc>(e: &L3<'_, 'gc>, v: Var) -> bool {
    matches!(e, L3::Ref(r) if *r == v) || any_child(e, |c| reads(c, v))
}

/// Whether `f` holds for any of `e`'s children, which it's called on in order until it does.
fn any_child<'gc>(e: &L3<'_, 'gc>, mut f: impl FnMut(&L3<'_, 'gc>) -> bool) -> bool {
    match e {
        L3::Quote(_) | L3::Ref(_) => false,
        L3::Set(_, value) => f(value),
        L3::If(a, b, c) => f(a) || f(b) || f(c),
        L3::Seq(a, b) => f(a) || f(b),
        L3::Let(binds, body) => {
            binds.iter().any(|b| match b {
                Bind::Val(_, init) => f(init),
                Bind::Fix(group) => group.iter().any(|(_, func)| f(&func.body)),
            }) || f(body)
        }
        L3::Join { group, scope } => group.iter().any(|(_, func)| f(&func.body)) || f(scope),
        L3::Lambda(func) => f(&func.body),
        L3::App(callee, args) => f(callee) || args.iter().any(f),
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => args.iter().any(f),
    }
}

fn boxing<'a, 'gc>(intrinsic: Intrinsic, args: Vec<'a, L3<'a, 'gc>>) -> L3<'a, 'gc> {
    L3::Intrinsic(Prim::Intrinsic(intrinsic), args)
}

/// `e` with the `boxed` variables in boxes.
fn rewrite<'a, 'gc>(arena: &'a Arena, e: &mut L3<'a, 'gc>, boxed: &HashSet<Var>, supply: &mut Supply) {
    match e {
        L3::Quote(_) => {}
        L3::Ref(v) => {
            if boxed.contains(v) {
                *e = boxing(Intrinsic::Unbox, vec_in![arena; L3::Ref(*v)]);
            }
        }
        L3::Set(v, value) => {
            rewrite(arena, value, boxed, supply);
            if boxed.contains(v) {
                let value = value.take();
                *e = boxing(Intrinsic::SetBox, vec_in![arena; L3::Ref(*v), value]);
            }
        }
        L3::Let(binds, body) => {
            for bind in binds.iter_mut() {
                match bind {
                    Bind::Val(v, init) => {
                        rewrite(arena, init, boxed, supply);
                        if boxed.contains(v) {
                            let value = init.take();
                            *init = boxing(Intrinsic::MakeBox, vec_in![arena; value]);
                        }
                    }
                    Bind::Fix(group) => group.iter_mut().for_each(|(_, func)| rewrite_func(arena, func, boxed, supply)),
                }
            }
            rewrite(arena, body, boxed, supply);
        }
        L3::Join { group, scope } => {
            for (_, func) in group.iter_mut() {
                rewrite_func(arena, func, boxed, supply);
            }
            rewrite(arena, scope, boxed, supply);
        }
        L3::Lambda(func) => rewrite_func(arena, func, boxed, supply),
        L3::If(a, b, c) => {
            rewrite(arena, a, boxed, supply);
            rewrite(arena, b, boxed, supply);
            rewrite(arena, c, boxed, supply);
        }
        L3::Seq(a, b) => {
            rewrite(arena, a, boxed, supply);
            rewrite(arena, b, boxed, supply);
        }
        L3::App(f, args) => {
            rewrite(arena, f, boxed, supply);
            args.iter_mut().for_each(|a| rewrite(arena, a, boxed, supply));
        }
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => {
            args.iter_mut().for_each(|a| rewrite(arena, a, boxed, supply));
        }
    }
}

/// `func` with its boxed parameters taken as fresh ones and boxed as its body starts.
fn rewrite_func<'a, 'gc>(arena: &'a Arena, func: &mut Func<'a, L3<'a, 'gc>>, boxed: &HashSet<Var>, supply: &mut Supply) {
    rewrite(arena, &mut func.body, boxed, supply);
    let mut binds: Vec<'a, Bind3<'a, 'gc>> = arena.vec();
    for p in func.params.iter_mut().chain(&mut func.rest) {
        if boxed.contains(p) {
            let raw = supply.fresh_var();
            binds.push(Bind::Val(*p, boxing(Intrinsic::MakeBox, vec_in![arena; L3::Ref(raw)])));
            *p = raw;
        }
    }
    if !binds.is_empty() {
        let body = func.body.take();
        *func.body = L3::Let(binds, arena.boxed(body));
    }
}
