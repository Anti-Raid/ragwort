//! Pass 4: assignment conversion, in two parts around [`contify`](crate::contify).
//!
//! [`lower`] (`L2 -> L3`) keeps each `Set` as an [`L3::Set`], so contification sees loops as they
//! are. After it, [`convert`] puts an assigned variable in a box (`MakeBox`, `Unbox`, `SetBox`)
//! only where its frame's register can't hold it:
//! - a closure uses it. A join's code doesn't count, as it runs in the frame.
//! - it can be assigned after a continuation is captured, since it was bound. A continuation
//!   that's re-entered copies the frame as it was when captured, where a box would be shared.
//! - an argument reads it and a later one of the same call assigns it, as codegen reads a
//!   variable's register in place, or moves the read past the others.
//!
//! The rest are assigned in their registers.

use std::collections::{HashMap, HashSet};

use ragwort_types::gc::Value;
use ragwort_vm::Intrinsic;

use crate::ir::{L2, L3, Supply};
use crate::{Func, Prim, Var};

/// `expr` as [`L3`], its assignments kept, and the variables they assign.
pub(crate) fn lower<'gc>(expr: L2<'gc>) -> (L3<'gc>, HashSet<Var>) {
    let mut assigned = HashSet::new();
    let out = lower_expr(expr, &mut assigned);
    (out, assigned)
}

fn lower_expr<'gc>(expr: L2<'gc>, assigned: &mut HashSet<Var>) -> L3<'gc> {
    let mut all = |exprs: Vec<L2<'gc>>| exprs.into_iter().map(|e| lower_expr(e, assigned)).collect();
    match expr {
        L2::Quote(v) => L3::Quote(v),
        L2::Ref(v) => L3::Ref(v),
        L2::If(test, then, other) => {
            let (test, then) = (lower_expr(*test, assigned), lower_expr(*then, assigned));
            L3::If(Box::new(test), Box::new(then), Box::new(lower_expr(*other, assigned)))
        }
        L2::Seq(a, b) => L3::Seq(Box::new(lower_expr(*a, assigned)), Box::new(lower_expr(*b, assigned))),
        L2::Let(binds, body) => {
            let binds = binds.into_iter().map(|(v, init)| (v, lower_expr(init, assigned))).collect();
            L3::Let(binds, Box::new(lower_expr(*body, assigned)))
        }
        L2::Fix(binds, body) => {
            let binds = binds.into_iter().map(|(v, f)| (v, lower_func(f, assigned))).collect();
            L3::Fix(binds, Box::new(lower_expr(*body, assigned)))
        }
        L2::Set(v, value) => {
            assigned.insert(v);
            L3::Set(v, Box::new(lower_expr(*value, assigned)))
        }
        L2::App(f, args) => {
            let f = lower_expr(*f, assigned);
            L3::App(Box::new(f), args.into_iter().map(|a| lower_expr(a, assigned)).collect())
        }
        L2::Lambda(f) => L3::Lambda(lower_func(f, assigned)),
        L2::Intrinsic(prim, args) => L3::Intrinsic(prim, all(args)),
        L2::ApplyIntrinsic(prim, args) => L3::ApplyIntrinsic(prim, all(args)),
    }
}

fn lower_func<'gc>(f: Func<L2<'gc>>, assigned: &mut HashSet<Var>) -> Func<L3<'gc>> {
    let body = Box::new(lower_expr(*f.body, assigned));
    Func { id: f.id, params: f.params, optional: f.optional, rest: f.rest, body }
}

/// Boxes those of the `assigned` variables of `expr` its frames' registers can't hold.
pub(crate) fn convert<'gc>(expr: &mut L3<'gc>, assigned: &HashSet<Var>, supply: &mut Supply) {
    if assigned.is_empty() {
        return;
    }
    let (bound, boxed) = (HashMap::new(), HashSet::new());
    let mut survey = Survey { assigned, bound, frame: 0, frames: 0, captures: 0, boxed };
    survey.expr(expr, true);
    let boxed = survey.boxed;
    if !boxed.is_empty() {
        rewrite(expr, &boxed, supply);
    }
}

/// Which assigned variables need boxes, walking each frame in the order it runs.
struct Survey<'s> {
    assigned: &'s HashSet<Var>,
    /// The frame each assigned variable is bound in, and how many capture points it had passed.
    bound: HashMap<Var, (u32, u32)>,
    frame: u32,
    frames: u32,
    /// The points where a continuation could be captured, so far on the way the walk follows.
    captures: u32,
    boxed: HashSet<Var>,
}

impl Survey<'_> {
    fn bind(&mut self, v: Var) {
        if self.assigned.contains(&v) {
            self.bound.insert(v, (self.frame, self.captures));
        }
    }

    fn uses(&mut self, v: Var) {
        if let Some(&(frame, _)) = self.bound.get(&v)
            && frame != self.frame
        {
            self.boxed.insert(v);
        }
    }

    /// `e`, which ends the frame if it's in `tail` position.
    fn expr<'gc>(&mut self, e: &L3<'gc>, tail: bool) {
        match e {
            L3::Quote(_) => {}
            L3::Ref(v) => self.uses(*v),
            L3::Set(v, value) => {
                self.expr(value, false);
                self.uses(*v);
                if let Some(&(_, at)) = self.bound.get(v)
                    && self.captures > at
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
                for (_, init) in binds {
                    self.expr(init, false);
                }
                for &(v, _) in binds {
                    self.bind(v);
                }
                self.expr(body, tail);
            }
            L3::Fix(binds, body) => {
                for (_, func) in binds {
                    self.func(func);
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
                // A join's code runs after any jump to it, and loops go round again, so the code is
                // walked twice, the second time as if all of it had run before.
                let mut start = self.captures;
                for _ in 0..2 {
                    let mut end = start;
                    for (_, func) in group {
                        self.captures = start;
                        for &p in func.params.iter().chain(&func.rest) {
                            self.bind(p);
                        }
                        self.expr(&func.body, tail);
                        end = end.max(self.captures);
                    }
                    start = end;
                }
                self.captures = start;
            }
        }
    }

    fn all<'gc>(&mut self, exprs: &[L3<'gc>]) {
        for e in exprs {
            self.expr(e, false);
        }
    }

    /// The body of a closure, a frame of its own.
    fn func<'gc>(&mut self, func: &Func<L3<'gc>>) {
        self.frames += 1;
        let outer = (std::mem::replace(&mut self.frame, self.frames), std::mem::replace(&mut self.captures, 0));
        for &p in func.params.iter().chain(&func.rest) {
            self.bind(p);
        }
        self.expr(&func.body, true);
        (self.frame, self.captures) = outer;
    }

    /// Boxes each variable an argument assigns that one before it reads.
    fn arguments<'a, 'gc: 'a>(&mut self, args: impl Iterator<Item = &'a L3<'gc>> + Clone) {
        for (j, arg) in args.clone().enumerate() {
            let mut sets = Vec::new();
            assigns(arg, &mut sets);
            for v in sets {
                if args.clone().take(j).any(|before| reads(before, v)) {
                    self.boxed.insert(v);
                }
            }
        }
    }
}

/// Adds the variables `e` assigns to `out`.
fn assigns<'gc>(e: &L3<'gc>, out: &mut Vec<Var>) {
    if let L3::Set(v, _) = e {
        out.push(*v);
    }
    children(e, |c| assigns(c, out));
}

/// Whether `e` reads `v`.
fn reads<'gc>(e: &L3<'gc>, v: Var) -> bool {
    if let L3::Ref(r) = e
        && *r == v
    {
        return true;
    }
    let mut found = false;
    children(e, |c| found |= reads(c, v));
    found
}

fn children<'gc>(e: &L3<'gc>, mut each: impl FnMut(&L3<'gc>)) {
    match e {
        L3::Quote(_) | L3::Ref(_) => {}
        L3::Set(_, value) => each(value),
        L3::If(a, b, c) => {
            each(a);
            each(b);
            each(c);
        }
        L3::Seq(a, b) => {
            each(a);
            each(b);
        }
        L3::Let(binds, body) => {
            binds.iter().for_each(|(_, init)| each(init));
            each(body);
        }
        L3::Fix(binds, body) | L3::Join { group: binds, scope: body } => {
            binds.iter().for_each(|(_, func)| each(&func.body));
            each(body);
        }
        L3::Lambda(func) => each(&func.body),
        L3::App(f, args) => {
            each(f);
            args.iter().for_each(each);
        }
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => args.iter().for_each(each),
    }
}

fn boxing<'gc>(intrinsic: Intrinsic, args: Vec<L3<'gc>>) -> L3<'gc> {
    L3::Intrinsic(Prim::Intrinsic(intrinsic), args)
}

/// `e` with the `boxed` variables in boxes.
fn rewrite<'gc>(e: &mut L3<'gc>, boxed: &HashSet<Var>, supply: &mut Supply) {
    match e {
        L3::Quote(_) => {}
        L3::Ref(v) => {
            if boxed.contains(v) {
                *e = boxing(Intrinsic::Unbox, vec![L3::Ref(*v)]);
            }
        }
        L3::Set(v, value) => {
            rewrite(value, boxed, supply);
            if boxed.contains(v) {
                let value = std::mem::replace(&mut **value, L3::Quote(Value::VOID));
                *e = boxing(Intrinsic::SetBox, vec![L3::Ref(*v), value]);
            }
        }
        L3::Let(binds, body) => {
            for (v, init) in binds.iter_mut() {
                rewrite(init, boxed, supply);
                if boxed.contains(v) {
                    let value = std::mem::replace(init, L3::Quote(Value::VOID));
                    *init = boxing(Intrinsic::MakeBox, vec![value]);
                }
            }
            rewrite(body, boxed, supply);
        }
        L3::Fix(binds, body) | L3::Join { group: binds, scope: body } => {
            for (_, func) in binds.iter_mut() {
                rewrite_func(func, boxed, supply);
            }
            rewrite(body, boxed, supply);
        }
        L3::Lambda(func) => rewrite_func(func, boxed, supply),
        L3::If(a, b, c) => {
            rewrite(a, boxed, supply);
            rewrite(b, boxed, supply);
            rewrite(c, boxed, supply);
        }
        L3::Seq(a, b) => {
            rewrite(a, boxed, supply);
            rewrite(b, boxed, supply);
        }
        L3::App(f, args) => {
            rewrite(f, boxed, supply);
            args.iter_mut().for_each(|a| rewrite(a, boxed, supply));
        }
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => {
            args.iter_mut().for_each(|a| rewrite(a, boxed, supply));
        }
    }
}

/// `func` with its boxed parameters taken as fresh ones and boxed as its body starts.
fn rewrite_func<'gc>(func: &mut Func<L3<'gc>>, boxed: &HashSet<Var>, supply: &mut Supply) {
    rewrite(&mut func.body, boxed, supply);
    let mut binds = Vec::new();
    for p in func.params.iter_mut().chain(&mut func.rest) {
        if boxed.contains(p) {
            let raw = supply.fresh_var();
            binds.push((*p, boxing(Intrinsic::MakeBox, vec![L3::Ref(raw)])));
            *p = raw;
        }
    }
    if !binds.is_empty() {
        let body = std::mem::replace(&mut *func.body, L3::Quote(Value::VOID));
        *func.body = L3::Let(binds, Box::new(body));
    }
}
