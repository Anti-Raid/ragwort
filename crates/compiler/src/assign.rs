//! Pass 4 (`L2 -> L3`): assignment conversion.
//!
//! Rewrites only variables that are actually mutated (`L2::Set`) into explicit heap boxes
//! (`Intrinsic::MakeBox`, `Intrinsic::Unbox`, `Intrinsic::SetBox`), eliminating `Set` from the IR
//! so all variables in [`L3`] are immutable.

use std::collections::HashSet;

use ragwort_vm::Intrinsic;

use crate::ir::{L2, L3, Supply};
use crate::letrec::collect_usage;
use crate::{Func, Prim, Var};

pub(crate) fn assignment_convert<'gc>(expr: L2<'gc>, mut supply: Supply) -> (L3<'gc>, Supply) {
    let mut used = HashSet::new();
    let mut assigned = HashSet::new();
    collect_usage(&expr, &mut used, &mut assigned);

    let out = convert(expr, &assigned, &mut supply);
    (out, supply)
}

fn convert<'gc>(expr: L2<'gc>, assigned: &HashSet<Var>, supply: &mut Supply) -> L3<'gc> {
    match expr {
        L2::Quote(v) => L3::Quote(v),
        L2::Ref(v) => {
            if assigned.contains(&v) {
                L3::Intrinsic(Prim::Intrinsic(Intrinsic::Unbox), vec![L3::Ref(v)])
            } else {
                L3::Ref(v)
            }
        }
        L2::If(test, then, other) => L3::If(
            Box::new(convert(*test, assigned, supply)),
            Box::new(convert(*then, assigned, supply)),
            Box::new(convert(*other, assigned, supply)),
        ),
        L2::Seq(a, b) => L3::Seq(Box::new(convert(*a, assigned, supply)), Box::new(convert(*b, assigned, supply))),
        L2::Let(binds, body) => {
            let binds = binds
                .into_iter()
                .map(|(v, init)| {
                    let init = convert(init, assigned, supply);
                    if assigned.contains(&v) {
                        (v, L3::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), vec![init]))
                    } else {
                        (v, init)
                    }
                })
                .collect();
            L3::Let(binds, Box::new(convert(*body, assigned, supply)))
        }
        L2::Fix(binds, body) => {
            let binds = binds.into_iter().map(|(v, f)| (v, convert_func(f, assigned, supply))).collect();
            L3::Fix(binds, Box::new(convert(*body, assigned, supply)))
        }
        L2::Set(v, value) => {
            let value = convert(*value, assigned, supply);
            L3::Intrinsic(Prim::Intrinsic(Intrinsic::SetBox), vec![L3::Ref(v), value])
        }
        L2::App(f, args) => L3::App(
            Box::new(convert(*f, assigned, supply)),
            args.into_iter().map(|a| convert(a, assigned, supply)).collect(),
        ),
        L2::Lambda(f) => L3::Lambda(convert_func(f, assigned, supply)),
        L2::Intrinsic(prim, args) => L3::Intrinsic(prim, args.into_iter().map(|a| convert(a, assigned, supply)).collect()),
        L2::ApplyIntrinsic(prim, args) => L3::ApplyIntrinsic(prim, args.into_iter().map(|a| convert(a, assigned, supply)).collect()),
    }
}

fn convert_func<'gc>(f: Func<L2<'gc>>, assigned: &HashSet<Var>, supply: &mut Supply) -> Func<L3<'gc>> {
    let mut box_binds = Vec::new();
    let params = f
        .params
        .into_iter()
        .map(|v| {
            if assigned.contains(&v) {
                let raw = supply.fresh_var();
                box_binds.push((v, L3::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), vec![L3::Ref(raw)])));
                raw
            } else {
                v
            }
        })
        .collect();
    let rest = f.rest.map(|v| {
        if assigned.contains(&v) {
            let raw = supply.fresh_var();
            box_binds.push((v, L3::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), vec![L3::Ref(raw)])));
            raw
        } else {
            v
        }
    });
    let body = convert(*f.body, assigned, supply);
    let body = if box_binds.is_empty() { body } else { L3::Let(box_binds, Box::new(body)) };
    Func { id: f.id, params, rest, body: Box::new(body) }
}
