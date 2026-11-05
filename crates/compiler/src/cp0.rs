//! Pass 3 (`L2 -> L2`): Chez-style `cp0` source optimizer.
//!
//! Performs in a single pass:
//! - Copy and constant propagation for unassigned variables
//! - Known prelude closure call lowering to direct [`Intrinsic`] / [`Request`] operations
//! - Pure intrinsic constant folding
//! - Direct beta-reduction (`((lambda (x ...) body) a ...)`)
//! - Single-use and small local procedure inlining
//! - Conditional (`if`) and negation (`not`) simplification
//! - Dead `Let` / `Fix` binding elimination and effect sequencing (`Seq`)

use std::collections::{HashMap, HashSet};

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Mutation, Value};
use ragwort_vm::objects::{BytecodeFields, Closure, ClosureFields};
use ragwort_vm::{Fuel, Intrinsic, Op};

use crate::ir::{L2, Supply};
use crate::letrec::collect_usage;
use crate::{Func, Prim, Var};

/// Maximum AST node count of a multi-use local lambda eligible for inlining.
const MAX_INLINE_SIZE: usize = 10;
/// Maximum number of rest-argument elements to expand inline into a `cons` chain.
const MAX_REST_INLINE: usize = 16;

pub(crate) fn optimize<'gc>(mc: &Mutation<'gc>, expr: L2<'gc>, supply: Supply) -> (L2<'gc>, Supply) {
    let mut used = HashSet::new();
    let mut assigned = HashSet::new();
    collect_usage(&expr, &mut used, &mut assigned);

    let mut pass = Cp0 {
        mc,
        supply,
        used,
        assigned,
        subst: HashMap::new(),
        truthy_vars: HashSet::new(),
        pred_facts: HashMap::new(),
        single_use: HashMap::new(),
        small_funcs: HashMap::new(),
        inline_depth: 0,
    };
    let out = pass.expr(expr);
    (out, pass.supply)
}

#[derive(Clone, Copy)]
enum Subst<'gc> {
    Quote(Value<'gc>),
    Var(Var),
}

struct Cp0<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    supply: Supply,
    used: HashSet<Var>,
    assigned: HashSet<Var>,
    subst: HashMap<Var, Subst<'gc>>,
    /// Unassigned variables known to hold a non-`#f` value in the current dominating branch.
    truthy_vars: HashSet<Var>,
    /// Dominating type-predicate facts `(pred, var) -> bool` for unassigned variables.
    pred_facts: HashMap<(Intrinsic, Var), bool>,
    /// Unassigned `Let`-bound lambdas referenced exactly once, in call position.
    single_use: HashMap<Var, Func<L2<'gc>>>,
    /// Small unassigned `Let`-bound lambdas with no nested lambdas, eligible for cloning at call sites.
    small_funcs: HashMap<Var, Func<L2<'gc>>>,
    inline_depth: usize,
}

impl<'gc> Cp0<'_, 'gc> {
    fn expr(&mut self, expr: L2<'gc>) -> L2<'gc> {
        match expr {
            L2::Quote(v) => L2::Quote(v),
            L2::Ref(v) => match self.subst.get(&v).copied() {
                Some(Subst::Quote(val)) => L2::Quote(val),
                Some(Subst::Var(u)) => L2::Ref(u),
                None => L2::Ref(v),
            },
            L2::If(test, then, other) => {
                let test = self.expr(*test);
                self.simplify_if(test, *then, *other)
            }
            L2::Seq(a, b) => {
                let a = self.expr(*a);
                let b = self.expr(*b);
                L2::seq(a, b)
            }
            L2::Let(binds, body) => self.opt_let(binds, *body),
            L2::Fix(binds, body) => self.opt_fix(binds, *body),
            L2::Set(v, value) => {
                let value = self.expr(*value);
                let target = match self.subst.get(&v).copied() {
                    Some(Subst::Var(u)) => u,
                    _ => v,
                };
                if !self.used.contains(&target) {
                    return L2::seq(value, L2::Quote(Value::VOID));
                }
                L2::Set(target, Box::new(value))
            }
            L2::App(f, args) => {
                let f = self.expr(*f);
                let args: Vec<L2<'gc>> = args.into_iter().map(|a| self.expr(a)).collect();
                self.opt_app(f, args)
            }
            L2::Lambda(f) => L2::Lambda(self.opt_func(f)),
            L2::Intrinsic(prim, args) => {
                let args: Vec<L2<'gc>> = args.into_iter().map(|a| self.expr(a)).collect();
                self.opt_intrinsic(prim, args)
            }
            L2::ApplyIntrinsic(prim, args) => {
                let args: Vec<L2<'gc>> = args.into_iter().map(|a| self.expr(a)).collect();
                L2::ApplyIntrinsic(prim, args)
            }
        }
    }

    fn opt_func(&mut self, f: Func<L2<'gc>>) -> Func<L2<'gc>> {
        Func { id: f.id, params: f.params, rest: f.rest, body: Box::new(self.expr(*f.body)) }
    }

    fn simplify_if(&mut self, test: L2<'gc>, then: L2<'gc>, other: L2<'gc>) -> L2<'gc> {
        match test {
            // (if #f then other) -> other; (if <non-#f-const> then other) -> then
            L2::Quote(v) => {
                if v == Value::FALSE {
                    self.expr(other)
                } else {
                    self.expr(then)
                }
            }
            // Known truthy variable from an enclosing dominating `if` test.
            L2::Ref(v) if self.truthy_vars.contains(&v) => self.expr(then),
            // Any expression guaranteed never to evaluate to `#f`.
            test if test.is_always_truthy() => {
                let then = self.expr(then);
                L2::seq(test, then)
            }
            // (if (not x) then other) -> (if x other then)
            L2::Intrinsic(Prim::Intrinsic(Intrinsic::Not), mut args) if args.len() == 1 => {
                let inner = args.pop().expect("checked single argument");
                self.simplify_if(inner, other, then)
            }
            // (if (seq a b) then other) -> (seq a (if b then other))
            L2::Seq(a, b) => {
                let branch = self.simplify_if(*b, then, other);
                L2::seq(*a, branch)
            }
            // Short-circuit `and` in test position: (if (if a b #f) then other) -> (if a (if b then other) other)
            // when `other` is a constant or variable reference (no code duplication).
            L2::If(a, b, c) if matches!(*c, L2::Quote(Value::FALSE)) && matches!(other, L2::Quote(_) | L2::Ref(_)) => {
                let inner_if = L2::If(b, Box::new(then), Box::new(other.clone()));
                self.simplify_if(*a, inner_if, other)
            }
            // Dominating variable test: in `then`, `v` is truthy; in `other`, `v` is `#f`.
            L2::Ref(v) if !self.assigned.contains(&v) => {
                let newly_truthy = self.truthy_vars.insert(v);
                let then = self.expr(then);
                if newly_truthy {
                    self.truthy_vars.remove(&v);
                }

                let prev_subst = self.subst.insert(v, Subst::Quote(Value::FALSE));
                let other = self.expr(other);
                match prev_subst {
                    Some(prev) => _ = self.subst.insert(v, prev),
                    None => _ = self.subst.remove(&v),
                }

                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    L2::seq(L2::Ref(v), then)
                } else {
                    L2::If(Box::new(L2::Ref(v)), Box::new(then), Box::new(other))
                }
            }
            // Dominating type-predicate test: `(if (pair? v) then other)` records `(IsPair, v)` in branches.
            L2::Intrinsic(Prim::Intrinsic(pred), ref args)
                if args.len() == 1
                    && pred.is_type_predicate()
                    && matches!(args[0], L2::Ref(v) if !self.assigned.contains(&v)) =>
            {
                let L2::Ref(v) = args[0] else { unreachable!() };
                let prev_fact = self.pred_facts.insert((pred, v), true);
                let newly_truthy = (pred != Intrinsic::IsBoolean) && self.truthy_vars.insert(v);
                let prev_subst = (pred == Intrinsic::IsNull).then(|| self.subst.insert(v, Subst::Quote(Value::NIL))).flatten();
                let then = self.expr(then);
                if newly_truthy {
                    self.truthy_vars.remove(&v);
                }
                if pred == Intrinsic::IsNull {
                    match prev_subst {
                        Some(prev) => _ = self.subst.insert(v, prev),
                        None => _ = self.subst.remove(&v),
                    }
                }
                self.pred_facts.insert((pred, v), false);
                let other = self.expr(other);
                match prev_fact {
                    Some(prev) => _ = self.pred_facts.insert((pred, v), prev),
                    None => _ = self.pred_facts.remove(&(pred, v)),
                }

                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    L2::seq(test, then)
                } else {
                    L2::If(Box::new(test), Box::new(then), Box::new(other))
                }
            }
            test => {
                let then = self.expr(then);
                let other = self.expr(other);
                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    L2::seq(test, then)
                } else {
                    L2::If(Box::new(test), Box::new(then), Box::new(other))
                }
            }
        }
    }

    fn opt_let(&mut self, binds: Vec<(Var, L2<'gc>)>, body: L2<'gc>) -> L2<'gc> {
        let mut kept: Vec<(Var, L2<'gc>)> = Vec::with_capacity(binds.len());
        let mut counts: Option<HashMap<Var, UseStats>> = None;

        for (v, init) in binds {
            let init = self.expr(init);
            if !self.assigned.contains(&v) {
                match init {
                    L2::Quote(val) => {
                        self.subst.insert(v, Subst::Quote(val));
                        continue;
                    }
                    L2::Ref(u) if !self.assigned.contains(&u) => {
                        self.subst.insert(v, Subst::Var(u));
                        continue;
                    }
                    L2::Lambda(func) => {
                        let map = counts.get_or_insert_with(|| count_uses(&body));
                        let stats = map.get(&v).copied().unwrap_or_default();
                        if stats.total == 0 {
                            continue;
                        }
                        if stats.total == 1 && stats.valid_calls == 1 && func_takes(&func, stats.call_arity) {
                            self.single_use.insert(v, func);
                            continue;
                        }
                        if self.inline_depth < 4
                            && is_small_inlinable(&func, &self.assigned)
                        {
                            self.small_funcs.insert(v, func.clone());
                        }
                        kept.push((v, L2::Lambda(func)));
                        continue;
                    }
                    _ => {}
                }
            }
            kept.push((v, init));
        }

        let body = self.expr(body);

        for &(v, _) in &kept {
            self.small_funcs.remove(&v);
        }

        Self::finish_let(kept, body)
    }

    fn finish_let(kept: Vec<(Var, L2<'gc>)>, body: L2<'gc>) -> L2<'gc> {
        crate::letrec::simplify_let(kept, body)
    }

    fn opt_fix(&mut self, binds: Vec<(Var, Func<L2<'gc>>)>, body: L2<'gc>) -> L2<'gc> {
        let binds: Vec<(Var, Func<L2<'gc>>)> = binds.into_iter().map(|(v, f)| (v, self.opt_func(f))).collect();
        let body = self.expr(body);
        Self::finish_fix(binds, body)
    }

    fn finish_fix(binds: Vec<(Var, Func<L2<'gc>>)>, body: L2<'gc>) -> L2<'gc> {
        let mut used = HashSet::new();
        let mut assigned = HashSet::new();
        collect_usage(&body, &mut used, &mut assigned);
        if binds.iter().any(|(v, _)| used.contains(v) || assigned.contains(v)) {
            L2::Fix(binds, Box::new(body))
        } else {
            body
        }
    }

    fn opt_app(&mut self, f: L2<'gc>, args: Vec<L2<'gc>>) -> L2<'gc> {
        // 0. Float `Seq`, `Let`, and `Fix` out of operator position:
        //    `((fix ((loop ...)) loop) 10 0)` -> `(fix ((loop ...)) (loop 10 0))`
        match f {
            L2::Seq(a, b) => {
                let call = self.opt_app(*b, args);
                return L2::seq(*a, call);
            }
            L2::Let(binds, body) => {
                let call = self.opt_app(*body, args);
                return Self::finish_let(binds, call);
            }
            L2::Fix(binds, body) => {
                let call = self.opt_app(*body, args);
                return Self::finish_fix(binds, call);
            }
            _ => {}
        }

        // 1. Direct beta-reduction: ((lambda (x ...) body) arg ...)
        if let L2::Lambda(ref func) = f
            && func_takes(func, args.len())
        {
            let L2::Lambda(func) = f else { unreachable!() };
            return self.beta_reduce(func, args);
        }

        // 2. Single-use or small local lambda inlining: (f arg ...)
        if let L2::Ref(v) = f {
            if let Some(func) = self.single_use.remove(&v) {
                if func_takes(&func, args.len()) {
                    return self.beta_reduce(func, args);
                }
                return L2::App(Box::new(L2::Lambda(func)), args);
            }
            if self.inline_depth < 4
                && let Some(func) = self.small_funcs.get(&v).cloned()
                && func_takes(&func, args.len())
            {
                let renamed = alpha_rename(&func, &mut self.supply);
                self.inline_depth += 1;
                let out = self.beta_reduce(renamed, args);
                self.inline_depth -= 1;
                return out;
            }
        }

        // 3. Known prelude/imported closure call lowering: (Quote(<Closure>) arg ...)
        if let L2::Quote(val) = f
            && let Some(lowered) = self.lower_closure_call(val, &args)
        {
            return lowered;
        }

        L2::App(Box::new(f), args)
    }

    fn beta_reduce(&mut self, func: Func<L2<'gc>>, mut args: Vec<L2<'gc>>) -> L2<'gc> {
        match func.rest {
            None => {
                let binds: Vec<(Var, L2<'gc>)> = func.params.into_iter().zip(args).collect();
                self.opt_let(binds, *func.body)
            }
            Some(rest_var) => {
                let fixed_len = func.params.len();
                let rest_args = args.split_off(fixed_len);
                let rest_list = rest_args.into_iter().rfold(L2::Quote(Value::NIL), |acc, item| {
                    self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, acc])
                });
                let mut binds: Vec<(Var, L2<'gc>)> = func.params.into_iter().zip(args).collect();
                binds.push((rest_var, rest_list));
                self.opt_let(binds, *func.body)
            }
        }
    }

    /// Inspects a constant 0-capture [`Closure`] (such as an imported prelude procedure) and
    /// lowers calls with matching arity directly to [`L2::Intrinsic`] or inline expressions.
    fn lower_closure_call(&mut self, val: Value<'gc>, args: &[L2<'gc>]) -> Option<L2<'gc>> {
        let mc = self.mc;
        let closure = val.downcast::<Closure>(mc)?;
        if !closure.items(mc).is_empty() {
            return None;
        }
        let code = closure.code(mc)?;
        let ops = code.ops(mc)?;
        let arity = code.arity(mc);

        if arity >= 0 {
            if args.len() != arity as usize {
                return None;
            }
            let (base, rest) = strip_arg_moves(ops, args.len())?;
            match *rest {
                [Op::TailCallIntrinsic { base: b, args: n, intrinsic }]
                    if b == base && usize::from(n) == args.len() =>
                {
                    return Some(self.opt_intrinsic(Prim::Intrinsic(intrinsic), args.to_vec()));
                }
                [Op::TailCallRequest { base: b, args: n, request }]
                    if b == base && usize::from(n) == args.len() =>
                {
                    return Some(L2::Intrinsic(Prim::Request(request), args.to_vec()));
                }
                [Op::LoadConst { dst: d1, index }, Op::Return { src: d2 }] if d1 == d2 => {
                    let cs = Constants::of(code.constants(mc))?;
                    let c = cs.get(mc, index)?;
                    return Some(args.iter().cloned().rfold(L2::Quote(c), |acc, e| L2::seq(e, acc)));
                }
                _ => return None,
            }
        }

        let req = (-arity - 1) as usize;
        if args.len() < req {
            return None;
        }
        let (base, rest) = strip_arg_moves(ops, req + 1)?;
        match *rest {
            [Op::ApplyIntrinsic { base: b, args: m, intrinsic }, ..]
                if b == base
                    && rest.len() <= 3
                    && usize::from(m) == req + 1
                    && intrinsic.arity().is_none_or(|a| usize::from(a) == args.len()) =>
            {
                Some(self.opt_intrinsic(Prim::Intrinsic(intrinsic), args.to_vec()))
            }
            [Op::TailApplyRequest { base: b, args: m, request }]
                if b == base && usize::from(m) == req + 1 && request.takes(args.len()) =>
            {
                Some(L2::Intrinsic(Prim::Request(request), args.to_vec()))
            }
            // `list`: (%lambda xs xs)
            [Op::Return { src: 1 }] if req == 0 && args.len() <= MAX_REST_INLINE => {
                let list = args.iter().cloned().rfold(L2::Quote(Value::NIL), |acc, item| {
                    self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, acc])
                });
                Some(list)
            }
            // `void`: (%lambda args (%intrinsic void))
            [Op::TailCallIntrinsic { base: b, args: 0, intrinsic: Intrinsic::Void }] if req == 0 && b >= 1 => {
                Some(args.iter().cloned().rfold(L2::Quote(Value::VOID), |acc, e| L2::seq(e, acc)))
            }
            [Op::LoadConst { dst: d1, index }, Op::Return { src: d2 }] if req == 0 && d1 == d2 => {
                let cs = Constants::of(code.constants(mc))?;
                let c = cs.get(mc, index)?;
                Some(args.iter().cloned().rfold(L2::Quote(c), |acc, e| L2::seq(e, acc)))
            }
            _ => None,
        }
    }

    fn opt_intrinsic(&mut self, prim: Prim, mut args: Vec<L2<'gc>>) -> L2<'gc> {
        let Prim::Intrinsic(intrinsic) = prim else {
            return L2::Intrinsic(prim, args);
        };

        // Float leading `Seq` out of single-argument intrinsics: `(car (seq e x)) -> (seq e (car x))`
        if args.len() == 1 && matches!(args[0], L2::Seq(_, _)) {
            let Some(L2::Seq(prefix, inner)) = args.pop() else { unreachable!() };
            let out = self.opt_intrinsic(prim, vec![*inner]);
            return L2::seq(*prefix, out);
        }

        // `(void e ...)` evaluates `e ...` for effect and returns `#<void>`.
        if intrinsic == Intrinsic::Void {
            return args.into_iter().rfold(L2::Quote(Value::VOID), |acc, e| L2::seq(e, acc));
        }

        // 1. Compile-time constant folding via `Intrinsic::is_pure_foldable`.
        if intrinsic.is_pure_foldable() && args.iter().all(|a| matches!(a, L2::Quote(_))) {
            let values: Vec<Value<'gc>> = args
                .iter()
                .map(|a| match *a {
                    L2::Quote(v) => v,
                    _ => unreachable!(),
                })
                .collect();
            let mut fuel = Fuel { run: u64::MAX, rest: u64::MAX };
            if let Ok(val) = intrinsic.run(self.mc, &values, &mut fuel) {
                return L2::Quote(val);
            }
        }

        // 2. Store-to-load forwarding for `car`..`cddddr` on `(cons head tail)` while preserving
        //    left-to-right `(head, tail)` evaluation order.
        if let Some((is_car, rest)) = intrinsic.cxr_step()
            && args.len() == 1
            && matches!(args[0], L2::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), ref c) if c.len() == 2)
        {
            let Some(L2::Intrinsic(_, mut cons_args)) = args.pop() else { unreachable!() };
            let tail = cons_args.pop().expect("checked 2 cons args");
            let head = cons_args.pop().expect("checked 2 cons args");
            if !is_car {
                let next = match rest {
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec![tail]),
                    None => tail,
                };
                return L2::seq(head, next);
            }
            if tail.is_pure() {
                return match rest {
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec![head]),
                    None => head,
                };
            }
            let tmp = self.supply.fresh_var();
            let projected = match rest {
                Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec![L2::Ref(tmp)]),
                None => L2::Ref(tmp),
            };
            return L2::Let(vec![(tmp, head)], Box::new(L2::seq(tail, projected)));
        }

        // 3. Store-to-load forwarding for `(unbox (box x)) -> x`.
        if intrinsic == Intrinsic::Unbox
            && args.len() == 1
            && matches!(args[0], L2::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), ref b) if b.len() == 1)
        {
            let Some(L2::Intrinsic(_, mut box_args)) = args.pop() else { unreachable!() };
            return box_args.pop().expect("checked 1 box arg");
        }

        // 4. `not` on truthy expressions or known truthy variables: `(not <truthy>) -> (seq <truthy> #f)`.
        if intrinsic == Intrinsic::Not && args.len() == 1 {
            if let L2::Ref(v) = args[0]
                && self.truthy_vars.contains(&v)
            {
                return L2::Quote(Value::FALSE);
            }
            if args[0].is_always_truthy() {
                let inner = args.pop().expect("checked 1 not arg");
                return L2::seq(inner, L2::Quote(Value::FALSE));
            }
        }

        // 5. Type predicates on dominating variables or freshly constructed values.
        if intrinsic.is_type_predicate() && args.len() == 1 {
            if let L2::Ref(v) = args[0] {
                if let Some(&known) = self.pred_facts.get(&(intrinsic, v)) {
                    return L2::Quote(if known { Value::TRUE } else { Value::FALSE });
                }
                if (intrinsic == Intrinsic::IsProcedure
                    && self.pred_facts.get(&(Intrinsic::IsContinuation, v)) == Some(&true))
                    || (intrinsic == Intrinsic::IsList
                        && self.pred_facts.get(&(Intrinsic::IsNull, v)) == Some(&true))
                {
                    return L2::Quote(Value::TRUE);
                }
                if (intrinsic == Intrinsic::IsContinuation
                    && self.pred_facts.get(&(Intrinsic::IsProcedure, v)) == Some(&false))
                    || (intrinsic == Intrinsic::IsNull
                        && self.pred_facts.get(&(Intrinsic::IsList, v)) == Some(&false))
                {
                    return L2::Quote(Value::FALSE);
                }
                if self.pred_facts.iter().any(|(&(other_pred, u), &val)| {
                    u == v && val && intrinsic.is_disjoint_predicate(other_pred)
                }) {
                    return L2::Quote(Value::FALSE);
                }
            }
            match &args[0] {
                L2::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), c) if c.len() == 2 => {
                    if intrinsic != Intrinsic::IsList {
                        let Some(L2::Intrinsic(_, cons_args)) = args.pop() else { unreachable!() };
                        let res = L2::Quote(if intrinsic == Intrinsic::IsPair { Value::TRUE } else { Value::FALSE });
                        return cons_args.into_iter().rfold(res, |acc, e| L2::seq(e, acc));
                    }
                }
                L2::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), b) if b.len() == 1 => {
                    let Some(L2::Intrinsic(_, box_args)) = args.pop() else { unreachable!() };
                    let res = L2::Quote(if intrinsic == Intrinsic::IsBox { Value::TRUE } else { Value::FALSE });
                    return box_args.into_iter().rfold(res, |acc, e| L2::seq(e, acc));
                }
                L2::Lambda(_) => {
                    return L2::Quote(if intrinsic == Intrinsic::IsProcedure { Value::TRUE } else { Value::FALSE });
                }
                _ => {}
            }
        }

        // 6. Equality simplifications (`eq?`, `eqv?`, `equal?`):
        //    - Reflexive `(eq? x x) -> #t`
        //    - `(eq? x '()) -> (null? x)` (1-arg intrinsic, no `'()` constant load)
        //    - `(eq? x #f)  -> (not x)`   (1-arg intrinsic, folds away in `if`)
        if matches!(intrinsic, Intrinsic::Eq | Intrinsic::Eqv | Intrinsic::Equal) && args.len() == 2 {
            if let [L2::Ref(a), L2::Ref(b)] = args.as_slice()
                && a == b
                && !self.assigned.contains(a)
            {
                return L2::Quote(Value::TRUE);
            }
            if matches!(args[1], L2::Quote(Value::NIL)) {
                let x = args.swap_remove(0);
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec![x]);
            }
            if matches!(args[0], L2::Quote(Value::NIL)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec![x]);
            }
            if matches!(args[1], L2::Quote(Value::FALSE)) {
                let x = args.swap_remove(0);
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec![x]);
            }
            if matches!(args[0], L2::Quote(Value::FALSE)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec![x]);
            }
        }

        L2::Intrinsic(prim, args)
    }
}

/// Matches either a direct parameter slice at `base = 1` or `k` leading `Move`s copying
/// parameters `1..=k` to `base..base + k`.
fn strip_arg_moves(ops: &[Op], k: usize) -> Option<(u8, &[Op])> {
    if k == 0 {
        return Some((1, ops));
    }
    if let Some(Op::Move { dst: base, src: 1 }) = ops.first().copied()
        && ops.len() >= k
    {
        let all_match = (0..k).all(|i| {
            matches!(ops[i], Op::Move { dst, src } if dst == base.wrapping_add(i as u8) && src == 1 + i as u8)
        });
        if all_match {
            return Some((base, &ops[k..]));
        }
    }
    Some((1, ops))
}

fn func_takes<E>(func: &Func<E>, argc: usize) -> bool {
    match func.rest {
        None => argc == func.params.len(),
        Some(_) => argc >= func.params.len() && argc - func.params.len() <= MAX_REST_INLINE,
    }
}

#[derive(Clone, Copy, Default)]
struct UseStats {
    total: usize,
    valid_calls: usize,
    call_arity: usize,
}

fn count_uses<'gc>(expr: &L2<'gc>) -> HashMap<Var, UseStats> {
    let mut map = HashMap::new();
    visit_uses(expr, &mut map);
    map
}

fn visit_uses<'gc>(expr: &L2<'gc>, map: &mut HashMap<Var, UseStats>) {
    match expr {
        L2::Quote(_) => {}
        L2::Ref(v) => {
            map.entry(*v).or_default().total += 1;
        }
        L2::If(test, then, other) => {
            visit_uses(test, map);
            visit_uses(then, map);
            visit_uses(other, map);
        }
        L2::Seq(a, b) => {
            visit_uses(a, map);
            visit_uses(b, map);
        }
        L2::Let(binds, body) => {
            for (_, init) in binds {
                visit_uses(init, map);
            }
            visit_uses(body, map);
        }
        L2::Fix(binds, body) => {
            for (_, f) in binds {
                visit_uses(&f.body, map);
            }
            visit_uses(body, map);
        }
        L2::Set(v, value) => {
            map.entry(*v).or_default().total += 2;
            visit_uses(value, map);
        }
        L2::App(f, args) => {
            if let L2::Ref(v) = **f {
                let entry = map.entry(v).or_default();
                entry.total += 1;
                entry.valid_calls += 1;
                entry.call_arity = args.len();
            } else {
                visit_uses(f, map);
            }
            for arg in args {
                visit_uses(arg, map);
            }
        }
        L2::Lambda(f) => visit_uses(&f.body, map),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => {
            for arg in args {
                visit_uses(arg, map);
            }
        }
    }
}

fn is_small_inlinable<'gc>(func: &Func<L2<'gc>>, assigned: &HashSet<Var>) -> bool {
    if func.params.iter().chain(&func.rest).any(|v| assigned.contains(v)) {
        return false;
    }
    let mut size = 0;
    check_small(&func.body, assigned, &mut size)
}

fn check_small<'gc>(expr: &L2<'gc>, assigned: &HashSet<Var>, size: &mut usize) -> bool {
    *size += 1;
    if *size > MAX_INLINE_SIZE {
        return false;
    }
    match expr {
        L2::Quote(_) => true,
        L2::Ref(v) => !assigned.contains(v),
        L2::If(a, b, c) => check_small(a, assigned, size) && check_small(b, assigned, size) && check_small(c, assigned, size),
        L2::Seq(a, b) => check_small(a, assigned, size) && check_small(b, assigned, size),
        L2::Let(binds, body) => {
            binds.iter().all(|(v, init)| !assigned.contains(v) && check_small(init, assigned, size))
                && check_small(body, assigned, size)
        }
        L2::Fix(_, _) | L2::Set(_, _) | L2::Lambda(_) => false,
        L2::App(f, args) => check_small(f, assigned, size) && args.iter().all(|a| check_small(a, assigned, size)),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => args.iter().all(|a| check_small(a, assigned, size)),
    }
}

fn alpha_rename<'gc>(func: &Func<L2<'gc>>, supply: &mut Supply) -> Func<L2<'gc>> {
    let mut map = HashMap::new();
    let params = func
        .params
        .iter()
        .map(|&v| {
            let fresh = supply.fresh_var();
            map.insert(v, fresh);
            fresh
        })
        .collect();
    let rest = func.rest.map(|v| {
        let fresh = supply.fresh_var();
        map.insert(v, fresh);
        fresh
    });
    let body = rename_expr(&func.body, &mut map, supply);
    Func { id: supply.fresh_lambda(), params, rest, body: Box::new(body) }
}

fn rename_expr<'gc>(expr: &L2<'gc>, map: &mut HashMap<Var, Var>, supply: &mut Supply) -> L2<'gc> {
    match expr {
        L2::Quote(v) => L2::Quote(*v),
        L2::Ref(v) => L2::Ref(map.get(v).copied().unwrap_or(*v)),
        L2::If(a, b, c) => L2::If(
            Box::new(rename_expr(a, map, supply)),
            Box::new(rename_expr(b, map, supply)),
            Box::new(rename_expr(c, map, supply)),
        ),
        L2::Seq(a, b) => L2::Seq(Box::new(rename_expr(a, map, supply)), Box::new(rename_expr(b, map, supply))),
        L2::Let(binds, body) => {
            let mut new_binds = Vec::with_capacity(binds.len());
            for &(v, ref init) in binds {
                new_binds.push((v, rename_expr(init, map, supply)));
            }
            let mut renamed_binds = Vec::with_capacity(new_binds.len());
            for (v, init) in new_binds {
                let fresh = supply.fresh_var();
                map.insert(v, fresh);
                renamed_binds.push((fresh, init));
            }
            let body = rename_expr(body, map, supply);
            L2::Let(renamed_binds, Box::new(body))
        }
        L2::App(f, args) => L2::App(
            Box::new(rename_expr(f, map, supply)),
            args.iter().map(|a| rename_expr(a, map, supply)).collect(),
        ),
        L2::Intrinsic(prim, args) => L2::Intrinsic(*prim, args.iter().map(|a| rename_expr(a, map, supply)).collect()),
        L2::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(*prim, args.iter().map(|a| rename_expr(a, map, supply)).collect()),
        L2::Fix(_, _) | L2::Set(_, _) | L2::Lambda(_) => unreachable!("small inlinable functions have no Fix/Set/Lambda"),
    }
}
