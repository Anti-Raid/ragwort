//! Pass 3 (`L2 -> L2`): Chez-style `cp0` source optimizer.
//!
//! Performs in a single pass:
//! - Copy and constant propagation for unassigned variables
//! - Pure intrinsic constant folding
//! - Direct beta-reduction (`((lambda (x ...) body) a ...)`)
//! - Single-use and small local procedure inlining, no deeper than source can nest
//! - Conditional (`if`) and negation (`not`) simplification
//! - Dead `Let` binding elimination and effect sequencing (`Seq`)

use crate::hash::{HashMap, HashSet};

/// The most fuel a constant fold may spend.
const FOLD_FUEL: u64 = 1 << 16;

use ragwort_alloc::{Arena, Box, CollectIn, Vec, vec_in};
use ragwort_types::gc::{Mutation, Value};
use ragwort_vm::{Fuel, Intrinsic, Purity};

use crate::ir::{Bind, Bind2, Func, L2, Supply};
use crate::letrec::collect_usage;
use crate::lower::MAX_DEPTH;
use crate::{Prim, Var};

/// Maximum AST node count of a multi-use local lambda eligible for inlining.
const MAX_INLINE_SIZE: usize = 10;
/// Maximum number of rest-argument elements to expand inline into a `cons` chain.
const MAX_REST_INLINE: usize = 16;

pub(crate) fn optimize<'a, 'gc>(mc: &Mutation<'gc>, arena: &'a Arena, expr: L2<'a, 'gc>, supply: Supply) -> (L2<'a, 'gc>, Supply) {
    let mut used = HashSet::default();
    let mut assigned = HashSet::default();
    collect_usage(&expr, &mut used, &mut assigned);

    let mut pass = Cp0 {
        mc,
        arena,
        supply,
        uses: count_uses(&expr),
        used,
        assigned,
        subst: HashMap::default(),
        truthy_vars: HashSet::default(),
        pred_facts: HashMap::default(),
        single_use: HashMap::default(),
        small_funcs: HashMap::default(),
        known_pairs: HashMap::default(),
        wanted: HashSet::default(),
        inline_depth: 0,
        depth: 0,
    };
    let out = crate::letrec::prune(arena, pass.expr(expr));
    (out, pass.supply)
}

/// A branch of an `if`: source still to optimize, or an `if` whose test is already optimized,
/// as splitting `(if (if a b #f) ...)` makes, so `b` isn't optimized twice.
enum Arm<'a, 'gc> {
    Raw(L2<'a, 'gc>),
    If(L2<'a, 'gc>, std::boxed::Box<Arm<'a, 'gc>>, std::boxed::Box<Arm<'a, 'gc>>),
}

impl<'a, 'gc> Arm<'a, 'gc> {
    fn clone_in(&self, arena: &'a Arena) -> Self {
        match self {
            Arm::Raw(e) => Arm::Raw(e.clone_in(arena)),
            Arm::If(test, then, other) => {
                Arm::If(test.clone_in(arena), std::boxed::Box::new(then.clone_in(arena)), std::boxed::Box::new(other.clone_in(arena)))
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Subst<'gc> {
    Quote(Value<'gc>),
    Var(Var),
}

struct Cp0<'m, 'a, 'gc> {
    mc: &'m Mutation<'gc>,
    arena: &'a Arena,
    supply: Supply,
    /// How each variable of the input is used. Variables are unique, so these are also its uses
    /// in the body of the one binding form that binds it.
    uses: HashMap<Var, UseStats>,
    used: HashSet<Var>,
    assigned: HashSet<Var>,
    subst: HashMap<Var, Subst<'gc>>,
    /// Unassigned variables known to hold a non-`#f` value in the current dominating branch.
    truthy_vars: HashSet<Var>,
    /// Dominating type-predicate facts `(pred, var) -> bool` for unassigned variables.
    pred_facts: HashMap<(Intrinsic, Var), bool>,
    /// Unassigned `Let`-bound lambdas referenced exactly once, in call position.
    single_use: HashMap<Var, Func<'a, L2<'a, 'gc>>>,
    /// Small unassigned `Let`-bound lambdas with no nested lambdas, eligible for cloning at call sites.
    small_funcs: HashMap<Var, Func<'a, L2<'a, 'gc>>>,
    /// Unassigned variables bound to `(cons a b)` of constants and unassigned variables. Pairs
    /// are immutable, so the variable's car and cdr are `a` and `b` wherever it's in scope.
    known_pairs: HashMap<Var, [L2<'a, 'gc>; 2]>,
    /// Those of `single_use` whose call they'd have nested too deeply at, so stays a call: they're
    /// bound where they were, after all.
    wanted: HashSet<Var>,
    inline_depth: usize,
    /// How deeply the expression being optimized is nested.
    depth: usize,
}

impl<'a, 'gc> Cp0<'_, 'a, 'gc> {
    fn expr(&mut self, expr: L2<'a, 'gc>) -> L2<'a, 'gc> {
        self.depth += 1;
        let out = self.node(expr);
        self.depth -= 1;
        out
    }

    fn node(&mut self, expr: L2<'a, 'gc>) -> L2<'a, 'gc> {
        match expr {
            L2::Quote(v) => L2::Quote(v),
            L2::Ref(v) => match self.subst.get(&v).copied() {
                Some(Subst::Quote(val)) => L2::Quote(val),
                Some(Subst::Var(u)) => L2::Ref(u),
                None => L2::Ref(v),
            },
            L2::If(test, then, other) => {
                let test = self.expr(Box::into_inner(test));
                self.simplify_if(test, Arm::Raw(Box::into_inner(then)), Arm::Raw(Box::into_inner(other)))
            }
            L2::Seq(a, b) => {
                let a = self.expr(Box::into_inner(a));
                let b = self.expr(Box::into_inner(b));
                self.seq(a, b)
            }
            L2::Let(binds, body) => self.opt_let(binds, false, Box::into_inner(body)),
            L2::Set(v, value) => {
                let value = self.expr(Box::into_inner(value));
                let target = match self.subst.get(&v).copied() {
                    Some(Subst::Var(u)) => u,
                    _ => v,
                };
                if !self.used.contains(&target) {
                    return self.seq(value, L2::Quote(Value::VOID));
                }
                L2::Set(target, self.arena.boxed(value))
            }
            L2::App(f, args) => self.app(Box::into_inner(f), args),
            L2::Lambda(f) => L2::Lambda(self.opt_func(f)),
            L2::Intrinsic(prim, args) => {
                let arena = self.arena;
                let args: Vec<'a, L2<'a, 'gc>> = args.into_iter().map(|a| self.expr(a)).collect_in(arena);
                self.opt_intrinsic(prim, args)
            }
            L2::ApplyIntrinsic(prim, args) => {
                let arena = self.arena;
                let args: Vec<'a, L2<'a, 'gc>> = args.into_iter().map(|a| self.expr(a)).collect_in(arena);
                L2::ApplyIntrinsic(prim, args)
            }
        }
    }

    fn opt_func(&mut self, f: Func<'a, L2<'a, 'gc>>) -> Func<'a, L2<'a, 'gc>> {
        Func { id: f.id, params: f.params, optional: f.optional, rest: f.rest, body: self.arena.boxed(self.expr(Box::into_inner(f.body))) }
    }

    fn arm(&mut self, arm: Arm<'a, 'gc>) -> L2<'a, 'gc> {
        match arm {
            Arm::Raw(e) => self.expr(e),
            Arm::If(test, then, other) => self.simplify_if(test, *then, *other),
        }
    }

    /// `(if test then other)` with `test` already optimized.
    fn simplify_if(&mut self, test: L2<'a, 'gc>, then: Arm<'a, 'gc>, other: Arm<'a, 'gc>) -> L2<'a, 'gc> {
        match test {
            // (if #f then other) -> other; (if <non-#f-const> then other) -> then
            L2::Quote(v) => {
                if v == Value::FALSE {
                    self.arm(other)
                } else {
                    self.arm(then)
                }
            }
            // Known truthy variable from an enclosing dominating `if` test.
            L2::Ref(v) if self.truthy_vars.contains(&v) => self.arm(then),
            // Any expression guaranteed never to evaluate to `#f`.
            test if test.is_always_truthy() => {
                let then = self.arm(then);
                self.seq(test, then)
            }
            // (if (not x) then other) -> (if x other then)
            L2::Intrinsic(Prim::Intrinsic(Intrinsic::Not), mut args) if args.len() == 1 => {
                let inner = args.pop().expect("checked single argument");
                self.simplify_if(inner, other, then)
            }
            // (if (seq a b) then other) -> (seq a (if b then other))
            L2::Seq(a, b) => {
                let branch = self.simplify_if(Box::into_inner(b), then, other);
                self.seq(Box::into_inner(a), branch)
            }
            // Short-circuit `and` in test position: (if (if a b #f) then other) -> (if a (if b then other) other)
            // when `other` is a constant or variable reference (no code duplication).
            L2::If(a, b, c) if matches!(*c, L2::Quote(Value::FALSE)) && matches!(other, Arm::Raw(L2::Quote(_) | L2::Ref(_))) => {
                let inner_if = Arm::If(Box::into_inner(b), std::boxed::Box::new(then), std::boxed::Box::new(other.clone_in(self.arena)));
                self.simplify_if(Box::into_inner(a), inner_if, other)
            }
            // Dominating variable test: in `then`, `v` is truthy; in `other`, `v` is `#f`.
            L2::Ref(v) if !self.assigned.contains(&v) => {
                let newly_truthy = self.truthy_vars.insert(v);
                let then = self.arm(then);
                if newly_truthy {
                    self.truthy_vars.remove(&v);
                }

                let prev_subst = self.subst.insert(v, Subst::Quote(Value::FALSE));
                let other = self.arm(other);
                match prev_subst {
                    Some(prev) => _ = self.subst.insert(v, prev),
                    None => _ = self.subst.remove(&v),
                }

                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    self.seq(L2::Ref(v), then)
                } else {
                    L2::If(self.arena.boxed(L2::Ref(v)), self.arena.boxed(then), self.arena.boxed(other))
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
                let then = self.arm(then);
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
                let other = self.arm(other);
                match prev_fact {
                    Some(prev) => _ = self.pred_facts.insert((pred, v), prev),
                    None => _ = self.pred_facts.remove(&(pred, v)),
                }

                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    self.seq(test, then)
                } else {
                    L2::If(self.arena.boxed(test), self.arena.boxed(then), self.arena.boxed(other))
                }
            }
            test => {
                let then = self.arm(then);
                let other = self.arm(other);
                if then == other && matches!(then, L2::Quote(_) | L2::Ref(_)) {
                    self.seq(test, then)
                } else {
                    L2::If(self.arena.boxed(test), self.arena.boxed(then), self.arena.boxed(other))
                }
            }
        }
    }

    /// `(let binds body)`, the inits already optimized if `done`.
    fn opt_let(&mut self, binds: Vec<'a, Bind2<'a, 'gc>>, done: bool, body: L2<'a, 'gc>) -> L2<'a, 'gc> {
        let mut kept: Vec<'a, Bind2<'a, 'gc>> = Vec::with_capacity_in(binds.len(), self.arena);
        // The lambdas called once, with where among `kept` each was.
        let mut parked = std::vec::Vec::new();

        for bind in binds {
            let (v, init) = match bind {
                Bind::Val(v, init) => (v, init),
                Bind::Fix(group) => {
                    let arena = self.arena;
                    kept.push(Bind::Fix(group.into_iter().map(|(v, f)| (v, self.opt_func(f))).collect_in(arena)));
                    continue;
                }
            };
            let unassigned = !self.assigned.contains(&v);
            // A lambda from source that's never used goes; one called once stays source until
            // it's inlined at that call, so its body is optimized once, there. A variable cp0 made
            // itself isn't counted, so it's neither.
            if unassigned
                && !done
                && let L2::Lambda(func) = &init
                && let Some(&stats) = self.uses.get(&v)
            {
                if stats.total == 0 {
                    continue;
                }
                if stats.total == 1 && stats.valid_calls == 1 && func_takes(func, stats.call_arity) {
                    let L2::Lambda(func) = init else { unreachable!() };
                    self.single_use.insert(v, func);
                    parked.push((kept.len(), v));
                    continue;
                }
            }
            let init = if done { init } else { self.expr(init) };
            if unassigned {
                match init {
                    L2::Quote(val) => {
                        self.subst.insert(v, Subst::Quote(val));
                        continue;
                    }
                    L2::Ref(u) if !self.assigned.contains(&u) => {
                        self.subst.insert(v, Subst::Var(u));
                        continue;
                    }
                    L2::Lambda(ref func) if self.inline_depth < 4 && is_small_inlinable(func, &self.assigned) => {
                        self.small_funcs.insert(v, func.clone_in(self.arena));
                    }
                    L2::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), ref parts) if parts.iter().all(|p| self.copyable(p)) => {
                        self.known_pairs.insert(v, [parts[0].clone_in(self.arena), parts[1].clone_in(self.arena)]);
                    }
                    _ => {}
                }
            }
            kept.push(Bind::Val(v, init));
        }

        let body = self.expr(body);
        self.unpark(&mut kept, &parked);

        for bind in &kept {
            for v in bind.vars() {
                self.small_funcs.remove(&v);
            }
        }

        self.finish_let(kept, body)
    }

    /// Binds those of the `parked` lambdas called once that weren't inlined where they were, each
    /// optimized here, where it's no deeper than its `let`.
    fn unpark(&mut self, kept: &mut Vec<'a, Bind2<'a, 'gc>>, parked: &[(usize, Var)]) {
        let mut placed = std::vec::Vec::new();
        // One's code can have the call of another.
        loop {
            let before = placed.len();
            for (i, &(at, v)) in parked.iter().enumerate() {
                if self.wanted.remove(&v) {
                    let func = self.single_use.remove(&v).expect("a lambda called once that wasn't inlined is still parked");
                    placed.push((at, i, Bind::Val(v, L2::Lambda(self.opt_func(func)))));
                }
            }
            if placed.len() == before {
                break;
            }
        }
        placed.sort_unstable_by_key(|&(at, i, _)| (at, i));
        for (at, _, bind) in placed.into_iter().rev() {
            kept.insert(at, bind);
        }
    }

    /// `first` evaluated for what it does, then `second`.
    fn seq(&mut self, first: L2<'a, 'gc>, second: L2<'a, 'gc>) -> L2<'a, 'gc> {
        self.seq_all([first], second)
    }

    /// `firsts` evaluated in order for what they do, then `second`, dropping their pure parts. Two
    /// or more effects left are one `Let`, of variables unused, so however many there are they
    /// nest no deeper.
    fn seq_all(&mut self, firsts: impl IntoIterator<Item = L2<'a, 'gc>, IntoIter: DoubleEndedIterator>, second: L2<'a, 'gc>) -> L2<'a, 'gc> {
        let mut todo: std::vec::Vec<L2<'a, 'gc>> = firsts.into_iter().rev().collect();
        let mut effects = std::vec::Vec::new();
        while let Some(e) = todo.pop() {
            if e.is_pure() {
                continue;
            }
            match e {
                L2::Seq(a, b) => todo.extend([Box::into_inner(b), Box::into_inner(a)]),
                L2::Intrinsic(Prim::Intrinsic(i), args) if i.is_discardable() => todo.extend(args.into_iter().rev()),
                L2::Intrinsic(Prim::Read(r), args) if r.is_discardable() => todo.extend(args.into_iter().rev()),
                L2::Intrinsic(Prim::Host(h), args) if h.purity == Purity::Discardable => todo.extend(args.into_iter().rev()),
                L2::If(test, then, other) if then.is_pure() && other.is_pure() => todo.push(Box::into_inner(test)),
                e => effects.push(e),
            }
        }
        if effects.len() < 2 {
            return match effects.pop() {
                Some(e) => L2::Seq(self.arena.boxed(e), self.arena.boxed(second)),
                None => second,
            };
        }
        let arena = self.arena;
        let binds = effects.into_iter().map(|e| Bind::Val(self.supply.fresh_var(), e)).collect_in(arena);
        L2::Let(binds, arena.boxed(second))
    }

    /// Whether `e` can be copied to wherever its value's used: a constant, or a variable no code
    /// assigns.
    fn copyable(&self, e: &L2<'a, 'gc>) -> bool {
        match e {
            L2::Quote(_) => true,
            L2::Ref(u) => !self.assigned.contains(u),
            _ => false,
        }
    }

    /// Unused bindings are left to [`prune`](crate::letrec::prune), which finds them all in one walk.
    fn finish_let(&self, kept: Vec<'a, Bind2<'a, 'gc>>, body: L2<'a, 'gc>) -> L2<'a, 'gc> {
        if kept.is_empty() { body } else { L2::Let(kept, self.arena.boxed(body)) }
    }

    /// A call from source. Binding forms around the operator float out first, so a lambda they
    /// end in is applied directly: `((let (...) f) x) -> (let (...) (f x))`. The bindings and
    /// effects still come before `f` and `x`, and every variable is unique, so nothing is
    /// captured. A lambda applied directly or called once is inlined with its body and
    /// arguments still source, so each is optimized once.
    fn app(&mut self, f: L2<'a, 'gc>, args: Vec<'a, L2<'a, 'gc>>) -> L2<'a, 'gc> {
        match f {
            L2::Seq(a, b) => return self.expr(L2::Seq(a, self.arena.boxed(L2::App(b, args)))),
            L2::Let(binds, body) => return self.expr(L2::Let(binds, self.arena.boxed(L2::App(body, args)))),
            L2::Lambda(func) if func_takes(&func, args.len()) => return self.beta_reduce(func, args, false),
            _ => {}
        }
        let f = self.expr(f);
        // A lambda called once is inlined unless its body would then nest deeper than source can,
        // as later passes recurse through it.
        if let L2::Ref(v) = f
            && let Some(func) = self.single_use.get(&v)
            && self.depth + depth(&func.body) > MAX_DEPTH
        {
            self.wanted.insert(v);
        } else if let L2::Ref(v) = f
            && let Some(func) = self.single_use.remove(&v)
        {
            if func_takes(&func, args.len()) {
                return self.beta_reduce(func, args, false);
            }
            let func = self.opt_func(func);
            let arena = self.arena;
            let args = args.into_iter().map(|a| self.expr(a)).collect_in(arena);
            return L2::App(self.arena.boxed(L2::Lambda(func)), args);
        }
        let arena = self.arena;
        let args = args.into_iter().map(|a| self.expr(a)).collect_in(arena);
        self.opt_app(f, args)
    }

    /// A call whose operator and arguments are already optimized.
    fn opt_app(&mut self, f: L2<'a, 'gc>, args: Vec<'a, L2<'a, 'gc>>) -> L2<'a, 'gc> {
        // Binding forms an inlined operator ended up in float out, as in `app`.
        match f {
            L2::Seq(a, b) => {
                let call = self.opt_app(Box::into_inner(b), args);
                return self.seq(Box::into_inner(a), call);
            }
            L2::Let(binds, body) => {
                let call = self.opt_app(Box::into_inner(body), args);
                return self.finish_let(binds, call);
            }
            _ => {}
        }

        // An optimized lambda applied directly binds its parameters around its body as it is,
        // rather than optimizing the body again.
        if let L2::Lambda(func) = f {
            if !func_takes(&func, args.len()) {
                return L2::App(self.arena.boxed(L2::Lambda(func)), args);
            }
            let (binds, body) = self.bind_params(func, args, true);
            return self.finish_let(binds, body);
        }

        // A small local lambda is copied in at each call, with its parameters renamed, and the
        // copy optimized again with the arguments it's given.
        if let L2::Ref(v) = f
            && self.inline_depth < 4
            && let Some(func) = self.small_funcs.get(&v).map(|f| f.clone_in(self.arena))
            && func_takes(&func, args.len())
        {
            let renamed = alpha_rename(self.arena, &func, &mut self.supply);
            self.inline_depth += 1;
            let out = self.beta_reduce(renamed, args, true);
            self.inline_depth -= 1;
            return out;
        }

        L2::App(self.arena.boxed(f), args)
    }

    /// `func`'s parameters bound to `args` (already optimized if `done`), and its body.
    fn bind_params(&mut self, func: Func<'a, L2<'a, 'gc>>, mut args: Vec<'a, L2<'a, 'gc>>, done: bool) -> (Vec<'a, Bind2<'a, 'gc>>, L2<'a, 'gc>) {
        // Optional parameters left out are unsupplied, as the VM binds them.
        while args.len() < func.params.len() {
            args.push(L2::Quote(Value::UNSUPPLIED));
        }
        let rest = func.rest.map(|rest| {
            let list = args.split_off(func.params.len()).into_iter().rfold(L2::Quote(Value::NIL), |acc, item| {
                let cons = Prim::Intrinsic(Intrinsic::Cons);
                if done { self.opt_intrinsic(cons, vec_in![self.arena; item, acc]) } else { L2::Intrinsic(cons, vec_in![self.arena; item, acc]) }
            });
            (rest, list)
        });
        let binds = func.params.into_iter().zip(args).chain(rest).map(|(v, e)| Bind::Val(v, e)).collect_in(self.arena);
        (binds, Box::into_inner(func.body))
    }

    /// `func` applied to `args` (already optimized if `done`), inlined: its body is optimized
    /// with its parameters bound.
    fn beta_reduce(&mut self, func: Func<'a, L2<'a, 'gc>>, args: Vec<'a, L2<'a, 'gc>>, done: bool) -> L2<'a, 'gc> {
        let (binds, body) = self.bind_params(func, args, done);
        self.opt_let(binds, done, body)
    }

    fn opt_intrinsic(&mut self, prim: Prim, mut args: Vec<'a, L2<'a, 'gc>>) -> L2<'a, 'gc> {
        let Prim::Intrinsic(intrinsic) = prim else {
            return L2::Intrinsic(prim, args);
        };

        // Float a leading `Seq` out of the first argument, which runs before the rest anyway:
        // `(f (seq e x) y ...) -> (seq e (f x y ...))`, so the rules below see `x` itself.
        if let Some(L2::Seq(_, _)) = args.first() {
            let L2::Seq(prefix, inner) = args.remove(0) else { unreachable!() };
            args.insert(0, Box::into_inner(inner));
            let out = self.opt_intrinsic(prim, args);
            return self.seq(Box::into_inner(prefix), out);
        }
        // Likewise a leading `let`, whose variables are unique, so the rest can't refer to them:
        // `(car (let ((x (f))) (cons x 1))) -> (let ((x (f))) x)`.
        if let Some(L2::Let(_, _)) = args.first() {
            let L2::Let(binds, inner) = args.remove(0) else { unreachable!() };
            args.insert(0, Box::into_inner(inner));
            let out = self.opt_intrinsic(prim, args);
            return self.finish_let(binds, out);
        }

        // `(void e ...)` evaluates `e ...` for effect and returns `#<void>`.
        if intrinsic == Intrinsic::Void {
            return self.seq_all(args, L2::Quote(Value::VOID));
        }

        // 1. Compile-time constant folding via `Intrinsic::is_pure_foldable`.
        if intrinsic.is_pure_foldable() && args.iter().all(|a| matches!(a, L2::Quote(_))) {
            let values: std::vec::Vec<Value<'gc>> = args
                .iter()
                .map(|a| match *a {
                    L2::Quote(v) => v,
                    _ => unreachable!(),
                })
                .collect();
            // A fold that would take long, such as a huge exact `expt`, is left to run.
            let mut fuel = Fuel { run: FOLD_FUEL, rest: 0 };
            if let Ok(val) = intrinsic.run(self.mc, &values, &mut fuel) {
                return L2::Quote(val);
            }
        }

        // 1b. Constant offsets have one form, `(+ x k)`: `(+ k x)` puts the constant second and
        //     `(- x k)` negates it, so the emitter only looks for one shape for `Op::AddImm`. The
        //     constant is pure, so moving it keeps evaluation order, and `x` faults the same.
        //     `(- x 0)` stays: it keeps `-0.0`, where `(+ x 0)` makes it `0.0`.
        if matches!(intrinsic, Intrinsic::Add | Intrinsic::Sub) && args.len() == 2 {
            let constant = |e: &L2<'a, 'gc>| match e {
                L2::Quote(v) => v.as_fixnum(),
                _ => None,
            };
            if intrinsic == Intrinsic::Add && constant(&args[0]).is_some() && constant(&args[1]).is_none() {
                args.swap(0, 1);
                return L2::Intrinsic(prim, args);
            }
            if intrinsic == Intrinsic::Sub
                && let Some(neg) = constant(&args[1]).filter(|&k| k != 0).and_then(i64::checked_neg).and_then(Value::fixnum)
            {
                args[1] = L2::Quote(neg);
                return L2::Intrinsic(Prim::Intrinsic(Intrinsic::Add), args);
            }
        }

        // A variable known to hold a pair is the `cons` that made it, to the rules below, which
        // then fold it away: but for `list?`, which would make the pair again.
        if args.len() == 1
            && (intrinsic.cxr_step().is_some() || (intrinsic.is_type_predicate() && intrinsic != Intrinsic::IsList))
            && let L2::Ref(v) = args[0]
            && let Some([head, tail]) = self.known_pairs.get(&v)
        {
            args[0] = L2::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec_in![self.arena; head.clone_in(self.arena), tail.clone_in(self.arena)]);
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
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec_in![self.arena; tail]),
                    None => tail,
                };
                return self.seq(head, next);
            }
            if tail.is_pure() {
                return match rest {
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec_in![self.arena; head]),
                    None => head,
                };
            }
            let tmp = self.supply.fresh_var();
            let projected = match rest {
                Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec_in![self.arena; L2::Ref(tmp)]),
                None => L2::Ref(tmp),
            };
            return L2::Let(vec_in![self.arena; Bind::Val(tmp, head)], self.arena.boxed(self.seq(tail, projected)));
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
                return self.seq(inner, L2::Quote(Value::FALSE));
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
                        return self.seq_all(cons_args, res);
                    }
                }
                L2::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), b) if b.len() == 1 => {
                    let Some(L2::Intrinsic(_, box_args)) = args.pop() else { unreachable!() };
                    let res = L2::Quote(if intrinsic == Intrinsic::IsBox { Value::TRUE } else { Value::FALSE });
                    return self.seq_all(box_args, res);
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
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec_in![self.arena; x]);
            }
            if matches!(args[0], L2::Quote(Value::NIL)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec_in![self.arena; x]);
            }
            if matches!(args[1], L2::Quote(Value::FALSE)) {
                let x = args.swap_remove(0);
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec_in![self.arena; x]);
            }
            if matches!(args[0], L2::Quote(Value::FALSE)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec_in![self.arena; x]);
            }
        }

        L2::Intrinsic(prim, args)
    }
}

/// How deeply `e` nests.
fn depth(e: &L2<'_, '_>) -> usize {
    let most = |es: &[L2<'_, '_>]| es.iter().map(depth).max().unwrap_or(0);
    1 + match e {
        L2::Quote(_) | L2::Ref(_) => 0,
        L2::If(a, b, c) => depth(a).max(depth(b)).max(depth(c)),
        L2::Seq(a, b) => depth(a).max(depth(b)),
        L2::Let(binds, body) => binds
            .iter()
            .map(|b| match b {
                Bind::Val(_, init) => depth(init),
                Bind::Fix(group) => group.iter().map(|(_, f)| depth(&f.body)).max().unwrap_or(0),
            })
            .fold(depth(body), usize::max),
        L2::Set(_, e) => depth(e),
        L2::App(f, args) => depth(f).max(most(args)),
        L2::Lambda(f) => depth(&f.body),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => most(args),
    }
}

fn func_takes<E>(func: &Func<'_, E>, argc: usize) -> bool {
    let (most, least) = (func.params.len(), func.params.len() - func.optional as usize);
    match func.rest {
        None => (least..=most).contains(&argc),
        Some(_) => argc >= least && argc.saturating_sub(most) <= MAX_REST_INLINE,
    }
}

#[derive(Clone, Copy, Default)]
struct UseStats {
    total: usize,
    valid_calls: usize,
    call_arity: usize,
}

fn count_uses(expr: &L2<'_, '_>) -> HashMap<Var, UseStats> {
    let mut map = HashMap::default();
    visit_uses(expr, &mut map);
    map
}

fn visit_uses(expr: &L2<'_, '_>, map: &mut HashMap<Var, UseStats>) {
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
            for bind in binds {
                match bind {
                    Bind::Val(_, init) => visit_uses(init, map),
                    Bind::Fix(group) => group.iter().for_each(|(_, f)| visit_uses(&f.body, map)),
                }
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

fn is_small_inlinable(func: &Func<'_, L2<'_, '_>>, assigned: &HashSet<Var>) -> bool {
    if func.params.iter().chain(&func.rest).any(|v| assigned.contains(v)) {
        return false;
    }
    let mut size = 0;
    check_small(&func.body, assigned, &mut size)
}

fn check_small(expr: &L2<'_, '_>, assigned: &HashSet<Var>, size: &mut usize) -> bool {
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
            binds.iter().all(|b| matches!(b, Bind::Val(v, init) if !assigned.contains(v) && check_small(init, assigned, size)))
                && check_small(body, assigned, size)
        }
        L2::Set(_, _) | L2::Lambda(_) => false,
        L2::App(f, args) => check_small(f, assigned, size) && args.iter().all(|a| check_small(a, assigned, size)),
        L2::Intrinsic(_, args) | L2::ApplyIntrinsic(_, args) => args.iter().all(|a| check_small(a, assigned, size)),
    }
}

fn alpha_rename<'a, 'gc>(arena: &'a Arena, func: &Func<'a, L2<'a, 'gc>>, supply: &mut Supply) -> Func<'a, L2<'a, 'gc>> {
    let mut map = HashMap::default();
    let params = func
        .params
        .iter()
        .map(|&v| {
            let fresh = supply.fresh_var();
            map.insert(v, fresh);
            fresh
        })
        .collect_in(arena);
    let rest = func.rest.map(|v| {
        let fresh = supply.fresh_var();
        map.insert(v, fresh);
        fresh
    });
    let body = rename_expr(arena, &func.body, &mut map, supply);
    Func { id: supply.fresh_lambda(), params, optional: func.optional, rest, body: arena.boxed(body) }
}

fn rename_expr<'a, 'gc>(arena: &'a Arena, expr: &L2<'a, 'gc>, map: &mut HashMap<Var, Var>, supply: &mut Supply) -> L2<'a, 'gc> {
    match expr {
        L2::Quote(v) => L2::Quote(*v),
        L2::Ref(v) => L2::Ref(map.get(v).copied().unwrap_or(*v)),
        L2::If(a, b, c) => L2::If(
            arena.boxed(rename_expr(arena, a, map, supply)),
            arena.boxed(rename_expr(arena, b, map, supply)),
            arena.boxed(rename_expr(arena, c, map, supply)),
        ),
        L2::Seq(a, b) => L2::Seq(arena.boxed(rename_expr(arena, a, map, supply)), arena.boxed(rename_expr(arena, b, map, supply))),
        L2::Let(binds, body) => {
            let mut renamed = Vec::with_capacity_in(binds.len(), arena);
            for bind in binds {
                let Bind::Val(v, init) = bind else { unreachable!("small inlinable functions have no Fix") };
                let init = rename_expr(arena, init, map, supply);
                let fresh = supply.fresh_var();
                map.insert(*v, fresh);
                renamed.push(Bind::Val(fresh, init));
            }
            let body = rename_expr(arena, body, map, supply);
            L2::Let(renamed, arena.boxed(body))
        }
        L2::App(f, args) => L2::App(
            arena.boxed(rename_expr(arena, f, map, supply)),
            args.iter().map(|a| rename_expr(arena, a, map, supply)).collect_in(arena),
        ),
        L2::Intrinsic(prim, args) => L2::Intrinsic(*prim, args.iter().map(|a| rename_expr(arena, a, map, supply)).collect_in(arena)),
        L2::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(*prim, args.iter().map(|a| rename_expr(arena, a, map, supply)).collect_in(arena)),
        L2::Set(_, _) | L2::Lambda(_) => unreachable!("small inlinable functions have no Set/Lambda"),
    }
}
