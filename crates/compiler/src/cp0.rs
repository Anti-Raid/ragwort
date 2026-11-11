//! Pass 3 (`L2 -> L2`): Chez-style `cp0` source optimizer.
//!
//! Performs in a single pass:
//! - Copy and constant propagation for unassigned variables
//! - Pure intrinsic constant folding
//! - Direct beta-reduction (`((lambda (x ...) body) a ...)`)
//! - Single-use and small local procedure inlining
//! - A call of a small procedure that only picks which procedure to call, where what's known
//!   decides the pick, is a call of the one picked: `match` makes one for each clause
//! - Conditional (`if`) and negation (`not`) simplification
//! - Dead `Let` binding elimination and effect sequencing (`Seq`)
//! - What's known of struct values:
//!   - a test or a field read says what type a value is or isn't of, so later tests fold and
//!     later reads check nothing;
//!   - a variable bound to a new struct has the values of its fields that can't be set
//!
//! It reads one table, the source, and makes what it optimizes to in another, so what's still to
//! optimize and what's done are of different tables. The one code it optimizes again, a small
//! function's copied in at a call, it copies back into the source, renamed. It's a loop over a
//! stack of tasks, what they make on a stack of their own, and inlining goes as deep as it goes
//! without taking more of the machine's stack. Each task does what a call of a recursive optimizer
//! would, in the same order, so the facts it learns hold where they did.

use crate::hash::{HashMap, HashSet};

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Fuel, Intrinsic, Purity, structs};

use crate::ir::Supply;
use crate::ir::l2::{Bind, Fun, Function, Id, L2, Node, Span};
use crate::{Prim, SlotOp, Var};

/// The most fuel a constant fold may spend.
const FOLD_FUEL: u64 = 1 << 16;
/// Maximum AST node count of a multi-use local lambda eligible for inlining.
const MAX_INLINE_SIZE: usize = 10;
/// Maximum number of rest-argument elements to expand inline into a `cons` chain.
const MAX_REST_INLINE: usize = 16;
/// How many copies of small functions can be in each other.
const MAX_INLINE_DEPTH: usize = 4;

/// `root` of `src` optimized into `out`, and its root there. `src` takes the code made to be
/// optimized on the way.
pub(crate) fn optimize<'s, 'd, 'gc>(mc: &Mutation<'gc>, src: &mut L2<'s, 'gc>, root: Id<'s>, out: &mut L2<'d, 'gc>, supply: Supply) -> (Id<'d>, Supply) {
    let (mut uses, mut used, mut assigned) = (HashMap::<Var, UseStats>::default(), HashSet::default(), HashSet::default());
    for id in src.deep(root) {
        match src[id] {
            Node::Ref(v) => {
                used.insert(v);
                uses.entry(v).or_default().total += 1;
            }
            Node::Set(v, _) => {
                assigned.insert(v);
                uses.entry(v).or_default().total += 2;
            }
            Node::App(f, args) => {
                if let Node::Ref(v) = src[f] {
                    let entry = uses.entry(v).or_default();
                    entry.valid_calls += 1;
                    entry.call_arity = src[args].len();
                }
            }
            _ => {}
        }
    }
    let mut pass = Cp0 {
        mc,
        src,
        out,
        supply,
        uses,
        used,
        assigned,
        subst: HashMap::default(),
        truthy_vars: HashSet::default(),
        pred_facts: HashMap::default(),
        single_use: HashMap::default(),
        small_bodies: Vec::new(),
        next_small: false,
        small_funcs: HashMap::default(),
        known_pairs: HashMap::default(),
        known_structs: HashMap::default(),
        derived: HashMap::default(),
        slot_derived: HashMap::default(),
        hidden: Vec::new(),
        learned: Vec::new(),
        inline_depth: 0,
        arms: Vec::new(),
        lets: Vec::new(),
        vals: Vec::new(),
    };
    let mut todo = vec![Task::Expr(root)];
    let mut then = Vec::new();
    while let Some(task) = todo.pop() {
        pass.run(task, &mut then);
        todo.extend(then.drain(..).rev());
    }
    let root = pass.pop();
    (root, pass.supply)
}

/// What a fact about a struct value is a fact about: an unassigned variable, or one of the
/// module's variables, which a call can change.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Subject {
    Local(Var),
    Slot(u32),
}

/// The struct types a value is known to be an instance of, and those it's known not to be.
#[derive(Default)]
struct Known<'gc> {
    is: Vec<Gc<'gc, StructType>>,
    isnt: Vec<Gc<'gc, StructType>>,
}

/// A branch of an `if`, in [`Cp0::arms`]: source still to optimize, or an `if` whose test is
/// already optimized, as splitting `(if (if a b #f) ...)` makes, so `b` isn't optimized twice.
#[derive(Clone, Copy)]
enum Arm<'s, 'd> {
    Raw(Id<'s>),
    If(Id<'d>, usize, usize),
}

#[derive(Clone, Copy)]
enum Subst<'gc> {
    Quote(Value<'gc>),
    Var(Var),
}

/// A binding of a `let` being optimized: its init still source, or done, or source functions.
#[derive(Clone, Copy)]
enum BindIn<'s, 'd> {
    Val(Var, Init<'s, 'd>),
    Fix(Span<'s, (Var, Fun<'s>)>),
}

#[derive(Clone, Copy)]
enum Init<'s, 'd> {
    Src(Id<'s>),
    Done(Id<'d>),
}

/// A `let` being optimized: its bindings, and those of them kept so far.
struct LetFrame<'s, 'd> {
    binds: Vec<BindIn<'s, 'd>>,
    kept: Vec<Bind<'d>>,
}

/// What's left to do: a source node to optimize, which makes one node, or what to do with those
/// made last.
enum Task<'s, 'd, 'gc> {
    Expr(Id<'s>),
    Arm(usize),
    /// An `if`'s test made: its branches.
    Test(usize, usize),
    /// `first` for what it does, then what's made last.
    Then(Id<'d>),
    /// What's made last in the scope of `binds`.
    Within(Span<'d, Bind<'d>>),
    Seq,
    Set(Var),
    /// The `then` of `(if v ...)` made, `v` truthy in it; `other` next, with `v` false.
    VarElse { v: Var, newly: bool, other: usize, test: Id<'d> },
    VarDone { v: Var, prev: Option<Subst<'gc>>, test: Id<'d> },
    /// The `then` of `(if (pred v) ...)` made; `other` next, with the fact false.
    PredElse { pred: Intrinsic, v: Var, newly: bool, prev_subst: Option<Subst<'gc>>, prev_fact: Option<bool>, other: usize, test: Id<'d> },
    PredDone { pred: Intrinsic, v: Var, prev_fact: Option<bool>, test: Id<'d> },
    /// The `then` of `(if (struct-derived-from? x type) ...)` made; `other` next, where `x`
    /// isn't an instance of the type, and `truthy` is no longer known to be true.
    DerivedElse { truthy: Option<Var>, subject: Subject, kind: Gc<'gc, StructType>, other: usize, test: Id<'d> },
    /// The branch of an `if` taken when the subject is an instance of the struct type, if
    /// `is`, or when it isn't.
    ArmOf(usize, Subject, Gc<'gc, StructType>, bool),
    /// Out of an `if`'s branch or a function's body: what [`Cp0::learned`] has past its first
    /// `n` is forgotten, as it's only known where that code has run.
    Forget(usize),
    /// Into a function's body, which runs after any code might have: what's known of the
    /// module's variables is put aside.
    Hide,
    /// Out of a function's body: what was put aside is known again.
    Show,
    /// Into the body of a function, which is one of [`Cp0::small_bodies`] if it says so, and
    /// out of it.
    Enter(bool),
    Leave,
    /// The lambda made last is bound to the variable, in the `let` that's that deep in
    /// [`Cp0::lets`]: one called once that wasn't inlined at its call.
    LateBind(usize, Var),
    /// Both branches of an `if` made.
    If(Id<'d>),
    /// The innermost `let`'s binding.
    Bind(usize),
    Val(Var),
    Fix(Span<'s, (Var, Fun<'s>)>),
    /// The innermost `let`'s body made.
    Let,
    /// A function's body made.
    Function(Fun<'s>),
    /// A call's operator made, its arguments source.
    Callee(Span<'s, Id<'s>>),
    /// A call's operator and arguments made.
    Call(usize),
    /// A call's operator and arguments made, to call as they are.
    App(usize),
    Intrinsic(Prim, usize),
    ApplyIntrinsic(Prim, usize),
    /// Out of a small function's copy.
    Inlined,
}

struct Cp0<'m, 't, 's, 'd, 'gc> {
    mc: &'m Mutation<'gc>,
    src: &'t mut L2<'s, 'gc>,
    out: &'t mut L2<'d, 'gc>,
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
    /// Unassigned `Let`-bound lambdas referenced exactly once, in call position, still source.
    single_use: HashMap<Var, (Fun<'s>, usize)>,
    /// For each function's body being optimized, innermost last, whether the function is one
    /// that's small as it's written and called in several places: a procedure called once
    /// isn't inlined in it and a small one isn't copied into it, so that it stays small enough
    /// to be copied to its calls, where more is known.
    small_bodies: Vec<bool>,
    /// Whether the lambda about to be optimized is such a function.
    next_small: bool,
    /// Small unassigned `Let`-bound lambdas with no nested lambdas, eligible for cloning at call sites.
    small_funcs: HashMap<Var, Fun<'d>>,
    /// Unassigned variables bound to `(cons a b)` of constants and unassigned variables. Pairs
    /// are immutable, so the variable's car and cdr are `a` and `b` wherever it's in scope.
    known_pairs: HashMap<Var, [Node<'d, 'gc>; 2]>,
    /// Unassigned variables bound to `(make-struct 'type part ...)`: the type, and each part, a
    /// constant or an unassigned variable. A field that can't be set is its part wherever the
    /// variable's in scope.
    known_structs: HashMap<Var, (Gc<'gc, StructType>, Vec<Node<'d, 'gc>>)>,
    /// What's known of the values of unassigned variables: a test said what struct type each is
    /// or isn't of, or a field read by a type didn't fault. A value's type never changes, so
    /// it holds in all the code that runs after.
    derived: HashMap<Var, Known<'gc>>,
    /// The same of the module's variables, which holds only till code that could assign one
    /// runs: a call, or a function's body, which `hidden` keeps it from, innermost last.
    slot_derived: HashMap<u32, Known<'gc>>,
    hidden: Vec<HashMap<u32, Known<'gc>>>,
    /// What `derived` and `slot_derived` were told, in order: of what, and whether it's a type
    /// it is of.
    learned: Vec<(Subject, bool)>,
    inline_depth: usize,
    arms: Vec<Arm<'s, 'd>>,
    /// The `let`s being optimized, innermost last.
    lets: Vec<LetFrame<'s, 'd>>,
    /// What's been made, innermost last.
    vals: Vec<Id<'d>>,
}

impl<'s, 'd, 'gc> Cp0<'_, '_, 's, 'd, 'gc> {
    fn pop(&mut self) -> Id<'d> {
        self.vals.pop().expect("a node made")
    }

    /// The last `n` nodes made.
    fn last(&mut self, n: usize) -> Vec<Id<'d>> {
        self.vals.split_off(self.vals.len() - n)
    }

    fn quote(&mut self, v: Value<'gc>) -> Id<'d> {
        self.out.add(Node::Quote(v))
    }

    fn arm_raw(&mut self, e: Id<'s>) -> usize {
        self.arms.push(Arm::Raw(e));
        self.arms.len() - 1
    }

    fn frame(&mut self) -> &mut LetFrame<'s, 'd> {
        self.lets.last_mut().expect("in a let")
    }

    fn run(&mut self, task: Task<'s, 'd, 'gc>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        let made = match task {
            Task::Expr(id) => return self.expr(id, then),
            Task::Arm(arm) => {
                let mark = self.learned.len();
                self.arm(arm, then);
                return then.push(Task::Forget(mark));
            }
            Task::ArmOf(arm, subject, kind, is) => {
                let mark = self.learned.len();
                self.learn(subject, kind, is);
                self.arm(arm, then);
                return then.push(Task::Forget(mark));
            }
            Task::Forget(mark) => {
                for (subject, is) in self.learned.split_off(mark) {
                    // A call may have forgotten what was known of a module's variable since.
                    let Some(known) = self.known_mut(subject) else { continue };
                    if is {
                        known.is.pop();
                    } else {
                        known.isnt.pop();
                    }
                }
                return;
            }
            Task::Enter(small) => return self.small_bodies.push(small),
            Task::Leave => {
                self.small_bodies.pop();
                return;
            }
            Task::LateBind(frame, v) => {
                let lambda = self.pop();
                if let Node::Lambda(fun) = self.out[lambda]
                    && self.inline_depth < MAX_INLINE_DEPTH
                    && self.is_small_inlinable(fun)
                {
                    self.small_funcs.insert(v, fun);
                }
                return self.lets[frame].kept.push(Bind::Val(v, lambda));
            }
            Task::Hide => return self.hidden.push(std::mem::take(&mut self.slot_derived)),
            Task::Show => return self.slot_derived = self.hidden.pop().expect("hidden"),
            Task::DerivedElse { truthy, subject, kind, other, test } => {
                if let Some(v) = truthy {
                    self.truthy_vars.remove(&v);
                }
                return then.extend([Task::ArmOf(other, subject, kind, false), Task::If(test)]);
            }
            Task::Test(t, o) => {
                let test = self.pop();
                return self.simplify_if(test, t, o, then);
            }
            Task::Then(first) => {
                let second = self.pop();
                self.seq(first, second)
            }
            Task::Within(binds) => {
                let body = self.pop();
                if self.out[binds].is_empty() { body } else { self.out.add(Node::Let(binds, body)) }
            }
            Task::Seq => {
                let (b, a) = (self.pop(), self.pop());
                self.seq(a, b)
            }
            Task::Set(v) => {
                let value = self.pop();
                let target = match self.subst.get(&v).copied() {
                    Some(Subst::Var(u)) => u,
                    _ => v,
                };
                if self.used.contains(&target) {
                    self.out.add(Node::Set(target, value))
                } else {
                    let void = self.quote(Value::VOID);
                    self.seq(value, void)
                }
            }
            Task::VarElse { v, newly, other, test } => {
                if newly {
                    self.truthy_vars.remove(&v);
                }
                let prev = self.subst.insert(v, Subst::Quote(Value::FALSE));
                return then.extend([Task::Arm(other), Task::VarDone { v, prev, test }]);
            }
            Task::VarDone { v, prev, test } => {
                let (other, t) = (self.pop(), self.pop());
                self.restore(v, prev);
                self.branches(test, t, other)
            }
            Task::PredElse { pred, v, newly, prev_subst, prev_fact, other, test } => {
                if newly {
                    self.truthy_vars.remove(&v);
                }
                if pred == Intrinsic::IsNull {
                    self.restore(v, prev_subst);
                }
                self.pred_facts.insert((pred, v), false);
                return then.extend([Task::Arm(other), Task::PredDone { pred, v, prev_fact, test }]);
            }
            Task::PredDone { pred, v, prev_fact, test } => {
                let (other, t) = (self.pop(), self.pop());
                match prev_fact {
                    Some(prev) => _ = self.pred_facts.insert((pred, v), prev),
                    None => _ = self.pred_facts.remove(&(pred, v)),
                }
                self.branches(test, t, other)
            }
            Task::If(test) => {
                let (other, t) = (self.pop(), self.pop());
                self.branches(test, t, other)
            }
            Task::Bind(i) => return self.bind(i, then),
            Task::Val(v) => {
                let init = self.pop();
                return self.bound(v, init);
            }
            Task::Fix(group) => {
                let bodies = self.last(self.src[group].len());
                let funs: Vec<(Var, Fun<'d>)> = (0..bodies.len()).map(|i| (self.src[group][i].0, self.function(self.src[group][i].1, bodies[i]))).collect();
                let group = self.out.list(funs);
                return self.frame().kept.push(Bind::Fix(group));
            }
            Task::Let => {
                let body = self.pop();
                let frame = self.lets.pop().expect("in a let");
                for &bind in &frame.kept {
                    for v in self.out.vars(bind) {
                        self.small_funcs.remove(&v);
                    }
                }
                self.finish_let(frame.kept, body)
            }
            Task::Function(fun) => {
                let body = self.pop();
                let fun = self.function(fun, body);
                self.out.add(Node::Lambda(fun))
            }
            Task::Callee(args) => return self.callee(args, then),
            Task::Call(n) => {
                let args = self.last(n);
                let f = self.pop();
                return self.opt_app(f, args, then);
            }
            Task::App(n) => {
                let args = self.last(n);
                let (f, args) = (self.pop(), self.out.list(args));
                self.slot_derived.clear();
                self.out.add(Node::App(f, args))
            }
            Task::Intrinsic(prim, n) => {
                let args = self.last(n);
                self.opt_intrinsic(prim, args)
            }
            Task::ApplyIntrinsic(prim, n) => {
                let args = self.last(n);
                let args = self.out.list(args);
                self.ran(prim);
                self.out.add(Node::ApplyIntrinsic(prim, args))
            }
            Task::Inlined => return self.inline_depth -= 1,
        };
        self.vals.push(made);
    }

    fn expr(&mut self, id: Id<'s>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        let node = self.src[id];
        let made = match node {
            Node::Quote(v) => Node::Quote(v),
            Node::Ref(v) => match self.subst.get(&v).copied() {
                Some(Subst::Quote(val)) => Node::Quote(val),
                Some(Subst::Var(u)) => Node::Ref(u),
                None => Node::Ref(v),
            },
            Node::If(test, t, o) => {
                let (t, o) = (self.arm_raw(t), self.arm_raw(o));
                return then.extend([Task::Expr(test), Task::Test(t, o)]);
            }
            Node::Seq(a, b) => return then.extend([Task::Expr(a), Task::Expr(b), Task::Seq]),
            Node::Let(binds, body) => {
                let binds = self.src[binds]
                    .iter()
                    .map(|&bind| match bind {
                        Bind::Val(v, init) => BindIn::Val(v, Init::Src(init)),
                        Bind::Fix(group) => BindIn::Fix(group),
                    })
                    .collect();
                return self.open_let(binds, body, then);
            }
            Node::Set(v, value) => return then.extend([Task::Expr(value), Task::Set(v)]),
            Node::App(f, args) => return self.app(f, args, then),
            Node::Lambda(fun) => {
                let small = std::mem::take(&mut self.next_small);
                return then.extend(self.body_tasks(fun, small).into_iter().chain([Task::Function(fun)]));
            }
            Node::Intrinsic(prim, args) => {
                then.extend(self.src[args].iter().map(|&a| Task::Expr(a)));
                return then.push(Task::Intrinsic(prim, self.src[args].len()));
            }
            Node::ApplyIntrinsic(prim, args) => {
                then.extend(self.src[args].iter().map(|&a| Task::Expr(a)));
                return then.push(Task::ApplyIntrinsic(prim, self.src[args].len()));
            }
        };
        let made = self.out.add(made);
        self.vals.push(made);
    }

    /// `fun`'s record, its body made.
    fn function(&mut self, fun: Fun<'s>, body: Id<'d>) -> Fun<'d> {
        let f = self.src[fun];
        let params = self.out.list(self.src[f.params].iter().copied());
        self.out.function(Function { id: f.id, optional: f.optional, params, rest: f.rest, body })
    }

    fn restore(&mut self, v: Var, prev: Option<Subst<'gc>>) {
        match prev {
            Some(prev) => _ = self.subst.insert(v, prev),
            None => _ = self.subst.remove(&v),
        }
    }

    fn arm(&mut self, arm: usize, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        match self.arms[arm] {
            Arm::Raw(e) => then.push(Task::Expr(e)),
            Arm::If(test, t, o) => self.simplify_if(test, t, o, then),
        }
    }

    /// The `if` of `test`, made, and its branches made: just one, if they're the same constant or
    /// variable.
    fn branches(&mut self, test: Id<'d>, t: Id<'d>, other: Id<'d>) -> Id<'d> {
        let same = match (self.out[t], self.out[other]) {
            (Node::Quote(a), Node::Quote(b)) => a == b,
            (Node::Ref(a), Node::Ref(b)) => a == b,
            _ => false,
        };
        if same { self.seq(test, t) } else { self.out.add(Node::If(test, t, other)) }
    }

    /// `(if test then other)` with `test` already made.
    fn simplify_if(&mut self, mut test: Id<'d>, mut t: usize, mut o: usize, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        // What's to be done with what the `if` makes, last first.
        let mut after = Vec::new();
        loop {
            let node = self.out[test];
            match node {
                // (if #f then other) -> other; (if <non-#f-const> then other) -> then
                Node::Quote(v) => then.push(Task::Arm(if v == Value::FALSE { o } else { t })),
                // Known truthy variable from an enclosing dominating `if` test.
                Node::Ref(v) if self.truthy_vars.contains(&v) => then.push(Task::Arm(t)),
                // Any expression guaranteed never to evaluate to `#f`.
                _ if self.out.is_always_truthy(test) => then.extend([Task::Arm(t), Task::Then(test)]),
                // (if (not x) then other) -> (if x other then)
                Node::Intrinsic(Prim::Intrinsic(Intrinsic::Not), args) if self.out[args].len() == 1 => {
                    test = self.out[args][0];
                    std::mem::swap(&mut t, &mut o);
                    continue;
                }
                // (if (seq a b) then other) -> (seq a (if b then other))
                Node::Seq(a, b) => {
                    after.push(Task::Then(a));
                    test = b;
                    continue;
                }
                // Short-circuit `and` in test position: (if (if a b #f) then other) -> (if a (if b then other) other)
                // when `other` is a constant or variable reference (no code duplication).
                Node::If(a, b, c)
                    if matches!(self.out[c], Node::Quote(Value::FALSE))
                        && matches!(self.arms[o], Arm::Raw(e) if matches!(self.src[e], Node::Quote(_) | Node::Ref(_))) =>
                {
                    let Arm::Raw(e) = self.arms[o] else { unreachable!() };
                    let copy = self.src.add(self.src[e]);
                    let copy = self.arm_raw(copy);
                    self.arms.push(Arm::If(b, t, copy));
                    t = self.arms.len() - 1;
                    test = a;
                    continue;
                }
                // Dominating variable test: in `then`, `v` is truthy; in `other`, `v` is `#f`.
                Node::Ref(v) if !self.assigned.contains(&v) => {
                    let newly = self.truthy_vars.insert(v);
                    then.extend([Task::Arm(t), Task::VarElse { v, newly, other: o, test }]);
                }
                // Dominating struct test: in `then`, the value is an instance of the type, and in
                // `other` it isn't.
                Node::Intrinsic(Prim::Intrinsic(Intrinsic::IsStructDerivedFrom), args)
                    if let [tested, kind] = self.out[args]
                        && let Some(subject) = self.subject(tested)
                        && let Some(kind) = self.struct_type(kind) =>
                {
                    let truthy = match subject {
                        Subject::Local(v) => self.truthy_vars.insert(v).then_some(v),
                        Subject::Slot(_) => None,
                    };
                    then.extend([Task::ArmOf(t, subject, kind, true), Task::DerivedElse { truthy, subject, kind, other: o, test }]);
                }
                // Dominating type-predicate test: `(if (pair? v) then other)` records `(IsPair, v)` in branches.
                Node::Intrinsic(Prim::Intrinsic(pred), args)
                    if self.out[args].len() == 1
                        && pred.is_type_predicate()
                        && matches!(self.out[self.out[args][0]], Node::Ref(v) if !self.assigned.contains(&v)) =>
                {
                    let Node::Ref(v) = self.out[self.out[args][0]] else { unreachable!() };
                    let prev_fact = self.pred_facts.insert((pred, v), true);
                    let newly = (pred != Intrinsic::IsBoolean) && self.truthy_vars.insert(v);
                    let prev_subst = if pred == Intrinsic::IsNull { self.subst.insert(v, Subst::Quote(Value::NIL)) } else { None };
                    then.extend([Task::Arm(t), Task::PredElse { pred, v, newly, prev_subst, prev_fact, other: o, test }]);
                }
                _ => then.extend([Task::Arm(t), Task::Arm(o), Task::If(test)]),
            }
            break;
        }
        then.extend(after.into_iter().rev());
    }

    /// Starts a `let` of `binds` and `body`.
    fn open_let(&mut self, binds: Vec<BindIn<'s, 'd>>, body: Id<'s>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        then.extend((0..binds.len()).map(Task::Bind));
        then.extend([Task::Expr(body), Task::Let]);
        self.lets.push(LetFrame { binds, kept: Vec::new() });
    }

    /// The innermost `let`'s binding `i`, once those before it are done.
    fn bind(&mut self, i: usize, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        let (v, init) = match self.frame().binds[i] {
            BindIn::Val(v, init) => (v, init),
            BindIn::Fix(group) => {
                for &(_, fun) in &self.src[group] {
                    then.extend(self.body_tasks(fun, false));
                }
                return then.push(Task::Fix(group));
            }
        };
        // A lambda from source that's never used goes; one called once stays source until it's
        // inlined at that call, so its body is optimized once, there. A variable cp0 made itself
        // isn't counted, so it's neither.
        if !self.assigned.contains(&v)
            && let Init::Src(e) = init
            && let Node::Lambda(fun) = self.src[e]
            && let Some(&stats) = self.uses.get(&v)
        {
            if stats.total == 0 {
                return;
            }
            if stats.total == 1 && stats.valid_calls == 1 && takes(self.src, fun, stats.call_arity) {
                self.single_use.insert(v, (fun, self.lets.len() - 1));
                return;
            }
            // One that's only called, in several places, and is small as it's written is kept
            // small, to be copied to those places.
            self.next_small = stats.valid_calls == stats.total && self.small_as_written(fun);
        }
        match init {
            Init::Src(e) => then.extend([Task::Expr(e), Task::Val(v)]),
            Init::Done(init) => self.bound(v, init),
        }
    }

    /// `v` bound to `init`, made, in the innermost `let`.
    fn bound(&mut self, v: Var, mut init: Id<'d>) {
        if !self.assigned.contains(&v) {
            if let Some((kind, args)) = self.out.made_struct(self.mc, init) {
                // Each field's value has a name, so a read of the field is the name: one that
                // isn't a constant or a variable is bound to a new variable first, in order.
                let mut args = self.out[args].to_vec();
                for arg in &mut args[1..] {
                    if !self.copyable(*arg) {
                        let part = self.supply.fresh_var();
                        self.frame().kept.push(Bind::Val(part, *arg));
                        *arg = self.out.add(Node::Ref(part));
                    }
                }
                let parts = args[1..].iter().map(|&arg| self.out[arg]).collect();
                self.known_structs.insert(v, (kind, parts));
                init = self.make(Prim::Intrinsic(Intrinsic::MakeStruct), args);
            }
            match self.out[init] {
                Node::Quote(val) => {
                    self.subst.insert(v, Subst::Quote(val));
                    return;
                }
                Node::Ref(u) if !self.assigned.contains(&u) => {
                    self.subst.insert(v, Subst::Var(u));
                    return;
                }
                Node::Lambda(fun) if self.inline_depth < MAX_INLINE_DEPTH && self.is_small_inlinable(fun) => _ = self.small_funcs.insert(v, fun),
                Node::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), parts) if self.out[parts].iter().all(|&p| self.copyable(p)) => {
                    let parts = [self.out[self.out[parts][0]], self.out[self.out[parts][1]]];
                    self.known_pairs.insert(v, parts);
                }
                _ => {}
            }
        }
        self.frame().kept.push(Bind::Val(v, init));
    }

    /// `first` evaluated for what it does, then `second`.
    fn seq(&mut self, first: Id<'d>, second: Id<'d>) -> Id<'d> {
        self.seq_all(vec![first], second)
    }

    /// `firsts` evaluated in order for what they do, then `second`, dropping their pure parts. Two
    /// or more effects left are one `Let`, of variables unused, so however many there are they
    /// nest no deeper.
    fn seq_all(&mut self, firsts: Vec<Id<'d>>, second: Id<'d>) -> Id<'d> {
        let mut todo: Vec<Id<'d>> = firsts.into_iter().rev().collect();
        let mut effects = Vec::new();
        while let Some(e) = todo.pop() {
            if self.out.is_pure(self.mc, e) {
                continue;
            }
            match self.out[e] {
                Node::Seq(a, b) => todo.extend([b, a]),
                Node::Intrinsic(Prim::Intrinsic(i), args) if i.is_discardable() => todo.extend(self.out[args].iter().rev()),
                Node::Intrinsic(Prim::Read(r), args) if r.is_discardable() => todo.extend(self.out[args].iter().rev()),
                Node::Intrinsic(Prim::Host(h), args) if h.purity == Purity::Discardable => todo.extend(self.out[args].iter().rev()),
                Node::If(test, t, o) if self.out.is_pure(self.mc, t) && self.out.is_pure(self.mc, o) => todo.push(test),
                _ => effects.push(e),
            }
        }
        if effects.len() < 2 {
            return match effects.pop() {
                Some(e) => self.out.add(Node::Seq(e, second)),
                None => second,
            };
        }
        let binds: Vec<Bind<'d>> = effects.into_iter().map(|e| Bind::Val(self.supply.fresh_var(), e)).collect();
        let binds = self.out.list(binds);
        self.out.add(Node::Let(binds, second))
    }

    /// Whether `e` can be copied to wherever its value's used: a constant, or a variable no code
    /// assigns.
    fn copyable(&self, e: Id<'d>) -> bool {
        match self.out[e] {
            Node::Quote(_) => true,
            Node::Ref(u) => !self.assigned.contains(&u),
            _ => false,
        }
    }

    /// Unused bindings are left to [`prune`](crate::letrec::prune), which finds them all in one walk.
    fn finish_let(&mut self, kept: Vec<Bind<'d>>, body: Id<'d>) -> Id<'d> {
        if kept.is_empty() {
            return body;
        }
        let kept = self.out.list(kept);
        self.out.add(Node::Let(kept, body))
    }

    /// A call from source. Binding forms around the operator float out first, so a lambda they
    /// end in is applied directly: `((let (...) f) x) -> (let (...) (f x))`. The bindings and
    /// effects still come before `f` and `x`, and every variable is unique, so nothing is
    /// captured. A lambda applied directly or called once is inlined with its body and
    /// arguments still source, so each is optimized once.
    fn app(&mut self, f: Id<'s>, args: Span<'s, Id<'s>>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        match self.src[f] {
            Node::Seq(a, b) => {
                let call = self.src.add(Node::App(b, args));
                return then.push(Task::Expr(self.src.add(Node::Seq(a, call))));
            }
            Node::Let(binds, body) => {
                let call = self.src.add(Node::App(body, args));
                return then.push(Task::Expr(self.src.add(Node::Let(binds, call))));
            }
            Node::Lambda(fun) if takes(self.src, fun, self.src[args].len()) => {
                let binds = self.bind_src(fun, args);
                return self.open_let(binds, self.src[fun].body, then);
            }
            _ => {}
        }
        then.extend([Task::Expr(f), Task::Callee(args)]);
    }

    /// A call from source whose operator is made: a lambda called once is inlined there.
    fn callee(&mut self, args: Span<'s, Id<'s>>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        let f = self.pop();
        let n = self.src[args].len();
        if let Node::Ref(v) = self.out[f]
            && let Some((fun, frame)) = self.single_use.remove(&v)
        {
            // In a function that's to stay small, it's called: it's bound where it was, to
            // what its body is made into here, its one call. It's called wherever that
            // function is copied to, so it stays small too, if it's small as it's written.
            if self.small_bodies.last() == Some(&true) {
                self.vals.push(f);
                let small = self.small_as_written(fun);
                then.extend(self.body_tasks(fun, small).into_iter().chain([Task::Function(fun), Task::LateBind(frame, v)]));
                then.extend(self.src[args].iter().map(|&a| Task::Expr(a)));
                return then.push(Task::Call(n));
            }
            if takes(self.src, fun, n) {
                let binds = self.bind_src(fun, args);
                return self.open_let(binds, self.src[fun].body, then);
            }
            then.extend(self.body_tasks(fun, false).into_iter().chain([Task::Function(fun)]));
            then.extend(self.src[args].iter().map(|&a| Task::Expr(a)));
            return then.push(Task::App(n));
        }
        self.vals.push(f);
        then.extend(self.src[args].iter().map(|&a| Task::Expr(a)));
        then.push(Task::Call(n));
    }

    /// What optimizes the body of `fun`, which runs after any code might have, as its own: what's
    /// known of the module's variables is put aside for it, and what it learns is forgotten.
    fn body_tasks(&self, fun: Fun<'s>, small: bool) -> [Task<'s, 'd, 'gc>; 6] {
        [Task::Enter(small), Task::Hide, Task::Expr(self.src[fun].body), Task::Forget(self.learned.len()), Task::Show, Task::Leave]
    }

    /// `fun`'s parameters bound to `args`, all source.
    fn bind_src(&mut self, fun: Fun<'s>, args: Span<'s, Id<'s>>) -> Vec<BindIn<'s, 'd>> {
        let f = self.src[fun];
        let params = self.src[f.params].to_vec();
        let mut args = self.src[args].to_vec();
        // Optional parameters left out are unsupplied, as the VM binds them.
        while args.len() < params.len() {
            args.push(self.src.add(Node::Quote(Value::UNSUPPLIED)));
        }
        let rest = f.rest.map(|rest| {
            let mut list = self.src.add(Node::Quote(Value::NIL));
            for item in args.split_off(params.len()).into_iter().rev() {
                let pair = self.src.list([item, list]);
                list = self.src.add(Node::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), pair));
            }
            (rest, list)
        });
        params.into_iter().zip(args).chain(rest).map(|(v, e)| BindIn::Val(v, Init::Src(e))).collect()
    }

    /// `params` and `rest` bound to `args`, made.
    fn bind_done(&mut self, params: Vec<Var>, rest: Option<Var>, mut args: Vec<Id<'d>>) -> Vec<(Var, Id<'d>)> {
        while args.len() < params.len() {
            args.push(self.quote(Value::UNSUPPLIED));
        }
        let rest = rest.map(|rest| {
            let mut list = self.quote(Value::NIL);
            for item in args.split_off(params.len()).into_iter().rev() {
                list = self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, list]);
            }
            (rest, list)
        });
        params.into_iter().zip(args).chain(rest).collect()
    }

    /// A call whose operator and arguments are made.
    fn opt_app(&mut self, mut f: Id<'d>, args: Vec<Id<'d>>, then: &mut Vec<Task<'s, 'd, 'gc>>) {
        // Binding forms an inlined operator ended up in float out, as in `app`.
        let mut wraps = Vec::new();
        loop {
            match self.out[f] {
                Node::Seq(a, b) => {
                    wraps.push(Task::Then(a));
                    f = b;
                }
                Node::Let(binds, body) => {
                    wraps.push(Task::Within(binds));
                    f = body;
                }
                _ => break,
            }
        }
        // A call of a small function that only picks which procedure to call is a call of the
        // one picked, and so on from that one. Each is bound before the one that calls it, so
        // this ends, however many there are.
        while args.is_empty()
            && let Node::Ref(v) = self.out[f]
            && let Some(&fun) = self.small_funcs.get(&v)
            && let Some(to) = self.picked(fun)
        {
            f = to;
        }
        let made = match self.out[f] {
            // An optimized lambda applied directly binds its parameters around its body as it is,
            // rather than optimizing the body again.
            Node::Lambda(fun) if takes(self.out, fun, args.len()) => {
                let func = self.out[fun];
                let params = self.out[func.params].to_vec();
                let binds = self.bind_done(params, func.rest, args).into_iter().map(|(v, e)| Bind::Val(v, e)).collect();
                // Its body, made already, may call anything.
                self.slot_derived.clear();
                self.finish_let(binds, func.body)
            }
            // A small local lambda is copied in at each call, with its parameters renamed, and the
            // copy optimized again with the arguments it's given: but not into a function
            // that's to stay small.
            Node::Ref(v)
                if self.inline_depth < MAX_INLINE_DEPTH
                    && self.small_bodies.last() != Some(&true)
                    && let Some(&fun) = self.small_funcs.get(&v)
                    && takes(self.out, fun, args.len()) =>
            {
                let renamed = self.alpha_rename(fun);
                self.inline_depth += 1;
                let func = self.src[renamed];
                let params = self.src[func.params].to_vec();
                let binds = self.bind_done(params, func.rest, args).into_iter().map(|(v, e)| BindIn::Val(v, Init::Done(e))).collect();
                self.open_let(binds, func.body, then);
                then.push(Task::Inlined);
                return then.extend(wraps.into_iter().rev());
            }
            _ => {
                let args = self.out.list(args);
                self.slot_derived.clear();
                self.out.add(Node::App(f, args))
            }
        };
        self.vals.push(made);
        then.extend(wraps.into_iter().rev());
    }

    fn opt_intrinsic(&mut self, prim: Prim, mut args: Vec<Id<'d>>) -> Id<'d> {
        let Prim::Intrinsic(intrinsic) = prim else {
            let args = self.out.list(args);
            self.ran(prim);
            return self.out.add(Node::Intrinsic(prim, args));
        };
        // Float leading `Seq`s and `let`s out of the first argument, which runs before the rest
        // anyway: `(f (seq e x) y ...) -> (seq e (f x y ...))`, so the rules below see `x` itself.
        // A `let`'s variables are unique, so the rest can't refer to them:
        // `(car (let ((x (f))) (cons x 1))) -> (let ((x (f))) x)`.
        let mut wraps = Vec::new();
        while let Some(&first) = args.first() {
            match self.out[first] {
                Node::Seq(prefix, inner) => {
                    wraps.push(Task::Then(prefix));
                    args[0] = inner;
                }
                Node::Let(binds, inner) => {
                    wraps.push(Task::Within(binds));
                    args[0] = inner;
                }
                _ => break,
            }
        }
        let mut made = self.rules(prim, intrinsic, args);
        for wrap in wraps.into_iter().rev() {
            made = match wrap {
                Task::Then(prefix) => self.seq(prefix, made),
                Task::Within(binds) => {
                    if self.out[binds].is_empty() { made } else { self.out.add(Node::Let(binds, made)) }
                }
                _ => unreachable!("only binding forms float out"),
            };
        }
        made
    }

    fn make(&mut self, prim: Prim, args: Vec<Id<'d>>) -> Id<'d> {
        let args = self.out.list(args);
        self.out.add(Node::Intrinsic(prim, args))
    }

    fn truth(&mut self, b: bool) -> Id<'d> {
        self.quote(if b { Value::TRUE } else { Value::FALSE })
    }

    fn rules(&mut self, prim: Prim, intrinsic: Intrinsic, mut args: Vec<Id<'d>>) -> Id<'d> {
        // `(void e ...)` evaluates `e ...` for effect and returns `#<void>`.
        if intrinsic == Intrinsic::Void {
            let void = self.quote(Value::VOID);
            return self.seq_all(args, void);
        }

        // 1. Compile-time constant folding via `Intrinsic::is_pure_foldable`.
        if intrinsic.is_pure_foldable() && args.iter().all(|&a| matches!(self.out[a], Node::Quote(_))) {
            let values: Vec<Value<'gc>> = args
                .iter()
                .map(|&a| match self.out[a] {
                    Node::Quote(v) => v,
                    _ => unreachable!(),
                })
                .collect();
            // A fold that would take long, such as a huge exact `expt`, is left to run.
            let mut fuel = Fuel { run: FOLD_FUEL, rest: 0 };
            if let Ok(val) = intrinsic.run(self.mc, &values, &mut fuel) {
                return self.quote(val);
            }
        }

        // 1b. Constant offsets have one form, `(+ x k)`: `(+ k x)` puts the constant second and
        //     `(- x k)` negates it, so the emitter only looks for one shape for `Op::AddImm`. The
        //     constant is pure, so moving it keeps evaluation order, and `x` faults the same.
        //     `(- x 0)` stays: it keeps `-0.0`, where `(+ x 0)` makes it `0.0`.
        if matches!(intrinsic, Intrinsic::Add | Intrinsic::Sub) && args.len() == 2 {
            let constant = |e: Node<'d, 'gc>| match e {
                Node::Quote(v) => v.as_fixnum(),
                _ => None,
            };
            if intrinsic == Intrinsic::Add && constant(self.out[args[0]]).is_some() && constant(self.out[args[1]]).is_none() {
                args.swap(0, 1);
                return self.make(prim, args);
            }
            if intrinsic == Intrinsic::Sub
                && let Some(neg) = constant(self.out[args[1]]).filter(|&k| k != 0).and_then(i64::checked_neg).and_then(Value::fixnum)
            {
                args[1] = self.quote(neg);
                return self.make(Prim::Intrinsic(Intrinsic::Add), args);
            }
        }

        // A variable known to hold a pair is the `cons` that made it, to the rules below, which
        // then fold it away: but for `list?`, which would make the pair again.
        if args.len() == 1
            && (intrinsic.cxr_step().is_some() || (intrinsic.is_type_predicate() && intrinsic != Intrinsic::IsList))
            && let Node::Ref(v) = self.out[args[0]]
            && let Some(&[head, tail]) = self.known_pairs.get(&v)
        {
            let parts = [self.out.add(head), self.out.add(tail)];
            args[0] = self.make(Prim::Intrinsic(Intrinsic::Cons), parts.to_vec());
        }

        // 2. Store-to-load forwarding for `car`..`cddddr` on `(cons head tail)` while preserving
        //    left-to-right `(head, tail)` evaluation order.
        if let Some((is_car, rest)) = intrinsic.cxr_step()
            && args.len() == 1
            && let Node::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), c) = self.out[args[0]]
            && self.out[c].len() == 2
        {
            let (head, tail) = (self.out[c][0], self.out[c][1]);
            if !is_car {
                let next = match rest {
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec![tail]),
                    None => tail,
                };
                return self.seq(head, next);
            }
            if self.out.is_pure(self.mc, tail) {
                return match rest {
                    Some(r) => self.opt_intrinsic(Prim::Intrinsic(r), vec![head]),
                    None => head,
                };
            }
            let tmp = self.supply.fresh_var();
            let r = self.out.add(Node::Ref(tmp));
            let projected = match rest {
                Some(rest) => self.opt_intrinsic(Prim::Intrinsic(rest), vec![r]),
                None => r,
            };
            let body = self.seq(tail, projected);
            let binds = self.out.list([Bind::Val(tmp, head)]);
            return self.out.add(Node::Let(binds, body));
        }

        // 3. Store-to-load forwarding for `(unbox (box x)) -> x`.
        if intrinsic == Intrinsic::Unbox
            && args.len() == 1
            && let Node::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), b) = self.out[args[0]]
            && self.out[b].len() == 1
        {
            return self.out[b][0];
        }

        // 4. `not` on truthy expressions or known truthy variables: `(not <truthy>) -> (seq <truthy> #f)`.
        if intrinsic == Intrinsic::Not && args.len() == 1 {
            if let Node::Ref(v) = self.out[args[0]]
                && self.truthy_vars.contains(&v)
            {
                return self.truth(false);
            }
            if self.out.is_always_truthy(args[0]) {
                let f = self.truth(false);
                return self.seq(args[0], f);
            }
        }

        // 5. Type predicates on dominating variables or freshly constructed values.
        if intrinsic.is_type_predicate() && args.len() == 1 {
            if let Some(known) = self.of_kind(intrinsic, args[0]) {
                return self.truth(known);
            }
            match self.out[args[0]] {
                Node::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), c) if self.out[c].len() == 2 => {
                    if intrinsic != Intrinsic::IsList {
                        let res = self.truth(intrinsic == Intrinsic::IsPair);
                        return self.seq_all(self.out[c].to_vec(), res);
                    }
                }
                Node::Intrinsic(Prim::Intrinsic(Intrinsic::MakeBox), b) if self.out[b].len() == 1 => {
                    let res = self.truth(intrinsic == Intrinsic::IsBox);
                    return self.seq_all(self.out[b].to_vec(), res);
                }
                Node::Lambda(_) => return self.truth(intrinsic == Intrinsic::IsProcedure),
                _ => {
                    if let Some((_, made)) = self.out.made_struct(self.mc, args[0]) {
                        let res = self.truth(intrinsic == Intrinsic::IsStruct);
                        return self.seq_all(self.out[made][1..].to_vec(), res);
                    }
                }
            }
        }

        // 6. Equality simplifications (`eq?`, `eqv?`, `equal?`):
        //    - Reflexive `(eq? x x) -> #t`
        //    - `(eq? x '()) -> (null? x)` (1-arg intrinsic, no `'()` constant load)
        //    - `(eq? x #f)  -> (not x)`   (1-arg intrinsic, folds away in `if`)
        if matches!(intrinsic, Intrinsic::Eq | Intrinsic::Eqv | Intrinsic::Equal) && args.len() == 2 {
            if let (Node::Ref(a), Node::Ref(b)) = (self.out[args[0]], self.out[args[1]])
                && a == b
                && !self.assigned.contains(&a)
            {
                return self.truth(true);
            }
            if matches!(self.out[args[1]], Node::Quote(Value::NIL)) {
                let x = args.swap_remove(0);
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec![x]);
            }
            if matches!(self.out[args[0]], Node::Quote(Value::NIL)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::IsNull), vec![x]);
            }
            if matches!(self.out[args[1]], Node::Quote(Value::FALSE)) {
                let x = args.swap_remove(0);
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec![x]);
            }
            if matches!(self.out[args[0]], Node::Quote(Value::FALSE)) {
                let x = args.pop().expect("checked 2 eq args");
                return self.opt_intrinsic(Prim::Intrinsic(Intrinsic::Not), vec![x]);
            }
        }

        // 7. Structs: a test or a read of one whose type is known, and what one teaches.
        if let Some(made) = self.struct_rules(intrinsic, &args) {
            return made;
        }
        if matches!(intrinsic, Intrinsic::StructRef | Intrinsic::StructSet)
            && let Some(subject) = self.subject(args[0])
            && let Some(kind) = self.struct_type(args[1])
        {
            self.learn(subject, kind, true);
        }
        self.make(prim, args)
    }

    /// Whether the value of `e` is of the kind the type predicate `pred` tests for, if what's
    /// known of it says.
    fn of_kind(&self, pred: Intrinsic, e: Id<'d>) -> Option<bool> {
        // What's an instance of a struct type is a struct, and of no other kind.
        if let Some(subject) = self.subject(e)
            && self.known(subject).is_some_and(|known| !known.is.is_empty())
        {
            return Some(pred == Intrinsic::IsStruct);
        }
        let Node::Ref(v) = self.out[e] else { return None };
        if let Some(&known) = self.pred_facts.get(&(pred, v)) {
            return Some(known);
        }
        if self.known_structs.contains_key(&v) {
            return Some(pred == Intrinsic::IsStruct);
        }
        // What's known of `v` by another predicate says this one's answer if that one implies
        // it and is true, or it implies that one, which is false, or the two are never both
        // true.
        let known = |holds: bool, tells: &dyn Fn(Intrinsic) -> bool| self.pred_facts.iter().any(|(&(other, u), &val)| u == v && val == holds && tells(other));
        if known(true, &|other| other.implies(pred)) {
            return Some(true);
        }
        if known(false, &|other| pred.implies(other)) || known(true, &|other| pred.is_disjoint_predicate(other)) {
            return Some(false);
        }
        None
    }

    /// Whether `test`, made, is true, if what's known here says so either way.
    fn decided(&self, test: Id<'d>) -> Option<bool> {
        match self.out[test] {
            Node::Quote(v) => Some(v != Value::FALSE),
            Node::Ref(v) if self.truthy_vars.contains(&v) => Some(true),
            Node::Intrinsic(Prim::Intrinsic(Intrinsic::IsStructDerivedFrom), args) if let [tested, kind] = self.out[args] => self.derives(self.subject(tested)?, self.struct_type(kind)?),
            Node::Intrinsic(Prim::Intrinsic(pred), args) if pred.is_type_predicate() && let [tested] = self.out[args] => self.of_kind(pred, tested),
            _ => None,
        }
    }

    /// The procedure a call of `fun` with no arguments is a call of, if `fun` only picks one
    /// to call, by tests that what's known here decides.
    ///
    /// `(lambda () (if (point? x) (matched) (next)))` is such a function: where `x` is known
    /// not to be a point, a call of it is `(next)`.
    fn picked(&self, fun: Fun<'d>) -> Option<Id<'d>> {
        let f = self.out[fun];
        if !self.out[f.params].is_empty() || f.rest.is_some() {
            return None;
        }
        let mut e = f.body;
        while let Node::If(test, t, o) = self.out[e] {
            e = if self.decided(test)? { t } else { o };
        }
        match self.out[e] {
            Node::App(to, args) if self.out[args].is_empty() && matches!(self.out[to], Node::Ref(_)) => Some(to),
            _ => None,
        }
    }

    /// The struct type `e` is, if it's one as a constant.
    fn struct_type(&self, e: Id<'d>) -> Option<Gc<'gc, StructType>> {
        match self.out[e] {
            Node::Quote(kind) => kind.downcast::<StructType>(self.mc),
            _ => None,
        }
    }

    /// What `e` reads, if facts are kept of it: an unassigned variable, or one of the module's.
    fn subject(&self, e: Id<'d>) -> Option<Subject> {
        match self.out[e] {
            Node::Ref(v) if !self.assigned.contains(&v) => Some(Subject::Local(v)),
            Node::Intrinsic(Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, slot), _) => Some(Subject::Slot(slot)),
            _ => None,
        }
    }

    fn known(&self, subject: Subject) -> Option<&Known<'gc>> {
        match subject {
            Subject::Local(v) => self.derived.get(&v),
            Subject::Slot(slot) => self.slot_derived.get(&slot),
        }
    }

    fn known_mut(&mut self, subject: Subject) -> Option<&mut Known<'gc>> {
        match subject {
            Subject::Local(v) => self.derived.get_mut(&v),
            Subject::Slot(slot) => self.slot_derived.get_mut(&slot),
        }
    }

    /// Notes that code which isn't an intrinsic's has run: a request or a host function, which
    /// can call a procedure, or an assignment of a module's variable. What's known of the
    /// module's variables may no longer hold.
    fn ran(&mut self, prim: Prim) {
        if !matches!(prim, Prim::Intrinsic(_) | Prim::Read(_) | Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, _)) {
            self.slot_derived.clear();
        }
    }

    /// Notes that the value of `subject` is an instance of `kind`, if `is`, or that it isn't,
    /// in the code that runs from here.
    fn learn(&mut self, subject: Subject, kind: Gc<'gc, StructType>, is: bool) {
        if self.derives(subject, kind).is_some() {
            return;
        }
        let known = match subject {
            Subject::Local(v) => self.derived.entry(v).or_default(),
            Subject::Slot(slot) => self.slot_derived.entry(slot).or_default(),
        };
        if is {
            known.is.push(kind);
        } else {
            known.isnt.push(kind);
        }
        self.learned.push((subject, is));
    }

    /// Whether the value of `subject` is an instance of `kind`, if that's known either way.
    fn derives(&self, subject: Subject, kind: Gc<'gc, StructType>) -> Option<bool> {
        let mc = self.mc;
        if let Subject::Local(v) = subject
            && let Some(&(made_as, _)) = self.known_structs.get(&v)
        {
            return Some(structs::derives(mc, made_as, kind));
        }
        let known = self.known(subject)?;
        // What isn't an instance of a type isn't one of its subtypes.
        if known.isnt.iter().any(|&isnt| structs::derives(mc, kind, isnt)) {
            return Some(false);
        }
        known.is.iter().find_map(|&is| {
            if structs::derives(mc, is, kind) {
                Some(true)
            } else if structs::derives(mc, kind, is) {
                None
            } else {
                // A value of two types is of one that derives from both, so one of the two
                // derives from the other: these don't.
                Some(false)
            }
        })
    }

    /// What a struct intrinsic on `args` is, by what's known of the struct, if that's simpler
    /// than the call.
    fn struct_rules(&mut self, intrinsic: Intrinsic, args: &[Id<'d>]) -> Option<Id<'d>> {
        let mc = self.mc;
        let index = |this: &Self, e: Id<'d>| match this.out[e] {
            Node::Quote(k) => k.as_fixnum().and_then(|k| usize::try_from(k).ok()),
            _ => None,
        };
        match (intrinsic, args) {
            (Intrinsic::IsStructDerivedFrom, &[tested, kind]) => {
                let kind = self.struct_type(kind)?;
                if let Some(subject) = self.subject(tested) {
                    return self.derives(subject, kind).map(|known| self.truth(known));
                }
                let (made_as, made) = self.out.made_struct(mc, tested)?;
                let res = self.truth(structs::derives(mc, made_as, kind));
                Some(self.seq_all(self.out[made][1..].to_vec(), res))
            }
            // A field that can't be set, of a variable bound to a new struct, is what the
            // struct was made with.
            (Intrinsic::StructField | Intrinsic::StructFixedField, &[read, at]) => {
                let (Node::Ref(v), k) = (self.out[read], index(self, at)?) else { return None };
                let (made_as, parts) = self.known_structs.get(&v)?;
                if structs::is_mutable(mc, *made_as, k) {
                    return None;
                }
                let part = *parts.get(k)?;
                Some(self.out.add(part))
            }
            (Intrinsic::StructRef, &[read, kind, at]) => {
                let (kind, k) = (self.struct_type(kind)?, index(self, at)?);
                if k >= kind.fields(mc) as usize {
                    return None;
                }
                if let Some(subject) = self.subject(read) {
                    if self.derives(subject, kind) != Some(true) {
                        return None;
                    }
                    // The type's known, so the read checks nothing: and a field that can't be
                    // set is the same whenever it's read.
                    let unchecked = if structs::is_mutable(mc, kind, k) { Intrinsic::StructField } else { Intrinsic::StructFixedField };
                    return Some(self.opt_intrinsic(Prim::Intrinsic(unchecked), vec![read, at]));
                }
                // A struct made only to be read is the value it was given for the field, once
                // the others are evaluated, in order.
                let (made_as, made) = self.out.made_struct(mc, read)?;
                if !structs::derives(mc, made_as, kind) {
                    return None;
                }
                let (mut binds, mut field) = (Vec::new(), None);
                for (i, &value) in self.out[made][1..].to_vec().iter().enumerate() {
                    let mut part = value;
                    if !self.copyable(value) {
                        let bound = self.supply.fresh_var();
                        binds.push(Bind::Val(bound, value));
                        part = self.out.add(Node::Ref(bound));
                    }
                    if i == k {
                        field = Some(part);
                    }
                }
                let field = field.expect("a value for each field");
                if binds.is_empty() {
                    return Some(field);
                }
                let binds = self.out.list(binds);
                Some(self.out.add(Node::Let(binds, field)))
            }
            _ => None,
        }
    }

    /// Whether `fun`, still source, is small enough to copy to its calls as it's written.
    fn small_as_written(&self, fun: Fun<'s>) -> bool {
        let params_unassigned = !self.src.params(fun).any(|param| self.assigned.contains(&param));
        params_unassigned && small(self.src, &self.assigned, self.src[fun].body, &mut 0)
    }

    fn is_small_inlinable(&self, fun: Fun<'d>) -> bool {
        if self.out.params(fun).any(|v| self.assigned.contains(&v)) {
            return false;
        }
        small(self.out, &self.assigned, self.out[fun].body, &mut 0)
    }

    /// A copy of `fun`, a small function, into the source, its variables fresh.
    fn alpha_rename(&mut self, fun: Fun<'d>) -> Fun<'s> {
        let f = self.out[fun];
        let mut map = HashMap::default();
        let params: Vec<Var> = self.out[f.params]
            .iter()
            .map(|&v| {
                let fresh = self.supply.fresh_var();
                map.insert(v, fresh);
                fresh
            })
            .collect();
        let rest = f.rest.map(|v| {
            let fresh = self.supply.fresh_var();
            map.insert(v, fresh);
            fresh
        });
        let body = self.rename(f.body, &mut map);
        let params = self.src.list(params);
        let id = self.supply.fresh_lambda();
        self.src.function(Function { id, params, optional: f.optional, rest, body })
    }

    /// `e`, of a small function, into the source with its variables renamed by `map`.
    fn rename(&mut self, e: Id<'d>, map: &mut HashMap<Var, Var>) -> Id<'s> {
        let node = match self.out[e] {
            Node::Quote(v) => Node::Quote(v),
            Node::Ref(v) => Node::Ref(map.get(&v).copied().unwrap_or(v)),
            Node::If(a, b, c) => {
                let (a, b) = (self.rename(a, map), self.rename(b, map));
                Node::If(a, b, self.rename(c, map))
            }
            Node::Seq(a, b) => {
                let a = self.rename(a, map);
                Node::Seq(a, self.rename(b, map))
            }
            Node::Let(binds, body) => {
                let mut renamed = Vec::with_capacity(self.out[binds].len());
                for i in 0..self.out[binds].len() {
                    let Bind::Val(v, init) = self.out[binds][i] else { unreachable!("small inlinable functions have no Fix") };
                    let init = self.rename(init, map);
                    let fresh = self.supply.fresh_var();
                    map.insert(v, fresh);
                    renamed.push(Bind::Val(fresh, init));
                }
                let body = self.rename(body, map);
                Node::Let(self.src.list(renamed), body)
            }
            Node::App(f, args) => {
                let f = self.rename(f, map);
                Node::App(f, self.rename_all(args, map))
            }
            Node::Intrinsic(prim, args) => Node::Intrinsic(prim, self.rename_all(args, map)),
            Node::ApplyIntrinsic(prim, args) => Node::ApplyIntrinsic(prim, self.rename_all(args, map)),
            Node::Set(..) | Node::Lambda(_) => unreachable!("small inlinable functions have no Set/Lambda"),
        };
        self.src.add(node)
    }

    fn rename_all(&mut self, args: Span<'d, Id<'d>>, map: &mut HashMap<Var, Var>) -> Span<'s, Id<'s>> {
        let renamed: Vec<Id<'s>> = (0..self.out[args].len()).map(|i| self.rename(self.out[args][i], map)).collect();
        self.src.list(renamed)
    }
}

/// Whether `e` of `tree` is small enough to copy to where it's used, `size` being how much has
/// been counted already. It stops looking as soon as it isn't, so it goes no deeper than
/// [`MAX_INLINE_SIZE`].
fn small<'x>(tree: &L2<'x, '_>, assigned: &HashSet<Var>, e: Id<'x>, size: &mut usize) -> bool {
    *size += 1;
    if *size > MAX_INLINE_SIZE {
        return false;
    }
    match tree[e] {
        Node::Quote(_) => true,
        Node::Ref(v) => !assigned.contains(&v),
        Node::If(a, b, c) => [a, b, c].into_iter().all(|part| small(tree, assigned, part, size)),
        Node::Seq(a, b) => small(tree, assigned, a, size) && small(tree, assigned, b, size),
        Node::Let(binds, body) => {
            tree[binds].iter().all(|&b| matches!(b, Bind::Val(v, init) if !assigned.contains(&v) && small(tree, assigned, init, size))) && small(tree, assigned, body, size)
        }
        Node::Set(..) | Node::Lambda(_) => false,
        Node::App(f, args) => small(tree, assigned, f, size) && tree[args].iter().all(|&a| small(tree, assigned, a, size)),
        Node::Intrinsic(_, args) | Node::ApplyIntrinsic(_, args) => tree[args].iter().all(|&a| small(tree, assigned, a, size)),
    }
}

/// Whether `fun` takes `argc` arguments, of which a rest list it's inlined with has few enough.
fn takes<'x>(tree: &L2<'x, '_>, fun: Fun<'x>, argc: usize) -> bool {
    let f = tree[fun];
    let (most, least) = (tree[f.params].len(), tree[f.params].len() - f.optional as usize);
    match f.rest {
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
