//! Contification (`L3 -> L3`): local functions that are joins, code in the frame that calls jump to.
//!
//! A function is one when each use of it is a call, with as many arguments as it has parameters,
//! and all of them are in tail position of one expression, `P`, with no lambda between: they all
//! return what `P` does, so its code can go at `P` and the calls can jump to it. The functions a
//! `Fix` binds are one group, joins together, when the calls from outside them are so, and those
//! in their code are in tail position of it. `P` is where the calls' tail positions meet, the
//! nearest node above them all. A call in a join's code is where that join is, as the code is
//! there. A loop is a group whose code goes at the call that starts it. `P` can be in a lambda
//! inside the one that binds the function, when every call is in it, if that doesn't have the
//! lambdas between capture more: their captures of the function go, its code's come.
//!
//! The analysis walks the tree once, numbering its nodes in order and noting each one's *chain*:
//! the nodes from the top of the run of tail positions it's at the bottom of down to it. Calls
//! whose chains start at the same node are in tail position of each node their chains share, so
//! `P` is the last of those. Functions are decided innermost first, as one can only call those
//! it's inside the scope of. A second walk, numbering the nodes the same way, moves each join's
//! code to its `P`, as an [`L3::Join`], and makes the calls [`L3::Jump`]s.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

use ragwort_types::gc::Value;

use crate::Func;
use crate::Var;
use crate::ir::L3;

/// Most parameters a group of joins can have, as their values move in its own registers.
const MAX_PARAMS: usize = 32;

/// A hasher for node numbers and variables, which are spread already.
#[derive(Default)]
struct Mix(u64);

impl Hasher for Mix {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(u64::from(b));
        }
    }

    fn write_u32(&mut self, n: u32) {
        self.write_u64(u64::from(n));
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0 ^ n).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(26);
    }
}

type Quick = BuildHasherDefault<Mix>;

pub(crate) fn contify(expr: &mut L3<'_>) {
    let mut survey = Survey::default();
    survey.tail(expr);
    let plan = survey.decide();
    if !plan.joins.is_empty() {
        Rewrite { plan, next: 0, moved: HashMap::default() }.visit(expr);
    }
}

/// What contification decided.
#[derive(Default)]
struct Plan {
    /// The groups of joins whose code goes at each node, by number, those decided first innermost.
    at: HashMap<u32, Vec<Vec<Var>>, Quick>,
    joins: HashSet<Var, Quick>,
}

/// A local function that could be a join.
struct Candidate {
    arity: usize,
    /// Whether every use so far is a call of `arity` arguments.
    called: bool,
    /// Each call's chain, as node numbers, and the frame it's in.
    calls: Vec<(Box<[u32]>, u32)>,
}

/// A binding of candidates, which are decided together.
struct Binding {
    members: Vec<Var>,
    frame: u32,
}

/// A lambda body's frame.
struct Frame<'a, 'gc> {
    /// The frame the lambda is in.
    outer: u32,
    lambda: &'a Func<L3<'gc>>,
    /// The candidate it's the code of.
    of: Option<Var>,
}

#[derive(Default)]
struct Survey<'a, 'gc> {
    candidates: HashMap<Var, Candidate, Quick>,
    funcs: HashMap<Var, &'a Func<L3<'gc>>, Quick>,
    /// The candidate whose code each function body is, by the body's number.
    bodies: HashMap<u32, Var, Quick>,
    /// Bindings, innermost first.
    bindings: Vec<Binding>,
    /// The nodes from the walk's top to where it is; the current chain is `chain[base..]`.
    chain: Vec<u32>,
    base: usize,
    frame: u32,
    /// Frame `n`'s at `n - 1`.
    frames: Vec<Frame<'a, 'gc>>,
    /// The next node's number.
    next: u32,
}

impl<'a, 'gc> Survey<'a, 'gc> {
    /// `e`, in tail position of the node above it.
    fn tail(&mut self, e: &'a L3<'gc>) {
        self.chain.push(self.next);
        self.next += 1;
        self.node(e);
        self.chain.pop();
    }

    /// `e`, which starts a chain.
    fn fresh(&mut self, e: &'a L3<'gc>) {
        let base = std::mem::replace(&mut self.base, self.chain.len());
        self.tail(e);
        self.base = base;
    }

    /// The body of `func`, a frame of its own, which is candidate `of`'s code.
    fn body(&mut self, func: &'a Func<L3<'gc>>, of: Option<Var>) {
        if let Some(v) = of {
            self.bodies.insert(self.next, v);
        }
        self.frames.push(Frame { outer: self.frame, lambda: func, of });
        let frame = std::mem::replace(&mut self.frame, self.frames.len() as u32);
        self.fresh(&func.body);
        self.frame = frame;
    }

    fn node(&mut self, e: &'a L3<'gc>) {
        match e {
            L3::Quote(_) => {}
            L3::Ref(v) => {
                if let Some(c) = self.candidates.get_mut(v) {
                    c.called = false;
                }
            }
            L3::Set(v, value) => {
                if let Some(c) = self.candidates.get_mut(v) {
                    c.called = false;
                }
                self.fresh(value);
            }
            L3::If(test, then, other) => {
                self.fresh(test);
                self.tail(then);
                self.tail(other);
            }
            L3::Seq(a, b) => {
                self.fresh(a);
                self.tail(b);
            }
            L3::Let(binds, body) => self.binds(binds, body),
            L3::Fix(binds, body) => self.fix(binds, body),
            L3::App(f, args) => {
                match **f {
                    L3::Ref(v) if self.candidates.contains_key(&v) => {
                        self.next += 1;
                        let chain = self.chain[self.base..].into();
                        let c = self.candidates.get_mut(&v).expect("a candidate");
                        if c.arity == args.len() {
                            c.calls.push((chain, self.frame));
                        } else {
                            c.called = false;
                        }
                    }
                    _ => self.fresh(f),
                }
                for a in args {
                    self.fresh(a);
                }
            }
            L3::Lambda(func) => self.body(func, None),
            L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => {
                for a in args {
                    self.fresh(a);
                }
            }
            L3::Join { group, scope } => {
                for (_, func) in group {
                    self.fresh(&func.body);
                }
                self.tail(scope);
            }
        }
    }

    /// Notes `var`, bound to `func`, as a candidate if it can be one.
    fn candidate(&mut self, var: Var, func: &'a Func<L3<'gc>>) -> bool {
        let fits = func.rest.is_none() && func.optional == 0 && func.params.len() <= MAX_PARAMS;
        if fits {
            self.candidates.insert(var, Candidate { arity: func.params.len(), called: true, calls: Vec::new() });
            self.funcs.insert(var, func);
        }
        fits
    }

    #[inline(never)]
    fn binds(&mut self, binds: &'a [(Var, L3<'gc>)], body: &'a L3<'gc>) {
        let mut mine = Vec::new();
        for &(v, ref init) in binds {
            match init {
                L3::Lambda(func) => {
                    self.next += 1;
                    let fits = self.candidate(v, func);
                    if fits {
                        mine.push(Binding { members: vec![v], frame: self.frame });
                    }
                    self.body(func, fits.then_some(v));
                }
                _ => self.fresh(init),
            }
        }
        self.tail(body);
        // After those inside it, which are decided first.
        self.bindings.extend(mine);
    }

    #[inline(never)]
    fn fix(&mut self, binds: &'a [(Var, Func<L3<'gc>>)], body: &'a L3<'gc>) {
        let fits: Vec<bool> = binds.iter().map(|(v, func)| self.candidate(*v, func)).collect();
        for ((v, func), &fits) in binds.iter().zip(&fits) {
            self.body(func, fits.then_some(*v));
        }
        self.tail(body);
        // The group's parameters all have registers across the code the joins are placed at.
        if fits.iter().all(|&f| f) && binds.iter().map(|(_, f)| f.params.len()).sum::<usize>() <= MAX_PARAMS {
            self.bindings.push(Binding { members: binds.iter().map(|(v, _)| *v).collect(), frame: self.frame });
        }
    }

    fn decide(self) -> Plan {
        let mut plan = Plan::default();
        // Where each join decided on is: the chain down to it, and its frame.
        let mut placed: HashMap<Var, (Vec<u32>, u32), Quick> = HashMap::default();
        for binding in &self.bindings {
            let members = &binding.members;
            if !members.iter().all(|v| self.candidates[v].called) {
                continue;
            }
            let mut common: Option<(Vec<u32>, u32)> = None;
            let mut fits = true;
            'calls: for v in members {
                for (chain, frame) in &self.candidates[v].calls {
                    // Through each join whose code it's in, which may be in another's, decided after.
                    let (mut chain, mut frame) = (chain.to_vec(), *frame);
                    while let Some((at, f)) = self.bodies.get(&chain[0]).and_then(|w| placed.get(w)) {
                        chain = at.iter().chain(&chain).copied().collect();
                        frame = *f;
                    }
                    // A call in a member's own code goes to it from there.
                    if self.bodies.get(&chain[0]).is_some_and(|w| members.contains(w)) {
                        continue;
                    }
                    match &mut common {
                        None => common = Some((chain, frame)),
                        Some((shared, other)) => {
                            if shared[0] != chain[0] || *other != frame {
                                fits = false;
                                break 'calls;
                            }
                            let n = shared.iter().zip(&chain).take_while(|(a, b)| a == b).count();
                            shared.truncate(n);
                        }
                    }
                }
            }
            let Some((chain, frame)) = common.filter(|&(_, frame)| fits && (frame == binding.frame || self.moves(binding, frame))) else { continue };
            plan.at.entry(*chain.last().expect("a chain has its call")).or_default().push(members.clone());
            plan.joins.extend(members);
            for &v in members {
                placed.insert(v, (chain.clone(), frame));
            }
        }
        plan
    }

    /// Whether `binding`'s functions' code can go in `frame`, inside the frame that binds them and
    /// not in their own: if none of the lambdas between captures more than it does now.
    fn moves(&self, binding: &Binding, frame: u32) -> bool {
        let (mut uses, mut bound) = (HashSet::default(), HashSet::default());
        for v in &binding.members {
            bound.insert(*v);
            vars(self.funcs[v], &mut uses, &mut bound);
        }
        let uses: Vec<Var> = uses.difference(&bound).copied().collect();
        let mut at = frame;
        while at != binding.frame {
            let Some(between) = at.checked_sub(1).and_then(|i| self.frames.get(i as usize)) else { return false };
            if between.of.is_some_and(|v| binding.members.contains(&v)) {
                return false;
            }
            let (mut captured, mut inside) = (HashSet::default(), HashSet::default());
            vars(between.lambda, &mut captured, &mut inside);
            let gone = binding.members.iter().filter(|v| captured.contains(v)).count();
            let come = uses.iter().filter(|v| !captured.contains(v)).count();
            if come > gone {
                return false;
            }
            at = between.outer;
        }
        true
    }
}

/// Adds the variables `func` refers to to `uses`, and those it binds to `bound`.
fn vars<'gc>(func: &Func<L3<'gc>>, uses: &mut HashSet<Var, Quick>, bound: &mut HashSet<Var, Quick>) {
    bound.extend(func.params.iter().chain(&func.rest));
    walk(&func.body, uses, bound);
}

fn walk<'gc>(e: &L3<'gc>, uses: &mut HashSet<Var, Quick>, bound: &mut HashSet<Var, Quick>) {
    match e {
        L3::Quote(_) => {}
        L3::Ref(v) => {
            uses.insert(*v);
        }
        L3::Set(v, value) => {
            uses.insert(*v);
            walk(value, uses, bound);
        }
        L3::If(a, b, c) => {
            walk(a, uses, bound);
            walk(b, uses, bound);
            walk(c, uses, bound);
        }
        L3::Seq(a, b) => {
            walk(a, uses, bound);
            walk(b, uses, bound);
        }
        L3::Let(binds, body) => {
            for (v, init) in binds {
                bound.insert(*v);
                walk(init, uses, bound);
            }
            walk(body, uses, bound);
        }
        L3::Fix(binds, body) | L3::Join { group: binds, scope: body } => {
            for (v, func) in binds {
                bound.insert(*v);
                vars(func, uses, bound);
            }
            walk(body, uses, bound);
        }
        L3::App(f, args) => {
            walk(f, uses, bound);
            for a in args {
                walk(a, uses, bound);
            }
        }
        L3::Lambda(func) => vars(func, uses, bound),
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => {
            for a in args {
                walk(a, uses, bound);
            }
        }
    }
}

/// The second walk, which numbers the nodes as [`Survey`] does.
struct Rewrite<'gc> {
    plan: Plan,
    next: u32,
    /// The joins' code, taken from where they're bound, until it goes where they're placed.
    moved: HashMap<Var, Func<L3<'gc>>, Quick>,
}

/// What a node is left as while it's moved.
fn hole<'gc>() -> L3<'gc> {
    L3::Quote(Value::FALSE)
}

impl<'gc> Rewrite<'gc> {
    fn visit(&mut self, e: &mut L3<'gc>) {
        let n = self.next;
        self.next += 1;
        match e {
            L3::Quote(_) | L3::Ref(_) => {}
            L3::Set(_, value) => self.visit(value),
            L3::If(a, b, c) => {
                self.visit(a);
                self.visit(b);
                self.visit(c);
            }
            L3::Seq(a, b) => {
                self.visit(a);
                self.visit(b);
            }
            L3::Let(..) => self.binds(e),
            L3::Fix(..) => self.fix(e),
            L3::App(..) => self.app(e),
            L3::Lambda(func) => self.visit(&mut func.body),
            L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => {
                for a in args {
                    self.visit(a);
                }
            }
            L3::Join { group, scope } => {
                for (_, func) in group {
                    self.visit(&mut func.body);
                }
                self.visit(scope);
            }
        }
        if let Some(groups) = self.plan.at.remove(&n) {
            self.place(e, groups);
        }
    }

    /// Puts `groups`' code around `e`, those decided first innermost.
    #[inline(never)]
    fn place(&mut self, e: &mut L3<'gc>, groups: Vec<Vec<Var>>) {
        for group in groups {
            let group = group.into_iter().map(|v| (v, self.moved.remove(&v).expect("a join is bound before where it goes"))).collect();
            let scope = Box::new(std::mem::replace(e, hole()));
            *e = L3::Join { group, scope };
        }
    }

    #[inline(never)]
    fn binds(&mut self, e: &mut L3<'gc>) {
        let L3::Let(binds, body) = e else { return };
        for (_, init) in binds.iter_mut() {
            self.visit(init);
        }
        if binds.iter().any(|(v, _)| self.plan.joins.contains(v)) {
            for (v, init) in std::mem::take(binds) {
                match init {
                    L3::Lambda(func) if self.plan.joins.contains(&v) => {
                        self.moved.insert(v, func);
                    }
                    init => binds.push((v, init)),
                }
            }
        }
        self.visit(body);
        if binds.is_empty() {
            *e = std::mem::replace(&mut **body, hole());
        }
    }

    #[inline(never)]
    fn fix(&mut self, e: &mut L3<'gc>) {
        let L3::Fix(binds, body) = e else { return };
        for (_, func) in binds.iter_mut() {
            self.visit(&mut func.body);
        }
        if binds.iter().any(|(v, _)| self.plan.joins.contains(v)) {
            for (v, func) in std::mem::take(binds) {
                if self.plan.joins.contains(&v) {
                    self.moved.insert(v, func);
                } else {
                    binds.push((v, func));
                }
            }
        }
        self.visit(body);
        if binds.is_empty() {
            *e = std::mem::replace(&mut **body, hole());
        }
    }

    #[inline(never)]
    fn app(&mut self, e: &mut L3<'gc>) {
        let L3::App(f, args) = e else { return };
        let join = match **f {
            L3::Ref(v) if self.plan.joins.contains(&v) => Some(v),
            _ => None,
        };
        match join {
            Some(_) => self.next += 1,
            None => self.visit(f),
        }
        for a in args.iter_mut() {
            self.visit(a);
        }
        if let Some(v) = join {
            *e = L3::Jump(v, std::mem::take(args));
        }
    }
}
