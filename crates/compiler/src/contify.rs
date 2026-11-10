//! Contification (`L3 -> L3`): local functions that are joins, code in the frame that calls jump to.
//!
//! A function is one when each use of it is a call, with as many arguments as it has parameters,
//! and all of them are in tail position of one expression, `P`, with no lambda between: they all
//! return what `P` does, so its code can go at `P` and the calls can jump to it. The functions a
//! `Fix` binding binds are one group, joins together, when the calls from outside them are so,
//! and those in their code are in tail position of it. `P` is where the calls' tail positions meet, the
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

use crate::hash::{HashMap, HashSet};


use ragwort_alloc::{Arena, CollectIn};

use crate::Var;
use crate::ir::{Bind, Bind3, Func, L3};
use crate::lower::MAX_DEPTH;

/// Most parameters a group of joins can have, as their values move in its own registers.
const MAX_PARAMS: usize = 32;

pub(crate) fn contify<'a>(arena: &'a Arena, expr: &mut L3<'a, '_>) {
    let mut survey = Survey::default();
    survey.tail(expr);
    let plan = survey.decide();
    if !plan.joins.is_empty() {
        let mut rewrite = Rewrite { arena, plan, next: 0, moved: HashMap::default(), depth: 0, refused: HashMap::default(), doomed: HashSet::default() };
        rewrite.visit(expr);
    }
}

/// What contification decided.
#[derive(Default)]
struct Plan {
    /// The groups of joins whose code goes at each node, by number, those decided first innermost.
    at: HashMap<u32, Vec<Vec<Var>>>,
    joins: HashSet<Var>,
}

/// A local function that could be a join.
struct Candidate {
    arity: usize,
    /// Whether every use so far is a call of `arity` arguments.
    called: bool,
    calls: Vec<Site<Box<[u32]>>>,
}

/// Where a call is, or a join goes: the chain down to it, as node numbers, and the frame it's in.
struct Site<C> {
    chain: C,
    frame: u32,
}

/// A binding of candidates, which are decided together.
struct Binding {
    members: Vec<Var>,
    frame: u32,
}

/// A lambda body's frame.
struct Frame<'s, 't, 'gc> {
    /// The frame the lambda is in.
    outer: u32,
    lambda: &'s Func<'t, L3<'t, 'gc>>,
    /// The candidate it's the code of.
    of: Option<Var>,
}

#[derive(Default)]
struct Survey<'s, 't, 'gc> {
    candidates: HashMap<Var, Candidate>,
    funcs: HashMap<Var, &'s Func<'t, L3<'t, 'gc>>>,
    /// The candidate whose code each function body is, by the body's number.
    bodies: HashMap<u32, Var>,
    /// Bindings, innermost first.
    bindings: Vec<Binding>,
    /// The nodes from the walk's top to where it is; the current chain is `chain[base..]`.
    chain: Vec<u32>,
    base: usize,
    frame: u32,
    /// Frame `n`'s at `n - 1`.
    frames: Vec<Frame<'s, 't, 'gc>>,
    /// The next node's number.
    next: u32,
}

impl<'s, 't, 'gc> Survey<'s, 't, 'gc> {
    /// `e`, in tail position of the node above it.
    fn tail(&mut self, e: &'s L3<'t, 'gc>) {
        self.chain.push(self.next);
        self.next += 1;
        self.node(e);
        self.chain.pop();
    }

    /// `e`, which starts a chain.
    fn fresh(&mut self, e: &'s L3<'t, 'gc>) {
        let base = std::mem::replace(&mut self.base, self.chain.len());
        self.tail(e);
        self.base = base;
    }

    /// The body of `func`, a frame of its own, which is candidate `of`'s code.
    fn body(&mut self, func: &'s Func<'t, L3<'t, 'gc>>, of: Option<Var>) {
        if let Some(v) = of {
            self.bodies.insert(self.next, v);
        }
        self.frames.push(Frame { outer: self.frame, lambda: func, of });
        let frame = std::mem::replace(&mut self.frame, self.frames.len() as u32);
        self.fresh(&func.body);
        self.frame = frame;
    }

    fn node(&mut self, e: &'s L3<'t, 'gc>) {
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
            L3::App(f, args) => {
                match **f {
                    L3::Ref(v) if self.candidates.contains_key(&v) => {
                        self.next += 1;
                        let chain = self.chain[self.base..].into();
                        let c = self.candidates.get_mut(&v).expect("a candidate");
                        if c.arity == args.len() {
                            c.calls.push(Site { chain, frame: self.frame });
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
    fn candidate(&mut self, var: Var, func: &'s Func<'t, L3<'t, 'gc>>) -> bool {
        let fits = func.rest.is_none() && func.optional == 0 && func.params.len() <= MAX_PARAMS;
        if fits {
            self.candidates.insert(var, Candidate { arity: func.params.len(), called: true, calls: Vec::new() });
            self.funcs.insert(var, func);
        }
        fits
    }

    #[inline(never)]
    fn binds(&mut self, binds: &'s [Bind3<'t, 'gc>], body: &'s L3<'t, 'gc>) {
        let mut mine = Vec::new();
        for bind in binds {
            match bind {
                Bind::Val(v, L3::Lambda(func)) => {
                    self.next += 1;
                    let fits = self.candidate(*v, func);
                    if fits {
                        mine.push(Binding { members: vec![*v], frame: self.frame });
                    }
                    self.body(func, fits.then_some(*v));
                }
                Bind::Val(_, init) => self.fresh(init),
                Bind::Fix(group) => {
                    let fits: Vec<bool> = group.iter().map(|(v, func)| self.candidate(*v, func)).collect();
                    for ((v, func), &fits) in group.iter().zip(&fits) {
                        self.body(func, fits.then_some(*v));
                    }
                    // The group's parameters all have registers across the code the joins are placed at.
                    if fits.iter().all(|&f| f) && group.iter().map(|(_, f)| f.params.len()).sum::<usize>() <= MAX_PARAMS {
                        mine.push(Binding { members: group.iter().map(|(v, _)| *v).collect(), frame: self.frame });
                    }
                }
            }
        }
        self.tail(body);
        // After those inside it, which are decided first, and the last first, as it's in the
        // scope of those before.
        self.bindings.extend(mine.into_iter().rev());
    }

    fn decide(self) -> Plan {
        let mut plan = Plan::default();
        // Where each join decided on is.
        let mut placed: HashMap<Var, Site<Vec<u32>>> = HashMap::default();
        for binding in &self.bindings {
            let members = &binding.members;
            if !members.iter().all(|v| self.candidates[v].called) {
                continue;
            }
            let mut common: Option<Site<Vec<u32>>> = None;
            let mut fits = true;
            'calls: for v in members {
                for call in &self.candidates[v].calls {
                    // Through each join whose code it's in, which may be in another's, decided after.
                    let mut chain = call.chain.to_vec();
                    let mut frame = call.frame;
                    while let Some(join) = self.bodies.get(&chain[0]).and_then(|w| placed.get(w)) {
                        chain = join.chain.iter().chain(&chain).copied().collect();
                        frame = join.frame;
                    }
                    // A call in a member's own code goes to it from there.
                    if self.bodies.get(&chain[0]).is_some_and(|w| members.contains(w)) {
                        continue;
                    }
                    match &mut common {
                        None => common = Some(Site { chain, frame }),
                        Some(Site { chain: shared, frame: other }) => {
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
            let Some(Site { chain, frame }) = common.filter(|site| fits && (site.frame == binding.frame || self.moves(binding, site.frame))) else {
                continue;
            };
            plan.at.entry(*chain.last().expect("a chain has its call")).or_default().push(members.clone());
            plan.joins.extend(members);
            for &v in members {
                placed.insert(v, Site { chain: chain.clone(), frame });
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
fn vars(func: &Func<'_, L3<'_, '_>>, uses: &mut HashSet<Var>, bound: &mut HashSet<Var>) {
    bound.extend(func.params.iter().chain(&func.rest));
    walk(&func.body, uses, bound);
}

fn walk(e: &L3<'_, '_>, uses: &mut HashSet<Var>, bound: &mut HashSet<Var>) {
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
            for bind in binds {
                match bind {
                    Bind::Val(v, init) => {
                        bound.insert(*v);
                        walk(init, uses, bound);
                    }
                    Bind::Fix(group) => {
                        for (v, func) in group {
                            bound.insert(*v);
                            vars(func, uses, bound);
                        }
                    }
                }
            }
            walk(body, uses, bound);
        }
        L3::Join { group: binds, scope: body } => {
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
struct Rewrite<'a, 'gc> {
    arena: &'a Arena,
    plan: Plan,
    next: u32,
    /// The joins' code, taken from where they're bound, until it goes where they're placed.
    moved: HashMap<Var, Moved<'a, 'gc>>,
    /// How deeply the node being visited is nested.
    depth: usize,
    /// The code of joins that would nest too deeply where they go, so stay functions, until it's
    /// back where they're bound.
    refused: HashMap<Var, Moved<'a, 'gc>>,
    /// Joins code that stays a function jumps to, which can't be joins either.
    doomed: HashSet<Var>,
}

/// A join's code, how tall it is, and how deeply it's nested where it's bound.
struct Moved<'a, 'gc> {
    code: Func<'a, L3<'a, 'gc>>,
    height: usize,
    site: usize,
}

impl<'a, 'gc> Rewrite<'a, 'gc> {
    /// Rewrites `e`, and returns how tall it is.
    fn visit(&mut self, e: &mut L3<'a, 'gc>) -> usize {
        let n = self.next;
        self.next += 1;
        self.depth += 1;
        let height = 1 + match e {
            L3::Quote(_) | L3::Ref(_) => 0,
            L3::Set(_, value) => self.visit(value),
            L3::If(a, b, c) => {
                let (a, b) = (self.visit(a), self.visit(b));
                a.max(b).max(self.visit(c))
            }
            L3::Seq(a, b) => {
                let a = self.visit(a);
                a.max(self.visit(b))
            }
            L3::Let(..) => self.binds(e),
            L3::App(..) => self.app(e),
            L3::Lambda(func) => self.visit(&mut func.body),
            L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => args.iter_mut().map(|a| self.visit(a)).fold(0, usize::max),
            L3::Join { group, scope } => {
                let code = group.iter_mut().map(|(_, func)| self.visit(&mut func.body)).fold(0, usize::max);
                code.max(self.visit(scope))
            }
        };
        let height = match self.plan.at.remove(&n) {
            Some(groups) => self.place(e, groups, height),
            None => height,
        };
        self.depth -= 1;
        height
    }

    /// Puts `groups`' code around `e`, of `height`, as one group, so however many go there it's
    /// one `Join`, and returns how tall that is. A group whose code would go deeper than source
    /// can nest, and than it was, stays where it's bound, as later passes recurse through it.
    #[inline(never)]
    fn place(&mut self, e: &mut L3<'a, 'gc>, groups: Vec<Vec<Var>>, height: usize) -> usize {
        let groups: std::vec::Vec<(Vec<Var>, std::vec::Vec<Moved<'a, 'gc>>)> = groups
            .into_iter()
            .map(|members| {
                let codes = members.iter().map(|v| self.moved.remove(v).expect("a join is bound before where it goes")).collect();
                (members, codes)
            })
            .collect();
        let fits = |codes: &[Moved<'_, '_>]| codes.iter().all(|m| self.depth + 1 + m.height <= MAX_DEPTH.max(m.site + 1 + m.height));
        let mut kept: std::vec::Vec<bool> =
            groups.iter().map(|(members, codes)| fits(codes) && !members.iter().any(|v| self.doomed.contains(v))).collect();
        // What code that stays jumps to from outside it can't be a join either, here or above.
        let mut back = HashSet::default();
        let mut gone = vec![false; groups.len()];
        while let Some(i) = (0..groups.len()).find(|&i| !kept[i] && !gone[i]) {
            gone[i] = true;
            back.extend(groups[i].0.iter().copied());
            let (mut targets, mut joined) = (HashSet::default(), HashSet::default());
            for m in &groups[i].1 {
                jumps(&m.code.body, &mut targets, &mut joined);
            }
            for v in targets.difference(&joined) {
                self.doomed.insert(*v);
                for (j, (members, _)) in groups.iter().enumerate() {
                    if members.contains(v) {
                        kept[j] = false;
                    }
                }
            }
        }
        let mut group = self.arena.vec();
        let mut tallest = height;
        for ((members, codes), kept) in groups.into_iter().zip(kept) {
            for (v, mut m) in members.into_iter().zip(codes) {
                if kept {
                    tallest = tallest.max(m.height + 1);
                    group.push((v, m.code));
                } else {
                    self.plan.joins.remove(&v);
                    let doomed = &self.doomed;
                    unjump(self.arena, &mut m.code.body, &|w| back.contains(&w) || doomed.contains(&w));
                    self.refused.insert(v, m);
                }
            }
        }
        if !back.is_empty() {
            unjump(self.arena, e, &|w| back.contains(&w));
            for (_, code) in group.iter_mut() {
                unjump(self.arena, &mut code.body, &|w| back.contains(&w));
            }
        }
        if group.is_empty() {
            return height;
        }
        let scope = self.arena.boxed(e.take());
        *e = L3::Join { group, scope };
        tallest + 1
    }

    #[inline(never)]
    fn binds(&mut self, e: &mut L3<'a, 'gc>) -> usize {
        let L3::Let(binds, body) = e else { return 0 };
        let arena = self.arena;
        let site = self.depth;
        let mut height = 0;
        // Where each binding of joins was among those left, to put back those refused.
        let mut slots = std::vec::Vec::new();
        for mut bind in std::mem::replace(binds, arena.vec()) {
            let heights: std::vec::Vec<usize> = match &mut bind {
                Bind::Val(_, init) => vec![self.visit(init)],
                Bind::Fix(group) => group.iter_mut().map(|(_, func)| self.visit(&mut func.body)).collect(),
            };
            height = heights.iter().copied().fold(height, usize::max);
            // Out now, as the code can go in a later binding.
            match bind {
                Bind::Val(v, L3::Lambda(code)) if self.plan.joins.contains(&v) => {
                    self.moved.insert(v, Moved { code, height: heights[0], site });
                    slots.push((binds.len(), vec![v], false));
                }
                // A group's members are joins together, or none are.
                Bind::Fix(group) if self.plan.joins.contains(&group[0].0) => {
                    let mut members = Vec::with_capacity(group.len());
                    for ((v, code), height) in group.into_iter().zip(heights) {
                        self.moved.insert(v, Moved { code, height, site });
                        members.push(v);
                    }
                    slots.push((binds.len(), members, true));
                }
                bind => binds.push(bind),
            }
        }
        height = height.max(self.visit(body));
        for (at, members, fix) in slots.into_iter().rev() {
            let codes: std::vec::Vec<(Var, Moved<'a, 'gc>)> = members.iter().filter_map(|v| self.refused.remove(v).map(|m| (*v, m))).collect();
            if codes.is_empty() {
                continue;
            }
            height = codes.iter().map(|(_, m)| m.height).fold(height, usize::max);
            let bind = if fix {
                Bind::Fix(codes.into_iter().map(|(v, m)| (v, m.code)).collect_in(arena))
            } else {
                let (v, m) = codes.into_iter().next().expect("not empty");
                Bind::Val(v, L3::Lambda(m.code))
            };
            binds.insert(at, bind);
        }
        if binds.is_empty() {
            *e = body.take();
        }
        height
    }

    #[inline(never)]
    fn app(&mut self, e: &mut L3<'a, 'gc>) -> usize {
        let L3::App(f, args) = e else { return 0 };
        let join = match **f {
            L3::Ref(v) if self.plan.joins.contains(&v) => Some(v),
            _ => None,
        };
        let mut height = match join {
            Some(_) => {
                self.next += 1;
                1
            }
            None => self.visit(f),
        };
        for a in args.iter_mut() {
            height = height.max(self.visit(a));
        }
        if let Some(v) = join {
            *e = L3::Jump(v, std::mem::replace(args, self.arena.vec()));
        }
        height
    }
}

/// Adds the joins `e` jumps to to `targets`, and those it has the code of to `joined`.
fn jumps(e: &L3<'_, '_>, targets: &mut HashSet<Var>, joined: &mut HashSet<Var>) {
    match e {
        L3::Jump(v, _) => _ = targets.insert(*v),
        L3::Join { group, .. } => joined.extend(group.iter().map(|(v, _)| *v)),
        _ => {}
    }
    each_child(e, &mut |c| jumps(c, targets, joined));
}

/// `e` with its jumps to the joins `to` picks calls again.
fn unjump<'a, 'gc>(arena: &'a Arena, e: &mut L3<'a, 'gc>, to: &dyn Fn(Var) -> bool) {
    if let L3::Jump(v, args) = e
        && to(*v)
    {
        let args = std::mem::replace(args, arena.vec());
        *e = L3::App(arena.boxed(L3::Ref(*v)), args);
    }
    each_child_mut(e, &mut |c| unjump(arena, c, to));
}

fn each_child<'t, 'gc>(e: &L3<'t, 'gc>, f: &mut dyn FnMut(&L3<'t, 'gc>)) {
    match e {
        L3::Quote(_) | L3::Ref(_) => {}
        L3::Set(_, value) => f(value),
        L3::If(a, b, c) => [a, b, c].into_iter().for_each(|e| f(e)),
        L3::Seq(a, b) => [a, b].into_iter().for_each(|e| f(e)),
        L3::Let(binds, body) => {
            for bind in binds {
                match bind {
                    Bind::Val(_, init) => f(init),
                    Bind::Fix(group) => group.iter().for_each(|(_, func)| f(&func.body)),
                }
            }
            f(body);
        }
        L3::Lambda(func) => f(&func.body),
        L3::App(callee, args) => {
            f(callee);
            args.iter().for_each(&mut *f);
        }
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => args.iter().for_each(&mut *f),
        L3::Join { group, scope } => {
            group.iter().for_each(|(_, func)| f(&func.body));
            f(scope);
        }
    }
}

fn each_child_mut<'t, 'gc>(e: &mut L3<'t, 'gc>, f: &mut dyn FnMut(&mut L3<'t, 'gc>)) {
    match e {
        L3::Quote(_) | L3::Ref(_) => {}
        L3::Set(_, value) => f(value),
        L3::If(a, b, c) => [a, b, c].into_iter().for_each(|e| f(e)),
        L3::Seq(a, b) => [a, b].into_iter().for_each(|e| f(e)),
        L3::Let(binds, body) => {
            for bind in binds.iter_mut() {
                match bind {
                    Bind::Val(_, init) => f(init),
                    Bind::Fix(group) => group.iter_mut().for_each(|(_, func)| f(&mut func.body)),
                }
            }
            f(body);
        }
        L3::Lambda(func) => f(&mut func.body),
        L3::App(callee, args) => {
            f(callee);
            args.iter_mut().for_each(&mut *f);
        }
        L3::Intrinsic(_, args) | L3::ApplyIntrinsic(_, args) | L3::Jump(_, args) => args.iter_mut().for_each(&mut *f),
        L3::Join { group, scope } => {
            group.iter_mut().for_each(|(_, func)| f(&mut func.body));
            f(scope);
        }
    }
}
