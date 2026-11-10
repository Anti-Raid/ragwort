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
//! The survey walks the tree once, noting each node's *chain*: the nodes from the top of the run
//! of tail positions it's at the bottom of down to it. Calls whose chains start at the same node
//! are in tail position of each node their chains share, so `P` is the last of those. Functions
//! are decided innermost first, as one can only call those it's inside the scope of. Then the
//! calls become [`Node::Jump`]s, each `P` a [`Node::Join`] of the code there, its node moved into
//! the join's scope, and the bindings of the joins go, the functions now the joins' code.

use crate::hash::{HashMap, HashSet};

use crate::Var;
use crate::ir::l3::{Bind, Fun, Id, JoinCode, L3, Node};

/// Most parameters a group of joins can have, as their values move in its own registers.
const MAX_PARAMS: usize = 32;

pub(crate) fn contify<'id>(tree: &mut L3<'id, '_>, root: Id<'id>) {
    let mut survey = Survey {
        tree,
        candidates: HashMap::default(),
        funs: HashMap::default(),
        bodies: HashMap::default(),
        bindings: Vec::new(),
        mine: Vec::new(),
        chain: Vec::new(),
        base: 0,
        bases: Vec::new(),
        frame: 0,
        outer: Vec::new(),
        frames: Vec::new(),
    };
    let mut todo = vec![Task::Fresh(root)];
    while let Some(task) = todo.pop() {
        survey.run(task, &mut todo);
    }
    let plan = survey.decide();
    if plan.joins.is_empty() {
        return;
    }
    let Survey { candidates, bindings, .. } = survey;
    for v in &plan.joins {
        for call in &candidates[v].calls {
            let at = *call.chain.last().expect("a chain has its call");
            let Node::App(_, args) = tree[at] else { unreachable!("a call of a join") };
            tree.set(at, Node::Jump(*v, args));
        }
    }
    // Where the node each join goes at is now: in its scope.
    let mut moved = HashMap::default();
    for (at, groups) in plan.at {
        let codes: Vec<JoinCode<'id>> = groups.iter().flatten().map(|&v| JoinCode { id: v, fun: plan.funs[&v] }).collect();
        let (scope, codes) = (tree.add(tree[at]), tree.list(codes));
        tree.set(at, Node::Join(scope, codes));
        moved.insert(at, scope);
    }
    // Innermost first, as a `Let` left with no bindings takes its body's place.
    let mut done = HashSet::default();
    for binding in bindings.iter().filter(|b| plan.joins.contains(&b.members[0])) {
        if !done.insert(binding.at) {
            continue;
        }
        let at = moved.get(&binding.at).copied().unwrap_or(binding.at);
        let Node::Let(binds, body) = tree[at] else { unreachable!("joins are bound by a let") };
        let kept: Vec<Bind<'id>> = tree[binds]
            .iter()
            .copied()
            .filter(|&bind| match bind {
                Bind::Val(v, _) => !plan.joins.contains(&v),
                // A group's members are joins together, or none are.
                Bind::Fix(group) => !plan.joins.contains(&tree[group][0].0),
            })
            .collect();
        let node = if kept.is_empty() { tree[body] } else { Node::Let(tree.list(kept), body) };
        tree.set(at, node);
    }
}

/// What contification decided.
struct Plan<'id> {
    /// The groups of joins whose code goes at each node, those decided first innermost.
    at: HashMap<Id<'id>, Vec<Vec<Var>>>,
    joins: HashSet<Var>,
    /// Each join's code.
    funs: HashMap<Var, Fun<'id>>,
}

/// A local function that could be a join.
struct Candidate<'id> {
    arity: usize,
    /// Whether every use so far is a call of `arity` arguments.
    called: bool,
    calls: Vec<Site<Box<[Id<'id>]>>>,
}

/// Where a call is, or a join goes: the chain down to it, and the frame it's in.
struct Site<C> {
    chain: C,
    frame: u32,
}

/// A binding of candidates, which are decided together, and the `Let` it's in.
struct Binding<'id> {
    members: Vec<Var>,
    frame: u32,
    at: Id<'id>,
}

/// A lambda body's frame.
struct Frame<'id> {
    /// The frame the lambda is in.
    outer: u32,
    lambda: Fun<'id>,
    /// The candidate it's the code of.
    of: Option<Var>,
}

/// What's left of the survey's walk.
enum Task<'id> {
    /// A node in tail position of the one above it.
    Tail(Id<'id>),
    /// A node that starts a chain.
    Fresh(Id<'id>),
    /// Back from a node's children.
    Pop,
    /// Back from a node that started a chain.
    Restore,
    /// The body of a function, a frame of its own, which is candidate `of`'s code.
    Body(Fun<'id>, Option<Var>),
    Leave,
    /// A `Let`'s binding, once those before it are walked.
    Bind(Id<'id>, Bind<'id>),
    /// After a `Let`'s body: its bindings of candidates, decided after those inside it.
    Bound,
}

struct Survey<'t, 'id, 'gc> {
    tree: &'t L3<'id, 'gc>,
    candidates: HashMap<Var, Candidate<'id>>,
    funs: HashMap<Var, Fun<'id>>,
    /// The candidate whose code each function body is.
    bodies: HashMap<Id<'id>, Var>,
    /// Bindings, innermost first.
    bindings: Vec<Binding<'id>>,
    /// Those of each `Let` the walk is in.
    mine: Vec<Vec<Binding<'id>>>,
    /// The nodes from the walk's top to where it is; the current chain is `chain[base..]`.
    chain: Vec<Id<'id>>,
    base: usize,
    bases: Vec<usize>,
    frame: u32,
    outer: Vec<u32>,
    /// Frame `n`'s at `n - 1`.
    frames: Vec<Frame<'id>>,
}

impl<'id> Survey<'_, 'id, '_> {
    fn run(&mut self, task: Task<'id>, todo: &mut Vec<Task<'id>>) {
        let at = todo.len();
        match task {
            Task::Tail(id) => {
                self.chain.push(id);
                self.node(id, todo);
                todo.push(Task::Pop);
            }
            Task::Fresh(id) => {
                self.bases.push(std::mem::replace(&mut self.base, self.chain.len()));
                todo.extend([Task::Tail(id), Task::Restore]);
            }
            Task::Pop => _ = self.chain.pop(),
            Task::Restore => self.base = self.bases.pop().expect("a chain was started"),
            Task::Body(fun, of) => {
                let body = self.tree[fun].body;
                if let Some(v) = of {
                    self.bodies.insert(body, v);
                }
                self.frames.push(Frame { outer: self.frame, lambda: fun, of });
                self.outer.push(std::mem::replace(&mut self.frame, self.frames.len() as u32));
                todo.extend([Task::Fresh(body), Task::Leave]);
            }
            Task::Leave => self.frame = self.outer.pop().expect("a function was entered"),
            Task::Bind(at, bind) => self.bind(at, bind, todo),
            Task::Bound => {
                let mine = self.mine.pop().expect("a let was entered");
                // The last first, as it's in the scope of those before.
                self.bindings.extend(mine.into_iter().rev());
            }
        }
        todo[at..].reverse();
    }

    /// Pushes the tasks of `id`'s children, in the order they're walked.
    fn node(&mut self, id: Id<'id>, todo: &mut Vec<Task<'id>>) {
        let tree = self.tree;
        let fresh = |ids: &[Id<'id>], todo: &mut Vec<Task<'id>>| todo.extend(ids.iter().map(|&a| Task::Fresh(a)));
        match tree[id] {
            Node::Quote(_) => {}
            Node::Ref(v) => self.unfit(v),
            Node::Set(v, value) => {
                self.unfit(v);
                todo.push(Task::Fresh(value));
            }
            Node::If(test, then, other) => todo.extend([Task::Fresh(test), Task::Tail(then), Task::Tail(other)]),
            Node::Seq(a, b) => todo.extend([Task::Fresh(a), Task::Tail(b)]),
            Node::Let(binds, body) => {
                self.mine.push(Vec::new());
                todo.extend(tree[binds].iter().map(|&bind| Task::Bind(id, bind)));
                todo.extend([Task::Tail(body), Task::Bound]);
            }
            Node::App(f, args) => {
                match tree[f] {
                    Node::Ref(v) if self.candidates.contains_key(&v) => {
                        let chain = self.chain[self.base..].into();
                        let c = self.candidates.get_mut(&v).expect("a candidate");
                        if c.arity == tree[args].len() {
                            c.calls.push(Site { chain, frame: self.frame });
                        } else {
                            c.called = false;
                        }
                    }
                    _ => todo.push(Task::Fresh(f)),
                }
                fresh(&tree[args], todo);
            }
            Node::Lambda(fun) => todo.push(Task::Body(fun, None)),
            Node::Intrinsic(_, args) | Node::ApplyIntrinsic(_, args) | Node::Jump(_, args) => fresh(&tree[args], todo),
            Node::Join(scope, codes) => {
                todo.extend(tree[codes].iter().map(|code| Task::Fresh(tree[code.fun].body)));
                todo.push(Task::Tail(scope));
            }
        }
    }

    /// Notes that `v` is used other than called, if it's a candidate.
    fn unfit(&mut self, v: Var) {
        if let Some(c) = self.candidates.get_mut(&v) {
            c.called = false;
        }
    }

    /// Notes `var`, bound to `fun`, as a candidate if it can be one.
    fn candidate(&mut self, var: Var, fun: Fun<'id>) -> bool {
        let f = self.tree[fun];
        let params = self.tree[f.params].len();
        let fits = f.rest.is_none() && f.optional == 0 && params <= MAX_PARAMS;
        if fits {
            self.candidates.insert(var, Candidate { arity: params, called: true, calls: Vec::new() });
            self.funs.insert(var, fun);
        }
        fits
    }

    fn bind(&mut self, at: Id<'id>, bind: Bind<'id>, todo: &mut Vec<Task<'id>>) {
        let tree = self.tree;
        let frame = self.frame;
        match bind {
            Bind::Val(v, init) => match tree[init] {
                Node::Lambda(fun) => {
                    let fits = self.candidate(v, fun);
                    if fits {
                        self.mine.last_mut().expect("in a let").push(Binding { members: vec![v], frame, at });
                    }
                    todo.push(Task::Body(fun, fits.then_some(v)));
                }
                _ => todo.push(Task::Fresh(init)),
            },
            Bind::Fix(group) => {
                let group = &tree[group];
                let fits: Vec<bool> = group.iter().map(|&(v, fun)| self.candidate(v, fun)).collect();
                // The group's parameters all have registers across the code the joins are placed at.
                let params: usize = group.iter().map(|&(_, fun)| tree[tree[fun].params].len()).sum();
                if fits.iter().all(|&f| f) && params <= MAX_PARAMS {
                    self.mine.last_mut().expect("in a let").push(Binding { members: group.iter().map(|&(v, _)| v).collect(), frame, at });
                }
                todo.extend(group.iter().zip(&fits).map(|(&(v, fun), &fits)| Task::Body(fun, fits.then_some(v))));
            }
        }
    }

    fn decide(&self) -> Plan<'id> {
        let mut plan = Plan { at: HashMap::default(), joins: HashSet::default(), funs: HashMap::default() };
        // Where each join decided on is.
        let mut placed: HashMap<Var, Site<Vec<Id<'id>>>> = HashMap::default();
        for binding in &self.bindings {
            let members = &binding.members;
            if !members.iter().all(|v| self.candidates[v].called) {
                continue;
            }
            let mut common: Option<Site<Vec<Id<'id>>>> = None;
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
                plan.funs.insert(v, self.funs[&v]);
                placed.insert(v, Site { chain: chain.clone(), frame });
            }
        }
        plan
    }

    /// Whether `binding`'s functions' code can go in `frame`, inside the frame that binds them and
    /// not in their own: if none of the lambdas between captures more than it does now.
    fn moves(&self, binding: &Binding<'id>, frame: u32) -> bool {
        let (mut uses, mut bound) = (HashSet::default(), HashSet::default());
        for v in &binding.members {
            bound.insert(*v);
            self.vars(self.funs[v], &mut uses, &mut bound);
        }
        let uses: Vec<Var> = uses.difference(&bound).copied().collect();
        let mut at = frame;
        while at != binding.frame {
            let Some(between) = at.checked_sub(1).and_then(|i| self.frames.get(i as usize)) else { return false };
            if between.of.is_some_and(|v| binding.members.contains(&v)) {
                return false;
            }
            let (mut captured, mut inside) = (HashSet::default(), HashSet::default());
            self.vars(between.lambda, &mut captured, &mut inside);
            let gone = binding.members.iter().filter(|v| captured.contains(v)).count();
            let come = uses.iter().filter(|v| !captured.contains(v)).count();
            if come > gone {
                return false;
            }
            at = between.outer;
        }
        true
    }

    /// Adds the variables `fun` refers to to `uses`, and those it binds to `bound`.
    fn vars(&self, fun: Fun<'id>, uses: &mut HashSet<Var>, bound: &mut HashSet<Var>) {
        let tree = self.tree;
        bound.extend(tree.params(fun));
        for id in tree.deep(tree[fun].body) {
            match tree[id] {
                Node::Ref(v) | Node::Set(v, _) => _ = uses.insert(v),
                Node::Let(binds, _) => {
                    for &bind in &tree[binds] {
                        bound.extend(tree.vars(bind));
                        if let Bind::Fix(group) = bind {
                            tree[group].iter().for_each(|&(_, f)| bound.extend(tree.params(f)));
                        }
                    }
                }
                Node::Join(_, codes) => {
                    for code in &tree[codes] {
                        bound.insert(code.id);
                        bound.extend(tree.params(code.fun));
                    }
                }
                Node::Lambda(f) => bound.extend(tree.params(f)),
                _ => {}
            }
        }
    }
}
