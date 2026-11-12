//! Pass 5 (`L3 -> L3`): Contification optimization.
//!
//! Contification turns local functions into join points (intra-procedural continuations), replacing
//! function calls with direct jumps within the same stack frame.
//!
//! A function is eligible for contification when every reference to it is a full call (matching its arity),
//! and all such calls share a single common continuation point `P` (the lowest common ancestor in the
//! tail-call forest) with no intervening closures. Because all call sites return to `P`, the function's
//! body can be placed at `P` and callers can jump to it directly. Mutually recursive functions bound by a
//! `Fix` are contified together as a group when all external calls target `P` and internal recursive calls
//! are in tail position. A tail-recursive loop becomes a join point placed at the loop's initial entry call.
//! If all calls reside within an inner lambda nested under the binding site, the join point may be moved
//! into that inner lambda, provided doing so does not increase the net number of captured upvalues across
//! intermediate closures.
//!
//! The pass runs a bottom-up survey that tracks each expression's *tail chain* (the sequence of ancestors
//! in mutual tail position). When call sites share an ancestor chain, their common continuation `P` is the
//! deepest shared node. Functions are evaluated from innermost to outermost scope. After decisions are made,
//! call sites are rewritten to [`Node::Jump`]s, each target `P` is wrapped in a [`Node::Join`] node, and
//! the original function bindings are eliminated.

use crate::hash::{HashMap, HashSet};

use crate::Var;
use crate::ir::l3::{Bind, Fun, Id, JoinCode, L3, Node};

/// Maximum aggregate number of parameters allowed for a group of join points, bounded by register capacity.
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
    // Maps original node IDs to their replacement IDs within the new Join node's scope.
    let mut moved = HashMap::default();
    for (at, groups) in plan.at {
        let codes: Vec<JoinCode<'id>> = groups.iter().flatten().map(|&v| JoinCode { id: v, fun: plan.funs[&v] }).collect();
        let (scope, codes) = (tree.add(tree[at]), tree.list(codes));
        tree.set(at, Node::Join(scope, codes));
        moved.insert(at, scope);
    }
    // Processes bindings innermost-first so that a `Let` with all bindings contified can be collapsed into its body.
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
                // All members of a mutually recursive `Fix` group are contified together, or none are.
                Bind::Fix(group) => !plan.joins.contains(&tree[group][0].0),
            })
            .collect();
        let node = if kept.is_empty() { tree[body] } else { Node::Let(tree.list(kept), body) };
        tree.set(at, node);
    }
}

/// Results of the contification analysis, specifying placement sites and functions to convert into joins.
struct Plan<'id> {
    /// Groups of contified functions to attach at each target node ID, ordered from innermost to outermost.
    at: HashMap<Id<'id>, Vec<Vec<Var>>>,
    joins: HashSet<Var>,
    /// Maps each contified function variable to its original function definition.
    funs: HashMap<Var, Fun<'id>>,
}

/// Analysis state for a candidate function eligible for contification.
struct Candidate<'id> {
    arity: usize,
    /// True if every observed use is an exact-arity direct call with no escaping references.
    called: bool,
    calls: Vec<Site<Box<[Id<'id>]>>>,
}

/// Location metadata for a call site or join placement: the tail chain of ancestor nodes and the enclosing stack frame.
struct Site<C> {
    chain: C,
    frame: u32,
}

/// Group of candidate functions bound at a single `Let` or `Fix` site, evaluated together for contification.
struct Binding<'id> {
    members: Vec<Var>,
    frame: u32,
    at: Id<'id>,
}

/// Represents a stack frame corresponding to a lambda body.
struct Frame<'id> {
    /// ID of the enclosing parent stack frame.
    outer: u32,
    lambda: Fun<'id>,
    /// Candidate function variable associated with this frame body, if any.
    of: Option<Var>,
}

/// A deferred worklist task for the bottom-up contification survey traversal.
enum Task<'id> {
    /// Visits an AST node that is in tail position relative to its parent.
    Tail(Id<'id>),
    /// Visits an AST node that begins a new tail chain (not in tail position of its parent).
    Fresh(Id<'id>),
    /// Pops the current node from the tail chain after traversing its children.
    Pop,
    /// Restores the previous tail chain base index after returning from a non-tail subtree.
    Restore,
    /// Enters a function body in a new stack frame, recording its candidate variable if applicable.
    Body(Fun<'id>, Option<Var>),
    Leave,
    /// Processes a single `Let` or `Fix` binding after preceding bindings have been visited.
    Bind(Id<'id>, Bind<'id>),
    /// Finalizes candidate bindings for a `Let` expression after its body has been traversed.
    Bound,
}

struct Survey<'t, 'id, 'gc> {
    tree: &'t L3<'id, 'gc>,
    candidates: HashMap<Var, Candidate<'id>>,
    funs: HashMap<Var, Fun<'id>>,
    /// Maps each function body node ID to the candidate variable it implements.
    bodies: HashMap<Id<'id>, Var>,
    /// Collected candidate binding groups, ordered from innermost to outermost.
    bindings: Vec<Binding<'id>>,
    /// Candidate binding groups for each currently enclosing `Let` scope.
    mine: Vec<Vec<Binding<'id>>>,
    /// Current path of ancestor nodes; the active tail chain is `chain[base..]`.
    chain: Vec<Id<'id>>,
    base: usize,
    bases: Vec<usize>,
    frame: u32,
    outer: Vec<u32>,
    /// Frame descriptor arena, indexed as `frames[frame_id - 1]`.
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
                // Reverse order ensures inner bindings are evaluated before outer ones.
                self.bindings.extend(mine.into_iter().rev());
            }
        }
        todo[at..].reverse();
    }

    /// Traverses child expressions of node `id`, pushing appropriate tail or non-tail worklist tasks.
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

    /// Disqualifies candidate `v` if it is passed as a value, stored, or referenced other than in a direct call.
    fn unfit(&mut self, v: Var) {
        if let Some(c) = self.candidates.get_mut(&v) {
            c.called = false;
        }
    }

    /// Registers `var` as a contification candidate if `fun` has no rest or optional parameters and fits parameter limits.
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
                // Verifies that total parameters across all group members do not exceed available registers.
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
        // Tracks the chosen placement site and stack frame for each successfully contified function.
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
                    // If the call site is located inside another join body that was already placed, prepend its tail chain.
                    let mut chain = call.chain.to_vec();
                    let mut frame = call.frame;
                    while let Some(join) = self.bodies.get(&chain[0]).and_then(|w| placed.get(w)) {
                        chain = join.chain.iter().chain(&chain).copied().collect();
                        frame = join.frame;
                    }
                    // Recursive self-calls or mutual calls within group members execute locally without changing the common continuation.
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

    /// Checks whether `binding`'s functions can be placed into `frame` (nested inside their binding frame)
    /// without increasing the number of upvalues captured by intermediate closures.
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

    /// Collects all variables referenced by `fun` into `uses` and all variables locally bound within it into `bound`.
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
