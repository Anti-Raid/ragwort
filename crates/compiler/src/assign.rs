//! Pass 4: Assignment conversion, performed in two phases surrounding [`contify`](crate::contify).
//!
//! [`lower`] (`L2 -> L3`) preserves `Set` expressions as [`l3::Node::Set`] so that contification
//! can analyze loop structure accurately. Afterwards, [`convert`] wraps assigned variables in heap
//! boxes (`MakeBox`, `Unbox`, `SetBox`) only when they cannot safely reside in stack-frame registers:
//! - A nested closure references the variable (references within join points do not require boxing
//!   because joins execute in the parent stack frame).
//! - The variable may be mutated after a continuation is captured subsequent to its binding (re-invoking
//!   a continuation restores a snapshot of the frame, whereas a heap box maintains shared mutable state).
//! - An argument reads the variable while a later argument in the same call assigns to it (preventing
//!   argument evaluation from observing unexpected in-place register mutations).
//!
//! All other assigned variables remain in registers without heap allocation.

use crate::hash::{HashMap, HashSet};

use ragwort_vm::Intrinsic;

use crate::ir::l2::{self, L2};
use crate::ir::l3::{self, Fun, Id, JoinCode, Node, Span};
use crate::ir::Supply;
use crate::{Prim, Var};

/// Lowers the L2 AST rooted at `root` in `from` into an L3 AST in `tree`, preserving
/// assignment nodes (`Set`) and collecting the set of all assigned variables.
pub(crate) fn lower<'s, 'id, 'gc>(tree: &mut l3::L3<'id, 'gc>, from: &L2<'s, 'gc>, root: l2::Id<'s>) -> (Id<'id>, HashSet<Var>) {
    /// A task in the lowering worklist: either an L2 expression to traverse, or an action
    /// to assemble lowered child expressions into an L3 node.
    enum Task<'s> {
        Expr(l2::Id<'s>),
        Make(l2::Id<'s>),
    }
    let mut assigned = HashSet::default();
    let mut vals: std::vec::Vec<Id<'id>> = std::vec::Vec::new();
    let mut todo = vec![Task::Expr(root)];
    let mut then = std::vec::Vec::new();
    let function = |tree: &mut l3::L3<'id, 'gc>, fun: l2::Fun<'s>, body: Id<'id>| {
        let original = from[fun];
        let params = tree.list(from[original.params].iter().copied());
        tree.function(l3::Function { id: original.id, optional: original.optional, params, rest: original.rest, body })
    };
    while let Some(task) = todo.pop() {
        let id = match task {
            Task::Expr(id) => id,
            Task::Make(id) => {
                tree.at(from.site(id));
                let mut pop = || vals.pop().expect("a lowered child");
                let node = match from[id] {
                    l2::Node::If(..) => {
                        let (other, then, test) = (pop(), pop(), pop());
                        Node::If(test, then, other)
                    }
                    l2::Node::Seq(..) => {
                        let (second, first) = (pop(), pop());
                        Node::Seq(first, second)
                    }
                    l2::Node::Set(var, _) => {
                        assigned.insert(var);
                        Node::Set(var, pop())
                    }
                    l2::Node::Lambda(fun) => {
                        let body = pop();
                        Node::Lambda(function(tree, fun, body))
                    }
                    l2::Node::App(_, args) => {
                        let args = tree.list(vals.drain(vals.len() - from[args].len()..));
                        Node::App(vals.pop().expect("a lowered callee"), args)
                    }
                    l2::Node::Intrinsic(prim, args) => Node::Intrinsic(prim, tree.list(vals.drain(vals.len() - from[args].len()..))),
                    l2::Node::ApplyIntrinsic(prim, args) => Node::ApplyIntrinsic(prim, tree.list(vals.drain(vals.len() - from[args].len()..))),
                    l2::Node::Let(binds, _) => {
                        let body = pop();
                        let mut lowered = std::vec::Vec::with_capacity(from[binds].len());
                        for &bind in from[binds].iter().rev() {
                            lowered.push(match bind {
                                l2::Bind::Val(var, _) => l3::Bind::Val(var, vals.pop().expect("a lowered init")),
                                l2::Bind::Fix(group) => {
                                    let bodies = vals.drain(vals.len() - from[group].len()..).collect::<std::vec::Vec<_>>();
                                    let group: std::vec::Vec<(Var, Fun<'id>)> =
                                        from[group].iter().zip(bodies).map(|(&(var, fun), body)| (var, function(tree, fun, body))).collect();
                                    l3::Bind::Fix(tree.list(group))
                                }
                            });
                        }
                        lowered.reverse();
                        Node::Let(tree.list(lowered), body)
                    }
                    l2::Node::Quote(_) | l2::Node::Ref(_) => unreachable!("leaves are made as they're reached"),
                };
                vals.push(tree.add(node));
                continue;
            }
        };
        match from[id] {
            l2::Node::Quote(value) => vals.push(tree.add(Node::Quote(value))),
            l2::Node::Ref(var) => vals.push(tree.add(Node::Ref(var))),
            l2::Node::Lambda(fun) => then.extend([Task::Expr(from[fun].body), Task::Make(id)]),
            l2::Node::Let(binds, body) => {
                for &bind in &from[binds] {
                    match bind {
                        l2::Bind::Val(_, init) => then.push(Task::Expr(init)),
                        l2::Bind::Fix(group) => then.extend(from[group].iter().map(|&(_, fun)| Task::Expr(from[fun].body))),
                    }
                }
                then.extend([Task::Expr(body), Task::Make(id)]);
            }
            _ => {
                from.children(id, |child| then.push(Task::Expr(child)));
                then.push(Task::Make(id));
            }
        }
        todo.extend(then.drain(..).rev());
    }
    (vals.pop().expect("the root's lowered"), assigned)
}

/// Wraps in heap boxes (`MakeBox`/`Unbox`/`SetBox`) any assigned variables in `root`
/// that cannot safely reside in frame registers.
pub(crate) fn convert<'id, 'gc>(tree: &mut l3::L3<'id, 'gc>, root: Id<'id>, assigned: &HashSet<Var>, supply: &mut Supply) {
    if assigned.is_empty() {
        return;
    }
    let mut boxed = HashSet::default();
    order_hazards(tree, root, assigned, &mut boxed);
    let mut survey = Survey {
        tree,
        assigned,
        bound: HashMap::default(),
        frame: 0,
        frames: 0,
        captures: 0,
        outer: std::vec::Vec::new(),
        saved: std::vec::Vec::new(),
        boxed,
    };
    let mut todo = vec![Step::Expr(root, true)];
    while let Some(step) = todo.pop() {
        survey.step(step, &mut todo);
    }
    let boxed = survey.boxed;
    if !boxed.is_empty() {
        rewrite(tree, root, &boxed, supply);
    }
}

/// A step in the survey traversal: either an expression to inspect (marking whether it is
/// in tail position), or an action to update frame and continuation-capture state.
enum Step<'id> {
    Expr(Id<'id>, bool),
    Set(Var),
    Bind(Var),
    Capture,
    /// Pre-branch marker for `If`: records the current continuation capture count before traversing branches.
    Mark,
    /// Intermediate step between `If` branches: saves the capture count after the `then` branch and resets to the pre-branch count for the `else` branch.
    Branch,
    /// Post-branch merge for `If`: sets the current capture count to the maximum observed across both branches.
    Merge,
    Enter(Fun<'id>),
    Leave,
    Joins(Span<'id, JoinCode<'id>>, bool),
    Code(Fun<'id>),
    Coded,
    Joined,
}

/// Analysis pass that traverses stack frames in execution order to identify which assigned variables must be boxed.
struct Survey<'s, 't, 'id, 'gc> {
    tree: &'t l3::L3<'id, 'gc>,
    assigned: &'s HashSet<Var>,
    bound: HashMap<Var, Bound>,
    frame: u32,
    frames: u32,
    /// The number of potential continuation-capture points encountered along the current execution path.
    captures: u32,
    /// Stack of `(frame_id, capture_count)` pairs for enclosing functions, ordered from outermost to innermost.
    outer: std::vec::Vec<(u32, u32)>,
    /// Saved capture counts for managing branching paths and loop join points currently being traversed.
    saved: std::vec::Vec<u32>,
    boxed: HashSet<Var>,
}

/// Binding site metadata for an assigned variable: its enclosing stack frame ID and the continuation capture count when it was bound.
#[derive(Clone, Copy)]
struct Bound {
    frame: u32,
    captures: u32,
}

impl<'id> Survey<'_, '_, 'id, '_> {
    fn bind(&mut self, var: Var) {
        if self.assigned.contains(&var) {
            self.bound.insert(var, Bound { frame: self.frame, captures: self.captures });
        }
    }

    fn uses(&mut self, var: Var) {
        if let Some(bound) = self.bound.get(&var)
            && bound.frame != self.frame
        {
            self.boxed.insert(var);
        }
    }

    fn save(&mut self) -> u32 {
        self.saved.pop().expect("noted before")
    }

    fn step(&mut self, step: Step<'id>, todo: &mut std::vec::Vec<Step<'id>>) {
        let tree = self.tree;
        match step {
            Step::Expr(id, tail) => self.expr(id, tail, todo),
            Step::Set(var) => {
                self.uses(var);
                if let Some(bound) = self.bound.get(&var)
                    && self.captures > bound.captures
                {
                    self.boxed.insert(var);
                }
            }
            Step::Bind(var) => self.bind(var),
            Step::Capture => self.captures += 1,
            Step::Mark => self.saved.push(self.captures),
            Step::Branch => {
                let start = self.save();
                self.saved.push(std::mem::replace(&mut self.captures, start));
            }
            Step::Merge => {
                let after_then = self.save();
                self.captures = self.captures.max(after_then);
            }
            // Entering a closure body, which executes in a new stack frame.
            Step::Enter(fun) => {
                self.frames += 1;
                self.outer.push((std::mem::replace(&mut self.frame, self.frames), std::mem::replace(&mut self.captures, 0)));
                tree.params(fun).for_each(|param| self.bind(param));
            }
            Step::Leave => (self.frame, self.captures) = self.outer.pop().expect("entered"),
            // Join points can be entered via jumps, and loops can repeat; therefore, if any join body
            // contains a continuation capture point, we treat it as preceding the entire join body.
            // A single pass suffices even when join points are nested.
            Step::Joins(codes, tail) => {
                let again = tree[codes].iter().any(|code| captures(tree, tree[code.fun].body, tail));
                let start = self.captures + u32::from(again);
                self.saved.extend([start, start]);
            }
            Step::Code(fun) => {
                self.captures = self.saved[self.saved.len() - 2];
                tree.params(fun).for_each(|param| self.bind(param));
            }
            Step::Coded => {
                let end = self.saved.last_mut().expect("noted at the join");
                *end = (*end).max(self.captures);
            }
            Step::Joined => {
                self.captures = self.save();
                self.save();
            }
        }
    }

    /// Inspects leaf expressions immediately and pushes traversal steps for compound expressions onto the worklist in reverse order.
    fn expr(&mut self, id: Id<'id>, tail: bool, todo: &mut std::vec::Vec<Step<'id>>) {
        let tree = self.tree;
        let at = todo.len();
        let exprs = |ids: &[Id<'id>], todo: &mut std::vec::Vec<Step<'id>>| todo.extend(ids.iter().map(|&child| Step::Expr(child, false)));
        match tree[id] {
            Node::Quote(_) => {}
            Node::Ref(var) => self.uses(var),
            Node::Set(var, value) => todo.extend([Step::Expr(value, false), Step::Set(var)]),
            Node::If(test, then, other) => {
                todo.extend([Step::Expr(test, false), Step::Mark, Step::Expr(then, tail), Step::Branch, Step::Expr(other, tail), Step::Merge]);
            }
            Node::Seq(first, second) => todo.extend([Step::Expr(first, false), Step::Expr(second, tail)]),
            Node::Let(binds, body) => {
                for &bind in &tree[binds] {
                    match bind {
                        l3::Bind::Val(var, init) => todo.extend([Step::Expr(init, false), Step::Bind(var)]),
                        l3::Bind::Fix(group) => {
                            for &(_, fun) in &tree[group] {
                                todo.extend([Step::Enter(fun), Step::Expr(tree[fun].body, true), Step::Leave]);
                            }
                        }
                    }
                }
                todo.push(Step::Expr(body, tail));
            }
            Node::Lambda(fun) => todo.extend([Step::Enter(fun), Step::Expr(tree[fun].body, true), Step::Leave]),
            Node::App(function, args) => {
                let all: std::vec::Vec<Id<'id>> = std::iter::once(function).chain(tree[args].iter().copied()).collect();
                exprs(&all, todo);
                if !tail {
                    todo.push(Step::Capture);
                }
            }
            Node::Intrinsic(prim, args) | Node::ApplyIntrinsic(prim, args) => {
                exprs(&tree[args], todo);
                if !tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..)) {
                    todo.push(Step::Capture);
                }
            }
            Node::Jump(_, args) => {
                exprs(&tree[args], todo);
            }
            Node::Join(scope, codes) => {
                todo.extend([Step::Expr(scope, tail), Step::Joins(codes, tail)]);
                for code in &tree[codes] {
                    todo.extend([Step::Code(code.fun), Step::Expr(tree[code.fun].body, tail), Step::Coded]);
                }
                todo.push(Step::Joined);
            }
        }
        todo[at..].reverse();
    }
}

/// Trait for bitsets tracking reads and writes of assigned variables during argument order analysis.
trait VarSet: Clone + Default {
    fn new(words: usize) -> Self;
    fn insert(&mut self, idx: usize);
    fn union_with(&mut self, other: &Self);
    fn for_each_intersection(&self, other: &Self, callback: impl FnMut(usize));
}

impl VarSet for u64 {
    fn new(_words: usize) -> Self {
        0
    }

    fn insert(&mut self, idx: usize) {
        *self |= 1u64 << idx;
    }

    fn union_with(&mut self, other: &Self) {
        *self |= *other;
    }

    fn for_each_intersection(&self, other: &Self, mut callback: impl FnMut(usize)) {
        let mut both = *self & *other;
        while both != 0 {
            let tz = both.trailing_zeros() as usize;
            callback(tz);
            both &= both - 1;
        }
    }
}

#[derive(Clone, Default)]
struct LargeSet(Vec<u64>);

impl VarSet for LargeSet {
    fn new(words: usize) -> Self {
        LargeSet(vec![0; words])
    }

    fn insert(&mut self, idx: usize) {
        self.0[idx / 64] |= 1u64 << (idx % 64);
    }

    fn union_with(&mut self, other: &Self) {
        for (left, &right) in self.0.iter_mut().zip(&other.0) {
            *left |= right;
        }
    }

    fn for_each_intersection(&self, other: &Self, mut callback: impl FnMut(usize)) {
        for (i, (&left, &right)) in self.0.iter().zip(&other.0).enumerate() {
            let mut both = left & right;
            while both != 0 {
                let tz = both.trailing_zeros() as usize;
                callback(i * 64 + tz);
                both &= both - 1;
            }
        }
    }
}

struct Effect<S> {
    reads: S,
    writes: S,
}

enum OrderTask<'id> {
    Enter(Id<'id>),
    Leave(Id<'id>, usize),
}

/// Identifies variables in `assigned` that must be boxed because an earlier argument in a call
/// reads the variable while a later argument in the same call assigns to it.
fn order_hazards<'id, 'gc>(
    tree: &l3::L3<'id, 'gc>,
    root: Id<'id>,
    assigned: &HashSet<Var>,
    boxed: &mut HashSet<Var>,
) {
    let var_list: Vec<Var> = assigned.iter().copied().collect();
    let var_map: HashMap<Var, usize> = var_list.iter().copied().enumerate().map(|(i, var)| (var, i)).collect();
    if assigned.len() <= 64 {
        survey_order::<u64>(tree, root, 1, &var_map, &var_list, boxed);
    } else {
        let words = assigned.len().div_ceil(64);
        survey_order::<LargeSet>(tree, root, words, &var_map, &var_list, boxed);
    }
}

fn survey_order<'id, 'gc, S: VarSet>(
    tree: &l3::L3<'id, 'gc>,
    root: Id<'id>,
    words: usize,
    var_map: &HashMap<Var, usize>,
    var_list: &[Var],
    boxed: &mut HashSet<Var>,
) {
    let mut results: Vec<Effect<S>> = Vec::new();
    let mut todo = vec![OrderTask::Enter(root)];
    let mut children_buf: Vec<Id<'id>> = Vec::new();

    while let Some(task) = todo.pop() {
        match task {
            OrderTask::Enter(id) => {
                let start = results.len();
                children_buf.clear();
                tree.children(id, |child| children_buf.push(child));
                tree.bodies(id, |body| children_buf.push(body));

                if children_buf.is_empty() {
                    let mut reads = S::new(words);
                    let mut writes = S::new(words);
                    match tree[id] {
                        Node::Ref(var) => {
                            if let Some(&idx) = var_map.get(&var) {
                                reads.insert(idx);
                            }
                        }
                        Node::Set(var, _) => {
                            if let Some(&idx) = var_map.get(&var) {
                                writes.insert(idx);
                            }
                        }
                        _ => {}
                    }
                    results.push(Effect { reads, writes });
                } else {
                    todo.push(OrderTask::Leave(id, start));
                    for &child in children_buf.iter().rev() {
                        todo.push(OrderTask::Enter(child));
                    }
                }
            }
            OrderTask::Leave(id, start) => {
                let is_call = matches!(
                    tree[id],
                    Node::App(..) | Node::Intrinsic(..) | Node::ApplyIntrinsic(..) | Node::Jump(..)
                );
                if is_call {
                    let mut seen_reads = S::new(words);
                    for child in &results[start..] {
                        child.writes.for_each_intersection(&seen_reads, |idx| {
                            boxed.insert(var_list[idx]);
                        });
                        seen_reads.union_with(&child.reads);
                    }
                }
                let mut node_reads = S::new(words);
                let mut node_writes = S::new(words);
                for child in results.drain(start..) {
                    node_reads.union_with(&child.reads);
                    node_writes.union_with(&child.writes);
                }
                match tree[id] {
                    Node::Ref(var) => {
                        if let Some(&idx) = var_map.get(&var) {
                            node_reads.insert(idx);
                        }
                    }
                    Node::Set(var, _) => {
                        if let Some(&idx) = var_map.get(&var) {
                            node_writes.insert(idx);
                        }
                    }
                    _ => {}
                }
                results.push(Effect { reads: node_reads, writes: node_writes });
            }
        }
    }
}

/// Checks whether expression `expr` contains any non-tail calls or operations that could capture a continuation,
/// taking into account whether `expr` itself is in tail position.
fn captures<'id>(tree: &l3::L3<'id, '_>, expr: Id<'id>, tail: bool) -> bool {
    let mut todo = vec![(expr, tail)];
    while let Some((id, tail)) = todo.pop() {
        let args = |ids: &[Id<'id>], todo: &mut std::vec::Vec<(Id<'id>, bool)>| todo.extend(ids.iter().map(|&arg| (arg, false)));
        match tree[id] {
            Node::Quote(_) | Node::Ref(_) | Node::Lambda(_) => {}
            Node::Set(_, value) => todo.push((value, false)),
            Node::If(test, then, other) => todo.extend([(test, false), (then, tail), (other, tail)]),
            Node::Seq(first, second) => todo.extend([(first, false), (second, tail)]),
            Node::Let(binds, body) => {
                todo.extend(tree[binds].iter().filter_map(|bind| if let l3::Bind::Val(_, init) = *bind { Some((init, false)) } else { None }));
                todo.push((body, tail));
            }
            Node::App(function, operands) => {
                if !tail {
                    return true;
                }
                todo.push((function, false));
                args(&tree[operands], &mut todo);
            }
            Node::Intrinsic(prim, operands) | Node::ApplyIntrinsic(prim, operands) => {
                if !tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..)) {
                    return true;
                }
                args(&tree[operands], &mut todo);
            }
            Node::Jump(_, operands) => args(&tree[operands], &mut todo),
            Node::Join(scope, codes) => {
                todo.push((scope, tail));
                todo.extend(tree[codes].iter().map(|code| (tree[code.fun].body, tail)));
            }
        }
    }
    false
}

/// Worklist task for rewriting expressions to use boxes; processes function bodies before
/// rebinding boxed parameters to fresh variables, and traverses join definitions before their scopes.
enum Redo<'id> {
    Node(Id<'id>),
    Function(Fun<'id>),
}

/// Rewrites the AST rooted at `root` in place, replacing accesses and assignments to variables in `boxed`
/// with heap box operations (`MakeBox`, `Unbox`, and `SetBox`).
fn rewrite<'id, 'gc>(tree: &mut l3::L3<'id, 'gc>, root: Id<'id>, boxed: &HashSet<Var>, supply: &mut Supply) {
    let boxing = |tree: &mut l3::L3<'id, 'gc>, intrinsic, args: &[Id<'id>]| {
        let args = tree.list(args.iter().copied());
        Node::Intrinsic(Prim::Intrinsic(intrinsic), args)
    };
    let mut todo = vec![Redo::Node(root)];
    let mut then = std::vec::Vec::new();
    while let Some(redo) = todo.pop() {
        let id = match redo {
            Redo::Node(id) => id,
            Redo::Function(fun) => {
                let mut binds = std::vec::Vec::new();
                let mut fresh = |param: Var, tree: &mut l3::L3<'id, 'gc>| {
                    if !boxed.contains(&param) {
                        return param;
                    }
                    let raw = supply.fresh_var();
                    let reference = tree.add(Node::Ref(raw));
                    let init = boxing(tree, Intrinsic::MakeBox, &[reference]);
                    binds.push(l3::Bind::Val(param, tree.add(init)));
                    raw
                };
                let function = tree[fun];
                let params: std::vec::Vec<Var> = (0..tree[function.params].len()).map(|i| fresh(tree[function.params][i], tree)).collect();
                let rest = function.rest.map(|param| fresh(param, tree));
                if !binds.is_empty() {
                    let (params, binds) = (tree.list(params), tree.list(binds));
                    let body = tree.add(Node::Let(binds, function.body));
                    tree[fun] = l3::Function { params, rest, body, ..function };
                }
                continue;
            }
        };
        let body = |fun: Fun<'id>, tree: &l3::L3<'id, 'gc>| [Redo::Node(tree[fun].body), Redo::Function(fun)];
        match tree[id] {
            Node::Ref(var) if boxed.contains(&var) => {
                let reference = tree.add(Node::Ref(var));
                let node = boxing(tree, Intrinsic::Unbox, &[reference]);
                tree.set(id, node);
            }
            Node::Set(var, value) if boxed.contains(&var) => {
                let reference = tree.add(Node::Ref(var));
                let node = boxing(tree, Intrinsic::SetBox, &[reference, value]);
                tree.set(id, node);
                then.push(Redo::Node(value));
            }
            Node::Let(binds, body_id) => {
                for i in 0..tree[binds].len() {
                    match tree[binds][i] {
                        l3::Bind::Val(var, init) if boxed.contains(&var) => {
                            let value = tree.add(tree[init]);
                            let node = boxing(tree, Intrinsic::MakeBox, &[value]);
                            tree.set(init, node);
                            then.push(Redo::Node(value));
                        }
                        l3::Bind::Val(_, init) => then.push(Redo::Node(init)),
                        l3::Bind::Fix(group) => {
                            for j in 0..tree[group].len() {
                                then.extend(body(tree[group][j].1, tree));
                            }
                        }
                    }
                }
                then.push(Redo::Node(body_id));
            }
            Node::Join(scope, codes) => {
                for i in 0..tree[codes].len() {
                    then.extend(body(tree[codes][i].fun, tree));
                }
                then.push(Redo::Node(scope));
            }
            Node::Lambda(fun) => then.extend(body(fun, tree)),
            _ => tree.children(id, |child| then.push(Redo::Node(child))),
        }
        todo.extend(then.drain(..).rev());
    }
}
