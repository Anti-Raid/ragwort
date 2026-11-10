//! Pass 4: assignment conversion, in two parts around [`contify`](crate::contify).
//!
//! [`lower`] (`L2 -> L3`) keeps each `Set` as an [`l3::Node::Set`], so contification sees loops as
//! they are. After it, [`convert`] puts an assigned variable in a box (`MakeBox`, `Unbox`, `SetBox`)
//! only where its frame's register can't hold it:
//! - a closure uses it. A join's code doesn't count, as it runs in the frame.
//! - it can be assigned after a continuation is captured, since it was bound. A continuation
//!   that's re-entered copies the frame as it was when captured, where a box would be shared.
//! - an argument reads it and a later one of the same call assigns it. The bytecode backend
//!   before L5 read a variable's register in place; L5's values already keep the read apart.
//!
//! The rest are assigned in their registers.

use crate::hash::{HashMap, HashSet};

use ragwort_vm::Intrinsic;

use crate::ir::l2::{self, L2};
use crate::ir::l3::{self, Fun, Id, JoinCode, Node, Span};
use crate::ir::Supply;
use crate::{Prim, Var};

/// `root` of `from` as [`L3`](l3::L3), its assignments kept, and the variables they assign.
pub(crate) fn lower<'s, 'id, 'gc>(tree: &mut l3::L3<'id, 'gc>, from: &L2<'s, 'gc>, root: l2::Id<'s>) -> (Id<'id>, HashSet<Var>) {
    /// A node to lower, or to make from those its children lowered to.
    enum Task<'s> {
        Expr(l2::Id<'s>),
        Make(l2::Id<'s>),
    }
    let mut assigned = HashSet::default();
    let mut vals: std::vec::Vec<Id<'id>> = std::vec::Vec::new();
    let mut todo = vec![Task::Expr(root)];
    let mut then = std::vec::Vec::new();
    let function = |tree: &mut l3::L3<'id, 'gc>, fun: l2::Fun<'s>, body: Id<'id>| {
        let f = from[fun];
        let params = tree.list(from[f.params].iter().copied());
        tree.function(l3::Function { id: f.id, optional: f.optional, params, rest: f.rest, body })
    };
    while let Some(task) = todo.pop() {
        let id = match task {
            Task::Expr(id) => id,
            Task::Make(id) => {
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
                    l2::Node::Set(v, _) => {
                        assigned.insert(v);
                        Node::Set(v, pop())
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
                                l2::Bind::Val(v, _) => l3::Bind::Val(v, vals.pop().expect("a lowered init")),
                                l2::Bind::Fix(group) => {
                                    let bodies = vals.drain(vals.len() - from[group].len()..).collect::<std::vec::Vec<_>>();
                                    let group: std::vec::Vec<(Var, Fun<'id>)> =
                                        from[group].iter().zip(bodies).map(|(&(v, fun), body)| (v, function(tree, fun, body))).collect();
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
            l2::Node::Quote(v) => vals.push(tree.add(Node::Quote(v))),
            l2::Node::Ref(v) => vals.push(tree.add(Node::Ref(v))),
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

/// Boxes those of the `assigned` variables of `root` its frames' registers can't hold.
pub(crate) fn convert<'id, 'gc>(tree: &mut l3::L3<'id, 'gc>, root: Id<'id>, assigned: &HashSet<Var>, supply: &mut Supply) {
    if assigned.is_empty() {
        return;
    }
    let mut survey = Survey {
        tree,
        assigned,
        bound: HashMap::default(),
        frame: 0,
        frames: 0,
        captures: 0,
        outer: std::vec::Vec::new(),
        saved: std::vec::Vec::new(),
        boxed: HashSet::default(),
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

/// What's left of the survey's walk: an expression, which ends the frame if it's in tail
/// position, or what to do once those before it are walked.
enum Step<'id> {
    Expr(Id<'id>, bool),
    Set(Var),
    Bind(Var),
    Capture,
    /// Before an `If`'s branches: notes the capture points so far.
    Mark,
    /// Between them: notes those after the first, and goes back to before it.
    Branch,
    /// After them: the most of either.
    Merge,
    Enter(Fun<'id>),
    Leave,
    Joins(Span<'id, JoinCode<'id>>, bool),
    Code(Fun<'id>),
    Coded,
    Joined,
}

/// Which assigned variables need boxes, walking each frame in the order it runs.
struct Survey<'s, 't, 'id, 'gc> {
    tree: &'t l3::L3<'id, 'gc>,
    assigned: &'s HashSet<Var>,
    bound: HashMap<Var, Bound>,
    frame: u32,
    frames: u32,
    /// The points where a continuation could be captured, so far on the way the walk follows.
    captures: u32,
    /// The frame and capture points of each function the walk is in, outermost first.
    outer: std::vec::Vec<(u32, u32)>,
    /// Capture points noted for the `If`s and `Join`s the walk is in.
    saved: std::vec::Vec<u32>,
    boxed: HashSet<Var>,
}

/// Where an assigned variable is bound: in which frame, and how many capture points the walk had
/// passed.
#[derive(Clone, Copy)]
struct Bound {
    frame: u32,
    captures: u32,
}

impl<'id> Survey<'_, '_, 'id, '_> {
    fn bind(&mut self, v: Var) {
        if self.assigned.contains(&v) {
            self.bound.insert(v, Bound { frame: self.frame, captures: self.captures });
        }
    }

    fn uses(&mut self, v: Var) {
        if let Some(bound) = self.bound.get(&v)
            && bound.frame != self.frame
        {
            self.boxed.insert(v);
        }
    }

    fn save(&mut self) -> u32 {
        self.saved.pop().expect("noted before")
    }

    fn step(&mut self, step: Step<'id>, todo: &mut std::vec::Vec<Step<'id>>) {
        let tree = self.tree;
        match step {
            Step::Expr(id, tail) => self.expr(id, tail, todo),
            Step::Set(v) => {
                self.uses(v);
                if let Some(bound) = self.bound.get(&v)
                    && self.captures > bound.captures
                {
                    self.boxed.insert(v);
                }
            }
            Step::Bind(v) => self.bind(v),
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
            // The body of a closure, a frame of its own.
            Step::Enter(fun) => {
                self.frames += 1;
                self.outer.push((std::mem::replace(&mut self.frame, self.frames), std::mem::replace(&mut self.captures, 0)));
                tree.params(fun).for_each(|p| self.bind(p));
            }
            Step::Leave => (self.frame, self.captures) = self.outer.pop().expect("entered"),
            // A join's code runs after any jump to it, and loops go round again, so it's walked as
            // if any capture point in it had come before all of it. Once, not twice, as joins
            // nest in joins' code.
            Step::Joins(codes, tail) => {
                let again = tree[codes].iter().any(|code| captures(tree, tree[code.fun].body, tail));
                let start = self.captures + u32::from(again);
                self.saved.extend([start, start]);
            }
            Step::Code(fun) => {
                self.captures = self.saved[self.saved.len() - 2];
                tree.params(fun).for_each(|p| self.bind(p));
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

    /// Walks what has no children, and pushes the steps of what has, last first.
    fn expr(&mut self, id: Id<'id>, tail: bool, todo: &mut std::vec::Vec<Step<'id>>) {
        let tree = self.tree;
        let at = todo.len();
        let exprs = |ids: &[Id<'id>], todo: &mut std::vec::Vec<Step<'id>>| todo.extend(ids.iter().map(|&a| Step::Expr(a, false)));
        match tree[id] {
            Node::Quote(_) => {}
            Node::Ref(v) => self.uses(v),
            Node::Set(v, value) => todo.extend([Step::Expr(value, false), Step::Set(v)]),
            Node::If(test, then, other) => {
                todo.extend([Step::Expr(test, false), Step::Mark, Step::Expr(then, tail), Step::Branch, Step::Expr(other, tail), Step::Merge]);
            }
            Node::Seq(a, b) => todo.extend([Step::Expr(a, false), Step::Expr(b, tail)]),
            Node::Let(binds, body) => {
                for &bind in &tree[binds] {
                    match bind {
                        l3::Bind::Val(v, init) => todo.extend([Step::Expr(init, false), Step::Bind(v)]),
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
            Node::App(f, args) => {
                let all: std::vec::Vec<Id<'id>> = std::iter::once(f).chain(tree[args].iter().copied()).collect();
                self.arguments(&all);
                exprs(&all, todo);
                if !tail {
                    todo.push(Step::Capture);
                }
            }
            Node::Intrinsic(prim, args) | Node::ApplyIntrinsic(prim, args) => {
                self.arguments(&tree[args]);
                exprs(&tree[args], todo);
                if !tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..)) {
                    todo.push(Step::Capture);
                }
            }
            Node::Jump(_, args) => {
                self.arguments(&tree[args]);
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

    /// Boxes each variable an argument assigns that one before it reads.
    fn arguments(&mut self, args: &[Id<'id>]) {
        let tree = self.tree;
        for (j, &arg) in args.iter().enumerate() {
            for id in tree.deep(arg) {
                if let Node::Set(v, _) = tree[id]
                    && args[..j].iter().any(|&before| tree.deep(before).any(|r| matches!(tree[r], Node::Ref(w) if w == v)))
                {
                    self.boxed.insert(v);
                }
            }
        }
    }
}

/// Whether `e`, which ends the frame if it's in `tail` position, has a point a continuation could
/// be captured at, as [`Survey`] counts them.
fn captures<'id>(tree: &l3::L3<'id, '_>, e: Id<'id>, tail: bool) -> bool {
    let mut todo = vec![(e, tail)];
    while let Some((id, tail)) = todo.pop() {
        let args = |ids: &[Id<'id>], todo: &mut std::vec::Vec<(Id<'id>, bool)>| todo.extend(ids.iter().map(|&a| (a, false)));
        match tree[id] {
            Node::Quote(_) | Node::Ref(_) | Node::Lambda(_) => {}
            Node::Set(_, value) => todo.push((value, false)),
            Node::If(test, then, other) => todo.extend([(test, false), (then, tail), (other, tail)]),
            Node::Seq(a, b) => todo.extend([(a, false), (b, tail)]),
            Node::Let(binds, body) => {
                todo.extend(tree[binds].iter().filter_map(|b| if let l3::Bind::Val(_, init) = *b { Some((init, false)) } else { None }));
                todo.push((body, tail));
            }
            Node::App(f, a) => {
                if !tail {
                    return true;
                }
                todo.push((f, false));
                args(&tree[a], &mut todo);
            }
            Node::Intrinsic(prim, a) | Node::ApplyIntrinsic(prim, a) => {
                if !tail && !matches!(prim, Prim::Intrinsic(_) | Prim::Slot(..)) {
                    return true;
                }
                args(&tree[a], &mut todo);
            }
            Node::Jump(_, a) => args(&tree[a], &mut todo),
            Node::Join(scope, codes) => {
                todo.push((scope, tail));
                todo.extend(tree[codes].iter().map(|code| (tree[code.fun].body, tail)));
            }
        }
    }
    false
}

/// What's left of the rewrite's walk, which goes through each function's body before taking its
/// boxed parameters as fresh ones, and a join's code before its scope.
enum Redo<'id> {
    Node(Id<'id>),
    Function(Fun<'id>),
}

/// `root` with the `boxed` variables in boxes.
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
                let mut fresh = |p: Var, tree: &mut l3::L3<'id, 'gc>| {
                    if !boxed.contains(&p) {
                        return p;
                    }
                    let raw = supply.fresh_var();
                    let r = tree.add(Node::Ref(raw));
                    let init = boxing(tree, Intrinsic::MakeBox, &[r]);
                    binds.push(l3::Bind::Val(p, tree.add(init)));
                    raw
                };
                let f = tree[fun];
                let params: std::vec::Vec<Var> = (0..tree[f.params].len()).map(|i| fresh(tree[f.params][i], tree)).collect();
                let rest = f.rest.map(|p| fresh(p, tree));
                if !binds.is_empty() {
                    let (params, binds) = (tree.list(params), tree.list(binds));
                    let body = tree.add(Node::Let(binds, f.body));
                    tree[fun] = l3::Function { params, rest, body, ..f };
                }
                continue;
            }
        };
        let body = |fun: Fun<'id>, tree: &l3::L3<'id, 'gc>| [Redo::Node(tree[fun].body), Redo::Function(fun)];
        match tree[id] {
            Node::Ref(v) if boxed.contains(&v) => {
                let r = tree.add(Node::Ref(v));
                let node = boxing(tree, Intrinsic::Unbox, &[r]);
                tree.set(id, node);
            }
            Node::Set(v, value) if boxed.contains(&v) => {
                let r = tree.add(Node::Ref(v));
                let node = boxing(tree, Intrinsic::SetBox, &[r, value]);
                tree.set(id, node);
                then.push(Redo::Node(value));
            }
            Node::Let(binds, body_id) => {
                for i in 0..tree[binds].len() {
                    match tree[binds][i] {
                        l3::Bind::Val(v, init) if boxed.contains(&v) => {
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
