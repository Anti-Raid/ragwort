//! Pass 1 (`Core -> L1`): validates the input AST and lowers module variables (`Place::Slot`)
//! into slot primitives.

use crate::hash::HashSet;
use crate::ir::Supply;
use crate::ir::l1::{Function, Id, L1, Node};
use crate::{CompileError, Core, Place, Prim, SlotOp, Var};

/// `core` into `tree`, its root there, and what makes variables and lambdas fresh after it.
///
/// It's a loop over a stack of tasks, the lowered nodes on a stack of their own, so it takes no
/// more of the machine's stack however deeply `core` nests.
pub(crate) fn lower<'id, 'gc>(tree: &mut L1<'id, 'gc>, core: &Core<'gc>) -> Result<(Id<'id>, Supply), CompileError> {
    let mut pass = Lower { tree, bound: HashSet::default(), scope: HashSet::default(), lambdas: HashSet::default(), max_var: 0, max_lambda: 0 };
    let mut vals = Vec::new();
    let mut todo = vec![Task::Expr(core)];
    let mut then = Vec::new();
    while let Some(task) = todo.pop() {
        match task {
            Task::Expr(core) => {
                if let Some(leaf) = pass.enter(core, &mut then)? {
                    vals.push(pass.tree.add(leaf));
                }
                todo.extend(then.drain(..).rev());
            }
            Task::Scope(binds) => pass.scope.extend(binds.iter().map(|&(v, _)| v)),
            Task::Make(core) => {
                let node = pass.make(core, &mut vals);
                vals.push(pass.tree.add(node));
            }
        }
    }
    let supply = Supply { next_var: pass.max_var, next_lambda: pass.max_lambda };
    Ok((vals.pop().expect("the root's lowered"), supply))
}

/// A form to lower, or what to make of what its parts lowered to.
enum Task<'c, 'gc> {
    Expr(&'c Core<'gc>),
    /// A `let`'s variables, in scope in its body.
    Scope(&'c [(Var, Core<'gc>)]),
    Make(&'c Core<'gc>),
}

struct Lower<'t, 'id, 'gc> {
    tree: &'t mut L1<'id, 'gc>,
    bound: HashSet<Var>,
    scope: HashSet<Var>,
    lambdas: HashSet<u32>,
    max_var: u32,
    max_lambda: u32,
}

impl<'id, 'gc> Lower<'_, 'id, 'gc> {
    /// Checks `core` as it's reached, and lowers it if it has no parts; else pushes the tasks
    /// that lower them and then it onto `then`, in order.
    fn enter<'c>(&mut self, core: &'c Core<'gc>, then: &mut Vec<Task<'c, 'gc>>) -> Result<Option<Node<'id, 'gc>>, CompileError> {
        let all = |args: &'c [Core<'gc>], then: &mut Vec<Task<'c, 'gc>>| then.extend(args.iter().map(Task::Expr));
        match core {
            Core::Quote(v) => return Ok(Some(Node::Quote(*v))),
            Core::Ref(Place::Local(v)) => {
                self.check_bound(*v)?;
                return Ok(Some(Node::Ref(*v)));
            }
            Core::Ref(Place::Slot { slot, checked }) => {
                let op = if *checked { SlotOp::LoadChecked } else { SlotOp::Load };
                return Ok(Some(Node::Intrinsic(Prim::Slot(op, *slot), self.tree.list([]))));
            }
            Core::If(test, t, other) => then.extend([Task::Expr(test), Task::Expr(t), Task::Expr(other)]),
            Core::Let(binds, body) => {
                for &(v, _) in binds {
                    self.reserve_var(v)?;
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.extend([Task::Scope(binds), Task::Expr(body)]);
            }
            Core::Letrec(binds, body) => {
                for &(v, _) in binds {
                    self.reserve_var(v)?;
                    self.scope.insert(v);
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.push(Task::Expr(body));
            }
            Core::Set(place, value) => {
                if let Place::Local(v) = place {
                    self.check_bound(*v)?;
                }
                then.push(Task::Expr(value));
            }
            Core::App(f, args) => {
                then.push(Task::Expr(f));
                all(args, then);
            }
            Core::Lambda(f) => {
                if !self.lambdas.insert(f.id) {
                    return Err(CompileError::SameLambda(f.id));
                }
                if f.optional as usize > f.params.len() {
                    return Err(CompileError::TooManyOptional(f.id));
                }
                self.max_lambda = self.max_lambda.max(f.id.saturating_add(1));
                for &v in f.params.iter().chain(&f.rest) {
                    self.reserve_var(v)?;
                    self.scope.insert(v);
                }
                then.push(Task::Expr(&f.body));
            }
            Core::Intrinsic(prim, args) => {
                let takes = match *prim {
                    Prim::Intrinsic(i) => i.arity().is_none_or(|n| usize::from(n) == args.len()),
                    Prim::Request(r) => r.takes(args.len()),
                    Prim::Host(h) => h.takes(args.len()),
                    Prim::Slot(op, _) => op.arity() == args.len(),
                };
                if !takes {
                    return Err(CompileError::Arity(*prim));
                }
                all(args, then);
            }
            Core::ApplyIntrinsic(prim, args) => {
                // A host function's arguments must fit a frame.
                if args.is_empty() || matches!(prim, Prim::Host(_) | Prim::Slot(..)) {
                    return Err(CompileError::Arity(*prim));
                }
                all(args, then);
            }
        }
        then.push(Task::Make(core));
        Ok(None)
    }

    /// `core`'s node, of its parts last lowered, which leave `vals`; what it bound leaves scope.
    fn make(&mut self, core: &Core<'gc>, vals: &mut Vec<Id<'id>>) -> Node<'id, 'gc> {
        let mut last = |n: usize| vals.split_off(vals.len() - n);
        match core {
            Core::If(..) => {
                let [test, t, other] = last(3)[..] else { unreachable!("an if has three parts") };
                Node::If(test, t, other)
            }
            Core::Let(binds, _) | Core::Letrec(binds, _) => {
                let mut ids = last(binds.len() + 1);
                let body = ids.pop().expect("a body");
                for &(v, _) in binds {
                    self.scope.remove(&v);
                }
                let binds = self.tree.list(binds.iter().map(|&(v, _)| v).zip(ids));
                if matches!(core, Core::Let(..)) { Node::Let(binds, body) } else { Node::Letrec(binds, body) }
            }
            Core::Set(Place::Local(v), _) => Node::Set(*v, last(1)[0]),
            Core::Set(Place::Slot { slot, checked }, _) => {
                let op = if *checked { SlotOp::StoreChecked } else { SlotOp::Store };
                let value = last(1);
                Node::Intrinsic(Prim::Slot(op, *slot), self.tree.list(value))
            }
            Core::App(_, args) => {
                let mut ids = last(args.len() + 1);
                let args = self.tree.list(ids.drain(1..));
                Node::App(ids[0], args)
            }
            Core::Lambda(f) => {
                let body = last(1)[0];
                for &v in f.params.iter().chain(&f.rest) {
                    self.scope.remove(&v);
                }
                let params = self.tree.list(f.params.iter().copied());
                Node::Lambda(self.tree.function(Function { id: f.id, params, optional: f.optional, rest: f.rest, body }))
            }
            Core::Intrinsic(prim, args) => Node::Intrinsic(*prim, self.tree.list(last(args.len()))),
            Core::ApplyIntrinsic(prim, args) => Node::ApplyIntrinsic(*prim, self.tree.list(last(args.len()))),
            Core::Quote(_) | Core::Ref(_) => unreachable!("leaves are lowered as they're reached"),
        }
    }

    fn reserve_var(&mut self, v: Var) -> Result<(), CompileError> {
        if !self.bound.insert(v) {
            return Err(CompileError::Rebound(v));
        }
        self.max_var = self.max_var.max(v.0.saturating_add(1));
        Ok(())
    }

    fn check_bound(&self, v: Var) -> Result<(), CompileError> {
        if !self.scope.contains(&v) {
            return Err(CompileError::Unbound(v));
        }
        Ok(())
    }
}
