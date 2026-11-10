//! Pass 1 (`Core -> L1`): validates the input AST and lowers module variables (`Place::Slot`)
//! into slot primitives.

use ragwort_alloc::{Arena, CollectIn, Vec, vec_in};

use crate::hash::HashSet;
use crate::ir::{Func, L1, Supply};
use crate::{CompileError, Core, Lambda, Place, Prim, SlotOp, Var};

/// How deeply expressions can nest before compiling them would take too much of the native stack.
pub(crate) const MAX_DEPTH: usize = 256;

pub(crate) fn lower<'a, 'gc>(arena: &'a Arena, core: &Core<'gc>) -> Result<(L1<'a, 'gc>, Supply), CompileError> {
    let mut pass = Lower {
        arena,
        bound: HashSet::default(),
        scope: HashSet::default(),
        lambdas: HashSet::default(),
        max_var: 0,
        max_lambda: 0,
        depth: 0,
    };
    let l1 = pass.expr(core)?;
    let supply = Supply { next_var: pass.max_var, next_lambda: pass.max_lambda };
    Ok((l1, supply))
}

struct Lower<'a> {
    arena: &'a Arena,
    bound: HashSet<Var>,
    scope: HashSet<Var>,
    lambdas: HashSet<u32>,
    max_var: u32,
    max_lambda: u32,
    depth: usize,
}

impl<'a> Lower<'a> {
    fn expr<'gc>(&mut self, core: &Core<'gc>) -> Result<L1<'a, 'gc>, CompileError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(CompileError::TooDeep);
        }
        let out = match core {
            Core::Quote(v) => L1::Quote(*v),
            Core::Ref(Place::Local(v)) => {
                self.check_bound(*v)?;
                L1::Ref(*v)
            }
            Core::Ref(Place::Slot { slot, checked }) => {
                L1::Intrinsic(Prim::Slot(if *checked { SlotOp::LoadChecked } else { SlotOp::Load }, *slot), self.arena.vec())
            }
            Core::If(test, then, other) => {
                let (test, then) = (self.expr(test)?, self.expr(then)?);
                L1::If(self.arena.boxed(test), self.arena.boxed(then), self.arena.boxed(self.expr(other)?))
            },
            Core::Let(binds, body) => self.let_form(binds, body)?,
            Core::Letrec(binds, body) => self.letrec_form(binds, body)?,
            Core::Set(Place::Local(v), value) => {
                self.check_bound(*v)?;
                L1::Set(*v, self.arena.boxed(self.expr(value)?))
            }
            Core::Set(Place::Slot { slot, checked }, value) => {
                let op = if *checked { SlotOp::StoreChecked } else { SlotOp::Store };
                L1::Intrinsic(Prim::Slot(op, *slot), vec_in![self.arena; self.expr(value)?])
            }
            Core::App(f, args) => {
                let f = self.expr(f)?;
                L1::App(self.arena.boxed(f), self.exprs(args)?)
            }
            Core::Lambda(f) => self.lambda_form(f)?,
            Core::Intrinsic(prim, args) => {
                let takes = match *prim {
                    Prim::Intrinsic(i) => i.arity().is_none_or(|n| usize::from(n) == args.len()),
                    Prim::Read(r) => usize::from(r.arity()) == args.len(),
                    Prim::Request(r) => r.takes(args.len()),
                    Prim::Host(h) => h.takes(args.len()),
                    Prim::Slot(op, _) => op.arity() == args.len(),
                };
                if !takes {
                    return Err(CompileError::Arity(*prim));
                }
                L1::Intrinsic(*prim, self.exprs(args)?)
            }
            Core::ApplyIntrinsic(prim, args) => {
                // A read takes a fixed number of arguments, so its prelude wrapper spreads them, and
                // a host function's arguments must fit a frame.
                if args.is_empty() || matches!(prim, Prim::Read(_) | Prim::Host(_) | Prim::Slot(..)) {
                    return Err(CompileError::Arity(*prim));
                }
                L1::ApplyIntrinsic(*prim, self.exprs(args)?)
            }
        };
        self.depth -= 1;
        Ok(out)
    }

    #[inline(never)]
    fn let_form<'gc>(&mut self, binds: &[(Var, Core<'gc>)], body: &Core<'gc>) -> Result<L1<'a, 'gc>, CompileError> {
        for &(v, _) in binds {
            self.reserve_var(v)?;
        }
        let mut lowered = Vec::with_capacity_in(binds.len(), self.arena);
        for &(v, ref init) in binds {
            lowered.push((v, self.expr(init)?));
        }
        for &(v, _) in &lowered {
            self.scope.insert(v);
        }
        let body = self.expr(body)?;
        for &(v, _) in &lowered {
            self.scope.remove(&v);
        }
        Ok(L1::Let(lowered, self.arena.boxed(body)))
    }

    #[inline(never)]
    fn letrec_form<'gc>(&mut self, binds: &[(Var, Core<'gc>)], body: &Core<'gc>) -> Result<L1<'a, 'gc>, CompileError> {
        for &(v, _) in binds {
            self.reserve_var(v)?;
            self.scope.insert(v);
        }
        let mut lowered = Vec::with_capacity_in(binds.len(), self.arena);
        for &(v, ref init) in binds {
            lowered.push((v, self.expr(init)?));
        }
        let body = self.expr(body)?;
        for &(v, _) in &lowered {
            self.scope.remove(&v);
        }
        Ok(L1::Letrec(lowered, self.arena.boxed(body)))
    }

    #[inline(never)]
    fn lambda_form<'gc>(&mut self, f: &Lambda<'gc>) -> Result<L1<'a, 'gc>, CompileError> {
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
        let body = self.expr(&f.body)?;
        for &v in f.params.iter().chain(&f.rest) {
            self.scope.remove(&v);
        }
        let params = f.params.iter().copied().collect_in(self.arena);
        Ok(L1::Lambda(Func { id: f.id, params, optional: f.optional, rest: f.rest, body: self.arena.boxed(body) }))
    }

    fn exprs<'gc>(&mut self, exprs: &[Core<'gc>]) -> Result<Vec<'a, L1<'a, 'gc>>, CompileError> {
        let arena = self.arena;
        exprs.iter().map(|e| self.expr(e)).try_collect_in(arena)
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
