//! Pass 1 (`Core -> L1`): validates the input AST and lowers globals (`DefineGlobal`,
//! `Place::Global`, `Place::Import`) into explicit intrinsics and constants.

use std::collections::HashSet;

use ragwort_types::gc::{Mutation, Value};
use ragwort_vm::Intrinsic;
use ragwort_vm::objects::GlobalFields;

use crate::ir::{L1, Supply};
use crate::{CompileError, Core, Func, Lambda, Place, Prim, Var};

/// How deeply expressions can nest before compiling them would take too much of the native stack.
const MAX_DEPTH: usize = 256;

pub(crate) fn lower_globals<'gc>(mc: &Mutation<'gc>, core: &Core<'gc>) -> Result<(L1<'gc>, Supply), CompileError> {
    let mut pass = Lower {
        mc,
        bound: HashSet::new(),
        scope: HashSet::new(),
        lambdas: HashSet::new(),
        max_var: 0,
        max_lambda: 0,
        depth: 0,
    };
    let l1 = pass.expr(core)?;
    let supply = Supply { next_var: pass.max_var, next_lambda: pass.max_lambda };
    Ok((l1, supply))
}

struct Lower<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    bound: HashSet<Var>,
    scope: HashSet<Var>,
    lambdas: HashSet<u32>,
    max_var: u32,
    max_lambda: u32,
    depth: usize,
}

impl<'gc> Lower<'_, 'gc> {
    fn expr(&mut self, core: &Core<'gc>) -> Result<L1<'gc>, CompileError> {
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
            Core::Ref(Place::Import(g)) if g.defined(self.mc) => L1::Quote(g.value(self.mc)),
            Core::Ref(Place::Global(g) | Place::Import(g)) => {
                L1::Intrinsic(Prim::Intrinsic(Intrinsic::GlobalRef), vec![L1::Quote(Value::object(self.mc, *g))])
            }
            Core::If(test, then, other) => L1::If(Box::new(self.expr(test)?), Box::new(self.expr(then)?), Box::new(self.expr(other)?)),
            Core::Let(binds, body) => self.let_form(binds, body)?,
            Core::Letrec(binds, body) => self.letrec_form(binds, body)?,
            Core::Set(Place::Local(v), value) => {
                self.check_bound(*v)?;
                L1::Set(*v, Box::new(self.expr(value)?))
            }
            Core::Set(Place::Global(g) | Place::Import(g), value) => {
                let value = self.expr(value)?;
                L1::Intrinsic(Prim::Intrinsic(Intrinsic::GlobalSet), vec![L1::Quote(Value::object(self.mc, *g)), value])
            }
            Core::DefineGlobal(g, value) => {
                let value = self.expr(value)?;
                L1::Intrinsic(Prim::Intrinsic(Intrinsic::DefineGlobal), vec![L1::Quote(Value::object(self.mc, *g)), value])
            }
            Core::App(f, args) => L1::App(Box::new(self.expr(f)?), self.exprs(args)?),
            Core::Lambda(f) => self.lambda_form(f)?,
            Core::Intrinsic(prim, args) => {
                let takes = match *prim {
                    Prim::Intrinsic(i) => i.arity().is_none_or(|n| usize::from(n) == args.len()),
                    Prim::Read(r) => usize::from(r.arity()) == args.len(),
                    Prim::Request(r) => r.takes(args.len()),
                };
                if !takes {
                    return Err(CompileError::Arity(*prim));
                }
                L1::Intrinsic(*prim, self.exprs(args)?)
            }
            Core::ApplyIntrinsic(prim, args) => {
                // A read takes a fixed number of arguments, so its prelude wrapper spreads them.
                if args.is_empty() || matches!(prim, Prim::Read(_)) {
                    return Err(CompileError::Arity(*prim));
                }
                L1::ApplyIntrinsic(*prim, self.exprs(args)?)
            }
        };
        self.depth -= 1;
        Ok(out)
    }

    #[inline(never)]
    fn let_form(&mut self, binds: &[(Var, Core<'gc>)], body: &Core<'gc>) -> Result<L1<'gc>, CompileError> {
        for &(v, _) in binds {
            self.reserve_var(v)?;
        }
        let mut lowered = Vec::with_capacity(binds.len());
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
        Ok(L1::Let(lowered, Box::new(body)))
    }

    #[inline(never)]
    fn letrec_form(&mut self, binds: &[(Var, Core<'gc>)], body: &Core<'gc>) -> Result<L1<'gc>, CompileError> {
        for &(v, _) in binds {
            self.reserve_var(v)?;
            self.scope.insert(v);
        }
        let mut lowered = Vec::with_capacity(binds.len());
        for &(v, ref init) in binds {
            lowered.push((v, self.expr(init)?));
        }
        let body = self.expr(body)?;
        for &(v, _) in &lowered {
            self.scope.remove(&v);
        }
        Ok(L1::Letrec(lowered, Box::new(body)))
    }

    #[inline(never)]
    fn lambda_form(&mut self, f: &Lambda<'gc>) -> Result<L1<'gc>, CompileError> {
        if !self.lambdas.insert(f.id) {
            return Err(CompileError::SameLambda(f.id));
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
        Ok(L1::Lambda(Func { id: f.id, params: f.params.clone(), rest: f.rest, body: Box::new(body) }))
    }

    fn exprs(&mut self, exprs: &[Core<'gc>]) -> Result<Vec<L1<'gc>>, CompileError> {
        exprs.iter().map(|e| self.expr(e)).collect()
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
