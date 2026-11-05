//! What the code generator needs to know before it starts: which variables a lambda captures,
//! so they're boxed where they're bound, and each lambda's free variables, in the order its
//! closures keep them as upvalues.

use std::collections::{HashMap, HashSet};

use crate::compile::{CompileError, MAX_DEPTH};
use crate::{Core, Lambda, Place, Var};

pub(crate) struct Analysis {
    pub(crate) captured: HashSet<Var>,
    /// Each lambda's free variables, by its id.
    free: HashMap<u32, Vec<Var>>,
}

impl Analysis {
    pub(crate) fn free(&self, lambda: &Lambda<'_>) -> &[Var] {
        self.free.get(&lambda.id).map_or(&[], Vec::as_slice)
    }
}

/// Analyzes `body`, the body of a lambda of no parameters.
pub(crate) fn analyze(body: &Core<'_>) -> Result<Analysis, CompileError> {
    let mut walk = Walk { bound: HashMap::new(), all: HashSet::new(), lambdas: Vec::new(), captured: HashSet::new(), free: HashMap::new(), depth: 0 };
    walk.expr(body)?;
    Ok(Analysis { captured: walk.captured, free: walk.free })
}

struct Walk {
    /// How many lambdas each variable in scope is bound inside.
    bound: HashMap<Var, usize>,
    /// Every variable bound so far, in scope or not.
    all: HashSet<Var>,
    /// The lambdas around what's being walked, with their free variables so far.
    lambdas: Vec<(Vec<Var>, HashSet<Var>)>,
    captured: HashSet<Var>,
    free: HashMap<u32, Vec<Var>>,
    depth: usize,
}

impl Walk {
    fn expr(&mut self, e: &Core<'_>) -> Result<(), CompileError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(CompileError::TooDeep);
        }
        match e {
            Core::Quote(_) | Core::Ref(Place::Global(_)) => {}
            Core::Ref(Place::Local(v)) => self.refer(*v)?,
            Core::If(test, then, other) => {
                self.expr(test)?;
                self.expr(then)?;
                self.expr(other)?;
            }
            Core::Let(binds, body) => {
                binds.iter().try_for_each(|(_, init)| self.expr(init))?;
                binds.iter().try_for_each(|&(v, _)| self.bind(v))?;
                self.expr(body)?;
                binds.iter().for_each(|(v, _)| self.unbind(*v));
            }
            Core::Letrec(binds, body) => {
                binds.iter().try_for_each(|&(v, _)| self.bind(v))?;
                binds.iter().try_for_each(|(_, init)| self.expr(init))?;
                self.expr(body)?;
                binds.iter().for_each(|(v, _)| self.unbind(*v));
            }
            Core::Set(place, value) => {
                if let Place::Local(v) = place {
                    self.refer(*v)?;
                }
                self.expr(value)?;
            }
            Core::DefineGlobal(_, value) => self.expr(value)?,
            Core::App(f, args) => {
                self.expr(f)?;
                args.iter().try_for_each(|arg| self.expr(arg))?;
            }
            Core::Intrinsic(_, args) | Core::ApplyIntrinsic(_, args) => args.iter().try_for_each(|arg| self.expr(arg))?,
            Core::Lambda(lambda) => {
                self.lambdas.push((Vec::new(), HashSet::new()));
                lambda.params.iter().chain(&lambda.rest).try_for_each(|&v| self.bind(v))?;
                self.expr(&lambda.body)?;
                lambda.params.iter().chain(&lambda.rest).for_each(|&v| self.unbind(v));
                let (free, _) = self.lambdas.pop().expect("pushed above");
                if self.free.insert(lambda.id, free).is_some() {
                    return Err(CompileError::SameLambda(lambda.id));
                }
            }
        }
        self.depth -= 1;
        Ok(())
    }

    fn bind(&mut self, v: Var) -> Result<(), CompileError> {
        if !self.all.insert(v) {
            return Err(CompileError::Rebound(v));
        }
        self.bound.insert(v, self.lambdas.len());
        Ok(())
    }

    fn unbind(&mut self, v: Var) {
        self.bound.remove(&v);
    }

    /// A use of `v`, which is free in every lambda between its binding and here.
    fn refer(&mut self, v: Var) -> Result<(), CompileError> {
        let &at = self.bound.get(&v).ok_or(CompileError::Unbound(v))?;
        for (free, seen) in &mut self.lambdas[at..] {
            if seen.insert(v) {
                free.push(v);
            }
        }
        if at < self.lambdas.len() {
            self.captured.insert(v);
        }
        Ok(())
    }
}
