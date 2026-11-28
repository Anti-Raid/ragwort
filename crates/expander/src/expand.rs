//! The operations that expand expressions of the front end's language.
//!
//! The engine does not know how a language's expressions are expanded. A front end says so by implementing [`Host`]. Every host then
//! has the operations of [`Expand`].

use std::fmt;
use std::ops::DerefMut;
use std::rc::Rc;

use ragwort_compiler::steps::{self, Step};
use ragwort_compiler::{Core, Lambda, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_vm::syntax_case;
use ragwort_vm::{Intrinsic, Request};

use crate::case::local;
use crate::engine::{Binding, Engine};
use crate::scope::Op;
use crate::tree::Stx;
use crate::{ExpandError, ExpandErrorKind};

/// The next step of expanding an expression. See [`steps`]. Each call produces a [`Core`] form. `H` is the front end's expander.
pub type Ex<'a, 'gc, H> = Step<'a, H, Call<'a, 'gc, H>, Core<'gc>, ExpandError>;

/// A call that the step driver runs for the expander.
pub enum Call<'a, 'gc, H> {
    /// Expands the expression.
    Expr(Stx),
    /// Runs the function, which returns the next step.
    Run(Work<'a, 'gc, H>),
}

/// A deferred part of an expansion: a function that takes the expander and returns the next step.
pub type Work<'a, 'gc, H> = Box<dyn FnOnce(&mut H) -> Result<Ex<'a, 'gc, H>, ExpandError> + 'a>;

/// A front end's expander: a type that holds an [`Engine`] and expands the expressions of its language.
pub trait Host<'a, 'gc: 'a>: DerefMut<Target = Engine<'a, 'gc, Self::Keyword>> + Sized + 'a {
    /// The language's keywords.
    type Keyword: Copy + PartialEq + fmt::Debug;

    /// Returns the first step of expanding the expression `stx`: the finished core form, or a request to expand parts of `stx` first.
    fn expand(&mut self, stx: Stx) -> Result<Ex<'a, 'gc, Self>, ExpandError>;

    /// Returns the first step of expanding an assignment of the expression `value` to the variable that the identifier `id` names.
    fn assign(&mut self, id: Stx, value: Stx) -> Result<Ex<'a, 'gc, Self>, ExpandError>;
}

/// The operations of the engine that expand expressions. Every [`Host`] has them.
pub trait Expand<'a, 'gc: 'a>: Host<'a, 'gc> {
    /// Expands the expression `stx` to a core form. The step driver keeps the pending continuations on a heap-allocated
    /// stack. So the native stack does not grow with the nesting depth of `stx`.
    fn expand_now(&mut self, stx: Stx) -> Result<Core<'gc>, ExpandError> {
        steps::run(self, Call::Expr(stx), Self::step)
    }

    /// Runs one call for the step driver. An error with an empty span, such as an out-of-memory error, gets the span of
    /// the expression being expanded.
    fn step(&mut self, call: Call<'a, 'gc, Self>) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        match call {
            Call::Expr(stx) => self.expand(stx).map_err(|error| self.placed(error, stx)),
            Call::Run(run) => run(self),
        }
    }

    /// Returns a step that expands the expression `stx` and passes the core form to `then`.
    fn expr(stx: Stx, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Ex<'a, 'gc, Self>, ExpandError> + 'a) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        Ok(Step::then(Call::Expr(stx), then))
    }

    /// Returns a step that expands each of `stxs` in order and passes the core forms to `then`.
    fn exprs(stxs: Vec<Stx>, then: impl FnOnce(&mut Self, Vec<Core<'gc>>) -> Result<Ex<'a, 'gc, Self>, ExpandError> + 'a) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        steps::all(stxs.into_iter().map(Call::Expr).collect(), then)
    }

    /// Creates the transformer of `form`, a `define-syntax` at the top level. Returns the identifier that `form` binds, and the index of the transformer.
    fn define_syntax_now(&mut self, form: Stx) -> Result<(Stx, u32), ExpandError> {
        let (id, expr) = self.syntax_definition(form)?;
        // The syntax quoted from here on belongs to this transformer. See `Engine::macro_refs`.
        let outer = std::mem::take(&mut self.quoted);
        self.in_transformer = true;
        let core = self.expand_now(expr);
        self.in_transformer = false;
        let refers_to = std::mem::replace(&mut self.quoted, outer);
        let macro_index = self.made_transformer(&core?, expr, form)?;
        self.macro_refs[macro_index as usize] = refers_to;
        Ok((id, macro_index))
    }

    /// Expands `expr`, the transformer expression of a macro that the form `at` defines. Then compiles and runs
    /// the expansion, stores the transformer, and passes its index to `then`.
    fn transformer(&mut self, expr: Stx, at: Stx, then: impl FnOnce(&mut Self, u32) -> Result<Ex<'a, 'gc, Self>, ExpandError> + 'a) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let outer = std::mem::take(&mut self.quoted);
        Self::expr(expr, move |this, core| {
            let macro_index = this.made_transformer(&core, expr, at)?;
            // A macro defined in a body is used only in that body, so its templates do not leave the module. Inside the transformer of a top-level
            // macro, they are counted with that transformer.
            let inner = std::mem::replace(&mut this.quoted, outer);
            if this.in_transformer {
                this.quoted.extend(inner);
            }
            then(this, macro_index)
        })
    }

    /// Expands `(syntax-case input (literal ...) clause ...)`. A clause is `(pattern output)` or `(pattern
    /// fender output)`. The clauses are tried in order. The pattern variables of a clause are bound in its fender and its output.
    fn syntax_case(&mut self, input: Stx, literals: Stx, clauses: Vec<Stx>) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let literals = self.proper(literals)?;
        if let Some(&bad) = literals.iter().find(|&&id| !self.is_id(id)) {
            return Err(self.error(ExpandErrorKind::BadSyntax, bad));
        }
        let var = self.fresh();
        let (literals, clauses): (Rc<[Stx]>, Rc<[Stx]>) = (literals.into(), clauses.into());
        Self::expr(input, move |_, value| {
            Ok(Step::then(Call::Run(Box::new(move |this: &mut Self| this.clauses(var, literals, clauses, 0))), move |_: &mut Self, clauses| Ok(Step::Done(Core::Let(vec![(var, value)], Box::new(clauses))))))
        })
    }

    /// Expands the clauses from index `at` on. Each clause is tried if the clauses before it do not match. If no clause matches, the code raises a syntax error with the input.
    fn clauses(&mut self, input: Var, literals: Rc<[Stx]>, clauses: Rc<[Stx]>, at: usize) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let Some(&clause) = clauses.get(at) else {
            let error = Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeSyntaxError), vec![Core::Quote(Value::VOID), local(input)], None);
            return Ok(Step::Done(Core::Intrinsic(Prim::Request(Request::Raise), vec![error], None)));
        };
        let (pattern, fender, output) = match *self.proper(clause)?.as_slice() {
            [pattern, output] => (pattern, None, output),
            [pattern, fender, output] => (pattern, Some(fender), output),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
        };
        let (mut vars, mut items) = (Vec::new(), Vec::new());
        let mut shape = self.pattern(pattern, &literals, &mut vars, &mut items)?;
        shape.vars = u32::try_from(vars.len()).expect("fewer than 2^32 variables");
        let pattern = Core::Quote(syntax_case::pattern(self.mc, shape, &items)?);
        let asked = Core::Intrinsic(Prim::Intrinsic(Intrinsic::SyntaxMatch), vec![pattern, local(input)], None);
        let scope = self.tree.scopes.fresh()?;
        let ids = vars.iter().map(|&(id, _)| self.tree.with(id, scope, Op::Add)).collect::<Result<Vec<_>, _>>()?;
        self.distinct(&ids)?;
        let matched = self.fresh();
        let mut binds = Vec::with_capacity(ids.len());
        for (slot, (&id, &(_, depth))) in ids.iter().zip(&vars).enumerate() {
            let var = self.fresh();
            self.bind(id, Binding::Pattern { var, depth })?;
            let at = Core::Quote(Value::fixnum(slot as i64).expect("a fixnum"));
            binds.push((var, Core::Intrinsic(Prim::Intrinsic(Intrinsic::VectorRef), vec![local(matched), at], None)));
        }
        let output = self.tree.with(output, scope, Op::Add)?;
        let fender = fender.map(|fender| self.tree.with(fender, scope, Op::Add)).transpose()?;
        Ok(Step::then(Call::Run(Box::new(move |this: &mut Self| this.clauses(input, literals, clauses, at + 1))), move |_, next| {
            Self::expr(output, move |this, output| {
                let Some(fender) = fender else {
                    let body = Core::Let(binds, Box::new(output));
                    return Ok(Step::Done(Core::Let(vec![(matched, asked)], Box::new(Core::If(Box::new(local(matched)), Box::new(body), Box::new(next))))));
                };
                // The remaining clauses are tried if the fender fails or the pattern does not match. So their code goes into a thunk that both cases call.
                let retry = this.fresh();
                let thunk = Core::Lambda(Lambda { id: this.lambda_id(), params: Vec::new(), optional: 0, rest: None, body: Box::new(next), name: None, at: None });
                Self::expr(fender, move |_, fender| {
                    fn again<'gc>(retry: Var) -> Core<'gc> {
                        Core::App(Box::new(local(retry)), Vec::new(), None)
                    }
                    let body = Core::If(Box::new(fender), Box::new(output), Box::new(again(retry)));
                    let body = Core::Let(binds, Box::new(body));
                    let tried = Core::If(Box::new(local(matched)), Box::new(body), Box::new(again(retry)));
                    Ok(Step::Done(Core::Let(vec![(retry, thunk)], Box::new(Core::Let(vec![(matched, asked)], Box::new(tried))))))
                })
            })
        }))
    }
}

impl<'a, 'gc: 'a, H: Host<'a, 'gc>> Expand<'a, 'gc> for H {}
