//! Macros that a program defines. `define-syntax`, `let-syntax` and `letrec-syntax` bind a name to a
//! transformer. A transformer is a procedure that takes the syntax object of a macro use and returns the syntax
//! to expand in its place. The expander runs transformers during expansion, in a machine of their own. A macro step flips a fresh scope on the
//! transformer's input and on its output, as a step of a built-in macro does.
//!
//! A running transformer does not call back into the expander. Each identifier in its input carries a value that
//! identifies its binding, and its patterns and templates are VM values. If a transformer raises a syntax error
//! and does not catch it, the expander reports bad syntax at the form that the error names.

use ragwort_compiler::steps::Step;
use ragwort_compiler::{CompileError, Core, compile};
use ragwort_types::gc::Value;
use ragwort_types::pair::Pair;
use ragwort_types::syntax::{Syntax, SyntaxSpan};
use ragwort_vm::objects::{Closure, Condition, ConditionFields};
use ragwort_types::gc::OutOfMemory;
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use crate::expand::{Binding, Call, Ex, Expander};
use crate::scope::{Op, Scope};
use crate::tree::Stx;
use crate::{ExpandError, ExpandErrorKind};

impl<'a, 'gc> Expander<'a, 'gc> {
    /// Returns the identifier that the `define-syntax` form `form` binds, and the expression for its transformer.
    pub(crate) fn syntax_definition(&mut self, form: Stx) -> Result<(Stx, Stx), ExpandError> {
        match *self.proper(form)?.as_slice() {
            [_, id, expr] if self.is_id(id) => Ok((id, expr)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, form)),
        }
    }

    /// Creates the transformer of `form`, a `define-syntax` at the top level. Returns the identifier that `form` binds, and the index of the transformer.
    pub(crate) fn define_syntax_now(&mut self, form: Stx) -> Result<(Stx, u32), ExpandError> {
        let (id, expr) = self.syntax_definition(form)?;
        let core = self.expand_now(expr)?;
        Ok((id, self.made_transformer(&core, expr, form)?))
    }

    /// Expands a `let-syntax` form, or a `letrec-syntax` form if `recursive`. The transformer expressions of
    /// `letrec-syntax` are in the scope of the names that the form binds.
    pub(crate) fn let_syntax(&mut self, stx: Stx, binds: Stx, body: Vec<Stx>, recursive: bool) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let (mut ids, mut exprs) = (Vec::new(), Vec::new());
        for bind in self.proper(binds)? {
            match *self.proper(bind)?.as_slice() {
                [id, expr] if self.is_id(id) => {
                    ids.push(self.tree.with(id, scope, Op::Add)?);
                    exprs.push(if recursive { self.tree.with(expr, scope, Op::Add)? } else { expr });
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, bind)),
            }
        }
        self.distinct(&ids)?;
        let macros: Vec<_> = ids.into_iter().zip(exprs).collect();
        self.let_macros(stx, macros.into_iter(), body, scope)
    }

    /// Creates the transformer of each of `macros` in turn and binds the macro's identifier to it. Then expands `body`.
    fn let_macros(&mut self, stx: Stx, mut macros: std::vec::IntoIter<(Stx, Stx)>, body: Vec<Stx>, scope: Scope) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some((id, expr)) = macros.next() else {
            let body = self.scoped(&body, scope)?;
            return Ok(Step::Tail(Call::Run(Box::new(move |this: &mut Self| this.body(stx, body)))));
        };
        self.transformer(expr, stx, move |this, macro_index| {
            this.bind(id, Binding::Macro(macro_index))?;
            this.let_macros(stx, macros, body, scope)
        })
    }

    /// Expands `expr`, the transformer expression of a macro that the form `at` defines. Then compiles and runs
    /// the expansion, stores the transformer, and passes its index to `then`.
    pub(crate) fn transformer(&mut self, expr: Stx, at: Stx, then: impl FnOnce(&mut Self, u32) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Self::expr(expr, move |this, core| {
            let macro_index = this.made_transformer(&core, expr, at)?;
            then(this, macro_index)
        })
    }

    /// Compiles and runs `core`, the expansion of the transformer expression `expr` of a macro that the form `at`
    /// defines. Stores the resulting transformer in `macros` and returns its index.
    fn made_transformer(&mut self, core: &Core<'gc>, expr: Stx, at: Stx) -> Result<u32, ExpandError> {
        let thunk = compile(self.mc, None, core).map_err(|error| match error {
            // The transformer refers to a variable of the surrounding code, which does not exist yet.
            CompileError::Unbound(_) | CompileError::UnknownSlot(_) => self.error(ExpandErrorKind::Phase, expr),
            CompileError::OutOfMemory => self.error(OutOfMemory, at),
            _ => self.error(ExpandErrorKind::Transformer, at),
        })?;
        let transformer = self.run(thunk, &[], at)?;
        if transformer.downcast::<Closure>(self.mc).is_none() {
            return Err(self.error(ExpandErrorKind::Transformer, at));
        }
        let macro_index = u32::try_from(self.macros.len()).map_err(|_| self.error(ExpandErrorKind::Transformer, at))?;
        self.macros.push(transformer);
        Ok(macro_index)
    }

    /// Expands `stx`, a use of the macro with index `macro_index`, by one step.
    pub(crate) fn expand_macro(&mut self, macro_index: u32, stx: Stx) -> Result<Stx, ExpandError> {
        let intro = self.tree.scopes.fresh()?;
        let input = self.tree.with(stx, intro, Op::Flip)?;
        let input = self.wrap(input)?;
        let output = self.run(self.macros[macro_index as usize], &[input], stx)?;
        let output = self.unwrap(output, stx)?;
        Ok(self.tree.with(output, intro, Op::Flip)?)
    }

    /// Calls `procedure` with `args` and runs it to completion, for the macro use or
    /// definition `at`. A run that pauses is resumed at once. All transformers of a load run one after another in one machine. Nothing
    /// is collected during expansion, so a separate stack for each transformer would add up.
    fn run(&mut self, procedure: Value<'gc>, args: &[Value<'gc>], at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mc = self.mc;
        let started = match self.machine.take() {
            Some(mut machine) => machine.restart(mc, procedure, args).map(|()| machine),
            None => Machine::new(mc, MIN_SEGMENT, procedure, args).map(|mut machine| {
                machine.set_fuel(self.fuel);
                machine
            }),
        };
        let mut machine = started.map_err(|fault| self.failed(fault, at))?;
        let mut outcome = machine.run(mc);
        let result = loop {
            match outcome {
                Ok(Outcome::Paused) => outcome = machine.run(mc),
                Ok(Outcome::Done(value)) => break Ok(value),
                Ok(Outcome::Raised(raised)) => break Err(self.raised(raised, at)),
                Err(fault) => break Err(self.failed(fault, at)),
                Ok(_) => break Err(self.error(ExpandErrorKind::Transformer, at)),
            }
        };
        self.machine = Some(machine);
        result
    }

    /// Returns the error of a transformer for `at` that stopped with `fault`.
    fn failed(&self, fault: Fault, at: Stx) -> ExpandError {
        match fault {
            Fault::OutOfMemory => self.error(OutOfMemory, at),
            _ => self.error(ExpandErrorKind::Transformer, at),
        }
    }

    /// Returns the error for a transformer for `at` that raised `raised`. A syntax error becomes `BadSyntax` at
    /// the span of its last irritant, which is the innermost form that it names. Any other value becomes `Transformer` at `at`.
    fn raised(&self, raised: Value<'gc>, at: Stx) -> ExpandError {
        let mc = self.mc;
        let Some(condition) = raised.downcast::<Condition>(mc).filter(|condition| condition.failure(mc).is_some_and(|failure| failure.fault == Fault::Syntax)) else {
            return self.error(ExpandErrorKind::Transformer, at);
        };
        let (mut form, mut rest) = (Value::VOID, condition.irritants(mc));
        while let Some(pair) = Pair::of(rest) {
            (form, rest) = (pair.head(mc), pair.tail(mc));
        }
        self.error_at(ExpandErrorKind::BadSyntax, self.span_of(form, at))
    }

    /// Returns the source span of the syntax object `value`. Returns the span of `at` if `value` is not a syntax object or has no source.
    pub(crate) fn span_of(&self, value: Value<'gc>, at: Stx) -> SyntaxSpan<'gc> {
        Syntax::of(value).map(|syntax| syntax.span(self.mc)).filter(|span| span.source().is_some()).unwrap_or_else(|| self.tree.span(at))
    }
}
