//! Macros defined in the code: `define-syntax`, `let-syntax` and `letrec-syntax` bind a name to a
//! transformer, a procedure the expander runs as it goes, in a machine of its own, on the syntax
//! of each use, for the syntax to expand in its place. A step flips a fresh scope on what the
//! transformer's given and on what it makes, as the built-in macros' do.
//!
//! A transformer needs nothing of the expander's as it runs: what it's given says what each of its
//! identifiers refers to, and its patterns and templates are values of the VM's. A syntax error
//! it raises, that it doesn't catch, is bad syntax where the error says.

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
    /// The identifier a `define-syntax` binds, and its transformer's expression.
    pub(crate) fn syntax_definition(&mut self, form: Stx) -> Result<(Stx, Stx), ExpandError> {
        match *self.proper(form)?.as_slice() {
            [_, id, expr] if self.is_id(id) => Ok((id, expr)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, form)),
        }
    }

    /// The identifier a `define-syntax` at the top level binds, and its transformer.
    pub(crate) fn define_syntax_now(&mut self, form: Stx) -> Result<(Stx, u32), ExpandError> {
        let (id, expr) = self.syntax_definition(form)?;
        let core = self.expand_now(expr)?;
        Ok((id, self.made_transformer(&core, expr, form)?))
    }

    /// A `let-syntax`, or if `recursive`, a `letrec-syntax`, whose transformers see what it
    /// binds.
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

    /// Binds each of `macros` to its transformer, made in turn, then expands `body`.
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

    /// Expands `expr`, the transformer of a macro `at` defines, then compiles, runs and keeps
    /// it, and goes on with `then`.
    pub(crate) fn transformer(&mut self, expr: Stx, at: Stx, then: impl FnOnce(&mut Self, u32) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Self::expr(expr, move |this, core| {
            let macro_index = this.made_transformer(&core, expr, at)?;
            then(this, macro_index)
        })
    }

    /// Compiles and runs `core`, the expansion of `expr`, the transformer of a macro `at`
    /// defines, and keeps it.
    fn made_transformer(&mut self, core: &Core<'gc>, expr: Stx, at: Stx) -> Result<u32, ExpandError> {
        let thunk = compile(self.mc, None, core).map_err(|error| match error {
            // It refers to a variable of the code around it, which isn't there yet.
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

    /// The use `stx` of the macro `macro_index`, expanded a step.
    pub(crate) fn expand_macro(&mut self, macro_index: u32, stx: Stx) -> Result<Stx, ExpandError> {
        let intro = self.tree.scopes.fresh()?;
        let input = self.tree.with(stx, intro, Op::Flip)?;
        let input = self.wrap(input)?;
        let output = self.run(self.macros[macro_index as usize], &[input], stx)?;
        let output = self.unwrap(output, stx)?;
        Ok(self.tree.with(output, intro, Op::Flip)?)
    }

    /// Runs `procedure` on `args` to its end, answering what it asks, for the macro use or
    /// definition `at`. The load's transformers run one after another in one machine, as
    /// nothing's collected while it's expanded, so a stack for each would add up.
    fn run(&mut self, procedure: Value<'gc>, args: &[Value<'gc>], at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mc = self.mc;
        let failed = |this: &Self, fault: Fault| match fault {
            Fault::OutOfMemory => this.error(OutOfMemory, at),
            _ => this.error(ExpandErrorKind::Transformer, at),
        };
        let started = match self.machine.take() {
            Some(mut machine) => machine.restart(mc, procedure, args).map(|()| machine),
            None => Machine::new(mc, MIN_SEGMENT, procedure, args).map(|mut machine| {
                machine.set_fuel(self.fuel);
                machine
            }),
        };
        let mut machine = started.map_err(|fault| failed(self, fault))?;
        let mut outcome = machine.run(mc);
        let result = loop {
            match outcome {
                Ok(Outcome::Paused) => outcome = machine.run(mc),
                Ok(Outcome::Done(value)) => break Ok(value),
                Ok(Outcome::Raised(raised)) => break Err(self.raised(raised, at)),
                Err(fault) => break Err(failed(self, fault)),
                Ok(_) => break Err(self.error(ExpandErrorKind::Transformer, at)),
            }
        };
        self.machine = Some(machine);
        result
    }

    /// What a transformer for `at` raising `raised` is: a syntax error is bad syntax where its
    /// innermost form is, and anything else is the transformer's failure.
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

    /// Where the syntax `value` came from, or `at` if it isn't syntax or has no span.
    pub(crate) fn span_of(&self, value: Value<'gc>, at: Stx) -> SyntaxSpan<'gc> {
        Syntax::of(value).map(|syntax| syntax.span(self.mc)).filter(|span| span.source().is_some()).unwrap_or_else(|| self.tree.span(at))
    }
}
