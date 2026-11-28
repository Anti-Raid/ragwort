//! Macros that a program defines. A macro's name is bound to a
//! transformer. A transformer is a procedure that takes the syntax object of a macro use and returns the syntax
//! to expand in its place. The expander runs transformers during expansion, in a machine of their own. A macro step flips a fresh scope on the
//! transformer's input and on its output, as a step of a built-in macro does.
//!
//! A running transformer does not call back into the expander. Each identifier in its input carries a value that
//! identifies its binding, and its patterns and templates are VM values. If a transformer raises a syntax error
//! and does not catch it, the expander reports bad syntax at the form that the error names.

use std::fmt;

use ragwort_compiler::{CompileError, Core, compile};
use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::pair::Pair;
use ragwort_types::syntax::{Syntax, SyntaxSpan};
use ragwort_vm::objects::{Closure, Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use crate::engine::Engine;
use crate::scope::Op;
use crate::tree::Stx;
use crate::{ExpandError, ExpandErrorKind};

impl<'a, 'gc, K: Copy + PartialEq + fmt::Debug> Engine<'a, 'gc, K> {
    /// Returns the identifier that the `define-syntax` form `form` binds, and the expression for its transformer.
    pub fn syntax_definition(&mut self, form: Stx) -> Result<(Stx, Stx), ExpandError> {
        match *self.proper(form)?.as_slice() {
            [_, id, expr] if self.is_id(id) => Ok((id, expr)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, form)),
        }
    }

    /// Compiles and runs `core`, the expansion of the transformer expression `expr` of a macro that the form `at`
    /// defines. Stores the resulting transformer in `macros` and returns its index.
    pub fn made_transformer(&mut self, core: &Core<'gc>, expr: Stx, at: Stx) -> Result<u32, ExpandError> {
        let thunk = compile(self.mc, None, core).map_err(|error| match error {
            // The transformer refers to a variable of the surrounding code, which does not exist yet.
            CompileError::Unbound(_) | CompileError::UnknownSlot(_) | CompileError::Global { .. } => self.error(ExpandErrorKind::Phase, expr),
            CompileError::OutOfMemory => self.error(OutOfMemory, at),
            _ => self.error(ExpandErrorKind::Transformer, at),
        })?;
        let transformer = self.run(thunk, &[], at)?;
        if transformer.downcast::<Closure>(self.mc).is_none() {
            return Err(self.error(ExpandErrorKind::Transformer, at));
        }
        let macro_index = u32::try_from(self.macros.len()).map_err(|_| self.error(ExpandErrorKind::Transformer, at))?;
        self.macros.push(transformer);
        self.macro_names.push(None);
        self.macro_refs.push(Vec::new());
        Ok(macro_index)
    }

    /// Expands `stx`, a use of the macro with index `macro_index`, by one step.
    pub fn expand_macro(&mut self, macro_index: u32, stx: Stx) -> Result<Stx, ExpandError> {
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
    pub fn run(&mut self, procedure: Value<'gc>, args: &[Value<'gc>], at: Stx) -> Result<Value<'gc>, ExpandError> {
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
    pub fn failed(&self, fault: Fault, at: Stx) -> ExpandError {
        match fault {
            Fault::OutOfMemory => self.error(OutOfMemory, at),
            _ => self.error(ExpandErrorKind::Transformer, at),
        }
    }

    /// Returns the error for a transformer for `at` that raised `raised`. A syntax error becomes `BadSyntax` at
    /// the span of its last irritant, which is the innermost form that it names. Any other value becomes `Transformer` at `at`.
    pub fn raised(&self, raised: Value<'gc>, at: Stx) -> ExpandError {
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
    pub fn span_of(&self, value: Value<'gc>, at: Stx) -> SyntaxSpan<'gc> {
        Syntax::of(value).map(|syntax| syntax.span(self.mc)).filter(|span| span.source().is_some()).unwrap_or_else(|| self.tree.span(at))
    }
}
