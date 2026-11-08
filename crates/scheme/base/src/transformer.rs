//! Macros defined in the code: `define-syntax`, `let-syntax` and `letrec-syntax` bind a name to a
//! transformer, a procedure the expander runs as it goes, in a machine of its own, on the syntax
//! of each use, for the syntax to expand in its place. A step flips a fresh scope on what the
//! transformer's given and on what it makes, as the built-in macros' do.
//!
//! What only the expander knows, a transformer asks with `host`: whether a pattern matches, the
//! syntax a template makes, what an identifier's bound to. The expander answers, and the machine
//! goes on.

use ragwort_compiler::{CompileError, Core, compile};
use ragwort_types::gc::Value;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxSpan};
use ragwort_vm::objects::{Closure, MultiValue, MultiValueFields};
use ragwort_types::gc::OutOfMemory;
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome, Request};

use crate::expand::{Binding, Expander};
use crate::scope::Op;
use crate::tree::Stx;
use crate::{ExpandError, ExpandErrorKind};

/// What a transformer asks the expander, with `host`: its first value. The prelude's syntax
/// procedures ask by these numbers too.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Ask {
    /// `(host 0 pattern input)`: the vector of what the pattern's variables matched, or `#f`.
    Match = 0,
    /// `(host 1 template value ...)`: the syntax the template makes of what its pattern
    /// variables matched.
    Build = 1,
    /// `(host 2 input)`: that no clause of a `syntax-case` matched `input`.
    NoMatch = 2,
    /// `(host 3 a b)`: `free-identifier=?`.
    FreeIdentifierEq = 3,
    /// `(host 4 list)`: `generate-temporaries`.
    Temporaries = 4,
    /// `(host 5 form)`: `syntax-violation`, of the syntax `form`.
    Violation = 5,
}

impl Ask {
    const ALL: [Ask; 6] = [Ask::Match, Ask::Build, Ask::NoMatch, Ask::FreeIdentifierEq, Ask::Temporaries, Ask::Violation];

    /// A call that asks this with `args`.
    pub(crate) fn call<'gc>(self, args: impl IntoIterator<Item = Core<'gc>>) -> Core<'gc> {
        let ask = Core::Quote(Value::fixnum(self as i64).expect("a fixnum"));
        Core::Intrinsic(ragwort_compiler::Prim::Request(Request::Host), std::iter::once(ask).chain(args).collect())
    }
}

impl<'gc> Expander<'_, 'gc> {
    /// The identifier a `define-syntax` binds, and its transformer.
    pub(crate) fn define_syntax(&mut self, form: Stx) -> Result<(Stx, u32), ExpandError> {
        match *self.proper(form)?.as_slice() {
            [_, id, expr] if self.is_id(id) => Ok((id, self.transformer(expr, form)?)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, form)),
        }
    }

    /// A `let-syntax`, or if `recursive`, a `letrec-syntax`, whose transformers see what it
    /// binds.
    pub(crate) fn let_syntax(&mut self, stx: Stx, binds: Stx, body: &[Stx], recursive: bool) -> Result<Core<'gc>, ExpandError> {
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
        for (id, expr) in ids.into_iter().zip(exprs) {
            let m = self.transformer(expr, stx)?;
            self.bind(id, Binding::Macro(m))?;
        }
        let body = self.scoped(body, scope)?;
        self.body(stx, &body)
    }

    /// Expands, compiles and runs `expr`, the transformer of a macro `at` defines, and keeps it.
    fn transformer(&mut self, expr: Stx, at: Stx) -> Result<u32, ExpandError> {
        let core = self.expr(expr)?;
        let thunk = compile(self.mc, None, &core).map_err(|e| match e {
            // It refers to a variable of the code around it, which isn't there yet.
            CompileError::Unbound(_) => self.error(ExpandErrorKind::Phase, expr),
            _ => self.error(ExpandErrorKind::Transformer, at),
        })?;
        let transformer = self.run(thunk, &[], at)?;
        if transformer.downcast::<Closure>(self.mc).is_none() {
            return Err(self.error(ExpandErrorKind::Transformer, at));
        }
        let m = u32::try_from(self.macros.len()).map_err(|_| self.error(ExpandErrorKind::Transformer, at))?;
        self.macros.push(transformer);
        Ok(m)
    }

    /// The use `stx` of the macro `m`, expanded a step.
    pub(crate) fn expand_macro(&mut self, m: u32, stx: Stx) -> Result<Stx, ExpandError> {
        let intro = self.tree.scopes.fresh()?;
        let input = self.tree.with(stx, intro, Op::Flip)?;
        let input = self.wrap(input)?;
        let output = self.run(self.macros[m as usize], &[input], stx)?;
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
                Ok(Outcome::Host(asked)) => match self.answer(asked, at) {
                    Ok(answer) => outcome = machine.reply(mc, answer),
                    Err(e) => break Err(e),
                },
                Ok(Outcome::Done(value)) => break Ok(value),
                Err(fault) => break Err(failed(self, fault)),
                Ok(_) => break Err(self.error(ExpandErrorKind::Transformer, at)),
            }
        };
        self.machine = Some(machine);
        result
    }

    fn answer(&mut self, asked: Value<'gc>, at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mc = self.mc;
        let values = match asked.downcast::<MultiValue>(mc) {
            Some(many) => {
                let items = many.items(mc);
                (0..items.len()).map(|i| items.get(i)).collect()
            }
            None => vec![asked],
        };
        let failed = |this: &Self| this.error(ExpandErrorKind::Transformer, at);
        let Some((ask, args)) = values.split_first() else { return Err(failed(self)) };
        let ask = ask.as_fixnum().and_then(|n| Ask::ALL.into_iter().find(|&a| a as i64 == n)).ok_or_else(|| failed(self))?;
        let index = |v: Value<'gc>| v.as_fixnum().and_then(|n| usize::try_from(n).ok());
        match (ask, args) {
            (Ask::Match, &[pattern, input]) => {
                let pattern = index(pattern).and_then(|i| self.patterns.get(i).cloned()).ok_or_else(|| failed(self))?;
                self.match_pattern(&pattern, input, at)
            }
            (Ask::Build, &[template, ref values @ ..]) => {
                let template = index(template).and_then(|i| self.templates.get(i).cloned()).ok_or_else(|| failed(self))?;
                self.instantiate(&template, values, at)
            }
            (Ask::NoMatch | Ask::Violation, &[input]) => Err(self.error_at(ExpandErrorKind::BadSyntax, self.span_of(input, at))),
            (Ask::FreeIdentifierEq, &[a, b]) => {
                let (a, b) = (self.binding_of(a, at)?, self.binding_of(b, at)?);
                Ok(if a == b { Value::TRUE } else { Value::FALSE })
            }
            (Ask::Temporaries, &[list]) => self.temporaries(list, at),
            _ => Err(failed(self)),
        }
    }

    /// Where the syntax `value` came from, or `at` if it isn't syntax or has no span.
    pub(crate) fn span_of(&self, value: Value<'gc>, at: Stx) -> SyntaxSpan<'gc> {
        Syntax::of(value).map(|s| s.span(self.mc)).filter(|span| span.source().is_some()).unwrap_or_else(|| self.tree.span(at))
    }

    /// What the identifier `id`, as syntax, refers to, its name with it if it's free, as two
    /// free identifiers are the same if they're named the same.
    pub(crate) fn binding_of(&mut self, id: Value<'gc>, at: Stx) -> Result<(Binding<'gc>, Option<Symbol<'gc>>), ExpandError> {
        let mc = self.mc;
        let id = Syntax::of(id).filter(|s| s.kind(mc) == Some(SyntaxKind::Identifier)).ok_or_else(|| self.error(ExpandErrorKind::Transformer, at))?;
        let symbol = Symbol::of(id.datum(mc)).ok_or_else(|| self.error(ExpandErrorKind::Transformer, at))?;
        let set = self.set_of(id.context(mc), id.span(mc))?;
        let binding = self.resolve_name(symbol, set).map_err(|_| self.error_at(ExpandErrorKind::Ambiguous, id.span(mc)))?;
        Ok((binding, matches!(binding, Binding::Free { .. } | Binding::Global(_) | Binding::Import(_)).then_some(symbol)))
    }

    /// A fresh identifier for each element of the list `list`, named as it is if it's an
    /// identifier: bound or referred to, it's apart from every other.
    fn temporaries(&mut self, list: Value<'gc>, at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mc = self.mc;
        let failed = |this: &Self| this.error(ExpandErrorKind::Transformer, at);
        let (mut names, mut rest) = (Vec::new(), list);
        loop {
            if let Some(pair) = Pair::of(rest) {
                let item = Syntax::of(pair.head(mc)).filter(|s| s.kind(mc) == Some(SyntaxKind::Identifier));
                names.push(item.and_then(|s| Symbol::of(s.datum(mc))));
                rest = pair.tail(mc);
            } else if let Some(list) = Syntax::of(rest).filter(|s| s.kind(mc) == Some(SyntaxKind::List)) {
                rest = list.datum(mc);
            } else if rest == Value::NIL {
                break;
            } else {
                return Err(failed(self));
            }
        }
        let t = self.symbol("t")?;
        let span = self.tree.span(at);
        let mut temps = Vec::with_capacity(names.len());
        for name in names {
            let scope = self.tree.scopes.fresh()?;
            let set = self.tree.scopes.set(vec![scope])?;
            let meta = self.meta(set, SyntaxKind::Identifier)?;
            temps.push(Syntax::new(mc, name.unwrap_or(t).value(mc), span, Some(meta))?.value(mc));
        }
        Ok(Pairs::new(mc).list(&temps)?)
    }
}
