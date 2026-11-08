//! `syntax-case` and `syntax`, as R6RS has them. A clause's pattern is kept here, and the code
//! asks the expander to match it, which gives a vector of what its variables matched, a list of
//! those for each ellipsis a variable's under. A template with pattern variables in it is kept
//! too, and the code asks for the syntax it makes of theirs; one without any is a constant.
//!
//! What's matched and made is the transformer's syntax: lists of syntax, or the syntax of lists,
//! as a pattern's rest is a list of the rest of the syntax it matched.

use std::ops::Range;
use std::rc::Rc;

use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxMeta, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};
use ragwort_vm::{Fuel, Intrinsic};

use crate::expand::{Aux, Binding, Expander};
use crate::scope::Op;
use crate::transformer::Ask;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A clause's pattern, and how many variables it has.
pub(crate) struct Compiled<'gc> {
    pattern: Pattern<'gc>,
    vars: usize,
}

enum Pattern<'gc> {
    /// `_`.
    Any,
    /// The variable matched into this slot.
    Var(usize),
    /// An identifier that means what this literal does.
    Literal(Stx),
    /// A datum `equal?` to this one.
    Datum(Value<'gc>),
    /// A list, or a vector, of items that match `before`, then any number that match `repeat`,
    /// then items that match `after`, and for a list, what's left matching `tail`, or nothing.
    Seq { before: Vec<Pattern<'gc>>, repeat: Option<Repeat<'gc>>, after: Vec<Pattern<'gc>>, tail: Option<Box<Pattern<'gc>>>, vector: bool },
}

type Items<'gc> = (Vec<Pattern<'gc>>, Option<Repeat<'gc>>, Vec<Pattern<'gc>>);

/// A pattern under an ellipsis, and the slots of its variables.
struct Repeat<'gc> {
    each: Box<Pattern<'gc>>,
    slots: Range<usize>,
}

/// A template with pattern variables in it, and how many ellipses each of those is under in its
/// pattern, in the order the code passes what they matched.
pub(crate) struct Built<'gc> {
    template: Template<'gc>,
    depths: Vec<u32>,
}

enum Template<'gc> {
    /// Syntax made already.
    Const(Value<'gc>),
    /// What the variable in this slot matched.
    Var(usize),
    /// A list or vector of items, a tail for a list, made with the template's scopes and span.
    Seq { items: Vec<Item<'gc>>, tail: Option<Box<Template<'gc>>>, vector: bool, meta: SyntaxMeta<'gc>, span: SyntaxSpan<'gc> },
}

/// An item of a list or vector template, made once for each match of the pattern variables in
/// it under `ellipses` ellipses, which are in `slots`.
struct Item<'gc> {
    template: Template<'gc>,
    ellipses: u32,
    slots: Vec<usize>,
}

impl Template<'_> {
    fn slots(&self, out: &mut Vec<usize>) {
        match self {
            Template::Const(_) => {}
            Template::Var(slot) => {
                if !out.contains(slot) {
                    out.push(*slot);
                }
            }
            Template::Seq { items, tail, .. } => {
                items.iter().for_each(|item| item.template.slots(out));
                if let Some(tail) = tail {
                    tail.slots(out);
                }
            }
        }
    }
}

impl<'gc> Expander<'_, 'gc> {
    /// `(syntax-case input (literal ...) clause ...)`: each clause `(pattern output)` or `(pattern
    /// fender output)` tried in turn, its pattern variables bound for the fender and output.
    pub(crate) fn syntax_case(&mut self, input: Stx, literals: Stx, clauses: &[Stx]) -> Result<Core<'gc>, ExpandError> {
        let literals = self.proper(literals)?;
        if let Some(&bad) = literals.iter().find(|&&id| !self.is_id(id)) {
            return Err(self.error(ExpandErrorKind::BadSyntax, bad));
        }
        let var = self.fresh();
        let value = self.expr(input)?;
        let clauses = self.clauses(var, &literals, clauses)?;
        Ok(Core::Let(vec![(var, value)], Box::new(clauses)))
    }

    fn clauses(&mut self, input: Var, literals: &[Stx], clauses: &[Stx]) -> Result<Core<'gc>, ExpandError> {
        let Some((&clause, rest)) = clauses.split_first() else { return Ok(Ask::NoMatch.call([local(input)])) };
        let (pattern, fender, output) = match *self.proper(clause)?.as_slice() {
            [pattern, output] => (pattern, None, output),
            [pattern, fender, output] => (pattern, Some(fender), output),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
        };
        let mut vars = Vec::new();
        let compiled = self.pattern(pattern, literals, 0, &mut vars)?;
        let index = self.patterns.len() as i64;
        self.patterns.push(Rc::new(Compiled { pattern: compiled, vars: vars.len() }));
        let scope = self.tree.scopes.fresh()?;
        let ids = vars.iter().map(|&(id, _)| self.tree.with(id, scope, Op::Add)).collect::<Result<Vec<_>, _>>()?;
        self.distinct(&ids)?;
        let matched = self.fresh();
        let mut binds = Vec::with_capacity(ids.len());
        for (k, (&id, &(_, depth))) in ids.iter().zip(&vars).enumerate() {
            let var = self.fresh();
            self.bind(id, Binding::Pattern { var, depth })?;
            let at = Core::Quote(Value::fixnum(k as i64).expect("a fixnum"));
            binds.push((var, Core::Intrinsic(Prim::Intrinsic(Intrinsic::VectorRef), vec![local(matched), at])));
        }
        let output = self.tree.with(output, scope, Op::Add)?;
        let fender = fender.map(|fender| self.tree.with(fender, scope, Op::Add)).transpose()?;
        let next = self.clauses(input, literals, rest)?;
        let output = self.expr(output)?;
        let (body, next) = match fender {
            None => (output, next),
            Some(fender) => {
                // The rest are tried if the fender fails or the pattern doesn't match.
                let k = self.fresh();
                let thunk = Core::Lambda(Lambda { id: self.lambda_id(), params: Vec::new(), rest: None, body: Box::new(next) });
                let again = || Core::App(Box::new(local(k)), Vec::new());
                let body = Core::If(Box::new(self.expr(fender)?), Box::new(output), Box::new(again()));
                let body = Core::Let(binds, Box::new(body));
                let tried = Core::If(Box::new(local(matched)), Box::new(body), Box::new(again()));
                let asked = Ask::Match.call([Core::Quote(Value::fixnum(index).expect("a fixnum")), local(input)]);
                return Ok(Core::Let(vec![(k, thunk)], Box::new(Core::Let(vec![(matched, asked)], Box::new(tried)))));
            }
        };
        let body = Core::Let(binds, Box::new(body));
        let asked = Ask::Match.call([Core::Quote(Value::fixnum(index).expect("a fixnum")), local(input)]);
        Ok(Core::Let(vec![(matched, asked)], Box::new(Core::If(Box::new(local(matched)), Box::new(body), Box::new(next)))))
    }

    /// The pattern `p`, under `depth` ellipses, adding its variables to `vars`.
    fn pattern(&mut self, p: Stx, literals: &[Stx], depth: u32, vars: &mut Vec<(Stx, u32)>) -> Result<Pattern<'gc>, ExpandError> {
        Ok(match self.tree.view(p)? {
            View::Id if self.is_aux(p, Aux::Underscore)? => Pattern::Any,
            View::Id if self.is_aux(p, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, p)),
            View::Id if self.is_literal(p, literals)? => Pattern::Literal(p),
            View::Id => {
                vars.push((p, depth));
                Pattern::Var(vars.len() - 1)
            }
            View::Datum(value) => Pattern::Datum(value),
            View::List(items, tail) => {
                let (before, repeat, after) = self.items(p, &items, literals, depth, vars)?;
                let tail = tail.map(|tail| self.pattern(tail, literals, depth, vars).map(Box::new)).transpose()?;
                Pattern::Seq { before, repeat, after, tail, vector: false }
            }
            View::Vector(items) => {
                let (before, repeat, after) = self.items(p, &items, literals, depth, vars)?;
                Pattern::Seq { before, repeat, after, tail: None, vector: true }
            }
        })
    }

    /// The items of a list or vector pattern: those before an ellipsis, the one it repeats, and
    /// those after, or all of them if there's none.
    fn items(&mut self, p: Stx, items: &[Stx], literals: &[Stx], depth: u32, vars: &mut Vec<(Stx, u32)>) -> Result<Items<'gc>, ExpandError> {
        let mut dots = Vec::new();
        for (i, &item) in items.iter().enumerate() {
            if self.is_aux(item, Aux::Ellipsis)? {
                dots.push(i);
            }
        }
        let each = |this: &mut Self, items: &[Stx], vars: &mut Vec<(Stx, u32)>| items.iter().map(|&item| this.pattern(item, literals, depth, vars)).collect::<Result<Vec<_>, _>>();
        match *dots.as_slice() {
            [] => Ok((each(self, items, vars)?, None, Vec::new())),
            [i] if i > 0 => {
                let before = each(self, &items[..i - 1], vars)?;
                let start = vars.len();
                let repeated = self.pattern(items[i - 1], literals, depth + 1, vars)?;
                let repeat = Repeat { each: Box::new(repeated), slots: start..vars.len() };
                Ok((before, Some(repeat), each(self, &items[i + 1..], vars)?))
            }
            _ => Err(self.error(ExpandErrorKind::BadSyntax, p)),
        }
    }

    /// Whether `id` is one of `literals`: the same name with the same scopes.
    fn is_literal(&mut self, id: Stx, literals: &[Stx]) -> Result<bool, ExpandError> {
        let (symbol, set) = (self.tree.symbol(id), self.tree.scopes_of(id)?);
        for &literal in literals {
            if self.tree.symbol(literal) == symbol && self.tree.scopes_of(literal)? == set {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// What the variables of `compiled` matched in `input`, as a vector, or `#f` if it doesn't
    /// match.
    pub(crate) fn match_pattern(&mut self, compiled: &Compiled<'gc>, input: Value<'gc>, at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mut out = vec![Value::VOID; compiled.vars];
        if !self.matches(&compiled.pattern, input, &mut out, at)? {
            return Ok(Value::FALSE);
        }
        Ok(Vectors::new(self.mc).immutable_from_slice(&out)?.value(self.mc))
    }

    fn matches(&mut self, p: &Pattern<'gc>, v: Value<'gc>, out: &mut [Value<'gc>], at: Stx) -> Result<bool, ExpandError> {
        let mc = self.mc;
        Ok(match p {
            Pattern::Any => true,
            Pattern::Var(slot) => {
                out[*slot] = v;
                true
            }
            Pattern::Literal(literal) => {
                let is_id = Syntax::of(v).is_some_and(|s| s.kind(mc) == Some(SyntaxKind::Identifier));
                if !is_id {
                    return Ok(false);
                }
                let symbol = self.tree.symbol(*literal).expect("literals are identifiers");
                let set = self.tree.scopes_of(*literal)?;
                let literal = self.resolve_name(symbol, set).map_err(|_| self.error(ExpandErrorKind::Ambiguous, *literal))?;
                let literal = (literal, matches!(literal, Binding::Free | Binding::Slot(_) | Binding::Import(_)).then_some(symbol));
                self.binding_of(v, at)? == literal
            }
            Pattern::Datum(datum) => {
                let v = Syntax::of(v).map_or(v, |s| s.datum(mc));
                let mut fuel = Fuel { run: u64::MAX, rest: 0 };
                Intrinsic::Equal.run(mc, &[v, *datum], &mut fuel).is_ok_and(|same| same == Value::TRUE)
            }
            Pattern::Seq { before, repeat, after, tail, vector } => {
                let Some((items, rests)) = (if *vector { self.vector_items(v) } else { self.list_items(v) }) else { return Ok(false) };
                let (k, m, n) = (before.len(), after.len(), items.len());
                let end = rests[n];
                let fits = match (repeat, tail) {
                    (None, None) => n == k && end == Value::NIL,
                    (None, Some(_)) => n >= k,
                    (Some(_), None) => n >= k + m && end == Value::NIL,
                    (Some(_), Some(_)) => n >= k + m,
                };
                if !fits {
                    return Ok(false);
                }
                for (p, &item) in before.iter().zip(&items) {
                    if !self.matches(p, item, out, at)? {
                        return Ok(false);
                    }
                }
                let after_start = if repeat.is_some() { n - m } else { k };
                if let Some(repeat) = repeat {
                    let mut lists = vec![Vec::new(); repeat.slots.len()];
                    for &item in &items[k..n - m] {
                        if !self.matches(&repeat.each, item, out, at)? {
                            return Ok(false);
                        }
                        for (list, slot) in lists.iter_mut().zip(repeat.slots.clone()) {
                            list.push(out[slot]);
                        }
                    }
                    for (list, slot) in lists.into_iter().zip(repeat.slots.clone()) {
                        out[slot] = Pairs::new(mc).list(&list)?;
                    }
                    for (p, &item) in after.iter().zip(&items[after_start..]) {
                        if !self.matches(p, item, out, at)? {
                            return Ok(false);
                        }
                    }
                }
                match tail {
                    Some(tail) => self.matches(tail, rests[if repeat.is_some() { n } else { k }], out, at)?,
                    None => true,
                }
            }
        })
    }

    /// The items of the list `v` is, or is the syntax of, and what's left of it from each, and
    /// after the last; `None` if it's neither.
    fn list_items(&self, v: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
        let mc = self.mc;
        let list = |v: Value<'gc>| match Syntax::of(v) {
            Some(s) if s.kind(mc) == Some(SyntaxKind::List) => Some(s.datum(mc)),
            Some(_) => None,
            None => Some(v),
        };
        let mut at = list(v).filter(|&v| v == Value::NIL || Pair::of(v).is_some())?;
        let (mut items, mut rests) = (Vec::new(), Vec::new());
        loop {
            if let Some(pair) = Pair::of(at) {
                items.push(pair.head(mc));
                rests.push(at);
                at = pair.tail(mc);
            } else if let Some(datum) = Syntax::of(at).filter(|s| s.kind(mc) == Some(SyntaxKind::List)).map(|s| s.datum(mc)) {
                at = datum;
            } else {
                break;
            }
        }
        rests.push(at);
        Some((items, rests))
    }

    fn vector_items(&self, v: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
        let mc = self.mc;
        let v = match Syntax::of(v) {
            Some(s) if s.kind(mc) == Some(SyntaxKind::Vector) => s.datum(mc),
            Some(_) => return None,
            None => v,
        };
        let vector = AnyVector::of(v)?;
        let items: Vec<_> = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).collect();
        let rests = vec![Value::NIL; items.len() + 1];
        Some((items, rests))
    }

    /// `(syntax template)`: what `template` makes, of what the pattern variables in it matched.
    pub(crate) fn syntax(&mut self, template: Stx) -> Result<Core<'gc>, ExpandError> {
        let mut used = Vec::new();
        Ok(match self.template(template, &mut used, 0, &mut false)? {
            Template::Const(value) => Core::Quote(value),
            Template::Var(_) => local(used[0].0),
            template => {
                let index = self.templates.len() as i64;
                let depths = used.iter().map(|&(_, depth)| depth).collect();
                self.templates.push(Rc::new(Built { template, depths }));
                let args = used.iter().map(|&(var, _)| local(var));
                Ask::Build.call(std::iter::once(Core::Quote(Value::fixnum(index).expect("a fixnum"))).chain(args))
            }
        })
    }

    /// The template `t`, under `nesting` ellipses, with the pattern variables it refers to added
    /// to `used`, unless they're there already. In an `escaped` one, `...` is an identifier;
    /// `escapes` is set if `t` has `(... template)` in it.
    fn template(&mut self, t: Stx, used: &mut Vec<(Var, u32)>, nesting: u32, escapes: &mut bool) -> Result<Template<'gc>, ExpandError> {
        self.template_in(t, used, nesting, false, escapes)
    }

    fn template_in(&mut self, t: Stx, used: &mut Vec<(Var, u32)>, nesting: u32, escaped: bool, escapes: &mut bool) -> Result<Template<'gc>, ExpandError> {
        let (items, tail, vector) = match self.tree.view(t)? {
            View::Id if !escaped && self.is_aux(t, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, t)),
            View::Id => {
                return Ok(match self.resolve(t)? {
                    Binding::Pattern { var, depth } => {
                        if nesting < depth {
                            return Err(self.error(ExpandErrorKind::BadSyntax, t));
                        }
                        let slot = used.iter().position(|&(v, _)| v == var).unwrap_or_else(|| {
                            used.push((var, depth));
                            used.len() - 1
                        });
                        Template::Var(slot)
                    }
                    _ => Template::Const(self.wrap(t)?),
                });
            }
            View::Datum(_) => return Ok(Template::Const(self.wrap(t)?)),
            View::List(items, tail) => {
                // `(... template)` is `template` with its ellipses as they are.
                if let [dots, inner] = items[..]
                    && !escaped
                    && tail.is_none()
                    && self.is_aux(dots, Aux::Ellipsis)?
                {
                    *escapes = true;
                    return self.template_in(inner, used, nesting, true, escapes);
                }
                (items, tail, false)
            }
            View::Vector(items) => (items, None, true),
        };
        let mut built = Vec::with_capacity(items.len());
        let mut inner = false;
        let mut i = 0;
        while i < items.len() {
            let item = items[i];
            let mut ellipses = 0;
            while !escaped && i + 1 < items.len() && self.is_aux(items[i + 1], Aux::Ellipsis)? {
                ellipses += 1;
                i += 1;
            }
            let template = self.template_in(item, used, nesting + ellipses, escaped, &mut inner)?;
            let mut slots = Vec::new();
            template.slots(&mut slots);
            if ellipses > 0 && !slots.iter().any(|&slot| used[slot].1 > nesting) {
                return Err(self.error(ExpandErrorKind::BadSyntax, item));
            }
            built.push(Item { template, ellipses, slots });
            i += 1;
        }
        let tail = tail.map(|tail| self.template_in(tail, used, nesting, escaped, &mut inner).map(Box::new)).transpose()?;
        *escapes |= inner;
        // A list of constants is the syntax it's made from, unless an escape in it is dropped.
        let constant = built.iter().all(|item| matches!(item.template, Template::Const(_))) && tail.as_deref().is_none_or(|t| matches!(t, Template::Const(_)));
        if constant && !inner {
            return Ok(Template::Const(self.wrap(t)?));
        }
        let kind = if vector { SyntaxKind::Vector } else { SyntaxKind::List };
        let set = self.tree.scopes_of(t)?;
        let meta = self.meta(set, kind)?;
        Ok(Template::Seq { items: built, tail, vector, meta, span: self.tree.span(t) })
    }

    /// The syntax `built` makes of `values`, what its pattern variables matched, for `at`.
    pub(crate) fn instantiate(&mut self, built: &Built<'gc>, values: &[Value<'gc>], at: Stx) -> Result<Value<'gc>, ExpandError> {
        if values.len() != built.depths.len() {
            return Err(self.error(ExpandErrorKind::Transformer, at));
        }
        let mut env: Vec<_> = values.iter().copied().zip(built.depths.iter().copied()).collect();
        self.make(&built.template, &mut env, at)
    }

    fn make(&mut self, t: &Template<'gc>, env: &mut Vec<(Value<'gc>, u32)>, at: Stx) -> Result<Value<'gc>, ExpandError> {
        let mc = self.mc;
        Ok(match t {
            Template::Const(value) => *value,
            Template::Var(slot) => env[*slot].0,
            Template::Seq { items, tail, vector, meta, span } => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    self.repeat(item, item.ellipses, env, &mut out, at)?;
                }
                let datum = if *vector {
                    Vectors::new(mc).immutable_from_slice(&out)?.value(mc)
                } else {
                    let tail = tail.as_deref().map_or(Ok(Value::NIL), |tail| self.make(tail, env, at))?;
                    Pairs::new(mc).list_with_tail(out, tail)?
                };
                Syntax::new(mc, datum, *span, Some(*meta))?.value(mc)
            }
        })
    }

    /// Makes `item` under `ellipses` of its ellipses, once for each match of the variables in it
    /// with matches left, adding what it makes to `out`.
    fn repeat(&mut self, item: &Item<'gc>, ellipses: u32, env: &mut Vec<(Value<'gc>, u32)>, out: &mut Vec<Value<'gc>>, at: Stx) -> Result<(), ExpandError> {
        if ellipses == 0 {
            out.push(self.make(&item.template, env, at)?);
            return Ok(());
        }
        let drivers: Vec<usize> = item.slots.iter().copied().filter(|&slot| env[slot].1 > 0).collect();
        let lists = drivers.iter().map(|&slot| self.list_items(env[slot].0).map(|(items, _)| items)).collect::<Option<Vec<_>>>();
        let lists = lists.ok_or_else(|| self.error(ExpandErrorKind::Transformer, at))?;
        let Some(len) = lists.first().map(Vec::len) else { return Err(self.error(ExpandErrorKind::BadSyntax, at)) };
        if lists.iter().any(|list| list.len() != len) {
            return Err(self.error(ExpandErrorKind::BadSyntax, at));
        }
        let saved: Vec<_> = drivers.iter().map(|&slot| env[slot]).collect();
        for i in 0..len {
            for ((&slot, list), &(_, depth)) in drivers.iter().zip(&lists).zip(&saved) {
                env[slot] = (list[i], depth - 1);
            }
            self.repeat(item, ellipses - 1, env, out, at)?;
        }
        for (&slot, &was) in drivers.iter().zip(&saved) {
            env[slot] = was;
        }
        Ok(())
    }
}

fn local<'gc>(var: Var) -> Core<'gc> {
    Core::Ref(Place::Local(var))
}
