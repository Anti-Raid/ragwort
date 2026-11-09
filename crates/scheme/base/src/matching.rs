//! `match`, as Racket's: `(match e clause ...)` tries each clause's pattern on `e`'s value in
//! turn and runs the body of the first that matches, with the pattern's variables bound. A
//! clause is `[pattern body ...+]`, `[pattern #:when test body ...+]`, which also needs `test`
//! true, or `[pattern (=> id) body ...+]`, which binds `id` to a procedure of no arguments that
//! goes on to the next clause. When none matches, it raises an error with the value.
//!
//! The patterns:
//! - `_` matches anything; an identifier matches anything and binds it, and one that's already
//!   bound in the pattern matches what's `equal?` to what it's bound to.
//! - A number, string, character, boolean, keyword, `()`, `'datum` or vector literal matches
//!   what's `equal?` to it.
//! - `(list p ...)` a list of as many elements, `(list-rest p ... rest)` and `(cons p rest)` one
//!   with a tail matching `rest`. A list's last pattern can be followed by `...`, which matches
//!   the rest of the list, each element matching it, and binds each of its variables to a list.
//! - `(vector p ...)` a vector of as many elements.
//! - `(? pred p ...)` what `pred` is true of and each `p` matches; `(and p ...)` what each `p`
//!   matches; `(or p ...)` what any does, each binding the same variables; `(not p ...)` what
//!   none does, binding nothing.
//! - `(app f p)` what `p` matches the result of `f` on; `(== v)` what's `equal?` to `v`, and
//!   `(== v same?)` what `(same? v x)` is true for.
//!
//! It's a step to simpler syntax, as the other macros in Rust are: each pattern is a list of
//! [`Step`]s, which [`Expander::emit`] makes `if`s and `let`s of, and a clause that fails calls a
//! procedure of no arguments that tries the next clause, which the compiler makes a jump. As in
//! Racket, the pattern's variables are bound only in the clause's body, and clauses next to each
//! other that start by looking at the same parts of the value the same way share those steps, so
//! a part can be looked at fewer times than the patterns say, if a predicate changes it.

use std::collections::HashMap;

use ragwort_types::gc::Value;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Symbol;

use crate::expand::{Aux, Expander};
use crate::scope::Set;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A temporary, which is the same as another with its number.
#[derive(Clone, Copy)]
struct Temp {
    n: u32,
    stx: Stx,
}

/// What a test with no effects checks a temporary is.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Pair,
    Null,
    List,
    Vector,
    Length(usize),
}

/// A part of a pair or vector.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Part {
    Car,
    Cdr,
    Item(usize),
}

/// What matching a pattern does, in order.
enum Step {
    /// Goes on if the temporary has the shape.
    Is(Shape, Temp),
    /// Binds the first temporary to the part of the second, which it's always the one for.
    Get(Temp, Part, Temp),
    /// Goes on if the expression is true.
    Test(Stx),
    /// Binds a temporary to the expression for what's after.
    Bind(Temp, Stx),
    /// Binds a pattern variable to the expression for what's after.
    Var(Stx, Stx),
    /// Goes on if any of `alts` matches, with `results` bound to that alternative's `values`.
    Or { alts: Vec<Vec<Step>>, values: Vec<Vec<Stx>>, results: Vec<Stx> },
    /// Goes on if the steps don't match.
    Not(Vec<Step>),
    /// Goes on if `list` is a list each element of which, in `item`, matches `steps`, with each
    /// of `results` bound to the list of what its `values` was for each.
    Each { list: Temp, item: Temp, steps: Vec<Step>, values: Vec<Stx>, results: Vec<Stx> },
}

impl Step {
    /// Whether this step is `other`, and has no effects, so clauses can share it.
    fn shares(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Is(shape, x), Self::Is(other, y)) => shape == other && x.n == y.n,
            (Self::Get(x, ..), Self::Get(y, ..)) => x.n == y.n,
            _ => false,
        }
    }
}

/// A clause's body: `body` if `guard` is true, with `escape` bound to the procedure that goes on
/// to the next clause.
struct Body {
    clause: Stx,
    guard: Option<Stx>,
    escape: Option<Stx>,
    body: Vec<Stx>,
}

/// What tells a pattern variable from others: its name and its scopes.
type Key<'gc> = (Symbol<'gc>, Set);

/// A `match` being expanded: where it is, how many temporaries it has made, the one for each
/// part of each, and the pattern variables of the pattern so far, each with what tells it from
/// others of its name and what it's bound to.
struct Matcher<'gc> {
    at: Stx,
    temps: u32,
    parts: HashMap<(u32, Part), Temp>,
    seen: Vec<Seen<'gc>>,
}

/// A pattern variable: its identifier, name and scopes, and what it's bound to.
#[derive(Clone, Copy)]
struct Seen<'gc> {
    id: Stx,
    symbol: Symbol<'gc>,
    set: Set,
    value: Stx,
}

impl<'gc> Seen<'gc> {
    fn key(&self) -> Key<'gc> {
        (self.symbol, self.set)
    }
}

impl<'gc> Expander<'_, 'gc> {
    /// `(let ((x e)) (let ((none (lambda () (error ...)))) clauses))`, the clauses as [`tries`]
    /// makes them.
    ///
    /// [`tries`]: Self::tries
    pub(crate) fn match_form(&mut self, stx: Stx, e: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let mut m = Matcher { at: stx, temps: 0, parts: HashMap::new(), seen: Vec::new() };
        let x = self.temp(&mut m)?;
        let none = self.temp(&mut m)?.stx;
        let mut parsed = Vec::with_capacity(clauses.len());
        for &clause in clauses {
            m.seen.clear();
            parsed.push(self.clause(&mut m, x, clause)?);
        }
        let parsed: Vec<_> = parsed.iter().map(|(steps, body)| (steps.as_slice(), body)).collect();
        let code = self.tries(&mut m, &parsed, none)?;
        let message = string::from_str(&Strings::new(self.mc), "match: no matching clause for")?.value();
        let message = self.value(message, stx)?;
        let error = self.build(stx, "error", &[&[message, x.stx]])?;
        let code = self.let_thunk(stx, none, error, code)?;
        self.with_temp(stx, x.stx, e, code)
    }

    /// `(let ((name (lambda () body))) code)`.
    fn let_thunk(&mut self, at: Stx, name: Stx, body: Stx, code: Stx) -> Result<Stx, ExpandError> {
        let none = self.list(&[], at)?;
        let lambda = self.build(at, "lambda", &[&[none, body]])?;
        self.with_temp(at, name, lambda, code)
    }

    fn temp(&mut self, m: &mut Matcher<'gc>) -> Result<Temp, ExpandError> {
        m.temps += 1;
        Ok(Temp { n: m.temps, stx: self.introduce(&format!("x{}", m.temps), m.at)? })
    }

    /// The temporary for `part` of `x`: the same one each time.
    fn part(&mut self, m: &mut Matcher<'gc>, x: Temp, part: Part) -> Result<Temp, ExpandError> {
        if let Some(&temp) = m.parts.get(&(x.n, part)) {
            return Ok(temp);
        }
        let temp = self.temp(m)?;
        m.parts.insert((x.n, part), temp);
        Ok(temp)
    }

    /// The code of `clauses`, each the steps it has left and its body: the body of the first whose
    /// steps match, or else `(fail)`. Each run of clauses that start with the same step that has
    /// no effects share it, and the run fails by calling a procedure that tries what's after it.
    fn tries(&mut self, m: &mut Matcher<'gc>, clauses: &[(&[Step], &Body)], fail: Stx) -> Result<Stx, ExpandError> {
        let mut runs = Vec::new();
        let mut rest = clauses;
        while let Some(((steps, _), others)) = rest.split_first() {
            let n = match steps.first() {
                Some(first) => 1 + others.iter().take_while(|(other, _)| other.first().is_some_and(|o| first.shares(o))).count(),
                None => 1,
            };
            let (run, after) = rest.split_at(n);
            runs.push(run);
            rest = after;
        }
        let mut code = None;
        for run in runs.into_iter().rev() {
            let next = if code.is_some() { self.temp(m)?.stx } else { fail };
            let this = self.match_run(m, run, next)?;
            code = Some(match code {
                Some(later) => self.let_thunk(m.at, next, later, this)?,
                None => this,
            });
        }
        match code {
            Some(code) => Ok(code),
            None => self.list(&[fail], m.at),
        }
    }

    /// The code of `run`, clauses that all start with the same step if there's more than one.
    fn match_run(&mut self, m: &mut Matcher<'gc>, run: &[(&[Step], &Body)], fail: Stx) -> Result<Stx, ExpandError> {
        let failed = self.list(&[fail], m.at)?;
        match run {
            &[(steps, body)] => {
                let done = self.match_body(body, fail)?;
                self.emit(m, steps, done, failed)
            }
            _ => {
                let rest: Vec<_> = run.iter().map(|&(steps, body)| (&steps[1..], body)).collect();
                let done = self.tries(m, &rest, fail)?;
                self.emit(m, &run[0].0[..1], done, failed)
            }
        }
    }

    /// A clause's steps for matching `x` and its body.
    fn clause(&mut self, m: &mut Matcher<'gc>, x: Temp, clause: Stx) -> Result<(Vec<Step>, Body), ExpandError> {
        let parts = self.proper(clause)?;
        let Some((&pattern, rest)) = parts.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, clause)) };
        let steps = self.match_pattern(m, x, pattern)?;
        let when_ = self.symbol("when")?;
        let when = rest.first().is_some_and(|&first| self.tree.keyword(first).is_some_and(|k| k.symbol(self.mc) == when_));
        let escape = match rest.first() {
            Some(&first) => self.escape(first)?,
            None => None,
        };
        let (guard, escape, body) = match (when, escape, rest) {
            (true, _, &[_, test, ref body @ ..]) if !body.is_empty() => (Some(test), None, body),
            (false, Some(id), &[_, ref body @ ..]) if !body.is_empty() => (None, Some(id), body),
            (false, None, body) if !body.is_empty() => (None, None, body),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
        };
        Ok((steps, Body { clause, guard, escape, body: body.to_vec() }))
    }

    /// The code of `body`, which calls `fail` if its guard is false.
    fn match_body(&mut self, body: &Body, fail: Stx) -> Result<Stx, ExpandError> {
        let Body { clause, guard, escape, ref body } = *body;
        let none = self.list(&[], clause)?;
        let code = self.build(clause, "let", &[&[none], body])?;
        match (guard, escape) {
            (Some(test), _) => {
                let failed = self.list(&[fail], clause)?;
                self.build(clause, "if", &[&[test, code, failed]])
            }
            (None, Some(id)) => self.with_temp(clause, id, fail, code),
            (None, None) => Ok(code),
        }
    }

    /// The `id` of `(=> id)`, if `stx` is one.
    fn escape(&mut self, stx: Stx) -> Result<Option<Stx>, ExpandError> {
        let View::List(items, None) = self.tree.view(stx)? else { return Ok(None) };
        Ok(match *items {
            [arrow, id] if self.is_aux(arrow, Aux::Arrow)? && self.is_id(id) => Some(id),
            _ => None,
        })
    }

    /// The steps of matching `p` against `x`, binding its variables last.
    fn match_pattern(&mut self, m: &mut Matcher<'gc>, x: Temp, p: Stx) -> Result<Vec<Step>, ExpandError> {
        let mut steps = Vec::new();
        self.pattern_into(m, x, p, &mut steps)?;
        let (mut steps, vars): (Vec<_>, Vec<_>) = steps.into_iter().partition(|step| !matches!(step, Step::Var(..)));
        steps.extend(vars);
        Ok(steps)
    }

    /// The steps of matching `p` against `x` within another pattern, which binds none of its
    /// variables: what they're bound to is in `m.seen`.
    fn inner_pattern(&mut self, m: &mut Matcher<'gc>, x: Temp, p: Stx) -> Result<Vec<Step>, ExpandError> {
        let mut steps = Vec::new();
        self.pattern_into(m, x, p, &mut steps)?;
        steps.retain(|step| !matches!(step, Step::Var(..)));
        Ok(steps)
    }

    /// Binds the variables `m.seen` has from `first` on to `results`, temporaries for what they're
    /// bound to once an `or` or a repeat has matched.
    fn bind_results(&mut self, m: &mut Matcher<'gc>, first: usize, results: &[Stx], out: &mut Vec<Step>) {
        for (seen, &result) in m.seen[first..].iter_mut().zip(results) {
            seen.value = result;
            out.push(Step::Var(seen.id, result));
        }
    }

    /// Adds what matching `p` against `x` does to `out`.
    fn pattern_into(&mut self, m: &mut Matcher<'gc>, x: Temp, p: Stx, out: &mut Vec<Step>) -> Result<(), ExpandError> {
        let bad = |this: &Self, at| Err(this.error(ExpandErrorKind::BadSyntax, at));
        let (items, tail) = match self.tree.view(p)? {
            View::Id if self.is_aux(p, Aux::Underscore)? => return Ok(()),
            View::Id if self.is_aux(p, Aux::Ellipsis)? => return bad(self, p),
            View::Id => return self.variable(m, x, p, out),
            View::Datum(value) => {
                let same = if value.immediate().is_some() { "eqv?" } else { "equal?" };
                let quoted = self.quoted(p, p)?;
                out.push(Step::Test(self.build(p, same, &[&[x.stx, quoted]])?));
                return Ok(());
            }
            View::Vector(_) => {
                let quoted = self.quoted(p, p)?;
                out.push(Step::Test(self.build(p, "equal?", &[&[x.stx, quoted]])?));
                return Ok(());
            }
            View::List(items, None) if items.is_empty() => {
                out.push(Step::Is(Shape::Null, x));
                return Ok(());
            }
            View::List(items, tail) => (items, tail),
        };
        let name = match self.tree.symbol(items[0]) {
            Some(symbol) if tail.is_none() => string::chars(&Strings::new(self.mc), symbol.name(self.mc)).collect::<String>(),
            _ => return bad(self, p),
        };
        let args = &items[1..];
        match (name.as_str(), args) {
            ("quote", [_]) => out.push(Step::Test(self.build(p, "equal?", &[&[x.stx, p]])?)),
            ("quasiquote", _) => return Err(self.error(ExpandErrorKind::Unsupported, p)),
            ("list", _) => self.list_pattern(m, x, args, None, out)?,
            ("list-rest", &[ref init @ .., rest]) => self.list_pattern(m, x, init, Some(rest), out)?,
            ("cons", &[head, rest]) => self.list_pattern(m, x, &[head], Some(rest), out)?,
            ("vector", _) => {
                out.push(Step::Is(Shape::Vector, x));
                out.push(Step::Is(Shape::Length(args.len()), x));
                for (i, &arg) in args.iter().enumerate() {
                    if self.is_aux(arg, Aux::Ellipsis)? {
                        return Err(self.error(ExpandErrorKind::Unsupported, arg));
                    }
                    let item = self.part(m, x, Part::Item(i))?;
                    out.push(Step::Get(item, Part::Item(i), x));
                    self.pattern_into(m, item, arg, out)?;
                }
            }
            ("?", &[pred, ref pats @ ..]) => {
                out.push(Step::Test(self.list(&[pred, x.stx], p)?));
                for &pat in pats {
                    self.pattern_into(m, x, pat, out)?;
                }
            }
            ("and", pats) => {
                for &pat in pats {
                    self.pattern_into(m, x, pat, out)?;
                }
            }
            ("or", []) => out.push(Step::Test(self.value(Value::FALSE, p)?)),
            ("or", alts) => {
                let before = m.seen.clone();
                let mut steps = Vec::with_capacity(alts.len());
                let mut bound: Vec<Vec<Seen<'gc>>> = Vec::with_capacity(alts.len());
                for &alt in alts {
                    m.seen.clone_from(&before);
                    steps.push(self.inner_pattern(m, x, alt)?);
                    let vars = m.seen[before.len()..].to_vec();
                    // Each alternative binds the same variables, in any order.
                    if let Some(first) = bound.first()
                        && (first.len() != vars.len() || !vars.iter().all(|v| first.iter().any(|f| f.key() == v.key())))
                    {
                        return bad(self, alt);
                    }
                    bound.push(vars);
                }
                let results = (before.len()..m.seen.len()).map(|_| Ok(self.temp(m)?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                let values = bound
                    .iter()
                    .map(|vars| m.seen[before.len()..].iter().map(|v| vars.iter().find(|w| w.key() == v.key()).expect("checked").value).collect())
                    .collect();
                out.push(Step::Or { alts: steps, values, results: results.clone() });
                self.bind_results(m, before.len(), &results, out);
            }
            ("not", pats) => {
                for &pat in pats {
                    let before = m.seen.clone();
                    let steps = self.inner_pattern(m, x, pat)?;
                    m.seen = before;
                    out.push(Step::Not(steps));
                }
            }
            ("app", &[f, pat]) => {
                let result = self.temp(m)?;
                out.push(Step::Bind(result, self.list(&[f, x.stx], p)?));
                self.pattern_into(m, result, pat, out)?;
            }
            ("==", &[v]) => out.push(Step::Test(self.build(p, "equal?", &[&[v, x.stx]])?)),
            ("==", &[v, same]) => out.push(Step::Test(self.list(&[same, v, x.stx], p)?)),
            _ => return bad(self, p),
        }
        Ok(())
    }

    /// Matches anything, bound to `id`, or if `id` is already bound in the pattern, what's
    /// `equal?` to it.
    fn variable(&mut self, m: &mut Matcher<'gc>, x: Temp, id: Stx, out: &mut Vec<Step>) -> Result<(), ExpandError> {
        let seen = Seen { id, symbol: self.tree.symbol(id).expect("an identifier"), set: self.tree.scopes_of(id)?, value: x.stx };
        match m.seen.iter().find(|other| other.key() == seen.key()) {
            Some(first) => out.push(Step::Test(self.build(id, "equal?", &[&[first.value, x.stx]])?)),
            None => {
                m.seen.push(seen);
                out.push(Step::Var(id, x.stx));
            }
        }
        Ok(())
    }

    /// Matches `x` against a list of `items`, the last of which can be followed by `...`, then
    /// `rest` against its tail, or else the end of the list.
    fn list_pattern(&mut self, m: &mut Matcher<'gc>, x: Temp, items: &[Stx], rest: Option<Stx>, out: &mut Vec<Step>) -> Result<(), ExpandError> {
        let mut at = x;
        for (i, &item) in items.iter().enumerate() {
            if self.is_aux(item, Aux::Ellipsis)? {
                return Err(self.error(ExpandErrorKind::BadSyntax, item));
            }
            if let Some(&next) = items.get(i + 1)
                && self.is_aux(next, Aux::Ellipsis)?
            {
                // Only the last pattern can repeat, as only the rest of the list can be split
                // without first counting it.
                if i + 2 != items.len() || rest.is_some() {
                    return Err(self.error(ExpandErrorKind::Unsupported, next));
                }
                // A list of anything is the list itself.
                if self.is_id(item) && !self.is_aux(item, Aux::Ellipsis)? {
                    out.push(Step::Is(Shape::List, at));
                    if !self.is_aux(item, Aux::Underscore)? {
                        let key = (self.tree.symbol(item).expect("an identifier"), self.tree.scopes_of(item)?);
                        if m.seen.iter().any(|seen| seen.key() == key) {
                            return Err(self.error(ExpandErrorKind::Duplicate, item));
                        }
                    }
                    return self.pattern_into(m, at, item, out);
                }
                let element = self.temp(m)?;
                let before = std::mem::take(&mut m.seen);
                let steps = self.inner_pattern(m, element, item)?;
                let inner = std::mem::replace(&mut m.seen, before);
                if let Some(seen) = inner.iter().find(|seen| m.seen.iter().any(|other| other.key() == seen.key())) {
                    return Err(self.error(ExpandErrorKind::Duplicate, seen.id));
                }
                let values = inner.iter().map(|v| v.value).collect();
                let results = inner.iter().map(|_| Ok(self.temp(m)?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                let first = m.seen.len();
                m.seen.extend(inner);
                out.push(Step::Each { list: at, item: element, steps, values, results: results.clone() });
                self.bind_results(m, first, &results, out);
                return Ok(());
            }
            out.push(Step::Is(Shape::Pair, at));
            let head = self.part(m, at, Part::Car)?;
            out.push(Step::Get(head, Part::Car, at));
            let tail = self.part(m, at, Part::Cdr)?;
            out.push(Step::Get(tail, Part::Cdr, at));
            self.pattern_into(m, head, item, out)?;
            at = tail;
        }
        match rest {
            Some(rest) => self.pattern_into(m, at, rest, out),
            None => {
                out.push(Step::Is(Shape::Null, at));
                Ok(())
            }
        }
    }

    /// The code of `steps`: `done` if they match, `fail` if they don't.
    fn emit(&mut self, m: &mut Matcher<'gc>, steps: &[Step], done: Stx, fail: Stx) -> Result<Stx, ExpandError> {
        let Some((step, rest)) = steps.split_first() else { return Ok(done) };
        let at = m.at;
        match step {
            &Step::Is(shape, x) => {
                let test = match shape {
                    Shape::Pair => self.build(at, "pair?", &[&[x.stx]])?,
                    Shape::Null => self.build(at, "null?", &[&[x.stx]])?,
                    Shape::List => self.build(at, "list?", &[&[x.stx]])?,
                    Shape::Vector => self.build(at, "vector?", &[&[x.stx]])?,
                    Shape::Length(n) => {
                        let n = self.value(Value::fixnum(n as i64).ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, at))?, at)?;
                        let len = self.build(at, "vector-length", &[&[x.stx]])?;
                        self.build(at, "eqv?", &[&[len, n]])?
                    }
                };
                let rest = self.emit(m, rest, done, fail)?;
                self.build(at, "if", &[&[test, rest, fail]])
            }
            &Step::Get(temp, part, x) => {
                let value = match part {
                    Part::Car => self.build(at, "car", &[&[x.stx]])?,
                    Part::Cdr => self.build(at, "cdr", &[&[x.stx]])?,
                    Part::Item(i) => {
                        let k = self.value(Value::fixnum(i as i64).ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, at))?, at)?;
                        self.build(at, "vector-ref", &[&[x.stx, k]])?
                    }
                };
                let rest = self.emit(m, rest, done, fail)?;
                self.with_temp(at, temp.stx, value, rest)
            }
            &Step::Test(test) => {
                let rest = self.emit(m, rest, done, fail)?;
                self.build(at, "if", &[&[test, rest, fail]])
            }
            &Step::Bind(temp, value) => {
                let rest = self.emit(m, rest, done, fail)?;
                self.with_temp(at, temp.stx, value, rest)
            }
            &Step::Var(var, value) => {
                let rest = self.emit(m, rest, done, fail)?;
                self.with_temp(at, var, value, rest)
            }
            Step::Not(steps) => {
                let (yes, no) = (self.value(Value::TRUE, at)?, self.value(Value::FALSE, at)?);
                let test = self.emit(m, steps, yes, no)?;
                let rest = self.emit(m, rest, done, fail)?;
                self.build(at, "if", &[&[test, fail, rest]])
            }
            // `(let ((k (lambda (result ...) rest))) alt)`, each alt calling `k` with its values,
            // and each but the last trying the next if it fails.
            Step::Or { alts, values, results } => {
                let k = self.temp(m)?.stx;
                let formals = self.list(results, at)?;
                let rest = self.emit(m, rest, done, fail)?;
                let lambda = self.build(at, "lambda", &[&[formals, rest]])?;
                let mut next: Option<Stx> = None;
                for (alt, values) in alts.iter().zip(values).rev() {
                    let matched = self.list(&[&[k], values.as_slice()].concat(), at)?;
                    next = Some(match next {
                        None => self.emit(m, alt, matched, fail)?,
                        Some(next) => {
                            let other = self.temp(m)?.stx;
                            let tried = self.list(&[other], at)?;
                            let code = self.emit(m, alt, matched, tried)?;
                            let none = self.list(&[], at)?;
                            let thunk = self.build(at, "lambda", &[&[none, next]])?;
                            self.with_temp(at, other, thunk, code)?
                        }
                    });
                }
                let alts = next.expect("an `or` of no patterns is a test");
                self.with_temp(at, k, lambda, alts)
            }
            // `(let loop ((xs list) (acc '()) ...) (if (null? xs) (let ((result (reverse acc)) ...)
            // rest) (if (pair? xs) (let ((item (car xs))) steps, then (loop (cdr xs) (cons value
            // acc) ...)) fail)))`.
            Step::Each { list, item, steps, values, results } => {
                let (again, xs) = (self.temp(m)?.stx, self.temp(m)?.stx);
                let accs = values.iter().map(|_| Ok(self.temp(m)?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                let mut finished = self.emit(m, rest, done, fail)?;
                for (&result, &acc) in results.iter().zip(&accs).rev() {
                    let reversed = self.build(at, "reverse", &[&[acc]])?;
                    finished = self.with_temp(at, result, reversed, finished)?;
                }
                let mut next = vec![again, self.build(at, "cdr", &[&[xs]])?];
                for (&value, &acc) in values.iter().zip(&accs) {
                    next.push(self.build(at, "cons", &[&[value, acc]])?);
                }
                let next = self.list(&next, at)?;
                let each = self.emit(m, steps, next, fail)?;
                let first = self.build(at, "car", &[&[xs]])?;
                let each = self.with_temp(at, item.stx, first, each)?;
                let is_pair = self.build(at, "pair?", &[&[xs]])?;
                let more = self.build(at, "if", &[&[is_pair, each, fail]])?;
                let is_null = self.build(at, "null?", &[&[xs]])?;
                let body = self.build(at, "if", &[&[is_null, finished, more]])?;
                let mut binds = vec![self.list(&[xs, list.stx], at)?];
                for &acc in &accs {
                    let empty = self.value(Value::NIL, at)?;
                    let empty = self.quoted(empty, at)?;
                    binds.push(self.list(&[acc, empty], at)?);
                }
                let binds = self.list(&binds, at)?;
                self.build(at, "let", &[&[again, binds, body]])
            }
        }
    }
}
