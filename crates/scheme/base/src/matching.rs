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
//! [`Step`]s, which [`Matching::emit`] makes `if`s and `let`s of, and a clause that fails calls a
//! procedure of no arguments that tries the next clause, which the compiler makes a jump. As in
//! Racket, the pattern's variables are bound only in the clause's body, and clauses next to each
//! other that start by looking at the same parts of the value the same way share those steps, so
//! a part can be looked at fewer times than the patterns say, if a predicate changes it.

use std::collections::HashMap;

use ragwort_compiler::steps::{self, Step as Next};
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

// A step's steps go on a list to drop, so dropping steps nested as deeply as their pattern takes
// no more of the machine's stack.
impl Drop for Step {
    fn drop(&mut self) {
        let mut todo = Vec::new();
        self.take_inner(&mut todo);
        while let Some(steps) = todo.pop() {
            for mut step in steps {
                step.take_inner(&mut todo);
            }
        }
    }
}

impl Step {
    fn take_inner(&mut self, todo: &mut Vec<Vec<Step>>) {
        match self {
            Step::Or { alts, .. } => todo.append(alts),
            Step::Not(steps) | Step::Each { steps, .. } => todo.push(std::mem::take(steps)),
            _ => {}
        }
    }
}

/// A `match` being expanded, by the expander: the steps of the patterns being made, the
/// innermost last.
struct Matching<'e, 'a, 'gc> {
    ex: &'e mut Expander<'a, 'gc>,
    m: Matcher<'gc>,
    out: Vec<Vec<Step>>,
}

/// What making a pattern's steps does next: see [`steps`]. Each call adds those of a pattern
/// matched against a temporary.
type Pat<'e, 'a, 'gc> = Next<'e, Matching<'e, 'a, 'gc>, (Temp, Stx), (), ExpandError>;

/// What making a `match`'s code does next. Each call makes code.
type Em<'s, 'e, 'a, 'gc> = Next<'s, Matching<'e, 'a, 'gc>, Code<'s>, Stx, ExpandError>;

/// A clause's steps left, and its body.
type Clause<'s> = (&'s [Step], &'s Body);

/// Code a `match` needs made.
enum Code<'s> {
    /// That of [`Matching::emit`].
    Emit(&'s [Step], Stx, Stx),
    /// That of [`Matching::tries`].
    Tries(Vec<Clause<'s>>, Stx),
    /// That of [`Matching::match_run`].
    Run(Vec<Clause<'s>>, Stx),
}

/// An `or` pattern's alternatives being matched: the alternatives, the steps of those so far,
/// and the variables each binds.
struct Or<'gc> {
    x: Temp,
    alts: Vec<Stx>,
    before: Vec<Seen<'gc>>,
    steps: Vec<Vec<Step>>,
    bound: Vec<Vec<Seen<'gc>>>,
}

/// An `or` step's code being made, its alternatives from the last: those `left`, and the code
/// of those after them.
struct Alternatives<'s> {
    alts: &'s [Vec<Step>],
    values: &'s [Vec<Stx>],
    left: usize,
    next: Option<Stx>,
    k: Stx,
    lambda: Stx,
    fail: Stx,
}

impl<'gc> Expander<'_, 'gc> {
    /// `(let ((x e)) (let ((none (lambda () (error ...)))) clauses))`, the clauses as
    /// [`Matching::tries`] makes them.
    pub(crate) fn match_form(&mut self, stx: Stx, e: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let m = Matcher { at: stx, temps: 0, parts: HashMap::new(), seen: Vec::new() };
        Matching { ex: self, m, out: Vec::new() }.form(stx, e, clauses)
    }
}

impl<'e, 'a, 'gc> Matching<'e, 'a, 'gc> {
    fn form(&mut self, stx: Stx, e: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let x = self.temp()?;
        let none = self.temp()?.stx;
        let mut parsed = Vec::with_capacity(clauses.len());
        for &clause in clauses {
            self.m.seen.clear();
            parsed.push(self.clause(x, clause)?);
        }
        let parsed: Vec<_> = parsed.iter().map(|(steps, body)| (steps.as_slice(), body)).collect();
        let code = steps::run(self, Code::Tries(parsed, none), Self::code)?;
        let message = string::from_str(&Strings::new(self.ex.mc), "match: no matching clause for")?.value();
        let message = self.ex.value(message, stx)?;
        let error = self.ex.build(stx, "error", &[&[message, x.stx]])?;
        let code = self.let_thunk(stx, none, error, code)?;
        self.ex.with_temp(stx, x.stx, e, code)
    }

    /// `(let ((name (lambda () body))) code)`.
    fn let_thunk(&mut self, at: Stx, name: Stx, body: Stx, code: Stx) -> Result<Stx, ExpandError> {
        let none = self.ex.list(&[], at)?;
        let lambda = self.ex.build(at, "lambda", &[&[none, body]])?;
        self.ex.with_temp(at, name, lambda, code)
    }

    fn temp(&mut self) -> Result<Temp, ExpandError> {
        self.m.temps += 1;
        Ok(Temp { n: self.m.temps, stx: self.ex.introduce(&format!("x{}", self.m.temps), self.m.at)? })
    }

    /// The temporary for `part` of `x`: the same one each time.
    fn part(&mut self, x: Temp, part: Part) -> Result<Temp, ExpandError> {
        if let Some(&temp) = self.m.parts.get(&(x.n, part)) {
            return Ok(temp);
        }
        let temp = self.temp()?;
        self.m.parts.insert((x.n, part), temp);
        Ok(temp)
    }

    fn code<'s>(&mut self, code: Code<'s>) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        match code {
            Code::Emit(steps, done, fail) => self.emit(steps, done, fail),
            Code::Tries(clauses, fail) => self.tries(clauses, fail),
            Code::Run(run, fail) => self.match_run(run, fail),
        }
    }

    /// The code of `clauses`: the body of the first whose steps match, or else `(fail)`. Each
    /// run of clauses that start with the same step that has no effects share it, and the run
    /// fails by calling a procedure that tries what's after it.
    fn tries<'s>(&mut self, clauses: Vec<Clause<'s>>, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let mut runs = Vec::new();
        let mut rest = clauses.as_slice();
        while let Some(((steps, _), others)) = rest.split_first() {
            let n = match steps.first() {
                Some(first) => 1 + others.iter().take_while(|(other, _)| other.first().is_some_and(|o| first.shares(o))).count(),
                None => 1,
            };
            let (run, after) = rest.split_at(n);
            runs.push(run.to_vec());
            rest = after;
        }
        self.runs(runs, None, fail)
    }

    /// The code of the `runs` left, from the last, the code after them `code`.
    fn runs<'s>(&mut self, mut runs: Vec<Vec<Clause<'s>>>, code: Option<Stx>, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let at = self.m.at;
        let Some(run) = runs.pop() else {
            return Ok(Next::Done(match code {
                Some(code) => code,
                None => self.ex.list(&[fail], at)?,
            }));
        };
        let next = if code.is_some() { self.temp()?.stx } else { fail };
        Ok(Next::then(Code::Run(run, next), move |s: &mut Self, this| {
            let code = match code {
                Some(later) => s.let_thunk(at, next, later, this)?,
                None => this,
            };
            s.runs(runs, Some(code), fail)
        }))
    }

    /// The code of `run`, clauses that all start with the same step if there's more than one.
    fn match_run<'s>(&mut self, run: Vec<Clause<'s>>, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let failed = self.ex.list(&[fail], self.m.at)?;
        if let [(steps, body)] = *run.as_slice() {
            let done = self.match_body(body, fail)?;
            return Ok(Next::Tail(Code::Emit(steps, done, failed)));
        }
        let shared: &'s [Step] = run[0].0;
        let rest = run.iter().map(|&(steps, body)| (&steps[1..], body)).collect();
        Ok(Next::then(Code::Tries(rest, fail), move |_, done| Ok(Next::Tail(Code::Emit(&shared[..1], done, failed)))))
    }

    /// A clause's steps for matching `x` and its body.
    fn clause(&mut self, x: Temp, clause: Stx) -> Result<(Vec<Step>, Body), ExpandError> {
        let parts = self.ex.proper(clause)?;
        let Some((&pattern, rest)) = parts.split_first() else { return Err(self.ex.error(ExpandErrorKind::BadSyntax, clause)) };
        let steps = self.match_pattern(x, pattern)?;
        let when_ = self.ex.symbol("when")?;
        let when = rest.first().is_some_and(|&first| self.ex.tree.keyword(first).is_some_and(|k| k.symbol(self.ex.mc) == when_));
        let escape = match rest.first() {
            Some(&first) => self.escape(first)?,
            None => None,
        };
        let (guard, escape, body) = match (when, escape, rest) {
            (true, _, &[_, test, ref body @ ..]) if !body.is_empty() => (Some(test), None, body),
            (false, Some(id), &[_, ref body @ ..]) if !body.is_empty() => (None, Some(id), body),
            (false, None, body) if !body.is_empty() => (None, None, body),
            _ => return Err(self.ex.error(ExpandErrorKind::BadSyntax, clause)),
        };
        Ok((steps, Body { clause, guard, escape, body: body.to_vec() }))
    }

    /// The code of `body`, which calls `fail` if its guard is false.
    fn match_body(&mut self, body: &Body, fail: Stx) -> Result<Stx, ExpandError> {
        let Body { clause, guard, escape, ref body } = *body;
        let none = self.ex.list(&[], clause)?;
        let code = self.ex.build(clause, "let", &[&[none], body])?;
        match (guard, escape) {
            (Some(test), _) => {
                let failed = self.ex.list(&[fail], clause)?;
                self.ex.build(clause, "if", &[&[test, code, failed]])
            }
            (None, Some(id)) => self.ex.with_temp(clause, id, fail, code),
            (None, None) => Ok(code),
        }
    }

    /// The `id` of `(=> id)`, if `stx` is one.
    fn escape(&mut self, stx: Stx) -> Result<Option<Stx>, ExpandError> {
        let View::List(items, None) = self.ex.tree.view(stx)? else { return Ok(None) };
        Ok(match *items {
            [arrow, id] if self.ex.is_aux(arrow, Aux::Arrow)? && self.ex.is_id(id) => Some(id),
            _ => None,
        })
    }

    /// The steps of matching `p` against `x`, binding its variables last.
    fn match_pattern(&mut self, x: Temp, p: Stx) -> Result<Vec<Step>, ExpandError> {
        self.out.push(Vec::new());
        steps::run(self, (x, p), Self::pattern)?;
        let steps = self.out.pop().expect("a pattern's steps");
        let (mut steps, vars): (Vec<_>, Vec<_>) = steps.into_iter().partition(|step| !matches!(step, Step::Var(..)));
        steps.extend(vars);
        Ok(steps)
    }

    /// The steps of matching `p` against `x` within another pattern, which binds none of its
    /// variables, to `then`: what they're bound to is in `m.seen`.
    fn inner_pattern(&mut self, x: Temp, p: Stx, then: impl FnOnce(&mut Self, Vec<Step>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> + 'e) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        self.out.push(Vec::new());
        Ok(Next::then((x, p), move |s: &mut Self, ()| {
            let mut steps = s.out.pop().expect("an inner pattern's steps");
            steps.retain(|step| !matches!(step, Step::Var(..)));
            then(s, steps)
        }))
    }

    fn push(&mut self, step: Step) {
        self.out.last_mut().expect("a pattern's steps").push(step);
    }

    /// Binds the variables `m.seen` has from `first` on to `results`, temporaries for what they're
    /// bound to once an `or` or a repeat has matched.
    fn bind_results(&mut self, first: usize, results: &[Stx]) {
        let out = self.out.last_mut().expect("a pattern's steps");
        for (seen, &result) in self.m.seen[first..].iter_mut().zip(results) {
            seen.value = result;
            out.push(Step::Var(seen.id, result));
        }
    }

    /// Adds what matching `p` against `x` does to the steps being made.
    fn pattern(&mut self, (x, p): (Temp, Stx)) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let bad = |this: &Self, at| Err(this.ex.error(ExpandErrorKind::BadSyntax, at));
        let (items, tail) = match self.ex.tree.view(p)? {
            View::Id if self.ex.is_aux(p, Aux::Underscore)? => return Ok(Next::Done(())),
            View::Id if self.ex.is_aux(p, Aux::Ellipsis)? => return bad(self, p),
            View::Id => {
                self.variable(x, p)?;
                return Ok(Next::Done(()));
            }
            View::Datum(value) => {
                let same = if value.immediate().is_some() { "eqv?" } else { "equal?" };
                let quoted = self.ex.quoted(p, p)?;
                let test = self.ex.build(p, same, &[&[x.stx, quoted]])?;
                self.push(Step::Test(test));
                return Ok(Next::Done(()));
            }
            View::Vector(_) => {
                let quoted = self.ex.quoted(p, p)?;
                let test = self.ex.build(p, "equal?", &[&[x.stx, quoted]])?;
                self.push(Step::Test(test));
                return Ok(Next::Done(()));
            }
            View::List(items, None) if items.is_empty() => {
                self.push(Step::Is(Shape::Null, x));
                return Ok(Next::Done(()));
            }
            View::List(items, tail) => (items, tail),
        };
        let name = match self.ex.tree.symbol(items[0]) {
            Some(symbol) if tail.is_none() => string::chars(&Strings::new(self.ex.mc), symbol.name(self.ex.mc)).collect::<String>(),
            _ => return bad(self, p),
        };
        let args = &items[1..];
        let step = match (name.as_str(), args) {
            ("quote", [_]) => Step::Test(self.ex.build(p, "equal?", &[&[x.stx, p]])?),
            ("quasiquote", _) => return Err(self.ex.error(ExpandErrorKind::Unsupported, p)),
            ("list", _) => return self.list_pattern(x, args.to_vec(), 0, None),
            ("list-rest", &[ref init @ .., rest]) => return self.list_pattern(x, init.to_vec(), 0, Some(rest)),
            ("cons", &[head, rest]) => return self.list_pattern(x, vec![head], 0, Some(rest)),
            ("vector", _) => {
                self.push(Step::Is(Shape::Vector, x));
                self.push(Step::Is(Shape::Length(args.len()), x));
                return self.vector_pattern(x, args.to_vec(), 0);
            }
            ("?", &[pred, ref pats @ ..]) => {
                let test = self.ex.list(&[pred, x.stx], p)?;
                self.push(Step::Test(test));
                return self.each_pattern(x, pats.to_vec(), 0);
            }
            ("and", pats) => return self.each_pattern(x, pats.to_vec(), 0),
            ("or", []) => Step::Test(self.ex.value(Value::FALSE, p)?),
            ("or", alts) => {
                let before = self.m.seen.clone();
                return self.or_pattern(Or { x, alts: alts.to_vec(), before, steps: Vec::with_capacity(alts.len()), bound: Vec::with_capacity(alts.len()) });
            }
            ("not", pats) => return self.not_pattern(x, pats.to_vec(), 0),
            ("app", &[f, pat]) => {
                let result = self.temp()?;
                let value = self.ex.list(&[f, x.stx], p)?;
                self.push(Step::Bind(result, value));
                return Ok(Next::Tail((result, pat)));
            }
            ("==", &[v]) => Step::Test(self.ex.build(p, "equal?", &[&[v, x.stx]])?),
            ("==", &[v, same]) => Step::Test(self.ex.list(&[same, v, x.stx], p)?),
            _ => return bad(self, p),
        };
        self.push(step);
        Ok(Next::Done(()))
    }

    /// Matches each of `pats` from `i` on against `x`.
    fn each_pattern(&mut self, x: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        Ok(Next::then((x, pat), move |s: &mut Self, ()| s.each_pattern(x, pats, i + 1)))
    }

    /// Matches the items of the vector `x` from `i` on against `pats`.
    fn vector_pattern(&mut self, x: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        if self.ex.is_aux(pat, Aux::Ellipsis)? {
            return Err(self.ex.error(ExpandErrorKind::Unsupported, pat));
        }
        let item = self.part(x, Part::Item(i))?;
        self.push(Step::Get(item, Part::Item(i), x));
        Ok(Next::then((item, pat), move |s: &mut Self, ()| s.vector_pattern(x, pats, i + 1)))
    }

    /// Matches the alternatives of `or` from the next on, each binding the same variables.
    fn or_pattern(&mut self, mut or: Or<'gc>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        if let Some(&alt) = or.alts.get(or.steps.len()) {
            self.m.seen.clone_from(&or.before);
            return self.inner_pattern(or.x, alt, move |s, steps| {
                or.steps.push(steps);
                let vars = s.m.seen[or.before.len()..].to_vec();
                // Each alternative binds the same variables, in any order.
                if let Some(first) = or.bound.first()
                    && (first.len() != vars.len() || !vars.iter().all(|v| first.iter().any(|f| f.key() == v.key())))
                {
                    return Err(s.ex.error(ExpandErrorKind::BadSyntax, alt));
                }
                or.bound.push(vars);
                s.or_pattern(or)
            });
        }
        let Or { before, steps, bound, .. } = or;
        let results = (before.len()..self.m.seen.len()).map(|_| Ok(self.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
        let values = bound
            .iter()
            .map(|vars| self.m.seen[before.len()..].iter().map(|v| vars.iter().find(|w| w.key() == v.key()).expect("checked").value).collect())
            .collect();
        self.push(Step::Or { alts: steps, values, results: results.clone() });
        self.bind_results(before.len(), &results);
        Ok(Next::Done(()))
    }

    /// Matches `x` against none of `pats` from `i` on, binding nothing.
    fn not_pattern(&mut self, x: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        let before = self.m.seen.clone();
        self.inner_pattern(x, pat, move |s, steps| {
            s.m.seen = before;
            s.push(Step::Not(steps));
            s.not_pattern(x, pats, i + 1)
        })
    }

    /// Matches anything, bound to `id`, or if `id` is already bound in the pattern, what's
    /// `equal?` to it.
    fn variable(&mut self, x: Temp, id: Stx) -> Result<(), ExpandError> {
        let seen = Seen { id, symbol: self.ex.tree.symbol(id).expect("an identifier"), set: self.ex.tree.scopes_of(id)?, value: x.stx };
        match self.m.seen.iter().find(|other| other.key() == seen.key()) {
            Some(first) => {
                let test = self.ex.build(id, "equal?", &[&[first.value, x.stx]])?;
                self.push(Step::Test(test));
            }
            None => {
                self.m.seen.push(seen);
                self.push(Step::Var(id, x.stx));
            }
        }
        Ok(())
    }

    /// Matches `at`, the rest of a list, against `items` from `i` on, the last of which can be
    /// followed by `...`, then `rest` against its tail, or else the end of the list.
    fn list_pattern(&mut self, at: Temp, items: Vec<Stx>, i: usize, rest: Option<Stx>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&item) = items.get(i) else {
            return match rest {
                Some(rest) => Ok(Next::Tail((at, rest))),
                None => {
                    self.push(Step::Is(Shape::Null, at));
                    Ok(Next::Done(()))
                }
            };
        };
        if self.ex.is_aux(item, Aux::Ellipsis)? {
            return Err(self.ex.error(ExpandErrorKind::BadSyntax, item));
        }
        if let Some(&next) = items.get(i + 1)
            && self.ex.is_aux(next, Aux::Ellipsis)?
        {
            // Only the last pattern can repeat, as only the rest of the list can be split
            // without first counting it.
            if i + 2 != items.len() || rest.is_some() {
                return Err(self.ex.error(ExpandErrorKind::Unsupported, next));
            }
            // A list of anything is the list itself.
            if self.ex.is_id(item) {
                self.push(Step::Is(Shape::List, at));
                if !self.ex.is_aux(item, Aux::Underscore)? {
                    let key = (self.ex.tree.symbol(item).expect("an identifier"), self.ex.tree.scopes_of(item)?);
                    if self.m.seen.iter().any(|seen| seen.key() == key) {
                        return Err(self.ex.error(ExpandErrorKind::Duplicate, item));
                    }
                }
                return Ok(Next::Tail((at, item)));
            }
            let element = self.temp()?;
            let before = std::mem::take(&mut self.m.seen);
            return self.inner_pattern(element, item, move |s, steps| {
                let inner = std::mem::replace(&mut s.m.seen, before);
                if let Some(seen) = inner.iter().find(|seen| s.m.seen.iter().any(|other| other.key() == seen.key())) {
                    return Err(s.ex.error(ExpandErrorKind::Duplicate, seen.id));
                }
                let values = inner.iter().map(|v| v.value).collect();
                let results = inner.iter().map(|_| Ok(s.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                let first = s.m.seen.len();
                s.m.seen.extend(inner);
                s.push(Step::Each { list: at, item: element, steps, values, results: results.clone() });
                s.bind_results(first, &results);
                Ok(Next::Done(()))
            });
        }
        self.push(Step::Is(Shape::Pair, at));
        let head = self.part(at, Part::Car)?;
        self.push(Step::Get(head, Part::Car, at));
        let tail = self.part(at, Part::Cdr)?;
        self.push(Step::Get(tail, Part::Cdr, at));
        Ok(Next::then((head, item), move |s: &mut Self, ()| s.list_pattern(tail, items, i + 1, rest)))
    }

    /// The code of `steps`: `done` if they match, `fail` if they don't.
    fn emit<'s>(&mut self, steps: &'s [Step], done: Stx, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let Some((step, rest)) = steps.split_first() else { return Ok(Next::Done(done)) };
        let at = self.m.at;
        let rest = Code::Emit(rest, done, fail);
        let fixnum = |this: &Self, n: usize| Value::fixnum(n as i64).ok_or_else(|| this.ex.error(ExpandErrorKind::BadSyntax, at));
        Ok(match *step {
            Step::Is(shape, x) => {
                let test = match shape {
                    Shape::Pair => self.ex.build(at, "pair?", &[&[x.stx]])?,
                    Shape::Null => self.ex.build(at, "null?", &[&[x.stx]])?,
                    Shape::List => self.ex.build(at, "list?", &[&[x.stx]])?,
                    Shape::Vector => self.ex.build(at, "vector?", &[&[x.stx]])?,
                    Shape::Length(n) => {
                        let n = self.ex.value(fixnum(self, n)?, at)?;
                        let len = self.ex.build(at, "vector-length", &[&[x.stx]])?;
                        self.ex.build(at, "eqv?", &[&[len, n]])?
                    }
                };
                Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.build(at, "if", &[&[test, rest, fail]])?)))
            }
            Step::Get(temp, part, x) => {
                let value = match part {
                    Part::Car => self.ex.build(at, "car", &[&[x.stx]])?,
                    Part::Cdr => self.ex.build(at, "cdr", &[&[x.stx]])?,
                    Part::Item(i) => {
                        let k = self.ex.value(fixnum(self, i)?, at)?;
                        self.ex.build(at, "vector-ref", &[&[x.stx, k]])?
                    }
                };
                Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.with_temp(at, temp.stx, value, rest)?)))
            }
            Step::Test(test) => Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.build(at, "if", &[&[test, rest, fail]])?))),
            Step::Bind(temp, value) => Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.with_temp(at, temp.stx, value, rest)?))),
            Step::Var(var, value) => Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.with_temp(at, var, value, rest)?))),
            Step::Not(ref steps) => {
                let (yes, no) = (self.ex.value(Value::TRUE, at)?, self.ex.value(Value::FALSE, at)?);
                Next::then(Code::Emit(steps, yes, no), move |_, test| {
                    Ok(Next::then(rest, move |s: &mut Self, rest| Ok(Next::Done(s.ex.build(at, "if", &[&[test, fail, rest]])?))))
                })
            }
            // `(let ((k (lambda (result ...) rest))) alt)`, each alt calling `k` with its values,
            // and each but the last trying the next if it fails.
            Step::Or { ref alts, ref values, ref results } => {
                let k = self.temp()?.stx;
                let formals = self.ex.list(results, at)?;
                Next::then(rest, move |s: &mut Self, rest| {
                    let lambda = s.ex.build(at, "lambda", &[&[formals, rest]])?;
                    s.alternatives(Alternatives { alts, values, left: alts.len(), next: None, k, lambda, fail })
                })
            }
            // `(let loop ((xs list) (acc '()) ...) (if (null? xs) (let ((result (reverse acc)) ...)
            // rest) (if (pair? xs) (let ((item (car xs))) steps, then (loop (cdr xs) (cons value
            // acc) ...)) fail)))`.
            Step::Each { list, item, ref steps, ref values, ref results } => {
                let (again, xs) = (self.temp()?.stx, self.temp()?.stx);
                let accs = values.iter().map(|_| Ok(self.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                Next::then(rest, move |s: &mut Self, mut finished| {
                    for (&result, &acc) in results.iter().zip(&accs).rev() {
                        let reversed = s.ex.build(at, "reverse", &[&[acc]])?;
                        finished = s.ex.with_temp(at, result, reversed, finished)?;
                    }
                    let mut next = vec![again, s.ex.build(at, "cdr", &[&[xs]])?];
                    for (&value, &acc) in values.iter().zip(&accs) {
                        next.push(s.ex.build(at, "cons", &[&[value, acc]])?);
                    }
                    let next = s.ex.list(&next, at)?;
                    Ok(Next::then(Code::Emit(steps, next, fail), move |s: &mut Self, each| {
                        let first = s.ex.build(at, "car", &[&[xs]])?;
                        let each = s.ex.with_temp(at, item.stx, first, each)?;
                        let is_pair = s.ex.build(at, "pair?", &[&[xs]])?;
                        let more = s.ex.build(at, "if", &[&[is_pair, each, fail]])?;
                        let is_null = s.ex.build(at, "null?", &[&[xs]])?;
                        let body = s.ex.build(at, "if", &[&[is_null, finished, more]])?;
                        let mut binds = vec![s.ex.list(&[xs, list.stx], at)?];
                        for &acc in &accs {
                            let empty = s.ex.value(Value::NIL, at)?;
                            let empty = s.ex.quoted(empty, at)?;
                            binds.push(s.ex.list(&[acc, empty], at)?);
                        }
                        let binds = s.ex.list(&binds, at)?;
                        Ok(Next::Done(s.ex.build(at, "let", &[&[again, binds, body]])?))
                    }))
                })
            }
        })
    }

    /// The code of an `or` step's alternatives left, each calling its `k` with its values.
    fn alternatives<'s>(&mut self, mut a: Alternatives<'s>) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let at = self.m.at;
        let Some(left) = a.left.checked_sub(1) else {
            let alts = a.next.expect("an `or` of no patterns is a test");
            return Ok(Next::Done(self.ex.with_temp(at, a.k, a.lambda, alts)?));
        };
        a.left = left;
        let (alts, values) = (a.alts, a.values);
        let matched = self.ex.list(&[&[a.k], values[left].as_slice()].concat(), at)?;
        Ok(match a.next {
            None => Next::then(Code::Emit(&alts[left], matched, a.fail), move |s: &mut Self, code| {
                a.next = Some(code);
                s.alternatives(a)
            }),
            Some(next) => {
                let other = self.temp()?.stx;
                let tried = self.ex.list(&[other], at)?;
                Next::then(Code::Emit(&alts[left], matched, tried), move |s: &mut Self, code| {
                    let none = s.ex.list(&[], at)?;
                    let thunk = s.ex.build(at, "lambda", &[&[none, next]])?;
                    a.next = Some(s.ex.with_temp(at, other, thunk, code)?);
                    s.alternatives(a)
                })
            }
        })
    }
}
