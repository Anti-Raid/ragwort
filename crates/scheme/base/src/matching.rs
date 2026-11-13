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
//! - `(name p ...)`, `name` a struct's, a struct of its type, or of a subtype of it, each field
//!   matching its `p`: all its fields, its supertype's first. One `p` can be followed by `...`,
//!   which matches it against each field the other patterns leave, and binds each of its
//!   variables to a list: `(user name _ ...)` looks at the first field only, and
//!   `(point3 x rest ...)` binds `rest` to the list of the other two.
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
    /// A struct of the type that's this one of the matcher's.
    Struct(usize),
}

/// A part of a pair or vector, or a field of a struct of one of the matcher's types.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Part {
    Car,
    Cdr,
    Item(usize),
    Field(usize, usize),
}

/// One of a struct pattern's patterns, with the fields it's matched against, `count` of them
/// from `first` on: one, or for a pattern that `...` follows, as many as the others leave.
#[derive(Clone, Copy)]
struct FieldPat {
    pat: Stx,
    first: usize,
    count: usize,
    repeats: bool,
}

/// A struct type patterns name: an expression for it, and what tells it from the others.
struct Named<'gc> {
    kind: Stx,
    key: Value<'gc>,
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
            (Self::Is(shape, temp), Self::Is(other, other_temp)) => shape == other && temp.n == other_temp.n,
            (Self::Get(temp, ..), Self::Get(other_temp, ..)) => temp.n == other_temp.n,
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
    structs: Vec<Named<'gc>>,
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
    /// `(let ((x expr)) (let ((none (lambda () (error ...)))) clauses))`, the clauses as
    /// [`Matching::tries`] makes them.
    pub(crate) fn match_form(&mut self, stx: Stx, expr: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let matcher = Matcher { at: stx, temps: 0, parts: HashMap::new(), seen: Vec::new(), structs: Vec::new() };
        Matching { ex: self, m: matcher, out: Vec::new() }.form(stx, expr, clauses)
    }
}

impl<'e, 'a, 'gc> Matching<'e, 'a, 'gc> {
    fn form(&mut self, stx: Stx, expr: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let target = self.temp()?;
        let none = self.temp()?.stx;
        let mut parsed = Vec::with_capacity(clauses.len());
        for &clause in clauses {
            self.m.seen.clear();
            parsed.push(self.clause(target, clause)?);
        }
        let parsed: Vec<_> = parsed.iter().map(|(steps, body)| (steps.as_slice(), body)).collect();
        let code = steps::run(self, Code::Tries(parsed, none), Self::code)?;
        let message = string::from_str(&Strings::new(self.ex.mc), "match: no matching clause for")?.value();
        let message = self.ex.value(message, stx)?;
        let error = self.ex.build(stx, "error", &[&[message, target.stx]])?;
        let code = self.let_thunk(stx, none, error, code)?;
        self.ex.with_temp(stx, target.stx, expr, code)
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

    /// The temporary for `part` of `target`: the same one each time.
    fn part(&mut self, target: Temp, part: Part) -> Result<Temp, ExpandError> {
        if let Some(&temp) = self.m.parts.get(&(target.n, part)) {
            return Ok(temp);
        }
        let temp = self.temp()?;
        self.m.parts.insert((target.n, part), temp);
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
    ///
    /// A run that starts with a test, such as `(point? x)`, is in two procedures: `matched`,
    /// which is the rest of the run, and one that's just `(if test (matched) (next))`. The
    /// optimizer takes a call of that small one to be a call of the procedure it picks,
    /// wherever what's known decides the test: a clause that failed for not being a `point`
    /// goes past the later `point` clauses without testing again, however many there are.
    fn tries<'s>(&mut self, clauses: Vec<Clause<'s>>, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let mut runs = Vec::new();
        let mut rest = clauses.as_slice();
        while let Some(((steps, _), others)) = rest.split_first() {
            let count = match steps.first() {
                Some(first) => 1 + others.iter().take_while(|(other, _)| other.first().is_some_and(|step| first.shares(step))).count(),
                None => 1,
            };
            let (run, after) = rest.split_at(count);
            runs.push(run.to_vec());
            rest = after;
        }
        if runs.is_empty() {
            return Ok(Next::Done(self.ex.list(&[fail], self.m.at)?));
        }
        self.runs(runs, Vec::new(), fail)
    }

    /// The code of the `runs` left, from the last. A run that fails calls `next`, and the
    /// procedures the runs after these are in are `later`, each with its name, from the last
    /// run's: each is bound around those after it in `later` and the code of the first run.
    fn runs<'s>(&mut self, mut runs: Vec<Vec<Clause<'s>>>, mut later: Vec<(Stx, Stx)>, next: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let at = self.m.at;
        let run = runs.pop().expect("a run left");
        // The first run is tried where the match is.
        if runs.is_empty() {
            return Ok(Next::then(Code::Run(run, next), move |this: &mut Self, mut code| {
                for (name, body) in later.into_iter().rev() {
                    code = this.let_thunk(at, name, body, code)?;
                }
                Ok(Next::Done(code))
            }));
        }
        let tries = self.temp()?.stx;
        let Some(&Step::Is(shape, temp)) = run[0].0.first() else {
            return Ok(Next::then(Code::Run(run, next), move |matching: &mut Self, this| {
                later.push((tries, this));
                matching.runs(runs, later, tries)
            }));
        };
        // A run that starts with a test is the test, which picks a procedure, and the rest.
        let matched = self.temp()?.stx;
        let test = self.shape_test(shape, temp)?;
        let (to_matched, to_next) = (self.ex.list(&[matched], at)?, self.ex.list(&[next], at)?);
        let pick = self.ex.build(at, "if", &[&[test, to_matched, to_next]])?;
        let rest = match *run.as_slice() {
            [(steps, body)] => Code::Emit(&steps[1..], self.match_body(body, next)?, to_next),
            _ => Code::Tries(run.iter().map(|&(steps, body)| (&steps[1..], body)).collect(), next),
        };
        Ok(Next::then(rest, move |this: &mut Self, rest| {
            later.extend([(matched, rest), (tries, pick)]);
            this.runs(runs, later, tries)
        }))
    }

    /// The test of whether `target` has `shape`.
    fn shape_test(&mut self, shape: Shape, target: Temp) -> Result<Stx, ExpandError> {
        let at = self.m.at;
        Ok(match shape {
            Shape::Pair => self.ex.build(at, "pair?", &[&[target.stx]])?,
            Shape::Null => self.ex.build(at, "null?", &[&[target.stx]])?,
            Shape::List => self.ex.build(at, "list?", &[&[target.stx]])?,
            Shape::Vector => self.ex.build(at, "vector?", &[&[target.stx]])?,
            Shape::Length(count) => {
                let count = Value::fixnum(count as i64).ok_or_else(|| self.ex.error(ExpandErrorKind::BadSyntax, at))?;
                let count = self.ex.value(count, at)?;
                let len = self.ex.build(at, "vector-length", &[&[target.stx]])?;
                self.ex.build(at, "eqv?", &[&[len, count]])?
            }
            Shape::Struct(of) => {
                let kind = self.m.structs[of].kind;
                self.ex.build(at, "struct-derived-from?", &[&[target.stx, kind]])?
            }
        })
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

    /// A clause's steps for matching `target` and its body.
    fn clause(&mut self, target: Temp, clause: Stx) -> Result<(Vec<Step>, Body), ExpandError> {
        let parts = self.ex.proper(clause)?;
        let Some((&pattern, rest)) = parts.split_first() else { return Err(self.ex.error(ExpandErrorKind::BadSyntax, clause)) };
        let steps = self.match_pattern(target, pattern)?;
        let when_ = self.ex.symbol("when")?;
        let when = rest.first().is_some_and(|&first| self.ex.tree.keyword(first).is_some_and(|keyword| keyword.symbol(self.ex.mc) == when_));
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

    /// The steps of matching `pattern` against `target`, binding its variables last.
    fn match_pattern(&mut self, target: Temp, pattern: Stx) -> Result<Vec<Step>, ExpandError> {
        self.out.push(Vec::new());
        steps::run(self, (target, pattern), Self::pattern)?;
        let steps = self.out.pop().expect("a pattern's steps");
        let (mut steps, vars): (Vec<_>, Vec<_>) = steps.into_iter().partition(|step| !matches!(step, Step::Var(..)));
        steps.extend(vars);
        Ok(steps)
    }

    /// The steps of matching `pattern` against `target` within another pattern, which binds none of its
    /// variables, to `then`: what they're bound to is in `m.seen`.
    fn inner_pattern(&mut self, target: Temp, pattern: Stx, then: impl FnOnce(&mut Self, Vec<Step>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> + 'e) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        self.out.push(Vec::new());
        Ok(Next::then((target, pattern), move |this: &mut Self, ()| {
            let mut steps = this.out.pop().expect("an inner pattern's steps");
            steps.retain(|step| !matches!(step, Step::Var(..)));
            then(this, steps)
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

    /// Adds what matching `pattern` against `target` does to the steps being made.
    fn pattern(&mut self, (target, pattern): (Temp, Stx)) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let bad = |this: &Self, at| Err(this.ex.error(ExpandErrorKind::BadSyntax, at));
        let (items, tail) = match self.ex.tree.view(pattern)? {
            View::Id if self.ex.is_aux(pattern, Aux::Underscore)? => return Ok(Next::Done(())),
            View::Id if self.ex.is_aux(pattern, Aux::Ellipsis)? => return bad(self, pattern),
            View::Id => {
                self.variable(target, pattern)?;
                return Ok(Next::Done(()));
            }
            View::Datum(value) => {
                let same = if value.immediate().is_some() { "eqv?" } else { "equal?" };
                let quoted = self.ex.quoted(pattern, pattern)?;
                let test = self.ex.build(pattern, same, &[&[target.stx, quoted]])?;
                self.push(Step::Test(test));
                return Ok(Next::Done(()));
            }
            View::Vector(_) => {
                let quoted = self.ex.quoted(pattern, pattern)?;
                let test = self.ex.build(pattern, "equal?", &[&[target.stx, quoted]])?;
                self.push(Step::Test(test));
                return Ok(Next::Done(()));
            }
            View::List(items, None) if items.is_empty() => {
                self.push(Step::Is(Shape::Null, target));
                return Ok(Next::Done(()));
            }
            View::List(items, tail) => (items, tail),
        };
        let name = match self.ex.tree.symbol(items[0]) {
            Some(symbol) if tail.is_none() => string::chars(&Strings::new(self.ex.mc), symbol.name(self.ex.mc)).collect::<String>(),
            _ => return bad(self, pattern),
        };
        let args = &items[1..];
        let step = match (name.as_str(), args) {
            ("quote", [_]) => Step::Test(self.ex.build(pattern, "equal?", &[&[target.stx, pattern]])?),
            ("quasiquote", _) => return Err(self.ex.error(ExpandErrorKind::Unsupported, pattern)),
            ("list", _) => return self.list_pattern(target, args.to_vec(), 0, None),
            ("list-rest", &[ref init @ .., rest]) => return self.list_pattern(target, init.to_vec(), 0, Some(rest)),
            ("cons", &[head, rest]) => return self.list_pattern(target, vec![head], 0, Some(rest)),
            ("vector", _) => {
                self.push(Step::Is(Shape::Vector, target));
                self.push(Step::Is(Shape::Length(args.len()), target));
                return self.vector_pattern(target, args.to_vec(), 0);
            }
            ("?", &[pred, ref pats @ ..]) => {
                let test = self.ex.list(&[pred, target.stx], pattern)?;
                self.push(Step::Test(test));
                return self.each_pattern(target, pats.to_vec(), 0);
            }
            ("and", pats) => return self.each_pattern(target, pats.to_vec(), 0),
            ("or", []) => Step::Test(self.ex.value(Value::FALSE, pattern)?),
            ("or", alts) => {
                let before = self.m.seen.clone();
                return self.or_pattern(Or { x: target, alts: alts.to_vec(), before, steps: Vec::with_capacity(alts.len()), bound: Vec::with_capacity(alts.len()) });
            }
            ("not", pats) => return self.not_pattern(target, pats.to_vec(), 0),
            ("app", &[function, pat]) => {
                let result = self.temp()?;
                let value = self.ex.list(&[function, target.stx], pattern)?;
                self.push(Step::Bind(result, value));
                return Ok(Next::Tail((result, pat)));
            }
            ("==", &[expected]) => Step::Test(self.ex.build(pattern, "equal?", &[&[expected, target.stx]])?),
            ("==", &[expected, same]) => Step::Test(self.ex.list(&[same, expected, target.stx], pattern)?),
            _ => {
                let Some(info) = self.ex.struct_info(items[0])? else { return bad(self, pattern) };
                let pats = self.field_pats(pattern, args, info.fields.len())?;
                let key = info.kind;
                let known = self.m.structs.iter().position(|named| named.key == key);
                let of = match known {
                    Some(of) => of,
                    None => {
                        let kind = self.ex.struct_type(&info, pattern)?;
                        self.m.structs.push(Named { kind, key });
                        self.m.structs.len() - 1
                    }
                };
                self.push(Step::Is(Shape::Struct(of), target));
                return self.field_pattern(target, of, pats, 0);
            }
        };
        self.push(step);
        Ok(Next::Done(()))
    }

    /// Matches each of `pats` from `i` on against `target`.
    fn each_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        Ok(Next::then((target, pat), move |this: &mut Self, ()| this.each_pattern(target, pats, i + 1)))
    }

    /// The fields each of `pats`, the patterns of the struct pattern `pattern`, is matched against,
    /// the struct having `fields` of them. Only one pattern can repeat, and there's a field
    /// for each one that doesn't.
    fn field_pats(&mut self, pattern: Stx, pats: &[Stx], fields: usize) -> Result<Vec<FieldPat>, ExpandError> {
        let bad = ExpandErrorKind::BadSyntax;
        let mut dots = None;
        for (i, &pat) in pats.iter().enumerate() {
            if self.ex.is_aux(pat, Aux::Ellipsis)? {
                if i == 0 || dots.is_some() {
                    return Err(self.ex.error(bad, pat));
                }
                dots = Some(i);
            }
        }
        let single = pats.len() - if dots.is_some() { 2 } else { 0 };
        let spare = match fields.checked_sub(single) {
            Some(spare) if spare == 0 || dots.is_some() => spare,
            _ => return Err(self.ex.error(bad, pattern)),
        };
        let mut out = Vec::with_capacity(pats.len());
        let mut first = 0;
        for (i, &pat) in pats.iter().enumerate() {
            if dots == Some(i) {
                continue;
            }
            let repeats = dots == Some(i + 1);
            let count = if repeats { spare } else { 1 };
            out.push(FieldPat { pat, first, count, repeats });
            first += count;
        }
        Ok(out)
    }

    /// A temporary for field `index` of `target`, a struct of the matcher's type `of`, read by then.
    fn field(&mut self, target: Temp, of: usize, index: usize) -> Result<Temp, ExpandError> {
        let field = self.part(target, Part::Field(of, index))?;
        self.push(Step::Get(field, Part::Field(of, index), target));
        Ok(field)
    }

    /// Matches the fields of `target`, a struct of the matcher's type `of`, against `pats` from `i`
    /// on. A pattern that repeats is matched against the list of its fields, as a list's last
    /// pattern is against the rest of the list, and `_ ...` reads none.
    fn field_pattern(&mut self, target: Temp, of: usize, pats: Vec<FieldPat>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&FieldPat { pat, first, count, repeats }) = pats.get(i) else { return Ok(Next::Done(())) };
        if !repeats {
            let field = self.field(target, of, first)?;
            return Ok(Next::then((field, pat), move |this: &mut Self, ()| this.field_pattern(target, of, pats, i + 1)));
        }
        if self.ex.is_aux(pat, Aux::Underscore)? {
            return self.field_pattern(target, of, pats, i + 1);
        }
        let mut values = Vec::with_capacity(count);
        for index in first..first + count {
            values.push(self.field(target, of, index)?.stx);
        }
        let all = self.temp()?;
        let list = self.ex.build(pat, "list", &[&values])?;
        self.push(Step::Bind(all, list));
        if self.ex.is_id(pat) {
            self.not_bound(pat)?;
            self.variable(all, pat)?;
            return self.field_pattern(target, of, pats, i + 1);
        }
        self.repeat_pattern(all, pat, move |this| this.field_pattern(target, of, pats, i + 1))
    }

    /// An error if the pattern so far binds the variable `id`: one that's bound to a list of
    /// what it matched can't also be a test against what it was bound to before.
    fn not_bound(&mut self, id: Stx) -> Result<(), ExpandError> {
        let key = (self.ex.tree.symbol(id).expect("an identifier"), self.ex.tree.scopes_of(id)?);
        if self.m.seen.iter().any(|seen| seen.key() == key) {
            return Err(self.ex.error(ExpandErrorKind::Duplicate, id));
        }
        Ok(())
    }

    /// Matches each element of `list`, a list, against `item`, binds each of `item`'s variables
    /// to the list of what it was bound to for each element, and goes on to `then`.
    fn repeat_pattern(&mut self, list: Temp, item: Stx, then: impl FnOnce(&mut Self) -> Result<Pat<'e, 'a, 'gc>, ExpandError> + 'e) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let element = self.temp()?;
        let before = std::mem::take(&mut self.m.seen);
        self.inner_pattern(element, item, move |this, steps| {
            let inner = std::mem::replace(&mut this.m.seen, before);
            if let Some(seen) = inner.iter().find(|seen| this.m.seen.iter().any(|other| other.key() == seen.key())) {
                return Err(this.ex.error(ExpandErrorKind::Duplicate, seen.id));
            }
            let values = inner.iter().map(|seen| seen.value).collect();
            let results = inner.iter().map(|_| Ok(this.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
            let first = this.m.seen.len();
            this.m.seen.extend(inner);
            this.push(Step::Each { list, item: element, steps, values, results: results.clone() });
            this.bind_results(first, &results);
            then(this)
        })
    }

    /// Matches the items of the vector `target` from `i` on against `pats`.
    fn vector_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        if self.ex.is_aux(pat, Aux::Ellipsis)? {
            return Err(self.ex.error(ExpandErrorKind::Unsupported, pat));
        }
        let item = self.part(target, Part::Item(i))?;
        self.push(Step::Get(item, Part::Item(i), target));
        Ok(Next::then((item, pat), move |this: &mut Self, ()| this.vector_pattern(target, pats, i + 1)))
    }

    /// Matches the alternatives of `or` from the next on, each binding the same variables.
    fn or_pattern(&mut self, mut or: Or<'gc>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        if let Some(&alt) = or.alts.get(or.steps.len()) {
            self.m.seen.clone_from(&or.before);
            return self.inner_pattern(or.x, alt, move |this, steps| {
                or.steps.push(steps);
                let vars = this.m.seen[or.before.len()..].to_vec();
                // Each alternative binds the same variables, in any order.
                if let Some(first) = or.bound.first()
                    && (first.len() != vars.len() || !vars.iter().all(|var| first.iter().any(|other| other.key() == var.key())))
                {
                    return Err(this.ex.error(ExpandErrorKind::BadSyntax, alt));
                }
                or.bound.push(vars);
                this.or_pattern(or)
            });
        }
        let Or { before, steps, bound, .. } = or;
        let results = (before.len()..self.m.seen.len()).map(|_| Ok(self.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
        let values = bound
            .iter()
            .map(|vars| self.m.seen[before.len()..].iter().map(|seen| vars.iter().find(|var| var.key() == seen.key()).expect("checked").value).collect())
            .collect();
        self.push(Step::Or { alts: steps, values, results: results.clone() });
        self.bind_results(before.len(), &results);
        Ok(Next::Done(()))
    }

    /// Matches `target` against none of `pats` from `i` on, binding nothing.
    fn not_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        let before = self.m.seen.clone();
        self.inner_pattern(target, pat, move |this, steps| {
            this.m.seen = before;
            this.push(Step::Not(steps));
            this.not_pattern(target, pats, i + 1)
        })
    }

    /// Matches anything, bound to `id`, or if `id` is already bound in the pattern, what's
    /// `equal?` to it.
    fn variable(&mut self, target: Temp, id: Stx) -> Result<(), ExpandError> {
        let seen = Seen { id, symbol: self.ex.tree.symbol(id).expect("an identifier"), set: self.ex.tree.scopes_of(id)?, value: target.stx };
        match self.m.seen.iter().find(|other| other.key() == seen.key()) {
            Some(first) => {
                let test = self.ex.build(id, "equal?", &[&[first.value, target.stx]])?;
                self.push(Step::Test(test));
            }
            None => {
                self.m.seen.push(seen);
                self.push(Step::Var(id, target.stx));
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
                    self.not_bound(item)?;
                }
                return Ok(Next::Tail((at, item)));
            }
            return self.repeat_pattern(at, item, |_| Ok(Next::Done(())));
        }
        self.push(Step::Is(Shape::Pair, at));
        let head = self.part(at, Part::Car)?;
        self.push(Step::Get(head, Part::Car, at));
        let tail = self.part(at, Part::Cdr)?;
        self.push(Step::Get(tail, Part::Cdr, at));
        Ok(Next::then((head, item), move |this: &mut Self, ()| this.list_pattern(tail, items, i + 1, rest)))
    }

    /// The code of `steps`: `done` if they match, `fail` if they don't.
    fn emit<'s>(&mut self, steps: &'s [Step], done: Stx, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let Some((step, rest)) = steps.split_first() else { return Ok(Next::Done(done)) };
        let at = self.m.at;
        let rest = Code::Emit(rest, done, fail);
        let fixnum = |this: &Self, index: usize| Value::fixnum(index as i64).ok_or_else(|| this.ex.error(ExpandErrorKind::BadSyntax, at));
        Ok(match *step {
            Step::Is(shape, target) => {
                let test = self.shape_test(shape, target)?;
                Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.build(at, "if", &[&[test, rest, fail]])?)))
            }
            Step::Get(temp, part, target) => {
                let value = match part {
                    Part::Car => self.ex.build(at, "car", &[&[target.stx]])?,
                    Part::Cdr => self.ex.build(at, "cdr", &[&[target.stx]])?,
                    Part::Item(index) => {
                        let index = self.ex.value(fixnum(self, index)?, at)?;
                        self.ex.build(at, "vector-ref", &[&[target.stx, index]])?
                    }
                    Part::Field(of, index) => {
                        let kind = self.m.structs[of].kind;
                        let index = self.ex.value(fixnum(self, index)?, at)?;
                        let get = self.ex.internal("struct-ref", at)?;
                        self.ex.list(&[get, target.stx, kind, index], at)?
                    }
                };
                Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.with_temp(at, temp.stx, value, rest)?)))
            }
            Step::Test(test) => Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.build(at, "if", &[&[test, rest, fail]])?))),
            Step::Bind(temp, value) => Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.with_temp(at, temp.stx, value, rest)?))),
            Step::Var(var, value) => Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.with_temp(at, var, value, rest)?))),
            Step::Not(ref steps) => {
                let (yes, no) = (self.ex.value(Value::TRUE, at)?, self.ex.value(Value::FALSE, at)?);
                Next::then(Code::Emit(steps, yes, no), move |_, test| {
                    Ok(Next::then(rest, move |this: &mut Self, rest| Ok(Next::Done(this.ex.build(at, "if", &[&[test, fail, rest]])?))))
                })
            }
            // `(let ((k (lambda (result ...) rest))) alt)`, each alt calling `k` with its values,
            // and each but the last trying the next if it fails.
            Step::Or { ref alts, ref values, ref results } => {
                let join = self.temp()?.stx;
                let formals = self.ex.list(results, at)?;
                Next::then(rest, move |this: &mut Self, rest| {
                    let lambda = this.ex.build(at, "lambda", &[&[formals, rest]])?;
                    this.alternatives(Alternatives { alts, values, left: alts.len(), next: None, k: join, lambda, fail })
                })
            }
            // `(let loop ((xs list) (acc '()) ...) (if (null? xs) (let ((result (reverse acc)) ...)
            // rest) (if (pair? xs) (let ((item (car xs))) steps, then (loop (cdr xs) (cons value
            // acc) ...)) fail)))`.
            Step::Each { list, item, ref steps, ref values, ref results } => {
                let (again, xs) = (self.temp()?.stx, self.temp()?.stx);
                let accs = values.iter().map(|_| Ok(self.temp()?.stx)).collect::<Result<Vec<_>, ExpandError>>()?;
                Next::then(rest, move |this: &mut Self, mut finished| {
                    for (&result, &acc) in results.iter().zip(&accs).rev() {
                        let reversed = this.ex.build(at, "reverse", &[&[acc]])?;
                        finished = this.ex.with_temp(at, result, reversed, finished)?;
                    }
                    let mut next = vec![again, this.ex.build(at, "cdr", &[&[xs]])?];
                    for (&value, &acc) in values.iter().zip(&accs) {
                        next.push(this.ex.build(at, "cons", &[&[value, acc]])?);
                    }
                    let next = this.ex.list(&next, at)?;
                    Ok(Next::then(Code::Emit(steps, next, fail), move |this: &mut Self, each| {
                        let first = this.ex.build(at, "car", &[&[xs]])?;
                        let each = this.ex.with_temp(at, item.stx, first, each)?;
                        let is_pair = this.ex.build(at, "pair?", &[&[xs]])?;
                        let more = this.ex.build(at, "if", &[&[is_pair, each, fail]])?;
                        let is_null = this.ex.build(at, "null?", &[&[xs]])?;
                        let body = this.ex.build(at, "if", &[&[is_null, finished, more]])?;
                        let mut binds = vec![this.ex.list(&[xs, list.stx], at)?];
                        for &acc in &accs {
                            let empty = this.ex.value(Value::NIL, at)?;
                            let empty = this.ex.quoted(empty, at)?;
                            binds.push(this.ex.list(&[acc, empty], at)?);
                        }
                        let binds = this.ex.list(&binds, at)?;
                        Ok(Next::Done(this.ex.build(at, "let", &[&[again, binds, body]])?))
                    }))
                })
            }
        })
    }

    /// The code of an `or` step's alternatives left, each calling its `k` with its values.
    fn alternatives<'s>(&mut self, mut alternatives: Alternatives<'s>) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let at = self.m.at;
        let Some(left) = alternatives.left.checked_sub(1) else {
            let alts = alternatives.next.expect("an `or` of no patterns is a test");
            return Ok(Next::Done(self.ex.with_temp(at, alternatives.k, alternatives.lambda, alts)?));
        };
        alternatives.left = left;
        let (alts, values) = (alternatives.alts, alternatives.values);
        let matched = self.ex.list(&[&[alternatives.k], values[left].as_slice()].concat(), at)?;
        Ok(match alternatives.next {
            None => Next::then(Code::Emit(&alts[left], matched, alternatives.fail), move |this: &mut Self, code| {
                alternatives.next = Some(code);
                this.alternatives(alternatives)
            }),
            Some(next) => {
                let other = self.temp()?.stx;
                let tried = self.ex.list(&[other], at)?;
                Next::then(Code::Emit(&alts[left], matched, tried), move |this: &mut Self, code| {
                    let none = this.ex.list(&[], at)?;
                    let thunk = this.ex.build(at, "lambda", &[&[none, next]])?;
                    alternatives.next = Some(this.ex.with_temp(at, other, thunk, code)?);
                    this.alternatives(alternatives)
                })
            }
        })
    }
}
