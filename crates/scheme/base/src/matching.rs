//! `match`, as in Racket. `(match e clause ...)` tries the pattern of each clause on the value of `e`, in
//! order. It runs the body of the first clause whose pattern matches, with the pattern's variables bound. A
//! clause is `[pattern body ...+]`, or `[pattern #:when test body ...+]`, which also requires `test`
//! to be true, or `[pattern (=> id) body ...+]`, which binds `id` to a procedure of no arguments that
//! continues with the next clause. If no clause matches, `match` raises an error with the value.
//!
//! The patterns:
//! - `_` matches any value. An identifier matches any value and binds it. An identifier that is already
//!   bound in the pattern matches a value that is `equal?` to its binding.
//! - A number, string, character, boolean, keyword, `()`, `'datum` or vector literal matches
//!   a value that is `equal?` to it.
//! - `(list p ...)` matches a list with one element for each `p`. `(list-rest p ... rest)` and `(cons p rest)` match a pair chain
//!   whose remaining tail matches `rest`. The last pattern of a list can be followed by `...`. It then matches
//!   each remaining element of the list, and each of its variables is bound to the list of its matches.
//! - `(vector p ...)` matches a vector with one element for each `p`.
//! - `(name p ...)`, where `name` is the name of a struct, matches an instance of that struct type or of a subtype. There is one
//!   `p` for each field, for all fields, the supertype's first. One `p` can be followed by `...`.
//!   That `p` is matched against each field that the other patterns do not take, and each of its
//!   variables is bound to a list. `(user name _ ...)` examines the first field only, and
//!   `(point3 x rest ...)` binds `rest` to the list of the other two fields.
//! - `(? pred p ...)` matches a value for which `pred` returns true and which each `p` matches. `(and p ...)` matches a value that each `p`
//!   matches. `(or p ...)` matches a value that any `p` matches, and each `p` must bind the same variables. `(not p ...)` matches a value that
//!   no `p` matches, and binds nothing.
//! - `(app f p)` matches a value `x` if `p` matches `(f x)`. `(== v)` matches a value that is `equal?` to `v`.
//!   `(== v same?)` matches a value `x` for which `(same? v x)` is true.
//!
//! `match` rewrites its use into simpler syntax in one step, as the other built-in macros do. Each pattern is compiled to a list of
//! [`Step`]s, and [`Matching::emit`] turns the steps into `if` and `let` forms. A clause that fails calls a
//! procedure of no arguments that tries the next clause. The compiler turns that call into a jump. As in
//! Racket, the variables of a pattern are bound only in the body of the clause. Adjacent clauses
//! that start with the same tests and reads of the value share those steps. So
//! a part of the value can be read fewer times than the patterns suggest, which a predicate that changes the value can observe.

use std::collections::HashMap;

use ragwort_compiler::steps::{self, Step as Next};
use ragwort_types::gc::Value;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Symbol;

use crate::expand::{Aux, Expander};
use crate::scope::Set;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A temporary variable. Two temporaries with the same number `n` are the same variable.
#[derive(Clone, Copy)]
struct Temp {
    n: u32,
    stx: Stx,
}

/// A property of a temporary's value that a test without side effects checks.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Pair,
    Null,
    List,
    Vector,
    Length(usize),
    /// An instance of the struct type at this index in `Matcher::structs`.
    Struct(usize),
}

/// A component of a value: the car or cdr of a pair, an element of a vector, or a field of a struct. `Field(of, index)` is field `index` of the struct type at index `of` in `Matcher::structs`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Part {
    Car,
    Cdr,
    Item(usize),
    Field(usize, usize),
}

/// A sub-pattern of a struct pattern, and the fields it is matched against: `count` fields
/// starting at field `first`. `count` is 1, except for a sub-pattern followed by `...`, which gets the fields that the other sub-patterns leave.
#[derive(Clone, Copy)]
struct FieldPat {
    pat: Stx,
    first: usize,
    count: usize,
    repeats: bool,
}

/// A struct type that a pattern names: an expression for the type, and the type's value, which identifies it.
struct Named<'gc> {
    kind: Stx,
    key: Value<'gc>,
}

/// One step of matching a pattern. The steps of a pattern run in order.
enum Step {
    /// Continues if the temporary has the shape. Otherwise the match fails.
    Is(Shape, Temp),
    /// Binds the first temporary to the given part of the second. A given part of a given temporary is always bound to the same temporary.
    Get(Temp, Part, Temp),
    /// Continues if the expression is true. Otherwise the match fails.
    Test(Stx),
    /// Binds the temporary to the value of the expression, for the steps after this one.
    Bind(Temp, Stx),
    /// Binds the pattern variable to the value of the expression, for the code after this step.
    Var(Stx, Stx),
    /// Continues if any of `alts` matches. `results` are then bound to the `values` of the alternative that matched.
    Or { alts: Vec<Vec<Step>>, values: Vec<Vec<Stx>>, results: Vec<Stx> },
    /// Continues if the steps do not match.
    Not(Vec<Step>),
    /// Continues if `list` is a list and each of its elements matches `steps`. `item` is bound to each element in turn. Each
    /// of `results` is then bound to a list that holds the value of the corresponding expression of `values` for each element.
    Each { list: Temp, item: Temp, steps: Vec<Step>, values: Vec<Stx>, results: Vec<Stx> },
}

impl Step {
    /// Returns whether this step is the same as `other` and has no side effects, so that clauses can share it.
    fn shares(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Is(shape, temp), Self::Is(other, other_temp)) => shape == other && temp.n == other_temp.n,
            (Self::Get(temp, ..), Self::Get(other_temp, ..)) => temp.n == other_temp.n,
            _ => false,
        }
    }
}

/// The body of a clause. `body` runs if `guard` is true or absent. `escape`, if present, is bound to the procedure that continues
/// with the next clause.
struct Body {
    clause: Stx,
    guard: Option<Stx>,
    escape: Option<Stx>,
    body: Vec<Stx>,
}

/// The identity of a pattern variable: its name and its scope set.
type Key<'gc> = (Symbol<'gc>, Set);

/// The state of expanding one `match` form. `at` is the form. `temps` is the number of temporaries created. `parts` maps
/// a temporary's number and a part to the temporary for that part. `seen` holds the pattern variables of the current pattern so far.
/// `structs` holds the struct types that the patterns name.
struct Matcher<'gc> {
    at: Stx,
    temps: u32,
    parts: HashMap<(u32, Part), Temp>,
    seen: Vec<Seen<'gc>>,
    structs: Vec<Named<'gc>>,
}

/// A pattern variable: its identifier, its name and scope set, and the expression for the value it is bound to.
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

// Dropping a step moves its nested steps to a work list, and the loop drops them one by one. So the native stack
// does not grow with the nesting depth of the pattern.
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

/// The expander, with the state of the `match` form being expanded. `out` is a stack of the step lists of the patterns being compiled, with the
/// innermost pattern last.
struct Matching<'e, 'a, 'gc> {
    ex: &'e mut Expander<'a, 'gc>,
    m: Matcher<'gc>,
    out: Vec<Vec<Step>>,
}

/// The next step of compiling a pattern. See [`steps`]. Each call holds a temporary and a pattern, and adds the steps that match the pattern
/// against the temporary.
type Pat<'e, 'a, 'gc> = Next<'e, Matching<'e, 'a, 'gc>, (Temp, Stx), (), ExpandError>;

/// The next step of generating the code of a `match`. Each call produces syntax.
type Em<'s, 'e, 'a, 'gc> = Next<'s, Matching<'e, 'a, 'gc>, Code<'s>, Stx, ExpandError>;

/// The remaining steps of a clause, and its body.
type Clause<'s> = (&'s [Step], &'s Body);

/// A call that generates a part of the code of a `match`.
enum Code<'s> {
    /// The arguments of [`Matching::emit`].
    Emit(&'s [Step], Stx, Stx),
    /// The arguments of [`Matching::tries`].
    Tries(Vec<Clause<'s>>, Stx),
    /// The arguments of [`Matching::match_run`].
    Run(Vec<Clause<'s>>, Stx),
}

/// The state of compiling an `or` pattern. `x` is the temporary to match. `alts` are the alternatives. `before` is `Matcher::seen` as it was before the pattern. `steps` and `bound` hold,
/// for each alternative compiled so far, its steps and the variables it binds.
struct Or<'gc> {
    x: Temp,
    alts: Vec<Stx>,
    before: Vec<Seen<'gc>>,
    steps: Vec<Vec<Step>>,
    bound: Vec<Vec<Seen<'gc>>>,
}

/// The state of generating the code of an `or` step. The alternatives are handled from the last to the first. `left` is the number still to handle, and `next` is the code
/// of the alternatives after them.
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
    /// Expands `match` to `(let ((x expr)) (let ((none (lambda () (error ...)))) clauses))`.
    /// [`Matching::tries`] generates the code of the clauses.
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
        let message = string::from_str(&Strings::new(self.ex.engine.mc), "match: no matching clause for")?.value();
        let message = self.ex.value(message, stx)?;
        let error = self.ex.build(stx, "error", &[&[message, target.stx]])?;
        let code = self.let_thunk(stx, none, error, code)?;
        self.ex.with_temp(stx, target.stx, expr, code)
    }

    /// Builds `(let ((name (lambda () body))) code)`.
    fn let_thunk(&mut self, at: Stx, name: Stx, body: Stx, code: Stx) -> Result<Stx, ExpandError> {
        let none = self.ex.list(&[], at)?;
        let lambda = self.ex.build(at, "lambda", &[&[none, body]])?;
        self.ex.with_temp(at, name, lambda, code)
    }

    fn temp(&mut self) -> Result<Temp, ExpandError> {
        self.m.temps += 1;
        Ok(Temp { n: self.m.temps, stx: self.ex.introduce(&format!("x{}", self.m.temps), self.m.at)? })
    }

    /// Returns the temporary for `part` of `target`. Each call with the same arguments returns the same temporary.
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

    /// Generates the code of `clauses`: the body of the first clause whose steps match, or `(fail)` if none does. Adjacent
    /// clauses that start with the same step without side effects form a run, and share that step. A run
    /// that fails calls a procedure that tries the clauses after the run.
    ///
    /// A run that starts with a test, such as `(point? x)`, becomes two procedures. `matched`
    /// is the rest of the run. The other procedure is only `(if test (matched) (next))`. Where the
    /// optimizer already knows the result of the test, it replaces a call of that small procedure with a call of the procedure that the test picks.
    /// So a clause that failed because the value is not a `point`
    /// skips all later `point` clauses without testing again.
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

    /// Generates the code of the remaining `runs`, starting with the last. A run that fails calls `next`. `later` holds the
    /// procedures of the runs generated so far, each with its name, starting with those of the last
    /// run. Each procedure is bound around the procedures after it in `later` and around the code of the first run.
    fn runs<'s>(&mut self, mut runs: Vec<Vec<Clause<'s>>>, mut later: Vec<(Stx, Stx)>, next: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let at = self.m.at;
        let run = runs.pop().expect("a run left");
        // The first run needs no procedure. Its code runs in place, where the `match` form is.
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
        // A run that starts with a test becomes two procedures: the test, which picks a procedure to call, and the rest of the run.
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

    /// Builds the expression that tests whether `target` has `shape`.
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

    /// Generates the code of `run`. If `run` has more than one clause, all of its clauses start with the same step.
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

    /// Parses `clause`. Returns the steps that match its pattern against `target`, and its body.
    fn clause(&mut self, target: Temp, clause: Stx) -> Result<(Vec<Step>, Body), ExpandError> {
        let parts = self.ex.proper(clause)?;
        let Some((&pattern, rest)) = parts.split_first() else { return Err(self.ex.error(ExpandErrorKind::BadSyntax, clause)) };
        let steps = self.match_pattern(target, pattern)?;
        let when_ = self.ex.symbol("when")?;
        let when = rest.first().is_some_and(|&first| self.ex.engine.tree.keyword(first).is_some_and(|keyword| keyword.symbol(self.ex.engine.mc) == when_));
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

    /// Builds the code of `body`. The code calls `fail` if the guard is false.
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

    /// Returns `id` if `stx` is `(=> id)`.
    fn escape(&mut self, stx: Stx) -> Result<Option<Stx>, ExpandError> {
        let View::List(items, None) = self.ex.engine.tree.view(stx)? else { return Ok(None) };
        Ok(match *items {
            [arrow, id] if self.ex.is_aux(arrow, Aux::Arrow)? && self.ex.is_id(id) => Some(id),
            _ => None,
        })
    }

    /// Returns the steps that match `pattern` against `target`. The steps that bind the pattern's variables come last.
    fn match_pattern(&mut self, target: Temp, pattern: Stx) -> Result<Vec<Step>, ExpandError> {
        self.out.push(Vec::new());
        steps::run(self, (target, pattern), Self::pattern)?;
        let steps = self.out.pop().expect("a pattern's steps");
        let (mut steps, vars): (Vec<_>, Vec<_>) = steps.into_iter().partition(|step| !matches!(step, Step::Var(..)));
        steps.extend(vars);
        Ok(steps)
    }

    /// Compiles `pattern`, a part of another pattern, against `target`, and passes the steps to `then`. The steps bind none of the pattern's
    /// variables. The expression for the value of each variable is in `m.seen`.
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

    /// Binds the variables of `m.seen` from index `first` on to `results`. `results` are the temporaries that hold the
    /// values of the variables once an `or` or a repeat has matched.
    fn bind_results(&mut self, first: usize, results: &[Stx]) {
        let out = self.out.last_mut().expect("a pattern's steps");
        for (seen, &result) in self.m.seen[first..].iter_mut().zip(results) {
            seen.value = result;
            out.push(Step::Var(seen.id, result));
        }
    }

    /// Adds the steps that match `pattern` against `target` to the step list being built.
    fn pattern(&mut self, (target, pattern): (Temp, Stx)) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let (items, tail) = match self.ex.engine.tree.view(pattern)? {
            View::Id if self.ex.is_aux(pattern, Aux::Underscore)? => return Ok(Next::Done(())),
            View::Id if self.ex.is_aux(pattern, Aux::Ellipsis)? => return Err(self.ex.error(ExpandErrorKind::BadSyntax, pattern)),
            View::Id => {
                self.variable(target, pattern)?;
                return Ok(Next::Done(()));
            }
            View::Datum(value) => {
                let same = if value.immediate().is_some() {
                    "eqv?"
                } else {
                    "equal?"
                };
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
        let name = match self.ex.engine.tree.symbol(items[0]) {
            Some(symbol) if tail.is_none() => string::chars(&Strings::new(self.ex.engine.mc), symbol.name(self.ex.engine.mc)).collect::<String>(),
            _ => return Err(self.ex.error(ExpandErrorKind::BadSyntax, pattern)),
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
                let Some(info) = self.ex.struct_info(items[0])? else { return Err(self.ex.error(ExpandErrorKind::BadSyntax, pattern)) };
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

    /// Matches `target` against each of `pats` from index `i` on.
    fn each_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        Ok(Next::then((target, pat), move |this: &mut Self, ()| this.each_pattern(target, pats, i + 1)))
    }

    /// Assigns fields to `pats`, the sub-patterns of the struct pattern `pattern`.
    /// `fields` is the number of fields of the struct. At most one sub-pattern can be followed by `...`. Each
    /// other sub-pattern gets exactly one field.
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
        let single = pats.len() - if dots.is_some() {
            2
        } else {
            0
        };
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
            let count = if repeats {
                spare
            } else {
                1
            };
            out.push(FieldPat { pat, first, count, repeats });
            first += count;
        }
        Ok(out)
    }

    /// Adds a step that reads field `index` of `target`, and returns the temporary that holds the field. `target` is an instance of the struct type at index `of` in `m.structs`.
    fn field(&mut self, target: Temp, of: usize, index: usize) -> Result<Temp, ExpandError> {
        let field = self.part(target, Part::Field(of, index))?;
        self.push(Step::Get(field, Part::Field(of, index), target));
        Ok(field)
    }

    /// Matches the fields of `target` against `pats` from index `i` on. `target` is an instance of the struct type at index `of` in `m.structs`.
    /// A sub-pattern followed by `...` is matched against the list of its fields, in the way the last
    /// pattern of a list is matched against the rest of the list. `_ ...` reads no field.
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

    /// Returns a `Duplicate` error if the pattern so far already binds the variable `id`. A variable that is bound to a list of
    /// matches cannot also be an equality test against an earlier binding.
    fn not_bound(&mut self, id: Stx) -> Result<(), ExpandError> {
        let key = (self.ex.engine.tree.symbol(id).expect("an identifier"), self.ex.engine.tree.scopes_of(id)?);
        if self.m.seen.iter().any(|seen| seen.key() == key) {
            return Err(self.ex.error(ExpandErrorKind::Duplicate, id));
        }
        Ok(())
    }

    /// Matches each element of the list `list` against the pattern `item`. Binds each variable of `item`
    /// to the list of its values, one for each element. Then continues with `then`.
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

    /// Matches the elements of the vector `target` from index `i` on against `pats`.
    fn vector_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        if self.ex.is_aux(pat, Aux::Ellipsis)? {
            return Err(self.ex.error(ExpandErrorKind::Unsupported, pat));
        }
        let item = self.part(target, Part::Item(i))?;
        self.push(Step::Get(item, Part::Item(i), target));
        Ok(Next::then((item, pat), move |this: &mut Self, ()| this.vector_pattern(target, pats, i + 1)))
    }

    /// Compiles the alternatives of `or` that are not compiled yet. Each alternative must bind the same variables.
    fn or_pattern(&mut self, mut or: Or<'gc>) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        if let Some(&alt) = or.alts.get(or.steps.len()) {
            self.m.seen.clone_from(&or.before);
            return self.inner_pattern(or.x, alt, move |this, steps| {
                or.steps.push(steps);
                let vars = this.m.seen[or.before.len()..].to_vec();
                // Each alternative must bind the same variables. Their order can differ.
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

    /// Adds steps that require `target` to match none of `pats` from index `i` on. The steps bind nothing.
    fn not_pattern(&mut self, target: Temp, pats: Vec<Stx>, i: usize) -> Result<Pat<'e, 'a, 'gc>, ExpandError> {
        let Some(&pat) = pats.get(i) else { return Ok(Next::Done(())) };
        let before = self.m.seen.clone();
        self.inner_pattern(target, pat, move |this, steps| {
            this.m.seen = before;
            this.push(Step::Not(steps));
            this.not_pattern(target, pats, i + 1)
        })
    }

    /// Compiles the variable pattern `id`. It matches any value and binds `id` to it. If the pattern already binds `id`, it instead matches a value that is
    /// `equal?` to that binding.
    fn variable(&mut self, target: Temp, id: Stx) -> Result<(), ExpandError> {
        let seen = Seen { id, symbol: self.ex.engine.tree.symbol(id).expect("an identifier"), set: self.ex.engine.tree.scopes_of(id)?, value: target.stx };
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

    /// Matches `at`, the remainder of a list, against `items` from index `i` on. The last item can be
    /// followed by `...`. The tail after the items is matched against `rest`. Without `rest`, the tail must be the empty list.
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
            // Only the last pattern can repeat. A repeat anywhere else would need the length of the list
            // before the list could be split.
            if i + 2 != items.len() || rest.is_some() {
                return Err(self.ex.error(ExpandErrorKind::Unsupported, next));
            }
            // An identifier followed by `...` matches each element of any list. So the identifier is bound to the list itself.
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

    /// Generates the code of `steps`. The code evaluates `done` if the steps match, and `fail` if they do not.
    fn emit<'s>(&mut self, steps: &'s [Step], done: Stx, fail: Stx) -> Result<Em<'s, 'e, 'a, 'gc>, ExpandError> {
        let Some((step, rest)) = steps.split_first() else { return Ok(Next::Done(done)) };
        let at = self.m.at;
        let rest = Code::Emit(rest, done, fail);
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
                        let index = self.ex.value(Value::fixnum(index as i64).ok_or_else(|| self.ex.error(ExpandErrorKind::BadSyntax, at))?, at)?;
                        self.ex.build(at, "vector-ref", &[&[target.stx, index]])?
                    }
                    Part::Field(of, index) => {
                        let kind = self.m.structs[of].kind;
                        let index = self.ex.value(Value::fixnum(index as i64).ok_or_else(|| self.ex.error(ExpandErrorKind::BadSyntax, at))?, at)?;
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
            // Expands to `(let ((k (lambda (result ...) rest))) alt)`. Each alternative calls `k` with its values.
            // Each alternative but the last tries the next alternative if it fails.
            Step::Or { ref alts, ref values, ref results } => {
                let join = self.temp()?.stx;
                let formals = self.ex.list(results, at)?;
                Next::then(rest, move |this: &mut Self, rest| {
                    let lambda = this.ex.build(at, "lambda", &[&[formals, rest]])?;
                    this.alternatives(Alternatives { alts, values, left: alts.len(), next: None, k: join, lambda, fail })
                })
            }
            // Expands to `(let loop ((xs list) (acc '()) ...) (if (null? xs) (let ((result (reverse acc)) ...)
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
                            let empty = this.ex.value(Value::NULL, at)?;
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

    /// Generates the code of the remaining alternatives of an `or` step. Each alternative calls `k` with its values.
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
