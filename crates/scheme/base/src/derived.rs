//! The built-in macros, written in Rust. They implement the derived expression types of R7RS. Each macro rewrites a use into
//! simpler syntax in one step, and the expander then expands the result. The identifiers that a macro introduces refer to the base
//! bindings, which the macro's input cannot shadow. The scope that the expander flips on each step keeps
//! the temporaries that a macro binds apart from the variables of its input.

use ragwort_compiler::steps::{self, Step};
use ragwort_types::gc::Value;

use crate::expand::{Aux, Binding, Expander, Keyword, Macro};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// The kind of a tagged form inside a quasiquoted template: `unquote`, `unquote-splicing` or a nested `quasiquote`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Tag {
    Unquote,
    UnquoteSplicing,
    Quasiquote,
}

/// The next step of building a quasiquoted template. See [`steps`]. Each call holds a template and
/// its quasiquote nesting depth, and produces the result of [`Expander::quasi`].
type Quasi<'a, 'gc> = Step<'a, Expander<'a, 'gc>, (Stx, usize), Option<Stx>, ExpandError>;

/// The state of building a quasiquoted list at nesting `depth`. `built` holds a [`Part`] for each item
/// processed so far. `any` records whether any of them is not constant.
struct Built {
    template: Stx,
    depth: usize,
    items: Vec<Stx>,
    tail: Option<Stx>,
    built: Vec<Part>,
    any: bool,
}

/// The result of building one item of a quasiquoted list.
#[derive(Clone, Copy)]
enum Part {
    /// The item has nothing unquoted, so it is quoted as it is.
    Constant,
    /// The expression that builds the item.
    Built(Stx),
    /// The operand of an `unquote-splicing`, whose elements are spliced in.
    Spliced(Stx),
}

impl<'a, 'gc> Expander<'a, 'gc> {
    pub(crate) fn derived(&mut self, kind: Macro, stx: Stx) -> Result<Stx, ExpandError> {
        let items = self.proper(stx)?;
        let args = &items[1..];
        match (kind, args) {
            (Macro::LetStar, &[binds, ref body @ ..]) if !body.is_empty() => {
                let binds = self.proper(binds)?;
                match binds.split_first() {
                    None => {
                        let none = self.list(&[], stx)?;
                        self.build(stx, "let", &[&[none], body])
                    }
                    Some((&first, rest)) => {
                        let rest = self.list(rest, stx)?;
                        let inner = self.build(stx, "let*", &[&[rest], body])?;
                        let first = self.list(&[first], stx)?;
                        self.build(stx, "let", &[&[first, inner]])
                    }
                }
            }
            (Macro::LetValues | Macro::LetStarValues, &[binds, ref body @ ..]) if !body.is_empty() => self.let_values(stx, kind == Macro::LetStarValues, binds, body),
            (Macro::DefineValues, &[formals, init]) => self.define_values(stx, formals, init),
            (Macro::And, []) => self.value(Value::TRUE, stx),
            (Macro::And | Macro::Or, &[expr]) => Ok(expr),
            // `and` returns the first false value itself, which can be `#f`, `#nil` or `#none`. So the value is kept in a temporary, as `or` keeps its first true value.
            (Macro::And, &[expr, ref rest @ ..]) => {
                let temp = self.introduce("t", stx)?;
                let rest = self.build(stx, "and", &[rest])?;
                let test = self.build(stx, "if", &[&[temp, rest, temp]])?;
                self.with_temp(stx, temp, expr, test)
            }
            (Macro::Or, []) => self.value(Value::FALSE, stx),
            (Macro::Or, &[expr, ref rest @ ..]) => {
                let temp = self.introduce("t", stx)?;
                let rest = self.build(stx, "or", &[rest])?;
                let test = self.build(stx, "if", &[&[temp, temp, rest]])?;
                self.with_temp(stx, temp, expr, test)
            }
            (Macro::When, &[test, ref body @ ..]) if !body.is_empty() => {
                let body = self.build(stx, "begin", &[body])?;
                self.build(stx, "if", &[&[test, body]])
            }
            (Macro::Unless, &[test, ref body @ ..]) if !body.is_empty() => {
                let body = self.build(stx, "begin", &[body])?;
                let void = self.value(Value::VOID, stx)?;
                self.build(stx, "if", &[&[test, void, body]])
            }
            (Macro::Cond, clauses) => self.cond(stx, clauses),
            (Macro::Case, &[key, ref clauses @ ..]) => self.case(stx, key, clauses),
            (Macro::Do, &[specs, end, ref commands @ ..]) => self.do_loop(stx, specs, end, commands),
            (Macro::Guard, &[spec, ref body @ ..]) if !body.is_empty() => self.guard(stx, spec, body),
            (Macro::SyntaxRules, &[literals, ref rules @ ..]) if !self.is_id(literals) => self.syntax_rules(stx, literals, rules),
            // An identifier before the literals list names a custom ellipsis, which is not supported yet.
            (Macro::SyntaxRules, &[ellipsis, ..]) => Err(self.error(ExpandErrorKind::Unsupported, ellipsis)),
            // Expands to `(syntax-case (list e ...) () ((pattern ...) (let () body ...)))`.
            (Macro::WithSyntax, &[binds, ref body @ ..]) if !body.is_empty() => {
                let (mut patterns, mut exprs) = (Vec::new(), Vec::new());
                for bind in self.proper(binds)? {
                    let &[pattern, expr] = self.proper(bind)?.as_slice() else { return Err(self.error(ExpandErrorKind::BadSyntax, bind)) };
                    patterns.push(pattern);
                    exprs.push(expr);
                }
                let (patterns, exprs) = (self.list(&patterns, stx)?, self.build(stx, "list", &[&exprs])?);
                let none = self.list(&[], stx)?;
                let body = self.build(stx, "let", &[&[none], body])?;
                let clause = self.list(&[patterns, body], stx)?;
                self.build(stx, "syntax-case", &[&[exprs, none, clause]])
            }
            // Expands to `(call-with-mark key value (lambda () body))`. As in Racket, the body is in tail
            // position. So a `with-continuation-mark` in tail position replaces the mark of its frame.
            (Macro::WithMark, &[key, value, body]) => {
                let none = self.list(&[], stx)?;
                let thunk = self.build(stx, "lambda", &[&[none, body]])?;
                self.build(stx, "call-with-mark", &[&[key, value, thunk]])
            }
            (Macro::Quasiquote, &[template]) => match steps::run(self, (template, 0), Self::quasi)? {
                Some(built) => Ok(built),
                None => self.quoted(template, stx),
            },
            (Macro::Match, &[expr, ref clauses @ ..]) => self.match_form(stx, expr, clauses),
            (Macro::StructCopy, &[name, expr, ref updates @ ..]) => self.struct_copy(stx, name, expr, updates),
            (Macro::NamedLet, &[name, binds, ref body @ ..]) => {
                let (vars, inits) = self.bindings_of(binds)?;
                let formals = self.list(&vars, stx)?;
                let lambda = self.build(stx, "lambda", &[&[formals], body])?;
                let bind = self.list(&[name, lambda], stx)?;
                let binds = self.list(&[bind], stx)?;
                let letrec = self.build(stx, "letrec", &[&[binds, name]])?;
                self.list(&[&[letrec], inits.as_slice()].concat(), stx)
            }
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    /// Builds `(name part ...)` with the span of `at`. `name` becomes an introduced identifier. The parts are the slices of `parts`, concatenated in order.
    pub(crate) fn build(&mut self, at: Stx, name: &str, parts: &[&[Stx]]) -> Result<Stx, ExpandError> {
        let head = self.introduce(name, at)?;
        self.list(&[&[head], parts.concat().as_slice()].concat(), at)
    }

    pub(crate) fn list(&mut self, items: &[Stx], at: Stx) -> Result<Stx, ExpandError> {
        let span = self.engine.tree.span(at);
        Ok(self.engine.tree.list(items, None, span)?)
    }

    pub(crate) fn value(&mut self, value: Value<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        let span = self.engine.tree.span(at);
        Ok(self.engine.tree.datum(value, span)?)
    }

    pub(crate) fn quoted(&mut self, datum: Stx, at: Stx) -> Result<Stx, ExpandError> {
        self.build(at, "quote", &[&[datum]])
    }

    /// Builds `(let ((temp value)) body)`.
    pub(crate) fn with_temp(&mut self, at: Stx, temp: Stx, value: Stx, body: Stx) -> Result<Stx, ExpandError> {
        let bind = self.list(&[temp, value], at)?;
        let binds = self.list(&[bind], at)?;
        self.build(at, "let", &[&[binds, body]])
    }

    /// Builds `(call-with-values (lambda () init) (lambda formals body ...))`.
    fn receiving(&mut self, at: Stx, formals: Stx, init: Stx, body: &[Stx]) -> Result<Stx, ExpandError> {
        let none = self.list(&[], at)?;
        let producer = self.build(at, "lambda", &[&[none, init]])?;
        let consumer = self.build(at, "lambda", &[&[formals], body])?;
        self.build(at, "call-with-values", &[&[producer, consumer]])
    }

    /// Returns formals of the same shape as `formals` with a temporary in place of each variable, and
    /// the list of each variable with its temporary. `prefix` is part of each temporary's name. It keeps the temporaries of one clause distinct from
    /// those of another clause.
    fn temporaries(&mut self, formals: Stx, prefix: usize) -> Result<(Stx, Vec<(Stx, Stx)>), ExpandError> {
        let (vars, tail) = match self.engine.tree.view(formals)? {
            View::Id => (Vec::new(), Some(formals)),
            View::List(vars, tail) => (vars, tail),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, formals)),
        };
        let mut pairs = Vec::with_capacity(vars.len() + 1);
        for (position, &var) in vars.iter().chain(&tail).enumerate() {
            if !self.is_id(var) {
                return Err(self.error(ExpandErrorKind::BadSyntax, var));
            }
            pairs.push((var, self.introduce(&format!("t{prefix}-{position}"), var)?));
        }
        let temps: Vec<Stx> = pairs.iter().map(|&(_, temp)| temp).collect();
        let span = self.engine.tree.span(formals);
        let shaped = match (tail, temps.split_last()) {
            (Some(_), Some((&last, []))) if vars.is_empty() => last,
            (Some(_), Some((&last, before))) => self.engine.tree.list(before, Some(last), span)?,
            _ => self.engine.tree.list(&temps, None, span)?,
        };
        Ok((shaped, pairs))
    }

    /// Expands `let-values` and `let*-values`. Each clause becomes a `call-with-values` whose consumer takes
    /// the clause's formals.
    ///
    /// The clauses of `let*-values` nest, so each sees the variables before it. The inits of
    /// `let-values` see none of its variables, so with several clauses the consumers take
    /// temporaries and a `let` innermost binds the variables.
    fn let_values(&mut self, stx: Stx, sequential: bool, binds: Stx, body: &[Stx]) -> Result<Stx, ExpandError> {
        let mut clauses = Vec::new();
        for bind in self.proper(binds)? {
            let &[formals, init] = self.proper(bind)?.as_slice() else { return Err(self.error(ExpandErrorKind::BadSyntax, bind)) };
            clauses.push((formals, init));
        }
        let none = self.list(&[], stx)?;
        match *clauses.as_slice() {
            [] => self.build(stx, "let", &[&[none], body]),
            [(formals, init)] => self.receiving(stx, formals, init, body),
            [(formals, init), ..] if sequential => {
                let mut rest = Vec::with_capacity(clauses.len() - 1);
                for &(formals, init) in &clauses[1..] {
                    rest.push(self.list(&[formals, init], stx)?);
                }
                let rest = self.list(&rest, stx)?;
                let inner = self.build(stx, "let*-values", &[&[rest], body])?;
                self.receiving(stx, formals, init, &[inner])
            }
            _ => {
                let (mut shaped, mut binds) = (Vec::with_capacity(clauses.len()), Vec::new());
                for (prefix, &(formals, _)) in clauses.iter().enumerate() {
                    let (formals, pairs) = self.temporaries(formals, prefix)?;
                    shaped.push(formals);
                    for (var, temp) in pairs {
                        binds.push(self.list(&[var, temp], stx)?);
                    }
                }
                let binds = self.list(&binds, stx)?;
                let mut inner = self.build(stx, "let", &[&[binds], body])?;
                for (&formals, &(_, init)) in shaped.iter().zip(&clauses).rev() {
                    inner = self.receiving(stx, formals, init, &[inner])?;
                }
                Ok(inner)
            }
        }
    }

    /// Expands `define-values` to `(begin (define var (void)) ... (call-with-values (lambda () init) (lambda temps (set! var temp) ... (void))))`.
    fn define_values(&mut self, stx: Stx, formals: Stx, init: Stx) -> Result<Stx, ExpandError> {
        let (shaped, pairs) = self.temporaries(formals, 0)?;
        let void = self.build(stx, "void", &[])?;
        let (mut forms, mut sets) = (Vec::with_capacity(pairs.len() + 1), Vec::with_capacity(pairs.len() + 1));
        for (var, temp) in pairs {
            forms.push(self.build(stx, "define", &[&[var, void]])?);
            sets.push(self.build(stx, "set!", &[&[var, temp]])?);
        }
        sets.push(void);
        forms.push(self.receiving(stx, shaped, init, &sets)?);
        self.build(stx, "begin", &[&forms])
    }

    /// Returns the variables and the init expressions of `((var init) ...)`.
    fn bindings_of(&mut self, binds: Stx) -> Result<(Vec<Stx>, Vec<Stx>), ExpandError> {
        let mut vars = Vec::new();
        let mut inits = Vec::new();
        for bind in self.proper(binds)? {
            match *self.proper(bind)?.as_slice() {
                [var, init] if self.is_id(var) => {
                    vars.push(var);
                    inits.push(init);
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, bind)),
            }
        }
        Ok((vars, inits))
    }

    /// Expands `cond` one clause at a time: a test of the first clause, with a `cond` of the remaining clauses as the alternative.
    fn cond(&mut self, stx: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let Some((&clause, rest)) = clauses.split_first() else { return self.value(Value::VOID, stx) };
        let parts = self.proper(clause)?;
        let Some((&test, body)) = parts.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, clause)) };
        if self.is_aux(test, Aux::Else)? {
            if !rest.is_empty() || body.is_empty() {
                return Err(self.error(ExpandErrorKind::BadSyntax, clause));
            }
            return self.build(clause, "begin", &[body]);
        }
        let more = self.build(stx, "cond", &[rest])?;
        match *body {
            [] => self.build(clause, "or", &[&[test, more]]),
            [arrow, receiver] if self.is_aux(arrow, Aux::Arrow)? => {
                let temp = self.introduce("t", clause)?;
                let call = self.list(&[receiver, temp], clause)?;
                let test_t = self.build(clause, "if", &[&[temp, call, more]])?;
                self.with_temp(clause, temp, test, test_t)
            }
            [first, ..] if self.is_aux(first, Aux::Arrow)? => Err(self.error(ExpandErrorKind::BadSyntax, clause)),
            _ => {
                let body = self.build(clause, "begin", &[body])?;
                self.build(clause, "if", &[&[test, body, more]])
            }
        }
    }

    /// Expands `syntax-rules` to `(lambda (x) (syntax-case x (literal ...) ((_ . pattern) (syntax template)) ...))`, for
    /// rules of the form `((keyword . pattern) template)`. The keyword of a rule is not matched.
    fn syntax_rules(&mut self, stx: Stx, literals: Stx, rules: &[Stx]) -> Result<Stx, ExpandError> {
        let input = self.introduce("x", stx)?;
        let mut clauses = Vec::with_capacity(rules.len());
        for &rule in rules {
            let &[pattern, template] = self.proper(rule)?.as_slice() else { return Err(self.error(ExpandErrorKind::BadSyntax, rule)) };
            let View::List(items, tail) = self.engine.tree.view(pattern)? else { return Err(self.error(ExpandErrorKind::BadSyntax, pattern)) };
            if items.is_empty() {
                return Err(self.error(ExpandErrorKind::BadSyntax, pattern));
            }
            let any = self.introduce("_", pattern)?;
            let span = self.engine.tree.span(pattern);
            let pattern = self.engine.tree.list(&[&[any], &items[1..]].concat(), tail, span)?;
            let template = self.build(rule, "syntax", &[&[template]])?;
            clauses.push(self.list(&[pattern, template], rule)?);
        }
        let case = self.build(stx, "syntax-case", &[&[input, literals], &clauses])?;
        let formals = self.list(&[input], stx)?;
        self.build(stx, "lambda", &[&[formals, case]])
    }

    /// Expands `guard` to `(%guard (lambda () body ...) (lambda (var) (cond clause ... (else (raise-continuable
    /// var)))))`. The `else` clause is added only if the clauses have none. The prelude's `%guard` calls the
    /// handler after it has left the body, so the clauses run in the context of the `guard` form.
    ///
    /// `(guard (var #:no-traceback clause ...) body ...)` expands to `%guard/no-traceback` instead, so a condition this guard catches records no call trace when it is raised.
    fn guard(&mut self, stx: Stx, spec: Stx, body: &[Stx]) -> Result<Stx, ExpandError> {
        let parts = self.proper(spec)?;
        let Some((&var, clauses)) = parts.split_first().filter(|(var, _)| self.is_id(**var)) else {
            return Err(self.error(ExpandErrorKind::BadSyntax, spec));
        };
        let quiet = clauses.first().is_some_and(|&option| self.keyword_name(option).as_deref() == Some("no-traceback"));
        let mut clauses = if quiet {
            clauses[1..].to_vec()
        } else {
            clauses.to_vec()
        };
        let has_else = match clauses.last() {
            Some(&last) => match self.proper(last)?.first() {
                Some(&head) => self.is_aux(head, Aux::Else)?,
                None => false,
            },
            None => false,
        };
        if !has_else {
            let otherwise = self.introduce("else", stx)?;
            let again = self.build(stx, "raise-continuable", &[&[var]])?;
            clauses.push(self.list(&[otherwise, again], stx)?);
        }
        let none = self.list(&[], stx)?;
        let thunk = self.build(stx, "lambda", &[&[none], body])?;
        let cond = self.build(stx, "cond", &[&clauses])?;
        let formals = self.list(&[var], stx)?;
        let handler = self.build(stx, "lambda", &[&[formals, cond]])?;
        let guard = if quiet {
            "%guard/no-traceback"
        } else {
            "%guard"
        };
        self.build(stx, guard, &[&[thunk, handler]])
    }

    /// Expands `case` to `(let ((t key)) (cond ((memv t '(datum ...)) body ...) ...))`. A clause body `=> f` becomes `(f t)`.
    fn case(&mut self, stx: Stx, key: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let temp = self.introduce("t", stx)?;
        let mut tests = Vec::with_capacity(clauses.len());
        for &clause in clauses {
            let parts = self.proper(clause)?;
            let Some((&data, body)) = parts.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, clause)) };
            let body = match *body {
                [] => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
                [arrow, receiver] if self.is_aux(arrow, Aux::Arrow)? => vec![self.list(&[receiver, temp], clause)?],
                _ => body.to_vec(),
            };
            let test = if self.is_aux(data, Aux::Else)? {
                data
            } else {
                self.proper(data)?;
                let quoted = self.quoted(data, clause)?;
                self.build(clause, "memv", &[&[temp, quoted]])?
            };
            tests.push(self.list(&[&[test], body.as_slice()].concat(), clause)?);
        }
        let cond = self.build(stx, "cond", &[&tests])?;
        self.with_temp(stx, temp, key, cond)
    }

    /// Expands `do` to `(let loop ((var init) ...) (if test (begin void result ...) (begin command ... (loop
    /// step ...))))`. A variable without a step expression is passed to the next iteration unchanged.
    fn do_loop(&mut self, stx: Stx, specs: Stx, end: Stx, commands: &[Stx]) -> Result<Stx, ExpandError> {
        let mut binds = Vec::new();
        let mut steps = Vec::new();
        for spec in self.proper(specs)? {
            match *self.proper(spec)?.as_slice() {
                [var, init] if self.is_id(var) => {
                    binds.push(self.list(&[var, init], spec)?);
                    steps.push(var);
                }
                [var, init, step] if self.is_id(var) => {
                    binds.push(self.list(&[var, init], spec)?);
                    steps.push(step);
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
            }
        }
        let end = self.proper(end)?;
        let Some((&test, results)) = end.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, stx)) };
        let name = self.introduce("loop", stx)?;
        let void = self.value(Value::VOID, stx)?;
        let done = self.build(stx, "begin", &[&[void], results])?;
        let again = self.list(&[&[name], steps.as_slice()].concat(), stx)?;
        let more = self.build(stx, "begin", &[commands, &[again]])?;
        let body = self.build(stx, "if", &[&[test, done, more]])?;
        let binds = self.list(&binds, stx)?;
        self.build(stx, "let", &[&[name, binds, body]])
    }

    /// Returns the tag and the operand `x` if `items` are `(unquote x)`, `(unquote-splicing x)` or `(quasiquote x)`.
    fn tag(&mut self, items: &[Stx]) -> Result<Option<(Tag, Stx)>, ExpandError> {
        let &[head, operand] = items else { return Ok(None) };
        if !self.is_id(head) {
            return Ok(None);
        }
        Ok(match self.resolve(head)? {
            Binding::Keyword(Keyword::Aux(Aux::Unquote)) => Some((Tag::Unquote, operand)),
            Binding::Keyword(Keyword::Aux(Aux::UnquoteSplicing)) => Some((Tag::UnquoteSplicing, operand)),
            Binding::Keyword(Keyword::Macro(Macro::Quasiquote)) => Some((Tag::Quasiquote, operand)),
            _ => None,
        })
    }

    /// Returns an expression that builds `template` at quasiquote nesting `depth`. Returns `None` if `template` has
    /// nothing unquoted, in which case it can be quoted as it is.
    fn quasi(&mut self, (template, depth): (Stx, usize)) -> Result<Quasi<'a, 'gc>, ExpandError> {
        match self.engine.tree.view(template)? {
            View::List(items, tail) => {
                if tail.is_none()
                    && let Some((tag, operand)) = self.tag(&items)?
                {
                    let depth = match (tag, depth) {
                        (Tag::Unquote, 0) => return Ok(Step::Done(Some(operand))),
                        (Tag::UnquoteSplicing, 0) => return Err(self.error(ExpandErrorKind::BadSyntax, template)),
                        (Tag::Unquote | Tag::UnquoteSplicing, depth) => depth - 1,
                        (Tag::Quasiquote, depth) => depth + 1,
                    };
                    let name = items[0];
                    return Ok(Step::then((operand, depth), move |this: &mut Self, built| {
                        let Some(built) = built else { return Ok(Step::Done(None)) };
                        let name = this.quoted(name, template)?;
                        Ok(Step::Done(Some(this.build(template, "list", &[&[name, built]])?)))
                    }));
                }
                // `(a . ,b)` reads as `(a unquote b)`.
                let (items, tail) = match items.len() {
                    3.. if tail.is_none() && self.tag(&items[items.len() - 2..])?.is_some() => {
                        let split = items.len() - 2;
                        (items[..split].to_vec(), Some(self.list(&items[split..], template)?))
                    }
                    _ => (items, tail),
                };
                let built = Vec::with_capacity(items.len());
                self.quasi_items(Built { template, depth, items, tail, built, any: false })
            }
            View::Vector(items) => self.quasi_vector(template, depth, items, 0),
            _ => Ok(Step::Done(None)),
        }
    }

    /// Builds the remaining items of a quasiquoted list, then its tail.
    fn quasi_items(&mut self, mut list: Built) -> Result<Quasi<'a, 'gc>, ExpandError> {
        while let Some(&item) = list.items.get(list.built.len()) {
            let spliced = match self.engine.tree.view(item)? {
                View::List(parts, None) if list.depth == 0 => match self.tag(&parts)? {
                    Some((Tag::UnquoteSplicing, operand)) => Some(operand),
                    _ => None,
                },
                _ => None,
            };
            let Some(spliced) = spliced else {
                return Ok(Step::then((item, list.depth), move |this: &mut Self, part: Option<Stx>| {
                    list.any |= part.is_some();
                    list.built.push(part.map_or(Part::Constant, Part::Built));
                    this.quasi_items(list)
                }));
            };
            list.any = true;
            list.built.push(Part::Spliced(spliced));
        }
        match list.tail {
            Some(tail) => Ok(Step::then((tail, list.depth), move |this: &mut Self, rest: Option<Stx>| this.quasi_list(list, rest.ok_or(tail)))),
            None => {
                let empty = self.list(&[], list.template)?;
                self.quasi_list(list, Err(empty))
            }
        }
    }

    /// Finishes a quasiquoted list whose items are built. `rest` is the tail: `Ok` holds the expression that builds it, and `Err` holds a constant tail.
    fn quasi_list(&mut self, list: Built, rest: Result<Stx, Stx>) -> Result<Quasi<'a, 'gc>, ExpandError> {
        let Built { template, items, built, any, .. } = list;
        if !any && rest.is_err() {
            return Ok(Step::Done(None));
        }
        let mut acc = match rest {
            Ok(built) => built,
            Err(constant) => self.quoted(constant, template)?,
        };
        for (part, &item) in built.into_iter().zip(&items).rev() {
            acc = match part {
                Part::Spliced(spliced) => self.build(template, "append", &[&[spliced, acc]])?,
                Part::Built(built) => self.build(template, "cons", &[&[built, acc]])?,
                Part::Constant => {
                    let head = self.quoted(item, item)?;
                    self.build(template, "cons", &[&[head, acc]])?
                }
            };
        }
        Ok(Step::Done(Some(acc)))
    }

    /// Checks that the items of a quasiquoted vector from index `i` on have nothing unquoted. An unquote inside a vector is not
    /// supported.
    fn quasi_vector(&mut self, template: Stx, depth: usize, items: Vec<Stx>, i: usize) -> Result<Quasi<'a, 'gc>, ExpandError> {
        let Some(&item) = items.get(i) else { return Ok(Step::Done(None)) };
        let spliced = match self.engine.tree.view(item)? {
            View::List(parts, None) => self.tag(&parts)?.is_some_and(|(tag, _)| tag == Tag::UnquoteSplicing),
            _ => false,
        };
        if spliced {
            return Err(self.error(ExpandErrorKind::Unsupported, template));
        }
        Ok(Step::then((item, depth), move |this: &mut Self, part: Option<Stx>| {
            if part.is_some() {
                return Err(this.error(ExpandErrorKind::Unsupported, template));
            }
            this.quasi_vector(template, depth, items, i + 1)
        }))
    }
}
