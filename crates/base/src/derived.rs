//! The macros written in Rust: R7RS's derived expression types, each a step from a use to
//! simpler syntax, which the expander then expands in turn. What they introduce names the base
//! bindings, which the code they're given can't shadow, and the expander's flipped scope keeps
//! the temporaries they bind apart from the code's own.

use ragwort_types::gc::Value;

use crate::expand::{Aux, Binding, Expander, Keyword, Macro};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// What a quasiquoted part is, if it's an unquote of some kind.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Tag {
    Unquote,
    UnquoteSplicing,
    Quasiquote,
}

impl<'gc> Expander<'_, 'gc> {
    pub(crate) fn derived(&mut self, m: Macro, stx: Stx) -> Result<Stx, ExpandError> {
        let items = self.proper(stx)?;
        let args = &items[1..];
        let bad = |this: &Self| Err(this.error(ExpandErrorKind::BadSyntax, stx));
        match (m, args) {
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
            (Macro::And, []) => self.value(Value::TRUE, stx),
            (Macro::And | Macro::Or, &[e]) => Ok(e),
            (Macro::And, &[e, ref rest @ ..]) => {
                let rest = self.build(stx, "and", &[rest])?;
                let no = self.value(Value::FALSE, stx)?;
                self.build(stx, "if", &[&[e, rest, no]])
            }
            (Macro::Or, []) => self.value(Value::FALSE, stx),
            (Macro::Or, &[e, ref rest @ ..]) => {
                let t = self.introduce("t", stx)?;
                let rest = self.build(stx, "or", &[rest])?;
                let test = self.build(stx, "if", &[&[t, t, rest]])?;
                self.with_temp(stx, t, e, test)
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
            (Macro::Quasiquote, &[template]) => match self.quasi(template, 0)? {
                Some(built) => Ok(built),
                None => self.quoted(template, stx),
            },
            (Macro::NamedLet, &[name, binds, ref body @ ..]) => {
                let (vars, inits) = self.bindings_of(binds)?;
                let formals = self.list(&vars, stx)?;
                let lambda = self.build(stx, "lambda", &[&[formals], body])?;
                let bind = self.list(&[name, lambda], stx)?;
                let binds = self.list(&[bind], stx)?;
                let letrec = self.build(stx, "letrec", &[&[binds, name]])?;
                self.list(&[&[letrec], inits.as_slice()].concat(), stx)
            }
            _ => bad(self),
        }
    }

    /// `(name part ...)`, `name` introduced, with the parts of each of `parts` in order.
    fn build(&mut self, at: Stx, name: &str, parts: &[&[Stx]]) -> Result<Stx, ExpandError> {
        let head = self.introduce(name, at)?;
        self.list(&[&[head], parts.concat().as_slice()].concat(), at)
    }

    fn list(&mut self, items: &[Stx], at: Stx) -> Result<Stx, ExpandError> {
        let span = self.tree.span(at);
        Ok(self.tree.list(items, None, span)?)
    }

    fn value(&mut self, value: Value<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        let span = self.tree.span(at);
        Ok(self.tree.datum(value, span)?)
    }

    fn quoted(&mut self, datum: Stx, at: Stx) -> Result<Stx, ExpandError> {
        self.build(at, "quote", &[&[datum]])
    }

    /// `(let ((t value)) body)`.
    fn with_temp(&mut self, at: Stx, t: Stx, value: Stx, body: Stx) -> Result<Stx, ExpandError> {
        let bind = self.list(&[t, value], at)?;
        let binds = self.list(&[bind], at)?;
        self.build(at, "let", &[&[binds, body]])
    }

    /// The variables and inits of `((var init) ...)`.
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

    /// The first clause tested, and a `cond` of the rest if it fails.
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
            [arrow, f] if self.is_aux(arrow, Aux::Arrow)? => {
                let t = self.introduce("t", clause)?;
                let call = self.list(&[f, t], clause)?;
                let test_t = self.build(clause, "if", &[&[t, call, more]])?;
                self.with_temp(clause, t, test, test_t)
            }
            [first, ..] if self.is_aux(first, Aux::Arrow)? => Err(self.error(ExpandErrorKind::BadSyntax, clause)),
            _ => {
                let body = self.build(clause, "begin", &[body])?;
                self.build(clause, "if", &[&[test, body, more]])
            }
        }
    }

    /// `(let ((t key)) (cond ((memv t '(datum ...)) body ...) ...))`, with `=> f` as `(f t)`.
    fn case(&mut self, stx: Stx, key: Stx, clauses: &[Stx]) -> Result<Stx, ExpandError> {
        let t = self.introduce("t", stx)?;
        let mut tests = Vec::with_capacity(clauses.len());
        for &clause in clauses {
            let parts = self.proper(clause)?;
            let Some((&data, body)) = parts.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, clause)) };
            let body = match *body {
                [] => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
                [arrow, f] if self.is_aux(arrow, Aux::Arrow)? => vec![self.list(&[f, t], clause)?],
                _ => body.to_vec(),
            };
            let test = if self.is_aux(data, Aux::Else)? {
                data
            } else {
                self.proper(data)?;
                let quoted = self.quoted(data, clause)?;
                self.build(clause, "memv", &[&[t, quoted]])?
            };
            tests.push(self.list(&[&[test], body.as_slice()].concat(), clause)?);
        }
        let cond = self.build(stx, "cond", &[&tests])?;
        self.with_temp(stx, t, key, cond)
    }

    /// `(let loop ((var init) ...) (if test (begin void result ...) (begin command ... (loop
    /// step ...))))`, a step being the variable itself where there's none.
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

    /// The `(unquote x)`, `(unquote-splicing x)` or `(quasiquote x)` that `items` are, if so.
    fn tag(&mut self, items: &[Stx]) -> Result<Option<(Tag, Stx)>, ExpandError> {
        let &[head, x] = items else { return Ok(None) };
        if !self.is_id(head) {
            return Ok(None);
        }
        Ok(match self.resolve(head)? {
            Binding::Keyword(Keyword::Aux(Aux::Unquote)) => Some((Tag::Unquote, x)),
            Binding::Keyword(Keyword::Aux(Aux::UnquoteSplicing)) => Some((Tag::UnquoteSplicing, x)),
            Binding::Keyword(Keyword::Macro(Macro::Quasiquote)) => Some((Tag::Quasiquote, x)),
            _ => None,
        })
    }

    /// An expression that builds `template` at quasiquote nesting `depth`, or `None` if it has
    /// nothing unquoted and can be quoted as it is.
    fn quasi(&mut self, template: Stx, depth: usize) -> Result<Option<Stx>, ExpandError> {
        match self.tree.view(template)? {
            View::List(items, tail) => {
                if tail.is_none()
                    && let Some((tag, x)) = self.tag(&items)?
                {
                    let depth = match (tag, depth) {
                        (Tag::Unquote, 0) => return Ok(Some(x)),
                        (Tag::UnquoteSplicing, 0) => return Err(self.error(ExpandErrorKind::BadSyntax, template)),
                        (Tag::Unquote | Tag::UnquoteSplicing, d) => d - 1,
                        (Tag::Quasiquote, d) => d + 1,
                    };
                    let Some(x) = self.quasi(x, depth)? else { return Ok(None) };
                    let name = self.quoted(items[0], template)?;
                    return Ok(Some(self.build(template, "list", &[&[name, x]])?));
                }
                // `(a . ,b)` reads as `(a unquote b)`.
                let (items, tail) = match items.len() {
                    3.. if tail.is_none() && self.tag(&items[items.len() - 2..])?.is_some() => {
                        let split = items.len() - 2;
                        (items[..split].to_vec(), Some(self.list(&items[split..], template)?))
                    }
                    _ => (items, tail),
                };
                let mut built = Vec::with_capacity(items.len());
                let mut any = false;
                for &item in &items {
                    let spliced = match self.tree.view(item)? {
                        View::List(parts, None) if depth == 0 => match self.tag(&parts)? {
                            Some((Tag::UnquoteSplicing, x)) => Some(x),
                            _ => None,
                        },
                        _ => None,
                    };
                    let part = match spliced {
                        Some(x) => Err(x),
                        None => Ok(self.quasi(item, depth)?),
                    };
                    any |= !matches!(part, Ok(None));
                    built.push(part);
                }
                let rest = match tail {
                    Some(tail) => self.quasi(tail, depth)?.ok_or(tail),
                    None => Err(self.list(&[], template)?),
                };
                if !any && rest.is_err() {
                    return Ok(None);
                }
                let mut acc = match rest {
                    Ok(built) => built,
                    Err(constant) => self.quoted(constant, template)?,
                };
                for (part, &item) in built.into_iter().zip(&items).rev() {
                    acc = match part {
                        Err(spliced) => self.build(template, "append", &[&[spliced, acc]])?,
                        Ok(built) => {
                            let head = match built {
                                Some(built) => built,
                                None => self.quoted(item, item)?,
                            };
                            self.build(template, "cons", &[&[head, acc]])?
                        }
                    };
                }
                Ok(Some(acc))
            }
            View::Vector(items) => {
                for item in items {
                    let spliced = match self.tree.view(item)? {
                        View::List(parts, None) => self.tag(&parts)?.is_some_and(|(tag, _)| tag == Tag::UnquoteSplicing),
                        _ => false,
                    };
                    if spliced || self.quasi(item, depth)?.is_some() {
                        return Err(self.error(ExpandErrorKind::Unsupported, template));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }
}
