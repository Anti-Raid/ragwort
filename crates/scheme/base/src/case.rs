//! `syntax-case` and `syntax`, as R6RS has them, compiled to the VM's
//! [`syntax_case`](ragwort_vm::syntax_case) patterns and templates: a clause's pattern is a
//! constant the code matches its input with, which gives a vector of what its variables matched,
//! a list of those for each ellipsis a variable's under. A template with pattern variables in it
//! is a constant too, which the code makes syntax of with theirs; one without any is the syntax
//! it's made of.

use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_types::syntax::{Syntax, SyntaxKind};
use ragwort_vm::syntax_case::{self, Item, Pattern, PatternShape, Repeat, Template, TemplateShape};
use ragwort_vm::{Intrinsic, Request};

use crate::expand::{Aux, Binding, Expander};
use crate::scope::Op;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

type Items = (Vec<Pattern>, Option<Box<Repeat>>, Vec<Pattern>);

/// The pattern variables `t` refers to, by the places they're passed in, added to `out`.
fn slots(t: &Template, out: &mut Vec<u32>) {
    match t {
        Template::Const(_) => {}
        Template::Var(slot) => {
            if !out.contains(slot) {
                out.push(*slot);
            }
        }
        Template::Seq { items, tail, .. } => {
            items.iter().for_each(|item| slots(&item.template, out));
            if let Some(tail) = tail {
                slots(tail, out);
            }
        }
    }
}

fn index(items: &[Value<'_>]) -> u32 {
    u32::try_from(items.len()).expect("fewer than 2^32 parts")
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
        let Some((&clause, rest)) = clauses.split_first() else {
            let error = Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeSyntaxError), vec![Core::Quote(Value::VOID), local(input)]);
            return Ok(Core::Intrinsic(Prim::Request(Request::Raise), vec![error]));
        };
        let (pattern, fender, output) = match *self.proper(clause)?.as_slice() {
            [pattern, output] => (pattern, None, output),
            [pattern, fender, output] => (pattern, Some(fender), output),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
        };
        let (mut vars, mut items) = (Vec::new(), Vec::new());
        let compiled = self.pattern(pattern, literals, 0, &mut vars, &mut items)?;
        let shape = PatternShape { pattern: compiled, vars: u32::try_from(vars.len()).expect("fewer than 2^32 variables") };
        let pattern = Core::Quote(syntax_case::pattern(self.mc, shape, &items)?);
        let asked = Core::Intrinsic(Prim::Intrinsic(Intrinsic::SyntaxMatch), vec![pattern, local(input)]);
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
                return Ok(Core::Let(vec![(k, thunk)], Box::new(Core::Let(vec![(matched, asked)], Box::new(tried)))));
            }
        };
        let body = Core::Let(binds, Box::new(body));
        Ok(Core::Let(vec![(matched, asked)], Box::new(Core::If(Box::new(local(matched)), Box::new(body), Box::new(next)))))
    }

    /// The pattern `p`, under `depth` ellipses, adding its variables to `vars` and what it
    /// refers to to `parts`.
    fn pattern(&mut self, p: Stx, literals: &[Stx], depth: u32, vars: &mut Vec<(Stx, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<Pattern, ExpandError> {
        Ok(match self.tree.view(p)? {
            View::Id if self.is_aux(p, Aux::Underscore)? => Pattern::Any,
            View::Id if self.is_aux(p, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, p)),
            View::Id if self.is_literal(p, literals)? => {
                let at = index(parts);
                parts.push(self.wrap(p)?);
                Pattern::Literal(at)
            }
            View::Id => {
                vars.push((p, depth));
                Pattern::Var(u32::try_from(vars.len() - 1).expect("fewer than 2^32 variables"))
            }
            View::Datum(value) => {
                let at = index(parts);
                parts.push(value);
                Pattern::Datum(at)
            }
            View::List(items, tail) => {
                let (before, repeat, after) = self.items(p, &items, literals, depth, vars, parts)?;
                let tail = tail.map(|tail| self.pattern(tail, literals, depth, vars, parts).map(Box::new)).transpose()?;
                Pattern::Seq { before: before.into(), repeat, after: after.into(), tail, vector: false }
            }
            View::Vector(items) => {
                let (before, repeat, after) = self.items(p, &items, literals, depth, vars, parts)?;
                Pattern::Seq { before: before.into(), repeat, after: after.into(), tail: None, vector: true }
            }
        })
    }

    /// The items of a list or vector pattern: those before an ellipsis, the one it repeats, and
    /// those after, or all of them if there's none.
    fn items(&mut self, p: Stx, items: &[Stx], literals: &[Stx], depth: u32, vars: &mut Vec<(Stx, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<Items, ExpandError> {
        let mut dots = Vec::new();
        for (i, &item) in items.iter().enumerate() {
            if self.is_aux(item, Aux::Ellipsis)? {
                dots.push(i);
            }
        }
        let each = |this: &mut Self, items: &[Stx], vars: &mut Vec<(Stx, u32)>, parts: &mut Vec<Value<'gc>>| {
            items.iter().map(|&item| this.pattern(item, literals, depth, vars, parts)).collect::<Result<Vec<_>, _>>()
        };
        let slot = |vars: &Vec<(Stx, u32)>| u32::try_from(vars.len()).expect("fewer than 2^32 variables");
        match *dots.as_slice() {
            [] => Ok((each(self, items, vars, parts)?, None, Vec::new())),
            [i] if i > 0 => {
                let before = each(self, &items[..i - 1], vars, parts)?;
                let start = slot(vars);
                let repeated = self.pattern(items[i - 1], literals, depth + 1, vars, parts)?;
                let repeat = Repeat { each: repeated, slots: start..slot(vars) };
                Ok((before, Some(Box::new(repeat)), each(self, &items[i + 1..], vars, parts)?))
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

    /// `(syntax template)`: what `template` makes, of what the pattern variables in it matched.
    pub(crate) fn syntax(&mut self, template: Stx) -> Result<Core<'gc>, ExpandError> {
        let (mut used, mut parts) = (Vec::new(), Vec::new());
        Ok(match self.template(template, &mut used, 0, &mut false, &mut parts)? {
            Template::Const(at) => Core::Quote(parts[at as usize]),
            Template::Var(_) => local(used[0].0),
            template => {
                let shape = TemplateShape { template, depths: used.iter().map(|&(_, depth)| depth).collect() };
                let template = Core::Quote(syntax_case::template(self.mc, shape, &parts)?);
                let args = std::iter::once(template).chain(used.iter().map(|&(var, _)| local(var)));
                Core::Intrinsic(Prim::Intrinsic(Intrinsic::SyntaxBuild), args.collect())
            }
        })
    }

    /// The template `t`, under `nesting` ellipses, with the pattern variables it refers to added
    /// to `used`, unless they're there already, and the syntax it's made of to `parts`. In an
    /// `escaped` one, `...` is an identifier; `escapes` is set if `t` has `(... template)` in it.
    fn template(&mut self, t: Stx, used: &mut Vec<(Var, u32)>, nesting: u32, escapes: &mut bool, parts: &mut Vec<Value<'gc>>) -> Result<Template, ExpandError> {
        self.template_in(t, used, nesting, false, escapes, parts)
    }

    fn template_in(&mut self, t: Stx, used: &mut Vec<(Var, u32)>, nesting: u32, escaped: bool, escapes: &mut bool, parts: &mut Vec<Value<'gc>>) -> Result<Template, ExpandError> {
        let start = parts.len();
        let constant = |this: &mut Self, parts: &mut Vec<Value<'gc>>| -> Result<Template, ExpandError> {
            parts.truncate(start);
            parts.push(this.wrap(t)?);
            Ok(Template::Const(index(&parts[..start])))
        };
        let (items, tail, vector) = match self.tree.view(t)? {
            View::Id if !escaped && self.is_aux(t, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, t)),
            View::Id => {
                return match self.resolve(t)? {
                    Binding::Pattern { var, depth } => {
                        if nesting < depth {
                            return Err(self.error(ExpandErrorKind::BadSyntax, t));
                        }
                        let slot = used.iter().position(|&(v, _)| v == var).unwrap_or_else(|| {
                            used.push((var, depth));
                            used.len() - 1
                        });
                        Ok(Template::Var(u32::try_from(slot).expect("fewer than 2^32 variables")))
                    }
                    _ => constant(self, parts),
                };
            }
            View::Datum(_) => return constant(self, parts),
            View::List(items, tail) => {
                // `(... template)` is `template` with its ellipses as they are.
                if let [dots, inner] = items[..]
                    && !escaped
                    && tail.is_none()
                    && self.is_aux(dots, Aux::Ellipsis)?
                {
                    *escapes = true;
                    return self.template_in(inner, used, nesting, true, escapes, parts);
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
            let template = self.template_in(item, used, nesting + ellipses, escaped, &mut inner, parts)?;
            let mut vars = Vec::new();
            slots(&template, &mut vars);
            if ellipses > 0 && !vars.iter().any(|&slot| used[slot as usize].1 > nesting) {
                return Err(self.error(ExpandErrorKind::BadSyntax, item));
            }
            built.push(Item { template, ellipses, slots: vars.into() });
            i += 1;
        }
        let tail = tail.map(|tail| self.template_in(tail, used, nesting, escaped, &mut inner, parts).map(Box::new)).transpose()?;
        *escapes |= inner;
        // A list of constants is the syntax it's made from, unless an escape in it is dropped.
        let all_constant = built.iter().all(|item| matches!(item.template, Template::Const(_))) && tail.as_deref().is_none_or(|t| matches!(t, Template::Const(_)));
        if all_constant && !inner {
            return constant(self, parts);
        }
        let kind = if vector { SyntaxKind::Vector } else { SyntaxKind::List };
        let set = self.tree.scopes_of(t)?;
        let meta = self.meta(set, kind)?;
        let like = index(parts);
        parts.push(Syntax::new(self.mc, Value::NIL, self.tree.span(t), Some(meta))?.value(self.mc));
        Ok(Template::Seq { items: built.into(), tail, vector, like })
    }
}

fn local<'gc>(var: Var) -> Core<'gc> {
    Core::Ref(Place::Local(var))
}
