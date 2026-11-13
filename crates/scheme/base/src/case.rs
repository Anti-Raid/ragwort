//! `syntax-case` and `syntax`, as R6RS has them, compiled to the VM's
//! [`syntax_case`] patterns and templates: a clause's pattern is a
//! constant the code matches its input with, which gives a vector of what its variables matched,
//! a list of those for each ellipsis a variable's under. A template with pattern variables in it
//! is a constant too, which the code makes syntax of with theirs; one without any is the syntax
//! it's made of.

use std::rc::Rc;

use ragwort_compiler::steps::Step;
use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_types::syntax::{Syntax, SyntaxKind};
use ragwort_vm::syntax_case::{self, Pattern, PatternShape, Repeat, Template, TemplateShape};
use ragwort_vm::{Intrinsic, Request};

use crate::expand::{Aux, Binding, Call, Ex, Expander};
use crate::scope::Op;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

fn index(items: &[Value<'_>]) -> u32 {
    u32::try_from(items.len()).expect("fewer than 2^32 parts")
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// `(syntax-case input (literal ...) clause ...)`: each clause `(pattern output)` or `(pattern
    /// fender output)` tried in turn, its pattern variables bound for the fender and output.
    pub(crate) fn syntax_case(&mut self, input: Stx, literals: Stx, clauses: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let literals = self.proper(literals)?;
        if let Some(&bad) = literals.iter().find(|&&id| !self.is_id(id)) {
            return Err(self.error(ExpandErrorKind::BadSyntax, bad));
        }
        let var = self.fresh();
        let (literals, clauses): (Rc<[Stx]>, Rc<[Stx]>) = (literals.into(), clauses.into());
        Self::expr(input, move |_, value| {
            let then = move |_: &mut Self, clauses| Ok(Step::Done(Core::Let(vec![(var, value)], Box::new(clauses))));
            Ok(Step::then(Call::Run(Box::new(move |this: &mut Self| this.clauses(var, literals, clauses, 0))), then))
        })
    }

    /// The clauses from `at` on, each tried if those before it don't match.
    fn clauses(&mut self, input: Var, literals: Rc<[Stx]>, clauses: Rc<[Stx]>, at: usize) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some(&clause) = clauses.get(at) else {
            let error = Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeSyntaxError), vec![Core::Quote(Value::VOID), local(input)], None);
            return Ok(Step::Done(Core::Intrinsic(Prim::Request(Request::Raise), vec![error], None)));
        };
        let (pattern, fender, output) = match *self.proper(clause)?.as_slice() {
            [pattern, output] => (pattern, None, output),
            [pattern, fender, output] => (pattern, Some(fender), output),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, clause)),
        };
        let (mut vars, mut items) = (Vec::new(), Vec::new());
        let mut shape = self.pattern(pattern, &literals, &mut vars, &mut items)?;
        shape.vars = u32::try_from(vars.len()).expect("fewer than 2^32 variables");
        let pattern = Core::Quote(syntax_case::pattern(self.mc, shape, &items)?);
        let asked = Core::Intrinsic(Prim::Intrinsic(Intrinsic::SyntaxMatch), vec![pattern, local(input)], None);
        let scope = self.tree.scopes.fresh()?;
        let ids = vars.iter().map(|&(id, _)| self.tree.with(id, scope, Op::Add)).collect::<Result<Vec<_>, _>>()?;
        self.distinct(&ids)?;
        let matched = self.fresh();
        let mut binds = Vec::with_capacity(ids.len());
        for (k, (&id, &(_, depth))) in ids.iter().zip(&vars).enumerate() {
            let var = self.fresh();
            self.bind(id, Binding::Pattern { var, depth })?;
            let at = Core::Quote(Value::fixnum(k as i64).expect("a fixnum"));
            binds.push((var, Core::Intrinsic(Prim::Intrinsic(Intrinsic::VectorRef), vec![local(matched), at], None)));
        }
        let output = self.tree.with(output, scope, Op::Add)?;
        let fender = fender.map(|fender| self.tree.with(fender, scope, Op::Add)).transpose()?;
        let rest = Call::Run(Box::new(move |this: &mut Self| this.clauses(input, literals, clauses, at + 1)));
        Ok(Step::then(rest, move |_, next| {
            Self::expr(output, move |this, output| {
                let Some(fender) = fender else {
                    let body = Core::Let(binds, Box::new(output));
                    return Ok(Step::Done(Core::Let(vec![(matched, asked)], Box::new(Core::If(Box::new(local(matched)), Box::new(body), Box::new(next))))));
                };
                // The rest are tried if the fender fails or the pattern doesn't match.
                let k = this.fresh();
                let thunk = Core::Lambda(Lambda { id: this.lambda_id(), params: Vec::new(), optional: 0, rest: None, body: Box::new(next), name: None, at: None });
                Self::expr(fender, move |_, fender| {
                    let again = || Core::App(Box::new(local(k)), Vec::new(), None);
                    let body = Core::If(Box::new(fender), Box::new(output), Box::new(again()));
                    let body = Core::Let(binds, Box::new(body));
                    let tried = Core::If(Box::new(local(matched)), Box::new(body), Box::new(again()));
                    Ok(Step::Done(Core::Let(vec![(k, thunk)], Box::new(Core::Let(vec![(matched, asked)], Box::new(tried))))))
                })
            })
        }))
    }

    /// The pattern `root`, adding its variables to `vars`, each with how many ellipses it's
    /// under, and what it refers to to `parts`. A list or vector's items are made before it,
    /// and those it repeats with the slots of their variables, from a stack of their own.
    fn pattern(&mut self, root: Stx, literals: &[Stx], vars: &mut Vec<(Stx, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<PatternShape, ExpandError> {
        enum Task {
            Visit(Stx, u32),
            /// Into an item an ellipsis repeats, whose variables' slots start here.
            Repeat,
            Repeated,
            Seq { before: usize, repeat: bool, after: usize, tail: bool, vector: bool },
        }
        let slot = |vars: &Vec<(Stx, u32)>| u32::try_from(vars.len()).expect("fewer than 2^32 variables");
        let mut shape = PatternShape::default();
        let (mut done, mut starts, mut repeats) = (Vec::new(), Vec::new(), Vec::new());
        let mut todo = vec![Task::Visit(root, 0)];
        while let Some(task) = todo.pop() {
            let (p, depth) = match task {
                Task::Visit(p, depth) => (p, depth),
                Task::Repeat => {
                    starts.push(slot(vars));
                    continue;
                }
                Task::Repeated => {
                    let each = done.pop().expect("a repeated item");
                    repeats.push(Repeat { each, slots: starts.pop().expect("a repeat's start")..slot(vars) });
                    continue;
                }
                Task::Seq { before, repeat, after, tail, vector } => {
                    let tail = tail.then(|| done.pop().expect("a tail"));
                    let after = done.split_off(done.len() - after);
                    let repeat = if repeat { repeats.pop() } else { None };
                    let before = done.split_off(done.len() - before);
                    let (before, after) = (shape.list(before), shape.list(after));
                    done.push(shape.add(Pattern::Seq { before, repeat, after, tail, vector }));
                    continue;
                }
            };
            let (items, tail, vector) = match self.tree.view(p)? {
                View::Id if self.is_aux(p, Aux::Underscore)? => {
                    done.push(shape.add(Pattern::Any));
                    continue;
                }
                View::Id if self.is_aux(p, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, p)),
                View::Id if self.is_literal(p, literals)? => {
                    let at = index(parts);
                    parts.push(self.wrap(p)?);
                    done.push(shape.add(Pattern::Literal(at)));
                    continue;
                }
                View::Id => {
                    vars.push((p, depth));
                    done.push(shape.add(Pattern::Var(slot(vars) - 1)));
                    continue;
                }
                View::Datum(value) => {
                    let at = index(parts);
                    parts.push(value);
                    done.push(shape.add(Pattern::Datum(at)));
                    continue;
                }
                View::List(items, tail) => (items, tail, false),
                View::Vector(items) => (items, None, true),
            };
            // Those before an ellipsis, the one it repeats, and those after, or all of them if
            // there's none.
            let mut dots = Vec::new();
            for (i, &item) in items.iter().enumerate() {
                if self.is_aux(item, Aux::Ellipsis)? {
                    dots.push(i);
                }
            }
            let at = todo.len();
            let seq = match *dots.as_slice() {
                [] => {
                    todo.extend(items.iter().map(|&item| Task::Visit(item, depth)));
                    Task::Seq { before: items.len(), repeat: false, after: 0, tail: tail.is_some(), vector }
                }
                [i] if i > 0 => {
                    todo.extend(items[..i - 1].iter().map(|&item| Task::Visit(item, depth)));
                    todo.extend([Task::Repeat, Task::Visit(items[i - 1], depth + 1), Task::Repeated]);
                    todo.extend(items[i + 1..].iter().map(|&item| Task::Visit(item, depth)));
                    Task::Seq { before: i - 1, repeat: true, after: items.len() - i - 1, tail: tail.is_some(), vector }
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, p)),
            };
            todo.extend(tail.map(|tail| Task::Visit(tail, depth)));
            todo.push(seq);
            todo[at..].reverse();
        }
        Ok(shape)
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
        let mut shape = self.template(template, &mut used, &mut parts)?;
        Ok(match *shape.nodes.last().expect("a template's root") {
            Template::Const(at) => Core::Quote(parts[at as usize]),
            Template::Var(_) => local(used[0].0),
            Template::Seq { .. } => {
                shape.depths = used.iter().map(|&(_, depth)| depth).collect();
                let template = Core::Quote(syntax_case::template(self.mc, shape, &parts)?);
                let args = std::iter::once(template).chain(used.iter().map(|&(var, _)| local(var)));
                Core::Intrinsic(Prim::Intrinsic(Intrinsic::SyntaxBuild), args.collect(), None)
            }
        })
    }

    /// The template `root`, its last node, with the pattern variables it refers to added to
    /// `used`, unless they're there already, and the syntax it's made of to `parts`. A list or
    /// vector's items are made before it. In an escaped one, `(... template)`, `...` is an
    /// identifier.
    fn template(&mut self, root: Stx, used: &mut Vec<(Var, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<TemplateShape, ExpandError> {
        /// A part made: its node, the slots of the variables in it, in the order they're first
        /// found, whether it's a constant, and whether it has an escape in it.
        struct Made {
            node: u32,
            slots: Vec<u32>,
            constant: bool,
            escapes: bool,
        }
        enum Task {
            /// A template, under so many ellipses, and whether it's escaped.
            Visit(Stx, u32, bool),
            Escaped,
            /// An item made, which has variables under more ellipses than the list it's in if
            /// it's under any of its own.
            Item(Stx, u32, u32),
            /// A list or vector, and how many parts, nodes, items and slots there were before it.
            Seq { t: Stx, ellipses: Vec<u32>, tail: bool, vector: bool, start: (usize, usize, usize, usize) },
        }
        let mut shape = TemplateShape::default();
        let mut done: Vec<Made> = Vec::new();
        let mut todo = vec![Task::Visit(root, 0, false)];
        while let Some(task) = todo.pop() {
            let (t, nesting, escaped) = match task {
                Task::Visit(t, nesting, escaped) => (t, nesting, escaped),
                Task::Escaped => {
                    done.last_mut().expect("an escaped template").escapes = true;
                    continue;
                }
                Task::Item(item, ellipses, nesting) => {
                    let made = done.last().expect("an item");
                    if ellipses > 0 && !made.slots.iter().any(|&slot| used[slot as usize].1 > nesting) {
                        return Err(self.error(ExpandErrorKind::BadSyntax, item));
                    }
                    continue;
                }
                Task::Seq { t, ellipses, tail, vector, start: (parts_at, nodes, items, slots) } => {
                    let tail = if tail { done.pop() } else { None };
                    let built = done.split_off(done.len() - ellipses.len());
                    let inner = built.iter().chain(&tail).any(|made| made.escapes);
                    // A list of constants is the syntax it's made from, unless an escape in it is
                    // dropped.
                    if built.iter().chain(&tail).all(|made| made.constant) && !inner {
                        parts.truncate(parts_at);
                        shape.truncate(nodes, items, slots);
                        parts.push(self.wrap(t)?);
                        done.push(Made { node: shape.add(Template::Const(index(&parts[..parts_at]))), slots: Vec::new(), constant: true, escapes: false });
                        continue;
                    }
                    let mut all = Vec::new();
                    for slot in built.iter().chain(&tail).flat_map(|made| &made.slots) {
                        if !all.contains(slot) {
                            all.push(*slot);
                        }
                    }
                    let tail = tail.map(|made| made.node);
                    let items = shape.items(built.into_iter().zip(ellipses).map(|(made, ellipses)| (made.node, ellipses, made.slots)));
                    let kind = if vector { SyntaxKind::Vector } else { SyntaxKind::List };
                    let set = self.tree.scopes_of(t)?;
                    let meta = self.meta(set, kind)?;
                    let like = index(parts);
                    parts.push(Syntax::new(self.mc, Value::NIL, self.tree.span(t), Some(meta))?.value(self.mc));
                    let node = shape.add(Template::Seq { items, tail, vector, like });
                    done.push(Made { node, slots: all, constant: false, escapes: inner });
                    continue;
                }
            };
            let (items, tail, vector) = match self.tree.view(t)? {
                View::Id if !escaped && self.is_aux(t, Aux::Ellipsis)? => return Err(self.error(ExpandErrorKind::BadSyntax, t)),
                View::Id => {
                    if let Binding::Pattern { var, depth } = self.resolve(t)? {
                        if nesting < depth {
                            return Err(self.error(ExpandErrorKind::BadSyntax, t));
                        }
                        let slot = used.iter().position(|&(v, _)| v == var).unwrap_or_else(|| {
                            used.push((var, depth));
                            used.len() - 1
                        });
                        let slot = u32::try_from(slot).expect("fewer than 2^32 variables");
                        done.push(Made { node: shape.add(Template::Var(slot)), slots: vec![slot], constant: false, escapes: false });
                        continue;
                    }
                    (Vec::new(), None, None)
                }
                View::Datum(_) => (Vec::new(), None, None),
                View::List(items, tail) => {
                    // `(... template)` is `template` with its ellipses as they are.
                    if let [dots, inner] = items[..]
                        && !escaped
                        && tail.is_none()
                        && self.is_aux(dots, Aux::Ellipsis)?
                    {
                        todo.extend([Task::Escaped, Task::Visit(inner, nesting, true)]);
                        continue;
                    }
                    (items, tail, Some(false))
                }
                View::Vector(items) => (items, None, Some(true)),
            };
            let Some(vector) = vector else {
                let at = index(parts);
                parts.push(self.wrap(t)?);
                done.push(Made { node: shape.add(Template::Const(at)), slots: Vec::new(), constant: true, escapes: false });
                continue;
            };
            let start = (parts.len(), shape.nodes.len(), shape.items.len(), shape.slots.len());
            let at = todo.len();
            let mut ellipses = Vec::new();
            let mut i = 0;
            while i < items.len() {
                let item = items[i];
                let mut n = 0;
                while !escaped && i + 1 < items.len() && self.is_aux(items[i + 1], Aux::Ellipsis)? {
                    n += 1;
                    i += 1;
                }
                todo.extend([Task::Visit(item, nesting + n, escaped), Task::Item(item, n, nesting)]);
                ellipses.push(n);
                i += 1;
            }
            todo.extend(tail.map(|tail| Task::Visit(tail, nesting, escaped)));
            todo.push(Task::Seq { t, ellipses, tail: tail.is_some(), vector, start });
            todo[at..].reverse();
        }
        Ok(shape)
    }
}

fn local<'gc>(var: Var) -> Core<'gc> {
    Core::Ref(Place::Local(var))
}
