//! `syntax-case` and `syntax`, as in R6RS, compiled to the patterns and templates of the VM's
//! [`syntax_case`] module. The pattern of a clause becomes a
//! constant, and the generated code matches the input against it. A successful match gives a vector with the match of each pattern variable.
//! The match of a variable under ellipses is a list, nested once for each ellipsis. A template that contains pattern variables
//! also becomes a constant, and the generated code builds syntax from it and the variables' matches. A template without pattern variables becomes
//! its own syntax object.

use std::fmt;

use ragwort_compiler::{Core, Place, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_types::syntax::{Syntax, SyntaxKind};
use ragwort_vm::Intrinsic;
use ragwort_vm::syntax_case::{self, Pattern, PatternShape, Repeat, Template, TemplateShape};

use crate::engine::{Binding, Engine};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

pub(crate) fn index(items: &[Value<'_>]) -> u32 {
    u32::try_from(items.len()).expect("fewer than 2^32 parts")
}

impl<'a, 'gc, K: Copy + PartialEq + fmt::Debug> Engine<'a, 'gc, K> {
    /// Compiles the pattern `root`. Adds each pattern variable to `vars`, with the number of ellipses that it is
    /// under. Adds the literals and data that the pattern refers to to `parts`. The traversal uses an explicit stack, and compiles the items of a list or vector before it.
    /// A repeated item is recorded with the range of the slots of its variables.
    pub fn pattern(&mut self, root: Stx, literals: &[Stx], vars: &mut Vec<(Stx, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<PatternShape, ExpandError> {
        enum Task {
            Visit(Stx, u32),
            /// Marks the start of an item that an ellipsis repeats. The slots of the item's variables start at the current number of variables.
            Repeat,
            Repeated,
            Seq { before: usize, repeat: bool, after: usize, tail: bool, vector: bool },
        }
        fn slot(vars: &[(Stx, u32)]) -> u32 {
            u32::try_from(vars.len()).expect("fewer than 2^32 variables")
        }
        let mut shape = PatternShape::default();
        let (mut done, mut starts, mut repeats) = (Vec::new(), Vec::new(), Vec::new());
        let mut todo = vec![Task::Visit(root, 0)];
        while let Some(task) = todo.pop() {
            let (pattern, depth) = match task {
                Task::Visit(pattern, depth) => (pattern, depth),
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
                    let tail = if tail { Some(done.pop().expect("a tail")) } else { None };
                    let after = done.split_off(done.len() - after);
                    let repeat = if repeat { repeats.pop() } else { None };
                    let before = done.split_off(done.len() - before);
                    let (before, after) = (shape.list(before), shape.list(after));
                    done.push(shape.add(Pattern::Seq { before, repeat, after, tail, vector }));
                    continue;
                }
            };
            let (items, tail, vector) = match self.tree.view(pattern)? {
                View::Id if self.is_underscore(pattern)? => {
                    done.push(shape.add(Pattern::Any));
                    continue;
                }
                View::Id if self.is_ellipsis(pattern)? => return Err(self.error(ExpandErrorKind::BadSyntax, pattern)),
                View::Id if self.is_literal(pattern, literals)? => {
                    let at = index(parts);
                    parts.push(self.wrap(pattern)?);
                    done.push(shape.add(Pattern::Literal(at)));
                    continue;
                }
                View::Id => {
                    vars.push((pattern, depth));
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
            // Split the items into those before the repeated item, the repeated item, and those after the ellipsis. Without
            // an ellipsis, all items count as before.
            let mut dots = Vec::new();
            for (i, &item) in items.iter().enumerate() {
                if self.is_ellipsis(item)? {
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
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, pattern)),
            };
            todo.extend(tail.map(|tail| Task::Visit(tail, depth)));
            todo.push(seq);
            todo[at..].reverse();
        }
        Ok(shape)
    }

    /// Returns whether `id` is one of `literals`, that is, has the same name and the same scopes as one of them.
    pub fn is_literal(&mut self, id: Stx, literals: &[Stx]) -> Result<bool, ExpandError> {
        let (symbol, set) = (self.tree.symbol(id), self.tree.scopes_of(id)?);
        for &literal in literals {
            if self.tree.symbol(literal) == symbol && self.tree.scopes_of(literal)? == set {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Expands `(syntax template)` to code that builds the syntax of `template`, with each pattern variable replaced by its match.
    pub fn syntax(&mut self, template: Stx) -> Result<Core<'gc>, ExpandError> {
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

    /// Compiles the template `root`. The root is the last node of the returned shape. Adds each pattern variable that the template refers to to
    /// `used`, once. Adds the constant syntax objects of the template to `parts`. The items of a list or
    /// vector are compiled before it. In an escaped template, `(... template)`, `...` is an ordinary
    /// identifier.
    pub fn template(&mut self, root: Stx, used: &mut Vec<(Var, u32)>, parts: &mut Vec<Value<'gc>>) -> Result<TemplateShape, ExpandError> {
        /// A compiled part of a template: its node, the slots of the variables in it in order of first
        /// occurrence, whether it is a constant, and whether it contains an escape.
        struct Made {
            node: u32,
            slots: Vec<u32>,
            constant: bool,
            escapes: bool,
        }
        enum Task {
            /// Compiles a template. The fields are the template, the number of ellipses that it is under, and whether it is escaped.
            Visit(Stx, u32, bool),
            Escaped,
            /// Checks a compiled item. The fields are the item, the number of ellipses that follow it, and the number of ellipses that the enclosing list is under.
            /// An item followed by ellipses must contain a pattern variable whose depth is greater than that of the enclosing list.
            Item(Stx, u32, u32),
            /// Builds a list or vector from its compiled items. `start` holds the lengths of `parts` and of the shape's nodes, items and slots before the items were compiled.
            Seq { t: Stx, ellipses: Vec<u32>, tail: bool, vector: bool, start: (usize, usize, usize, usize) },
        }
        let mut shape = TemplateShape::default();
        let mut done: Vec<Made> = Vec::new();
        let mut todo = vec![Task::Visit(root, 0, false)];
        while let Some(task) = todo.pop() {
            let (template, nesting, escaped) = match task {
                Task::Visit(template, nesting, escaped) => (template, nesting, escaped),
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
                Task::Seq { t: template, ellipses, tail, vector, start: (parts_at, nodes, items, slots) } => {
                    let tail = if tail { done.pop() } else { None };
                    let built = done.split_off(done.len() - ellipses.len());
                    let inner = built.iter().chain(&tail).any(|made| made.escapes);
                    // A list of constants becomes one constant: the syntax object of the list itself. That is not possible if the list contains an escape,
                    // because the `(... )` around the escaped template must be dropped.
                    if built.iter().chain(&tail).all(|made| made.constant) && !inner {
                        parts.truncate(parts_at);
                        shape.truncate(nodes, items, slots);
                        parts.push(self.wrap(template)?);
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
                    let set = self.tree.scopes_of(template)?;
                    let meta = self.meta(set, kind)?;
                    let like = index(parts);
                    parts.push(Syntax::new(self.mc, Value::NULL, self.tree.span(template), Some(meta))?.value(self.mc));
                    let node = shape.add(Template::Seq { items, tail, vector, like });
                    done.push(Made { node, slots: all, constant: false, escapes: inner });
                    continue;
                }
            };
            let (items, tail, vector) = match self.tree.view(template)? {
                View::Id if !escaped && self.is_ellipsis(template)? => return Err(self.error(ExpandErrorKind::BadSyntax, template)),
                View::Id => {
                    if let Binding::Pattern { var, depth } = self.resolve(template)? {
                        if nesting < depth {
                            return Err(self.error(ExpandErrorKind::BadSyntax, template));
                        }
                        let slot = used.iter().position(|&(used_var, _)| used_var == var).unwrap_or_else(|| {
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
                    // `(... template)` stands for `template`, with each `...` in it taken as an identifier.
                    if let [dots, inner] = items[..]
                        && !escaped
                        && tail.is_none()
                        && self.is_ellipsis(dots)?
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
                parts.push(self.wrap(template)?);
                done.push(Made { node: shape.add(Template::Const(at)), slots: Vec::new(), constant: true, escapes: false });
                continue;
            };
            let start = (parts.len(), shape.nodes.len(), shape.items.len(), shape.slots.len());
            let at = todo.len();
            let mut ellipses = Vec::new();
            let mut i = 0;
            while i < items.len() {
                let item = items[i];
                let mut count = 0;
                while !escaped && i + 1 < items.len() && self.is_ellipsis(items[i + 1])? {
                    count += 1;
                    i += 1;
                }
                todo.extend([Task::Visit(item, nesting + count, escaped), Task::Item(item, count, nesting)]);
                ellipses.push(count);
                i += 1;
            }
            todo.extend(tail.map(|tail| Task::Visit(tail, nesting, escaped)));
            todo.push(Task::Seq { t: template, ellipses, tail: tail.is_some(), vector, start });
            todo[at..].reverse();
        }
        Ok(shape)
    }
}

pub(crate) fn local<'gc>(var: Var) -> Core<'gc> {
    Core::Ref(Place::Local(var))
}
