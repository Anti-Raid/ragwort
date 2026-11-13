//! Syntax between the expander's tree and the arena's syntax objects, which macros' transformers
//! take and make. An identifier's object holds its scopes, and a list's a list of syntax. Each
//! object made from the tree goes back to the node it came from, so the parts of a use that a
//! transformer hands back as they were cost nothing to take back.

use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxContext, SyntaxKind, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};

use ragwort_compiler::module;
use ragwort_vm::objects::ModuleFields;

use crate::expand::{Binding, Expander, Stamp};
use crate::scope::{Scope, Set};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

impl<'gc> Expander<'_, 'gc> {
    /// `stx` as a syntax object. A list or vector is made of its items', from a stack of their
    /// own.
    pub(crate) fn wrap(&mut self, root: Stx) -> Result<Value<'gc>, ExpandError> {
        enum Task {
            Visit(Stx),
            /// A list of the last items wrapped, after its tail if it has one, or a vector of
            /// them.
            Make(Stx, usize, bool, SyntaxKind),
        }
        let mc = self.mc;
        let (mut todo, mut done) = (vec![Task::Visit(root)], Vec::new());
        while let Some(task) = todo.pop() {
            let (stx, datum, kind) = match task {
                Task::Visit(stx) => match self.tree.view(stx)? {
                    View::Id => (stx, self.tree.symbol(stx).expect("an identifier").value(mc), SyntaxKind::Identifier),
                    View::Datum(value) => (stx, value, SyntaxKind::Literal),
                    View::List(items, tail) => {
                        todo.push(Task::Make(stx, items.len(), tail.is_some(), SyntaxKind::List));
                        todo.extend(tail.map(Task::Visit));
                        todo.extend(items.into_iter().rev().map(Task::Visit));
                        continue;
                    }
                    View::Vector(items) => {
                        todo.push(Task::Make(stx, items.len(), false, SyntaxKind::Vector));
                        todo.extend(items.into_iter().rev().map(Task::Visit));
                        continue;
                    }
                },
                Task::Make(stx, count, tail, kind) => {
                    let tail = if tail { done.pop().expect("a tail") } else { Value::NIL };
                    let items = done.split_off(done.len() - count);
                    let datum = if kind == SyntaxKind::Vector { Vectors::new(mc).immutable_from_slice(&items)?.value(mc) } else { Pairs::new(mc).list_with_tail(items, tail)? };
                    (stx, datum, kind)
                }
            };
            let meta = match kind {
                SyntaxKind::Literal => None,
                _ => {
                    let set = self.tree.scopes_of(stx)?;
                    Some(self.meta(set, kind)?)
                }
            };
            let binding = if kind == SyntaxKind::Identifier { self.binding_value(stx)? } else { None };
            let value = Syntax::bound(mc, datum, self.tree.span(stx), meta, binding)?.value(mc);
            self.tree.scopes.charge(size_of::<(u64, Stx)>())?;
            self.unwrapped.insert(value.to_bits(), stx);
            done.push(value);
        }
        Ok(done.pop().expect("the root's wrapped"))
    }

    /// The metadata of syntax of `kind` with the scopes `set`, made once for each.
    pub(crate) fn meta(&mut self, set: Set, kind: SyntaxKind) -> Result<SyntaxMeta<'gc>, ExpandError> {
        let tag = match kind {
            SyntaxKind::Identifier => 0,
            SyntaxKind::List => 1,
            SyntaxKind::Vector => 2,
            _ => 3,
        };
        if let Some(&meta) = self.metas.get(&(set, tag)) {
            return Ok(meta);
        }
        let context = match self.contexts.get(&set) {
            Some(&context) => context,
            None => {
                let numbers = self.tree.scopes.scopes(set).to_vec();
                let scopes = numbers.into_iter().map(|scope| self.scope_object(scope)).collect::<Result<Vec<_>, _>>()?;
                let context = SyntaxContext::new(self.mc, &scopes)?;
                self.contexts.insert(set, context);
                context
            }
        };
        let meta = SyntaxMeta::new(self.mc, kind, Some(context), None)?;
        self.tree.scopes.charge(size_of::<((Set, usize), SyntaxMeta)>())?;
        self.metas.insert((set, tag), meta);
        Ok(meta)
    }

    /// What the identifier `id` refers to, as a value for its syntax: see
    /// `ragwort_vm`'s `free-identifier=?`. One that's ambiguous has none.
    fn binding_value(&mut self, id: Stx) -> Result<Option<Value<'gc>>, ExpandError> {
        let mc = self.mc;
        let symbol = self.tree.symbol(id).expect("an identifier");
        let set = self.tree.scopes_of(id)?;
        let Ok(binding) = self.resolve_name(symbol, set) else { return Ok(None) };
        let named = |module: Value<'gc>, name: Value<'gc>| Stamp::Named(module.to_bits(), name.to_bits());
        let (stamp, name) = match binding {
            Binding::Keyword(_) => return Ok(Some(symbol.value(mc))),
            Binding::Local(var) => (Stamp::Own(0, var.0), None),
            Binding::Macro(macro_index) => (Stamp::Own(1, macro_index), None),
            Binding::Pattern { var, .. } => (Stamp::Own(2, var.0), None),
            Binding::Slot(slot) if !matches!(self.builder.binding(symbol.value(mc)), Some(module::Binding::Slot(bound)) if bound == slot) => (Stamp::Own(3, slot), None),
            Binding::Slot(_) | Binding::Free => {
                let module = self.builder.name();
                (named(module, symbol.value(mc)), Some((module, symbol.value(mc))))
            }
            Binding::Import(import) => {
                let (module, names) = (import.module.name(mc), import.module.names(mc));
                let name = AnyVector::of(names).and_then(|names| names.get(mc, import.export.slot as usize)).unwrap_or(Value::FALSE);
                (named(module, name), Some((module, name)))
            }
        };
        if let Some(&value) = self.binding_values.get(&stamp) {
            return Ok(Some(value));
        }
        let value = match name {
            Some((module, name)) => Pairs::new(mc).cons(module, name)?.value(mc),
            None => SyntaxScope::new(mc)?.value(),
        };
        self.tree.scopes.charge(size_of::<(Stamp, Value)>())?;
        self.binding_values.insert(stamp, value);
        Ok(Some(value))
    }

    /// The object that's `scope` in syntax.
    fn scope_object(&mut self, scope: Scope) -> Result<SyntaxScope<'gc>, OutOfMemory> {
        if let Some(&object) = self.scope_objects.get(&scope) {
            return Ok(object);
        }
        let object = SyntaxScope::new(self.mc)?;
        self.tree.scopes.charge(size_of::<(Scope, SyntaxScope)>() + size_of::<(u64, Scope)>())?;
        self.scope_objects.insert(scope, object);
        self.scope_numbers.insert(object.value().to_bits(), scope);
        Ok(object)
    }

    /// The scopes of `context`. One the load hasn't seen, from another or made at run time,
    /// is a new scope to it.
    pub(crate) fn set_of(&mut self, context: Option<SyntaxContext<'gc>>) -> Result<Set, OutOfMemory> {
        let Some(context) = context else { return Ok(Set::EMPTY) };
        let mut scopes = Vec::with_capacity(context.scopes(self.mc).len());
        for object in context.scopes(self.mc) {
            let scope = match self.scope_numbers.get(&object.value().to_bits()) {
                Some(&scope) => scope,
                None => {
                    let scope = self.tree.scopes.fresh()?;
                    self.tree.scopes.charge(size_of::<(Scope, SyntaxScope)>() + size_of::<(u64, Scope)>())?;
                    self.scope_objects.insert(scope, object);
                    self.scope_numbers.insert(object.value().to_bits(), scope);
                    scope
                }
            };
            scopes.push(scope);
        }
        self.tree.scopes.set(scopes)
    }

    /// The syntax a transformer made, `value`, in the tree. What it has that isn't syntax is as
    /// if it were, at `at`, the use it's the output of; a symbol in it is an error. A list or
    /// vector's items are made before it, from a stack charged as it grows, as data that
    /// contains itself would grow it forever.
    pub(crate) fn unwrap(&mut self, value: Value<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        enum Task<'gc> {
            Visit(Value<'gc>),
            /// A list of the last items made, after its tail if it has one, or a vector of them.
            Make(SyntaxSpan<'gc>, usize, bool, bool),
        }
        let mc = self.mc;
        let bad = |this: &Self| this.error(ExpandErrorKind::BadSyntax, at);
        let (mut todo, mut done) = (vec![Task::Visit(value)], Vec::new());
        while let Some(task) = todo.pop() {
            let value = match task {
                Task::Visit(value) => value,
                Task::Make(span, count, tail, vector) => {
                    let tail = if tail { done.pop() } else { None };
                    let items = done.split_off(done.len() - count);
                    done.push(if vector { self.tree.vector(&items, span)? } else { self.tree.list(&items, tail, span)? });
                    continue;
                }
            };
            if let Some(&stx) = self.unwrapped.get(&value.to_bits()) {
                done.push(stx);
                continue;
            }
            self.tree.scopes.charge(size_of::<Task<'gc>>())?;
            let (datum, span, kind, context) = match Syntax::of(value) {
                Some(syntax) => (syntax.datum(mc), syntax.span(mc), syntax.kind(mc).ok_or_else(|| bad(self))?, syntax.context(mc)),
                None if value == Value::NIL || Pair::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::List, None),
                None if AnyVector::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::Vector, None),
                None if Symbol::of(value).is_some() => return Err(bad(self)),
                None => (value, self.tree.span(at), SyntaxKind::Literal, None),
            };
            match kind {
                SyntaxKind::Identifier => {
                    let symbol = Symbol::of(datum).ok_or_else(|| bad(self))?;
                    let set = self.set_of(context)?;
                    done.push(self.tree.id(symbol, set, span)?);
                }
                SyntaxKind::List => {
                    let (mut items, mut rest) = (Vec::new(), datum);
                    loop {
                        if let Some(pair) = Pair::of(rest) {
                            self.tree.scopes.charge(size_of::<Task<'gc>>())?;
                            items.push(Task::Visit(pair.head(mc)));
                            rest = pair.tail(mc);
                        } else if let Some(list) = Syntax::of(rest).filter(|syntax| syntax.kind(mc) == Some(SyntaxKind::List)) {
                            // A tail that's the syntax of a list goes on with its items.
                            rest = list.datum(mc);
                        } else {
                            break;
                        }
                    }
                    let tail = rest != Value::NIL;
                    todo.push(Task::Make(span, items.len(), tail, false));
                    if tail {
                        todo.push(Task::Visit(rest));
                    }
                    todo.extend(items.into_iter().rev());
                }
                SyntaxKind::Vector => {
                    let vector = AnyVector::of(datum).ok_or_else(|| bad(self))?;
                    let items: Vec<_> = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).collect();
                    self.tree.scopes.charge(items.len() * size_of::<Task<'gc>>())?;
                    todo.push(Task::Make(span, items.len(), false, true));
                    todo.extend(items.into_iter().rev().map(Task::Visit));
                }
                SyntaxKind::Literal if Symbol::of(datum).is_none() => done.push(self.tree.datum(datum, span)?),
                _ => return Err(bad(self)),
            }
        }
        Ok(done.pop().expect("the root's made"))
    }
}
