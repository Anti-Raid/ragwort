//! Conversion between the expander's tree and the arena's syntax objects. Macro transformers
//! take and return syntax objects. The syntax object of an identifier holds its scopes. The syntax object of a list holds a list of syntax objects. Each
//! syntax object created from the tree is mapped back to its node. So when a transformer returns a part of
//! its input unchanged, converting that part back takes one lookup.

use std::fmt;

use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxContext, SyntaxKind, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};

use ragwort_compiler::module;

use crate::engine::{Binding, Engine, Found, Stamp, internal_name};
use crate::scope::{Scope, Set, TOP};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

impl<'a, 'gc, K: Copy + PartialEq + fmt::Debug> Engine<'a, 'gc, K> {
    /// Converts `root` to a syntax object. The traversal uses an explicit stack, and builds each
    /// list or vector from the syntax objects of its items.
    pub fn wrap(&mut self, root: Stx) -> Result<Value<'gc>, ExpandError> {
        enum Task {
            Visit(Stx),
            /// Builds the list or vector of a node from the last `count` syntax objects created. The
            /// syntax object of a list's tail, if the list has one, is on the stack above them.
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
                    let tail = if tail {
                        done.pop().expect("a tail")
                    } else {
                        Value::NULL
                    };
                    let items = done.split_off(done.len() - count);
                    let datum = if kind == SyntaxKind::Vector {
                        Vectors::new(mc).immutable_from_slice(&items)?.value(mc)
                    } else {
                        Pairs::new(mc).list_with_tail(items, tail)?
                    };
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
            let binding = if kind == SyntaxKind::Identifier {
                self.binding_value(stx)?
            } else {
                None
            };
            let value = Syntax::bound(mc, datum, self.tree.span(stx), meta, binding)?.value(mc);
            self.tree.scopes.charge(size_of::<(u64, Stx)>())?;
            self.unwrapped.insert(value.to_bits(), stx);
            done.push(value);
        }
        Ok(done.pop().expect("the root's wrapped"))
    }

    /// Converts `root` to a syntax object that becomes part of the code, such as a template. Records the bindings of the module that `root` refers
    /// to, so the module can keep them for another module that gets the syntax.
    pub fn quote(&mut self, root: Stx) -> Result<Value<'gc>, ExpandError> {
        self.quoting = true;
        let wrapped = self.wrap(root);
        self.quoting = false;
        wrapped
    }

    /// Returns the metadata for syntax of `kind` with the scope set `set`. It is created once for each such pair and cached.
    pub fn meta(&mut self, set: Set, kind: SyntaxKind) -> Result<SyntaxMeta<'gc>, ExpandError> {
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

    /// Returns the binding value for the syntax object of the identifier `id`, or `None` if `id` is ambiguous.
    /// `free-identifier=?` in `ragwort_vm` compares these values.
    ///
    /// - The value of a keyword or a core form is the identifier's symbol.
    /// - A [`Stamp::Named`] binding has a mutable vector of two items: the module that binds the name, and the name. For a name of the module being
    ///   expanded, the first item is the module's name until [`Sealed::patch`](crate::Sealed::patch) replaces it with the module.
    /// - A [`Stamp::Own`] binding has a fresh `SyntaxScope` object. The object is not used as a scope. It only serves as a unique value that is compared by identity.
    ///
    /// An identifier that a macro of another module introduced keeps the binding value that it came with.
    pub fn binding_value(&mut self, id: Stx) -> Result<Option<Value<'gc>>, ExpandError> {
        let mc = self.mc;
        let symbol = self.tree.symbol(id).expect("an identifier");
        let set = self.tree.scopes_of(id)?;
        let origin = self.origin(id, set);
        // A macro of another file of the module has the binding value of a name that the module binds.
        let binding = match self.find(symbol, set, origin) {
            Ok(Found::Bound(binding)) => binding,
            Ok(Found::ModuleMacro(_)) => Binding::Free,
            Err(_) => return Ok(None),
        };
        if let Some(origin) = origin
            && !matches!(binding, Binding::Local(_) | Binding::Macro(_) | Binding::Pattern { .. } | Binding::Slot(_))
        {
            // The origin can be a binding of this module, from a file in another language.
            if self.quoting
                && let Some(named) = AnyVector::of(origin).filter(|vector| vector.len(mc) == 2)
                && named.get(mc, 0) == Some(self.module.name())
                && let Some(key) = named.get(mc, 1)
            {
                self.quoted.push(key);
            }
            return Ok(Some(origin));
        }
        let (stamp, name) = match binding {
            Binding::Keyword(_) | Binding::Core(_) => return Ok(Some(symbol.value(mc))),
            Binding::Local(var) => (Stamp::Own(0, var.0), None),
            Binding::Macro(macro_index) => match self.macro_names[macro_index as usize] {
                Some((module, name)) => (Stamp::Named(module.to_bits(), name.to_bits()), Some((module, name))),
                None => (Stamp::Own(1, macro_index), None),
            },
            Binding::Pattern { var, .. } => (Stamp::Own(2, var.0), None),
            Binding::Slot(slot) if !matches!(self.module.binding(symbol.value(mc)), Some(module::Binding::Slot(bound)) if bound == slot) => {
                let (module, slot) = (self.module.name(), Value::fixnum(i64::from(slot)).expect("slots are fixnums"));
                (Stamp::Named(module.to_bits(), slot.to_bits()), Some((module, slot)))
            }
            Binding::Slot(_) | Binding::Free => {
                let module = self.module.name();
                (Stamp::Named(module.to_bits(), symbol.value(mc).to_bits()), Some((module, symbol.value(mc))))
            }
            Binding::Import(import) => {
                let (module, name) = (Value::object(mc, import.module), internal_name(mc, import));
                (Stamp::Named(module.to_bits(), name.to_bits()), Some((module, name)))
            }
        };
        if self.quoting
            && let Some((module, key)) = name
            && module == self.module.name()
        {
            self.quoted.push(key);
        }
        if let Some(&value) = self.binding_values.get(&stamp) {
            return Ok(Some(value));
        }
        let value = match name {
            Some((module, name)) => Vectors::new(mc).from_slice(&[module, name])?.value(mc),
            None => SyntaxScope::new(mc)?.value(),
        };
        self.tree.scopes.charge(size_of::<(Stamp, Value)>())?;
        self.binding_values.insert(stamp, value);
        Ok(Some(value))
    }

    /// Returns the `SyntaxScope` object that represents `scope` in syntax objects. It is created on first use.
    pub fn scope_object(&mut self, scope: Scope) -> Result<SyntaxScope<'gc>, OutOfMemory> {
        if let Some(&object) = self.scope_objects.get(&scope) {
            return Ok(object);
        }
        let object = SyntaxScope::new(self.mc)?;
        self.tree.scopes.charge(size_of::<(Scope, SyntaxScope)>() + size_of::<(u64, Scope)>())?;
        self.scope_objects.insert(scope, object);
        self.scope_numbers.insert(object.value().to_bits(), scope);
        Ok(object)
    }

    /// Returns the scope set of `context`. A scope object that this load has not seen gets a fresh
    /// scope number. Such an object comes from another load or was created at run time.
    pub fn set_of(&mut self, context: Option<SyntaxContext<'gc>>) -> Result<Set, OutOfMemory> {
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

    /// Converts `value`, the output of a transformer, into the tree. A part that is not a syntax
    /// object is treated as syntax with the span of `at`, the macro use. A bare symbol is an error. The traversal uses an explicit stack, and creates the items of a list or
    /// vector before it. The stack is charged to the arena's budget as it grows. Otherwise cyclic data
    /// would grow the stack without limit.
    pub fn unwrap(&mut self, value: Value<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        enum Task<'gc> {
            Visit(Value<'gc>),
            /// Builds a list or vector from the last `count` nodes created. The node of a list's tail, if the list has one, is on the stack above them.
            Make(SyntaxSpan<'gc>, usize, bool, bool),
        }
        let mc = self.mc;
        let (mut todo, mut done) = (vec![Task::Visit(value)], Vec::new());
        while let Some(task) = todo.pop() {
            let value = match task {
                Task::Visit(value) => value,
                Task::Make(span, count, tail, vector) => {
                    let tail = if tail {
                        done.pop()
                    } else {
                        None
                    };
                    let items = done.split_off(done.len() - count);
                    let made = if vector {
                        self.tree.vector(&items, span)?
                    } else {
                        self.tree.list(&items, tail, span)?
                    };
                    done.push(made);
                    continue;
                }
            };
            if let Some(&stx) = self.unwrapped.get(&value.to_bits()) {
                done.push(stx);
                continue;
            }
            self.tree.scopes.charge(size_of::<Task<'gc>>())?;
            let origin = Syntax::of(value).and_then(|syntax| syntax.binding(mc));
            let (datum, span, kind, context) = match Syntax::of(value) {
                Some(syntax) => (syntax.datum(mc), syntax.span(mc), syntax.kind(mc).ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, at))?, syntax.context(mc)),
                None if value == Value::NULL || Pair::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::List, None),
                None if AnyVector::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::Vector, None),
                None if Symbol::of(value).is_some() => return Err(self.error(ExpandErrorKind::BadSyntax, at)),
                None => (value, self.tree.span(at), SyntaxKind::Literal, None),
            };
            match kind {
                SyntaxKind::Identifier => {
                    let symbol = Symbol::of(datum).ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, at))?;
                    let set = self.set_of(context)?;
                    let id = self.tree.id(symbol, set, span)?;
                    // An identifier without the `TOP` scope was not read from this module's source. Its binding value says what it refers to.
                    if let Some(origin) = origin
                        && !self.tree.scopes.contains(set, TOP)
                    {
                        self.tree.set_origin(id, origin)?;
                    }
                    done.push(id);
                }
                SyntaxKind::List => {
                    let (mut items, mut rest) = (Vec::new(), datum);
                    loop {
                        if let Some(pair) = Pair::of(rest) {
                            self.tree.scopes.charge(size_of::<Task<'gc>>())?;
                            items.push(Task::Visit(pair.head(mc)));
                            rest = pair.tail(mc);
                        } else if let Some(list) = Syntax::of(rest).filter(|syntax| syntax.kind(mc) == Some(SyntaxKind::List)) {
                            // A tail that is the syntax object of a list continues the list with its items.
                            rest = list.datum(mc);
                        } else {
                            break;
                        }
                    }
                    let tail = rest != Value::NULL;
                    todo.push(Task::Make(span, items.len(), tail, false));
                    if tail {
                        todo.push(Task::Visit(rest));
                    }
                    todo.extend(items.into_iter().rev());
                }
                SyntaxKind::Vector => {
                    let vector = AnyVector::of(datum).ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, at))?;
                    let items: Vec<_> = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).collect();
                    self.tree.scopes.charge(items.len() * size_of::<Task<'gc>>())?;
                    todo.push(Task::Make(span, items.len(), false, true));
                    todo.extend(items.into_iter().rev().map(Task::Visit));
                }
                SyntaxKind::Literal if Symbol::of(datum).is_none() => done.push(self.tree.datum(datum, span)?),
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, at)),
            }
        }
        Ok(done.pop().expect("the root's made"))
    }
}
