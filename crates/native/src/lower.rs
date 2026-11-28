//! Lowers native ragwort syntax to the compiler's core forms.

use std::fmt;
use std::ops::{Deref, DerefMut};

use ragwort_compiler::module::{self, Filter, Item, ModuleBuilder, ModuleError, Provide, Require, RequireSpec, Resolver, Unusable};
use ragwort_compiler::steps::Step;
use ragwort_compiler::structs::{self, Declaration};
use ragwort_compiler::{CompileError, Core, GlobalError, Place};
use ragwort_expander::tree::{Stx, View};
use ragwort_expander::{Binding, Call, CoreForm, Engine, Ex, Expand, ExpandError, ExpandErrorKind, Forms, Host, Sealed};
use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::string::chars;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{Syntax, SyntaxSpan};
use ragwort_vm::structs::TypeFlags;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LowerErrorKind {
    /// A list did not start with a form's name. For example, a call was not written with `%app`.
    NotAForm,
    /// A form was malformed: it had the wrong number or the wrong kind of parts.
    BadShape,
    /// One `%let`, `%letrec` or `%lambda` bound a name twice, or a module defined or provided a
    /// name twice. A repeated keyword and a repeated struct field are reported this way too.
    Duplicate,
    /// A name was not a local variable, a module variable or an import.
    Unbound,
    /// The module both defined and required a name, or required one name as two different bindings.
    Conflict,
    /// A `%set!` assigned an import, a binding that a struct form defines, or a keyword procedure.
    Immutable,
    /// A `%define`, `%struct`, `%require` or `%provide` was not at the top level.
    Definition,
    /// The resolver did not find a required module, or it returned a module that no [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder) built.
    Resolve,
    /// A `%require` named a binding that the required module does not export.
    NotProvided,
    /// A `%provide` named a binding that the module does not define.
    NotDefined,
    /// The code referred to an export that its module has not defined yet.
    Uninitialized,
    /// The code used a struct's name as a value, but the struct's module provides the struct without its constructor.
    NoConstructor,
    /// An `%intrinsic` or `%apply-intrinsic` named something that is not an intrinsic available to the code.
    UnknownIntrinsic,
    /// A `%call-host` named something that is not one of the host functions given to the code.
    UnknownHost,
    /// An `%intrinsic` or `%call-host` had a number of arguments that the intrinsic or host function does not accept.
    Arity,
    /// A `%break` or `%continue` named a loop that is not around it.
    Label,
    /// The code used syntax that native ragwort does not have, such as a quasiquote outside a quoted datum.
    Unsupported,
    /// An identifier had two candidate bindings, and neither binding's scope set was a subset of the other's.
    Ambiguous,
    /// A macro's transformer failed: it raised an error, ran out of fuel, or yielded to the host. Also
    /// reported when a transformer expression does not evaluate to a procedure.
    Transformer,
    /// The code used a macro of another language. Native ragwort can use only the macros of native ragwort.
    Language,
    /// A macro's transformer referred to a variable of the module. The variable does not exist when the transformer runs, because the module is still being lowered.
    Phase,
    /// The arena could not create a value that lowering needed.
    Arena(Error),
}

impl From<OutOfMemory> for LowerErrorKind {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

impl From<Error> for LowerErrorKind {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

/// A lowering error: its kind, and the byte range `start..end` of the source text where it occurred.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LowerError {
    pub kind: LowerErrorKind,
    pub start: u32,
    pub end: u32,
}

impl LowerError {
    /// Converts `error`, an error from declaring an item, into a lowering error. `span` is the span that the module builder reported with the error.
    pub fn declared(error: ModuleError, span: SyntaxSpan<'_>) -> Self {
        let kind = match error {
            ModuleError::Duplicate => LowerErrorKind::Duplicate,
            ModuleError::Conflict => LowerErrorKind::Conflict,
            ModuleError::NotDefined => LowerErrorKind::NotDefined,
            ModuleError::Immutable => LowerErrorKind::Immutable,
            ModuleError::Resolve => LowerErrorKind::Resolve,
            ModuleError::NotProvided => LowerErrorKind::NotProvided,
            ModuleError::Supertype | ModuleError::Struct => LowerErrorKind::BadShape,
            ModuleError::OutOfMemory => OutOfMemory.into(),
        };
        Self { kind, start: span.start(), end: span.end() }
    }

    /// Converts `error` into a lowering error if `error` is a [`CompileError::Global`], and returns `None` otherwise.
    ///
    /// The lowerer does not resolve module-level names. The compiler does, so the compiler is where an unbound or immutable name is found. The error carries the span that the lowerer gave the name.
    pub fn located(error: CompileError) -> Option<Self> {
        let CompileError::Global { kind, start, end } = error else { return None };
        let kind = match kind {
            GlobalError::Unbound => LowerErrorKind::Unbound,
            GlobalError::Immutable => LowerErrorKind::Immutable,
            GlobalError::Import(Unusable::Uninitialized) => LowerErrorKind::Uninitialized,
            GlobalError::Import(Unusable::MatchOnly) => LowerErrorKind::NoConstructor,
        };
        Some(Self { kind, start, end })
    }
}

impl fmt::Display for LowerErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            LowerErrorKind::NotAForm => "a list that doesn't start with a form's name",
            LowerErrorKind::BadShape => "a form with the wrong parts",
            LowerErrorKind::Duplicate => "a name bound twice",
            LowerErrorKind::Unbound => "a name nothing defines",
            LowerErrorKind::Conflict => "a name both defined and required",
            LowerErrorKind::Immutable => "an assignment of a name that can't change",
            LowerErrorKind::Definition => "a definition that isn't at the top level",
            LowerErrorKind::Resolve => "a module that can't be found",
            LowerErrorKind::NotProvided => "a name the module doesn't provide",
            LowerErrorKind::NotDefined => "a provide of a name that isn't defined",
            LowerErrorKind::Uninitialized => "an export of a module that hasn't defined it yet",
            LowerErrorKind::NoConstructor => "a struct whose constructor its module doesn't provide",
            LowerErrorKind::UnknownIntrinsic => "an intrinsic the code can't name",
            LowerErrorKind::UnknownHost => "a host function the module wasn't given",
            LowerErrorKind::Arity => "an intrinsic or host call with the wrong number of arguments",
            LowerErrorKind::Label => "a break or continue of a loop that isn't around it",
            LowerErrorKind::Unsupported => "syntax native ragwort doesn't have",
            LowerErrorKind::Ambiguous => "an identifier with more than one binding",
            LowerErrorKind::Transformer => "a macro's transformer that failed",
            LowerErrorKind::Language => "a macro of another language",
            LowerErrorKind::Phase => "a macro's transformer that refers to a variable that doesn't exist yet",
            LowerErrorKind::Arena(_) => "running out of memory",
        })
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at bytes {}..{}", self.kind, self.start, self.end)
    }
}

impl std::error::Error for LowerError {}

impl From<Error> for LowerError {
    fn from(error: Error) -> Self {
        Self { kind: error.into(), start: 0, end: 0 }
    }
}

impl From<ExpandError> for LowerError {
    fn from(error: ExpandError) -> Self {
        let kind = match error.kind {
            ExpandErrorKind::BadSyntax | ExpandErrorKind::NoExpression => LowerErrorKind::BadShape,
            ExpandErrorKind::Duplicate => LowerErrorKind::Duplicate,
            ExpandErrorKind::Definition => LowerErrorKind::Definition,
            ExpandErrorKind::Immutable => LowerErrorKind::Immutable,
            ExpandErrorKind::Unbound => LowerErrorKind::Unbound,
            ExpandErrorKind::Conflict => LowerErrorKind::Conflict,
            ExpandErrorKind::Resolve => LowerErrorKind::Resolve,
            ExpandErrorKind::NotProvided => LowerErrorKind::NotProvided,
            ExpandErrorKind::NotDefined => LowerErrorKind::NotDefined,
            ExpandErrorKind::NoConstructor => LowerErrorKind::NoConstructor,
            ExpandErrorKind::Ambiguous => LowerErrorKind::Ambiguous,
            ExpandErrorKind::Unsupported => LowerErrorKind::Unsupported,
            ExpandErrorKind::Transformer => LowerErrorKind::Transformer,
            ExpandErrorKind::Phase => LowerErrorKind::Phase,
            ExpandErrorKind::NotAForm => LowerErrorKind::NotAForm,
            ExpandErrorKind::UnknownIntrinsic => LowerErrorKind::UnknownIntrinsic,
            ExpandErrorKind::UnknownHost => LowerErrorKind::UnknownHost,
            ExpandErrorKind::Arity => LowerErrorKind::Arity,
            ExpandErrorKind::Label => LowerErrorKind::Label,
            ExpandErrorKind::Language => LowerErrorKind::Language,
            ExpandErrorKind::Arena(error) => LowerErrorKind::Arena(error),
        };
        Self { kind, start: error.start, end: error.end }
    }
}

/// Native ragwort has no keywords of its own. Its forms are the [core forms](ragwort_expander::forms).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoKeyword {}

/// A top-level form, classified by [`Lowerer::head`] after the macro uses at its head are expanded.
enum Head {
    Define(Stx),
    DefineSyntax(Stx),
    Struct(Stx),
    Require(Stx),
    Provide(Stx),
    Begin(Vec<Stx>),
    Expr(Stx),
}

/// A top-level form whose names are bound, and whose expressions are not lowered yet.
enum Scanned<'gc> {
    /// A definition of `id` as `value`. `private` is the variable's slot if a macro introduced `id`. The module does not bind such a
    /// variable by name.
    Define { id: Stx, value: Stx, private: Option<u32> },
    Struct(Stx),
    Provide(Stx),
    Expr(Stx),
    /// An item that is lowered and declared already.
    Declared(Item<'gc>),
}

/// Lowers the top-level forms of a module's native files. [`Lowerer::declare`] lowers each form to
/// [`Item`]s and declares them in the module's builder.
pub struct Lowerer<'a, 'gc> {
    /// The state of the expander. See [`Engine`]. Its `module` is the module's builder only while [`Lowerer::declare`] runs, and an
    /// empty builder otherwise.
    engine: Engine<'a, 'gc, NoKeyword>,
    /// The index of the top-level form being lowered.
    form: u32,
    /// Whether the expression being lowered is the transformer of a macro. It runs while the module is being lowered.
    transformer: bool,
}

impl<'a, 'gc> Deref for Lowerer<'a, 'gc> {
    type Target = Engine<'a, 'gc, NoKeyword>;

    fn deref(&self) -> &Self::Target {
        &self.engine
    }
}

impl DerefMut for Lowerer<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.engine
    }
}

impl<'a, 'gc> Host<'a, 'gc> for Lowerer<'a, 'gc> {
    type Keyword = NoKeyword;

    fn expand(&mut self, stx: Stx) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let (items, tail) = match self.engine.tree.view(stx)? {
            View::Id => return self.reference(stx),
            View::Datum(value) => return Ok(Step::Done(Core::Quote(value))),
            View::Vector(_) => return Ok(Step::Done(Core::Quote(self.strip(stx)?))),
            View::List(items, tail) => (items, tail),
        };
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        let Some(&head) = items.first().filter(|&&head| self.is_id(head)) else { return Err(self.error(ExpandErrorKind::NotAForm, stx)) };
        match self.resolve(head)? {
            Binding::Core(form) => self.core_form(form, stx, items, None),
            Binding::Macro(macro_index) => Ok(Step::Tail(Call::Expr(self.expand_macro(macro_index, stx)?))),
            _ => Err(self.error(ExpandErrorKind::NotAForm, stx)),
        }
    }

    fn assign(&mut self, id: Stx, value: Stx) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Slot(slot) if !self.by_name(id, slot) => {
                self.engine.module.assign(slot).map_err(|error| self.module_error(error, id))?;
                self.engine.module.place(slot, self.form, None)
            }
            Binding::Macro(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
            Binding::Import(import) if !self.imported_by_name(id, import) => return Err(self.error(ExpandErrorKind::Immutable, id)),
            _ if !self.is_own(id)? => return Err(self.error(ExpandErrorKind::Unbound, id)),
            // The compiler resolves any other name.
            _ => {
                let (name, span) = self.spanned(id);
                return Self::expr(value, move |_, value| Ok(Step::Done(Core::SetGlobal(name, Box::new(value), span))));
            }
        };
        Self::expr(value, move |_, value| Ok(Step::Done(Core::Set(place, Box::new(value)))))
    }
}

impl<'a, 'gc> Lowerer<'a, 'gc> {
    /// Creates a lowerer. Names are interned in `symbols`.
    /// An `%intrinsic` can name an [internal intrinsic](ragwort_vm::Intrinsic::is_internal) only if `internals` is true.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, internals: bool) -> Result<Self, LowerError> {
        let mut engine = Engine::new(mc, symbols, ModuleBuilder::new(Value::FALSE, &[]), &[], None, None, None, true, module::CORE)?;
        engine.internals = internals;
        Ok(Self { engine, form: 0, transformer: false })
    }

    /// Lowers `node`, a top-level form from the reader, and declares what it defines in `builder`. `resolver` finds the modules that the form requires.
    /// Returns the items of the form. `first` is the index of the first of them among the module's top-level forms.
    ///
    /// A form is one item, except in two cases. A `%define-syntax` has no item. A `%begin` has the items of its forms.
    ///
    /// An item refers to module-level bindings by name: the names that it defines, requires, provides and uses. The module builder resolves those names.
    pub fn declare(&mut self, builder: &mut ModuleBuilder<'gc>, resolver: &mut dyn Resolver<'gc>, node: Syntax<'gc>, first: u32) -> Result<Vec<Item<'gc>>, LowerError> {
        // The expander works on the module's builder until the form is lowered.
        std::mem::swap(&mut self.engine.module, builder);
        let items = self.declare_form(resolver, node, first);
        std::mem::swap(&mut self.engine.module, builder);
        items
    }

    /// Records which names the module's syntax refers to. Call it with the module's builder after every form is declared, and before the builder is
    /// finished. Then pass the finished module to [`Sealed::patch`]. See [`Engine::seal`].
    pub fn seal(&mut self, builder: &mut ModuleBuilder<'gc>) -> Sealed<'gc> {
        std::mem::swap(&mut self.engine.module, builder);
        let sealed = self.engine.seal();
        std::mem::swap(&mut self.engine.module, builder);
        sealed
    }

    fn declare_form(&mut self, resolver: &mut dyn Resolver<'gc>, node: Syntax<'gc>, first: u32) -> Result<Vec<Item<'gc>>, LowerError> {
        let mc = self.engine.mc;
        // Every definition of the form is bound before any expression of the form is lowered. So the definitions that one macro use makes can refer to each other.
        let mut queue = vec![self.read(node)?];
        let mut scanned = Vec::new();
        while let Some(form) = queue.pop() {
            let index = self.index(first, scanned.len(), form)?;
            match self.head(form)? {
                Head::Begin(forms) => queue.extend(forms.into_iter().rev()),
                Head::DefineSyntax(form) => {
                    self.transformer = true;
                    let defined = self.define_syntax_now(form);
                    self.transformer = false;
                    let (id, macro_index) = defined?;
                    self.bind_macro(id, macro_index, index)?;
                }
                Head::Define(form) => {
                    let &[_, id, value] = self.proper(form)?.as_slice() else { return Err(self.error(ExpandErrorKind::BadSyntax, form).into()) };
                    if !self.is_id(id) {
                        return Err(self.error(ExpandErrorKind::BadSyntax, id).into());
                    }
                    let mut private = None;
                    if self.engine.tree.scopes_of(id).map_err(|error| self.error(error, id))? != self.engine.top {
                        let (name, _) = self.spanned(id);
                        let slot = self.engine.module.define_private(name, index).map_err(|error| self.module_error(error, id))?;
                        self.bind(id, Binding::Slot(slot))?;
                        private = Some(slot);
                    }
                    scanned.push(Scanned::Define { id, value, private });
                }
                Head::Require(form) => {
                    let mut requires = Vec::new();
                    for spec in self.proper(form)?.into_iter().skip(1) {
                        requires.push(Require { spec: self.spec(spec)?, span: self.engine.tree.span(spec) });
                    }
                    // A require is declared at once, so the forms after it can use what it imports.
                    let item = Item::Require(requires);
                    self.engine.module.declare(mc, resolver, index, &item).map_err(|(error, span)| LowerError::declared(error, span))?;
                    scanned.push(Scanned::Declared(item));
                }
                Head::Struct(form) => scanned.push(Scanned::Struct(form)),
                Head::Provide(form) => scanned.push(Scanned::Provide(form)),
                Head::Expr(form) => scanned.push(Scanned::Expr(form)),
            }
        }
        let mut items = Vec::with_capacity(scanned.len());
        for (offset, scanned) in scanned.into_iter().enumerate() {
            self.form = first + u32::try_from(offset).expect("the index was checked");
            let item = match scanned {
                Scanned::Declared(item) => {
                    items.push(item);
                    continue;
                }
                Scanned::Define { id, value, private: None } => {
                    let (name, span) = self.spanned(id);
                    Item::Define(name, span, self.expand_now(value)?)
                }
                Scanned::Define { value, private: Some(slot), .. } => Item::Expr(Core::Set(Place::Slot { slot, checked: false }, Box::new(self.expand_now(value)?))),
                Scanned::Struct(form) => Item::Struct(self.struct_form(form)?),
                Scanned::Provide(form) => {
                    let mut provides = Vec::new();
                    for spec in self.proper(form)?.into_iter().skip(1) {
                        self.provide_spec(spec, &mut provides)?;
                    }
                    Item::Provide(provides)
                }
                Scanned::Expr(form) => Item::Expr(self.expand_now(form)?),
            };
            self.engine.module.declare(mc, resolver, self.form, &item).map_err(|(error, span)| LowerError::declared(error, span))?;
            items.push(item);
        }
        Ok(items)
    }

    /// Returns the index of the top-level form that is `offset` forms after the form with index `first`. `at` is where an error is reported.
    fn index(&self, first: u32, offset: usize, at: Stx) -> Result<u32, ExpandError> {
        u32::try_from(offset).ok().and_then(|offset| first.checked_add(offset)).ok_or_else(|| self.error(OutOfMemory, at))
    }

    /// Classifies `form`: a definition of a variable or a macro, a `%struct`, a `%require`, a `%provide`, a `%begin`, or
    /// an expression. Macro uses at the head of `form` are expanded first.
    fn head(&mut self, mut form: Stx) -> Result<Head, ExpandError> {
        loop {
            let (head, alone) = match self.engine.tree.view(form)? {
                View::Id => (form, true),
                View::List(items, None) if items.first().is_some_and(|&head| self.is_id(head)) => (items[0], false),
                _ => return Ok(Head::Expr(form)),
            };
            form = match self.resolve(head)? {
                Binding::Macro(macro_index) => self.expand_macro(macro_index, form)?,
                _ if alone => return Ok(Head::Expr(form)),
                Binding::Core(CoreForm::Define) => return Ok(Head::Define(form)),
                Binding::Core(CoreForm::DefineSyntax) => return Ok(Head::DefineSyntax(form)),
                Binding::Core(CoreForm::Struct) => return Ok(Head::Struct(form)),
                Binding::Core(CoreForm::Require) => return Ok(Head::Require(form)),
                Binding::Core(CoreForm::Provide) => return Ok(Head::Provide(form)),
                Binding::Core(CoreForm::Begin) => return Ok(Head::Begin(self.proper(form)?[1..].to_vec())),
                _ => return Ok(Head::Expr(form)),
            };
        }
    }

    /// Returns whether `slot` is the module variable that the module binds to the name of `id`. A variable that a macro's output
    /// defines is not bound by name.
    fn by_name(&self, id: Stx, slot: u32) -> bool {
        let (name, _) = self.spanned(id);
        matches!(self.engine.module.binding(name), Some(module::Binding::Slot(bound)) if bound == slot)
    }

    /// Returns whether `import` is what the module binds to the name of `id`.
    fn imported_by_name(&self, id: Stx, import: module::Import<'gc>) -> bool {
        let (name, _) = self.spanned(id);
        matches!(self.engine.module.binding(name), Some(module::Binding::Import(bound)) if bound == import)
    }

    /// Lowers a reference to the variable that the identifier `id` names.
    fn reference(&mut self, id: Stx) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        let (name, span) = self.spanned(id);
        Ok(Step::Done(match self.resolve(id)? {
            Binding::Local(var) => Core::Ref(Place::Local(var)),
            Binding::Macro(macro_index) => return Ok(Step::Tail(Call::Expr(self.expand_macro(macro_index, id)?))),
            Binding::Slot(slot) if !self.by_name(id, slot) => Core::Ref(self.engine.module.place(slot, self.form, None)),
            // A transformer runs before the module exists, so the compiler cannot resolve its names. An import already has its value.
            // An import that the module does not bind by this name comes from the module of a macro that introduced `id`.
            Binding::Import(import) if self.transformer || !self.imported_by_name(id, import) => {
                import.usable(self.engine.mc).map_err(|error| self.import_error(error, id))?;
                Core::Import(import)
            }
            Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
            _ if !self.is_own(id)? => return Err(self.error(ExpandErrorKind::Unbound, id)),
            // The compiler resolves any other name to a module variable or an import.
            _ => Core::Global(name, span),
        }))
    }

    /// Parses the `%struct` form `form` into a struct declaration.
    /// The form has the syntax of Scheme's `struct` and defines the same bindings. See [`structs`].
    /// It is written `(%struct name (field ...) option ...)`. A subtype puts the supertype's name
    /// before the fields: `(%struct name super (field ...) option ...)`.
    fn struct_form(&mut self, form: Stx) -> Result<structs::Form<'gc>, ExpandError> {
        let bad = ExpandErrorKind::BadSyntax;
        let parts = self.proper(form)?;
        let mut rest = parts[1..].iter().copied();
        let Some(name) = rest.next().filter(|&part| self.is_id(part)) else { return Err(self.error(bad, form)) };
        let Some(mut next) = rest.next() else { return Err(self.error(bad, form)) };
        let mut parent = None;
        if self.is_id(next) {
            parent = Some(next);
            next = rest.next().ok_or_else(|| self.error(bad, form))?;
        }
        // The fields that the form declares. Each entry is the field's name and whether the field is mutable.
        let mut own: Vec<(Stx, bool)> = Vec::new();
        for spec in self.proper(next)? {
            if self.is_id(spec) {
                own.push((spec, false));
                continue;
            }
            let written = self.proper(spec)?;
            let mut options = written.iter().copied();
            let Some(id) = options.next().filter(|&part| self.is_id(part)) else { return Err(self.error(bad, spec)) };
            if !options.all(|at| self.keyword_name(at).as_deref() == Some("mutable")) {
                return Err(self.error(bad, spec));
            }
            own.push((id, written.len() > 1));
        }
        self.distinct(&own.iter().map(|&(id, _)| id).collect::<Vec<_>>())?;
        let (mut constructors, mut flags) = (Vec::new(), TypeFlags::empty());
        while let Some(at) = rest.next() {
            match self.keyword_name(at).as_deref() {
                Some("mutable") => own.iter_mut().for_each(|(_, mutable)| *mutable = true),
                Some("identity-eq?") => flags |= TypeFlags::IDENTITY,
                Some("sealed") => flags |= TypeFlags::SEALED,
                Some("transparent") => {}
                Some("constructor-name" | "extra-constructor-name") => {
                    let Some(id) = rest.next().filter(|&part| self.is_id(part)) else { return Err(self.error(bad, at)) };
                    constructors.push(id);
                }
                _ => return Err(self.error(bad, at)),
            }
        }
        Ok(structs::Form {
            name: self.spanned(name),
            span: self.engine.tree.span(form),
            parent: parent.map(|parent| self.spanned(parent)),
            fields: own.iter().map(|&(id, mutable)| Declaration { name: self.spanned(id).0, mutable }).collect(),
            flags,
            constructors: constructors.into_iter().map(|id| self.spanned(id)).collect(),
        })
    }

    /// Returns the name of the keyword `stx`, or `None` if `stx` is not a keyword.
    fn keyword_name(&self, stx: Stx) -> Option<String> {
        let mc = self.engine.mc;
        self.engine.tree.keyword(stx).map(|keyword| chars(&self.engine.strings, keyword.symbol(mc).name(mc)).collect::<String>())
    }

    /// Returns the symbol of the identifier `id` and its span.
    fn spanned(&self, id: Stx) -> (Value<'gc>, SyntaxSpan<'gc>) {
        (self.engine.tree.symbol(id).expect("an identifier").value(self.engine.mc), self.engine.tree.span(id))
    }

    /// Parses the require spec `spec`. The spec is written with its filters outermost first, around the module's name.
    /// The returned filters are in the order in which they apply, innermost first.
    fn spec(&mut self, mut spec: Stx) -> Result<RequireSpec<SyntaxSpan<'gc>>, ExpandError> {
        let mut filters = Vec::new();
        loop {
            if let Some(module) = self.text(spec) {
                filters.reverse();
                return Ok(RequireSpec { module, at: self.engine.tree.span(spec), filters });
            }
            let items = self.proper(spec)?;
            let Some((&head, args)) = items.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, spec)) };
            let word = if self.is_id(head) {
                self.text(head)
            } else {
                None
            };
            let (filter, inner) = match (word.as_deref(), args) {
                (Some("only-in"), &[inner, ref names @ ..]) => (Filter::Only(self.identifiers(names)?), inner),
                (Some("except-in"), &[inner, ref names @ ..]) => (Filter::Except(self.identifiers(names)?), inner),
                (Some("prefix-in"), &[prefix, inner]) => (Filter::Prefix(self.identifier(prefix)?), inner),
                (Some("rename-in"), &[inner, ref renames @ ..]) => {
                    let mut pairs = Vec::with_capacity(renames.len());
                    for &rename in renames {
                        let (old, new) = self.pair_of_names(rename)?;
                        pairs.push((old, new, self.engine.tree.span(rename)));
                    }
                    (Filter::Rename(pairs), inner)
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
            };
            filters.push(filter);
            spec = inner;
        }
    }

    /// Parses the provide spec `spec` and appends the exports that it names to `out`.
    fn provide_spec(&mut self, spec: Stx, out: &mut Vec<Provide<'gc>>) -> Result<(), ExpandError> {
        let span = self.engine.tree.span(spec);
        if self.is_id(spec) {
            out.push(Provide::Variable { name: self.spanned(spec).0, external: self.identifier(spec)?, span });
            return Ok(());
        }
        let items = self.proper(spec)?;
        let Some((&head, args)) = items.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, spec)) };
        let word = if self.is_id(head) {
            self.text(head)
        } else {
            None
        };
        match (word.as_deref(), args) {
            (Some("all-defined-out"), []) => out.push(Provide::AllDefined(span)),
            (Some("all-var-defined-out"), []) => out.push(Provide::AllVariables(span)),
            (Some("all-from-out"), modules) => {
                for &module in modules {
                    let Some(name) = self.text(module) else { return Err(self.error(ExpandErrorKind::BadSyntax, module)) };
                    out.push(Provide::AllFrom { module: name, span: self.engine.tree.span(module) });
                }
            }
            (Some("struct-out"), &[name, ref options @ ..]) => {
                if !self.is_id(name) {
                    return Err(self.error(ExpandErrorKind::BadSyntax, name));
                }
                let constructors = match options {
                    [] => true,
                    &[option] if self.keyword_name(option).as_deref() == Some("omit-constructor") => false,
                    _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
                };
                let (name, span) = self.spanned(name);
                out.push(Provide::Struct { name, constructors, span });
            }
            (Some("rename-out"), renames) => {
                for &rename in renames {
                    let &[inner, external] = self.proper(rename)?.as_slice() else { return Err(self.error(ExpandErrorKind::BadSyntax, rename)) };
                    if !self.is_id(inner) {
                        return Err(self.error(ExpandErrorKind::BadSyntax, inner));
                    }
                    let external = self.identifier(external)?;
                    out.push(Provide::Variable { name: self.spanned(inner).0, external, span: self.engine.tree.span(rename) });
                }
            }
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
        }
        Ok(())
    }

    /// Returns the two names in `stx`, which has the form `(old new)`.
    fn pair_of_names(&mut self, stx: Stx) -> Result<(String, String), ExpandError> {
        match *self.proper(stx)?.as_slice() {
            [old, new] => Ok((self.identifier(old)?, self.identifier(new)?)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    /// Returns the name and the span of each of the identifiers `ids`.
    fn identifiers(&mut self, ids: &[Stx]) -> Result<Vec<(String, SyntaxSpan<'gc>)>, ExpandError> {
        let mut named = Vec::with_capacity(ids.len());
        for &id in ids {
            named.push((self.identifier(id)?, self.engine.tree.span(id)));
        }
        Ok(named)
    }

    /// Returns the name of the identifier `stx`. Fails with `BadSyntax` if `stx` is not an identifier.
    fn identifier(&mut self, stx: Stx) -> Result<String, ExpandError> {
        if !self.is_id(stx) {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        Ok(self.text(stx).expect("an identifier"))
    }
}
