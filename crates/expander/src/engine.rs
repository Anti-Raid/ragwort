//! The state of one expansion, and the binding and resolution of identifiers.

use std::fmt;

use ragwort_compiler::module::{self, Import, Imports, ModuleBuilder, ModuleError, Unusable};
use ragwort_compiler::{Position, Prim, Var};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxContext, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vector, Vectors};
use ragwort_vm::{Intrinsic, Machine, Request};
use ragwort_vm::objects::{Module, ModuleFields};

use crate::forms::CoreForm;
use crate::scope::{BASE, CORE, INTERNAL, Map, Op, Scope, Set, TOP};
use crate::table::{Ambiguous, Table};
use crate::tree::{Stx, Tree, View};
use crate::{ExpandError, ExpandErrorKind};

/// The total fuel that all macro transformers of a load share. The limit stops a transformer
/// that would otherwise run forever.
pub const MACRO_FUEL: u64 = 1 << 26;

/// Identifies a binding. It is the key of `Engine::binding_values`, the cache of the binding values that
/// identifiers' syntax objects carry.
///
/// `Own(kind, number)` is a binding that exists only in this load. The kinds are:
/// - 0: a local variable. The number is its `Var` number.
/// - 1: a macro. The number is the index of its transformer in `Engine::macros`.
/// - 2: a `syntax-case` pattern variable. The number is the `Var` number of the local that holds its match.
/// - 3: a private module variable, which the module does not bind by name, such as one that a macro's output defines. The number is its slot.
///
/// `Named(module, name)` is a binding known by name. It holds the raw bits of two values:
/// - For a variable or a macro that the module being expanded binds by name, the module's name and the identifier's name.
/// - For an import, the exporting module and the name that the module itself uses for the binding.
/// - For an identifier with no binding, the name of the module being expanded and the identifier's name.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Stamp {
    Own(u8, u32),
    Named(u64, u64),
}

/// What an identifier refers to. `K` is the front end's type of keywords.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binding<'gc, K> {
    Keyword(K),
    /// A core form. See [`crate::forms`].
    Core(CoreForm),
    Local(Var),
    /// A variable of the module being expanded: its slot.
    Slot(u32),
    /// An import from a required module. Code cannot assign it.
    Import(Import<'gc>),
    /// No binding.
    Free,
    /// A macro defined in this load: the index of its transformer.
    Macro(u32),
    /// A pattern variable of `syntax-case`. Only a `syntax` template can refer to it. `var` is the local that holds
    /// its match. `depth` is the number of ellipses that the variable is under. The match is a list nested `depth` levels deep.
    Pattern { var: Var, depth: u32 },
}

/// The state of one expansion. `K` is the front end's type of keywords.
pub struct Engine<'a, 'gc, K> {
    pub mc: &'a Mutation<'gc>,
    pub strings: Strings<'a, 'gc>,
    pub symbols: Symbols<'gc>,
    pub tree: Tree<'a, 'gc>,
    keywords: Map<u64, K>,
    /// The keywords for `...` and `_` in patterns and templates, if the language has them.
    ellipsis: Option<K>,
    underscore: Option<K>,
    /// The core forms, keyed by the raw bits of the name's symbol.
    core_names: Map<u64, CoreForm>,
    /// Whether the module's source can name the core forms.
    source_core: bool,
    /// Whether an `%intrinsic` can name an [internal intrinsic](Intrinsic::is_internal).
    pub internals: bool,
    /// The intrinsics and the requests, keyed by the raw bits of the name's symbol. The table is filled when the first `%intrinsic` is expanded.
    prims: Map<u64, Prim>,
    /// The labels of loops. Loop names are apart from the names of variables.
    labels: Table<Var>,
    /// The builder of the module being expanded. An identifier that has no binding in `bindings` and
    /// lacks the `BASE` scope is looked up in it by name.
    pub module: ModuleBuilder<'gc>,
    /// The exports of the base module, keyed by the raw bits of the name's symbol. They are the base bindings: an identifier with the `BASE` scope refers to one of them.
    base_cells: Map<u64, Import<'gc>>,
    /// The bindings made in this load.
    bindings: Table<Binding<'gc, K>>,
    pub top: Set,
    pub base: Set,
    pub internal: Set,
    core: Set,
    /// The tag of the module's language. See [`ragwort_compiler::module::Export::transformer`].
    language: u8,
    /// The transformers of the load's macros, and of the macros of other modules that the load has used.
    pub macros: Vec<Value<'gc>>,
    /// For each entry of `macros`, where the macro is bound by name: a module or a module's name, and the macro's name in that module. `None` for a macro
    /// that no module binds by name.
    pub(crate) macro_names: Vec<Option<(Value<'gc>, Value<'gc>)>>,
    /// The index in `macros` of each macro of another module that the load has used, keyed by the raw bits of the module and the slot of the transformer.
    imported: Map<(u64, u32), u32>,
    /// The machine that runs the transformers. It is created when the first transformer runs, and reused for the later ones.
    pub machine: Option<Machine>,
    /// The fuel that `machine` gets when it is created. All transformers of the load share it.
    pub fuel: u64,
    /// Maps the raw bits of each syntax object created from the tree to the node it was created from.
    pub unwrapped: Map<u64, Stx>,
    /// Cache of syntax metadata, keyed by scope set and a tag for the syntax kind.
    pub metas: Map<(Set, usize), SyntaxMeta<'gc>>,
    /// Cache of the binding value for each binding that the syntax object of an identifier has referred to. See [`Stamp`].
    pub binding_values: Map<Stamp, Value<'gc>>,
    /// Cache of the syntax context for each scope set.
    pub contexts: Map<Set, SyntaxContext<'gc>>,
    /// Maps each scope of this load to the `SyntaxScope` object that represents it in syntax objects.
    /// The base module's object represents the `BASE` scope, in every load.
    pub scope_objects: Map<Scope, SyntaxScope<'gc>>,
    /// The inverse of `scope_objects`, keyed by the raw bits of the scope object.
    pub scope_numbers: Map<u64, Scope>,
}

fn key<'gc>(symbol: Symbol<'gc>, mc: &Mutation<'gc>) -> u64 {
    symbol.value(mc).to_bits()
}

/// Returns the name that the module of `import` itself uses for the imported binding.
pub(crate) fn internal_name<'gc>(mc: &Mutation<'gc>, import: Import<'gc>) -> Value<'gc> {
    AnyVector::of(import.module.names(mc)).and_then(|names| names.get(mc, import.export.slot as usize)).unwrap_or(Value::FALSE)
}

/// The binding values of the names that a module's syntax refers to, with what each name turned out to be bound to. [`Engine::seal`] creates it once the
/// module's forms are expanded.
pub struct Sealed<'gc> {
    patches: Vec<(Vector<'gc>, Patch<'gc>)>,
}

enum Patch<'gc> {
    /// The module itself binds the name.
    Own,
    /// The name is an import: the exporting module, and the name that the module uses for the binding.
    Import(Value<'gc>, Value<'gc>),
}

impl<'gc> Sealed<'gc> {
    /// Completes the binding values, now that `module` is finished. Each value then names the module that binds the name, so another module that uses
    /// one of this module's macros can find the binding.
    pub fn patch(self, mc: &Mutation<'gc>, module: Gc<'gc, Module>) {
        for (binding, patch) in self.patches {
            let (bound_in, name) = match patch {
                Patch::Own => (Value::object(mc, module), None),
                Patch::Import(exporter, name) => (exporter, Some(name)),
            };
            binding.items(mc).set(mc, 0, bound_in);
            if let Some(name) = name {
                binding.items(mc).set(mc, 1, name);
            }
        }
    }
}

impl<'a, 'gc, K: Copy + PartialEq + fmt::Debug> Engine<'a, 'gc, K> {
    /// Creates the state for expanding the module that `module` builds.
    ///
    /// - `keywords` are the names of the language's keywords. `ellipsis` and `underscore` are the keywords for `...` and `_` in
    ///   patterns and templates, if the language has them.
    /// - `base` is the language's base module, if it has one. Its exports are the base bindings, which an identifier with the `BASE`
    ///   scope refers to. The module must have run. Without a base module, such an identifier refers only to a keyword.
    /// - `source_core` says whether the module's source can name the [core forms](crate::forms). If it is false, only an identifier that the
    ///   expander or a macro from native ragwort introduced refers to one.
    /// - `language` is the tag of the module's language. A module can use the macros of its own language and the macros made of core forms.
    #[allow(clippy::too_many_arguments)]
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, module: ModuleBuilder<'gc>, keywords: &[(&str, K)], ellipsis: Option<K>, underscore: Option<K>, base: Option<Gc<'gc, Module>>, source_core: bool, language: u8) -> Result<Self, ExpandError> {
        let strings = Strings::new(mc);
        let mut core_names = Map::default();
        for (name, form) in CoreForm::NAMED {
            core_names.insert(key(symbols.intern_str(&strings, name)?, mc), form);
        }
        let keywords = keywords.iter().map(|&(name, keyword)| Ok((key(symbols.intern_str(&strings, name)?, mc), keyword))).collect::<Result<_, ragwort_types::Error>>()?;
        let abbreviations = Abbreviation::ALL.iter().map(|abbreviation| symbols.intern_str(&strings, abbreviation.name())).collect::<Result<_, _>>()?;
        let mut tree = Tree::new(mc, abbreviations);
        let top = tree.scopes.set(vec![TOP])?;
        let base_set = tree.scopes.set(vec![BASE])?;
        let internal = tree.scopes.set(vec![BASE, INTERNAL])?;
        let core = tree.scopes.set(vec![CORE])?;
        let mut base_cells = Map::default();
        let (mut scope_objects, mut scope_numbers) = (Map::default(), Map::default());
        if let Some(base) = base {
            for (name, import) in Imports::all(mc, base).unwrap_or_default().0 {
                base_cells.insert(key(symbols.intern_str(&strings, &name)?, mc), import);
            }
            scope_objects.insert(BASE, SyntaxScope::of(Value::object(mc, base)));
            scope_numbers.insert(Value::object(mc, base).to_bits(), BASE);
        }
        Ok(Self {
            mc,
            strings,
            symbols,
            tree,
            keywords,
            ellipsis,
            underscore,
            core_names,
            source_core,
            internals: false,
            prims: Map::default(),
            labels: Table::default(),
            module,
            base_cells,
            bindings: Table::default(),
            top,
            base: base_set,
            internal,
            core,
            language,
            macros: Vec::new(),
            macro_names: Vec::new(),
            imported: Map::default(),
            machine: None,
            fuel: MACRO_FUEL,
            unwrapped: Map::default(),
            metas: Map::default(),
            binding_values: Map::default(),
            contexts: Map::default(),
            scope_objects,
            scope_numbers,
        })
    }

    /// Binds `name` to `keyword` for the identifiers that [`Engine::internal`] creates. A program cannot write such an identifier.
    pub fn bind_internal(&mut self, name: &str, keyword: K) -> Result<(), ExpandError> {
        let name_key = key(self.symbols.intern_str(&self.strings, name)?, self.mc);
        Ok(self.bindings.bind(&mut self.tree.scopes, name_key, self.internal, Binding::Keyword(keyword))?)
    }

    /// Returns whether `stx` is an identifier that refers to the keyword for `...`.
    pub fn is_ellipsis(&mut self, stx: Stx) -> Result<bool, ExpandError> {
        if !self.is_id(stx) {
            return Ok(false);
        }
        Ok(match self.resolve(stx)? {
            Binding::Keyword(found) => Some(found) == self.ellipsis,
            Binding::Core(form) => form == CoreForm::Ellipsis,
            _ => false,
        })
    }

    /// Returns whether `stx` is an identifier that refers to the keyword for `_`.
    pub fn is_underscore(&mut self, stx: Stx) -> Result<bool, ExpandError> {
        if !self.is_id(stx) {
            return Ok(false);
        }
        Ok(match self.resolve(stx)? {
            Binding::Keyword(found) => Some(found) == self.underscore,
            Binding::Core(form) => form == CoreForm::Underscore,
            _ => false,
        })
    }

    pub fn error(&self, kind: impl Into<ExpandErrorKind>, stx: Stx) -> ExpandError {
        self.error_at(kind, self.tree.span(stx))
    }

    pub fn error_at(&self, kind: impl Into<ExpandErrorKind>, span: SyntaxSpan<'gc>) -> ExpandError {
        ExpandError { kind: kind.into(), start: span.start(), end: span.end() }
    }

    /// Converts `node`, a form from the reader, into the tree and adds the `TOP` scope to it.
    pub fn read(&mut self, node: Syntax<'gc>) -> Result<Stx, ExpandError> {
        let span = node.span(self.mc);
        let stx = self.tree.read(node).map_err(|error| ExpandError { kind: error.into(), start: span.start(), end: span.end() })?;
        Ok(self.tree.with(stx, TOP, Op::Add)?)
    }

    /// Returns the text of `stx` if it is an identifier or a string literal.
    pub fn text(&mut self, stx: Stx) -> Option<String> {
        let string = match self.tree.symbol(stx) {
            Some(symbol) => symbol.name(self.mc),
            None => match self.tree.view(stx).ok()? {
                View::Datum(value) => self.strings.string(value)?,
                _ => return None,
            },
        };
        Some(chars(&self.strings, string).collect())
    }

    /// Converts `error`, the reason why the import `stx` cannot be used, to an expansion error at `stx`.
    pub fn import_error(&self, error: Unusable, stx: Stx) -> ExpandError {
        let kind = match error {
            Unusable::Uninitialized => ExpandErrorKind::Unbound,
            Unusable::MatchOnly => ExpandErrorKind::NoConstructor,
        };
        self.error(kind, stx)
    }

    pub fn module_error(&self, error: ModuleError, stx: Stx) -> ExpandError {
        let kind = match error {
            ModuleError::Duplicate => ExpandErrorKind::Duplicate,
            ModuleError::Conflict => ExpandErrorKind::Conflict,
            ModuleError::NotDefined => ExpandErrorKind::NotDefined,
            ModuleError::Immutable => ExpandErrorKind::Immutable,
            ModuleError::Resolve => ExpandErrorKind::Resolve,
            ModuleError::NotProvided => ExpandErrorKind::NotProvided,
            ModuleError::Supertype | ModuleError::Struct => ExpandErrorKind::BadSyntax,
            ModuleError::OutOfMemory => OutOfMemory.into(),
        };
        self.error(kind, stx)
    }

    /// Returns `error`. If `error` has an empty span, as an out-of-memory error has, the result has the span of `stx` instead.
    pub fn placed(&self, error: ExpandError, stx: Stx) -> ExpandError {
        if error.start == error.end { self.error(error.kind, stx) } else { error }
    }

    /// Returns the binding that the identifier `id` refers to. An import of a macro is returned as the macro.
    pub fn resolve(&mut self, id: Stx) -> Result<Binding<'gc, K>, ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers resolve");
        let set = self.tree.scopes_of(id)?;
        let origin = self.origin(id, set);
        match self.resolve_name(symbol, set, origin).map_err(|Ambiguous| self.error(ExpandErrorKind::Ambiguous, id))? {
            Binding::Import(import) if import.export.transformer.is_some() => Ok(Binding::Macro(self.imported_macro(import, id)?)),
            binding => Ok(binding),
        }
    }

    /// Returns whether the identifier `id` was read from the module's own source, or made by one of the module's own macros. Any other
    /// identifier does not refer to the module's bindings by its name.
    pub fn is_own(&mut self, id: Stx) -> Result<bool, ExpandError> {
        let set = self.tree.scopes_of(id)?;
        Ok(self.tree.scopes.contains(set, TOP))
    }

    /// Returns the origin of the identifier `id`, whose scope set is `set`, if a macro of another module introduced `id`. Such an identifier lacks the
    /// `TOP` scope, which everything read from the module's own source has.
    pub fn origin(&self, id: Stx, set: Set) -> Option<Value<'gc>> {
        if self.tree.scopes.contains(set, TOP) { None } else { self.tree.origin(id) }
    }

    /// Returns the index in `macros` of the transformer of `import`, an import of a macro. `at` is the identifier that refers to the macro.
    fn imported_macro(&mut self, import: Import<'gc>, at: Stx) -> Result<u32, ExpandError> {
        let mc = self.mc;
        let imported_key = (Value::object(mc, import.module).to_bits(), import.export.slot);
        if let Some(&macro_index) = self.imported.get(&imported_key) {
            return Ok(macro_index);
        }
        if import.export.transformer.is_some_and(|language| language != module::CORE && language != self.language) {
            return Err(self.error(ExpandErrorKind::Language, at));
        }
        let items = import.module.items(mc);
        let transformer = if (import.export.slot as usize) < items.len() { items.get(import.export.slot as usize) } else { Value::UNDEFINED };
        if transformer == Value::UNDEFINED {
            return Err(self.error(ExpandErrorKind::Unbound, at));
        }
        let macro_index = u32::try_from(self.macros.len()).map_err(|_| self.error(ExpandErrorKind::Transformer, at))?;
        self.tree.scopes.charge(size_of::<((u64, u32), u32)>())?;
        self.macros.push(transformer);
        self.macro_names.push(Some((Value::object(mc, import.module), internal_name(mc, import))));
        self.imported.insert(imported_key, macro_index);
        Ok(macro_index)
    }

    /// Binds the identifier `id` to the macro with index `macro_index`, which the top-level form with index `form` defines. If `id` was read
    /// from the module's source, the module binds the macro by name, and can provide it.
    pub fn bind_macro(&mut self, id: Stx, macro_index: u32, form: u32) -> Result<(), ExpandError> {
        self.bind(id, Binding::Macro(macro_index))?;
        if self.tree.scopes_of(id)? == self.top {
            let name = self.tree.symbol(id).expect("only identifiers are bound").value(self.mc);
            self.module.define_macro(name, form, self.language, self.macros[macro_index as usize]).map_err(|error| self.module_error(error, id))?;
            self.macro_names[macro_index as usize] = Some((self.module.name(), name));
        }
        Ok(())
    }

    /// Returns what the identifier named `symbol` refers to in the module of its origin. `origin` is the binding value that a macro of that module gave the identifier.
    fn resolve_origin(&self, symbol: Symbol<'gc>, origin: Value<'gc>) -> Binding<'gc, K> {
        let mc = self.mc;
        let name_key = key(symbol, mc);
        // A symbol is the binding value of a keyword or a core form.
        if Symbol::of(origin).is_some() {
            return match (self.keywords.get(&name_key), self.core_names.get(&name_key)) {
                (Some(&keyword), _) => Binding::Keyword(keyword),
                (None, Some(&form)) => Binding::Core(form),
                (None, None) => Binding::Free,
            };
        }
        let named = AnyVector::of(origin).filter(|vector| vector.len(mc) == 2);
        let Some((module, name)) = named.and_then(|vector| Some((vector.get(mc, 0)?.downcast::<Module>(mc)?, Symbol::of(vector.get(mc, 1)?)?))) else { return Binding::Free };
        let name: String = chars(&self.strings, name.name(mc)).collect();
        match module::interface(mc, module).and_then(|interface| interface.internal(&name)) {
            Some((name, export)) => Binding::Import(Import { module, export, name }),
            None => Binding::Free,
        }
    }

    /// Returns the binding that an identifier named `symbol` with the scope set `set` refers to. `origin` is the identifier's origin, if it has one. See [`Engine::origin`].
    pub fn resolve_name(&self, symbol: Symbol<'gc>, set: Set, origin: Option<Value<'gc>>) -> Result<Binding<'gc, K>, Ambiguous> {
        let name_key = key(symbol, self.mc);
        if let Some(binding) = self.bindings.resolve(&self.tree.scopes, name_key, set)? {
            return Ok(binding);
        }
        if let Some(origin) = origin {
            return Ok(self.resolve_origin(symbol, origin));
        }
        // An identifier with the `CORE` scope refers to a core form, even if the module binds the same name.
        if self.tree.scopes.contains(set, CORE) {
            return Ok(self.core_names.get(&name_key).map_or(Binding::Free, |&form| Binding::Core(form)));
        }
        // An identifier with the `BASE` scope refers to the prelude's binding, even if the module binds the same name.
        let base = self.tree.scopes.contains(set, BASE);
        if !base && let Some(binding) = self.module.binding(symbol.value(self.mc)) {
            return Ok(match binding {
                module::Binding::Slot(slot) => Binding::Slot(slot),
                module::Binding::Import(import) => Binding::Import(import),
            });
        }
        if let Some(&keyword) = self.keywords.get(&name_key) {
            return Ok(Binding::Keyword(keyword));
        }
        if self.source_core && let Some(&form) = self.core_names.get(&name_key) {
            return Ok(Binding::Core(form));
        }
        if base && let Some(&import) = self.base_cells.get(&name_key) {
            return Ok(Binding::Import(import));
        }
        Ok(Binding::Free)
    }

    pub fn bind(&mut self, id: Stx, binding: Binding<'gc, K>) -> Result<(), ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers are bound");
        let set = self.tree.scopes_of(id)?;
        Ok(self.bindings.bind(&mut self.tree.scopes, key(symbol, self.mc), set, binding)?)
    }

    /// Allocates a local variable for the identifier `id` and binds `id` to it. If the variable is later bound to a lambda, error reports show the lambda under this name.
    pub fn local(&mut self, id: Stx) -> Result<Var, ExpandError> {
        let var = match self.tree.symbol(id) {
            Some(name) => self.module.locals().named(name.value(self.mc)),
            None => self.fresh(),
        };
        self.bind(id, Binding::Local(var))?;
        Ok(var)
    }

    pub fn fresh(&mut self) -> Var {
        self.module.locals().fresh()
    }

    /// Returns a `Duplicate` error at the second of any two `ids` that have the same name and scopes.
    pub fn distinct(&mut self, ids: &[Stx]) -> Result<(), ExpandError> {
        let mut seen = std::collections::HashSet::new();
        for &id in ids {
            let symbol = self.tree.symbol(id).expect("only identifiers are bound");
            if !seen.insert((key(symbol, self.mc), self.tree.scopes_of(id)?)) {
                return Err(self.error(ExpandErrorKind::Duplicate, id));
            }
        }
        Ok(())
    }

    /// Returns the source position of the form `stx`. Error reports use it for a call or operation expanded from the form.
    pub fn position(&self, stx: Stx) -> Option<Position<'gc>> {
        Position::of(self.mc, self.tree.span(stx))
    }

    pub fn lambda_id(&mut self) -> u32 {
        self.module.locals().lambda()
    }

    /// Returns `stxs` with `scope` added to each.
    pub fn scoped(&mut self, stxs: &[Stx], scope: Scope) -> Result<Vec<Stx>, ExpandError> {
        Ok(stxs.iter().map(|&stx| self.tree.with(stx, scope, Op::Add)).collect::<Result<_, _>>()?)
    }

    pub fn strip(&mut self, stx: Stx) -> Result<Value<'gc>, ExpandError> {
        self.tree.strip(stx).map_err(|error| self.error(error, stx))
    }

    pub fn is_id(&self, stx: Stx) -> bool {
        self.tree.symbol(stx).is_some()
    }

    /// Returns the items of `stx`, or a `BadSyntax` error if `stx` is not a proper list.
    pub fn proper(&mut self, stx: Stx) -> Result<Vec<Stx>, ExpandError> {
        match self.tree.view(stx)? {
            View::List(items, None) => Ok(items),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    pub fn symbol(&self, name: &str) -> Result<Symbol<'gc>, ExpandError> {
        Ok(self.symbols.intern_str(&self.strings, name)?)
    }

    /// Creates an identifier named `name` with only the `BASE` scope and the span of `at`. It refers to the base binding of `name`, which code read from source cannot shadow.
    pub fn introduce(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.base, span)?)
    }

    /// Records which names the module's syntax refers to, so the module keeps their bindings for the macros that it exports. Call it after every
    /// form of the module is expanded, and before the module's builder is finished. Then pass the finished module to [`Sealed::patch`].
    pub fn seal(&mut self) -> Sealed<'gc> {
        let mc = self.mc;
        let own = self.module.name().to_bits();
        let mut patches = Vec::new();
        for (stamp, &value) in &self.binding_values {
            let Stamp::Named(bound_in, _) = *stamp else { continue };
            let Some(binding) = Vectors::new(mc).mutable(value).filter(|_| bound_in == own) else { continue };
            let name = binding.items(mc).get(1);
            let patch = match self.module.binding(name) {
                _ if self.module.defines_macro(name) => Patch::Own,
                Some(module::Binding::Slot(_)) => Patch::Own,
                Some(module::Binding::Import(import)) => Patch::Import(Value::object(mc, import.module), internal_name(mc, import)),
                None => continue,
            };
            if matches!(patch, Patch::Own) {
                self.module.refer(name);
            }
            patches.push((binding, patch));
        }
        Sealed { patches }
    }

    /// Finishes the module and returns it. Call it after every form of the module is compiled.
    pub fn finish(mut self) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let sealed = self.seal();
        let module = self.module.finish(self.mc)?;
        sealed.patch(self.mc, module);
        Ok(module)
    }

    /// Creates an identifier named `name` with only the `CORE` scope and the span of `at`. If `name` is the name of a core form, the identifier refers to
    /// that form in a module of any language.
    pub fn core_id(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.core, span)?)
    }

    /// Binds the loop name `id` to `label`.
    pub fn bind_label(&mut self, id: Stx, label: Var) -> Result<(), ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers name loops");
        let set = self.tree.scopes_of(id)?;
        Ok(self.labels.bind(&mut self.tree.scopes, key(symbol, self.mc), set, label)?)
    }

    /// Returns the label of the loop that the identifier `id` names, or `None` if no loop of that name is around `id`.
    pub fn label(&mut self, id: Stx) -> Result<Option<Var>, ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers name loops");
        let set = self.tree.scopes_of(id)?;
        self.labels.resolve(&self.tree.scopes, key(symbol, self.mc), set).map_err(|Ambiguous| self.error(ExpandErrorKind::Ambiguous, id))
    }

    /// Returns the intrinsic or the request that the identifier `id` names.
    pub fn primitive(&mut self, id: Stx) -> Result<Option<Prim>, ExpandError> {
        if self.prims.is_empty() {
            for &intrinsic in Intrinsic::ALL {
                self.prims.insert(key(self.symbols.intern_str(&self.strings, intrinsic.name())?, self.mc), Prim::Intrinsic(intrinsic));
            }
            for &request in Request::ALL {
                self.prims.insert(key(self.symbols.intern_str(&self.strings, request.name())?, self.mc), Prim::Request(request));
            }
        }
        let symbol = self.tree.symbol(id).expect("only identifiers name intrinsics");
        Ok(self.prims.get(&key(symbol, self.mc)).copied())
    }

    /// Creates an identifier for the form named `name` that only the expander generates, with the span of `at`. A
    /// program cannot write such an identifier: `struct-ref` in a program is an unbound variable.
    pub fn internal(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.internal, span)?)
    }
}
