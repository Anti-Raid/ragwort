//! The expander. It translates Scheme syntax into the compiler's core forms. Hygiene uses sets of scopes,
//! as in Racket. A binding form adds a fresh scope to the identifiers it binds and to its body.
//! Each macro step flips a fresh scope on its input and on its output. The flip distinguishes the syntax that the macro introduces
//! from the syntax that it was given. An identifier refers to the binding of its name whose
//! scope set is the largest subset of the identifier's own scope set.



use ragwort_compiler::module::{self, Filter, Import, Imports, ModuleBuilder, ModuleError, RequireSpec, Resolver, SpecError, Unusable};
use ragwort_compiler::steps::{self, Step};
use ragwort_compiler::structs::Declared;
use ragwort_compiler::{Core, Lambda, Place, Position, Prim, Var};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxContext, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_vm::{HostDef, Intrinsic, Machine};
use ragwort_vm::objects::Module;

use crate::scope::{BASE, INTERNAL, Map, Op, Scope, Set, TOP};
use crate::tree::{Stx, Tree, View};
use crate::{ExpandError, ExpandErrorKind};

/// The total fuel that all macro transformers of a load share. The limit stops a transformer
/// that would otherwise run forever.
const MACRO_FUEL: u64 = 1 << 26;

/// The forms that the expander handles directly.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Form {
    Quote,
    If,
    Lambda,
    Define,
    Set,
    Begin,
    Let,
    Letrec,
    Require,
    Provide,
    DefineSyntax,
    LetSyntax,
    LetrecSyntax,
    SyntaxCase,
    Syntax,
    /// `(quote-syntax datum)`: returns `datum` as a syntax object, unchanged. A pattern variable in `datum` is not replaced by its match.
    QuoteSyntax,
    /// `quasisyntax`, `unsyntax` and `unsyntax-splicing`, which are not supported yet.
    Unsupported,
    Struct,
    /// `(struct-ref s type k)`: reads field `k` of `s`, an instance of `type`. Only the expander
    /// generates this form, for `match` and `struct-copy`. See [`Expander::internal`].
    StructRef,
}

/// The built-in macros, which are written in Rust.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Macro {
    LetStar,
    LetValues,
    LetStarValues,
    DefineValues,
    And,
    Or,
    When,
    Unless,
    Cond,
    Case,
    Do,
    Quasiquote,
    Guard,
    WithMark,
    SyntaxRules,
    WithSyntax,
    Match,
    StructCopy,
    /// A named `let`. No keyword is bound to this macro. The `let` form expands to it when its first argument is an identifier.
    NamedLet,
}

/// Auxiliary keywords, which have a meaning only inside other forms.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Aux {
    Else,
    Arrow,
    Unquote,
    UnquoteSplicing,
    Underscore,
    Ellipsis,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Keyword {
    Form(Form),
    Macro(Macro),
    Aux(Aux),
}

const KEYWORDS: [(&str, Keyword); 45] = [
    ("struct-copy", Keyword::Macro(Macro::StructCopy)),
    ("struct", Keyword::Form(Form::Struct)),
    ("quote", Keyword::Form(Form::Quote)),
    ("if", Keyword::Form(Form::If)),
    ("lambda", Keyword::Form(Form::Lambda)),
    ("define", Keyword::Form(Form::Define)),
    ("set!", Keyword::Form(Form::Set)),
    ("begin", Keyword::Form(Form::Begin)),
    ("let", Keyword::Form(Form::Let)),
    ("letrec", Keyword::Form(Form::Letrec)),
    ("letrec*", Keyword::Form(Form::Letrec)),
    ("require", Keyword::Form(Form::Require)),
    ("provide", Keyword::Form(Form::Provide)),
    ("define-syntax", Keyword::Form(Form::DefineSyntax)),
    ("let-syntax", Keyword::Form(Form::LetSyntax)),
    ("letrec-syntax", Keyword::Form(Form::LetrecSyntax)),
    ("syntax-case", Keyword::Form(Form::SyntaxCase)),
    ("syntax", Keyword::Form(Form::Syntax)),
    ("quote-syntax", Keyword::Form(Form::QuoteSyntax)),
    ("quasisyntax", Keyword::Form(Form::Unsupported)),
    ("unsyntax", Keyword::Form(Form::Unsupported)),
    ("unsyntax-splicing", Keyword::Form(Form::Unsupported)),
    ("syntax-rules", Keyword::Macro(Macro::SyntaxRules)),
    ("match", Keyword::Macro(Macro::Match)),
    ("with-syntax", Keyword::Macro(Macro::WithSyntax)),
    ("let*", Keyword::Macro(Macro::LetStar)),
    ("let-values", Keyword::Macro(Macro::LetValues)),
    ("let*-values", Keyword::Macro(Macro::LetStarValues)),
    ("define-values", Keyword::Macro(Macro::DefineValues)),
    ("and", Keyword::Macro(Macro::And)),
    ("or", Keyword::Macro(Macro::Or)),
    ("when", Keyword::Macro(Macro::When)),
    ("unless", Keyword::Macro(Macro::Unless)),
    ("cond", Keyword::Macro(Macro::Cond)),
    ("case", Keyword::Macro(Macro::Case)),
    ("do", Keyword::Macro(Macro::Do)),
    ("quasiquote", Keyword::Macro(Macro::Quasiquote)),
    ("guard", Keyword::Macro(Macro::Guard)),
    ("with-continuation-mark", Keyword::Macro(Macro::WithMark)),
    ("else", Keyword::Aux(Aux::Else)),
    ("=>", Keyword::Aux(Aux::Arrow)),
    ("unquote", Keyword::Aux(Aux::Unquote)),
    ("unquote-splicing", Keyword::Aux(Aux::UnquoteSplicing)),
    ("_", Keyword::Aux(Aux::Underscore)),
    ("...", Keyword::Aux(Aux::Ellipsis)),
];

/// Identifies a binding. It is the key of `Expander::binding_values`, the cache of the binding values that
/// identifiers' syntax objects carry.
///
/// `Own(kind, number)` is a binding that exists only in this load. The kinds are:
/// - 0: a local variable. The number is its `Var` number.
/// - 1: a macro. The number is the index of its transformer in `Expander::macros`.
/// - 2: a `syntax-case` pattern variable. The number is the `Var` number of the local that holds its match.
/// - 3: a private module variable, which the module does not bind by name, such as one that a macro's output defines. The number is its slot.
///
/// `Named(module, name)` is a binding known by name. It holds the raw bits of a module's name and of a variable's name:
/// - For a module variable bound by name, the module being expanded and the identifier's name.
/// - For an import, the exporting module and the name of the export.
/// - For an identifier with no binding, the module being expanded and the identifier's name.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Stamp {
    Own(u8, u32),
    Named(u64, u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Binding<'gc> {
    Keyword(Keyword),
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

/// The error for an identifier with two candidate bindings, where neither binding's scope set is a subset of the other's.
pub(crate) struct Ambiguous;

/// An item of a body: a variable definition or an expression. The items keep their source order.
enum Item {
    /// A definition: the variable, and the expression for its value.
    Define(Var, Stx),
    Expr(Stx),
}

/// The state of scanning a body. `stx` is the form that owns the body. `queue` holds the forms still to scan, in reverse order. `items` holds the definitions and expressions found so far. `defined` holds the identifiers of the variables defined. `names` holds those and the identifiers of the macros defined.
struct Scan {
    stx: Stx,
    queue: Vec<Stx>,
    items: Vec<Item>,
    defined: Vec<Stx>,
    names: Vec<Stx>,
}

/// The next step of expanding an expression. See [`steps`]. Each call produces a [`Core`] form.
pub(crate) type Ex<'a, 'gc> = Step<'a, Expander<'a, 'gc>, Call<'a, 'gc>, Core<'gc>, ExpandError>;

/// A call that the step driver runs for the expander.
pub(crate) enum Call<'a, 'gc> {
    /// Expands the expression.
    Expr(Stx),
    /// Runs the function, which returns the next step.
    Run(Work<'a, 'gc>),
}

/// A deferred part of an expansion: a function that takes the expander and returns the next step.
pub(crate) type Work<'a, 'gc> = Box<dyn FnOnce(&mut Expander<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a>;

/// A form at the top level or in a body, classified by [`Expander::head`] after the macro uses at its head are expanded.
enum Head {
    Define(Stx),
    DefineSyntax(Stx),
    Require(Stx),
    Provide(Stx),
    Begin(Vec<Stx>),
    Struct(Stx),
    Expr(Stx),
}

/// A declared top-level form of a module's Scheme source. Its definitions are already bound. Pass it to [`Expander::lower`].
pub struct Top(TopForm);

enum TopForm {
    /// A definition: the slot of the module variable, and the expression for its value.
    Define(u32, Stx),
    /// A definition of a keyword procedure: the slot of its variable, and its `lambda` expression.
    DefineKeyword { procedure: u32, lambda: Stx },
    Struct(Declared),
    Expr(Stx),
}

/// Expands the Scheme files of a module into a [`ModuleBuilder`], which other front ends can also add to.
/// First call [`Expander::declare`] on each form of the files. Then call [`Expander::provide`] and start
/// the module. Then call [`Expander::lower`] on each [`Top`], in order. Finally call [`Expander::finish`].
pub struct Expander<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
    pub(crate) strings: Strings<'a, 'gc>,
    symbols: Symbols<'gc>,
    pub(crate) tree: Tree<'a, 'gc>,
    keywords: Map<u64, Keyword>,
    /// The builder of the module being expanded. An identifier that has no binding in `bindings` and
    /// lacks the `BASE` scope is looked up in the builder by name.
    pub(crate) builder: ModuleBuilder<'gc>,
    /// The prelude's exports, keyed by the raw bits of the name's symbol. They are the base bindings: an identifier with the `BASE` scope refers to one of them.
    base_cells: Map<u64, Import<'gc>>,
    /// The `provide` forms declared so far. [`Expander::provide`] processes them after every form is declared, so they can name a definition anywhere in the module.
    provides: Vec<Stx>,
    /// The index of the top-level form being expanded.
    pub(crate) form: u32,
    /// The slot of the module variable that the form defines, if the form defines it as a `lambda`.
    pub(crate) defining: Option<u32>,
    /// The bindings made in this load. Each entry is a binding and the scope set of the identifier that was bound. The key is the newest
    /// scope of that set and the raw bits of the name's symbol. So every binding that an identifier can refer to is stored under one of the identifier's own scopes.
    bindings: Map<(Scope, u64), Vec<(Set, Binding<'gc>)>>,
    /// For each name, the scopes that `bindings` has entries for the name under. When a name has fewer
    /// such scopes than an identifier has scopes, the lookup goes through this list instead of the identifier's scopes.
    bound_in: Map<u64, Vec<Scope>>,
    top: Set,
    base: Set,
    internal: Set,
    /// The transformers of the load's macros.
    pub(crate) macros: Vec<Value<'gc>>,
    /// The machine that runs the transformers. It is created when the first transformer runs, and reused for the later ones.
    pub(crate) machine: Option<Machine>,
    /// The fuel that `machine` gets when it is created. All transformers of the load share it.
    pub(crate) fuel: u64,
    /// Maps the raw bits of each syntax object created from the tree to the node it was created from.
    pub(crate) unwrapped: Map<u64, Stx>,
    /// Cache of syntax metadata, keyed by scope set and a tag for the syntax kind.
    pub(crate) metas: Map<(Set, usize), SyntaxMeta<'gc>>,
    /// Cache of the binding value for each binding that the syntax object of an identifier has referred to. See [`Stamp`].
    pub(crate) binding_values: Map<Stamp, Value<'gc>>,
    /// Cache of the syntax context for each scope set.
    pub(crate) contexts: Map<Set, SyntaxContext<'gc>>,
    /// Maps each scope of this load to the `SyntaxScope` object that represents it in syntax objects.
    /// The prelude's module object represents the `BASE` scope, in every load.
    pub(crate) scope_objects: Map<Scope, SyntaxScope<'gc>>,
    /// The inverse of `scope_objects`, keyed by the raw bits of the scope object.
    pub(crate) scope_numbers: Map<u64, Scope>,
}

fn key<'gc>(symbol: Symbol<'gc>, mc: &Mutation<'gc>) -> u64 {
    symbol.value(mc).to_bits()
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// Creates an expander for the Scheme files of the module named `name`. `hosts` are the host functions that the module's native files
    /// call. The module implicitly requires `prelude`, then each module of `implicit` in order. An export of a later
    /// module shadows the same name from an earlier one. `prelude` must have run. Its exports are also the base
    /// bindings.
    pub fn new(
        mc: &'a Mutation<'gc>,
        symbols: Symbols<'gc>,
        prelude: Gc<'gc, Module>,
        name: &str,
        hosts: &'static [HostDef],
        implicit: &[Gc<'gc, Module>],
    ) -> Result<Self, ExpandError> {
        let strings = Strings::new(mc);
        let mut builder = ModuleBuilder::new(symbols.intern_str(&strings, name)?.value(mc), hosts);
        for &module in std::iter::once(&prelude).chain(implicit) {
            builder.require_implicitly(mc, symbols, module).map_err(|_| OutOfMemory)?;
        }
        let keywords = KEYWORDS.iter().map(|&(name, keyword)| Ok((key(symbols.intern_str(&strings, name)?, mc), keyword))).collect::<Result<_, ragwort_types::Error>>()?;
        let abbreviations = Abbreviation::ALL.iter().map(|abbreviation| symbols.intern_str(&strings, abbreviation.name())).collect::<Result<_, _>>()?;
        let mut tree = Tree::new(mc, abbreviations);
        let top = tree.scopes.set(vec![TOP])?;
        let base = tree.scopes.set(vec![BASE])?;
        let internal = tree.scopes.set(vec![BASE, INTERNAL])?;
        let struct_ref = key(symbols.intern_str(&strings, "struct-ref")?, mc);
        let exports = Imports::all(mc, prelude).unwrap_or_default().0;
        let base_cells = exports.into_iter().map(|(name, import)| Ok((key(symbols.intern_str(&strings, &name)?, mc), import))).collect::<Result<_, ragwort_types::Error>>()?;
        Ok(Self {
            mc,
            strings,
            symbols,
            tree,
            keywords,
            builder,
            base_cells,
            provides: Vec::new(),
            form: 0,
            defining: None,
            bindings: [((INTERNAL, struct_ref), vec![(internal, Binding::Keyword(Keyword::Form(Form::StructRef)))])].into_iter().collect(),
            bound_in: [(struct_ref, vec![INTERNAL])].into_iter().collect(),
            top,
            base,
            internal,
            macros: Vec::new(),
            machine: None,
            fuel: MACRO_FUEL,
            unwrapped: Map::default(),
            metas: Map::default(),
            binding_values: Map::default(),
            contexts: Map::default(),
            scope_objects: [(BASE, SyntaxScope::of(Value::object(mc, prelude)))].into_iter().collect(),
            scope_numbers: [(Value::object(mc, prelude).to_bits(), BASE)].into_iter().collect(),
        })
    }

    pub(crate) fn error(&self, kind: impl Into<ExpandErrorKind>, stx: Stx) -> ExpandError {
        self.error_at(kind, self.tree.span(stx))
    }

    pub(crate) fn error_at(&self, kind: impl Into<ExpandErrorKind>, span: SyntaxSpan<'gc>) -> ExpandError {
        ExpandError { kind: kind.into(), start: span.start(), end: span.end() }
    }

    /// Returns the module's builder, which other front ends use to add to the same module.
    pub fn builder(&mut self) -> &mut ModuleBuilder<'gc> {
        &mut self.builder
    }

    /// Converts `node`, a form from the reader, into the tree and adds the `TOP` scope to it.
    fn read(&mut self, node: Syntax<'gc>) -> Result<Stx, ExpandError> {
        let span = node.span(self.mc);
        let stx = self.tree.read(node).map_err(|error| ExpandError { kind: error.into(), start: span.start(), end: span.end() })?;
        Ok(self.tree.with(stx, TOP, Op::Add)?)
    }

    /// Declares `node`, a form from the reader. Binds its definitions, resolves its `require`s through `resolver`, and records its `provide`s.
    /// Appends the definitions and expressions it holds to `out`. `first` is the index, among the module's top-level forms, of the form at `out[0]`.
    pub fn declare(&mut self, node: Syntax<'gc>, first: u32, out: &mut Vec<Top>, resolver: &mut dyn Resolver<'gc>) -> Result<(), ExpandError> {
        let mut queue = vec![self.read(node)?];
        while let Some(form) = queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    let index = u32::try_from(out.len()).ok().and_then(|count| first.checked_add(count)).ok_or_else(|| self.error(OutOfMemory, form))?;
                    let slot = self.define_top(id, index)?;
                    match self.keyword_lambda(value)? {
                        Some(shape) => {
                            let name = self.tree.symbol(id).expect("definitions bind identifiers").value(self.mc);
                            let core = self.builder.define_private(name, index).map_err(|error| self.module_error(error, id))?;
                            self.builder.keyword_core(slot, core, shape);
                            out.push(Top(TopForm::DefineKeyword { procedure: slot, lambda: value }));
                        }
                        None => out.push(Top(TopForm::Define(slot, value))),
                    }
                }
                Head::DefineSyntax(form) => {
                    let (id, macro_index) = self.define_syntax_now(form)?;
                    self.bind(id, Binding::Macro(macro_index))?;
                }
                Head::Require(form) => {
                    for spec in self.proper(form)?.into_iter().skip(1) {
                        let imports = self.spec(spec)?.imports(self.mc, resolver, self.builder.name()).map_err(|error| match error {
                            SpecError::Resolve(at) => self.error(ExpandErrorKind::Resolve, at),
                            SpecError::NotProvided(at) => self.error(ExpandErrorKind::NotProvided, at),
                        })?;
                        self.builder.require(self.mc, self.symbols, imports).map_err(|error| self.module_error(error, spec))?;
                    }
                }
                Head::Provide(form) => self.provides.push(form),
                Head::Begin(forms) => queue.extend(forms.into_iter().rev()),
                Head::Struct(form) => {
                    let index = u32::try_from(out.len()).ok().and_then(|count| first.checked_add(count)).ok_or_else(|| self.error(OutOfMemory, form))?;
                    let declared = self.declare_struct(form, index)?;
                    out.push(Top(TopForm::Struct(declared)));
                }
                Head::Expr(expr) => out.push(Top(TopForm::Expr(expr))),
            }
        }
        Ok(())
    }

    /// Exports the names of the module's `provide` forms. Call it after every form is declared.
    pub fn provide(&mut self) -> Result<(), ExpandError> {
        for form in std::mem::take(&mut self.provides) {
            for spec in self.proper(form)?.into_iter().skip(1) {
                if self.is_id(spec) {
                    let symbol = self.tree.symbol(spec).expect("an identifier");
                    let name = self.text(spec).expect("an identifier");
                    self.builder.provide(&name, symbol.value(self.mc)).map_err(|error| self.module_error(error, spec))?;
                    continue;
                }
                let items = self.proper(spec)?;
                let Some((&head, args)) = items.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, spec)) };
                let word = if self.is_id(head) { self.text(head) } else { None };
                match (word.as_deref(), args) {
                    (Some("all-defined-out"), []) => self.builder.provide_all(self.mc).map_err(|error| self.module_error(error, spec))?,
                    (Some("struct-out"), &[name, ref options @ ..]) if self.is_id(name) => {
                        let constructors = match options {
                            [] => true,
                            &[option] if self.keyword_name(option).as_deref() == Some("omit-constructor") => false,
                            _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
                        };
                        let Binding::Slot(constructor) = self.resolve(name)? else { return Err(self.error(ExpandErrorKind::NotDefined, name)) };
                        self.builder.provide_struct(self.mc, constructor, constructors).map_err(|error| self.module_error(error, name))?;
                    }
                    (Some("rename-out"), renames) => {
                        for &rename in renames {
                            let (inner, external) = self.pair_of_names(rename)?;
                            let symbol = self.tree.symbol(inner).expect("an identifier");
                            self.builder.provide(&external, symbol.value(self.mc)).map_err(|error| self.module_error(error, rename))?;
                        }
                    }
                    _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
                }
            }
        }
        Ok(())
    }

    /// Parses the require spec `spec`. Filters are written outermost first, around the module name.
    /// The returned filters are in the order they apply, innermost first.
    fn spec(&mut self, mut spec: Stx) -> Result<RequireSpec<Stx>, ExpandError> {
        let mut filters = Vec::new();
        loop {
            if let Some(module) = self.text(spec) {
                filters.reverse();
                return Ok(RequireSpec { module, at: spec, filters });
            }
            let items = self.proper(spec)?;
            let Some((&head, args)) = items.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, spec)) };
            let word = if self.is_id(head) { self.text(head) } else { None };
            let (filter, inner) = match (word.as_deref(), args) {
                (Some("only-in"), &[inner, ref ids @ ..]) => (Filter::Only(self.identifiers(ids)?), inner),
                (Some("except-in"), &[inner, ref ids @ ..]) => (Filter::Except(self.identifiers(ids)?), inner),
                (Some("prefix-in"), &[prefix, inner]) => (Filter::Prefix(self.identifier(prefix)?), inner),
                (Some("rename-in"), &[inner, ref renames @ ..]) => {
                    let mut pairs = Vec::with_capacity(renames.len());
                    for &rename in renames {
                        let (old, new) = self.pair_of_names(rename)?;
                        pairs.push((self.text(old).expect("an identifier"), new, rename));
                    }
                    (Filter::Rename(pairs), inner)
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
            };
            filters.push(filter);
            spec = inner;
        }
    }

    /// Parses `stx` as `(old new)`, a list of two identifiers. Returns the identifier `old` and the name of `new`.
    fn pair_of_names(&mut self, stx: Stx) -> Result<(Stx, String), ExpandError> {
        match *self.proper(stx)?.as_slice() {
            [old, new] if self.is_id(old) && self.is_id(new) => Ok((old, self.text(new).expect("an identifier"))),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    /// Returns the name of each of the identifiers `ids`, with the identifier.
    fn identifiers(&mut self, ids: &[Stx]) -> Result<Vec<(String, Stx)>, ExpandError> {
        let mut named = Vec::with_capacity(ids.len());
        for &id in ids {
            named.push((self.identifier(id)?, id));
        }
        Ok(named)
    }

    /// Returns the name of the identifier `stx`, or a `BadSyntax` error if `stx` is not an identifier.
    fn identifier(&mut self, stx: Stx) -> Result<String, ExpandError> {
        if !self.is_id(stx) {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        Ok(self.text(stx).expect("an identifier"))
    }

    /// Returns the text of `stx` if it is an identifier or a string literal.
    pub(crate) fn text(&mut self, stx: Stx) -> Option<String> {
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
    pub(crate) fn import_error(&self, error: Unusable, stx: Stx) -> ExpandError {
        let kind = match error {
            Unusable::Uninitialized => ExpandErrorKind::Unbound,
            Unusable::MatchOnly => ExpandErrorKind::NoConstructor,
        };
        self.error(kind, stx)
    }

    pub(crate) fn module_error(&self, error: ModuleError, stx: Stx) -> ExpandError {
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

    /// Expands `top`, the module's top-level form with index `form`. The module must have been started.
    pub fn lower(&mut self, top: Top, form: u32) -> Result<module::Form<'gc>, ExpandError> {
        self.form = form;
        match top.0 {
            TopForm::Define(slot, value) => {
                let lambda = matches!(self.tree.view(value)?, View::List(items, None) if items.first().is_some_and(|&head| {
                    self.is_id(head) && matches!(self.resolve(head), Ok(Binding::Keyword(Keyword::Form(Form::Lambda))))
                }));
                self.defining = lambda.then_some(slot);
                let value = self.expand_now(value);
                self.defining = None;
                Ok(module::Form::Define(slot, value?))
            }
            TopForm::DefineKeyword { procedure, lambda } => {
                self.defining = Some(procedure);
                let value = self.expand_now(lambda);
                self.defining = None;
                Ok(module::Form::Define(procedure, value?))
            }
            TopForm::Struct(declared) => Ok(module::Form::Expr(self.lower_struct(declared))),
            TopForm::Expr(expr) => self.expand_now(expr).map(module::Form::Expr),
        }
    }

    /// Returns the finished module. Call it after all forms are compiled.
    pub fn finish(self) -> Result<Gc<'gc, Module>, OutOfMemory> {
        self.builder.finish(self.mc)
    }

    /// Returns `error`. If `error` has an empty span, as an out-of-memory error has, the result has the span of `stx` instead.
    fn placed(&self, error: ExpandError, stx: Stx) -> ExpandError {
        if error.start == error.end { self.error(error.kind, stx) } else { error }
    }

    /// Classifies `form`: a definition of a variable or a macro, a `require`, a `provide`, a `begin`, a `struct`, or
    /// an expression. Macro uses at the head of `form` are expanded first.
    fn head(&mut self, form: Stx) -> Result<Head, ExpandError> {
        self.head_of(form).map_err(|error| self.placed(error, form))
    }

    fn head_of(&mut self, mut form: Stx) -> Result<Head, ExpandError> {
        loop {
            let (head, alone) = match self.tree.view(form)? {
                View::Id => (form, true),
                View::List(items, None) if items.first().is_some_and(|&head| self.is_id(head)) => (items[0], false),
                _ => return Ok(Head::Expr(form)),
            };
            form = match self.resolve(head)? {
                Binding::Macro(macro_index) => self.expand_macro(macro_index, form)?,
                _ if alone => return Ok(Head::Expr(form)),
                Binding::Keyword(Keyword::Macro(kind)) => self.transform(kind, form)?,
                Binding::Keyword(Keyword::Form(Form::Define)) => return Ok(Head::Define(form)),
                Binding::Keyword(Keyword::Form(Form::DefineSyntax)) => return Ok(Head::DefineSyntax(form)),
                Binding::Keyword(Keyword::Form(Form::Require)) => return Ok(Head::Require(form)),
                Binding::Keyword(Keyword::Form(Form::Provide)) => return Ok(Head::Provide(form)),
                Binding::Keyword(Keyword::Form(Form::Begin)) => return Ok(Head::Begin(self.proper(form)?[1..].to_vec())),
                Binding::Keyword(Keyword::Form(Form::Struct)) => return Ok(Head::Struct(form)),
                _ => return Ok(Head::Expr(form)),
            };
        }
    }

    /// Returns the identifier that the `define` form `form` binds, and the expression for its value. `(define (f . formals)
    /// body ...)` means `(define f (lambda formals body ...))`. `f` can itself be such a list, as in `(define ((f a) b) body ...)`.
    fn definition(&mut self, form: Stx) -> Result<(Stx, Stx), ExpandError> {
        let items = self.proper(form)?;
        match *items.as_slice() {
            [_, target, value] if self.is_id(target) => Ok((target, value)),
            [_, mut target, ref body @ ..] if !body.is_empty() && !self.is_id(target) => {
                let mut body = body.to_vec();
                loop {
                    let View::List(parts, tail) = self.tree.view(target)? else { return Err(self.error(ExpandErrorKind::BadSyntax, target)) };
                    let Some((&name, params)) = parts.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, target)) };
                    let formals = match (params, tail) {
                        ([], Some(rest)) => rest,
                        _ => self.tree.list(params, tail, self.tree.span(target))?,
                    };
                    let lambda = self.introduce("lambda", target)?;
                    let lambda = self.tree.list(&[&[lambda, formals], body.as_slice()].concat(), None, self.tree.span(form))?;
                    if self.is_id(name) {
                        return Ok((name, lambda));
                    }
                    (target, body) = (name, vec![lambda]);
                }
            }
            _ => Err(self.error(ExpandErrorKind::BadSyntax, form)),
        }
    }

    /// Defines a module variable for the identifier `id` in the top-level form `form`, and returns its slot.
    /// If `TOP` is the only scope of `id`, the module binds the variable by name. Otherwise the variable is private, and only identifiers
    /// with the scopes of `id` refer to it.
    pub(crate) fn define_top(&mut self, id: Stx, form: u32) -> Result<u32, ExpandError> {
        let name = self.tree.symbol(id).expect("definitions bind identifiers").value(self.mc);
        if self.tree.scopes_of(id)? == self.top {
            return self.builder.define(name, form).map_err(|error| self.module_error(error, id));
        }
        let slot = self.builder.define_private(name, form).map_err(|error| self.module_error(error, id))?;
        self.bind(id, Binding::Slot(slot))?;
        Ok(slot)
    }

    /// Returns the binding that the identifier `id` refers to.
    pub(crate) fn resolve(&mut self, id: Stx) -> Result<Binding<'gc>, ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers resolve");
        let set = self.tree.scopes_of(id)?;
        self.resolve_name(symbol, set).map_err(|Ambiguous| self.error(ExpandErrorKind::Ambiguous, id))
    }

    /// Returns the bindings of the name with the word `name_key` whose scopes are all in `set`. The bindings are looked up under the scopes of `bound_in` that are in `set`, then under the scopes of `own`.
    #[inline]
    fn candidates<'s>(&'s self, name_key: u64, set: Set, bound_in: &'s [Scope], own: &'s [Scope]) -> impl Iterator<Item = &'s (Set, Binding<'gc>)> {
        let scopes = &self.tree.scopes;
        let under = bound_in.iter().filter(move |&&scope| scopes.contains(set, scope)).chain(own);
        let lists = under.filter_map(move |&scope| self.bindings.get(&(scope, name_key)));
        lists.flatten().filter(move |&&(bound, _)| scopes.subset(bound, set))
    }

    /// Returns the binding that an identifier named `symbol` with the scope set `set` refers to.
    pub(crate) fn resolve_name(&self, symbol: Symbol<'gc>, set: Set) -> Result<Binding<'gc>, Ambiguous> {
        let name_key = key(symbol, self.mc);
        let scopes = &self.tree.scopes;
        // Every binding that the identifier can refer to is stored under one of the identifier's scopes. So iterate over the shorter
        // list: the identifier's scopes, or the scopes that the name has bindings under.
        let bound_in = self.bound_in.get(&name_key).map_or(&[][..], Vec::as_slice);
        let own = scopes.scopes(set);
        let (bound_in, own) = if bound_in.len() < own.len() { (bound_in, &[][..]) } else { (&[][..], own) };
        let mut best: Option<(Set, Binding<'gc>)> = None;
        for &(bound, binding) in self.candidates(name_key, set, bound_in, own) {
            if best.is_none_or(|(best_set, _)| scopes.subset(best_set, bound)) {
                best = Some((bound, binding));
            }
        }
        if let Some((best, binding)) = best {
            if self.candidates(name_key, set, bound_in, own).any(|&(bound, _)| !scopes.subset(bound, best)) {
                return Err(Ambiguous);
            }
            return Ok(binding);
        }
        // An identifier with the `BASE` scope refers to the prelude's binding, even if the module binds the same name.
        let base = self.tree.scopes.contains(set, BASE);
        if !base && let Some(binding) = self.builder.binding(symbol.value(self.mc)) {
            return Ok(match binding {
                module::Binding::Slot(slot) => Binding::Slot(slot),
                module::Binding::Import(import) => Binding::Import(import),
            });
        }
        if let Some(&keyword) = self.keywords.get(&name_key) {
            return Ok(Binding::Keyword(keyword));
        }
        if base && let Some(&import) = self.base_cells.get(&name_key) {
            return Ok(Binding::Import(import));
        }
        Ok(Binding::Free)
    }

    pub(crate) fn bind(&mut self, id: Stx, binding: Binding<'gc>) -> Result<(), ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers are bound");
        let set = self.tree.scopes_of(id)?;
        self.tree.scopes.charge(size_of::<(Set, Binding)>())?;
        let newest = self.tree.scopes.scopes(set).last().copied().unwrap_or(TOP);
        let name_key = key(symbol, self.mc);
        let under = self.bindings.entry((newest, name_key)).or_default();
        if under.is_empty() {
            self.tree.scopes.charge(size_of::<Scope>())?;
            self.bound_in.entry(name_key).or_default().push(newest);
        }
        under.push((set, binding));
        Ok(())
    }

    /// Allocates a local variable for the identifier `id` and binds `id` to it. If the variable is later bound to a lambda, error reports show the lambda under this name.
    pub(crate) fn local(&mut self, id: Stx) -> Result<Var, ExpandError> {
        let var = match self.tree.symbol(id) {
            Some(name) => self.builder.locals().named(name.value(self.mc)),
            None => self.fresh(),
        };
        self.bind(id, Binding::Local(var))?;
        Ok(var)
    }

    pub(crate) fn fresh(&mut self) -> Var {
        self.builder.locals().fresh()
    }

    /// Returns a `Duplicate` error at the second of any two `ids` that have the same name and scopes.
    pub(crate) fn distinct(&mut self, ids: &[Stx]) -> Result<(), ExpandError> {
        let mut seen = std::collections::HashSet::new();
        for &id in ids {
            let symbol = self.tree.symbol(id).expect("only identifiers are bound");
            if !seen.insert((key(symbol, self.mc), self.tree.scopes_of(id)?)) {
                return Err(self.error(ExpandErrorKind::Duplicate, id));
            }
        }
        Ok(())
    }

    /// Applies the built-in macro `kind` to its use `stx`. Flips a fresh scope on the macro's input and
    /// on its output.
    pub(crate) fn transform(&mut self, kind: Macro, stx: Stx) -> Result<Stx, ExpandError> {
        let intro = self.tree.scopes.fresh()?;
        let input = self.tree.with(stx, intro, Op::Flip)?;
        let output = self.derived(kind, input)?;
        Ok(self.tree.with(output, intro, Op::Flip)?)
    }

    /// Expands the expression `stx` to a core form. The step driver keeps the pending continuations on a heap-allocated
    /// stack. So the native stack does not grow with the nesting depth of `stx`.
    pub(crate) fn expand_now(&mut self, stx: Stx) -> Result<Core<'gc>, ExpandError> {
        steps::run(self, Call::Expr(stx), Self::step)
    }

    /// Runs one call for the step driver. An error with an empty span, such as an out-of-memory error, gets the span of
    /// the expression being expanded.
    fn step(&mut self, call: Call<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> {
        match call {
            Call::Expr(stx) => self.expand(stx).map_err(|error| self.placed(error, stx)),
            Call::Run(run) => run(self),
        }
    }

    /// Returns a step that expands the expression `stx` and passes the core form to `then`.
    pub(crate) fn expr(stx: Stx, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Ok(Step::then(Call::Expr(stx), then))
    }

    /// Returns a step that expands each of `stxs` in order and passes the core forms to `then`.
    pub(crate) fn exprs(stxs: Vec<Stx>, then: impl FnOnce(&mut Self, Vec<Core<'gc>>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        steps::all(stxs.into_iter().map(Call::Expr).collect(), then)
    }

    /// Returns a step that expands `forms`, the body of the form `stx`, and passes the core form to `then`.
    pub(crate) fn body_then(stx: Stx, forms: Vec<Stx>, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Ok(Step::then(Call::Run(Box::new(move |this: &mut Self| this.body(stx, forms))), then))
    }

    /// Returns the first step of expanding `stx`: the finished core form, or a request to expand parts of `stx` first.
    fn expand(&mut self, stx: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        match self.tree.view(stx)? {
            View::Id => self.reference(stx),
            // As in Racket, a keyword such as `#:k` is not an expression. It must be quoted to be used as a value.
            View::Datum(value) if ragwort_types::symbol::Keyword::of(value).is_some() => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
            View::Datum(value) => Ok(Step::Done(Core::Quote(value))),
            View::Vector(_) => Ok(Step::Done(Core::Quote(self.strip(stx)?))),
            View::List(items, tail) => self.compound(stx, items, tail),
        }
    }

    fn compound(&mut self, stx: Stx, items: Vec<Stx>, tail: Option<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some(&head) = items.first() else { return Err(self.error(ExpandErrorKind::BadSyntax, stx)) };
        if self.is_id(head) {
            match self.resolve(head)? {
                Binding::Keyword(Keyword::Form(form)) => return self.form(form, stx, items, tail),
                Binding::Keyword(Keyword::Macro(kind)) => return Ok(Step::Tail(Call::Expr(self.transform(kind, stx)?))),
                Binding::Keyword(Keyword::Aux(_)) => return Err(self.error(ExpandErrorKind::BadSyntax, head)),
                Binding::Macro(macro_index) => return Ok(Step::Tail(Call::Expr(self.expand_macro(macro_index, stx)?))),
                Binding::Import(import) if tail.is_none() && !self.has_keyword_args(&items[1..]) => {
                    return Self::exprs(items[1..].to_vec(), move |this, args| {
                        import.callable(this.mc, args.len()).map_err(|error| this.import_error(error, head))?;
                        Ok(Step::Done(Core::App(Box::new(Core::Import(import)), args, this.position(stx))))
                    });
                }
                _ => {}
            }
        }
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        if self.has_keyword_args(&items[1..]) {
            return self.keyword_call(stx, head, items[1..].to_vec());
        }
        Self::expr(head, move |_, callee| Self::exprs(items[1..].to_vec(), move |this, args| Ok(Step::Done(Core::App(Box::new(callee), args, this.position(stx))))))
    }

    /// Returns the source position of the form `stx`. Error reports use it for a call or operation expanded from the form.
    pub(crate) fn position(&self, stx: Stx) -> Option<Position<'gc>> {
        Position::of(self.mc, self.tree.span(stx))
    }

    fn form(&mut self, form: Form, stx: Stx, items: Vec<Stx>, tail: Option<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Ok(Step::Done(Core::Quote(self.strip(datum)?))),
            (Form::If, &[test, then]) => Self::exprs(vec![test, then], |_, parts| {
                let [test, then] = <[Core<'gc>; 2]>::try_from(parts).expect("two parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(Core::Quote(Value::VOID)))))
            }),
            (Form::If, &[test, then, other]) => Self::exprs(vec![test, then, other], |_, parts| {
                let [test, then, other] = <[Core<'gc>; 3]>::try_from(parts).expect("three parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(other))))
            }),
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(stx, formals, body.to_vec()),
            (Form::Define | Form::Require | Form::Provide | Form::Struct, _) => Err(self.error(ExpandErrorKind::Definition, stx)),
            (Form::Set, &[id, value]) if self.is_id(id) => self.set(id, value),
            (Form::Begin, &[_, ..]) => self.sequence(items[1..].to_vec()),
            (Form::Let, &[name, _, _, ..]) if self.is_id(name) => Ok(Step::Tail(Call::Expr(self.transform(Macro::NamedLet, stx)?))),
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(stx, binds, body.to_vec(), form == Form::Letrec),
            (Form::DefineSyntax, _) => Err(self.error(ExpandErrorKind::Definition, stx)),
            (Form::LetSyntax | Form::LetrecSyntax, &[binds, ref body @ ..]) => self.let_syntax(stx, binds, body.to_vec(), form == Form::LetrecSyntax),
            (Form::SyntaxCase, &[input, literals, ref clauses @ ..]) => self.syntax_case(input, literals, clauses.to_vec()),
            (Form::Syntax, &[template]) => Ok(Step::Done(self.syntax(template)?)),
            (Form::QuoteSyntax, &[datum]) => Ok(Step::Done(Core::Quote(self.wrap(datum)?))),
            (Form::Unsupported, _) => Err(self.error(ExpandErrorKind::Unsupported, stx)),
            (Form::StructRef, &[instance, kind, index]) => Self::exprs(vec![instance, kind, index], move |this, parts| Ok(Step::Done(Core::Intrinsic(Prim::Intrinsic(Intrinsic::StructRef), parts, this.position(stx))))),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    fn reference(&mut self, id: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Slot(slot) => match self.builder.constant(slot, self.form) {
                Some(value) => return Ok(Step::Done(Core::Quote(value))),
                None => self.builder.place(slot, self.form, self.defining),
            },
            Binding::Import(import) => {
                import.usable(self.mc).map_err(|error| self.import_error(error, id))?;
                return Ok(Step::Done(Core::Import(import)));
            }
            Binding::Free => return Err(self.error(ExpandErrorKind::Unbound, id)),
            Binding::Macro(macro_index) => return Ok(Step::Tail(Call::Expr(self.expand_macro(macro_index, id)?))),
            Binding::Keyword(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Ok(Step::Done(Core::Ref(place)))
    }

    fn set(&mut self, id: Stx, value: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Slot(slot) => {
                self.builder.assign(slot).map_err(|error| self.module_error(error, id))?;
                self.builder.place(slot, self.form, self.defining)
            }
            Binding::Import(_) => return Err(self.error(ExpandErrorKind::Immutable, id)),
            Binding::Free => return Err(self.error(ExpandErrorKind::Unbound, id)),
            Binding::Keyword(_) | Binding::Macro(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Self::expr(value, move |_, value| Ok(Step::Done(Core::Set(place, Box::new(value)))))
    }

    /// Expands `stxs` as a sequence. The expressions run in order, and the last one gives the value.
    fn sequence(&mut self, mut stxs: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let last = stxs.pop().expect("sequences aren't empty");
        self.sequence_from(stxs.into_iter(), Vec::new(), last)
    }

    /// Expands the rest of a sequence. `before` holds the expressions still to expand before `last`. Each is bound to a variable that
    /// nothing reads, and the binding is added to `binds`.
    fn sequence_from(&mut self, mut before: std::vec::IntoIter<Stx>, mut binds: Vec<(Var, Core<'gc>)>, last: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        match before.next() {
            Some(stx) => {
                let var = self.fresh();
                Self::expr(stx, move |this, core| {
                    binds.push((var, core));
                    this.sequence_from(before, binds, last)
                })
            }
            None => Self::expr(last, move |_, last| Ok(Step::Done(if binds.is_empty() { last } else { Core::Let(binds, Box::new(last)) }))),
        }
    }

    pub(crate) fn lambda_id(&mut self) -> u32 {
        self.builder.locals().lambda()
    }

    fn lambda(&mut self, stx: Stx, formals: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let formals = self.tree.with(formals, scope, Op::Add)?;
        if !self.plain_formals(formals)? {
            return self.lambda_with(stx, formals, body, scope);
        }
        let (ids, rest) = match self.tree.view(formals)? {
            View::Id => (Vec::new(), Some(formals)),
            View::List(ids, rest) => (ids, rest),
            _ => return Err(self.error(ExpandErrorKind::BadSyntax, formals)),
        };
        if let Some(&id) = ids.iter().chain(&rest).find(|&&id| !self.is_id(id)) {
            return Err(self.error(ExpandErrorKind::BadSyntax, id));
        }
        self.distinct(&[ids.as_slice(), rest.as_slice()].concat())?;
        let params = ids.iter().map(|&id| self.local(id)).collect::<Result<_, _>>()?;
        let rest = rest.map(|id| self.local(id)).transpose()?;
        let body = self.scoped(&body, scope)?;
        Self::body_then(stx, body, move |this, body| Ok(Step::Done(Core::Lambda(Lambda { id: this.lambda_id(), params, optional: 0, rest, body: Box::new(body), name: None, at: Position::of(this.mc, this.tree.span(stx)) }))))
    }

    /// Expands a `let` form, or a `letrec` form if `recursive`.
    fn binding(&mut self, stx: Stx, binds: Stx, body: Vec<Stx>, recursive: bool) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let mut ids = Vec::new();
        let mut inits = Vec::new();
        for bind in self.proper(binds)? {
            match *self.proper(bind)?.as_slice() {
                [id, init] if self.is_id(id) => {
                    ids.push(self.tree.with(id, scope, Op::Add)?);
                    inits.push(init);
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, bind)),
            }
        }
        self.distinct(&ids)?;
        if recursive {
            let vars: Vec<_> = ids.iter().map(|&id| self.local(id)).collect::<Result<_, _>>()?;
            let inits = self.scoped(&inits, scope)?;
            Self::exprs(inits, move |this, inits| this.binding_body(stx, body, scope, recursive, vars, inits))
        } else {
            Self::exprs(inits, move |this, inits| {
                let vars = ids.iter().map(|&id| this.local(id)).collect::<Result<_, _>>()?;
                this.binding_body(stx, body, scope, recursive, vars, inits)
            })
        }
    }

    /// Expands the `body` of the `let` or `letrec` form `stx` in `scope`. The result binds `vars` to `inits` around the body.
    fn binding_body(&mut self, stx: Stx, body: Vec<Stx>, scope: Scope, recursive: bool, vars: Vec<Var>, inits: Vec<Core<'gc>>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let body = self.scoped(&body, scope)?;
        Self::body_then(stx, body, move |_, body| {
            let binds = vars.into_iter().zip(inits).collect();
            let body = Box::new(body);
            Ok(Step::Done(if recursive { Core::Letrec(binds, body) } else { Core::Let(binds, body) }))
        })
    }

    /// Expands a body. A body has definitions and expressions in any order, bound as by `letrec*`. Its last
    /// item must be an expression, which gives the value. `stx` is the form that owns the body.
    pub(crate) fn body(&mut self, stx: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let mut queue = self.scoped(&body, scope)?;
        queue.reverse();
        self.scan(Scan { stx, queue, items: Vec::new(), defined: Vec::new(), names: Vec::new() })
    }

    /// Scans the remaining forms of a body, then expands the definitions and expressions found. When a form defines a macro, the macro's transformer is created
    /// before the forms after it are scanned.
    fn scan(&mut self, mut scan: Scan) -> Result<Ex<'a, 'gc>, ExpandError> {
        while let Some(form) = scan.queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    scan.defined.push(id);
                    scan.names.push(id);
                    scan.items.push(Item::Define(self.local(id)?, value));
                }
                Head::DefineSyntax(form) => {
                    let (id, expr) = self.syntax_definition(form)?;
                    return self.transformer(expr, form, move |this, macro_index| {
                        scan.names.push(id);
                        this.bind(id, Binding::Macro(macro_index))?;
                        this.scan(scan)
                    });
                }
                Head::Require(form) | Head::Provide(form) | Head::Struct(form) => return Err(self.error(ExpandErrorKind::Definition, form)),
                Head::Begin(forms) => scan.queue.extend(forms.into_iter().rev()),
                Head::Expr(expr) => scan.items.push(Item::Expr(expr)),
            }
        }
        self.distinct(&scan.names)?;
        let Some(Item::Expr(last)) = scan.items.pop() else { return Err(self.error(ExpandErrorKind::NoExpression, scan.stx)) };
        if scan.defined.is_empty() {
            let mut stxs: Vec<Stx> = scan.items.into_iter().filter_map(|item| if let Item::Expr(expr) = item { Some(expr) } else { None }).collect();
            stxs.push(last);
            return self.sequence(stxs);
        }
        let count = scan.items.len();
        self.defines(scan.items.into_iter(), Vec::with_capacity(count), last)
    }

    /// Expands the remaining `items` of a body and adds a binding for each to `binds`. An expression is bound to a fresh variable. The result is a `Core::Letrec` of `binds` around the
    /// `last` expression.
    fn defines(&mut self, mut items: std::vec::IntoIter<Item>, mut binds: Vec<(Var, Core<'gc>)>, last: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let (var, value) = match items.next() {
            None => return Self::expr(last, move |_, last| Ok(Step::Done(Core::Letrec(binds, Box::new(last))))),
            Some(Item::Define(var, value)) => (var, value),
            Some(Item::Expr(expr)) => (self.fresh(), expr),
        };
        Self::expr(value, move |this, value| {
            binds.push((var, value));
            this.defines(items, binds, last)
        })
    }

    /// Returns `stxs` with `scope` added to each.
    pub(crate) fn scoped(&mut self, stxs: &[Stx], scope: Scope) -> Result<Vec<Stx>, ExpandError> {
        Ok(stxs.iter().map(|&stx| self.tree.with(stx, scope, Op::Add)).collect::<Result<_, _>>()?)
    }

    pub(crate) fn strip(&mut self, stx: Stx) -> Result<Value<'gc>, ExpandError> {
        self.tree.strip(stx).map_err(|error| self.error(error, stx))
    }

    pub(crate) fn is_id(&self, stx: Stx) -> bool {
        self.tree.symbol(stx).is_some()
    }

    /// Returns whether `stx` is an identifier that refers to the auxiliary keyword `aux`.
    pub(crate) fn is_aux(&mut self, stx: Stx, aux: Aux) -> Result<bool, ExpandError> {
        Ok(self.is_id(stx) && matches!(self.resolve(stx)?, Binding::Keyword(Keyword::Aux(found)) if found == aux))
    }

    /// Returns the items of `stx`, or a `BadSyntax` error if `stx` is not a proper list.
    pub(crate) fn proper(&mut self, stx: Stx) -> Result<Vec<Stx>, ExpandError> {
        match self.tree.view(stx)? {
            View::List(items, None) => Ok(items),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    pub(crate) fn symbol(&self, name: &str) -> Result<Symbol<'gc>, ExpandError> {
        Ok(self.symbols.intern_str(&self.strings, name)?)
    }

    /// Creates an identifier named `name` with only the `BASE` scope and the span of `at`. It refers to the base binding of `name`, which code read from source cannot shadow.
    pub(crate) fn introduce(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.base, span)?)
    }

    /// Creates an identifier for the form named `name` that only the expander generates, with the span of `at`. A
    /// program cannot write such an identifier: `struct-ref` in a program is an unbound variable.
    pub(crate) fn internal(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.internal, span)?)
    }
}
