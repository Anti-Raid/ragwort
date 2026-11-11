//! The expander: Scheme's syntax to the compiler's core forms, hygienically, by sets of scopes
//! as Racket does it. Binding forms add a fresh scope to what they bind and to their bodies, and
//! each macro step flips a fresh scope on its input and output, so what the macro introduces
//! is told apart from what it was given. An identifier means the binding of its name whose
//! scopes are the most of its own.



use ragwort_compiler::keyword::CallShape;
use ragwort_compiler::module::{self, Filter, Import, Imports, ModuleBuilder, ModuleError, RequireSpec, Resolver, SpecError, Uninitialized};
use ragwort_compiler::steps::{self, Step};
use ragwort_compiler::structs::{self, Declared};
use ragwort_compiler::{Core, Lambda, Place, Var};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxContext, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_vm::{HostDef, Machine};
use ragwort_vm::objects::Module;

use crate::formals::{CoreAt, KeywordDef};
use crate::scope::{BASE, Map, Op, Scope, Set, TOP};
use crate::structs::{Info, Local};
use crate::tree::{Stx, Tree, View};
use crate::{ExpandError, ExpandErrorKind};

/// How much fuel the transformers of a load's macros have, between them, so a macro that
/// expands forever ends.
const MACRO_FUEL: u64 = 1 << 26;

/// The forms the expander knows itself.
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
    /// `(quote-syntax datum)`: the syntax of `datum`, as it is, pattern variables and all.
    QuoteSyntax,
    /// `quasisyntax` and its unquotes.
    Unsupported,
    Struct,
}

/// The macros built in, written in Rust.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Macro {
    LetStar,
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
    /// A `let` with a name, which nothing binds by itself.
    NamedLet,
}

/// Names that mean something only inside other forms.
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

const KEYWORDS: [(&str, Keyword); 42] = [
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

/// A binding identifiers have been made with: one of the load's own, of a kind and number, or a
/// module's variable or free name, by the words of the module's name and the variable's.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Stamp {
    Own(u8, u32),
    Named(u64, u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Binding<'gc> {
    Keyword(Keyword),
    Local(Var),
    /// A variable of the module's own.
    Slot(u32),
    /// What the module requires, which code can't assign.
    Import(Import<'gc>),
    /// No binding.
    Free,
    /// A macro defined in this load: the index of its transformer.
    Macro(u32),
    /// A pattern variable of `syntax-case`, which only `syntax` refers to: the local that holds
    /// what it matched, a list of them for each ellipsis it's under, `depth` of them.
    Pattern { var: Var, depth: u32 },
}

/// An identifier that two bindings could be, neither of whose scopes include the other's.
pub(crate) struct Ambiguous;

/// What a body has, in order: a definition of a variable, or of a keyword procedure, the core's
/// variable too, or a variable a struct form defines, with its value, or an expression.
enum Item<'gc> {
    Define(Var, Stx),
    Keyword(Var, Var, Stx),
    Made(Var, Core<'gc>),
    Expr(Stx),
}

/// A body's forms still to look at, last first, and what's been found in those before them.
struct Scan<'gc> {
    stx: Stx,
    queue: Vec<Stx>,
    items: Vec<Item<'gc>>,
    defined: Vec<Stx>,
    names: Vec<Stx>,
}

/// What expanding an expression does next: see [`steps`]. Each call makes core forms.
pub(crate) type Ex<'a, 'gc> = Step<'a, Expander<'a, 'gc>, Call<'a, 'gc>, Core<'gc>, ExpandError>;

/// What an expression's expansion needs made first.
pub(crate) enum Call<'a, 'gc> {
    /// The expression.
    Expr(Stx),
    /// What the function makes.
    Run(Work<'a, 'gc>),
}

/// Expansion that goes on from the state it's given.
pub(crate) type Work<'a, 'gc> = Box<dyn FnOnce(&mut Expander<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a>;

/// A form at the top level or in a body, expanded far enough to tell what it is.
enum Head {
    Define(Stx),
    DefineSyntax(Stx),
    Require(Stx),
    Provide(Stx),
    Begin(Vec<Stx>),
    Struct(Stx),
    Expr(Stx),
}

/// A top-level form of a module's Scheme, with what it defines bound, to [`Expander::lower`].
pub struct Top(TopForm);

enum TopForm {
    /// The module variable's slot, and its value.
    Define(u32, Stx),
    /// A definition of a keyword procedure: its variable's slot, its core's, and its `lambda`.
    DefineKeyword { procedure: u32, core: u32, lambda: Stx },
    Struct(Declared),
    Expr(Stx),
}

/// Expands the Scheme files of a module, into a [`ModuleBuilder`] other front ends can build it
/// with too: first [`Expander::declare`] each of their forms, then [`Expander::provide`] and start
/// the module, then [`Expander::lower`] each, in order, and [`Expander::finish`].
pub struct Expander<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
    pub(crate) strings: Strings<'a, 'gc>,
    symbols: Symbols<'gc>,
    pub(crate) tree: Tree<'a, 'gc>,
    keywords: Map<u64, Keyword>,
    /// The module being expanded, which what's read in just the top-level scope refers to by
    /// name, and the prelude's exports, which the base bindings are.
    pub(crate) builder: ModuleBuilder<'gc>,
    base_cells: Map<u64, Import<'gc>>,
    /// The `provide`s, which name what the module defines anywhere.
    provides: Vec<Stx>,
    /// The top-level form being expanded, and the variable whose lambda it's in, if it's one.
    pub(crate) form: u32,
    pub(crate) defining: Option<u32>,
    /// The keyword procedures definitions in bodies made, by their variables, which calls go to
    /// the cores of. The module's own are its builder's, whichever language defined them.
    keyword_defs: Map<Var, KeywordDef<'gc>>,
    /// The struct types forms in bodies made, by the locals of the constructors named for them,
    /// and what each local such a form defined is. The module's own are its builder's.
    pub(crate) struct_infos: Map<Var, Info<'gc>>,
    pub(crate) struct_locals: Map<Var, Local>,
    /// The bindings made in this load, with the scopes each was made in, by the newest of those
    /// scopes and the name's word. An identifier's bindings are under its own scopes.
    bindings: Map<(Scope, u64), Vec<(Set, Binding<'gc>)>>,
    /// The scopes `bindings` has bindings of each name's word under, so a name bound in fewer
    /// places than an identifier has scopes is looked up from its side.
    bound_in: Map<u64, Vec<Scope>>,
    top: Set,
    base: Set,
    vars: u32,
    lambdas: u32,
    /// The transformers of the load's macros.
    pub(crate) macros: Vec<Value<'gc>>,
    /// What runs the transformers, once one has, and the fuel they have between them till then.
    pub(crate) machine: Option<Machine>,
    pub(crate) fuel: u64,
    /// The node each syntax object made from the tree was made from, by the object's word.
    pub(crate) unwrapped: Map<u64, Stx>,
    /// The metadata made for syntax of each kind with each set of scopes, and their contexts.
    pub(crate) metas: Map<(Set, usize), SyntaxMeta<'gc>>,
    /// The value standing for each binding identifiers have been made with.
    pub(crate) binding_values: Map<Stamp, Value<'gc>>,
    pub(crate) contexts: Map<Set, SyntaxContext<'gc>>,
    /// The object each of the load's scopes is, in syntax, and the scope each object it's been
    /// given is, by the object's word. The prelude is the base scope, in every load.
    pub(crate) scope_objects: Map<Scope, SyntaxScope<'gc>>,
    pub(crate) scope_numbers: Map<u64, Scope>,
}

fn key<'gc>(symbol: Symbol<'gc>, mc: &Mutation<'gc>) -> u64 {
    symbol.value(mc).to_bits()
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// An expander of the Scheme files of the module named `name`, whose native files call
    /// `hosts`. It requires the `prelude` module, which has run and whose exports the base
    /// bindings are, implicitly, then each of `implicit`, whose exports shadow what those before
    /// it export.
    pub fn new(
        mc: &'a Mutation<'gc>,
        symbols: Symbols<'gc>,
        prelude: Gc<'gc, Module>,
        name: &str,
        hosts: &'static [HostDef],
        implicit: &[Gc<'gc, Module>],
    ) -> Result<Self, ExpandError> {
        let strings = Strings::new(mc);
        let intern = |name: &str| symbols.intern_str(&strings, name);
        let mut builder = ModuleBuilder::new(intern(name)?.value(mc), hosts);
        for &module in std::iter::once(&prelude).chain(implicit) {
            builder.require_implicitly(mc, symbols, module).map_err(|_| OutOfMemory)?;
        }
        let keywords = KEYWORDS.iter().map(|&(name, k)| Ok((key(intern(name)?, mc), k))).collect::<Result<_, ragwort_types::Error>>()?;
        let abbreviations = Abbreviation::ALL.iter().map(|a| intern(a.name())).collect::<Result<_, _>>()?;
        let mut tree = Tree::new(mc, abbreviations);
        let top = tree.scopes.set(vec![TOP])?;
        let base = tree.scopes.set(vec![BASE])?;
        let exports = Imports::all(mc, prelude).unwrap_or_default().0;
        let base_cells = exports.into_iter().map(|(name, import)| Ok((key(intern(&name)?, mc), import))).collect::<Result<_, ragwort_types::Error>>()?;
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
            keyword_defs: Map::default(),
            struct_infos: Map::default(),
            struct_locals: Map::default(),
            bindings: Map::default(),
            bound_in: Map::default(),
            top,
            base,
            vars: 0,
            lambdas: 0,
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

    /// The module, which the other front ends build it with.
    pub fn builder(&mut self) -> &mut ModuleBuilder<'gc> {
        &mut self.builder
    }

    /// What the reader read, in the top-level scope.
    fn read(&mut self, node: Syntax<'gc>) -> Result<Stx, ExpandError> {
        let span = node.span(self.mc);
        let stx = self.tree.read(node).map_err(|e| ExpandError { kind: e.into(), start: span.start(), end: span.end() })?;
        Ok(self.tree.with(stx, TOP, Op::Add)?)
    }

    /// Binds what `node`, a form the reader read, defines, requires from `resolver` or provides,
    /// and adds what it holds to `out`, the module's top-level forms from its `first` on.
    pub fn declare(&mut self, node: Syntax<'gc>, first: u32, out: &mut Vec<Top>, resolver: &mut dyn Resolver<'gc>) -> Result<(), ExpandError> {
        let mut queue = vec![self.read(node)?];
        while let Some(form) = queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    let index = u32::try_from(out.len()).ok().and_then(|n| first.checked_add(n)).ok_or_else(|| self.error(OutOfMemory, form))?;
                    let slot = self.define_top(id, index)?;
                    match self.keyword_lambda(value)? {
                        Some(shape) => {
                            let name = self.tree.symbol(id).expect("definitions bind identifiers").value(self.mc);
                            let core = self.builder.define_private(name, index).map_err(|e| self.module_error(e, id))?;
                            self.builder.keyword_core(slot, core, shape);
                            out.push(Top(TopForm::DefineKeyword { procedure: slot, core, lambda: value }));
                        }
                        None => out.push(Top(TopForm::Define(slot, value))),
                    }
                }
                Head::DefineSyntax(form) => {
                    let (id, m) = self.define_syntax_now(form)?;
                    self.bind(id, Binding::Macro(m))?;
                }
                Head::Require(form) => {
                    for spec in self.proper(form)?.into_iter().skip(1) {
                        let imports = self.spec(spec)?.imports(self.mc, resolver, self.builder.name()).map_err(|e| match e {
                            SpecError::Resolve(at) => self.error(ExpandErrorKind::Resolve, at),
                            SpecError::NotProvided(at) => self.error(ExpandErrorKind::NotProvided, at),
                        })?;
                        self.builder.require(self.mc, self.symbols, imports).map_err(|e| self.module_error(e, spec))?;
                    }
                }
                Head::Provide(form) => self.provides.push(form),
                Head::Begin(forms) => queue.extend(forms.into_iter().rev()),
                Head::Struct(form) => {
                    let index = u32::try_from(out.len()).ok().and_then(|n| first.checked_add(n)).ok_or_else(|| self.error(OutOfMemory, form))?;
                    out.push(Top(TopForm::Struct(self.declare_struct(form, index)?)));
                }
                Head::Expr(e) => out.push(Top(TopForm::Expr(e))),
            }
        }
        Ok(())
    }

    /// Exports what the module provides, once every form is declared.
    pub fn provide(&mut self) -> Result<(), ExpandError> {
        for form in std::mem::take(&mut self.provides) {
            for spec in self.proper(form)?.into_iter().skip(1) {
                if self.is_id(spec) {
                    let symbol = self.tree.symbol(spec).expect("an identifier");
                    let name = self.text(spec).expect("an identifier");
                    self.builder.provide(&name, symbol.value(self.mc)).map_err(|e| self.module_error(e, spec))?;
                    continue;
                }
                let items = self.proper(spec)?;
                let Some((&head, args)) = items.split_first() else { return Err(self.error(ExpandErrorKind::BadSyntax, spec)) };
                let word = if self.is_id(head) { self.text(head) } else { None };
                match (word.as_deref(), args) {
                    (Some("all-defined-out"), []) => self.builder.provide_all(self.mc).map_err(|e| self.module_error(e, spec))?,
                    (Some("struct-out"), &[name]) if self.is_id(name) => {
                        let Binding::Slot(constructor) = self.resolve(name)? else { return Err(self.error(ExpandErrorKind::NotDefined, name)) };
                        self.builder.provide_struct(self.mc, constructor).map_err(|e| self.module_error(e, name))?;
                    }
                    (Some("rename-out"), renames) => {
                        for &rename in renames {
                            let (inner, external) = self.pair_of_names(rename)?;
                            let symbol = self.tree.symbol(inner).expect("an identifier");
                            self.builder.provide(&external, symbol.value(self.mc)).map_err(|e| self.module_error(e, rename))?;
                        }
                    }
                    _ => return Err(self.error(ExpandErrorKind::BadSyntax, spec)),
                }
            }
        }
        Ok(())
    }

    /// The require spec `spec`: its filters, outermost first as they're written, then the
    /// module inside them.
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
            let named = |this: &mut Self, ids: &[Stx]| -> Result<Vec<(String, Stx)>, ExpandError> {
                ids.iter().map(|&id| Ok((this.identifier(id)?, id))).collect()
            };
            let (filter, inner) = match (word.as_deref(), args) {
                (Some("only-in"), &[inner, ref ids @ ..]) => (Filter::Only(named(self, ids)?), inner),
                (Some("except-in"), &[inner, ref ids @ ..]) => (Filter::Except(named(self, ids)?), inner),
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

    /// The identifiers in `(old new)`.
    fn pair_of_names(&mut self, stx: Stx) -> Result<(Stx, String), ExpandError> {
        match *self.proper(stx)?.as_slice() {
            [old, new] if self.is_id(old) && self.is_id(new) => Ok((old, self.text(new).expect("an identifier"))),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    /// The name of the identifier `stx`.
    fn identifier(&mut self, stx: Stx) -> Result<String, ExpandError> {
        if !self.is_id(stx) {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        Ok(self.text(stx).expect("an identifier"))
    }

    /// The text of `stx`, if it's an identifier or a string.
    pub(crate) fn text(&mut self, stx: Stx) -> Option<String> {
        let s = match self.tree.symbol(stx) {
            Some(symbol) => symbol.name(self.mc),
            None => match self.tree.view(stx).ok()? {
                View::Datum(value) => self.strings.string(value)?,
                _ => return None,
            },
        };
        Some(chars(&self.strings, s).collect())
    }

    fn module_error(&self, e: ModuleError, stx: Stx) -> ExpandError {
        let kind = match e {
            ModuleError::Duplicate => ExpandErrorKind::Duplicate,
            ModuleError::Conflict => ExpandErrorKind::Conflict,
            ModuleError::NotDefined => ExpandErrorKind::NotDefined,
            ModuleError::Immutable => ExpandErrorKind::Immutable,
            ModuleError::OutOfMemory => OutOfMemory.into(),
        };
        self.error(kind, stx)
    }

    /// Expands `top`, the module's top-level form `form`, once it's started.
    pub fn lower(&mut self, top: Top, form: u32) -> Result<Core<'gc>, ExpandError> {
        self.form = form;
        match top.0 {
            TopForm::Define(slot, value) => {
                let lambda = matches!(self.tree.view(value)?, View::List(items, None) if items.first().is_some_and(|&head| {
                    self.is_id(head) && matches!(self.resolve(head), Ok(Binding::Keyword(Keyword::Form(Form::Lambda))))
                }));
                self.defining = lambda.then_some(slot);
                let value = self.expand_now(value);
                self.defining = None;
                let value = value?;
                self.builder.defined(slot, &value);
                Ok(Core::Set(Place::Slot { slot, checked: false }, Box::new(value)))
            }
            TopForm::DefineKeyword { procedure, core, lambda } => {
                self.defining = Some(core);
                let made = self.run_now(move |this| {
                    this.keyword_definition(lambda, move |this, lambda, shape| {
                        let lambda = Core::Lambda(lambda);
                        this.builder.defined(core, &lambda);
                        let place = this.builder.place(core, this.form, None);
                        let value = this.keyword_procedure(&shape, Core::Ref(place))?;
                        let core = Core::Set(Place::Slot { slot: core, checked: false }, Box::new(lambda));
                        let procedure = Core::Set(Place::Slot { slot: procedure, checked: false }, Box::new(value));
                        Ok(Step::Done(Core::Let(vec![(this.fresh(), core)], Box::new(procedure))))
                    })
                });
                self.defining = None;
                made
            }
            TopForm::Struct(declared) => Ok(self.lower_struct(declared)),
            TopForm::Expr(e) => self.expand_now(e),
        }
    }

    /// The core of the keyword procedure `lambda`, a `lambda` form with keyword parameters, and
    /// its shape, to `then`.
    fn keyword_definition(&mut self, lambda: Stx, then: impl FnOnce(&mut Self, Lambda<'gc>, CallShape<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        let items = self.proper(lambda)?;
        let scope = self.tree.scopes.fresh()?;
        let formals = self.tree.with(items[1], scope, Op::Add)?;
        let formals = self.formals(formals)?;
        self.optional_lambda(lambda, formals, items[2..].to_vec(), scope, then)
    }

    /// The module, once its forms are compiled.
    pub fn finish(self) -> Result<Gc<'gc, Module>, OutOfMemory> {
        self.builder.finish(self.mc)
    }

    /// `e`, or if it says nowhere, as running out of room does, `e` where `stx` is.
    fn placed(&self, e: ExpandError, stx: Stx) -> ExpandError {
        if e.start == e.end { self.error(e.kind, stx) } else { e }
    }

    /// Whether `form` is a definition, of a variable or a macro, a `begin`, or some other
    /// expression, once the macro uses it is are expanded.
    fn head(&mut self, form: Stx) -> Result<Head, ExpandError> {
        self.head_of(form).map_err(|e| self.placed(e, form))
    }

    fn head_of(&mut self, mut form: Stx) -> Result<Head, ExpandError> {
        loop {
            let (head, alone) = match self.tree.view(form)? {
                View::Id => (form, true),
                View::List(items, None) if items.first().is_some_and(|&head| self.is_id(head)) => (items[0], false),
                _ => return Ok(Head::Expr(form)),
            };
            form = match self.resolve(head)? {
                Binding::Macro(m) => self.expand_macro(m, form)?,
                _ if alone => return Ok(Head::Expr(form)),
                Binding::Keyword(Keyword::Macro(m)) => self.transform(m, form)?,
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

    /// The identifier a `define` binds and the expression it binds it to. `(define (f . formals)
    /// body ...)` is `(define f (lambda formals body ...))`, and `f` can itself be such a list.
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

    /// The slot of the module variable a definition of `id`, in top-level form `form`, defines:
    /// one its name refers to if it's in just the top-level scope, or else one only identifiers
    /// with its scopes do.
    pub(crate) fn define_top(&mut self, id: Stx, form: u32) -> Result<u32, ExpandError> {
        let name = self.tree.symbol(id).expect("definitions bind identifiers").value(self.mc);
        if self.tree.scopes_of(id)? == self.top {
            return self.builder.define(name, form).map_err(|e| self.module_error(e, id));
        }
        let slot = self.builder.define_private(name, form).map_err(|e| self.module_error(e, id))?;
        self.bind(id, Binding::Slot(slot))?;
        Ok(slot)
    }

    /// What `id` refers to.
    pub(crate) fn resolve(&mut self, id: Stx) -> Result<Binding<'gc>, ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers resolve");
        let set = self.tree.scopes_of(id)?;
        self.resolve_name(symbol, set).map_err(|Ambiguous| self.error(ExpandErrorKind::Ambiguous, id))
    }

    /// What an identifier named `symbol` with the scopes `set` refers to.
    pub(crate) fn resolve_name(&self, symbol: Symbol<'gc>, set: Set) -> Result<Binding<'gc>, Ambiguous> {
        let k = key(symbol, self.mc);
        let scopes = &self.tree.scopes;
        // A binding visible to `id` is under one of `id`'s scopes, so look up whichever list
        // is shorter: `id`'s scopes, or those the name is bound under that are among them.
        let bound_in = self.bound_in.get(&k).map_or(&[][..], Vec::as_slice);
        let own = scopes.scopes(set);
        let (bound_in, own) = if bound_in.len() < own.len() { (bound_in, &[][..]) } else { (&[][..], own) };
        let candidates = || {
            let under = bound_in.iter().filter(|&&scope| scopes.contains(set, scope)).chain(own);
            let lists = under.filter_map(|&scope| self.bindings.get(&(scope, k)));
            lists.flatten().filter(|&&(s, _)| scopes.subset(s, set))
        };
        let mut best: Option<(Set, Binding<'gc>)> = None;
        for &(s, binding) in candidates() {
            if best.is_none_or(|(b, _)| scopes.subset(b, s)) {
                best = Some((s, binding));
            }
        }
        if let Some((best, binding)) = best {
            if candidates().any(|&(s, _)| !scopes.subset(s, best)) {
                return Err(Ambiguous);
            }
            return Ok(binding);
        }
        // What's introduced as the base's means the prelude's, whatever the module binds.
        let base = self.tree.scopes.contains(set, BASE);
        if !base && let Some(binding) = self.builder.binding(symbol.value(self.mc)) {
            return Ok(match binding {
                module::Binding::Slot(slot) => Binding::Slot(slot),
                module::Binding::Import(import) => Binding::Import(import),
            });
        }
        if let Some(&keyword) = self.keywords.get(&k) {
            return Ok(Binding::Keyword(keyword));
        }
        if base && let Some(&import) = self.base_cells.get(&k) {
            return Ok(Binding::Import(import));
        }
        Ok(Binding::Free)
    }

    pub(crate) fn bind(&mut self, id: Stx, binding: Binding<'gc>) -> Result<(), ExpandError> {
        let symbol = self.tree.symbol(id).expect("only identifiers are bound");
        let set = self.tree.scopes_of(id)?;
        self.tree.scopes.charge(size_of::<(Set, Binding)>())?;
        let newest = self.tree.scopes.scopes(set).last().copied().unwrap_or(TOP);
        let k = key(symbol, self.mc);
        let under = self.bindings.entry((newest, k)).or_default();
        if under.is_empty() {
            self.tree.scopes.charge(size_of::<Scope>())?;
            self.bound_in.entry(k).or_default().push(newest);
        }
        under.push((set, binding));
        Ok(())
    }

    pub(crate) fn local(&mut self, id: Stx) -> Result<Var, ExpandError> {
        let var = self.fresh();
        self.bind(id, Binding::Local(var))?;
        Ok(var)
    }

    pub(crate) fn fresh(&mut self) -> Var {
        let var = Var(self.vars);
        self.vars = self.vars.checked_add(1).expect("fewer than 2^32 variables");
        var
    }

    /// Fails on the second of any two `ids` with the same name and scopes.
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

    /// Applies the macro `m` to its use `stx`, flipping a fresh scope on what it's given and
    /// what it makes.
    pub(crate) fn transform(&mut self, m: Macro, stx: Stx) -> Result<Stx, ExpandError> {
        let intro = self.tree.scopes.fresh()?;
        let input = self.tree.with(stx, intro, Op::Flip)?;
        let output = self.derived(m, input)?;
        Ok(self.tree.with(output, intro, Op::Flip)?)
    }

    /// The core forms of the expression `stx`, made from a stack of what's waiting on each
    /// part, so expanding it takes no more of the machine's stack however deeply it nests.
    pub(crate) fn expand_now(&mut self, stx: Stx) -> Result<Core<'gc>, ExpandError> {
        steps::run(self, Call::Expr(stx), Self::step)
    }

    /// What `f` makes, as [`expand_now`](Self::expand_now) makes it.
    pub(crate) fn run_now(&mut self, f: impl FnOnce(&mut Self) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Core<'gc>, ExpandError> {
        steps::run(self, Call::Run(Box::new(f)), Self::step)
    }

    /// A step of expansion. An error that says nowhere, as running out of room does, is where
    /// the expression being expanded is.
    fn step(&mut self, call: Call<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> {
        match call {
            Call::Expr(stx) => self.expand(stx).map_err(|e| self.placed(e, stx)),
            Call::Run(f) => f(self),
        }
    }

    /// The expression `stx`, expanded, then `then`.
    pub(crate) fn expr(stx: Stx, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Ok(Step::then(Call::Expr(stx), then))
    }

    /// Each of `stxs`, expanded in order, then `then`.
    pub(crate) fn exprs(stxs: Vec<Stx>, then: impl FnOnce(&mut Self, Vec<Core<'gc>>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        steps::all(stxs.into_iter().map(Call::Expr).collect(), then)
    }

    /// The body `forms` of the form `stx`, expanded, then `then`.
    pub(crate) fn body_then(stx: Stx, forms: Vec<Stx>, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a) -> Result<Ex<'a, 'gc>, ExpandError> {
        Ok(Step::then(Call::Run(Box::new(move |this: &mut Self| this.body(stx, forms))), then))
    }

    /// The step `stx` takes: what it is if it's done, or what it needs expanded first.
    fn expand(&mut self, stx: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        match self.tree.view(stx)? {
            View::Id => self.reference(stx),
            // A keyword isn't an expression, as in Racket: it's quoted to be a value.
            View::Datum(value) if ragwort_types::symbol::Keyword::of(value).is_some() => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
            View::Datum(value) => Ok(Step::Done(Core::Quote(value))),
            View::Vector(_) => Ok(Step::Done(Core::Quote(self.strip(stx)?))),
            View::List(items, tail) => self.compound(stx, items, tail),
        }
    }

    fn compound(&mut self, stx: Stx, items: Vec<Stx>, tail: Option<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some(&head) = items.first() else { return Err(self.error(ExpandErrorKind::BadSyntax, stx)) };
        let (mut def, mut of_struct) = (None, None);
        if self.is_id(head) {
            match self.resolve(head)? {
                Binding::Keyword(Keyword::Form(form)) => return self.form(form, stx, items, tail),
                Binding::Keyword(Keyword::Macro(m)) => return Ok(Step::Tail(Call::Expr(self.transform(m, stx)?))),
                Binding::Keyword(Keyword::Aux(_)) => return Err(self.error(ExpandErrorKind::BadSyntax, head)),
                Binding::Macro(m) => return Ok(Step::Tail(Call::Expr(self.expand_macro(m, stx)?))),
                Binding::Import(import) if tail.is_none() => {
                    def = self.imported_keyword_def(import);
                    if def.is_none() && !self.has_keyword_args(&items[1..]) {
                        return Self::exprs(items[1..].to_vec(), move |this, args| {
                            let mc = this.mc;
                            let call = import.call(mc, args, &mut || this.fresh());
                            call.map(Step::Done).map_err(|Uninitialized| this.error(ExpandErrorKind::Unbound, head))
                        });
                    }
                }
                Binding::Local(var) => {
                    def = self.keyword_defs.get(&var).cloned();
                    if let Some(Local::Procedure(inline, kind)) = self.struct_locals.get(&var) {
                        of_struct = Some(structs::Call::new(inline.clone(), Core::Ref(Place::Local(*kind)), None));
                    }
                }
                Binding::Slot(slot) => {
                    def = self.builder.keyword_def(slot).map(|(core, shape)| KeywordDef { core: CoreAt::Slot(core), shape: shape.clone() });
                    of_struct = self.builder.struct_call(slot, self.form);
                }
                _ => {}
            }
        }
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        // A call of a struct's procedure that takes the arguments does what it does itself.
        if let Some(call) = of_struct
            && call.takes(items.len() - 1)
            && !self.has_keyword_args(&items[1..])
        {
            return Self::exprs(items[1..].to_vec(), move |this, args| Ok(Step::Done(call.core(args, &mut || this.fresh()))));
        }
        if def.is_some() || self.has_keyword_args(&items[1..]) {
            return self.keyword_call(head, items[1..].to_vec(), def);
        }
        Self::expr(head, move |_, f| Self::exprs(items[1..].to_vec(), move |_, args| Ok(Step::Done(Core::App(Box::new(f), args)))))
    }

    fn form(&mut self, form: Form, stx: Stx, items: Vec<Stx>, tail: Option<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let bad = |this: &Self| Err(this.error(ExpandErrorKind::BadSyntax, stx));
        if tail.is_some() {
            return bad(self);
        }
        match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Ok(Step::Done(Core::Quote(self.strip(datum)?))),
            (Form::If, &[test, then]) => Self::exprs(vec![test, then], |_, parts| {
                let [test, then] = <[Core<'gc>; 2]>::try_from(parts).map_err(|_| ()).expect("two parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(Core::Quote(Value::VOID)))))
            }),
            (Form::If, &[test, then, other]) => Self::exprs(vec![test, then, other], |_, parts| {
                let [test, then, other] = <[Core<'gc>; 3]>::try_from(parts).map_err(|_| ()).expect("three parts");
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
            _ => bad(self),
        }
    }

    fn reference(&mut self, id: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Slot(slot) => self.builder.place(slot, self.form, self.defining),
            Binding::Import(import) => return import.reference(self.mc).map(Step::Done).map_err(|Uninitialized| self.error(ExpandErrorKind::Unbound, id)),
            Binding::Free => return Err(self.error(ExpandErrorKind::Unbound, id)),
            Binding::Macro(m) => return Ok(Step::Tail(Call::Expr(self.expand_macro(m, id)?))),
            Binding::Keyword(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Ok(Step::Done(Core::Ref(place)))
    }

    fn set(&mut self, id: Stx, value: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            // Calls of a keyword procedure a definition made go to its core, as if it can't change:
            // the module builder rules out assigning a module variable that is one.
            Binding::Local(var) if self.keyword_defs.contains_key(&var) || self.struct_locals.contains_key(&var) => {
                return Err(self.error(ExpandErrorKind::Immutable, id));
            }
            Binding::Local(var) => Place::Local(var),
            Binding::Slot(slot) => {
                self.builder.assign(slot).map_err(|e| self.module_error(e, id))?;
                self.builder.place(slot, self.form, self.defining)
            }
            Binding::Import(_) => return Err(self.error(ExpandErrorKind::Immutable, id)),
            Binding::Free => return Err(self.error(ExpandErrorKind::Unbound, id)),
            Binding::Keyword(_) | Binding::Macro(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Self::expr(value, move |_, value| Ok(Step::Done(Core::Set(place, Box::new(value)))))
    }

    /// Expressions run in order, with the last one's value.
    fn sequence(&mut self, mut stxs: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let last = stxs.pop().expect("sequences aren't empty");
        self.sequence_from(stxs.into_iter(), Vec::new(), last)
    }

    /// The rest of a sequence: the expressions `before` its `last`, each bound to a variable no
    /// one reads, after those of `binds`.
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
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        id
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
        Self::body_then(stx, body, move |this, body| Ok(Step::Done(Core::Lambda(Lambda { id: this.lambda_id(), params, optional: 0, rest, body: Box::new(body) }))))
    }

    /// A `let`, or if `recursive`, a `letrec`.
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
        let finish = move |this: &mut Self, vars: Vec<Var>, inits: Vec<Core<'gc>>| {
            let body = this.scoped(&body, scope)?;
            Self::body_then(stx, body, move |_, body| {
                let binds = vars.into_iter().zip(inits).collect();
                let body = Box::new(body);
                Ok(Step::Done(if recursive { Core::Letrec(binds, body) } else { Core::Let(binds, body) }))
            })
        };
        if recursive {
            let vars: Vec<_> = ids.iter().map(|&id| self.local(id)).collect::<Result<_, _>>()?;
            let inits = self.scoped(&inits, scope)?;
            Self::exprs(inits, move |this, inits| finish(this, vars, inits))
        } else {
            Self::exprs(inits, move |this, inits| {
                let vars = ids.iter().map(|&id| this.local(id)).collect::<Result<_, _>>()?;
                finish(this, vars, inits)
            })
        }
    }

    /// A body: definitions and expressions in any order, as `letrec*` binds them, then an
    /// expression for its value. `stx` is the form it's the body of.
    pub(crate) fn body(&mut self, stx: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let mut queue = self.scoped(&body, scope)?;
        queue.reverse();
        self.scan(Scan { stx, queue, items: Vec::new(), defined: Vec::new(), names: Vec::new() })
    }

    /// Goes on looking at a body's forms till they're all found, each macro one defines made
    /// before those after it are looked at, then expands what they define and do.
    fn scan(&mut self, mut s: Scan<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> {
        while let Some(form) = s.queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    s.defined.push(id);
                    s.names.push(id);
                    match self.keyword_lambda(value)? {
                        Some(shape) => {
                            let (procedure, core) = (self.local(id)?, self.fresh());
                            self.keyword_defs.insert(procedure, KeywordDef { core: CoreAt::Local(core), shape });
                            s.items.push(Item::Keyword(procedure, core, value));
                        }
                        None => s.items.push(Item::Define(self.local(id)?, value)),
                    }
                }
                Head::DefineSyntax(form) => {
                    let (id, expr) = self.syntax_definition(form)?;
                    return self.transformer(expr, form, move |this, m| {
                        s.names.push(id);
                        this.bind(id, Binding::Macro(m))?;
                        this.scan(s)
                    });
                }
                Head::Require(form) | Head::Provide(form) => return Err(self.error(ExpandErrorKind::Definition, form)),
                Head::Begin(forms) => s.queue.extend(forms.into_iter().rev()),
                Head::Struct(form) => {
                    for (id, var, value) in self.local_struct(form)? {
                        s.defined.push(id);
                        s.names.push(id);
                        s.items.push(Item::Made(var, value));
                    }
                }
                Head::Expr(e) => s.items.push(Item::Expr(e)),
            }
        }
        self.distinct(&s.names)?;
        let Some(Item::Expr(last)) = s.items.pop() else { return Err(self.error(ExpandErrorKind::NoExpression, s.stx)) };
        if s.defined.is_empty() {
            let mut stxs: Vec<Stx> = s.items.into_iter().filter_map(|item| if let Item::Expr(e) = item { Some(e) } else { None }).collect();
            stxs.push(last);
            return self.sequence(stxs);
        }
        let n = s.items.len();
        self.defines(s.items.into_iter(), Vec::with_capacity(n), last)
    }

    /// The rest of a body's definitions and expressions, `items`, bound after `binds`, then its
    /// `last` expression.
    fn defines(&mut self, mut items: std::vec::IntoIter<Item<'gc>>, mut binds: Vec<(Var, Core<'gc>)>, last: Stx) -> Result<Ex<'a, 'gc>, ExpandError> {
        let (var, value) = loop {
            match items.next() {
                None => return Self::expr(last, move |_, last| Ok(Step::Done(Core::Letrec(binds, Box::new(last))))),
                Some(Item::Define(var, value)) => break (var, value),
                Some(Item::Expr(e)) => break (self.fresh(), e),
                Some(Item::Made(var, value)) => binds.push((var, value)),
                Some(Item::Keyword(procedure, core, lambda)) => {
                    return self.keyword_definition(lambda, move |this, lambda, shape| {
                        binds.push((core, Core::Lambda(lambda)));
                        binds.push((procedure, this.keyword_procedure(&shape, Core::Ref(Place::Local(core)))?));
                        this.defines(items, binds, last)
                    });
                }
            }
        };
        Self::expr(value, move |this, value| {
            binds.push((var, value));
            this.defines(items, binds, last)
        })
    }

    /// `stxs` with `scope` added.
    pub(crate) fn scoped(&mut self, stxs: &[Stx], scope: Scope) -> Result<Vec<Stx>, ExpandError> {
        Ok(stxs.iter().map(|&stx| self.tree.with(stx, scope, Op::Add)).collect::<Result<_, _>>()?)
    }

    pub(crate) fn strip(&mut self, stx: Stx) -> Result<Value<'gc>, ExpandError> {
        self.tree.strip(stx).map_err(|e| self.error(e, stx))
    }

    pub(crate) fn is_id(&self, stx: Stx) -> bool {
        self.tree.symbol(stx).is_some()
    }

    /// Whether `stx` is an identifier that means `aux`.
    pub(crate) fn is_aux(&mut self, stx: Stx, aux: Aux) -> Result<bool, ExpandError> {
        Ok(self.is_id(stx) && matches!(self.resolve(stx)?, Binding::Keyword(Keyword::Aux(a)) if a == aux))
    }

    /// The items of `stx`, a proper list.
    pub(crate) fn proper(&mut self, stx: Stx) -> Result<Vec<Stx>, ExpandError> {
        match self.tree.view(stx)? {
            View::List(items, None) => Ok(items),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }

    pub(crate) fn symbol(&self, name: &str) -> Result<Symbol<'gc>, ExpandError> {
        Ok(self.symbols.intern_str(&self.strings, name)?)
    }

    /// An identifier for the base binding of `name`, which nothing read can shadow, at `at`.
    pub(crate) fn introduce(&mut self, name: &str, at: Stx) -> Result<Stx, ExpandError> {
        let symbol = self.symbol(name)?;
        let span = self.tree.span(at);
        Ok(self.tree.id(symbol, self.base, span)?)
    }
}
