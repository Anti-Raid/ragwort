//! Lowering: native ragwort's syntax to core forms.

use std::collections::{HashMap, HashSet};
use std::fmt;

use ragwort_compiler::keyword;
use ragwort_compiler::module::{Filter, Item, Locals, ModuleError, Provide, Require, RequireSpec, Unusable};
use ragwort_compiler::steps::{self, Step};
use ragwort_compiler::structs::{self, Declaration};
use ragwort_compiler::{Arg, CompileError, Core, Formal, GlobalError, Lambda, OptionalLambda, Place, Position, Prim, Var};
use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Keyword, Symbol, Symbols};
use ragwort_types::vector::Vectors;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind, SyntaxSpan};
use ragwort_vm::structs::TypeFlags;
use ragwort_vm::{HostDef, Intrinsic, Request};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LowerErrorKind {
    /// A list that doesn't start with a form's name, such as a call not written as an `%app`.
    NotAForm,
    /// A form whose parts aren't the ones it takes.
    BadShape,
    /// A name bound twice by one `%let`, `%letrec` or `%lambda`, or a module that defines or
    /// provides a name twice.
    Duplicate,
    /// A name that's no local, definition of the module's or import.
    Unbound,
    /// A name the module both defines and requires, or requires as two different things.
    Conflict,
    /// A `%set!` of an import, a struct's binding or a keyword procedure.
    Immutable,
    /// A `%define`, `%struct`, `%require` or `%provide` that isn't at the top level.
    Definition,
    /// A module the resolver doesn't have, or one it gave that no [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder) built.
    Resolve,
    /// A require of a name the module doesn't export.
    NotProvided,
    /// A provide of a name the module doesn't define.
    NotDefined,
    /// A reference to an export of a module that hasn't defined it yet.
    Uninitialized,
    /// The name of a struct whose module provides it without its constructor, used as a value.
    NoConstructor,
    /// An `%intrinsic` of a name that isn't one the code can name.
    UnknownIntrinsic,
    /// A `%call-host` of a name that isn't one of the host functions the code was given.
    UnknownHost,
    /// An `%intrinsic` or `%call-host` with a number of arguments it doesn't take.
    Arity,
    /// Syntax native ragwort doesn't have, such as a quasiquote outside a quoted datum.
    Unsupported,
    /// The arena couldn't make a value lowering needed.
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

/// What went wrong, and the bytes `start..end` of the text where.
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
            LowerErrorKind::Unsupported => "syntax native ragwort doesn't have",
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    Quote,
    If,
    Let,
    LetStar,
    Letrec,
    Set,
    Define,
    Struct,
    Require,
    Provide,
    Lambda,
    App,
    Intrinsic,
    ApplyIntrinsic,
    CallHost,
}

const FORMS: [(&str, Form); 15] = [
    ("%struct", Form::Struct),
    ("%quote", Form::Quote),
    ("%if", Form::If),
    ("%let", Form::Let),
    ("%let*", Form::LetStar),
    ("%letrec", Form::Letrec),
    ("%set!", Form::Set),
    ("%define", Form::Define),
    ("%require", Form::Require),
    ("%provide", Form::Provide),
    ("%lambda", Form::Lambda),
    ("%app", Form::App),
    ("%intrinsic", Form::Intrinsic),
    ("%apply-intrinsic", Form::ApplyIntrinsic),
    ("%call-host", Form::CallHost),
];

/// Lowers the forms of a module's native files, each to an [`Item`] with [`Lowerer::item`]. The
/// items make the module's [`Description`](ragwort_compiler::module::Description), or go to the
/// builder of a module that has forms in other languages too.
pub struct Lowerer<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    pairs: Pairs<'a, 'gc>,
    strings: Strings<'a, 'gc>,
    /// The forms and the built-ins, by their names' words.
    forms: HashMap<u64, Form>,
    prims: HashMap<u64, Prim>,
    /// The host functions, by their names' words.
    hosts: HashMap<u64, &'static HostDef>,
    /// The symbols each [`Abbreviation`] stands for, in order, for what they read
    /// as in a quoted datum.
    abbreviations: Vec<Value<'gc>>,
    /// The locals in scope of each name, innermost last.
    scope: HashMap<u64, Vec<Var>>,
}

/// A `%lambda`'s formals: each parameter, its name and its default, if it has one, as they're
/// written, and the rest parameter.
struct Formals<'gc> {
    params: Vec<keyword::Param<'gc>>,
    names: Vec<Syntax<'gc>>,
    defaults: Vec<Option<Syntax<'gc>>>,
    rest: Option<Syntax<'gc>>,
}

impl Formals<'_> {
    fn is_plain(&self) -> bool {
        self.params.iter().all(|param| param.keyword.is_none() && !param.optional)
    }
}

impl<'a, 'gc> Lowerer<'a, 'gc> {
    /// A lowerer of code that calls the host functions `hosts`. The code's `%intrinsic`s name
    /// [internal intrinsics](Intrinsic::is_internal) only if `internals`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, hosts: &'static [HostDef], internals: bool) -> Result<Self, Error> {
        let strings = Strings::new(mc);
        let symbol = |name: &str| symbols.intern_str(&strings, name).map(|interned| interned.value(mc));
        let mut forms = HashMap::new();
        for (name, form) in FORMS {
            forms.insert(symbol(name)?.to_bits(), form);
        }
        let mut prims = HashMap::new();
        for &intrinsic in Intrinsic::ALL {
            if internals || !intrinsic.is_internal() {
                prims.insert(symbol(intrinsic.name())?.to_bits(), Prim::Intrinsic(intrinsic));
            }
        }
        for &request in Request::ALL {
            prims.insert(symbol(request.name())?.to_bits(), Prim::Request(request));
        }
        let mut named_hosts = HashMap::new();
        for def in hosts {
            named_hosts.insert(symbol(def.name)?.to_bits(), def);
        }
        let mut abbreviations = Vec::with_capacity(Abbreviation::ALL.len());
        for abbreviation in Abbreviation::ALL {
            abbreviations.push(symbol(abbreviation.name())?);
        }
        Ok(Self {
            mc,
            pairs: Pairs::new(mc),
            strings,
            forms,
            prims,
            hosts: named_hosts,
            abbreviations,
            scope: HashMap::new(),
        })
    }

    /// Lowers the top-level form `node` to an [`Item`]. Local variables are allocated from `locals`.
    ///
    /// The item refers to module-level bindings by name: what it defines, requires, provides and uses. The module builder resolves those names.
    pub fn item(&mut self, locals: &mut Locals<'gc>, node: Syntax<'gc>) -> Result<Item<'gc>, LowerError> {
        self.scope.clear();
        let items = match self.head(node) {
            Some(Form::Define | Form::Struct | Form::Require | Form::Provide) => self.list(node)?,
            _ => return Ok(Item::Expr(self.expr(locals, node)?)),
        };
        match (self.head(node), &items[1..]) {
            (Some(Form::Struct), parts) => Ok(Item::Struct(self.struct_form(node, parts)?)),
            (Some(Form::Define), &[name, value]) => {
                self.name(name)?;
                Ok(Item::Define(name.datum(self.mc), name.span(self.mc), self.expr(locals, value)?))
            }
            (Some(Form::Require), specs) => {
                let mut requires = Vec::with_capacity(specs.len());
                for &spec in specs {
                    requires.push(Require { spec: self.spec(spec)?, span: spec.span(self.mc) });
                }
                Ok(Item::Require(requires))
            }
            (Some(Form::Provide), specs) => {
                let mut provides = Vec::new();
                for &spec in specs {
                    self.provide_spec(spec, &mut provides)?;
                }
                Ok(Item::Provide(provides))
            }
            _ => Err(self.error(LowerErrorKind::BadShape, node)),
        }
    }

    /// The declaration a `%struct` form makes: `node`, whose parts after its head are `parts`.
    /// It's written as Scheme's `struct` is, and defines what that does, as [`structs`] says:
    /// `(%struct name (field ...) option ...)`, with a supertype's name before the fields for a
    /// subtype of it.
    fn struct_form(&self, node: Syntax<'gc>, parts: &[Syntax<'gc>]) -> Result<structs::Form<'gc>, LowerError> {
        let bad = LowerErrorKind::BadShape;
        let is_name = |node: &Syntax<'gc>| node.kind(self.mc) == Some(SyntaxKind::Identifier);
        let option = |node: Syntax<'gc>| self.keyword(node).map(|keyword| chars(&self.strings, keyword.symbol(self.mc).name(self.mc)).collect::<String>());
        let mut rest = parts.iter().copied();
        let Some(name) = rest.next().filter(is_name) else { return Err(self.error(bad, node)) };
        let Some(mut next) = rest.next() else { return Err(self.error(bad, node)) };
        let mut parent = None;
        if is_name(&next) {
            parent = Some(next);
            next = rest.next().ok_or_else(|| self.error(bad, node))?;
        }
        // Each field the form declares: its name, and whether it's mutable.
        let mut own: Vec<(Syntax<'gc>, bool)> = Vec::new();
        for spec in self.list(next)? {
            if is_name(&spec) {
                own.push((spec, false));
                continue;
            }
            let written = self.list(spec)?;
            let mut options = written.iter().copied();
            let Some(id) = options.next().filter(is_name) else { return Err(self.error(bad, spec)) };
            if !options.all(|at| option(at).as_deref() == Some("mutable")) {
                return Err(self.error(bad, spec));
            }
            own.push((id, written.len() > 1));
        }
        self.distinct(&own.iter().map(|&(id, _)| id).collect::<Vec<_>>())?;
        let (mut constructors, mut flags) = (Vec::new(), TypeFlags::empty());
        while let Some(at) = rest.next() {
            match option(at).as_deref() {
                Some("mutable") => own.iter_mut().for_each(|(_, mutable)| *mutable = true),
                Some("identity-eq?") => flags |= TypeFlags::IDENTITY,
                Some("sealed") => flags |= TypeFlags::SEALED,
                Some("transparent") => {}
                Some("constructor-name" | "extra-constructor-name") => {
                    let Some(id) = rest.next().filter(is_name) else { return Err(self.error(bad, at)) };
                    constructors.push(id);
                }
                _ => return Err(self.error(bad, at)),
            }
        }
        let spanned = |node: Syntax<'gc>| (node.datum(self.mc), node.span(self.mc));
        Ok(structs::Form {
            name: spanned(name),
            span: node.span(self.mc),
            parent: parent.map(spanned),
            fields: own.iter().map(|&(id, mutable)| Declaration { name: id.datum(self.mc), mutable }).collect(),
            flags,
            constructors: constructors.into_iter().map(spanned).collect(),
        })
    }

    /// The parameters `formals` has: names, `[name default]`s and keywords before either, and a
    /// rest parameter, as Racket's `lambda` takes them.
    fn formals(&self, formals: Syntax<'gc>) -> Result<Formals<'gc>, LowerError> {
        let mut parsed = Formals { params: Vec::new(), names: Vec::new(), defaults: Vec::new(), rest: None };
        let items = match formals.kind(self.mc) {
            Some(SyntaxKind::Identifier) => {
                parsed.rest = Some(formals);
                return Ok(parsed);
            }
            Some(SyntaxKind::List) => {
                let mut elements = self.pairs.elements(formals.datum(self.mc));
                let items = elements.by_ref().map(|value| self.syntax(value, formals)).collect::<Result<Vec<_>, _>>()?;
                let rest = elements.rest();
                parsed.rest = if rest == Value::NIL { None } else { Some(self.name(self.syntax(rest, formals)?)?) };
                items
            }
            _ => return Err(self.error(LowerErrorKind::BadShape, formals)),
        };
        let mut items = items.into_iter();
        while let Some(item) = items.next() {
            let keyword = self.keyword(item);
            let at = match keyword {
                Some(_) => items.next().ok_or_else(|| self.error(LowerErrorKind::BadShape, item))?,
                None => item,
            };
            let (name, default) = match at.kind(self.mc) {
                Some(SyntaxKind::Identifier) => (at, None),
                Some(SyntaxKind::List) => match self.list(at)?.as_slice() {
                    &[name, default] => (self.name(name)?, Some(default)),
                    _ => return Err(self.error(LowerErrorKind::BadShape, at)),
                },
                _ => return Err(self.error(LowerErrorKind::BadShape, at)),
            };
            if keyword.is_some() && parsed.params.iter().any(|param| param.keyword == keyword) {
                return Err(self.error(LowerErrorKind::Duplicate, item));
            }
            // As in Racket, a required positional parameter can't follow an optional one.
            if keyword.is_none() && default.is_none() && parsed.params.iter().any(|param| param.keyword.is_none() && param.optional) {
                return Err(self.error(LowerErrorKind::BadShape, at));
            }
            parsed.params.push(keyword::Param { keyword, optional: default.is_some() });
            parsed.names.push(name);
            parsed.defaults.push(default);
        }
        Ok(parsed)
    }

    /// The keyword `node` is, if it's one.
    fn keyword(&self, node: Syntax<'gc>) -> Option<Keyword<'gc>> {
        if node.kind(self.mc) != Some(SyntaxKind::Literal) {
            return None;
        }
        Keyword::of(node.datum(self.mc))
    }

    /// The form `node` is, if it's a list that starts with one's name.
    fn head(&self, node: Syntax<'gc>) -> Option<Form> {
        if node.kind(self.mc) != Some(SyntaxKind::List) {
            return None;
        }
        let head = Syntax::of(Pair::of(node.datum(self.mc))?.head(self.mc))?;
        if head.kind(self.mc) != Some(SyntaxKind::Identifier) {
            return None;
        }
        self.forms.get(&head.datum(self.mc).to_bits()).copied()
    }

    /// The require spec `spec`: its filters, outermost first as they're written, then the
    /// module inside them.
    fn spec(&self, mut spec: Syntax<'gc>) -> Result<RequireSpec<SyntaxSpan<'gc>>, LowerError> {
        let mut filters = Vec::new();
        loop {
            if let Some(module) = self.text(spec) {
                filters.reverse();
                return Ok(RequireSpec { module, at: spec.span(self.mc), filters });
            }
            let items = self.list(spec)?;
            let Some((&head, args)) = items.split_first() else { return Err(self.error(LowerErrorKind::BadShape, spec)) };
            let word = self.text(head).filter(|_| head.kind(self.mc) == Some(SyntaxKind::Identifier));
            let named = |node: &Syntax<'gc>| -> Result<(String, SyntaxSpan<'gc>), LowerError> { Ok((self.identifier(*node)?, node.span(self.mc))) };
            let (filter, inner) = match (word.as_deref(), args) {
                (Some("only-in"), &[inner, ref names @ ..]) => (Filter::Only(names.iter().map(named).collect::<Result<_, _>>()?), inner),
                (Some("except-in"), &[inner, ref names @ ..]) => (Filter::Except(names.iter().map(named).collect::<Result<_, _>>()?), inner),
                (Some("prefix-in"), &[prefix, inner]) => (Filter::Prefix(self.identifier(prefix)?), inner),
                (Some("rename-in"), &[inner, ref renames @ ..]) => {
                    let renames = renames.iter().map(|&rename| self.pair_of_names(rename).map(|(old, new)| (old, new, rename.span(self.mc)))).collect::<Result<_, _>>()?;
                    (Filter::Rename(renames), inner)
                }
                _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
            };
            filters.push(filter);
            spec = inner;
        }
    }

    /// Exports what the provide spec `spec` names.
    fn provide_spec(&self, spec: Syntax<'gc>, out: &mut Vec<Provide<'gc>>) -> Result<(), LowerError> {
        let span = spec.span(self.mc);
        if spec.kind(self.mc) == Some(SyntaxKind::Identifier) {
            out.push(Provide::Variable { name: spec.datum(self.mc), external: self.identifier(spec)?, span });
            return Ok(());
        }
        let items = self.list(spec)?;
        let Some((&head, args)) = items.split_first() else { return Err(self.error(LowerErrorKind::BadShape, spec)) };
        let word = if head.kind(self.mc) == Some(SyntaxKind::Identifier) { self.text(head) } else { None };
        match (word.as_deref(), args) {
            (Some("all-defined-out"), []) => out.push(Provide::AllDefined(span)),
            (Some("struct-out"), &[name, ref options @ ..]) => {
                self.name(name)?;
                let constructors = match options {
                    [] => true,
                    &[option] if self.keyword(option).is_some_and(|keyword| chars(&self.strings, keyword.symbol(self.mc).name(self.mc)).eq("omit-constructor".chars())) => false,
                    _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
                };
                out.push(Provide::Struct { name: name.datum(self.mc), constructors, span: name.span(self.mc) });
            }
            (Some("rename-out"), renames) => {
                for &rename in renames {
                    let &[inner, external] = self.list(rename)?.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, rename)) };
                    self.name(inner)?;
                    let external = self.identifier(external)?;
                    out.push(Provide::Variable { name: inner.datum(self.mc), external, span: rename.span(self.mc) });
                }
            }
            _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
        }
        Ok(())
    }

    /// The names in `(old new)`.
    fn pair_of_names(&self, node: Syntax<'gc>) -> Result<(String, String), LowerError> {
        match self.list(node)?.as_slice() {
            &[old, new] => Ok((self.identifier(old)?, self.identifier(new)?)),
            _ => Err(self.error(LowerErrorKind::BadShape, node)),
        }
    }

    /// The name of the identifier `node`.
    fn identifier(&self, node: Syntax<'gc>) -> Result<String, LowerError> {
        self.name(node)?;
        self.text(node).ok_or_else(|| self.error(LowerErrorKind::BadShape, node))
    }

    /// The text of `node`, if it's an identifier or a string.
    fn text(&self, node: Syntax<'gc>) -> Option<String> {
        let datum = node.datum(self.mc);
        let string = match node.kind(self.mc)? {
            SyntaxKind::Identifier => Symbol::of(datum)?.name(self.mc),
            SyntaxKind::Literal => self.strings.string(datum)?,
            _ => return None,
        };
        Some(chars(&self.strings, string).collect())
    }

    /// Returns the source position of the form `node`. Error reports use it for a call or operation lowered from the form.
    fn position(&self, node: Syntax<'gc>) -> Option<Position<'gc>> {
        Position::of(self.mc, node.span(self.mc))
    }

    fn expr(&mut self, locals: &mut Locals<'gc>, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        steps::run(&mut Lowering { l: self, locals }, node, Lowering::expr)
    }

    /// The quoted datum `root` reads as, without its syntax.
    fn datum(&mut self, root: Syntax<'gc>) -> Result<Value<'gc>, LowerError> {
        enum Task<'gc> {
            Node(Syntax<'gc>),
            /// A part of a list or vector, which is syntax.
            Item(Value<'gc>, Syntax<'gc>),
            Abbreviation(Value<'gc>, Syntax<'gc>),
            Vector(usize, Syntax<'gc>),
            /// A list of so many items, and a tail if it's dotted.
            List(usize, bool, Syntax<'gc>),
        }
        let oom = |this: &Self, error: OutOfMemory, node| this.error(error, node);
        let mut todo = vec![Task::Node(root)];
        let mut done = Vec::new();
        while let Some(task) = todo.pop() {
            let node = match task {
                Task::Node(node) => node,
                Task::Item(value, parent) => self.syntax(value, parent)?,
                Task::Abbreviation(name, node) => {
                    let inner = done.pop().expect("an abbreviation's datum");
                    done.push(self.pairs.list(&[name, inner]).map_err(|error| oom(self, error, node))?);
                    continue;
                }
                Task::Vector(count, node) => {
                    let items = done.split_off(done.len() - count);
                    done.push(Vectors::new(self.mc).immutable_from_slice(&items).map_err(|error| oom(self, error, node))?.value(self.mc));
                    continue;
                }
                Task::List(count, dotted, node) => {
                    let rest = if dotted { done.pop().expect("a list's tail") } else { Value::NIL };
                    let items = done.split_off(done.len() - count);
                    done.push(self.pairs.list_with_tail(items, rest).map_err(|error| oom(self, error, node))?);
                    continue;
                }
            };
            match node.kind(self.mc) {
                Some(SyntaxKind::Identifier | SyntaxKind::Literal) => done.push(node.datum(self.mc)),
                Some(SyntaxKind::Abbreviation(abbreviation)) => {
                    let name = self.abbreviations[abbreviation as usize];
                    let inner = self.inner(node)?;
                    todo.extend([Task::Abbreviation(name, node), Task::Node(inner)]);
                }
                Some(SyntaxKind::Vector) => {
                    let vector = Vectors::new(self.mc).vector(node.datum(self.mc)).ok_or_else(|| self.error(LowerErrorKind::Unsupported, node))?;
                    let items: Vec<_> = (0..vector.len(self.mc)).filter_map(|i| vector.get(self.mc, i)).collect();
                    todo.push(Task::Vector(items.len(), node));
                    todo.extend(items.into_iter().rev().map(|value| Task::Item(value, node)));
                }
                Some(SyntaxKind::List) => {
                    let mut elements = self.pairs.elements(node.datum(self.mc));
                    let items: Vec<_> = elements.by_ref().collect();
                    let rest = elements.rest();
                    let dotted = rest != Value::NIL;
                    todo.push(Task::List(items.len(), dotted, node));
                    if dotted {
                        todo.push(Task::Item(rest, node));
                    }
                    todo.extend(items.into_iter().rev().map(|value| Task::Item(value, node)));
                }
                _ => return Err(self.error(LowerErrorKind::Unsupported, node)),
            }
        }
        Ok(done.pop().expect("a datum"))
    }

    /// Returns the innermost local variable named `name` that is in scope, if there is one. Any other name is left to the compiler, which resolves it to a module variable or an import.
    fn local(&self, name: Syntax<'gc>) -> Option<Var> {
        self.scope.get(&name.datum(self.mc).to_bits()).and_then(|vars| vars.last()).copied()
    }

    fn reference(&self, name: Syntax<'gc>) -> Core<'gc> {
        match self.local(name) {
            Some(var) => Core::Ref(Place::Local(var)),
            None => Core::Global(name.datum(self.mc), name.span(self.mc)),
        }
    }

    fn unbind(&mut self, names: &[Syntax<'gc>]) {
        for name in names {
            self.scope.get_mut(&name.datum(self.mc).to_bits()).and_then(Vec::pop);
        }
    }

    /// Fails on the second of any two `names` that are the same.
    fn distinct(&self, names: &[Syntax<'gc>]) -> Result<(), LowerError> {
        let mut seen = HashSet::new();
        match names.iter().find(|name| !seen.insert(name.datum(self.mc).to_bits())) {
            Some(&name) => Err(self.error(LowerErrorKind::Duplicate, name)),
            None => Ok(()),
        }
    }

    /// `node`, if it's an identifier.
    fn name(&self, node: Syntax<'gc>) -> Result<Syntax<'gc>, LowerError> {
        match node.kind(self.mc) {
            Some(SyntaxKind::Identifier) => Ok(node),
            _ => Err(self.error(LowerErrorKind::BadShape, node)),
        }
    }

    /// The items of `node`, a proper list.
    fn list(&self, node: Syntax<'gc>) -> Result<Vec<Syntax<'gc>>, LowerError> {
        if node.kind(self.mc) != Some(SyntaxKind::List) {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        let mut elements = self.pairs.elements(node.datum(self.mc));
        let items = elements.by_ref().map(|value| self.syntax(value, node)).collect::<Result<_, _>>()?;
        if elements.rest() != Value::NIL {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        Ok(items)
    }

    /// The datum `node` quotes.
    fn inner(&self, node: Syntax<'gc>) -> Result<Syntax<'gc>, LowerError> {
        self.syntax(node.datum(self.mc), node)
    }

    /// `value`, a part of `node`, as syntax, which the reader makes every part of a list.
    fn syntax(&self, value: Value<'gc>, node: Syntax<'gc>) -> Result<Syntax<'gc>, LowerError> {
        Syntax::of(value).ok_or_else(|| self.error(LowerErrorKind::Unsupported, node))
    }

    fn error(&self, kind: impl Into<LowerErrorKind>, node: Syntax<'gc>) -> LowerError {
        let span = node.span(self.mc);
        LowerError { kind: kind.into(), start: span.start(), end: span.end() }
    }
}

/// A form being lowered by the lowerer: what [`steps`] works on, so lowering it takes no more of
/// the machine's stack however deeply it nests.
struct Lowering<'s, 'a, 'gc> {
    l: &'s mut Lowerer<'a, 'gc>,
    /// The module's allocator of local variables and lambda IDs.
    locals: &'s mut Locals<'gc>,
}

/// What lowering an expression does next. Each call lowers an expression.
type Lo<'s, 'a, 'gc> = Step<'s, Lowering<'s, 'a, 'gc>, Syntax<'gc>, Core<'gc>, LowerError>;

/// The state of lowering a `%lambda` that has optional or keyword parameters. `params` holds the parameters bound so far, and `next` is the index of the next parameter to bind.
struct Optional<'gc> {
    node: Syntax<'gc>,
    formals: Formals<'gc>,
    body: Vec<Syntax<'gc>>,
    params: Vec<Formal<'gc>>,
    next: usize,
}

/// A `%let*` being lowered: the bindings left, and the names bound so far, each with its `%let`.
struct Sequential<'gc> {
    binds: Syntax<'gc>,
    left: std::vec::IntoIter<Syntax<'gc>>,
    names: Vec<Syntax<'gc>>,
    lets: Vec<(Var, Core<'gc>)>,
    body: Vec<Syntax<'gc>>,
}

impl<'s, 'a, 'gc> Lowering<'s, 'a, 'gc> {
    /// Allocates a local variable for each of `names` and brings the names into scope.
    fn bind(&mut self, names: &[Syntax<'gc>]) -> Vec<Var> {
        let mut vars = Vec::with_capacity(names.len());
        for name in names {
            let symbol = name.datum(self.l.mc);
            let var = self.locals.named(symbol);
            self.l.scope.entry(symbol.to_bits()).or_default().push(var);
            vars.push(var);
        }
        vars
    }

    fn expr(&mut self, node: Syntax<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        Ok(Step::Done(match node.kind(lowerer.mc) {
            Some(SyntaxKind::Identifier) => lowerer.reference(node),
            Some(SyntaxKind::Literal | SyntaxKind::Vector) => Core::Quote(lowerer.datum(node)?),
            Some(SyntaxKind::Abbreviation(Abbreviation::Quote)) => Core::Quote(lowerer.datum(lowerer.inner(node)?)?),
            Some(SyntaxKind::List) => return self.form(node),
            _ => return Err(lowerer.error(LowerErrorKind::Unsupported, node)),
        }))
    }

    fn form(&mut self, node: Syntax<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        let items = lowerer.list(node)?;
        let form = items.first().filter(|head| head.kind(lowerer.mc) == Some(SyntaxKind::Identifier)).and_then(|head| lowerer.forms.get(&head.datum(lowerer.mc).to_bits()));
        let Some(&form) = form else { return Err(lowerer.error(LowerErrorKind::NotAForm, node)) };
        match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Ok(Step::Done(Core::Quote(lowerer.datum(datum)?))),
            (Form::If, &[test, then, other]) => steps::all(vec![test, then, other], |_, parts| {
                let [test, then, other] = <[Core<'gc>; 3]>::try_from(parts).map_err(|_| ()).expect("three parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(other))))
            }),
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(matches!(form, Form::Letrec), node, binds, body.to_vec()),
            (Form::LetStar, &[binds, ref body @ ..]) => self.sequential(node, binds, body.to_vec()),
            (Form::Set, &[name, value]) => {
                lowerer.name(name)?;
                let local = lowerer.local(name);
                Ok(Step::then(value, move |this: &mut Self, value| {
                    Ok(Step::Done(match local {
                        Some(var) => Core::Set(Place::Local(var), Box::new(value)),
                        None => Core::SetGlobal(name.datum(this.l.mc), Box::new(value), name.span(this.l.mc)),
                    }))
                }))
            }
            (Form::Define | Form::Struct | Form::Require | Form::Provide, _) => Err(lowerer.error(LowerErrorKind::Definition, node)),
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(node, formals, body.to_vec()),
            (Form::App, &[callee, ref args @ ..]) if args.iter().any(|&arg| lowerer.keyword(arg).is_some()) => self.keyword_call(node, callee, args.to_vec()),
            (Form::App, &[callee, ref args @ ..]) => {
                let args = args.to_vec();
                Ok(Step::then(callee, move |_: &mut Self, callee| steps::all(args, move |this: &mut Self, args| Ok(Step::Done(Core::App(Box::new(callee), args, this.l.position(node)))))))
            }
            (Form::Intrinsic, &[name, ref args @ ..]) => self.intrinsic(node, name, args.to_vec(), false),
            (Form::ApplyIntrinsic, &[name, ref args @ ..]) if !args.is_empty() => self.intrinsic(node, name, args.to_vec(), true),
            (Form::CallHost, &[name, ref args @ ..]) => self.call_host(node, name, args.to_vec()),
            _ => Err(lowerer.error(LowerErrorKind::BadShape, node)),
        }
    }

    /// A `%let`, or if `recursive`, a `%letrec`.
    fn binding(&mut self, recursive: bool, node: Syntax<'gc>, binds: Syntax<'gc>, body: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        if body.is_empty() {
            return Err(lowerer.error(LowerErrorKind::BadShape, node));
        }
        let (mut names, mut inits) = (Vec::new(), Vec::new());
        for bind in lowerer.list(binds)? {
            let bind = lowerer.list(bind)?;
            let &[name, init] = bind.as_slice() else { return Err(lowerer.error(LowerErrorKind::BadShape, binds)) };
            names.push(lowerer.name(name)?);
            inits.push(init);
        }
        lowerer.distinct(&names)?;
        // A `%letrec`'s names are in scope in its inits, a `%let`'s only in its body.
        let vars = if recursive { self.bind(&names) } else { Vec::new() };
        steps::all(inits, move |this: &mut Self, inits: Vec<Core<'gc>>| {
            let vars = if recursive { vars } else { this.bind(&names) };
            this.body(body, move |this, body| {
                this.l.unbind(&names);
                let binds = vars.into_iter().zip(inits).collect();
                Ok(Step::Done(if recursive { Core::Letrec(binds, Box::new(body)) } else { Core::Let(binds, Box::new(body)) }))
            })
        })
    }

    /// A `%let*`: nested `%let`s of one binding each, so each init sees the names before it.
    fn sequential(&mut self, node: Syntax<'gc>, binds: Syntax<'gc>, body: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        if body.is_empty() {
            return Err(self.l.error(LowerErrorKind::BadShape, node));
        }
        let left = self.l.list(binds)?.into_iter();
        self.sequential_from(Sequential { binds, left, names: Vec::new(), lets: Vec::new(), body })
    }

    fn sequential_from(&mut self, mut sequential: Sequential<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let Some(bind) = sequential.left.next() else {
            let Sequential { names, mut lets, body, .. } = sequential;
            return self.body(body, move |this, mut core| {
                this.l.unbind(&names);
                while let Some(bind) = lets.pop() {
                    core = Core::Let(vec![bind], Box::new(core));
                }
                Ok(Step::Done(core))
            });
        };
        let bind = self.l.list(bind)?;
        let &[name, init] = bind.as_slice() else { return Err(self.l.error(LowerErrorKind::BadShape, sequential.binds)) };
        let name = self.l.name(name)?;
        Ok(Step::then(init, move |this: &mut Self, init| {
            sequential.lets.extend(this.bind(&[name]).into_iter().zip([init]));
            sequential.names.push(name);
            this.sequential_from(sequential)
        }))
    }

    /// A `%lambda`.
    fn lambda(&mut self, node: Syntax<'gc>, formals: Syntax<'gc>, body: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        if body.is_empty() {
            return Err(lowerer.error(LowerErrorKind::BadShape, node));
        }
        let formals = lowerer.formals(formals)?;
        let mut names = formals.names.clone();
        names.extend(formals.rest);
        lowerer.distinct(&names)?;
        if !formals.is_plain() {
            let params = Vec::with_capacity(formals.names.len());
            return self.defaults(Optional { node, formals, body, params, next: 0 });
        }
        let params = formals.names.len();
        let mut vars = self.bind(&names);
        self.body(body, move |this, body| {
            this.l.unbind(&names);
            let rest = (vars.len() > params).then(|| vars.pop()).flatten();
            let id = this.locals.lambda();
            Ok(Step::Done(Core::Lambda(Lambda { id, params: vars, optional: 0, rest, body: Box::new(body), name: None, at: Position::of(this.l.mc, node.span(this.l.mc)) })))
        })
    }

    /// Binds the remaining parameters of an optional lambda, then lowers the body. A default is lowered before its parameter is bound, so it can refer only to earlier parameters.
    fn defaults(&mut self, mut optional: Optional<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        while let Some(&name) = optional.formals.names.get(optional.next) {
            let (keyword, default) = (optional.formals.params[optional.next].keyword, optional.formals.defaults[optional.next]);
            optional.next += 1;
            let Some(default) = default else {
                let var = self.bind(&[name])[0];
                optional.params.push(Formal { var, keyword, default: None });
                continue;
            };
            return Ok(Step::then(default, move |this: &mut Self, default| {
                let var = this.bind(&[name])[0];
                optional.params.push(Formal { var, keyword, default: Some(default) });
                this.defaults(optional)
            }));
        }
        let rest = optional.formals.rest.map(|name| self.bind(&[name])[0]);
        let Optional { node, formals, body, params, .. } = optional;
        self.body(body, move |this, body| {
            this.l.unbind(&formals.names);
            this.l.unbind(&formals.rest.into_iter().collect::<Vec<_>>());
            let mc = this.l.mc;
            let lambda = OptionalLambda { id: this.locals.lambda(), params, rest, body: Box::new(body), name: None, at: Position::of(mc, node.span(mc)) };
            Ok(Step::Done(Core::OptionalLambda(lambda)))
        })
    }

    /// Lowers an `%app` of `callee` that has keyword arguments in `args` into a [`Core::KeywordApp`].
    fn keyword_call(&mut self, node: Syntax<'gc>, callee: Syntax<'gc>, args: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        let (mut kinds, mut nodes) = (Vec::new(), Vec::new());
        let mut items = args.into_iter();
        while let Some(arg) = items.next() {
            let Some(keyword) = lowerer.keyword(arg) else {
                kinds.push(None);
                nodes.push(arg);
                continue;
            };
            let value = items.next().ok_or_else(|| lowerer.error(LowerErrorKind::BadShape, arg))?;
            if kinds.contains(&Some(keyword)) {
                return Err(lowerer.error(LowerErrorKind::Duplicate, arg));
            }
            kinds.push(Some(keyword));
            nodes.push(value);
        }
        Ok(Step::then(callee, move |_: &mut Self, callee| {
            steps::all(nodes, move |this: &mut Self, values| {
                let args = kinds.into_iter().zip(values).map(|(keyword, value)| Arg { keyword, value }).collect();
                Ok(Step::Done(Core::KeywordApp(Box::new(callee), args, this.l.position(node))))
            })
        }))
    }

    /// An `%intrinsic`, or if `spread`, an `%apply-intrinsic`, whose argument count is only known
    /// as it runs.
    fn intrinsic(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: Vec<Syntax<'gc>>, spread: bool) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        lowerer.name(name)?;
        let &prim = lowerer.prims.get(&name.datum(lowerer.mc).to_bits()).ok_or_else(|| lowerer.error(LowerErrorKind::UnknownIntrinsic, name))?;
        if spread {
            return steps::all(args, move |this: &mut Self, args| Ok(Step::Done(Core::ApplyIntrinsic(prim, args, this.l.position(node)))));
        }
        let takes = match prim {
            Prim::Intrinsic(intrinsic) => intrinsic.arity().is_none_or(|arity| usize::from(arity) == args.len()),
            Prim::Request(request) => request.takes(args.len()),
            Prim::Host(host) => host.takes(args.len()),
            Prim::Slot(op, _) => op.arity() == args.len(),
        };
        if !takes {
            return Err(lowerer.error(LowerErrorKind::Arity, node));
        }
        steps::all(args, move |this: &mut Self, args| Ok(Step::Done(Core::Intrinsic(prim, args, this.l.position(node)))))
    }

    /// A `%call-host` of the host function named `name`.
    fn call_host(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let lowerer = &mut *self.l;
        lowerer.name(name)?;
        let &def = lowerer.hosts.get(&name.datum(lowerer.mc).to_bits()).ok_or_else(|| lowerer.error(LowerErrorKind::UnknownHost, name))?;
        if !def.takes(args.len()) {
            return Err(lowerer.error(LowerErrorKind::Arity, node));
        }
        steps::all(args, move |this: &mut Self, args| Ok(Step::Done(Core::Intrinsic(Prim::Host(def), args, this.l.position(node)))))
    }

    /// A body's expressions, in order, as one, to `then`.
    fn body(&mut self, nodes: Vec<Syntax<'gc>>, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> + 's) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        steps::all(nodes, move |this: &mut Self, mut cores| {
            let body = cores.pop().expect("bodies aren't empty");
            if cores.is_empty() {
                return then(this, body);
            }
            // One `let` of what the forms before the last return, however many there are.
            let binds = cores.into_iter().map(|core| (this.locals.fresh(), core)).collect();
            then(this, Core::Let(binds, Box::new(body)))
        })
    }
}
