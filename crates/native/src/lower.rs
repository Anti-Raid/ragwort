//! Lowering: native ragwort's syntax to core forms.

use std::collections::{HashMap, HashSet};
use std::fmt;

use ragwort_compiler::keyword::{self, CallShape, Fresh};
use ragwort_compiler::module::{Binding, Field, Filter, Import, ModuleBuilder, ModuleError, RequireSpec, Resolver, SpecError, Unusable};
use ragwort_compiler::steps::{self, Step};
use ragwort_compiler::structs::{self, Declaration, Declared, Member};
use ragwort_compiler::{Core, Lambda, Place, Position, Prim, Var};
use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Keyword, Symbol, Symbols};
use ragwort_types::vector::Vectors;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind};
use ragwort_vm::structs::TypeFlags;
use ragwort_vm::{Fault, HostDef, Intrinsic, Request};

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
    /// A `%set!` of an import.
    Immutable,
    /// A `%define`, `%struct`, `%require` or `%provide` that isn't at the top level.
    Definition,
    /// A module the resolver doesn't have, or one it gave that no [`ModuleBuilder`] built.
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
    fn from(e: OutOfMemory) -> Self {
        Self::Arena(e.into())
    }
}

impl From<Error> for LowerErrorKind {
    fn from(e: Error) -> Self {
        Self::Arena(e)
    }
}

/// What went wrong, and the bytes `start..end` of the text where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LowerError {
    pub kind: LowerErrorKind,
    pub start: u32,
    pub end: u32,
}

impl fmt::Display for LowerErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            LowerErrorKind::NotAForm => "a list that doesn't start with a form's name",
            LowerErrorKind::BadShape => "a form with the wrong parts",
            LowerErrorKind::Duplicate => "a name bound twice",
            LowerErrorKind::Unbound => "a name nothing defines",
            LowerErrorKind::Conflict => "a name both defined and required",
            LowerErrorKind::Immutable => "an assignment of an import",
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at bytes {}..{}", self.kind, self.start, self.end)
    }
}

impl std::error::Error for LowerError {}

impl From<Error> for LowerError {
    fn from(e: Error) -> Self {
        Self { kind: e.into(), start: 0, end: 0 }
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

/// Lowers the forms of a module's native files, into the module's builder, numbering their
/// variables and lambdas apart: first [`Lowerer::declare`] each, then [`Lowerer::provide`] and
/// start the module, then [`Lowerer::lower`] each, in order.
pub struct Lowerer<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    pairs: Pairs<'a, 'gc>,
    strings: Strings<'a, 'gc>,
    symbols: Symbols<'gc>,
    /// The `%provide`s, which name what the module defines anywhere.
    provides: Vec<Syntax<'gc>>,
    /// The struct forms declared, by which top-level form each is, till they're lowered.
    structs: HashMap<u32, Declared>,
    /// The top-level form being lowered, and the variable whose lambda it's in, if it's one.
    top: u32,
    defining: Option<u32>,
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
    vars: u32,
    lambdas: u32,
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
        self.params.iter().all(|p| p.keyword.is_none() && !p.optional)
    }

    fn has_keywords(&self) -> bool {
        self.params.iter().any(|p| p.keyword.is_some())
    }
}

/// Where the core of a keyword procedure a call knows of is.
#[derive(Clone, Copy)]
enum CoreAt<'gc> {
    Slot(u32),
    Import(Import<'gc>),
}

impl<'a, 'gc> Lowerer<'a, 'gc> {
    /// A lowerer of code that calls the host functions `hosts`. The code's `%intrinsic`s name
    /// [internal intrinsics](Intrinsic::is_internal) only if `internals`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, hosts: &'static [HostDef], internals: bool) -> Result<Self, Error> {
        let strings = Strings::new(mc);
        let symbol = |name: &str| symbols.intern_str(&strings, name).map(|s| s.value(mc));
        let mut forms = HashMap::new();
        for (name, form) in FORMS {
            forms.insert(symbol(name)?.to_bits(), form);
        }
        let mut prims = HashMap::new();
        for &i in Intrinsic::ALL {
            if internals || !i.is_internal() {
                prims.insert(symbol(i.name())?.to_bits(), Prim::Intrinsic(i));
            }
        }
        for &r in Request::ALL {
            prims.insert(symbol(r.name())?.to_bits(), Prim::Request(r));
        }
        let mut named_hosts = HashMap::new();
        for def in hosts {
            named_hosts.insert(symbol(def.name)?.to_bits(), def);
        }
        let mut abbreviations = Vec::with_capacity(Abbreviation::ALL.len());
        for a in Abbreviation::ALL {
            abbreviations.push(symbol(a.name())?);
        }
        Ok(Self {
            mc,
            pairs: Pairs::new(mc),
            strings,
            symbols,
            provides: Vec::new(),
            structs: HashMap::new(),
            top: 0,
            defining: None,
            forms,
            prims,
            hosts: named_hosts,
            abbreviations,
            scope: HashMap::new(),
            vars: 0,
            lambdas: 0,
        })
    }

    /// Declares what top-level form `top`, `node`, defines, requires from `resolver` or provides.
    pub fn declare(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, top: u32, resolver: &mut dyn Resolver<'gc>) -> Result<(), LowerError> {
        let items = match self.head(node) {
            Some(Form::Define | Form::Struct | Form::Require | Form::Provide) => self.list(node)?,
            _ => return Ok(()),
        };
        match (self.head(node), &items[1..]) {
            (Some(Form::Struct), parts) => {
                let declared = self.declare_struct(builder, node, parts, top)?;
                self.structs.insert(top, declared);
            }
            (Some(Form::Define), &[name, value]) => {
                self.name(name)?;
                let slot = builder.define(name.datum(self.mc), top).map_err(|e| self.module_error(e, name))?;
                if let Some(formals) = self.keyword_formals(value)? {
                    let shape = CallShape::of(self.mc, &formals.params, formals.rest.is_some());
                    let core = builder.define_private(name.datum(self.mc), top).map_err(|e| self.module_error(e, name))?;
                    builder.keyword_core(slot, core, shape);
                }
            }
            (Some(Form::Require), specs) => {
                for &spec in specs {
                    let imports = self.spec(spec)?.imports(self.mc, resolver, builder.name()).map_err(|e| match e {
                        SpecError::Resolve(at) => self.error(LowerErrorKind::Resolve, at),
                        SpecError::NotProvided(at) => self.error(LowerErrorKind::NotProvided, at),
                    })?;
                    builder.require(self.mc, self.symbols, imports).map_err(|e| self.module_error(e, spec))?;
                }
            }
            (Some(Form::Provide), _) => self.provides.push(node),
            _ => return Err(self.error(LowerErrorKind::BadShape, node)),
        }
        Ok(())
    }

    /// Exports what the module provides, once every form is declared.
    pub fn provide(&mut self, builder: &mut ModuleBuilder<'gc>) -> Result<(), LowerError> {
        for node in std::mem::take(&mut self.provides) {
            for spec in self.list(node)?.into_iter().skip(1) {
                self.provide_spec(builder, spec)?;
            }
        }
        Ok(())
    }

    /// Lowers top-level form `top`, `node`, if it has code to run, once the module's started.
    pub fn lower(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, top: u32) -> Result<Option<Core<'gc>>, LowerError> {
        self.scope.clear();
        self.top = top;
        match self.head(node) {
            Some(Form::Require | Form::Provide) => Ok(None),
            Some(Form::Struct) => {
                let declared = self.structs.remove(&top).expect("a declared struct");
                let (_, kind) = builder.struct_def(declared.constructor()).expect("a declared struct");
                Ok(Some(declared.define(kind, self)))
            }
            Some(Form::Define) => {
                let items = self.list(node)?;
                let &[_, name, value] = items.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, node)) };
                let Some(Binding::Slot(slot)) = builder.binding(name.datum(self.mc)) else { unreachable!("declared") };
                if let Some((core, shape)) = builder.keyword_def(slot).map(|(core, shape)| (core, shape.clone())) {
                    return self.keyword_definition(builder, slot, core, &shape, value).map(Some);
                }
                self.defining = (self.head(value) == Some(Form::Lambda)).then_some(slot);
                let value = self.expr(builder, value);
                self.defining = None;
                let value = value?;
                builder.defined(slot, &value);
                Ok(Some(Core::Set(Place::Slot { slot, checked: false }, Box::new(value))))
            }
            _ => self.expr(builder, node).map(Some),
        }
    }

    /// Declares what a `%struct` form defines: `node`, whose parts after its head are `parts`,
    /// the module's top-level form `top`. It's written as Scheme's `struct` is, and defines what
    /// that does, as [`structs`] says: `(%struct name (field ...) option ...)`, with a
    /// supertype's name before the fields for a subtype of it.
    fn declare_struct(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, parts: &[Syntax<'gc>], top: u32) -> Result<Declared, LowerError> {
        let bad = LowerErrorKind::BadShape;
        let is_name = |node: &Syntax<'gc>| node.kind(self.mc) == Some(SyntaxKind::Identifier);
        let option = |node: Syntax<'gc>| self.keyword(node).map(|k| chars(&self.strings, k.symbol(self.mc).name(self.mc)).collect::<String>());
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
        // The supertype is a struct type the module defines or requires, by its constructor,
        // that isn't sealed.
        let (above, mut fields) = match parent {
            None => (Value::FALSE, Vec::new()),
            Some(id) => {
                let def = match builder.binding(id.datum(self.mc)) {
                    Some(Binding::Slot(slot)) => builder.struct_def(slot).map(|(def, kind)| (def.clone(), kind)),
                    Some(Binding::Import(import)) => import.struct_def(self.mc).map(|(def, kind)| (def.clone(), kind)),
                    None => None,
                };
                match def {
                    Some((def, kind)) if !def.sealed => (kind, def.fields.into_vec()),
                    _ => return Err(self.error(bad, id)),
                }
            }
        };
        let inherited = fields.len();
        for &(id, mutable) in &own {
            fields.push(Field { name: self.identifier(id)?.into(), mutable });
        }
        let named = structs::members(&self.identifier(name)?, &fields[inherited..], inherited).ok_or_else(|| self.error(OutOfMemory, node))?;
        let declared: Vec<Declaration<'gc>> = own.iter().map(|&(id, mutable)| Declaration { name: id.datum(self.mc), mutable }).collect();
        let kind = structs::make_type(self.mc, name.datum(self.mc), above, &declared, flags).map_err(|fault| match fault {
            Fault::OutOfMemory => self.error(OutOfMemory, node),
            _ => self.error(bad, node),
        })?;
        let mut members = Vec::with_capacity(named.len() + constructors.len());
        for (text, member) in named {
            let symbol = self.symbols.intern_str(&self.strings, &text).map_err(|e| self.error(e, node))?;
            members.push((builder.define(symbol.value(self.mc), top).map_err(|e| self.module_error(e, name))?, member));
            // The constructors of other names go after the one that has the struct's name.
            if member == Member::Make {
                for &id in &constructors {
                    members.push((builder.define(id.datum(self.mc), top).map_err(|e| self.module_error(e, id))?, Member::Make));
                }
            }
        }
        Ok(Declared::new(builder, kind, fields, flags.contains(TypeFlags::SEALED), members))
    }

    /// A call of the procedure of a struct type that `f` names, if it names one of the module's
    /// that takes `n` arguments: one that does what the procedure does.
    fn struct_call(&self, builder: &ModuleBuilder<'gc>, f: Syntax<'gc>, n: usize) -> Option<structs::Call<'gc>> {
        if f.kind(self.mc) != Some(SyntaxKind::Identifier) {
            return None;
        }
        let Ok(Err(Binding::Slot(slot))) = self.resolve(builder, f) else { return None };
        builder.struct_call(slot, self.top).filter(|call| call.takes(n))
    }

    /// Sets the keyword procedure `procedure`, which `value` makes, and its core, `core`.
    fn keyword_definition(&mut self, builder: &mut ModuleBuilder<'gc>, procedure: u32, core: u32, shape: &CallShape<'gc>, value: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        self.defining = Some(core);
        let mut root = true;
        let lambda = steps::run(&mut Lowering { l: self, builder }, value, |s, node| {
            if !std::mem::take(&mut root) {
                return s.expr(node);
            }
            let items = s.l.list(node)?;
            s.lambda(node, items[1], items[2..].to_vec(), true)
        });
        self.defining = None;
        let lambda = lambda?;
        builder.defined(core, &lambda);
        let place = builder.place(core, self.top, None);
        let value = keyword::procedure(self.mc, shape, Core::Ref(place), self).map_err(|e| self.error(e, value))?;
        let core = Core::Set(Place::Slot { slot: core, checked: false }, Box::new(lambda));
        let procedure = Core::Set(Place::Slot { slot: procedure, checked: false }, Box::new(value));
        Ok(Core::Let(vec![(self.fresh(), core)], Box::new(procedure)))
    }

    /// The formals of `value`, if it's a `%lambda` with keyword parameters.
    fn keyword_formals(&self, value: Syntax<'gc>) -> Result<Option<Formals<'gc>>, LowerError> {
        if self.head(value) != Some(Form::Lambda) {
            return Ok(None);
        }
        let items = self.list(value)?;
        let Some(&formals) = items.get(1) else { return Ok(None) };
        let formals = self.formals(formals)?;
        Ok(formals.has_keywords().then_some(formals))
    }

    /// The parameters `formals` has: names, `[name default]`s and keywords before either, and a
    /// rest parameter, as Racket's `lambda` takes them.
    fn formals(&self, formals: Syntax<'gc>) -> Result<Formals<'gc>, LowerError> {
        let mut f = Formals { params: Vec::new(), names: Vec::new(), defaults: Vec::new(), rest: None };
        let items = match formals.kind(self.mc) {
            Some(SyntaxKind::Identifier) => {
                f.rest = Some(formals);
                return Ok(f);
            }
            Some(SyntaxKind::List) => {
                let mut elements = self.pairs.elements(formals.datum(self.mc));
                let items = elements.by_ref().map(|v| self.syntax(v, formals)).collect::<Result<Vec<_>, _>>()?;
                let rest = elements.rest();
                f.rest = if rest == Value::NIL { None } else { Some(self.name(self.syntax(rest, formals)?)?) };
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
            if keyword.is_some() && f.params.iter().any(|p| p.keyword == keyword) {
                return Err(self.error(LowerErrorKind::Duplicate, item));
            }
            // As in Racket, a required positional parameter can't follow an optional one.
            if keyword.is_none() && default.is_none() && f.params.iter().any(|p| p.keyword.is_none() && p.optional) {
                return Err(self.error(LowerErrorKind::BadShape, at));
            }
            f.params.push(keyword::Param { keyword, optional: default.is_some() });
            f.names.push(name);
            f.defaults.push(default);
        }
        Ok(f)
    }

    /// The keyword `node` is, if it's one.
    fn keyword(&self, node: Syntax<'gc>) -> Option<Keyword<'gc>> {
        if node.kind(self.mc) != Some(SyntaxKind::Literal) {
            return None;
        }
        Keyword::of(node.datum(self.mc))
    }

    /// The core of the keyword procedure `f` names, and its shape, if it's one whose core is known:
    /// one the module defines, or imports from a module that exports its core.
    fn keyword_def(&self, builder: &ModuleBuilder<'gc>, f: Syntax<'gc>) -> Option<(CoreAt<'gc>, CallShape<'gc>)> {
        if f.kind(self.mc) != Some(SyntaxKind::Identifier) {
            return None;
        }
        match self.resolve(builder, f) {
            Ok(Err(Binding::Slot(slot))) => builder.keyword_def(slot).map(|(core, shape)| (CoreAt::Slot(core), shape.clone())),
            Ok(Err(Binding::Import(import))) => CallShape::of_import(self.mc, import).map(|(core, shape)| (CoreAt::Import(core), shape)),
            _ => None,
        }
    }

    fn lambda_id(&mut self) -> u32 {
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        id
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
    fn spec(&self, mut spec: Syntax<'gc>) -> Result<RequireSpec<Syntax<'gc>>, LowerError> {
        let mut filters = Vec::new();
        loop {
            if let Some(module) = self.text(spec) {
                filters.reverse();
                return Ok(RequireSpec { module, at: spec, filters });
            }
            let items = self.list(spec)?;
            let Some((&head, args)) = items.split_first() else { return Err(self.error(LowerErrorKind::BadShape, spec)) };
            let word = self.text(head).filter(|_| head.kind(self.mc) == Some(SyntaxKind::Identifier));
            let named = |n: &Syntax<'gc>| -> Result<(String, Syntax<'gc>), LowerError> { Ok((self.identifier(*n)?, *n)) };
            let (filter, inner) = match (word.as_deref(), args) {
                (Some("only-in"), &[inner, ref names @ ..]) => (Filter::Only(names.iter().map(named).collect::<Result<_, _>>()?), inner),
                (Some("except-in"), &[inner, ref names @ ..]) => (Filter::Except(names.iter().map(named).collect::<Result<_, _>>()?), inner),
                (Some("prefix-in"), &[prefix, inner]) => (Filter::Prefix(self.identifier(prefix)?), inner),
                (Some("rename-in"), &[inner, ref renames @ ..]) => {
                    let renames = renames.iter().map(|&r| self.pair_of_names(r).map(|(old, new)| (old, new, r))).collect::<Result<_, _>>()?;
                    (Filter::Rename(renames), inner)
                }
                _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
            };
            filters.push(filter);
            spec = inner;
        }
    }

    /// Exports what the provide spec `spec` names.
    fn provide_spec(&mut self, builder: &mut ModuleBuilder<'gc>, spec: Syntax<'gc>) -> Result<(), LowerError> {
        if spec.kind(self.mc) == Some(SyntaxKind::Identifier) {
            let name = self.identifier(spec)?;
            return builder.provide(&name, spec.datum(self.mc)).map_err(|e| self.module_error(e, spec));
        }
        let items = self.list(spec)?;
        let Some((&head, args)) = items.split_first() else { return Err(self.error(LowerErrorKind::BadShape, spec)) };
        let word = if head.kind(self.mc) == Some(SyntaxKind::Identifier) { self.text(head) } else { None };
        match (word.as_deref(), args) {
            (Some("all-defined-out"), []) => builder.provide_all(self.mc).map_err(|e| self.module_error(e, spec)),
            (Some("struct-out"), &[name, ref options @ ..]) => {
                self.name(name)?;
                let constructors = match options {
                    [] => true,
                    &[option] if self.keyword(option).is_some_and(|k| chars(&self.strings, k.symbol(self.mc).name(self.mc)).eq("omit-constructor".chars())) => false,
                    _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
                };
                let Some(Binding::Slot(constructor)) = builder.binding(name.datum(self.mc)) else { return Err(self.error(LowerErrorKind::NotDefined, name)) };
                builder.provide_struct(self.mc, constructor, constructors).map_err(|e| self.module_error(e, name))
            }
            (Some("rename-out"), renames) => {
                for &rename in renames {
                    let (_, external) = self.pair_of_names(rename)?;
                    let inner = self.list(rename)?[0];
                    builder.provide(&external, inner.datum(self.mc)).map_err(|e| self.module_error(e, rename))?;
                }
                Ok(())
            }
            _ => Err(self.error(LowerErrorKind::BadShape, spec)),
        }
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
        let s = match node.kind(self.mc)? {
            SyntaxKind::Identifier => Symbol::of(datum)?.name(self.mc),
            SyntaxKind::Literal => self.strings.string(datum)?,
            _ => return None,
        };
        Some(chars(&self.strings, s).collect())
    }

    /// The error of using the import `node` as a value, which it doesn't have.
    fn import_error(&self, e: Unusable, node: Syntax<'gc>) -> LowerError {
        let kind = match e {
            Unusable::Uninitialized => LowerErrorKind::Uninitialized,
            Unusable::MatchOnly => LowerErrorKind::NoConstructor,
        };
        self.error(kind, node)
    }

    fn module_error(&self, e: ModuleError, node: Syntax<'gc>) -> LowerError {
        let kind = match e {
            ModuleError::Duplicate => LowerErrorKind::Duplicate,
            ModuleError::Conflict => LowerErrorKind::Conflict,
            ModuleError::NotDefined => LowerErrorKind::NotDefined,
            ModuleError::Immutable => LowerErrorKind::Immutable,
            ModuleError::OutOfMemory => OutOfMemory.into(),
        };
        self.error(kind, node)
    }

    fn expr(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        steps::run(&mut Lowering { l: self, builder }, node, Lowering::expr)
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
        let oom = |this: &Self, e: OutOfMemory, node| this.error(e, node);
        let mut todo = vec![Task::Node(root)];
        let mut done = Vec::new();
        while let Some(task) = todo.pop() {
            let node = match task {
                Task::Node(node) => node,
                Task::Item(v, parent) => self.syntax(v, parent)?,
                Task::Abbreviation(name, node) => {
                    let inner = done.pop().expect("an abbreviation's datum");
                    done.push(self.pairs.list(&[name, inner]).map_err(|e| oom(self, e, node))?);
                    continue;
                }
                Task::Vector(n, node) => {
                    let items = done.split_off(done.len() - n);
                    done.push(Vectors::new(self.mc).immutable_from_slice(&items).map_err(|e| oom(self, e, node))?.value(self.mc));
                    continue;
                }
                Task::List(n, dotted, node) => {
                    let rest = if dotted { done.pop().expect("a list's tail") } else { Value::NIL };
                    let items = done.split_off(done.len() - n);
                    done.push(self.pairs.list_with_tail(items, rest).map_err(|e| oom(self, e, node))?);
                    continue;
                }
            };
            match node.kind(self.mc) {
                Some(SyntaxKind::Identifier | SyntaxKind::Literal) => done.push(node.datum(self.mc)),
                Some(SyntaxKind::Abbreviation(a)) => {
                    let name = self.abbreviations[a as usize];
                    let inner = self.inner(node)?;
                    todo.extend([Task::Abbreviation(name, node), Task::Node(inner)]);
                }
                Some(SyntaxKind::Vector) => {
                    let vector = Vectors::new(self.mc).vector(node.datum(self.mc)).ok_or_else(|| self.error(LowerErrorKind::Unsupported, node))?;
                    let items: Vec<_> = (0..vector.len(self.mc)).filter_map(|i| vector.get(self.mc, i)).collect();
                    todo.push(Task::Vector(items.len(), node));
                    todo.extend(items.into_iter().rev().map(|v| Task::Item(v, node)));
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
                    todo.extend(items.into_iter().rev().map(|v| Task::Item(v, node)));
                }
                _ => return Err(self.error(LowerErrorKind::Unsupported, node)),
            }
        }
        Ok(done.pop().expect("a datum"))
    }

    /// What `name`, an identifier, refers to: the innermost local of that name, or else the
    /// module's variable, or else its import.
    fn resolve(&self, builder: &ModuleBuilder<'gc>, name: Syntax<'gc>) -> Result<Result<Var, Binding<'gc>>, LowerError> {
        if let Some(&var) = self.scope.get(&name.datum(self.mc).to_bits()).and_then(|vars| vars.last()) {
            return Ok(Ok(var));
        }
        builder.binding(name.datum(self.mc)).map(Err).ok_or_else(|| self.error(LowerErrorKind::Unbound, name))
    }

    fn reference(&mut self, builder: &mut ModuleBuilder<'gc>, name: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        Ok(match self.resolve(builder, name)? {
            Ok(var) => Core::Ref(Place::Local(var)),
            Err(Binding::Slot(slot)) => match builder.constant(slot, self.top) {
                Some(value) => Core::Quote(value),
                None => Core::Ref(builder.place(slot, self.top, self.defining)),
            },
            Err(Binding::Import(import)) => import.reference(self.mc).map_err(|e| self.import_error(e, name))?,
        })
    }

    /// The place a `%set!` of `name` assigns.
    fn assigned(&mut self, builder: &mut ModuleBuilder<'gc>, name: Syntax<'gc>) -> Result<Place, LowerError> {
        match self.resolve(builder, name)? {
            Ok(var) => Ok(Place::Local(var)),
            Err(Binding::Slot(slot)) => {
                builder.assign(slot).map_err(|e| self.module_error(e, name))?;
                Ok(builder.place(slot, self.top, self.defining))
            }
            Err(Binding::Import(_)) => Err(self.error(LowerErrorKind::Immutable, name)),
        }
    }

    /// The import `f` names, if it's an identifier that names one.
    fn import(&self, builder: &ModuleBuilder<'gc>, f: Syntax<'gc>) -> Option<ragwort_compiler::module::Import<'gc>> {
        if f.kind(self.mc) != Some(SyntaxKind::Identifier) {
            return None;
        }
        match self.resolve(builder, f) {
            Ok(Err(Binding::Import(import))) => Some(import),
            _ => None,
        }
    }

    fn bind(&mut self, names: &[Syntax<'gc>]) -> Vec<Var> {
        names
            .iter()
            .map(|name| {
                let var = self.fresh();
                self.scope.entry(name.datum(self.mc).to_bits()).or_default().push(var);
                var
            })
            .collect()
    }

    fn unbind(&mut self, names: &[Syntax<'gc>]) {
        for name in names {
            self.scope.get_mut(&name.datum(self.mc).to_bits()).and_then(Vec::pop);
        }
    }

    fn fresh(&mut self) -> Var {
        let var = Var(self.vars);
        self.vars = self.vars.checked_add(1).expect("fewer than 2^32 variables");
        var
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
        let items = elements.by_ref().map(|v| self.syntax(v, node)).collect::<Result<_, _>>()?;
        if elements.rest() != Value::NIL {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        Ok(items)
    }

    /// The datum `node` quotes.
    fn inner(&self, node: Syntax<'gc>) -> Result<Syntax<'gc>, LowerError> {
        self.syntax(node.datum(self.mc), node)
    }

    /// `v`, a part of `node`, as syntax, which the reader makes every part of a list.
    fn syntax(&self, v: Value<'gc>, node: Syntax<'gc>) -> Result<Syntax<'gc>, LowerError> {
        Syntax::of(v).ok_or_else(|| self.error(LowerErrorKind::Unsupported, node))
    }

    fn error(&self, kind: impl Into<LowerErrorKind>, node: Syntax<'gc>) -> LowerError {
        let span = node.span(self.mc);
        LowerError { kind: kind.into(), start: span.start(), end: span.end() }
    }
}

/// A form being lowered, by the lowerer, in the module `builder` builds: what [`steps`] works on,
/// so lowering it takes no more of the machine's stack however deeply it nests.
struct Lowering<'s, 'a, 'gc> {
    l: &'s mut Lowerer<'a, 'gc>,
    builder: &'s mut ModuleBuilder<'gc>,
}

impl Fresh for Lowerer<'_, '_> {
    fn var(&mut self) -> Var {
        self.fresh()
    }

    fn lambda(&mut self) -> u32 {
        self.lambda_id()
    }
}

/// What lowering an expression does next. Each call lowers an expression.
type Lo<'s, 'a, 'gc> = Step<'s, Lowering<'s, 'a, 'gc>, Syntax<'gc>, Core<'gc>, LowerError>;

/// A `%lambda` with optional or keyword parameters being lowered: a variable for each parameter,
/// as its formals have them, the order it takes them in, and the defaults so far, each binding
/// the parameter it's for, `next` the parameter after them. If it's `core_only`, it makes just the
/// core of a keyword procedure.
struct Optional<'gc> {
    node: Syntax<'gc>,
    formals: Formals<'gc>,
    body: Vec<Syntax<'gc>>,
    raws: Vec<Var>,
    inits: Vec<(Var, Core<'gc>)>,
    next: usize,
    core_only: bool,
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
    fn expr(&mut self, node: Syntax<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        Ok(Step::Done(match node.kind(l.mc) {
            Some(SyntaxKind::Identifier) => l.reference(self.builder, node)?,
            Some(SyntaxKind::Literal | SyntaxKind::Vector) => Core::Quote(l.datum(node)?),
            Some(SyntaxKind::Abbreviation(Abbreviation::Quote)) => Core::Quote(l.datum(l.inner(node)?)?),
            Some(SyntaxKind::List) => return self.form(node),
            _ => return Err(l.error(LowerErrorKind::Unsupported, node)),
        }))
    }

    fn form(&mut self, node: Syntax<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        let items = l.list(node)?;
        let form = items.first().filter(|head| head.kind(l.mc) == Some(SyntaxKind::Identifier)).and_then(|head| l.forms.get(&head.datum(l.mc).to_bits()));
        let Some(&form) = form else { return Err(l.error(LowerErrorKind::NotAForm, node)) };
        match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Ok(Step::Done(Core::Quote(l.datum(datum)?))),
            (Form::If, &[test, then, other]) => steps::all(vec![test, then, other], |_, parts| {
                let [test, then, other] = <[Core<'gc>; 3]>::try_from(parts).map_err(|_| ()).expect("three parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(other))))
            }),
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(matches!(form, Form::Letrec), node, binds, body.to_vec()),
            (Form::LetStar, &[binds, ref body @ ..]) => self.sequential(node, binds, body.to_vec()),
            (Form::Set, &[name, value]) => {
                l.name(name)?;
                let place = l.assigned(self.builder, name)?;
                Ok(Step::then(value, move |_, value| Ok(Step::Done(Core::Set(place, Box::new(value))))))
            }
            (Form::Define | Form::Struct | Form::Require | Form::Provide, _) => Err(l.error(LowerErrorKind::Definition, node)),
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(node, formals, body.to_vec(), false),
            (Form::App, &[f, ref args @ ..]) if args.iter().any(|&a| l.keyword(a).is_some()) || l.keyword_def(self.builder, f).is_some() => {
                self.keyword_call(node, f, args.to_vec())
            }
            (Form::App, &[f, ref args @ ..]) => match (l.struct_call(self.builder, f, args.len()), l.import(self.builder, f)) {
                (Some(call), _) => steps::all(args.to_vec(), move |s: &mut Self, args| Ok(Step::Done(call.core(args, &mut || s.l.fresh())))),
                (None, Some(import)) => steps::all(args.to_vec(), move |s: &mut Self, args| {
                    let mc = s.l.mc;
                    let call = import.call(mc, args, &mut || s.l.fresh());
                    call.map(Step::Done).map_err(|e| s.l.import_error(e, f))
                }),
                (None, None) => {
                    let args = args.to_vec();
                    Ok(Step::then(f, move |_: &mut Self, f| steps::all(args, move |_, args| Ok(Step::Done(Core::App(Box::new(f), args))))))
                }
            },
            (Form::Intrinsic, &[name, ref args @ ..]) => self.intrinsic(node, name, args.to_vec(), false),
            (Form::ApplyIntrinsic, &[name, ref args @ ..]) if !args.is_empty() => self.intrinsic(node, name, args.to_vec(), true),
            (Form::CallHost, &[name, ref args @ ..]) => self.call_host(node, name, args.to_vec()),
            _ => Err(l.error(LowerErrorKind::BadShape, node)),
        }
    }

    /// A `%let`, or if `recursive`, a `%letrec`.
    fn binding(&mut self, recursive: bool, node: Syntax<'gc>, binds: Syntax<'gc>, body: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        if body.is_empty() {
            return Err(l.error(LowerErrorKind::BadShape, node));
        }
        let (mut names, mut inits) = (Vec::new(), Vec::new());
        for bind in l.list(binds)? {
            let bind = l.list(bind)?;
            let &[name, init] = bind.as_slice() else { return Err(l.error(LowerErrorKind::BadShape, binds)) };
            names.push(l.name(name)?);
            inits.push(init);
        }
        l.distinct(&names)?;
        // A `%letrec`'s names are in scope in its inits, a `%let`'s only in its body.
        let vars = if recursive { l.bind(&names) } else { Vec::new() };
        steps::all(inits, move |s: &mut Self, mut inits: Vec<Core<'gc>>| {
            let vars = if recursive { vars } else { s.l.bind(&names) };
            s.body(body, move |s, body| {
                s.l.unbind(&names);
                for (init, name) in inits.iter_mut().zip(&names) {
                    init.name(name.datum(s.l.mc));
                }
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

    fn sequential_from(&mut self, mut q: Sequential<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let Some(bind) = q.left.next() else {
            let Sequential { names, mut lets, body, .. } = q;
            return self.body(body, move |s, mut core| {
                s.l.unbind(&names);
                while let Some(bind) = lets.pop() {
                    core = Core::Let(vec![bind], Box::new(core));
                }
                Ok(Step::Done(core))
            });
        };
        let bind = self.l.list(bind)?;
        let &[name, init] = bind.as_slice() else { return Err(self.l.error(LowerErrorKind::BadShape, q.binds)) };
        let name = self.l.name(name)?;
        Ok(Step::then(init, move |s: &mut Self, init| {
            q.lets.extend(s.l.bind(&[name]).into_iter().zip([init]));
            q.names.push(name);
            s.sequential_from(q)
        }))
    }

    /// A `%lambda`, or if `core_only`, the core of the keyword procedure it makes.
    fn lambda(&mut self, node: Syntax<'gc>, formals: Syntax<'gc>, body: Vec<Syntax<'gc>>, core_only: bool) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        if body.is_empty() {
            return Err(l.error(LowerErrorKind::BadShape, node));
        }
        let formals = l.formals(formals)?;
        let mut names = formals.names.clone();
        names.extend(formals.rest);
        l.distinct(&names)?;
        if !formals.is_plain() {
            let raws = formals.names.iter().map(|_| l.fresh()).collect();
            return self.defaults(Optional { node, formals, body, raws, inits: Vec::new(), next: 0, core_only });
        }
        let params = formals.names.len();
        let mut vars = l.bind(&names);
        self.body(body, move |s, body| {
            s.l.unbind(&names);
            let rest = (vars.len() > params).then(|| vars.pop()).flatten();
            let id = s.l.lambda_id();
            Ok(Step::Done(Core::Lambda(Lambda { id, params: vars, optional: 0, rest, body: Box::new(body), name: None, at: Position::of(s.l.mc, node.span(s.l.mc)) })))
        })
    }

    /// Binds the rest of an optional lambda's parameters, each with a default after what that
    /// lowers to, which sees the parameters before it, then lowers its body.
    fn defaults(&mut self, mut f: Optional<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        while let Some(&name) = f.formals.names.get(f.next) {
            let (raw, default) = (f.raws[f.next], f.formals.defaults[f.next]);
            f.next += 1;
            let Some(default) = default else {
                self.l.scope.entry(name.datum(self.l.mc).to_bits()).or_default().push(raw);
                continue;
            };
            return Ok(Step::then(default, move |s: &mut Self, default| {
                let var = s.l.bind(&[name])[0];
                f.inits.push(keyword::defaulted(var, raw, default));
                s.defaults(f)
            }));
        }
        let rest = f.formals.rest.map(|name| self.l.bind(&[name])[0]);
        let Optional { node, formals, body, raws, inits, core_only, .. } = f;
        self.body(body, move |s, mut body| {
            s.l.unbind(&formals.names);
            s.l.unbind(&formals.rest.into_iter().collect::<Vec<_>>());
            for bind in inits.into_iter().rev() {
                body = Core::Let(vec![bind], Box::new(body));
            }
            let mc = s.l.mc;
            let params = keyword::order(mc, &formals.params).into_iter().map(|i| raws[i]).collect();
            let shape = CallShape::of(mc, &formals.params, rest.is_some());
            let optional = u32::try_from(shape.optional).expect("fewer than 2^32 parameters");
            let lambda = Lambda { id: s.l.lambda_id(), optional, params, rest, body: Box::new(body), name: None, at: Position::of(mc, node.span(mc)) };
            if core_only || !formals.has_keywords() {
                return Ok(Step::Done(Core::Lambda(lambda)));
            }
            let core = s.l.fresh();
            let procedure = keyword::procedure(mc, &shape, Core::Ref(Place::Local(core)), &mut *s.l).map_err(|e| s.l.error(e, node))?;
            Ok(Step::Done(Core::Let(vec![(core, Core::Lambda(lambda))], Box::new(procedure))))
        })
    }

    /// An `%app` of `f` with keyword arguments in `args`, or of a keyword procedure whose core
    /// is known: a direct call of the core, if it takes the call, or else a `keyword-apply`. The
    /// arguments are each bound to a local, in the order they're written, the procedure's first
    /// if it isn't called directly.
    fn keyword_call(&mut self, node: Syntax<'gc>, f: Syntax<'gc>, args: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        let (mut kinds, mut nodes) = (Vec::new(), Vec::new());
        let mut items = args.into_iter();
        while let Some(arg) = items.next() {
            let Some(k) = l.keyword(arg) else {
                kinds.push(None);
                nodes.push(arg);
                continue;
            };
            let value = items.next().ok_or_else(|| l.error(LowerErrorKind::BadShape, arg))?;
            if kinds.contains(&Some(k)) {
                return Err(l.error(LowerErrorKind::Duplicate, arg));
            }
            kinds.push(Some(k));
            nodes.push(value);
        }
        let mut given: Vec<Keyword<'gc>> = kinds.iter().flatten().copied().collect();
        keyword::sort(l.mc, &mut given);
        let positional = kinds.iter().filter(|k| k.is_none()).count();
        let direct = l.keyword_def(self.builder, f).filter(|(_, shape)| shape.matches(&given, positional));
        let calls = direct.is_none().then_some(f).into_iter().chain(nodes).collect();
        steps::all(calls, move |s: &mut Self, cores| {
            let mut cores = cores.into_iter();
            let mut binds = Vec::new();
            let mut local = |s: &mut Self, core| {
                let var = s.l.fresh();
                binds.push((var, core));
                Core::Ref(Place::Local(var))
            };
            let procedure = if direct.is_none() { Some(local(s, cores.next().expect("the procedure"))) } else { None };
            let (mut keyword_values, mut positional) = (Vec::new(), Vec::new());
            for (kind, core) in kinds.into_iter().zip(cores) {
                let value = local(s, core);
                match kind {
                    Some(k) => keyword_values.push((k, value)),
                    None => positional.push(value),
                }
            }
            let value_of = |k: Keyword<'gc>| keyword_values.iter().find(|&&(other, _)| other == k).map(|(_, v)| v.clone());
            let call = match (direct, procedure) {
                (Some((CoreAt::Slot(core), shape)), _) => {
                    let place = s.builder.place(core, s.l.top, s.l.defining);
                    Core::App(Box::new(Core::Ref(place)), shape.core_args(value_of, positional))
                }
                (Some((CoreAt::Import(core), shape)), _) => {
                    let (mc, args) = (s.l.mc, shape.core_args(value_of, positional));
                    core.call(mc, args, &mut || s.l.fresh()).map_err(|e| s.l.import_error(e, f))?
                }
                (None, Some(procedure)) => {
                    let given = given.iter().map(|&k| (k, value_of(k).expect("a keyword given"))).collect();
                    keyword::apply(s.l.mc, procedure, given, positional).map_err(|e| s.l.error(e, node))?
                }
                (None, None) => unreachable!("an indirect call has its procedure"),
            };
            Ok(Step::Done(if binds.is_empty() { call } else { Core::Let(binds, Box::new(call)) }))
        })
    }

    /// An `%intrinsic`, or if `spread`, an `%apply-intrinsic`, whose argument count is only known
    /// as it runs.
    fn intrinsic(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: Vec<Syntax<'gc>>, spread: bool) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        l.name(name)?;
        let &prim = l.prims.get(&name.datum(l.mc).to_bits()).ok_or_else(|| l.error(LowerErrorKind::UnknownIntrinsic, name))?;
        if spread {
            return steps::all(args, move |_, args| Ok(Step::Done(Core::ApplyIntrinsic(prim, args))));
        }
        let takes = match prim {
            Prim::Intrinsic(i) => i.arity().is_none_or(|arity| usize::from(arity) == args.len()),
            Prim::Request(r) => r.takes(args.len()),
            Prim::Host(h) => h.takes(args.len()),
            Prim::Slot(op, _) => op.arity() == args.len(),
        };
        if !takes {
            return Err(l.error(LowerErrorKind::Arity, node));
        }
        steps::all(args, move |_, args| Ok(Step::Done(Core::Intrinsic(prim, args))))
    }

    /// A `%call-host` of the host function named `name`.
    fn call_host(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: Vec<Syntax<'gc>>) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        let l = &mut *self.l;
        l.name(name)?;
        let &def = l.hosts.get(&name.datum(l.mc).to_bits()).ok_or_else(|| l.error(LowerErrorKind::UnknownHost, name))?;
        if !def.takes(args.len()) {
            return Err(l.error(LowerErrorKind::Arity, node));
        }
        steps::all(args, move |_, args| Ok(Step::Done(Core::Intrinsic(Prim::Host(def), args))))
    }

    /// A body's expressions, in order, as one, to `then`.
    fn body(&mut self, nodes: Vec<Syntax<'gc>>, then: impl FnOnce(&mut Self, Core<'gc>) -> Result<Lo<'s, 'a, 'gc>, LowerError> + 's) -> Result<Lo<'s, 'a, 'gc>, LowerError> {
        steps::all(nodes, move |s: &mut Self, mut cores| {
            let body = cores.pop().expect("bodies aren't empty");
            if cores.is_empty() {
                return then(s, body);
            }
            // One `let` of what the forms before the last return, however many there are.
            let binds = cores.into_iter().map(|core| (s.l.fresh(), core)).collect();
            then(s, Core::Let(binds, Box::new(body)))
        })
    }
}
