//! Lowering: native ragwort's syntax to core forms.

use std::collections::{HashMap, HashSet};

use ragwort_compiler::module::{Binding, ModuleBuilder, ModuleError, RequireSpec, Resolver, SpecError, Uninitialized};
use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::vector::Vectors;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind};
use ragwort_vm::{HostDef, Intrinsic, Read, Request};

/// How deeply forms can nest before lowering them would take too much of the native stack.
const MAX_DEPTH: usize = 256;

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
    /// A `%define`, `%require` or `%provide` that isn't at the top level.
    Definition,
    /// A module the resolver doesn't have, or one it gave that no [`ModuleBuilder`] built.
    Resolve,
    /// A require of a name the module doesn't export.
    NotProvided,
    /// A provide of a name the module doesn't define.
    NotDefined,
    /// A reference to an export of a module that hasn't defined it yet.
    Uninitialized,
    /// An `%intrinsic` of a name that isn't one.
    UnknownIntrinsic,
    /// A `%call-host` of a name that isn't one of the host functions the code was given.
    UnknownHost,
    /// An `%intrinsic` or `%call-host` with a number of arguments it doesn't take.
    Arity,
    /// Syntax native ragwort doesn't have, such as a quasiquote outside a quoted datum.
    Unsupported,
    /// Forms nested more than 256 deep.
    TooDeep,
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
    Require,
    Provide,
    Lambda,
    App,
    Intrinsic,
    ApplyIntrinsic,
    CallHost,
}

const FORMS: [(&str, Form); 14] = [
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
    depth: usize,
}

impl<'a, 'gc> Lowerer<'a, 'gc> {
    /// A lowerer of code that calls the host functions `hosts`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, hosts: &'static [HostDef]) -> Result<Self, Error> {
        let strings = Strings::new(mc);
        let word = |name: &str| symbols.intern_str(&strings, name).map(|s| s.value(mc).to_bits());
        let forms = FORMS.iter().map(|&(name, form)| Ok((word(name)?, form))).collect::<Result<_, Error>>()?;
        let intrinsics = Intrinsic::ALL.iter().map(|&i| (i.name(), Prim::Intrinsic(i)));
        let reads = Read::ALL.iter().map(|&r| (r.name(), Prim::Read(r)));
        let requests = Request::ALL.iter().map(|&r| (r.name(), Prim::Request(r)));
        let prims = intrinsics.chain(reads).chain(requests).map(|(name, prim)| Ok((word(name)?, prim))).collect::<Result<_, Error>>()?;
        let hosts = hosts.iter().map(|def| Ok((word(def.name)?, def))).collect::<Result<_, Error>>()?;
        Ok(Self {
            mc,
            pairs: Pairs::new(mc),
            strings: Strings::new(mc),
            symbols,
            provides: Vec::new(),
            top: 0,
            defining: None,
            forms,
            prims,
            hosts,
            abbreviations: Abbreviation::ALL.iter().map(|a| Ok(symbols.intern_str(&strings, a.name())?.value(mc))).collect::<Result<_, ragwort_types::Error>>()?,
            scope: HashMap::new(),
            vars: 0,
            lambdas: 0,
            depth: 0,
        })
    }

    /// Declares what top-level form `top`, `node`, defines, requires from `resolver` or provides.
    pub fn declare(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, top: u32, resolver: &mut dyn Resolver<'gc>) -> Result<(), LowerError> {
        let items = match self.head(node) {
            Some(Form::Define | Form::Require | Form::Provide) => self.list(node)?,
            _ => return Ok(()),
        };
        match (self.head(node), &items[1..]) {
            (Some(Form::Define), &[name, _]) => {
                self.name(name)?;
                builder.define(name.datum(self.mc), top).map_err(|e| self.module_error(e, name))?;
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
        self.depth = 0;
        self.top = top;
        match self.head(node) {
            Some(Form::Require | Form::Provide) => Ok(None),
            Some(Form::Define) => {
                let items = self.list(node)?;
                let &[_, name, value] = items.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, node)) };
                let Some(Binding::Slot(slot)) = builder.binding(name.datum(self.mc)) else { unreachable!("declared") };
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

    /// The require spec `spec`.
    fn spec(&self, spec: Syntax<'gc>) -> Result<RequireSpec<Syntax<'gc>>, LowerError> {
        if let Some(name) = self.text(spec) {
            return Ok(RequireSpec::Module(name, spec));
        }
        let items = self.list(spec)?;
        let Some((&head, args)) = items.split_first() else { return Err(self.error(LowerErrorKind::BadShape, spec)) };
        let word = self.text(head).filter(|_| head.kind(self.mc) == Some(SyntaxKind::Identifier));
        let named = |n: &Syntax<'gc>| -> Result<(String, Syntax<'gc>), LowerError> { Ok((self.identifier(*n)?, *n)) };
        Ok(match (word.as_deref(), args) {
            (Some("only-in"), &[inner, ref names @ ..]) => RequireSpec::Only(Box::new(self.spec(inner)?), names.iter().map(named).collect::<Result<_, _>>()?),
            (Some("except-in"), &[inner, ref names @ ..]) => RequireSpec::Except(Box::new(self.spec(inner)?), names.iter().map(named).collect::<Result<_, _>>()?),
            (Some("prefix-in"), &[prefix, inner]) => RequireSpec::Prefix(self.identifier(prefix)?, Box::new(self.spec(inner)?)),
            (Some("rename-in"), &[inner, ref renames @ ..]) => {
                let renames = renames.iter().map(|&r| self.pair_of_names(r).map(|(old, new)| (old, new, r))).collect::<Result<_, _>>()?;
                RequireSpec::Rename(Box::new(self.spec(inner)?), renames)
            }
            _ => return Err(self.error(LowerErrorKind::BadShape, spec)),
        })
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
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error(LowerErrorKind::TooDeep, node));
        }
        let core = match node.kind(self.mc) {
            Some(SyntaxKind::Identifier) => self.reference(builder, node)?,
            Some(SyntaxKind::Literal | SyntaxKind::Vector) => Core::Quote(self.datum(node)?),
            Some(SyntaxKind::Abbreviation(Abbreviation::Quote)) => Core::Quote(self.datum(self.inner(node)?)?),
            Some(SyntaxKind::List) => self.form(builder, node)?,
            _ => return Err(self.error(LowerErrorKind::Unsupported, node)),
        };
        self.depth -= 1;
        Ok(core)
    }

    fn form(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        let items = self.list(node)?;
        let form = items.first().filter(|head| head.kind(self.mc) == Some(SyntaxKind::Identifier)).and_then(|head| self.forms.get(&head.datum(self.mc).to_bits()));
        let Some(&form) = form else { return Err(self.error(LowerErrorKind::NotAForm, node)) };
        Ok(match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Core::Quote(self.datum(datum)?),
            (Form::If, &[test, then, other]) => Core::If(Box::new(self.expr(builder, test)?), Box::new(self.expr(builder, then)?), Box::new(self.expr(builder, other)?)),
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(builder, matches!(form, Form::Letrec), node, binds, body)?,
            (Form::LetStar, &[binds, ref body @ ..]) => self.sequential(builder, node, binds, body)?,
            (Form::Set, &[name, value]) => {
                self.name(name)?;
                let place = self.assigned(builder, name)?;
                Core::Set(place, Box::new(self.expr(builder, value)?))
            }
            (Form::Define | Form::Require | Form::Provide, _) => return Err(self.error(LowerErrorKind::Definition, node)),
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(builder, node, formals, body)?,
            (Form::App, &[f, ref args @ ..]) => match self.import(builder, f) {
                Some(import) => {
                    let args = self.exprs(builder, args)?;
                    let mc = self.mc;
                    import.call(mc, args, &mut || self.fresh()).map_err(|Uninitialized| self.error(LowerErrorKind::Uninitialized, f))?
                }
                None => Core::App(Box::new(self.expr(builder, f)?), self.exprs(builder, args)?),
            },
            (Form::Intrinsic, &[name, ref args @ ..]) => self.intrinsic(builder, node, name, args, false)?,
            (Form::ApplyIntrinsic, &[name, ref args @ ..]) if !args.is_empty() => self.intrinsic(builder, node, name, args, true)?,
            (Form::CallHost, &[name, ref args @ ..]) => self.call_host(builder, node, name, args)?,
            _ => return Err(self.error(LowerErrorKind::BadShape, node)),
        })
    }

    /// A `%let`, or if `recursive`, a `%letrec`.
    fn binding(&mut self, builder: &mut ModuleBuilder<'gc>, recursive: bool, node: Syntax<'gc>, binds: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        if body.is_empty() {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        let mut pairs = Vec::new();
        for bind in self.list(binds)? {
            let bind = self.list(bind)?;
            let &[name, init] = bind.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, binds)) };
            pairs.push((self.name(name)?, init));
        }
        let names: Vec<_> = pairs.iter().map(|&(name, _)| name).collect();
        self.distinct(&names)?;
        // A `%letrec`'s names are in scope in its inits, a `%let`'s only in its body.
        let vars = if recursive { self.bind(&names) } else { Vec::new() };
        let inits = pairs.iter().map(|&(_, init)| self.expr(builder, init)).collect::<Result<Vec<_>, _>>()?;
        let vars = if recursive { vars } else { self.bind(&names) };
        let body = self.body(builder, body)?;
        self.unbind(&names);
        let binds = vars.into_iter().zip(inits).collect();
        Ok(if recursive { Core::Letrec(binds, Box::new(body)) } else { Core::Let(binds, Box::new(body)) })
    }

    /// A `%let*`: nested `%let`s of one binding each, so each init sees the names before it.
    fn sequential(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, binds: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        if body.is_empty() {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        let (mut names, mut lets) = (Vec::new(), Vec::new());
        for bind in self.list(binds)? {
            let bind = self.list(bind)?;
            let &[name, init] = bind.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, binds)) };
            let name = self.name(name)?;
            let init = self.expr(builder, init)?;
            lets.extend(self.bind(&[name]).into_iter().zip([init]));
            names.push(name);
        }
        let mut core = self.body(builder, body)?;
        self.unbind(&names);
        while let Some(bind) = lets.pop() {
            core = Core::Let(vec![bind], Box::new(core));
        }
        Ok(core)
    }

    fn lambda(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, formals: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        if body.is_empty() {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        let (mut names, rest) = match formals.kind(self.mc) {
            Some(SyntaxKind::Identifier) => (Vec::new(), Some(formals)),
            Some(SyntaxKind::List) => {
                let mut elements = self.pairs.elements(formals.datum(self.mc));
                let names = elements.by_ref().map(|v| self.syntax(v, formals).and_then(|n| self.name(n))).collect::<Result<Vec<_>, _>>()?;
                let rest = elements.rest();
                let rest = if rest == Value::NIL { None } else { Some(self.name(self.syntax(rest, formals)?)?) };
                (names, rest)
            }
            _ => return Err(self.error(LowerErrorKind::BadShape, formals)),
        };
        let params = names.len();
        names.extend(rest);
        self.distinct(&names)?;
        let mut vars = self.bind(&names);
        let body = self.body(builder, body)?;
        self.unbind(&names);
        let rest = (vars.len() > params).then(|| vars.pop()).flatten();
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        Ok(Core::Lambda(Lambda { id, params: vars, optional: 0, rest, body: Box::new(body) }))
    }

    /// An `%intrinsic`, or if `spread`, an `%apply-intrinsic`, whose argument count is only known
    /// as it runs.
    fn intrinsic(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, name: Syntax<'gc>, args: &[Syntax<'gc>], spread: bool) -> Result<Core<'gc>, LowerError> {
        self.name(name)?;
        let &prim = self.prims.get(&name.datum(self.mc).to_bits()).ok_or_else(|| self.error(LowerErrorKind::UnknownIntrinsic, name))?;
        if spread {
            return Ok(Core::ApplyIntrinsic(prim, self.exprs(builder, args)?));
        }
        let takes = match prim {
            Prim::Intrinsic(i) => i.arity().is_none_or(|arity| usize::from(arity) == args.len()),
            Prim::Read(r) => usize::from(r.arity()) == args.len(),
            Prim::Request(r) => r.takes(args.len()),
            Prim::Host(h) => h.takes(args.len()),
            Prim::Slot(op, _) => op.arity() == args.len(),
        };
        if !takes {
            return Err(self.error(LowerErrorKind::Arity, node));
        }
        Ok(Core::Intrinsic(prim, self.exprs(builder, args)?))
    }

    /// A `%call-host` of the host function named `name`.
    fn call_host(&mut self, builder: &mut ModuleBuilder<'gc>, node: Syntax<'gc>, name: Syntax<'gc>, args: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        self.name(name)?;
        let &def = self.hosts.get(&name.datum(self.mc).to_bits()).ok_or_else(|| self.error(LowerErrorKind::UnknownHost, name))?;
        if !def.takes(args.len()) {
            return Err(self.error(LowerErrorKind::Arity, node));
        }
        Ok(Core::Intrinsic(Prim::Host(def), self.exprs(builder, args)?))
    }

    /// A body's expressions, in order, as one.
    fn body(&mut self, builder: &mut ModuleBuilder<'gc>, nodes: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        let mut cores = self.exprs(builder, nodes)?;
        let body = cores.pop().expect("bodies aren't empty");
        if cores.is_empty() {
            return Ok(body);
        }
        // One `let` of what the forms before the last return, however many there are.
        let binds = cores.into_iter().map(|core| (self.fresh(), core)).collect();
        Ok(Core::Let(binds, Box::new(body)))
    }

    fn exprs(&mut self, builder: &mut ModuleBuilder<'gc>, nodes: &[Syntax<'gc>]) -> Result<Vec<Core<'gc>>, LowerError> {
        nodes.iter().map(|&node| self.expr(builder, node)).collect()
    }

    /// The quoted datum `node` reads as, without its syntax.
    fn datum(&mut self, node: Syntax<'gc>) -> Result<Value<'gc>, LowerError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error(LowerErrorKind::TooDeep, node));
        }
        let oom = |this: &Self, e: OutOfMemory| this.error(e, node);
        let datum = match node.kind(self.mc) {
            Some(SyntaxKind::Identifier | SyntaxKind::Literal) => node.datum(self.mc),
            Some(SyntaxKind::Abbreviation(a)) => {
                let name = self.abbreviations[a as usize];
                let inner = self.datum(self.inner(node)?)?;
                self.pairs.list(&[name, inner]).map_err(|e| oom(self, e))?
            }
            Some(SyntaxKind::Vector) => {
                let vector = Vectors::new(self.mc).vector(node.datum(self.mc)).ok_or_else(|| self.error(LowerErrorKind::Unsupported, node))?;
                let items = (0..vector.len(self.mc)).filter_map(|i| vector.get(self.mc, i));
                let items = items.map(|v| self.syntax(v, node).and_then(|n| self.datum(n))).collect::<Result<Vec<_>, _>>()?;
                Vectors::new(self.mc).immutable_from_slice(&items).map_err(|e| oom(self, e))?.value(self.mc)
            }
            Some(SyntaxKind::List) => {
                let mut elements = self.pairs.elements(node.datum(self.mc));
                let items: Vec<_> = elements.by_ref().collect();
                let rest = elements.rest();
                let items = items.into_iter().map(|v| self.syntax(v, node).and_then(|n| self.datum(n))).collect::<Result<Vec<_>, _>>()?;
                let rest = if rest == Value::NIL { rest } else { self.datum(self.syntax(rest, node)?)? };
                self.pairs.list_with_tail(items, rest).map_err(|e| oom(self, e))?
            }
            _ => return Err(self.error(LowerErrorKind::Unsupported, node)),
        };
        self.depth -= 1;
        Ok(datum)
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
            Err(Binding::Slot(slot)) => Core::Ref(builder.place(slot, self.top, self.defining)),
            Err(Binding::Import(import)) => import.reference(self.mc).map_err(|Uninitialized| self.error(LowerErrorKind::Uninitialized, name))?,
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
