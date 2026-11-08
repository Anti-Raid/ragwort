//! Lowering: native ragwort's syntax to core forms.

use std::collections::{HashMap, HashSet};

use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::Error;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;
use ragwort_types::vector::Vectors;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind};
use ragwort_vm::objects::{Global, GlobalFields};
use ragwort_vm::{HostDef, Intrinsic, Read, Request};

use crate::Globals;

/// How deeply forms can nest before lowering them would take too much of the native stack.
const MAX_DEPTH: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LowerErrorKind {
    /// A list that doesn't start with a form's name, such as a call not written as an `%app`.
    NotAForm,
    /// A form whose parts aren't the ones it takes.
    BadShape,
    /// A name bound twice by one `%let`, `%letrec` or `%lambda`.
    Duplicate,
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

#[derive(Clone, Copy)]
enum Form {
    Quote,
    If,
    Let,
    LetStar,
    Letrec,
    Set,
    DefineGlobal,
    Lambda,
    App,
    Intrinsic,
    ApplyIntrinsic,
    CallHost,
}

const FORMS: [(&str, Form); 12] = [
    ("%quote", Form::Quote),
    ("%if", Form::If),
    ("%let", Form::Let),
    ("%let*", Form::LetStar),
    ("%letrec", Form::Letrec),
    ("%set!", Form::Set),
    ("%define-global", Form::DefineGlobal),
    ("%lambda", Form::Lambda),
    ("%app", Form::App),
    ("%intrinsic", Form::Intrinsic),
    ("%apply-intrinsic", Form::ApplyIntrinsic),
    ("%call-host", Form::CallHost),
];

/// Lowers forms one at a time, numbering their variables and lambdas apart, naming globals in
/// its [`Globals`], and calling the host functions it was given.
pub struct Lowerer<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    pairs: Pairs<'a, 'gc>,
    globals: Globals<'gc>,
    /// The globals, by their names' words.
    cells: HashMap<u64, Gc<'gc, Global>>,
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
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, globals: Globals<'gc>, hosts: &'static [HostDef]) -> Result<Self, Error> {
        let strings = Strings::new(mc);
        let word = |name: &str| symbols.intern_str(&strings, name).map(|s| s.value(mc).to_bits());
        let forms = FORMS.iter().map(|&(name, form)| Ok((word(name)?, form))).collect::<Result<_, Error>>()?;
        let intrinsics = Intrinsic::ALL.iter().map(|&i| (i.name(), Prim::Intrinsic(i)));
        let reads = Read::ALL.iter().map(|&r| (r.name(), Prim::Read(r)));
        let requests = Request::ALL.iter().map(|&r| (r.name(), Prim::Request(r)));
        let prims = intrinsics.chain(reads).chain(requests).map(|(name, prim)| Ok((word(name)?, prim))).collect::<Result<_, Error>>()?;
        let cells = globals.iter(mc).map(|g| (g.name(mc).to_bits(), g)).collect();
        let hosts = hosts.iter().map(|def| Ok((word(def.name)?, def))).collect::<Result<_, Error>>()?;
        Ok(Self {
            mc,
            pairs: Pairs::new(mc),
            globals,
            cells,
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

    /// Lowers a form read at the top level.
    pub fn lower(&mut self, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        self.scope.clear();
        self.depth = 0;
        self.expr(node)
    }

    fn expr(&mut self, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error(LowerErrorKind::TooDeep, node));
        }
        let core = match node.kind(self.mc) {
            Some(SyntaxKind::Identifier) => Core::Ref(self.place(node)?),
            Some(SyntaxKind::Literal | SyntaxKind::Vector) => Core::Quote(self.datum(node)?),
            Some(SyntaxKind::Abbreviation(Abbreviation::Quote)) => Core::Quote(self.datum(self.inner(node)?)?),
            Some(SyntaxKind::List) => self.form(node)?,
            _ => return Err(self.error(LowerErrorKind::Unsupported, node)),
        };
        self.depth -= 1;
        Ok(core)
    }

    fn form(&mut self, node: Syntax<'gc>) -> Result<Core<'gc>, LowerError> {
        let items = self.list(node)?;
        let form = items.first().filter(|head| head.kind(self.mc) == Some(SyntaxKind::Identifier)).and_then(|head| self.forms.get(&head.datum(self.mc).to_bits()));
        let Some(&form) = form else { return Err(self.error(LowerErrorKind::NotAForm, node)) };
        Ok(match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Core::Quote(self.datum(datum)?),
            (Form::If, &[test, then, other]) => Core::If(Box::new(self.expr(test)?), Box::new(self.expr(then)?), Box::new(self.expr(other)?)),
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(matches!(form, Form::Letrec), node, binds, body)?,
            (Form::LetStar, &[binds, ref body @ ..]) => self.sequential(node, binds, body)?,
            (Form::Set, &[name, value]) => {
                self.name(name)?;
                Core::Set(self.place(name)?, Box::new(self.expr(value)?))
            }
            (Form::DefineGlobal, &[name, value]) => {
                self.name(name)?;
                Core::DefineGlobal(self.global(name)?, Box::new(self.expr(value)?))
            }
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(node, formals, body)?,
            (Form::App, &[f, ref args @ ..]) => Core::App(Box::new(self.expr(f)?), self.exprs(args)?),
            (Form::Intrinsic, &[name, ref args @ ..]) => self.intrinsic(node, name, args, false)?,
            (Form::ApplyIntrinsic, &[name, ref args @ ..]) if !args.is_empty() => self.intrinsic(node, name, args, true)?,
            (Form::CallHost, &[name, ref args @ ..]) => self.call_host(node, name, args)?,
            _ => return Err(self.error(LowerErrorKind::BadShape, node)),
        })
    }

    /// A `%let`, or if `recursive`, a `%letrec`.
    fn binding(&mut self, recursive: bool, node: Syntax<'gc>, binds: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
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
        let inits = pairs.iter().map(|&(_, init)| self.expr(init)).collect::<Result<Vec<_>, _>>()?;
        let vars = if recursive { vars } else { self.bind(&names) };
        let body = self.body(body)?;
        self.unbind(&names);
        let binds = vars.into_iter().zip(inits).collect();
        Ok(if recursive { Core::Letrec(binds, Box::new(body)) } else { Core::Let(binds, Box::new(body)) })
    }

    /// A `%let*`: nested `%let`s of one binding each, so each init sees the names before it.
    fn sequential(&mut self, node: Syntax<'gc>, binds: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        if body.is_empty() {
            return Err(self.error(LowerErrorKind::BadShape, node));
        }
        let (mut names, mut lets) = (Vec::new(), Vec::new());
        for bind in self.list(binds)? {
            let bind = self.list(bind)?;
            let &[name, init] = bind.as_slice() else { return Err(self.error(LowerErrorKind::BadShape, binds)) };
            let name = self.name(name)?;
            let init = self.expr(init)?;
            lets.extend(self.bind(&[name]).into_iter().zip([init]));
            names.push(name);
        }
        let mut core = self.body(body)?;
        self.unbind(&names);
        while let Some(bind) = lets.pop() {
            core = Core::Let(vec![bind], Box::new(core));
        }
        Ok(core)
    }

    fn lambda(&mut self, node: Syntax<'gc>, formals: Syntax<'gc>, body: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
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
        let body = self.body(body)?;
        self.unbind(&names);
        let rest = (vars.len() > params).then(|| vars.pop()).flatten();
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        Ok(Core::Lambda(Lambda { id, params: vars, rest, body: Box::new(body) }))
    }

    /// An `%intrinsic`, or if `spread`, an `%apply-intrinsic`, whose argument count is only known
    /// as it runs.
    fn intrinsic(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: &[Syntax<'gc>], spread: bool) -> Result<Core<'gc>, LowerError> {
        self.name(name)?;
        let &prim = self.prims.get(&name.datum(self.mc).to_bits()).ok_or_else(|| self.error(LowerErrorKind::UnknownIntrinsic, name))?;
        if spread {
            return Ok(Core::ApplyIntrinsic(prim, self.exprs(args)?));
        }
        let takes = match prim {
            Prim::Intrinsic(i) => i.arity().is_none_or(|arity| usize::from(arity) == args.len()),
            Prim::Read(r) => usize::from(r.arity()) == args.len(),
            Prim::Request(r) => r.takes(args.len()),
            Prim::Host(h) => h.takes(args.len()),
        };
        if !takes {
            return Err(self.error(LowerErrorKind::Arity, node));
        }
        Ok(Core::Intrinsic(prim, self.exprs(args)?))
    }

    /// A `%call-host` of the host function named `name`.
    fn call_host(&mut self, node: Syntax<'gc>, name: Syntax<'gc>, args: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        self.name(name)?;
        let &def = self.hosts.get(&name.datum(self.mc).to_bits()).ok_or_else(|| self.error(LowerErrorKind::UnknownHost, name))?;
        if !def.takes(args.len()) {
            return Err(self.error(LowerErrorKind::Arity, node));
        }
        Ok(Core::Intrinsic(Prim::Host(def), self.exprs(args)?))
    }

    /// A body's expressions, in order, as one.
    fn body(&mut self, nodes: &[Syntax<'gc>]) -> Result<Core<'gc>, LowerError> {
        let mut cores = self.exprs(nodes)?;
        let mut body = cores.pop().expect("bodies aren't empty");
        while let Some(core) = cores.pop() {
            body = Core::Let(vec![(self.fresh(), core)], Box::new(body));
        }
        Ok(body)
    }

    fn exprs(&mut self, nodes: &[Syntax<'gc>]) -> Result<Vec<Core<'gc>>, LowerError> {
        nodes.iter().map(|&node| self.expr(node)).collect()
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

    /// What `name`, an identifier, refers to.
    fn place(&mut self, name: Syntax<'gc>) -> Result<Place<'gc>, LowerError> {
        match self.scope.get(&name.datum(self.mc).to_bits()).and_then(|vars| vars.last()) {
            Some(&var) => Ok(Place::Local(var)),
            None => Ok(Place::Global(self.global(name)?)),
        }
    }

    /// The global named by `name`, made if no code has named it yet.
    fn global(&mut self, name: Syntax<'gc>) -> Result<Gc<'gc, Global>, LowerError> {
        let symbol = name.datum(self.mc);
        if let Some(&global) = self.cells.get(&symbol.to_bits()) {
            return Ok(global);
        }
        let global = Global::new(self.mc, symbol, Value::VOID, false).map_err(|e| self.error(e, name))?;
        self.globals.add(self.mc, global).map_err(|e| self.error(e, name))?;
        self.cells.insert(symbol.to_bits(), global);
        Ok(global)
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
