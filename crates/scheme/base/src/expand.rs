//! The expander: Scheme's syntax to the compiler's core forms, hygienically, by sets of scopes
//! as Racket does it. Binding forms add a fresh scope to what they bind and to their bodies, and
//! each macro step flips a fresh scope on its input and output, so what the macro introduces
//! is told apart from what it was given. An identifier means the binding of its name whose
//! scopes are the most of its own.


use std::rc::Rc;

use ragwort_compiler::{Core, Lambda, Place, Var};
use ragwort_native::Globals;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::string::Strings;
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxContext, SyntaxMeta, SyntaxSpan};
use ragwort_vm::Machine;
use ragwort_vm::objects::{Global, GlobalFields};

use crate::case::{Built, Compiled};
use crate::scope::{BASE, Map, Op, Scope, Set, TOP};
use crate::tree::{Stx, Tree, TreeError, View};
use crate::{ExpandError, ExpandErrorKind};

/// How deeply expressions can nest before expanding them would take too much of the native
/// stack.
const MAX_DEPTH: usize = 256;
/// How deeply data can nest, which takes less of it.
pub(crate) const MAX_DATA_DEPTH: usize = 1024;
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
    DefineSyntax,
    LetSyntax,
    LetrecSyntax,
    SyntaxCase,
    Syntax,
    /// `quasisyntax` and its unquotes.
    Unsupported,
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

const KEYWORDS: [(&str, Keyword); 36] = [
    ("quote", Keyword::Form(Form::Quote)),
    ("if", Keyword::Form(Form::If)),
    ("lambda", Keyword::Form(Form::Lambda)),
    ("define", Keyword::Form(Form::Define)),
    ("set!", Keyword::Form(Form::Set)),
    ("begin", Keyword::Form(Form::Begin)),
    ("let", Keyword::Form(Form::Let)),
    ("letrec", Keyword::Form(Form::Letrec)),
    ("letrec*", Keyword::Form(Form::Letrec)),
    ("define-syntax", Keyword::Form(Form::DefineSyntax)),
    ("let-syntax", Keyword::Form(Form::LetSyntax)),
    ("letrec-syntax", Keyword::Form(Form::LetrecSyntax)),
    ("syntax-case", Keyword::Form(Form::SyntaxCase)),
    ("syntax", Keyword::Form(Form::Syntax)),
    ("quasisyntax", Keyword::Form(Form::Unsupported)),
    ("unsyntax", Keyword::Form(Form::Unsupported)),
    ("unsyntax-splicing", Keyword::Form(Form::Unsupported)),
    ("syntax-rules", Keyword::Macro(Macro::SyntaxRules)),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Binding<'gc> {
    Keyword(Keyword),
    Local(Var),
    Global(Gc<'gc, Global>),
    /// A global of the prelude's, which code outside it can't assign.
    Import(Gc<'gc, Global>),
    /// No binding: a global of the code's own named so, or of the prelude's if `base`.
    Free { base: bool },
    /// A macro defined in this load: the index of its transformer.
    Macro(u32),
    /// A pattern variable of `syntax-case`, which only `syntax` refers to: the local that holds
    /// what it matched, a list of them for each ellipsis it's under, `depth` of them.
    Pattern { var: Var, depth: u32 },
}

/// An identifier that two bindings could be, neither of whose scopes include the other's.
pub(crate) struct Ambiguous;

/// A form at the top level or in a body, expanded far enough to tell what it is.
enum Head {
    Define(Stx),
    DefineSyntax(Stx),
    Begin(Vec<Stx>),
    Expr(Stx),
}

/// A top-level form, with what it defines bound.
pub(crate) enum Top<'gc> {
    Define(Gc<'gc, Global>, Stx),
    Expr(Stx),
}

pub(crate) struct Expander<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
    strings: Strings<'a, 'gc>,
    symbols: Symbols<'gc>,
    pub(crate) tree: Tree<'a, 'gc>,
    keywords: Map<u64, Keyword>,
    globals: Globals<'gc>,
    prelude: Globals<'gc>,
    /// The globals of each table, by their names' words.
    user_cells: Map<u64, Gc<'gc, Global>>,
    base_cells: Map<u64, Gc<'gc, Global>>,
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
    depth: usize,
    /// The transformers of the load's macros.
    pub(crate) macros: Vec<Value<'gc>>,
    /// The patterns of its `syntax-case` clauses, and the templates of its `syntax` forms that
    /// have pattern variables in them.
    pub(crate) patterns: Vec<Rc<Compiled<'gc>>>,
    pub(crate) templates: Vec<Rc<Built<'gc>>>,
    /// What runs the transformers, once one has, and the fuel they have between them till then.
    pub(crate) machine: Option<Machine>,
    pub(crate) fuel: u64,
    /// The node each syntax object made from the tree was made from, by the object's word.
    pub(crate) unwrapped: Map<u64, Stx>,
    /// The metadata made for syntax of each kind with each set of scopes, and their contexts.
    pub(crate) metas: Map<(Set, usize), SyntaxMeta<'gc>>,
    pub(crate) contexts: Map<Set, SyntaxContext<'gc>>,
}

fn key<'gc>(symbol: Symbol<'gc>, mc: &Mutation<'gc>) -> u64 {
    symbol.value(mc).to_bits()
}

impl<'a, 'gc> Expander<'a, 'gc> {
    pub(crate) fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, globals: Globals<'gc>, prelude: Globals<'gc>) -> Result<Self, ExpandError> {
        let strings = Strings::new(mc);
        let intern = |name: &str| symbols.intern_str(&strings, name);
        let keywords = KEYWORDS.iter().map(|&(name, k)| Ok((key(intern(name)?, mc), k))).collect::<Result<_, ragwort_types::Error>>()?;
        let abbreviations = Abbreviation::ALL.iter().map(|a| intern(a.name())).collect::<Result<_, _>>()?;
        let mut tree = Tree::new(mc, abbreviations);
        let top = tree.scopes.set(vec![TOP])?;
        let base = tree.scopes.set(vec![BASE])?;
        let cells = |table: Globals<'gc>| table.iter(mc).map(|g| (g.name(mc).to_bits(), g)).collect();
        Ok(Self {
            mc,
            strings,
            symbols,
            tree,
            keywords,
            globals,
            prelude,
            user_cells: cells(globals),
            base_cells: cells(prelude),
            bindings: Map::default(),
            bound_in: Map::default(),
            top,
            base,
            vars: 0,
            lambdas: 0,
            depth: 0,
            macros: Vec::new(),
            patterns: Vec::new(),
            templates: Vec::new(),
            machine: None,
            fuel: MACRO_FUEL,
            unwrapped: Map::default(),
            metas: Map::default(),
            contexts: Map::default(),
        })
    }

    pub(crate) fn error(&self, kind: impl Into<ExpandErrorKind>, stx: Stx) -> ExpandError {
        self.error_at(kind, self.tree.span(stx))
    }

    pub(crate) fn error_at(&self, kind: impl Into<ExpandErrorKind>, span: SyntaxSpan<'gc>) -> ExpandError {
        ExpandError { kind: kind.into(), start: span.start(), end: span.end() }
    }

    fn tree_error(&self, e: TreeError, stx: Stx) -> ExpandError {
        match e {
            TreeError::TooDeep => self.error(ExpandErrorKind::TooDeep, stx),
            TreeError::OutOfMemory => self.error(OutOfMemory, stx),
        }
    }

    /// What the reader read, in the top-level scope.
    pub(crate) fn read(&mut self, node: Syntax<'gc>) -> Result<Stx, ExpandError> {
        let span = node.span(self.mc);
        let stx = self.tree.read(node, MAX_DATA_DEPTH).map_err(|e| {
            let kind = if e == TreeError::TooDeep { ExpandErrorKind::TooDeep } else { OutOfMemory.into() };
            ExpandError { kind, start: span.start(), end: span.end() }
        })?;
        Ok(self.tree.with(stx, TOP, Op::Add)?)
    }

    /// Binds what `form`, read at the top level, defines, and adds what it holds to `out`.
    pub(crate) fn top(&mut self, form: Stx, out: &mut Vec<Top<'gc>>) -> Result<(), ExpandError> {
        let mut queue = vec![form];
        while let Some(form) = queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    let cell = self.define_top(id)?;
                    out.push(Top::Define(cell, value));
                }
                Head::DefineSyntax(form) => {
                    let (id, m) = self.define_syntax(form)?;
                    self.bind(id, Binding::Macro(m))?;
                }
                Head::Begin(forms) => queue.extend(forms.into_iter().rev()),
                Head::Expr(e) => out.push(Top::Expr(e)),
            }
        }
        Ok(())
    }

    pub(crate) fn lower(&mut self, top: Top<'gc>) -> Result<Core<'gc>, ExpandError> {
        self.depth = 0;
        match top {
            Top::Define(cell, value) => Ok(Core::DefineGlobal(cell, Box::new(self.expr(value)?))),
            Top::Expr(e) => self.expr(e),
        }
    }

    /// Whether `form` is a definition, of a variable or a macro, a `begin`, or some other
    /// expression, once the macro uses it is are expanded.
    fn head(&mut self, mut form: Stx) -> Result<Head, ExpandError> {
        for _ in 0..MAX_DEPTH {
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
                Binding::Keyword(Keyword::Form(Form::Begin)) => return Ok(Head::Begin(self.proper(form)?[1..].to_vec())),
                _ => return Ok(Head::Expr(form)),
            };
        }
        Err(self.error(ExpandErrorKind::TooDeep, form))
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

    /// The global a top-level definition of `id` sets: the one of its name if it's in just the
    /// top-level scope, or else a new one only identifiers with its scopes refer to.
    fn define_top(&mut self, id: Stx) -> Result<Gc<'gc, Global>, ExpandError> {
        let symbol = self.tree.symbol(id).expect("definitions bind identifiers");
        if self.tree.scopes_of(id)? == self.top {
            return self.cell(symbol, false);
        }
        let cell = Global::new(self.mc, symbol.value(self.mc), Value::VOID, false)?;
        self.bind(id, Binding::Global(cell))?;
        Ok(cell)
    }

    /// The global named `symbol` in the code's table, or if `base`, the prelude's, made if it's
    /// not there.
    fn cell(&mut self, symbol: Symbol<'gc>, base: bool) -> Result<Gc<'gc, Global>, ExpandError> {
        let (cells, table) = if base { (&mut self.base_cells, self.prelude) } else { (&mut self.user_cells, self.globals) };
        let k = key(symbol, self.mc);
        if let Some(&cell) = cells.get(&k) {
            return Ok(cell);
        }
        let cell = Global::new(self.mc, symbol.value(self.mc), Value::VOID, false)?;
        table.add(self.mc, cell)?;
        cells.insert(k, cell);
        Ok(cell)
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
        let base = self.tree.scopes.contains(set, BASE);
        if !base && let Some(&cell) = self.user_cells.get(&k) {
            return Ok(Binding::Global(cell));
        }
        if let Some(&keyword) = self.keywords.get(&k) {
            return Ok(Binding::Keyword(keyword));
        }
        if let Some(&cell) = self.base_cells.get(&k) {
            return Ok(Binding::Import(cell));
        }
        Ok(Binding::Free { base })
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

    fn local(&mut self, id: Stx) -> Result<Var, ExpandError> {
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

    pub(crate) fn expr(&mut self, stx: Stx) -> Result<Core<'gc>, ExpandError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error(ExpandErrorKind::TooDeep, stx));
        }
        let core = match self.tree.view(stx)? {
            View::Id => self.reference(stx)?,
            View::Datum(value) => Core::Quote(value),
            View::Vector(_) => Core::Quote(self.strip(stx)?),
            View::List(items, tail) => self.compound(stx, &items, tail)?,
        };
        self.depth -= 1;
        Ok(core)
    }

    fn compound(&mut self, stx: Stx, items: &[Stx], tail: Option<Stx>) -> Result<Core<'gc>, ExpandError> {
        let Some(&head) = items.first() else { return Err(self.error(ExpandErrorKind::BadSyntax, stx)) };
        if self.is_id(head) {
            match self.resolve(head)? {
                Binding::Keyword(Keyword::Form(form)) => return self.form(form, stx, items, tail),
                Binding::Keyword(Keyword::Macro(m)) => {
                    let out = self.transform(m, stx)?;
                    return self.expr(out);
                }
                Binding::Keyword(Keyword::Aux(_)) => return Err(self.error(ExpandErrorKind::BadSyntax, head)),
                Binding::Macro(m) => {
                    let out = self.expand_macro(m, stx)?;
                    return self.expr(out);
                }
                _ => {}
            }
        }
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        let f = self.expr(head)?;
        Ok(Core::App(Box::new(f), self.exprs(&items[1..])?))
    }

    fn exprs(&mut self, stxs: &[Stx]) -> Result<Vec<Core<'gc>>, ExpandError> {
        stxs.iter().map(|&stx| self.expr(stx)).collect()
    }

    fn form(&mut self, form: Form, stx: Stx, items: &[Stx], tail: Option<Stx>) -> Result<Core<'gc>, ExpandError> {
        let bad = |this: &Self| Err(this.error(ExpandErrorKind::BadSyntax, stx));
        if tail.is_some() {
            return bad(self);
        }
        match (form, &items[1..]) {
            (Form::Quote, &[datum]) => Ok(Core::Quote(self.strip(datum)?)),
            (Form::If, &[test, then]) => Ok(Core::If(Box::new(self.expr(test)?), Box::new(self.expr(then)?), Box::new(Core::Quote(Value::VOID)))),
            (Form::If, &[test, then, other]) => {
                Ok(Core::If(Box::new(self.expr(test)?), Box::new(self.expr(then)?), Box::new(self.expr(other)?)))
            }
            (Form::Lambda, &[formals, ref body @ ..]) => self.lambda(stx, formals, body),
            (Form::Define, _) => Err(self.error(ExpandErrorKind::Definition, stx)),
            (Form::Set, &[id, value]) if self.is_id(id) => self.set(id, value),
            (Form::Begin, &[_, ..]) => self.sequence(&items[1..]),
            (Form::Let, &[name, _, _, ..]) if self.is_id(name) => {
                let out = self.transform(Macro::NamedLet, stx)?;
                self.expr(out)
            }
            (Form::Let | Form::Letrec, &[binds, ref body @ ..]) => self.binding(stx, binds, body, form == Form::Letrec),
            (Form::DefineSyntax, _) => Err(self.error(ExpandErrorKind::Definition, stx)),
            (Form::LetSyntax | Form::LetrecSyntax, &[binds, ref body @ ..]) => self.let_syntax(stx, binds, body, form == Form::LetrecSyntax),
            (Form::SyntaxCase, &[input, literals, ref clauses @ ..]) => self.syntax_case(input, literals, clauses),
            (Form::Syntax, &[template]) => self.syntax(template),
            (Form::Unsupported, _) => Err(self.error(ExpandErrorKind::Unsupported, stx)),
            _ => bad(self),
        }
    }

    fn reference(&mut self, id: Stx) -> Result<Core<'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Global(cell) => Place::Global(cell),
            Binding::Import(cell) => Place::Import(cell),
            Binding::Free { base } => Place::Global(self.cell(self.tree.symbol(id).expect("an identifier"), base)?),
            Binding::Macro(m) => {
                let out = self.expand_macro(m, id)?;
                return self.expr(out);
            }
            Binding::Keyword(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Ok(Core::Ref(place))
    }

    fn set(&mut self, id: Stx, value: Stx) -> Result<Core<'gc>, ExpandError> {
        let place = match self.resolve(id)? {
            Binding::Local(var) => Place::Local(var),
            Binding::Global(cell) => Place::Global(cell),
            Binding::Free { base: false } => Place::Global(self.cell(self.tree.symbol(id).expect("an identifier"), false)?),
            Binding::Import(_) | Binding::Free { base: true } => return Err(self.error(ExpandErrorKind::Immutable, id)),
            Binding::Keyword(_) | Binding::Macro(_) | Binding::Pattern { .. } => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
        };
        Ok(Core::Set(place, Box::new(self.expr(value)?)))
    }

    /// Expressions run in order, with the last one's value.
    fn sequence(&mut self, stxs: &[Stx]) -> Result<Core<'gc>, ExpandError> {
        let (&last, before) = stxs.split_last().expect("sequences aren't empty");
        let mut binds = Vec::with_capacity(before.len());
        for &stx in before {
            binds.push((self.fresh(), self.expr(stx)?));
        }
        let last = self.expr(last)?;
        Ok(if binds.is_empty() { last } else { Core::Let(binds, Box::new(last)) })
    }

    pub(crate) fn lambda_id(&mut self) -> u32 {
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        id
    }

    fn lambda(&mut self, stx: Stx, formals: Stx, body: &[Stx]) -> Result<Core<'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let formals = self.tree.with(formals, scope, Op::Add)?;
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
        let body = self.scoped(body, scope)?;
        let body = self.body(stx, &body)?;
        Ok(Core::Lambda(Lambda { id: self.lambda_id(), params, rest, body: Box::new(body) }))
    }

    /// A `let`, or if `recursive`, a `letrec`.
    fn binding(&mut self, stx: Stx, binds: Stx, body: &[Stx], recursive: bool) -> Result<Core<'gc>, ExpandError> {
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
        let (vars, inits) = if recursive {
            let vars: Vec<_> = ids.iter().map(|&id| self.local(id)).collect::<Result<_, _>>()?;
            let inits = self.scoped(&inits, scope)?;
            (vars, self.exprs(&inits)?)
        } else {
            let inits = self.exprs(&inits)?;
            (ids.iter().map(|&id| self.local(id)).collect::<Result<_, _>>()?, inits)
        };
        let body = self.scoped(body, scope)?;
        let body = Box::new(self.body(stx, &body)?);
        let binds = vars.into_iter().zip(inits).collect();
        Ok(if recursive { Core::Letrec(binds, body) } else { Core::Let(binds, body) })
    }

    /// A body: definitions and expressions in any order, as `letrec*` binds them, then an
    /// expression for its value. `stx` is the form it's the body of.
    pub(crate) fn body(&mut self, stx: Stx, body: &[Stx]) -> Result<Core<'gc>, ExpandError> {
        let scope = self.tree.scopes.fresh()?;
        let mut queue = self.scoped(body, scope)?;
        queue.reverse();
        let mut items: Vec<(Option<Var>, Stx)> = Vec::new();
        let (mut defined, mut names) = (Vec::new(), Vec::new());
        while let Some(form) = queue.pop() {
            match self.head(form)? {
                Head::Define(form) => {
                    let (id, value) = self.definition(form)?;
                    defined.push(id);
                    names.push(id);
                    items.push((Some(self.local(id)?), value));
                }
                Head::DefineSyntax(form) => {
                    let (id, m) = self.define_syntax(form)?;
                    names.push(id);
                    self.bind(id, Binding::Macro(m))?;
                }
                Head::Begin(forms) => queue.extend(forms.into_iter().rev()),
                Head::Expr(e) => items.push((None, e)),
            }
        }
        self.distinct(&names)?;
        let Some((None, last)) = items.pop() else { return Err(self.error(ExpandErrorKind::NoExpression, stx)) };
        if defined.is_empty() {
            let mut stxs: Vec<Stx> = items.into_iter().map(|(_, e)| e).collect();
            stxs.push(last);
            return self.sequence(&stxs);
        }
        let mut binds = Vec::with_capacity(items.len());
        for (var, value) in items {
            let var = var.unwrap_or_else(|| self.fresh());
            binds.push((var, self.expr(value)?));
        }
        Ok(Core::Letrec(binds, Box::new(self.expr(last)?)))
    }

    /// `stxs` with `scope` added.
    pub(crate) fn scoped(&mut self, stxs: &[Stx], scope: Scope) -> Result<Vec<Stx>, ExpandError> {
        Ok(stxs.iter().map(|&stx| self.tree.with(stx, scope, Op::Add)).collect::<Result<_, _>>()?)
    }

    pub(crate) fn strip(&mut self, stx: Stx) -> Result<Value<'gc>, ExpandError> {
        self.tree.strip(stx, MAX_DATA_DEPTH).map_err(|e| self.tree_error(e, stx))
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
