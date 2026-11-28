//! The core forms: the forms of native ragwort, which the expander of every language can expand.
//!
//! A macro written in native ragwort expands to core forms. Because every front end expands them, such a macro can be used from any
//! language. The parts of a core form are expressions of the language that the form is in, so a use of the macro can pass it
//! expressions of its own language.
//!
//! A program can name a core form only if its language says so. Native ragwort does. In other languages, an identifier refers to a
//! core form only if a macro from native ragwort introduced it.

use ragwort_compiler::steps::Step;
use ragwort_compiler::{Arg, Core, Formal, Lambda, OptionalLambda, Prim, Var, keyword};
use ragwort_types::symbol::Keyword;
use ragwort_vm::HostDef;

use crate::engine::Binding;
use crate::expand::{Call, Ex, Expand, Host};
use crate::scope::{Op, Scope};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A core form. [`CoreForm::NAMED`] gives the name of each.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreForm {
    Quote,
    If,
    Let,
    LetStar,
    Letrec,
    Set,
    Lambda,
    App,
    Intrinsic,
    ApplyIntrinsic,
    CallHost,
    Loop,
    Break,
    Continue,
    Begin,
    Define,
    DefineSyntax,
    Struct,
    Require,
    Provide,
    SyntaxCase,
    Syntax,
    SyntaxRules,
    /// `...` in a pattern or a template.
    Ellipsis,
    /// `_` in a pattern.
    Underscore,
    /// A form that the reader has an abbreviation for, but that is not a core form, such as `quasiquote`.
    Unsupported,
}

impl CoreForm {
    /// The names of the core forms. `quote` and `syntax` are the forms that the reader's `'` and `#'` stand for.
    pub const NAMED: [(&'static str, CoreForm); 33] = [
        ("%struct", CoreForm::Struct),
        ("%quote", CoreForm::Quote),
        ("%if", CoreForm::If),
        ("%let", CoreForm::Let),
        ("%let*", CoreForm::LetStar),
        ("%letrec", CoreForm::Letrec),
        ("%set!", CoreForm::Set),
        ("%define", CoreForm::Define),
        ("%require", CoreForm::Require),
        ("%provide", CoreForm::Provide),
        ("%lambda", CoreForm::Lambda),
        ("%app", CoreForm::App),
        ("%intrinsic", CoreForm::Intrinsic),
        ("%apply-intrinsic", CoreForm::ApplyIntrinsic),
        ("%call-host", CoreForm::CallHost),
        ("%loop", CoreForm::Loop),
        ("%break", CoreForm::Break),
        ("%continue", CoreForm::Continue),
        ("%begin", CoreForm::Begin),
        ("%define-syntax", CoreForm::DefineSyntax),
        ("%syntax-case", CoreForm::SyntaxCase),
        ("%syntax", CoreForm::Syntax),
        ("%syntax-rules", CoreForm::SyntaxRules),
        ("...", CoreForm::Ellipsis),
        ("_", CoreForm::Underscore),
        ("quote", CoreForm::Quote),
        ("syntax", CoreForm::Syntax),
        ("quasiquote", CoreForm::Unsupported),
        ("unquote", CoreForm::Unsupported),
        ("unquote-splicing", CoreForm::Unsupported),
        ("quasisyntax", CoreForm::Unsupported),
        ("unsyntax", CoreForm::Unsupported),
        ("unsyntax-splicing", CoreForm::Unsupported),
    ];

    /// Returns the core form named `name`.
    pub fn named(name: &str) -> Option<Self> {
        Self::NAMED.iter().find(|(known, _)| *known == name).map(|&(_, form)| form)
    }
}

/// The expansion of the core forms. Every [`Host`] has it.
pub trait Forms<'a, 'gc: 'a>: Host<'a, 'gc> {
    /// Returns the first step of expanding `stx`, a use of the core form `form` as an expression. `items` are the items of `stx`,
    /// and `tail` is its tail if it is an improper list.
    fn core_form(&mut self, form: CoreForm, stx: Stx, items: Vec<Stx>, tail: Option<Stx>) -> Result<Ex<'a, 'gc, Self>, ExpandError> {
        if tail.is_some() {
            return Err(self.error(ExpandErrorKind::BadSyntax, stx));
        }
        match (form, &items[1..]) {
            (CoreForm::Quote, &[datum]) => Ok(Step::Done(Core::Quote(self.strip(datum)?))),
            (CoreForm::If, &[test, then, other]) => Self::exprs(vec![test, then, other], |_, parts| {
                let [test, then, other] = <[Core<'gc>; 3]>::try_from(parts).expect("three parts");
                Ok(Step::Done(Core::If(Box::new(test), Box::new(then), Box::new(other))))
            }),
            (CoreForm::Let | CoreForm::Letrec, &[binds, ref body @ ..]) => binding(self, form == CoreForm::Letrec, stx, binds, body.to_vec()),
            (CoreForm::LetStar, &[binds, ref body @ ..]) => sequential(self, stx, binds, body.to_vec()),
            (CoreForm::Set, &[name, value]) => {
                if !self.is_id(name) {
                    return Err(self.error(ExpandErrorKind::BadSyntax, name));
                }
                self.assign(name, value)
            }
            (CoreForm::Define | CoreForm::DefineSyntax | CoreForm::Struct | CoreForm::Require | CoreForm::Provide, _) => Err(self.error(ExpandErrorKind::Definition, stx)),
            (CoreForm::Lambda, &[formals, ref body @ ..]) => lambda(self, stx, formals, body.to_vec()),
            (CoreForm::App, &[callee, ref args @ ..]) if args.iter().any(|&arg| self.tree.keyword(arg).is_some()) => keyword_call(self, stx, callee, args.to_vec()),
            (CoreForm::App, &[callee, ref args @ ..]) => {
                let args = args.to_vec();
                Self::expr(callee, move |_, callee| Self::exprs(args, move |this, args| Ok(Step::Done(Core::App(Box::new(callee), args, this.position(stx))))))
            }
            (CoreForm::Intrinsic, &[name, ref args @ ..]) => intrinsic(self, stx, name, args.to_vec(), false),
            (CoreForm::ApplyIntrinsic, &[name, ref args @ ..]) if !args.is_empty() => intrinsic(self, stx, name, args.to_vec(), true),
            (CoreForm::CallHost, &[name, ref args @ ..]) => call_host(self, stx, name, args.to_vec()),
            // `(%loop name body ...)` runs its body again and again. `(%break name)` leaves the loop of that name, and `(%continue name)` starts its next round.
            (CoreForm::Loop, &[name, ref body @ ..]) if !body.is_empty() => {
                if !self.is_id(name) {
                    return Err(self.error(ExpandErrorKind::BadSyntax, name));
                }
                let label = self.fresh();
                let scope = self.tree.scopes.fresh()?;
                let name = self.tree.with(name, scope, Op::Add)?;
                self.bind_label(name, label)?;
                let body = self.scoped(body, scope)?;
                sequence(self, body, Wrap::Loop(label))
            }
            (CoreForm::Break | CoreForm::Continue, &[name]) => {
                if !self.is_id(name) {
                    return Err(self.error(ExpandErrorKind::BadSyntax, name));
                }
                let Some(label) = self.label(name)? else { return Err(self.error(ExpandErrorKind::Label, name)) };
                let jump = if form == CoreForm::Break {
                    Core::Break(label)
                } else {
                    Core::Continue(label)
                };
                Ok(Step::Done(jump))
            }
            (CoreForm::Begin, &[_, ..]) => sequence(self, items[1..].to_vec(), Wrap::None),
            (CoreForm::SyntaxCase, &[input, literals, ref clauses @ ..]) => self.syntax_case(input, literals, clauses.to_vec()),
            (CoreForm::Syntax, &[template]) => Ok(Step::Done(self.syntax(template)?)),
            (CoreForm::SyntaxRules, &[literals, ref rules @ ..]) => Ok(Step::Tail(Call::Expr(syntax_rules(self, stx, literals, rules)?))),
            (CoreForm::Unsupported, _) => Err(self.error(ExpandErrorKind::Unsupported, stx)),
            _ => Err(self.error(ExpandErrorKind::BadSyntax, stx)),
        }
    }
}

impl<'a, 'gc: 'a, H: Host<'a, 'gc>> Forms<'a, 'gc> for H {}

/// What goes around the expression of a body.
enum Wrap<'gc> {
    None,
    Loop(Var),
    /// A `%let` of the bindings, or a `%letrec` if the flag is set.
    Let(Vec<(Var, Core<'gc>)>, bool),
    /// Nested `%let`s of one binding each, outermost first.
    Lets(Vec<(Var, Core<'gc>)>),
    /// A lambda with `params` positional parameters. `vars` holds them, followed by the rest parameter if there is one.
    Lambda { stx: Stx, vars: Vec<Var>, params: usize },
    OptionalLambda { stx: Stx, params: Vec<Formal<'gc>>, rest: Option<Var> },
}

/// Expands `stxs`, the expressions of a body, in order. Combines them into one expression, which has the value of the last, and puts `wrap` around it.
fn sequence<'a, 'gc: 'a, H: Host<'a, 'gc>>(_: &mut H, stxs: Vec<Stx>, wrap: Wrap<'gc>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    H::exprs(stxs, move |this, mut cores| {
        let last = cores.pop().expect("bodies aren't empty");
        // A single `let` binds the values of all the expressions before the last to unused variables, however many there are. The last expression is the `let`'s body.
        let body = if cores.is_empty() {
            last
        } else {
            let mut binds = Vec::with_capacity(cores.len());
            for core in cores {
                binds.push((this.fresh(), core));
            }
            Core::Let(binds, Box::new(last))
        };
        Ok(Step::Done(match wrap {
            Wrap::None => body,
            Wrap::Loop(label) => Core::Loop(label, Box::new(body)),
            Wrap::Let(binds, true) => Core::Letrec(binds, Box::new(body)),
            Wrap::Let(binds, false) => Core::Let(binds, Box::new(body)),
            Wrap::Lets(mut lets) => {
                let mut core = body;
                while let Some(bind) = lets.pop() {
                    core = Core::Let(vec![bind], Box::new(core));
                }
                core
            }
            Wrap::Lambda { stx, mut vars, params } => {
                let rest = if vars.len() > params {
                    vars.pop()
                } else {
                    None
                };
                let id = this.lambda_id();
                Core::Lambda(Lambda { id, params: vars, optional: 0, rest, body: Box::new(body), name: None, at: this.position(stx) })
            }
            Wrap::OptionalLambda { stx, params, rest } => {
                let id = this.lambda_id();
                Core::OptionalLambda(OptionalLambda { id, params, rest, body: Box::new(body), name: None, at: this.position(stx) })
            }
        }))
    })
}

/// Allocates a local variable for each of `ids` and binds the identifier to it.
fn locals<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, ids: &[Stx]) -> Result<Vec<Var>, ExpandError> {
    let mut vars = Vec::with_capacity(ids.len());
    for &id in ids {
        vars.push(this.local(id)?);
    }
    Ok(vars)
}

/// Expands a `%let`, or a `%letrec` if `recursive` is true.
fn binding<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, recursive: bool, stx: Stx, binds: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    if body.is_empty() {
        return Err(this.error(ExpandErrorKind::BadSyntax, stx));
    }
    let scope = this.tree.scopes.fresh()?;
    let (mut ids, mut inits) = (Vec::new(), Vec::new());
    for bind in this.proper(binds)? {
        let bind = this.proper(bind)?;
        let &[name, init] = bind.as_slice() else { return Err(this.error(ExpandErrorKind::BadSyntax, binds)) };
        if !this.is_id(name) {
            return Err(this.error(ExpandErrorKind::BadSyntax, name));
        }
        ids.push(this.tree.with(name, scope, Op::Add)?);
        inits.push(init);
    }
    this.distinct(&ids)?;
    let body = this.scoped(&body, scope)?;
    // The names of a `%letrec` are in scope in its inits. The names of a `%let` are in scope only in its body.
    if recursive {
        let vars = locals(this, &ids)?;
        let inits = this.scoped(&inits, scope)?;
        return H::exprs(inits, move |this, inits| sequence(this, body, Wrap::Let(vars.into_iter().zip(inits).collect(), true)));
    }
    H::exprs(inits, move |this, inits| {
        let vars = locals(this, &ids)?;
        sequence(this, body, Wrap::Let(vars.into_iter().zip(inits).collect(), false))
    })
}

/// The state of expanding a `%let*`. `left` holds the bindings that are not expanded yet. `scopes` holds the scope of each name bound so far, and `lets` holds the variable and the expanded init of each.
struct Sequential<'gc> {
    binds: Stx,
    left: std::vec::IntoIter<Stx>,
    scopes: Vec<Scope>,
    lets: Vec<(Var, Core<'gc>)>,
    body: Vec<Stx>,
}

/// Expands a `%let*` to nested `%let`s of one binding each, so each init can refer to the names bound before it.
fn sequential<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, binds: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    if body.is_empty() {
        return Err(this.error(ExpandErrorKind::BadSyntax, stx));
    }
    let left = this.proper(binds)?.into_iter();
    sequential_from(this, Sequential { binds, left, scopes: Vec::new(), lets: Vec::new(), body })
}

fn sequential_from<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, mut sequential: Sequential<'gc>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    let Some(bind) = sequential.left.next() else {
        let mut body = sequential.body;
        for &scope in &sequential.scopes {
            body = this.scoped(&body, scope)?;
        }
        return sequence(this, body, Wrap::Lets(sequential.lets));
    };
    let bind = this.proper(bind)?;
    let &[name, init] = bind.as_slice() else { return Err(this.error(ExpandErrorKind::BadSyntax, sequential.binds)) };
    if !this.is_id(name) {
        return Err(this.error(ExpandErrorKind::BadSyntax, name));
    }
    let (mut name, mut init) = (name, init);
    for &scope in &sequential.scopes {
        name = this.tree.with(name, scope, Op::Add)?;
        init = this.tree.with(init, scope, Op::Add)?;
    }
    let scope = this.tree.scopes.fresh()?;
    let name = this.tree.with(name, scope, Op::Add)?;
    H::expr(init, move |this, init| {
        let var = this.local(name)?;
        sequential.scopes.push(scope);
        sequential.lets.push((var, init));
        sequential_from(this, sequential)
    })
}

/// The parsed formals of a `%lambda`. `params`, `names` and `defaults` are parallel: entry `i`
/// describes parameter `i`, its name, and its default if it has one. `rest` is the rest parameter.
struct Formals<'gc> {
    params: Vec<keyword::Param<'gc>>,
    names: Vec<Stx>,
    defaults: Vec<Option<Stx>>,
    rest: Option<Stx>,
}

/// Parses `formals`, the parameter list of a `%lambda`, which has the syntax of Racket's `lambda`. A parameter is a name or
/// `[name default]`, and a keyword may precede either. A rest parameter may follow a dot. If `formals` is a single name, that name is the rest parameter.
fn formals<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, formals: Stx) -> Result<Formals<'gc>, ExpandError> {
    let mut parsed = Formals { params: Vec::new(), names: Vec::new(), defaults: Vec::new(), rest: None };
    let items = match this.tree.view(formals)? {
        View::Id => {
            parsed.rest = Some(formals);
            return Ok(parsed);
        }
        View::List(items, tail) => {
            if let Some(tail) = tail {
                if !this.is_id(tail) {
                    return Err(this.error(ExpandErrorKind::BadSyntax, tail));
                }
                parsed.rest = Some(tail);
            }
            items
        }
        _ => return Err(this.error(ExpandErrorKind::BadSyntax, formals)),
    };
    let mut items = items.into_iter();
    while let Some(item) = items.next() {
        let keyword = this.tree.keyword(item);
        let at = if keyword.is_some() {
            items.next().ok_or_else(|| this.error(ExpandErrorKind::BadSyntax, item))?
        } else {
            item
        };
        let (name, default) = match this.tree.view(at)? {
            View::Id => (at, None),
            View::List(parts, None) => match *parts.as_slice() {
                // The reader turns `'a` into `(quote a)`, which is not a parameter named `quote`.
                [name, _] if this.is_id(name) && matches!(this.resolve(name)?, Binding::Core(_)) => return Err(this.error(ExpandErrorKind::BadSyntax, at)),
                [name, default] if this.is_id(name) => (name, Some(default)),
                [name, _] => return Err(this.error(ExpandErrorKind::BadSyntax, name)),
                _ => return Err(this.error(ExpandErrorKind::BadSyntax, at)),
            },
            _ => return Err(this.error(ExpandErrorKind::BadSyntax, at)),
        };
        if keyword.is_some() && parsed.params.iter().any(|param| param.keyword == keyword) {
            return Err(this.error(ExpandErrorKind::Duplicate, item));
        }
        // As in Racket, a required positional parameter can't follow an optional one.
        if keyword.is_none() && default.is_none() && parsed.params.iter().any(|param| param.keyword.is_none() && param.optional) {
            return Err(this.error(ExpandErrorKind::BadSyntax, at));
        }
        parsed.params.push(keyword::Param { keyword, optional: default.is_some() });
        parsed.names.push(name);
        parsed.defaults.push(default);
    }
    Ok(parsed)
}

/// Expands a `%lambda`.
fn lambda<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, written: Stx, body: Vec<Stx>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    if body.is_empty() {
        return Err(this.error(ExpandErrorKind::BadSyntax, stx));
    }
    let scope = this.tree.scopes.fresh()?;
    let written = this.tree.with(written, scope, Op::Add)?;
    let parsed = formals(this, written)?;
    let mut ids = parsed.names.clone();
    ids.extend(parsed.rest);
    this.distinct(&ids)?;
    let body = this.scoped(&body, scope)?;
    if parsed.params.iter().any(|param| param.keyword.is_some() || param.optional) {
        let params = Vec::with_capacity(parsed.names.len());
        return defaults(this, Optional { stx, formals: parsed, body, params, next: 0 });
    }
    let params = parsed.names.len();
    let vars = locals(this, &ids)?;
    sequence(this, body, Wrap::Lambda { stx, vars, params })
}

/// The state of expanding a `%lambda` that has optional or keyword parameters. `params` holds the parameters bound so far, and `next` is the index of the next parameter to bind.
struct Optional<'gc> {
    stx: Stx,
    formals: Formals<'gc>,
    body: Vec<Stx>,
    params: Vec<Formal<'gc>>,
    next: usize,
}

/// Binds the remaining parameters of an optional lambda, then expands the body. A default is expanded before its parameter is bound, so it can refer only to earlier parameters.
fn defaults<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, mut optional: Optional<'gc>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    while let Some(&name) = optional.formals.names.get(optional.next) {
        let (keyword, default) = (optional.formals.params[optional.next].keyword, optional.formals.defaults[optional.next]);
        optional.next += 1;
        let Some(default) = default else {
            let var = this.local(name)?;
            optional.params.push(Formal { var, keyword, default: None });
            continue;
        };
        return H::expr(default, move |this, default| {
            let var = this.local(name)?;
            optional.params.push(Formal { var, keyword, default: Some(default) });
            defaults(this, optional)
        });
    }
    let rest = match optional.formals.rest {
        Some(name) => Some(this.local(name)?),
        None => None,
    };
    sequence(this, optional.body, Wrap::OptionalLambda { stx: optional.stx, params: optional.params, rest })
}

/// Expands an `%app` of `callee` that has keyword arguments in `args` into a [`Core::KeywordApp`].
fn keyword_call<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, callee: Stx, args: Vec<Stx>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    let (mut kinds, mut values): (Vec<Option<Keyword<'gc>>>, Vec<Stx>) = (Vec::new(), Vec::new());
    let mut items = args.into_iter();
    while let Some(arg) = items.next() {
        let Some(keyword) = this.tree.keyword(arg) else {
            kinds.push(None);
            values.push(arg);
            continue;
        };
        let value = items.next().ok_or_else(|| this.error(ExpandErrorKind::BadSyntax, arg))?;
        if kinds.contains(&Some(keyword)) {
            return Err(this.error(ExpandErrorKind::Duplicate, arg));
        }
        kinds.push(Some(keyword));
        values.push(value);
    }
    H::expr(callee, move |_, callee| {
        H::exprs(values, move |this, values| {
            let args = kinds.into_iter().zip(values).map(|(keyword, value)| Arg { keyword, value }).collect();
            Ok(Step::Done(Core::KeywordApp(Box::new(callee), args, this.position(stx))))
        })
    })
}

/// Expands an `%intrinsic`, or an `%apply-intrinsic` if `spread` is true. The argument count of
/// an `%apply-intrinsic` is known only at run time, so it is not checked here.
fn intrinsic<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, name: Stx, args: Vec<Stx>, spread: bool) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    if !this.is_id(name) {
        return Err(this.error(ExpandErrorKind::BadSyntax, name));
    }
    let Some(prim) = this.primitive(name)? else { return Err(this.error(ExpandErrorKind::UnknownIntrinsic, name)) };
    if let Prim::Intrinsic(found) = prim
        && found.is_internal()
        && !this.internals
    {
        return Err(this.error(ExpandErrorKind::UnknownIntrinsic, name));
    }
    if spread {
        return H::exprs(args, move |this, args| Ok(Step::Done(Core::ApplyIntrinsic(prim, args, this.position(stx)))));
    }
    let takes = match prim {
        Prim::Intrinsic(intrinsic) => intrinsic.arity().is_none_or(|arity| usize::from(arity) == args.len()),
        Prim::Request(request) => request.takes(args.len()),
        Prim::Host(host) => host.takes(args.len()),
        Prim::Slot(op, _) => op.arity() == args.len(),
    };
    if !takes {
        return Err(this.error(ExpandErrorKind::Arity, stx));
    }
    H::exprs(args, move |this, args| Ok(Step::Done(Core::Intrinsic(prim, args, this.position(stx)))))
}

/// Expands a `%call-host` of the host function named `name`.
fn call_host<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, name: Stx, args: Vec<Stx>) -> Result<Ex<'a, 'gc, H>, ExpandError> {
    if !this.is_id(name) {
        return Err(this.error(ExpandErrorKind::BadSyntax, name));
    }
    let text = this.text(name).expect("an identifier");
    let hosts: &'static [HostDef] = this.module.hosts();
    let Some(def) = hosts.iter().find(|def| def.name == text) else { return Err(this.error(ExpandErrorKind::UnknownHost, name)) };
    if !def.takes(args.len()) {
        return Err(this.error(ExpandErrorKind::Arity, stx));
    }
    H::exprs(args, move |this, args| Ok(Step::Done(Core::Intrinsic(Prim::Host(def), args, this.position(stx)))))
}

/// Rewrites `(%syntax-rules (literal ...) ((keyword . pattern) template) ...)`, the form `stx`, to
/// `(%lambda (x) (%syntax-case x (literal ...) ((_ . pattern) (%syntax template)) ...))`. The keyword of a rule is not matched.
fn syntax_rules<'a, 'gc: 'a, H: Host<'a, 'gc>>(this: &mut H, stx: Stx, literals: Stx, rules: &[Stx]) -> Result<Stx, ExpandError> {
    let span = this.tree.span(stx);
    let input = this.core_id("x", stx)?;
    let mut clauses = Vec::with_capacity(rules.len());
    for &rule in rules {
        let &[pattern, template] = this.proper(rule)?.as_slice() else { return Err(this.error(ExpandErrorKind::BadSyntax, rule)) };
        let View::List(items, tail) = this.tree.view(pattern)? else { return Err(this.error(ExpandErrorKind::BadSyntax, pattern)) };
        if items.is_empty() {
            return Err(this.error(ExpandErrorKind::BadSyntax, pattern));
        }
        let any = this.core_id("_", pattern)?;
        let pattern_span = this.tree.span(pattern);
        let pattern = this.tree.list(&[&[any], &items[1..]].concat(), tail, pattern_span)?;
        let quote = this.core_id("%syntax", rule)?;
        let rule_span = this.tree.span(rule);
        let template = this.tree.list(&[quote, template], None, rule_span)?;
        clauses.push(this.tree.list(&[pattern, template], None, rule_span)?);
    }
    let case = this.core_id("%syntax-case", stx)?;
    let case = this.tree.list(&[&[case, input, literals], clauses.as_slice()].concat(), None, span)?;
    let formals = this.tree.list(&[input], None, span)?;
    let lambda = this.core_id("%lambda", stx)?;
    Ok(this.tree.list(&[lambda, formals, case], None, span)?)
}
