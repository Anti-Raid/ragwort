//! Formals with optional and keyword parameters, as Racket's `lambda` takes them, and calls with
//! keyword arguments.
//!
//! A positional parameter `[x default]`, or a keyword one `#:k [x default]`, is optional; `x` or
//! `#:k x` is required. Optional positional ones are optional to the VM too, which binds them to
//! `#<unsupplied>` when a call leaves them out, and the code puts the default in its place. A
//! `lambda` with keyword parameters makes a keyword procedure (see [`ragwort_vm::keyword`]): a
//! core, which takes each keyword's value, sorted by name, then the positional arguments, and a
//! plain procedure for calls without keywords. A call with keywords goes through `keyword-apply`,
//! unless what it calls is a keyword procedure a definition made, here or in a module this one
//! requires, which it calls the core of itself, as Racket does.

use ragwort_compiler::module::{Import, Uninitialized};
use ragwort_compiler::steps::Step;
use ragwort_compiler::{Core, Lambda, Place, Prim, Var};
use ragwort_types::gc::Value;
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Keyword;
use ragwort_vm::{Intrinsic, Request, keyword};

use crate::expand::{Binding, Ex, Expander};
use crate::scope::Scope;
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A parameter, in the order its formals have it.
struct Param<'gc> {
    keyword: Option<Keyword<'gc>>,
    id: Stx,
    default: Option<Stx>,
}

/// Formals that take more than plain positional parameters.
pub(crate) struct Formals<'gc> {
    params: Vec<Param<'gc>>,
    rest: Option<Stx>,
}

/// What a call of a keyword procedure has to match: its keywords, sorted, each with whether it's
/// required, and how many positional arguments it takes.
#[derive(Clone)]
pub(crate) struct CallShape<'gc> {
    keywords: Vec<(Keyword<'gc>, bool)>,
    required: usize,
    optional: usize,
    rest: bool,
}

/// A variable a definition of a keyword procedure binds.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Def {
    Local(Var),
    Slot(u32),
}

/// Where a keyword procedure's core is: in a variable of this load's, or another module's.
#[derive(Clone, Copy)]
pub(crate) enum CoreAt<'gc> {
    Local(Var),
    Slot(u32),
    Import(Import<'gc>),
}

/// What a definition of a keyword procedure tells calls of it: where its core is.
#[derive(Clone)]
pub(crate) struct KeywordDef<'gc> {
    pub(crate) core: CoreAt<'gc>,
    pub(crate) shape: CallShape<'gc>,
}

/// A call's arguments: the positional ones, and the keyword ones, in the order they're written.
enum Arg<'gc> {
    Positional(Stx),
    Keyword(Keyword<'gc>, Stx),
}

impl<'gc> Formals<'gc> {
    pub(crate) fn has_keywords(&self) -> bool {
        self.params.iter().any(|p| p.keyword.is_some())
    }

    fn shape(&self, ex: &Expander<'_, 'gc>) -> CallShape<'gc> {
        let mut keywords: Vec<_> = self.params.iter().filter_map(|p| Some((p.keyword?, p.default.is_none()))).collect();
        keywords.sort_by(|a, b| keyword::order(ex.mc, a.0, b.0));
        let positional = || self.params.iter().filter(|p| p.keyword.is_none());
        CallShape {
            keywords,
            required: positional().filter(|p| p.default.is_none()).count(),
            optional: positional().filter(|p| p.default.is_some()).count(),
            rest: self.rest.is_some(),
        }
    }
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// Whether `formals` are plain: identifiers, or a list of them with one as its tail.
    pub(crate) fn plain_formals(&mut self, formals: Stx) -> Result<bool, ExpandError> {
        Ok(match self.tree.view(formals)? {
            View::Id => true,
            View::List(ids, rest) => ids.iter().chain(&rest).all(|&id| self.is_id(id)),
            _ => false,
        })
    }

    /// `formals` with optional or keyword parameters.
    pub(crate) fn formals(&mut self, formals: Stx) -> Result<Formals<'gc>, ExpandError> {
        let View::List(items, rest) = self.tree.view(formals)? else { return Err(self.error(ExpandErrorKind::BadSyntax, formals)) };
        let mut params: Vec<Param<'gc>> = Vec::new();
        let mut items = items.into_iter();
        while let Some(item) = items.next() {
            let keyword = self.tree.keyword(item);
            let at = match keyword {
                Some(_) => items.next().ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, item))?,
                None => item,
            };
            let (id, default) = match self.tree.view(at)? {
                View::Id => (at, None),
                View::List(parts, None) if matches!(*parts, [id, _] if self.is_id(id)) => (parts[0], Some(parts[1])),
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, at)),
            };
            if let Some(k) = keyword
                && params.iter().any(|p| p.keyword == Some(k))
            {
                return Err(self.error(ExpandErrorKind::Duplicate, item));
            }
            // As in Racket, a required positional parameter can't follow an optional one.
            if keyword.is_none() && default.is_none() && params.iter().any(|p| p.keyword.is_none() && p.default.is_some()) {
                return Err(self.error(ExpandErrorKind::BadSyntax, at));
            }
            params.push(Param { keyword, id, default });
        }
        if let Some(rest) = rest
            && !self.is_id(rest)
        {
            return Err(self.error(ExpandErrorKind::BadSyntax, rest));
        }
        Ok(Formals { params, rest })
    }

    /// The keyword procedure's shape, if `value` is a `lambda` with keyword parameters.
    pub(crate) fn keyword_lambda(&mut self, value: Stx) -> Result<Option<CallShape<'gc>>, ExpandError> {
        let View::List(items, None) = self.tree.view(value)? else { return Ok(None) };
        let [head, formals, _, ..] = items[..] else { return Ok(None) };
        if !self.is_id(head) || !matches!(self.resolve(head)?, Binding::Keyword(crate::expand::Keyword::Form(crate::expand::Form::Lambda))) {
            return Ok(None);
        }
        if self.plain_formals(formals)? {
            return Ok(None);
        }
        let formals = self.formals(formals)?;
        Ok(formals.has_keywords().then(|| formals.shape(self)))
    }

    /// The procedure `formals` and `body` make, which `formals`, scoped with `scope`, take, and
    /// its shape, to `then`. Its optional parameters' defaults are worked out in order, each
    /// seeing the parameters before it. With keyword parameters it's the core of a keyword
    /// procedure, which takes the keywords' values first, sorted.
    pub(crate) fn optional_lambda(
        &mut self,
        stx: Stx,
        formals: Formals<'gc>,
        body: Vec<Stx>,
        scope: Scope,
        then: impl FnOnce(&mut Self, Lambda<'gc>, CallShape<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a,
    ) -> Result<Ex<'a, 'gc>, ExpandError> {
        let ids: Vec<Stx> = formals.params.iter().map(|p| p.id).chain(formals.rest).collect();
        self.distinct(&ids)?;
        let shape = formals.shape(self);
        let raws: Vec<Var> = formals.params.iter().map(|_| self.fresh()).collect();
        let mut order: Vec<usize> = (0..raws.len()).filter(|&i| formals.params[i].keyword.is_some()).collect();
        let mc = self.mc;
        order.sort_by(|&a, &b| keyword::order(mc, formals.params[a].keyword.expect("a keyword"), formals.params[b].keyword.expect("a keyword")));
        order.extend((0..raws.len()).filter(|&i| formals.params[i].keyword.is_none()));
        let lambda = Optional { stx, formals, body, scope, shape, raws, order, inits: Vec::new(), next: 0 };
        self.defaults(lambda, Box::new(then))
    }

    /// Binds the rest of an optional lambda's parameters, each with a default after what that
    /// expands to, then expands its body.
    fn defaults(&mut self, mut f: Optional<'gc>, then: Made<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> {
        while let Some(param) = f.formals.params.get(f.next) {
            let raw = f.raws[f.next];
            f.next += 1;
            let Some(default) = param.default else {
                self.bind(param.id, Binding::Local(raw))?;
                continue;
            };
            let id = param.id;
            return Self::expr(default, move |this, default| {
                let var = this.local(id)?;
                let missing = Core::Intrinsic(Prim::Intrinsic(Intrinsic::Eq), vec![Core::Ref(Place::Local(raw)), Core::Quote(Value::UNSUPPLIED)]);
                f.inits.push((var, Core::If(Box::new(missing), Box::new(default), Box::new(Core::Ref(Place::Local(raw))))));
                this.defaults(f, then)
            });
        }
        let rest = f.formals.rest.map(|id| self.local(id)).transpose()?;
        let body = self.scoped(&f.body, f.scope)?;
        Self::body_then(f.stx, body, move |this, mut body| {
            for bind in f.inits.into_iter().rev() {
                body = Core::Let(vec![bind], Box::new(body));
            }
            let params = f.order.into_iter().map(|i| f.raws[i]).collect();
            let optional = u32::try_from(f.shape.optional).map_err(|_| this.error(ExpandErrorKind::BadSyntax, f.stx))?;
            let lambda = Lambda { id: this.lambda_id(), optional, params, rest, body: Box::new(body) };
            then(this, lambda, f.shape)
        })
    }

    /// The keyword procedure of `core`, whose shape is `shape`.
    pub(crate) fn keyword_procedure(&mut self, shape: &CallShape<'gc>, core: Core<'gc>) -> Result<Core<'gc>, ExpandError> {
        let plain = if shape.keywords.iter().any(|&(_, required)| required) {
            Core::Quote(Value::FALSE)
        } else {
            let params: Vec<Var> = (0..shape.required + shape.optional).map(|_| self.fresh()).collect();
            let rest = shape.rest.then(|| self.fresh());
            let unsupplied = std::iter::repeat_n(Core::Quote(Value::UNSUPPLIED), shape.keywords.len());
            let passed = unsupplied.chain(params.iter().map(|&v| Core::Ref(Place::Local(v))));
            let body = match rest {
                None => Core::App(Box::new(core.clone()), passed.collect()),
                Some(rest) => {
                    let args = std::iter::once(core.clone()).chain(passed).chain([Core::Ref(Place::Local(rest))]).collect();
                    Core::Intrinsic(Prim::Request(Request::Apply), args)
                }
            };
            let optional = shape.optional as u32;
            Core::Lambda(Lambda { id: self.lambda_id(), optional, params, rest, body: Box::new(body) })
        };
        let pairs = Pairs::new(self.mc);
        let all: Vec<Value<'gc>> = shape.keywords.iter().map(|&(k, _)| k.value(self.mc)).collect();
        let required: Vec<Value<'gc>> = shape.keywords.iter().filter(|&&(_, r)| r).map(|&(k, _)| k.value(self.mc)).collect();
        let (all, required) = (Core::Quote(pairs.list(&all)?), Core::Quote(pairs.list(&required)?));
        Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeKeywordProcedure), vec![plain, core, all, required]))
    }

    /// A `lambda` whose `formals` aren't plain.
    pub(crate) fn lambda_with(&mut self, stx: Stx, formals: Stx, body: Vec<Stx>, scope: Scope) -> Result<Ex<'a, 'gc>, ExpandError> {
        let formals = self.formals(formals)?;
        let keywords = formals.has_keywords();
        self.optional_lambda(stx, formals, body, scope, move |this, lambda, shape| {
            if !keywords {
                return Ok(Step::Done(Core::Lambda(lambda)));
            }
            let core = this.fresh();
            let procedure = this.keyword_procedure(&shape, Core::Ref(Place::Local(core)))?;
            Ok(Step::Done(Core::Let(vec![(core, Core::Lambda(lambda))], Box::new(procedure))))
        })
    }

    /// Whether any of a call's `args` is a keyword.
    pub(crate) fn has_keyword_args(&self, args: &[Stx]) -> bool {
        args.iter().any(|&arg| self.tree.keyword(arg).is_some())
    }

    /// A call of `head` on `args`, which has keyword arguments, or calls a keyword procedure
    /// `def` says a definition made.
    pub(crate) fn keyword_call(&mut self, head: Stx, args: Vec<Stx>, def: Option<KeywordDef<'gc>>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let mut parsed = Vec::with_capacity(args.len());
        let mut items = args.iter().copied();
        while let Some(arg) = items.next() {
            let Some(k) = self.tree.keyword(arg) else {
                parsed.push(Arg::Positional(arg));
                continue;
            };
            let value = items.next().ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, arg))?;
            if parsed.iter().any(|a| matches!(*a, Arg::Keyword(other, _) if other == k)) {
                return Err(self.error(ExpandErrorKind::Duplicate, arg));
            }
            parsed.push(Arg::Keyword(k, value));
        }
        let mut given: Vec<Keyword<'gc>> = parsed.iter().filter_map(|a| if let Arg::Keyword(k, _) = *a { Some(k) } else { None }).collect();
        let mc = self.mc;
        given.sort_by(|&a, &b| keyword::order(mc, a, b));
        let positional = parsed.iter().filter(|a| matches!(a, Arg::Positional(_))).count();
        // The arguments, in the order they're written, each in a local, and the procedure first
        // unless it's called directly.
        let direct = def.filter(|def| def.shape.matches(&given, positional));
        let call = KeywordCall { head, given, direct, binds: Vec::with_capacity(parsed.len() + 1), f: None, keyword_vars: Vec::new(), positional_vars: Vec::new() };
        let parsed = parsed.into_iter();
        if call.direct.is_some() {
            return self.keyword_args(call, parsed);
        }
        Self::expr(head, move |this, f| {
            let mut call = call;
            let var = this.fresh();
            call.binds.push((var, f));
            call.f = Some(var);
            this.keyword_args(call, parsed)
        })
    }

    /// Expands the rest of a keyword call's arguments, `args`, each into a local, then makes
    /// the call.
    fn keyword_args(&mut self, mut call: KeywordCall<'gc>, mut args: std::vec::IntoIter<Arg<'gc>>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some(arg) = args.next() else { return self.keyword_called(call).map(Step::Done) };
        let (stx, k) = match arg {
            Arg::Positional(stx) => (stx, None),
            Arg::Keyword(k, stx) => (stx, Some(k)),
        };
        Self::expr(stx, move |this, value| {
            let var = this.fresh();
            call.binds.push((var, value));
            match k {
                Some(k) => call.keyword_vars.push((k, var)),
                None => call.positional_vars.push(var),
            }
            this.keyword_args(call, args)
        })
    }

    /// A keyword call whose arguments are all expanded.
    fn keyword_called(&mut self, call: KeywordCall<'gc>) -> Result<Core<'gc>, ExpandError> {
        let KeywordCall { head, given, direct, binds, f, keyword_vars, positional_vars } = call;
        let refs = |vars: &[Var]| vars.iter().map(|&v| Core::Ref(Place::Local(v))).collect::<Vec<_>>();
        let value_of = |k: Keyword<'gc>| keyword_vars.iter().find(|&&(other, _)| other == k).map(|&(_, v)| Core::Ref(Place::Local(v)));
        let call = match (direct, f) {
            (Some(def), _) => {
                let mut args: Vec<Core<'gc>> = def.shape.keywords.iter().map(|&(k, _)| value_of(k).unwrap_or(Core::Quote(Value::UNSUPPLIED))).collect();
                args.extend(refs(&positional_vars));
                let core = match def.core {
                    CoreAt::Local(var) => Place::Local(var),
                    CoreAt::Slot(slot) => self.builder.place(slot, self.form, self.defining),
                    CoreAt::Import(import) => {
                        let mc = self.mc;
                        let call = import.call(mc, args, &mut || self.fresh()).map_err(|Uninitialized| self.error(ExpandErrorKind::Unbound, head))?;
                        return Ok(if binds.is_empty() { call } else { Core::Let(binds, Box::new(call)) });
                    }
                };
                Core::App(Box::new(Core::Ref(core)), args)
            }
            (None, Some(f)) => {
                let pairs = Pairs::new(self.mc);
                let kws: Vec<Value<'gc>> = given.iter().map(|k| k.value(self.mc)).collect();
                let cons = |item, rest| Core::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, rest]);
                let vals = given.iter().rev().fold(Core::Quote(Value::NIL), |rest, &k| cons(value_of(k).expect("a keyword given"), rest));
                let mut args = vec![Core::Ref(Place::Local(f)), Core::Quote(pairs.list(&kws)?), vals];
                args.extend(refs(&positional_vars));
                args.push(Core::Quote(Value::NIL));
                Core::Intrinsic(Prim::Request(Request::KeywordApply), args)
            }
            (None, None) => unreachable!("an indirect call has its procedure"),
        };
        Ok(if binds.is_empty() { call } else { Core::Let(binds, Box::new(call)) })
    }
}

/// A lambda with optional or keyword parameters being expanded: its parameters' variables, as
/// its formals have them, in the order it takes them, and the defaults so far, each binding the
/// parameter it's for, `next` the parameter after them.
struct Optional<'gc> {
    stx: Stx,
    formals: Formals<'gc>,
    body: Vec<Stx>,
    scope: Scope,
    shape: CallShape<'gc>,
    raws: Vec<Var>,
    order: Vec<usize>,
    inits: Vec<(Var, Core<'gc>)>,
    next: usize,
}

/// What goes on with an optional lambda once it's made.
type Made<'a, 'gc> = Box<dyn FnOnce(&mut Expander<'a, 'gc>, Lambda<'gc>, CallShape<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a>;

/// A keyword call being expanded: what it calls, the keywords it gives, sorted, the definition
/// it calls the core of directly, if any, and the arguments so far, each bound to a local, the
/// procedure's first if it isn't called directly.
struct KeywordCall<'gc> {
    head: Stx,
    given: Vec<Keyword<'gc>>,
    direct: Option<KeywordDef<'gc>>,
    binds: Vec<(Var, Core<'gc>)>,
    f: Option<Var>,
    keyword_vars: Vec<(Keyword<'gc>, Var)>,
    positional_vars: Vec<Var>,
}

impl<'gc> Expander<'_, 'gc> {
    /// What `import` tells calls of it, if it's a keyword procedure whose core its module exports.
    pub(crate) fn imported_keyword_def(&self, import: Import<'gc>) -> Option<KeywordDef<'gc>> {
        let core = import.keyword_core()?;
        let Ok(Core::Quote(f)) = import.reference(self.mc) else { return None };
        let (keywords, shape) = keyword::signature(self.mc, f)?;
        let (required, optional) = (usize::try_from(shape.required).ok()?, usize::try_from(shape.optional).ok()?);
        Some(KeywordDef { core: CoreAt::Import(core), shape: CallShape { keywords, required, optional, rest: shape.rest } })
    }
}

impl<'gc> CallShape<'gc> {
    /// Whether a call with the keywords `given`, sorted, and `positional` other arguments is one
    /// the procedure takes.
    fn matches(&self, given: &[Keyword<'gc>], positional: usize) -> bool {
        let takes = positional >= self.required && (self.rest || positional <= self.required + self.optional);
        let known = given.iter().all(|k| self.keywords.iter().any(|&(other, _)| other == *k));
        let required = self.keywords.iter().filter(|&&(_, r)| r).all(|(k, _)| given.contains(k));
        takes && known && required
    }
}
