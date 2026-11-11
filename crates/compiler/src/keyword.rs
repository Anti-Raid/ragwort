//! Optional and keyword parameters, and calls with keyword arguments, as core forms, for any
//! front end, as Racket's `lambda` takes them.
//!
//! An optional positional parameter is optional to the VM too, which binds it to
//! `#<unsupplied>` when a call leaves it out, and the code puts the default in its place. A
//! procedure with keyword parameters is a keyword procedure (see [`ragwort_vm::keyword`]): a
//! core, which takes each keyword's value, sorted by name, then the positional arguments, and a
//! plain procedure for calls without keywords. A call with keywords goes through `keyword-apply`,
//! unless what it calls is a keyword procedure whose core the caller knows, which it calls
//! itself.

use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Keyword;
use ragwort_vm::{Intrinsic, Request, keyword};

use crate::module::Import;
use crate::{Core, Lambda, Place, Prim, Var};

/// Where a front end gets new locals and lambda numbers from.
pub trait Fresh {
    fn var(&mut self) -> Var;
    fn lambda(&mut self) -> u32;
}

/// A parameter, as formals have it: its keyword, if it's a keyword parameter, and whether it has
/// a default.
#[derive(Clone, Copy)]
pub struct Param<'gc> {
    pub keyword: Option<Keyword<'gc>>,
    pub optional: bool,
}

/// What a call of a keyword procedure has to match: its keywords, sorted, each with whether it's
/// required, and how many positional arguments it takes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallShape<'gc> {
    pub keywords: Vec<(Keyword<'gc>, bool)>,
    pub required: usize,
    pub optional: usize,
    pub rest: bool,
}

impl<'gc> CallShape<'gc> {
    /// The shape of formals with `params`, and a rest parameter if `rest`.
    pub fn of(mc: &Mutation<'gc>, params: &[Param<'gc>], rest: bool) -> Self {
        let mut keywords: Vec<_> = params.iter().filter_map(|p| Some((p.keyword?, !p.optional))).collect();
        keywords.sort_by(|a, b| keyword::order(mc, a.0, b.0));
        let positional = || params.iter().filter(|p| p.keyword.is_none());
        CallShape { keywords, required: positional().filter(|p| !p.optional).count(), optional: positional().filter(|p| p.optional).count(), rest }
    }

    /// The shape of the keyword procedure `import` refers to, and the import of its core, if its
    /// module exports that.
    pub fn of_import(mc: &Mutation<'gc>, import: Import<'gc>) -> Option<(Import<'gc>, Self)> {
        let core = import.keyword_core()?;
        let Ok(Core::Quote(f)) = import.reference(mc) else { return None };
        let (keywords, shape) = keyword::signature(mc, f)?;
        let (required, optional) = (usize::try_from(shape.required).ok()?, usize::try_from(shape.optional).ok()?);
        Some((core, CallShape { keywords, required, optional, rest: shape.rest }))
    }

    /// Whether a call with the keywords `given`, sorted, and `positional` other arguments is one
    /// the procedure takes.
    pub fn matches(&self, given: &[Keyword<'gc>], positional: usize) -> bool {
        let takes = positional >= self.required && (self.rest || positional <= self.required + self.optional);
        let known = given.iter().all(|k| self.keywords.iter().any(|&(other, _)| other == *k));
        let required = self.keywords.iter().filter(|&&(_, r)| r).all(|(k, _)| given.contains(k));
        takes && known && required
    }

    /// The arguments of a direct call of the core: each keyword's value, or `#<unsupplied>` where
    /// `value_of` has none, then the `positional` ones.
    pub fn core_args(&self, value_of: impl Fn(Keyword<'gc>) -> Option<Core<'gc>>, positional: Vec<Core<'gc>>) -> Vec<Core<'gc>> {
        let mut args: Vec<Core<'gc>> = self.keywords.iter().map(|&(k, _)| value_of(k).unwrap_or(Core::Quote(Value::UNSUPPLIED))).collect();
        args.extend(positional);
        args
    }
}

/// The order a lambda with `params` takes them in: the keyword ones, sorted, then the positional
/// ones, as indexes into `params`.
pub fn order<'gc>(mc: &Mutation<'gc>, params: &[Param<'gc>]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..params.len()).filter(|&i| params[i].keyword.is_some()).collect();
    order.sort_by(|&a, &b| keyword::order(mc, params[a].keyword.expect("a keyword"), params[b].keyword.expect("a keyword")));
    order.extend((0..params.len()).filter(|&i| params[i].keyword.is_none()));
    order
}

/// `var` bound to the parameter `raw`, or to `default` if the call left it out.
pub fn defaulted<'gc>(var: Var, raw: Var, default: Core<'gc>) -> (Var, Core<'gc>) {
    let missing = Core::Intrinsic(Prim::Intrinsic(Intrinsic::Eq), vec![Core::Ref(Place::Local(raw)), Core::Quote(Value::UNSUPPLIED)]);
    (var, Core::If(Box::new(missing), Box::new(default), Box::new(Core::Ref(Place::Local(raw)))))
}

/// The keyword procedure of `core`, whose shape is `shape`, with what it needs that's new from
/// `fresh`.
pub fn procedure<'gc>(mc: &Mutation<'gc>, shape: &CallShape<'gc>, core: Core<'gc>, fresh: &mut impl Fresh) -> Result<Core<'gc>, OutOfMemory> {
    let plain = if shape.keywords.iter().any(|&(_, required)| required) {
        Core::Quote(Value::FALSE)
    } else {
        let params: Vec<Var> = (0..shape.required + shape.optional).map(|_| fresh.var()).collect();
        let rest = shape.rest.then(|| fresh.var());
        let unsupplied = std::iter::repeat_n(Core::Quote(Value::UNSUPPLIED), shape.keywords.len());
        let passed = unsupplied.chain(params.iter().map(|&v| Core::Ref(Place::Local(v))));
        let body = match rest {
            None => Core::App(Box::new(core.clone()), passed.collect()),
            Some(rest) => {
                let args = std::iter::once(core.clone()).chain(passed).chain([Core::Ref(Place::Local(rest))]).collect();
                Core::Intrinsic(Prim::Request(Request::Apply), args)
            }
        };
        let optional = u32::try_from(shape.optional).map_err(|_| OutOfMemory)?;
        Core::Lambda(Lambda { id: fresh.lambda(), optional, params, rest, body: Box::new(body) })
    };
    let pairs = Pairs::new(mc);
    let all: Vec<Value<'gc>> = shape.keywords.iter().map(|&(k, _)| k.value(mc)).collect();
    let required: Vec<Value<'gc>> = shape.keywords.iter().filter(|&&(_, r)| r).map(|&(k, _)| k.value(mc)).collect();
    let (all, required) = (Core::Quote(pairs.list(&all)?), Core::Quote(pairs.list(&required)?));
    Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeKeywordProcedure), vec![plain, core, all, required]))
}

/// A call of `f` through `keyword-apply`, with the keywords `given`, sorted, each with its value,
/// and the `positional` arguments.
pub fn apply<'gc>(mc: &Mutation<'gc>, f: Core<'gc>, given: Vec<(Keyword<'gc>, Core<'gc>)>, positional: Vec<Core<'gc>>) -> Result<Core<'gc>, OutOfMemory> {
    let kws: Vec<Value<'gc>> = given.iter().map(|(k, _)| k.value(mc)).collect();
    let cons = |item, rest| Core::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, rest]);
    let vals = given.into_iter().rev().fold(Core::Quote(Value::NIL), |rest, (_, value)| cons(value, rest));
    let mut args = vec![f, Core::Quote(Pairs::new(mc).list(&kws)?), vals];
    args.extend(positional);
    args.push(Core::Quote(Value::NIL));
    Ok(Core::Intrinsic(Prim::Request(Request::KeywordApply), args))
}

/// Sorts `keywords` as keyword procedures take them.
pub fn sort<'gc>(mc: &Mutation<'gc>, keywords: &mut [Keyword<'gc>]) {
    keywords.sort_by(|&a, &b| keyword::order(mc, a, b));
}
