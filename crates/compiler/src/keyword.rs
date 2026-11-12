//! Lowers optional parameters, keyword parameters, and keyword calls into core forms for use by
//! front ends. Parameter behavior follows Racket's `lambda`.
//!
//! The VM binds omitted optional positional arguments to `#<unsupplied>`; generated code evaluates
//! their defaults. A keyword procedure has a core procedure that receives keyword values sorted by
//! name, followed by positional arguments, and a plain procedure for calls without keywords. See
//! [`ragwort_vm::keyword`].
//!
//! Keyword calls use `keyword-apply` unless the caller knows the keyword procedure's core and can
//! call it directly.

use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Keyword;
use ragwort_vm::{Intrinsic, Request, keyword};

use crate::module::Import;
use crate::{Core, Lambda, Place, Prim, Var};

/// Supplies fresh local-variable and lambda IDs to a front end.
pub trait Fresh {
    fn var(&mut self) -> Var;
    fn lambda(&mut self) -> u32;
}

/// Parameter metadata: its keyword, if any, and whether it has a default.
#[derive(Clone, Copy)]
pub struct Param<'gc> {
    pub keyword: Option<Keyword<'gc>>,
    pub optional: bool,
}

/// A keyword procedure's accepted arguments: sorted keywords with required flags, plus its
/// positional arity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallShape<'gc> {
    pub keywords: Vec<(Keyword<'gc>, bool)>,
    pub required: usize,
    pub optional: usize,
    pub rest: bool,
}

impl<'gc> CallShape<'gc> {
    /// Computes the argument shape of `params`, including a rest parameter when `rest` is true.
    pub fn of(mc: &Mutation<'gc>, params: &[Param<'gc>], rest: bool) -> Self {
        let mut keywords: Vec<_> = params.iter().filter_map(|p| Some((p.keyword?, !p.optional))).collect();
        keywords.sort_by(|a, b| keyword::order(mc, a.0, b.0));
        let positional = || params.iter().filter(|p| p.keyword.is_none());
        CallShape { keywords, required: positional().filter(|p| !p.optional).count(), optional: positional().filter(|p| p.optional).count(), rest }
    }

    /// Returns the imported keyword procedure's shape and core import, if the exporting module exposes
    /// them.
    pub fn of_import(mc: &Mutation<'gc>, import: Import<'gc>) -> Option<(Import<'gc>, Self)> {
        let core = import.keyword_core()?;
        let Ok(Core::Quote(f)) = import.reference(mc) else { return None };
        let (keywords, shape) = keyword::signature(mc, f)?;
        let (required, optional) = (usize::try_from(shape.required).ok()?, usize::try_from(shape.optional).ok()?);
        Some((core, CallShape { keywords, required, optional, rest: shape.rest }))
    }

    /// Checks whether the procedure accepts sorted keywords `given` and `positional` positional
    /// arguments.
    pub fn matches(&self, given: &[Keyword<'gc>], positional: usize) -> bool {
        let takes = positional >= self.required && (self.rest || positional <= self.required + self.optional);
        let known = given.iter().all(|k| self.keywords.iter().any(|&(other, _)| other == *k));
        let required = self.keywords.iter().filter(|&&(_, r)| r).all(|(k, _)| given.contains(k));
        takes && known && required
    }

    /// Builds arguments for a direct core call: sorted keyword values, using `#<unsupplied>` when
    /// `value_of` returns none, followed by positional arguments.
    pub fn core_args(&self, value_of: impl Fn(Keyword<'gc>) -> Option<Core<'gc>>, positional: Vec<Core<'gc>>) -> Vec<Core<'gc>> {
        let mut args: Vec<Core<'gc>> = self.keywords.iter().map(|&(k, _)| value_of(k).unwrap_or(Core::Quote(Value::UNSUPPLIED))).collect();
        args.extend(positional);
        args
    }
}

/// Returns indices into `params` in calling order: sorted keyword parameters followed by positional
/// parameters.
pub fn order<'gc>(mc: &Mutation<'gc>, params: &[Param<'gc>]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..params.len()).filter(|&i| params[i].keyword.is_some()).collect();
    order.sort_by(|&a, &b| keyword::order(mc, params[a].keyword.expect("a keyword"), params[b].keyword.expect("a keyword")));
    order.extend((0..params.len()).filter(|&i| params[i].keyword.is_none()));
    order
}

/// Binds `var` to `raw`, or evaluates `default` when the argument was omitted.
pub fn defaulted<'gc>(var: Var, raw: Var, default: Core<'gc>) -> (Var, Core<'gc>) {
    let missing = Core::Intrinsic(Prim::Intrinsic(Intrinsic::Eq), vec![Core::Ref(Place::Local(raw)), Core::Quote(Value::UNSUPPLIED)]);
    (var, Core::If(Box::new(missing), Box::new(default), Box::new(Core::Ref(Place::Local(raw)))))
}

/// Builds a keyword procedure from `core` and `shape`, using `fresh` for generated IDs.
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
        Core::Lambda(Lambda { id: fresh.lambda(), optional, params, rest, body: Box::new(body), name: None, at: None })
    };
    let pairs = Pairs::new(mc);
    let all: Vec<Value<'gc>> = shape.keywords.iter().map(|&(k, _)| k.value(mc)).collect();
    let required: Vec<Value<'gc>> = shape.keywords.iter().filter(|&&(_, r)| r).map(|&(k, _)| k.value(mc)).collect();
    let (all, required) = (Core::Quote(pairs.list(&all)?), Core::Quote(pairs.list(&required)?));
    Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeKeywordProcedure), vec![plain, core, all, required]))
}

/// Builds a `keyword-apply` call to `f` with sorted keyword/value pairs `given` and the positional
/// arguments.
pub fn apply<'gc>(mc: &Mutation<'gc>, f: Core<'gc>, given: Vec<(Keyword<'gc>, Core<'gc>)>, positional: Vec<Core<'gc>>) -> Result<Core<'gc>, OutOfMemory> {
    let kws: Vec<Value<'gc>> = given.iter().map(|(k, _)| k.value(mc)).collect();
    let cons = |item, rest| Core::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, rest]);
    let vals = given.into_iter().rev().fold(Core::Quote(Value::NIL), |rest, (_, value)| cons(value, rest));
    let mut args = vec![f, Core::Quote(Pairs::new(mc).list(&kws)?), vals];
    args.extend(positional);
    args.push(Core::Quote(Value::NIL));
    Ok(Core::Intrinsic(Prim::Request(Request::KeywordApply), args))
}

/// Sorts keywords into the order required by keyword procedures.
pub fn sort<'gc>(mc: &Mutation<'gc>, keywords: &mut [Keyword<'gc>]) {
    keywords.sort_by(|&a, &b| keyword::order(mc, a, b));
}
