//! Describes the shape of a procedure with optional and keyword parameters: the order in which
//! its core takes them, and the calls it accepts. The compiler's first pass builds keyword
//! procedures and keyword calls from these shapes. Parameter behavior follows Racket's `lambda`.
//!
//! The VM binds omitted optional positional arguments to `#<unsupplied>`; generated code evaluates
//! their defaults. A keyword procedure has a core procedure that receives keyword values sorted by
//! name, followed by positional arguments, and a plain procedure for calls without keywords. See
//! [`ragwort_vm::keyword`].
//!
//! Keyword calls use `keyword-apply` unless the caller knows the keyword procedure's core and can
//! call it directly.

use ragwort_types::gc::Mutation;
use ragwort_types::symbol::Keyword;
use ragwort_vm::keyword;

use crate::module::Import;
use crate::Core;

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

}

/// Returns indices into `params` in calling order: sorted keyword parameters followed by positional
/// parameters.
pub fn order<'gc>(mc: &Mutation<'gc>, params: &[Param<'gc>]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..params.len()).filter(|&i| params[i].keyword.is_some()).collect();
    order.sort_by(|&a, &b| keyword::order(mc, params[a].keyword.expect("a keyword"), params[b].keyword.expect("a keyword")));
    order.extend((0..params.len()).filter(|&i| params[i].keyword.is_none()));
    order
}

/// Sorts keywords into the order required by keyword procedures.
pub fn sort<'gc>(mc: &Mutation<'gc>, keywords: &mut [Keyword<'gc>]) {
    keywords.sort_by(|&a, &b| keyword::order(mc, a, b));
}
