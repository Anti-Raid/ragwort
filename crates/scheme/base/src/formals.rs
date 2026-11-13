//! Formals with optional and keyword parameters, as Racket's `lambda` takes them, and calls with
//! keyword arguments, made as [`ragwort_compiler::keyword`] says.
//!
//! A positional parameter `[x default]`, or a keyword one `#:k [x default]`, is optional; `x` or
//! `#:k x` is required. Optional lambdas and keyword calls expand to [`Core::OptionalLambda`] and
//! [`Core::KeywordApp`], which the compiler lowers to keyword procedures and direct core calls.

use ragwort_compiler::keyword::{self, CallShape};
use ragwort_compiler::steps::Step;
use ragwort_compiler::{Arg, Core, Formal, OptionalLambda, Position};
use ragwort_types::symbol::Keyword;

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

impl<'gc> Formals<'gc> {
    pub(crate) fn has_keywords(&self) -> bool {
        self.params.iter().any(|param| param.keyword.is_some())
    }

    fn params(&self) -> Vec<keyword::Param<'gc>> {
        self.params.iter().map(|param| keyword::Param { keyword: param.keyword, optional: param.default.is_some() }).collect()
    }

    fn shape(&self, ex: &Expander<'_, 'gc>) -> CallShape<'gc> {
        CallShape::of(ex.mc, &self.params(), self.rest.is_some())
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
            if let Some(name) = keyword
                && params.iter().any(|param| param.keyword == Some(name))
            {
                return Err(self.error(ExpandErrorKind::Duplicate, item));
            }
            // As in Racket, a required positional parameter can't follow an optional one.
            if keyword.is_none() && default.is_none() && params.iter().any(|param| param.keyword.is_none() && param.default.is_some()) {
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

    /// Expands a lambda with optional or keyword parameters and passes the result to `then`. `formals` already has `scope` added, and `scope` is added to `body` too.
    ///
    /// Defaults are expanded in written order. Each default can refer only to earlier parameters.
    pub(crate) fn optional_lambda(
        &mut self,
        stx: Stx,
        formals: Formals<'gc>,
        body: Vec<Stx>,
        scope: Scope,
        then: impl FnOnce(&mut Self, OptionalLambda<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a,
    ) -> Result<Ex<'a, 'gc>, ExpandError> {
        let ids: Vec<Stx> = formals.params.iter().map(|param| param.id).chain(formals.rest).collect();
        self.distinct(&ids)?;
        let params = Vec::with_capacity(formals.params.len());
        let lambda = Optional { stx, left: formals.params.into_iter(), rest: formals.rest, body, scope, params };
        self.defaults(lambda, Box::new(then))
    }

    /// Binds the remaining parameters of an optional lambda, then expands the body. A default is expanded before its parameter is bound.
    fn defaults(&mut self, mut lambda: Optional<'gc>, then: Made<'a, 'gc>) -> Result<Ex<'a, 'gc>, ExpandError> {
        while let Some(param) = lambda.left.next() {
            let Some(default) = param.default else {
                let var = self.local(param.id)?;
                lambda.params.push(Formal { var, keyword: param.keyword, default: None });
                continue;
            };
            return Self::expr(default, move |this, default| {
                let var = this.local(param.id)?;
                lambda.params.push(Formal { var, keyword: param.keyword, default: Some(default) });
                this.defaults(lambda, then)
            });
        }
        let rest = lambda.rest.map(|id| self.local(id)).transpose()?;
        let body = self.scoped(&lambda.body, lambda.scope)?;
        Self::body_then(lambda.stx, body, move |this, body| {
            let at = Position::of(this.mc, this.tree.span(lambda.stx));
            let id = this.lambda_id();
            then(this, OptionalLambda { id, params: lambda.params, rest, body: Box::new(body), name: None, at })
        })
    }

    /// A `lambda` whose `formals` aren't plain.
    pub(crate) fn lambda_with(&mut self, stx: Stx, formals: Stx, body: Vec<Stx>, scope: Scope) -> Result<Ex<'a, 'gc>, ExpandError> {
        let formals = self.formals(formals)?;
        self.optional_lambda(stx, formals, body, scope, |_, lambda| Ok(Step::Done(Core::OptionalLambda(lambda))))
    }

    /// Whether any of a call's `args` is a keyword.
    pub(crate) fn has_keyword_args(&self, args: &[Stx]) -> bool {
        args.iter().any(|&arg| self.tree.keyword(arg).is_some())
    }

    /// Expands the call `stx` of `head` with arguments `args`, some of which have keywords, into a [`Core::KeywordApp`].
    pub(crate) fn keyword_call(&mut self, stx: Stx, head: Stx, args: Vec<Stx>) -> Result<Ex<'a, 'gc>, ExpandError> {
        let (mut keywords, mut values) = (Vec::with_capacity(args.len()), Vec::with_capacity(args.len()));
        let mut items = args.iter().copied();
        while let Some(arg) = items.next() {
            let Some(keyword) = self.tree.keyword(arg) else {
                keywords.push(None);
                values.push(arg);
                continue;
            };
            let value = items.next().ok_or_else(|| self.error(ExpandErrorKind::BadSyntax, arg))?;
            if keywords.contains(&Some(keyword)) {
                return Err(self.error(ExpandErrorKind::Duplicate, arg));
            }
            keywords.push(Some(keyword));
            values.push(value);
        }
        Self::expr(head, move |_, callee| {
            Self::exprs(values, move |this, values| {
                let args = keywords.into_iter().zip(values).map(|(keyword, value)| Arg { keyword, value }).collect();
                Ok(Step::Done(Core::KeywordApp(Box::new(callee), args, this.position(stx))))
            })
        })
    }
}

/// The state of expanding a lambda with optional or keyword parameters: the parameters still to bind, and the parameters bound so far.
struct Optional<'gc> {
    stx: Stx,
    left: std::vec::IntoIter<Param<'gc>>,
    rest: Option<Stx>,
    body: Vec<Stx>,
    scope: Scope,
    params: Vec<Formal<'gc>>,
}

/// The continuation that receives the expanded optional lambda.
type Made<'a, 'gc> = Box<dyn FnOnce(&mut Expander<'a, 'gc>, OptionalLambda<'gc>) -> Result<Ex<'a, 'gc>, ExpandError> + 'a>;

