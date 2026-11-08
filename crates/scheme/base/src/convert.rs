//! Syntax between the expander's tree and the arena's syntax objects, which macros' transformers
//! take and make. An identifier's object holds its scopes, and a list's a list of syntax. Each
//! object made from the tree goes back to the node it came from, so the parts of a use that a
//! transformer hands back as they were cost nothing to take back.

use ragwort_types::gc::Value;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxContext, SyntaxKind, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::expand::{Expander, MAX_DATA_DEPTH};
use crate::scope::{Scope, Set};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

impl<'gc> Expander<'_, 'gc> {
    /// `stx` as a syntax object.
    pub(crate) fn wrap(&mut self, stx: Stx) -> Result<Value<'gc>, ExpandError> {
        self.wrap_in(stx, MAX_DATA_DEPTH)
    }

    fn wrap_in(&mut self, stx: Stx, depth: usize) -> Result<Value<'gc>, ExpandError> {
        let depth = depth.checked_sub(1).ok_or_else(|| self.error(ExpandErrorKind::TooDeep, stx))?;
        let (mc, span) = (self.mc, self.tree.span(stx));
        let (datum, kind) = match self.tree.view(stx)? {
            View::Id => (self.tree.symbol(stx).expect("an identifier").value(mc), SyntaxKind::Identifier),
            View::Datum(value) => (value, SyntaxKind::Literal),
            View::List(items, tail) => {
                let items = items.into_iter().map(|item| self.wrap_in(item, depth)).collect::<Result<Vec<_>, _>>()?;
                let tail = tail.map_or(Ok(Value::NIL), |tail| self.wrap_in(tail, depth))?;
                (Pairs::new(mc).list_with_tail(items, tail)?, SyntaxKind::List)
            }
            View::Vector(items) => {
                let items = items.into_iter().map(|item| self.wrap_in(item, depth)).collect::<Result<Vec<_>, _>>()?;
                (Vectors::new(mc).immutable_from_slice(&items)?.value(mc), SyntaxKind::Vector)
            }
        };
        let meta = match kind {
            SyntaxKind::Literal => None,
            _ => {
                let set = self.tree.scopes_of(stx)?;
                Some(self.meta(set, kind)?)
            }
        };
        let value = Syntax::new(mc, datum, span, meta)?.value(mc);
        self.tree.scopes.charge(size_of::<(u64, Stx)>())?;
        self.unwrapped.insert(value.to_bits(), stx);
        Ok(value)
    }

    /// The metadata of syntax of `kind` with the scopes `set`, made once for each.
    pub(crate) fn meta(&mut self, set: Set, kind: SyntaxKind) -> Result<SyntaxMeta<'gc>, ExpandError> {
        let tag = match kind {
            SyntaxKind::Identifier => 0,
            SyntaxKind::List => 1,
            SyntaxKind::Vector => 2,
            _ => 3,
        };
        if let Some(&meta) = self.metas.get(&(set, tag)) {
            return Ok(meta);
        }
        let context = match self.contexts.get(&set) {
            Some(&context) => context,
            None => {
                let scopes: Vec<_> = self.tree.scopes.scopes(set).iter().map(|&scope| SyntaxScope(u64::from(scope))).collect();
                let context = SyntaxContext::new(self.mc, &scopes)?;
                self.contexts.insert(set, context);
                context
            }
        };
        let meta = SyntaxMeta::new(self.mc, kind, Some(context), None)?;
        self.tree.scopes.charge(size_of::<((Set, usize), SyntaxMeta)>())?;
        self.metas.insert((set, tag), meta);
        Ok(meta)
    }

    /// The scopes of `context`.
    pub(crate) fn set_of(&mut self, context: Option<SyntaxContext<'gc>>, at: SyntaxSpan<'gc>) -> Result<Set, ExpandError> {
        let Some(context) = context else { return Ok(Set::EMPTY) };
        let scopes = context.scopes(self.mc).map(|scope| Scope::try_from(scope.0)).collect::<Result<Vec<_>, _>>();
        let scopes = scopes.map_err(|_| self.error_at(ExpandErrorKind::BadSyntax, at))?;
        Ok(self.tree.scopes.set(scopes)?)
    }

    /// The syntax a transformer made, `value`, in the tree. What it has that isn't syntax is as
    /// if it were, at `at`, the use it's the output of; a symbol in it is an error.
    pub(crate) fn unwrap(&mut self, value: Value<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        self.unwrap_in(value, at, MAX_DATA_DEPTH)
    }

    fn unwrap_in(&mut self, value: Value<'gc>, at: Stx, depth: usize) -> Result<Stx, ExpandError> {
        if let Some(&stx) = self.unwrapped.get(&value.to_bits()) {
            return Ok(stx);
        }
        let depth = depth.checked_sub(1).ok_or_else(|| self.error(ExpandErrorKind::TooDeep, at))?;
        let mc = self.mc;
        let bad = |this: &Self| this.error(ExpandErrorKind::BadSyntax, at);
        let (datum, span, kind, context) = match Syntax::of(value) {
            Some(s) => (s.datum(mc), s.span(mc), s.kind(mc).ok_or_else(|| bad(self))?, s.context(mc)),
            None if value == Value::NIL || Pair::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::List, None),
            None if AnyVector::of(value).is_some() => (value, self.tree.span(at), SyntaxKind::Vector, None),
            None if Symbol::of(value).is_some() => return Err(bad(self)),
            None => (value, self.tree.span(at), SyntaxKind::Literal, None),
        };
        Ok(match kind {
            SyntaxKind::Identifier => {
                let symbol = Symbol::of(datum).ok_or_else(|| bad(self))?;
                let set = self.set_of(context, span)?;
                self.tree.id(symbol, set, span)?
            }
            SyntaxKind::List => {
                let (mut items, mut rest) = (Vec::new(), datum);
                loop {
                    if let Some(pair) = Pair::of(rest) {
                        items.push(self.unwrap_in(pair.head(mc), at, depth)?);
                        rest = pair.tail(mc);
                    } else if let Some(list) = Syntax::of(rest).filter(|s| s.kind(mc) == Some(SyntaxKind::List)) {
                        // A tail that's the syntax of a list goes on with its items.
                        rest = list.datum(mc);
                    } else {
                        break;
                    }
                }
                let tail = if rest == Value::NIL { None } else { Some(self.unwrap_in(rest, at, depth)?) };
                self.tree.list(&items, tail, span)?
            }
            SyntaxKind::Vector => {
                let vector = AnyVector::of(datum).ok_or_else(|| bad(self))?;
                let items = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i));
                let items = items.map(|item| self.unwrap_in(item, at, depth)).collect::<Result<Vec<_>, _>>()?;
                self.tree.vector(&items, span)?
            }
            SyntaxKind::Literal if Symbol::of(datum).is_none() => self.tree.datum(datum, span)?,
            _ => return Err(bad(self)),
        })
    }
}
