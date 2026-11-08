//! Syntax objects, as the intrinsics that take them apart and make them see them: what the reader
//! makes, and what the expander hands a macro's transformer. A list's syntax holds a list of
//! syntax, and a vector's a vector of it; an identifier's holds a symbol, and its scopes.

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxMeta, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::equal::PER_FUEL;
use crate::op::Fuel;

/// How deeply the data these take apart can nest, as deeply as the reader reads.
const MAX_DEPTH: usize = 1024;

pub(crate) fn is_identifier<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> bool {
    Syntax::of(x).is_some_and(|s| s.kind(mc) == Some(SyntaxKind::Identifier))
}

/// What `x` wraps: a symbol, a list or vector of syntax, or a literal.
pub(crate) fn unwrap<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Syntax::of(x).ok_or(Fault::WrongType)?.datum(mc))
}

/// The datum `x` stands for: its syntax unwrapped, all the way down.
pub(crate) fn to_datum<'gc>(mc: &Mutation<'gc>, x: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let mut count = 0;
    let datum = strip(mc, x, MAX_DEPTH, &mut count)?;
    fuel.spend(count / PER_FUEL)?;
    Ok(datum)
}

fn strip<'gc>(mc: &Mutation<'gc>, x: Value<'gc>, depth: usize, count: &mut u64) -> Result<Value<'gc>, Fault> {
    let depth = depth.checked_sub(1).ok_or(Fault::OutOfRange)?;
    *count += 1;
    let x = Syntax::of(x).map_or(x, |s| s.datum(mc));
    if Pair::of(x).is_some() {
        let (mut items, mut at) = (Vec::new(), x);
        while let Some(pair) = Pair::of(at) {
            items.push(strip(mc, pair.head(mc), depth, count)?);
            at = Syntax::of(pair.tail(mc)).map_or(pair.tail(mc), |s| s.datum(mc));
            *count += 1;
        }
        let tail = if at == Value::NIL { at } else { strip(mc, at, depth, count)? };
        return Ok(Pairs::new(mc).list_with_tail(items, tail)?);
    }
    if let Some(vector) = AnyVector::of(x) {
        let items = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).map(|v| strip(mc, v, depth, count)).collect::<Result<Vec<_>, _>>()?;
        return Ok(Vectors::new(mc).immutable_from_slice(&items)?.value(mc));
    }
    Ok(x)
}

/// `datum` as syntax, with the scopes and span of `context`, syntax or `#f` for none: its
/// symbols as identifiers, and its pairs and vectors as lists and vectors of syntax. What's
/// syntax already stays as it is.
pub(crate) fn to_syntax<'gc>(mc: &Mutation<'gc>, context: Value<'gc>, datum: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let (scopes, span) = match Syntax::of(context) {
        Some(s) => (s.context(mc), s.span(mc)),
        None if context == Value::FALSE => (None, SyntaxSpan::default()),
        None => return Err(Fault::WrongType),
    };
    let meta = |kind| SyntaxMeta::new(mc, kind, scopes, None);
    let wrap = Wrap { span, id: meta(SyntaxKind::Identifier)?, list: meta(SyntaxKind::List)?, vector: meta(SyntaxKind::Vector)? };
    let mut count = 0;
    let syntax = wrap.wrap(mc, datum, MAX_DEPTH, &mut count)?;
    fuel.spend(count / PER_FUEL)?;
    Ok(syntax)
}

struct Wrap<'gc> {
    span: SyntaxSpan<'gc>,
    id: SyntaxMeta<'gc>,
    list: SyntaxMeta<'gc>,
    vector: SyntaxMeta<'gc>,
}

impl<'gc> Wrap<'gc> {
    fn wrap(&self, mc: &Mutation<'gc>, x: Value<'gc>, depth: usize, count: &mut u64) -> Result<Value<'gc>, Fault> {
        let depth = depth.checked_sub(1).ok_or(Fault::OutOfRange)?;
        *count += 1;
        let (datum, meta) = if Syntax::of(x).is_some() {
            return Ok(x);
        } else if Symbol::of(x).is_some() {
            (x, Some(self.id))
        } else if Pair::of(x).is_some() {
            let (mut items, mut at) = (Vec::new(), x);
            while let Some(pair) = Pair::of(at) {
                items.push(self.wrap(mc, pair.head(mc), depth, count)?);
                at = pair.tail(mc);
                *count += 1;
            }
            let tail = if at == Value::NIL { at } else { self.wrap(mc, at, depth, count)? };
            (Pairs::new(mc).list_with_tail(items, tail)?, Some(self.list))
        } else if let Some(vector) = AnyVector::of(x) {
            let items = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).map(|v| self.wrap(mc, v, depth, count)).collect::<Result<Vec<_>, _>>()?;
            (Vectors::new(mc).immutable_from_slice(&items)?.value(mc), Some(self.vector))
        } else {
            (x, None)
        };
        Ok(Syntax::new(mc, datum, self.span, meta)?.value(mc))
    }
}

/// Whether the identifiers `a` and `b` have the same name and scopes, so that a binding of one
/// would bind the other.
pub(crate) fn same_identifier<'gc>(mc: &Mutation<'gc>, a: Value<'gc>, b: Value<'gc>) -> Result<bool, Fault> {
    if !is_identifier(mc, a) || !is_identifier(mc, b) {
        return Err(Fault::WrongType);
    }
    let (a, b) = (Syntax::of(a).ok_or(Fault::WrongType)?, Syntax::of(b).ok_or(Fault::WrongType)?);
    if a.datum(mc) != b.datum(mc) {
        return Ok(false);
    }
    Ok(match (a.context(mc), b.context(mc)) {
        (Some(x), Some(y)) => x == y || x.scopes(mc).eq(y.scopes(mc)),
        (x, y) => x.is_none_or(|x| x.scopes(mc).len() == 0) && y.is_none_or(|y| y.scopes(mc).len() == 0),
    })
}
