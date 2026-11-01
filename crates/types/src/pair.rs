//! Pairs, which are immutable, as in Racket. Each knows the length of the list it starts, so
//! `length` and `list?` take constant time. A pair can't come to reach itself, so the length
//! is always exact.

use crate::gc::{Gc, Mutation, OutOfMemory, Value};
use crate::objects::{self, Data, PairFields};

#[cfg(test)]
#[path = "tests/pair.rs"]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Pair<'gc>(Gc<'gc, objects::Pair>);

impl<'gc> Pair<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Pair(p)) => Some(Self(p)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    #[inline]
    pub fn head(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.head(mc)
    }

    #[inline]
    pub fn tail(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.tail(mc)
    }

    /// The length of the list this pair starts, unless its pairs end in something other than
    /// `()`.
    #[inline]
    pub fn list_len(self, mc: &Mutation<'gc>) -> Option<u64> {
        Some(self.0.length(mc)).filter(|&n| n != 0)
    }
}

/// Pair operations for one step.
#[derive(Clone, Copy)]
pub struct Pairs<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Pairs<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    #[inline]
    pub fn pair(&self, v: Value<'gc>) -> Option<Pair<'gc>> {
        Pair::of(v)
    }

    pub fn cons(&self, head: Value<'gc>, tail: Value<'gc>) -> Result<Pair<'gc>, OutOfMemory> {
        let len = self.list_len(tail).map_or(0, |n| n.saturating_add(1));
        Ok(Pair(objects::Pair::new(self.mc, head, tail, len)?))
    }

    /// A list of `items`.
    pub fn list(&self, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
        self.list_with_tail(items.iter().copied(), Value::NIL)
    }

    /// Prepends `items`, in order, to a proper or dotted `tail`.
    pub fn list_with_tail<I>(&self, items: I, mut tail: Value<'gc>) -> Result<Value<'gc>, OutOfMemory>
    where
        I: IntoIterator<Item = Value<'gc>>,
        I::IntoIter: DoubleEndedIterator,
    {
        let mut len = self.list_len(tail);
        for head in items.into_iter().rev() {
            len = len.map(|n| n.saturating_add(1));
            tail = Value::object(self.mc, objects::Pair::new(self.mc, head, tail, len.unwrap_or(0))?);
        }
        Ok(tail)
    }

    /// The length of `v` if it's a list: `()` or a pair whose pairs end in `()`.
    #[inline]
    pub fn list_len(&self, v: Value<'gc>) -> Option<u64> {
        match Pair::of(v) {
            Some(p) => p.list_len(self.mc),
            None => (v == Value::NIL).then_some(0),
        }
    }

    pub fn is_list(&self, v: Value<'gc>) -> bool {
        self.list_len(v).is_some()
    }

    /// The heads of the pairs starting at `v`. [`Elements::rest`] is what follows them.
    pub fn elements(&self, v: Value<'gc>) -> Elements<'a, 'gc> {
        Elements { mc: self.mc, rest: v }
    }
}

/// The heads of a chain of pairs, from [`Pairs::elements`].
pub struct Elements<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    rest: Value<'gc>,
}

impl<'gc> Elements<'_, 'gc> {
    /// What's left: the tail of the last pair reached, `()` once a list is used up.
    pub fn rest(&self) -> Value<'gc> {
        self.rest
    }
}

impl<'gc> Iterator for Elements<'_, 'gc> {
    type Item = Value<'gc>;

    fn next(&mut self) -> Option<Value<'gc>> {
        let p = Pair::of(self.rest)?;
        self.rest = p.tail(self.mc);
        Some(p.head(self.mc))
    }
}
