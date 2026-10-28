//! Pairs, which are immutable, as in Racket. Each knows the length of the list it starts, so
//! `length` and `list?` take constant time. A pair can't come to reach itself, so the length
//! is always exact.

use ragwort_gc::{Gc, Mutation, OutOfMemory, Plain, Trace, TypeTag, Value};

#[cfg(test)]
mod tests;

#[derive(Trace, Plain)]
pub struct Pair<'gc> {
    head: Value<'gc>,
    tail: Value<'gc>,
    /// The length of the list this pair starts, or 0 if its pairs don't end in `()`.
    len: u64,
}

impl<'gc> Pair<'gc> {
    pub fn head(&self) -> Value<'gc> {
        self.head
    }

    pub fn tail(&self) -> Value<'gc> {
        self.tail
    }

    /// The length of the list this pair starts, unless its pairs end in something other than
    /// `()`.
    pub fn list_len(&self) -> Option<u64> {
        (self.len != 0).then_some(self.len)
    }
}

/// Pair operations for one step.
#[derive(Clone, Copy)]
pub struct Pairs<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    tag: TypeTag<'gc, Pair<'gc>>,
}

impl<'a, 'gc> Pairs<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self { mc, tag: mc.type_tag()? })
    }

    pub fn pair(&self, v: Value<'gc>) -> Option<Gc<'gc, Pair<'gc>>> {
        v.downcast_tag(self.mc, self.tag)
    }

    pub fn cons(&self, head: Value<'gc>, tail: Value<'gc>) -> Result<Gc<'gc, Pair<'gc>>, OutOfMemory> {
        let len = match self.pair(tail) {
            Some(p) if p.len != 0 => p.len.saturating_add(1),
            Some(_) => 0,
            None => u64::from(tail == Value::NIL),
        };
        self.mc.alloc(Pair { head, tail, len })
    }

    /// A list of `items`.
    pub fn list(&self, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
        items.iter().rev().try_fold(Value::NIL, |tail, &head| Ok(Value::object(self.mc, self.cons(head, tail)?)))
    }

    /// The length of `v` if it's a list: `()` or a pair whose pairs end in `()`.
    pub fn list_len(&self, v: Value<'gc>) -> Option<u64> {
        match self.pair(v) {
            Some(p) => p.list_len(),
            None => (v == Value::NIL).then_some(0),
        }
    }

    pub fn is_list(&self, v: Value<'gc>) -> bool {
        self.list_len(v).is_some()
    }

    /// The heads of the pairs starting at `v`. [`Elements::rest`] is what follows them.
    pub fn elements(&self, v: Value<'gc>) -> Elements<'a, 'gc> {
        Elements { pairs: *self, rest: v }
    }
}

/// The heads of a chain of pairs, from [`Pairs::elements`].
pub struct Elements<'a, 'gc> {
    pairs: Pairs<'a, 'gc>,
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
        let p = self.pairs.pair(self.rest)?;
        self.rest = p.tail;
        Some(p.head)
    }
}
