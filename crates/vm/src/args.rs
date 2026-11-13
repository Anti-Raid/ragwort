//! Implements [`Args`]: represents procedure call arguments dispatched by the outer VM loop, reading values in place rather than eagerly allocating heap storage.
//!
//! When a runtime operation yields to the dispatch loop, argument registers remain in the stack slots above the stack base (or, for tail requests, in the deallocated frame). When initiating the callee, arguments are transferred into the new frame. Because the stack clears abandoned slots when migrating between stack segments, arguments must be [detached](Args::detach) into safe inline or heap representations before segment switching.

#[cfg(test)]
#[path = "tests/args.rs"]
mod tests;

use ragwort_types::gc::{Frame, Mutation, Slots, Stack, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::frame::ARGS;
use crate::intrinsic::values;
use crate::run::MAX_ARGS;
use crate::objects::{MultiValue, MultiValueFields};

/// Represents arguments passed to a call by the outer execution loop: holds arguments either directly in stack slots or inlined in an array, followed by remaining arguments in `rest` (represented as a Scheme list or a [`MultiValue`]).
#[derive(Clone, Copy)]
pub(crate) struct Args<'gc> {
    held: Held<'gc>,
    pub(crate) rest: Value<'gc>,
}

/// The maximum number of arguments stored inline. Four values fit in the space `Held::Slots` already occupies, so they add nothing to the size of [`Args`].
const INLINE: usize = 4;

#[derive(Clone, Copy)]
enum Held<'gc> {
    Slots(Slots<'gc>),
    Inline([Value<'gc>; INLINE], u8),
}

const _: () = assert!(size_of::<Held<'static>>() <= size_of::<Slots<'static>>() + size_of::<u64>());

/// Checks `last`, the final argument of an `apply`, and returns it as the list to spread.
///
/// Returns [`Fault::WrongType`] if `last` is a multiple-values object. Such an object is not a list, although `call-with-values` passes its arguments in the same field. This function does not check that `last` is a proper list. That check happens where the elements are bound.
fn spread<'gc>(mc: &Mutation<'gc>, last: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if last.downcast::<MultiValue>(mc).is_some() { Err(Fault::WrongType) } else { Ok(last) }
}

/// Stores `from`, which holds at most [`INLINE`] values, inline.
fn inline<'gc>(from: &[Value<'gc>]) -> Held<'gc> {
    let mut values = [Value::VOID; INLINE];
    values[..from.len()].copy_from_slice(from);
    Held::Inline(values, from.len() as u8)
}

impl<'gc> Args<'gc> {
    pub(crate) fn none() -> Self {
        Args { held: inline(&[]), rest: Value::NIL }
    }

    pub(crate) fn one(value: Value<'gc>) -> Self {
        Args { held: inline(&[value]), rest: Value::NIL }
    }

    pub(crate) fn two(first: Value<'gc>, second: Value<'gc>) -> Self {
        Args { held: inline(&[first, second]), rest: Value::NIL }
    }

    /// Constructs an `Args` sequence starting with `first`, followed by the elements in `rest` (a list or [`MultiValue`]).
    pub(crate) fn before(first: Value<'gc>, rest: Value<'gc>) -> Self {
        Args { held: inline(&[first]), rest }
    }

    /// Constructs an `Args` sequence containing the elements of `rest` (a list or [`MultiValue`]).
    pub(crate) fn list(rest: Value<'gc>) -> Self {
        Args { held: inline(&[]), rest }
    }

    /// Constructs an `Args` sequence backed by stack `slots`, followed by trailing elements in `rest`.
    pub(crate) fn slots(slots: Slots<'gc>, rest: Value<'gc>) -> Self {
        Args { held: Held::Slots(slots), rest }
    }

    fn held(self) -> usize {
        match self.held {
            Held::Slots(slots) => slots.len(),
            Held::Inline(_, count) => usize::from(count),
        }
    }

    fn held_get(self, index: usize) -> Value<'gc> {
        match self.held {
            Held::Slots(slots) => slots.get(index),
            Held::Inline(values, _) => values[index],
        }
    }

    /// Computes the total number of arguments, returning [`Fault::WrongType`] if `rest` is not a proper list.
    pub(crate) fn len(self, mc: &Mutation<'gc>) -> Result<usize, Fault> {
        if let Some(mv) = self.rest.downcast::<MultiValue>(mc) {
            return Ok(self.held() + mv.items(mc).len());
        }
        // A pair stores the length of the list that it starts, so this does not walk the list.
        let rest = Pairs::new(mc).list_len(self.rest).ok_or(Fault::WrongType)?;
        usize::try_from(rest).ok().and_then(|rest| self.held().checked_add(rest)).ok_or(Fault::OutOfRange)
    }

    /// Retrieves the argument at 0-based index `index`, returning [`Fault::Arity`] if `index` is out of bounds.
    pub(crate) fn get(self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Fault> {
        if index < self.held() {
            return Ok(self.held_get(index));
        }
        let index = index - self.held();
        if let Some(mv) = self.rest.downcast::<MultiValue>(mc) {
            let items = mv.items(mc);
            return if index < items.len() { Ok(items.get(index)) } else { Err(Fault::Arity) };
        }
        let mut at = self.rest;
        for _ in 0..index {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Pair::of(at).ok_or(Fault::Arity)?.head(mc))
    }

    /// Returns a new `Args` slice containing the arguments starting from index `start` onward.
    pub(crate) fn tail(self, mc: &Mutation<'gc>, start: usize) -> Result<Self, Fault> {
        let held = self.held();
        if start <= held {
            let held = match self.held {
                Held::Slots(slots) => Held::Slots(slots.slice(start..held).ok_or(Fault::Malformed)?),
                Held::Inline(values, count) => inline(&values[start..usize::from(count)]),
            };
            return Ok(Args { held, rest: self.rest });
        }
        if self.rest.downcast::<MultiValue>(mc).is_some() {
            return Err(Fault::Malformed);
        }
        let mut at = self.rest;
        for _ in held..start {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Args::list(at))
    }

    /// Spreads the final argument (which must be a list) in place, matching `apply` calling semantics.
    pub(crate) fn spread_last(self, mc: &Mutation<'gc>) -> Result<Self, Fault> {
        if self.rest == Value::NIL {
            let last = self.held().checked_sub(1).ok_or(Fault::Arity)?;
            let held = match self.held {
                Held::Slots(slots) => Held::Slots(slots.slice(0..last).ok_or(Fault::Malformed)?),
                Held::Inline(values, _) => inline(&values[..last]),
            };
            return Ok(Args { held, rest: spread(mc, self.held_get(last))? });
        }
        // Here `rest` is a list that the caller supplied, such as the list of an outer `apply`.
        let mut before = Vec::new();
        let mut at = Pair::of(self.rest).ok_or(Fault::WrongType)?;
        while let Some(next) = Pair::of(at.tail(mc)) {
            before.push(at.head(mc));
            at = next;
        }
        if at.tail(mc) != Value::NIL {
            return Err(Fault::WrongType);
        }
        let pairs = Pairs::new(mc);
        let mut rest = spread(mc, at.head(mc))?;
        for &value in before.iter().rev() {
            rest = pairs.cons(value, rest)?.value(mc);
        }
        Ok(Args { held: self.held, rest })
    }

    /// Writes the held positional arguments into the argument register slots of `frame` starting at `fp` on `stack` (handling potential overlap), and returns the number of written arguments. Any remaining arguments remain in `rest`.
    pub(crate) fn write(self, mc: &Mutation<'gc>, stack: &Stack, frame: Frame<'_, 'gc>, fp: usize) -> Result<u8, Fault> {
        let argc = u8::try_from(self.held()).ok().filter(|&count| usize::from(count) <= MAX_ARGS).ok_or(Fault::Malformed)?;
        match self.held {
            Held::Slots(slots) => {
                if !stack.write(mc, fp + usize::from(ARGS), slots) {
                    return Err(Fault::Malformed);
                }
            }
            Held::Inline(values, count) => (ARGS..).zip(&values[..usize::from(count)]).for_each(|(register, &value)| frame.set(register, value)),
        }
        Ok(argc)
    }

    /// Formats these arguments as the return value of `(values arg ...)`, returning the single value directly if there is exactly one argument, or wrapping them in a [`MultiValue`].
    pub(crate) fn values(self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Fault> {
        match (self.held(), self.rest) {
            (1, Value::NIL) => Ok(self.held_get(0)),
            (count, Value::NIL) => values(mc, (0..count).map(|i| self.held_get(i))),
            (0, rest) if rest.downcast::<MultiValue>(mc).is_some() => Ok(rest),
            _ => values(mc, self.iter(mc)?),
        }
    }

    /// Detaches arguments from stack slot references by copying them into inline arrays or heap lists, ensuring they survive stack segment relocation.
    pub(crate) fn detach(self, mc: &Mutation<'gc>) -> Result<Self, Fault> {
        let Held::Slots(slots) = self.held else { return Ok(self) };
        if slots.len() > INLINE {
            return Ok(Args::list(self.to_list(mc)?));
        }
        let mut values = [Value::VOID; INLINE];
        for (i, value) in values.iter_mut().enumerate().take(slots.len()) {
            *value = slots.get(i);
        }
        Ok(Args { held: Held::Inline(values, slots.len() as u8), rest: self.rest })
    }

    /// Converts all arguments into a Scheme list, preserving `self.rest` as the tail.
    pub(crate) fn to_list(self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Fault> {
        let pairs = Pairs::new(mc);
        let mut list = match self.rest.downcast::<MultiValue>(mc) {
            Some(mv) => {
                let items = mv.items(mc);
                let mut list = Value::NIL;
                for i in (0..items.len()).rev() {
                    list = pairs.cons(items.get(i), list)?.value(mc);
                }
                list
            }
            None => self.rest,
        };
        for i in (0..self.held()).rev() {
            list = pairs.cons(self.held_get(i), list)?.value(mc);
        }
        Ok(list)
    }

    /// Returns an exact-size iterator yielding all arguments in order.
    pub(crate) fn iter<'a>(self, mc: &'a Mutation<'gc>) -> Result<Iter<'a, 'gc>, Fault> {
        let items = self.rest.downcast::<MultiValue>(mc).map(|mv| mv.items(mc));
        Ok(Iter { mc, args: self, i: 0, rest: self.rest, items, left: self.len(mc)? })
    }
}

pub(crate) struct Iter<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    args: Args<'gc>,
    i: usize,
    rest: Value<'gc>,
    items: Option<Slots<'gc>>,
    left: usize,
}

impl<'gc> Iterator for Iter<'_, 'gc> {
    type Item = Value<'gc>;

    fn next(&mut self) -> Option<Value<'gc>> {
        self.left = self.left.checked_sub(1)?;
        let index = self.i;
        self.i += 1;
        let held = self.args.held();
        if index < held {
            return Some(self.args.held_get(index));
        }
        if let Some(items) = self.items {
            return Some(items.get(index - held));
        }
        let pair = Pair::of(self.rest)?;
        self.rest = pair.tail(self.mc);
        Some(pair.head(self.mc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

impl ExactSizeIterator for Iter<'_, '_> {}
