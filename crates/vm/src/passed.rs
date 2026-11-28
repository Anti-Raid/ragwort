//! [`Passed`]: the values the outer loop passes to a call, or returns from one.
//!
//! They have the shape of a call's arguments in the inner loop: a run of consecutive stack slots,
//! followed by the elements of a list.
//!
//! - The operands of a request are already in registers. A `Passed` refers to them in place.
//! - A value the VM passes itself, such as the condition a handler receives, is first written
//!   into the argument slots of the bottom frame. See [`Outer::pass`].
//!
//! The slots belong to the stack segment they were on when the `Passed` was made. They are cleared
//! when the stack moves to another segment, so before that the values are either used or taken off
//! the stack with [`Passed::take`].

#[cfg(test)]
#[path = "tests/passed.rs"]
mod tests;

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Mutation, Slots, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::frame::ARGS;
use crate::machine::{Outer, Then};
use crate::run::MAX_ARGS;

/// Values held in stack slots, followed by the elements of the list `rest`.
#[derive(Clone, Copy)]
pub(crate) struct Passed<'gc> {
    slots: Option<Slots<'gc>>,
    pub(crate) rest: Value<'gc>,
    /// Whether the slots are already the argument slots of the bottom frame, as written by [`Outer::pass`]. The call that receives them then does not need to move them.
    pub(crate) placed: bool,
}

/// Values taken off the stack: exactly one value, or the list of all of them.
pub(crate) enum Taken<'gc> {
    One(Value<'gc>),
    List(Value<'gc>),
}

impl<'gc> Taken<'gc> {
    /// Returns the action that returns these values to the current continuation.
    pub(crate) fn returned(self) -> Then<'gc> {
        match self {
            Taken::One(value) => Then::Return(value),
            Taken::List(list) => Then::ReturnValues(list),
        }
    }
}

impl<'gc> Passed<'gc> {
    pub(crate) fn none() -> Self {
        Passed { slots: None, rest: Value::NULL, placed: false }
    }

    /// Returns the elements of the list `rest` as passed values.
    pub(crate) fn list(rest: Value<'gc>) -> Self {
        Passed { slots: None, rest, placed: false }
    }

    /// Returns the values in `slots`, followed by the elements of the list `rest`, as passed values.
    pub(crate) fn slots(slots: Slots<'gc>, rest: Value<'gc>) -> Self {
        Passed { slots: Some(slots), rest, placed: false }
    }

    /// Returns the slots that hold values, if any.
    pub(crate) fn held(self) -> Option<Slots<'gc>> {
        self.slots.filter(|slots| !slots.is_empty())
    }

    fn count(self) -> usize {
        self.slots.map_or(0, Slots::len)
    }

    /// Returns the number of values, or `None` if `rest` is not a list.
    pub(crate) fn len(self, mc: &Mutation<'gc>) -> Option<u64> {
        Pairs::new(mc).list_len(self.rest).map(|listed| listed + self.count() as u64)
    }

    /// Returns the value at position `index`. Fails with [`Fault::Arity`] if there are not that many.
    pub(crate) fn get(self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Fault> {
        if let Some(slots) = self.slots.filter(|slots| index < slots.len()) {
            return Ok(slots.get(index));
        }
        let mut at = self.rest;
        for _ in self.count()..index {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Pair::of(at).ok_or(Fault::Arity)?.head(mc))
    }

    /// Returns the values from position `start` on. Fails with [`Fault::Arity`] if there are fewer than `start`.
    pub(crate) fn skip(self, mc: &Mutation<'gc>, start: usize) -> Result<Self, Fault> {
        let count = self.count();
        if let Some(slots) = self.slots.filter(|_| start <= count) {
            return Ok(Passed { slots: slots.slice(start..count), rest: self.rest, placed: false });
        }
        let mut at = self.rest;
        for _ in count..start {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Passed::list(at))
    }

    /// Spreads the last value as `apply` does. The last value must be a list, and its elements replace it. This function does not check that the list is a proper list. That check happens when the values are bound to parameters.
    pub(crate) fn spread_last(self, mc: &Mutation<'gc>) -> Result<Self, Fault> {
        if self.rest == Value::NULL {
            let slots = self.held().ok_or(Fault::Arity)?;
            let last = slots.len() - 1;
            return Ok(Passed { slots: slots.slice(0..last), rest: slots.get(last), placed: self.placed });
        }
        // Here `rest` is a list that the caller supplied, such as the list of an outer `apply`.
        let mut before = Vec::new();
        let mut at = Pair::of(self.rest).ok_or(Fault::WrongType)?;
        while let Some(next) = Pair::of(at.tail(mc)) {
            before.push(at.head(mc));
            at = next;
        }
        if at.tail(mc) != Value::NULL {
            return Err(Fault::WrongType);
        }
        let pairs = Pairs::new(mc);
        let mut rest = at.head(mc);
        for &value in before.iter().rev() {
            rest = pairs.cons(value, rest)?.value(mc);
        }
        Ok(Passed { slots: self.slots, rest, placed: self.placed })
    }

    /// Returns all the values as one list, which ends in `rest`.
    pub(crate) fn to_list(self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Fault> {
        let pairs = Pairs::new(mc);
        let mut list = self.rest;
        if let Some(slots) = self.slots {
            for i in (0..slots.len()).rev() {
                list = pairs.cons(slots.get(i), list)?.value(mc);
            }
        }
        Ok(list)
    }

    /// Takes the values off the stack. Exactly one value is taken as it is, without allocating. Fails with [`Fault::WrongType`] if `rest` is not a proper list.
    pub(crate) fn take(self, mc: &Mutation<'gc>) -> Result<Taken<'gc>, Fault> {
        if let Some(slots) = self.slots.filter(|slots| slots.len() == 1 && self.rest == Value::NULL) {
            return Ok(Taken::One(slots.get(0)));
        }
        if self.rest == Value::NULL && self.count() == 0 {
            return Ok(Taken::List(Value::NULL));
        }
        if !Pairs::new(mc).is_list(self.rest) {
            return Err(Fault::WrongType);
        }
        Ok(Taken::List(self.to_list(mc)?))
    }

    /// Returns the action that returns these values, as `(values x ...)` does.
    pub(crate) fn returned(self, mc: &Mutation<'gc>) -> Result<Then<'gc>, Fault> {
        Ok(self.take(mc)?.returned())
    }
}

impl<'gc> Outer<'_, 'gc> {
    /// Writes `values` into the argument slots of the bottom frame, where the next call starts, and returns them as passed values.
    ///
    /// Call this last, when everything the call needs from the stack has been read. It can move the stack to a new segment, and nothing else may use the stack between this and the call.
    pub(crate) fn pass(&mut self, values: &[Value<'gc>]) -> Result<Passed<'gc>, Fault> {
        let mc = self.mc();
        // Register indexes wrap around the frame window. So more values than a call can take would overwrite the first values.
        if values.len() > MAX_ARGS {
            return Err(Fault::Malformed);
        }
        let fp = self.segments.bottom(0)?;
        let frame = self.segments.frame(fp)?;
        for (register, &value) in (ARGS..).zip(values) {
            frame.set(register, value);
        }
        let at = fp + usize::from(ARGS);
        let slots = self.segments.stack.segment(mc).slots(mc).slice(at..at + values.len()).ok_or(Fault::Malformed)?;
        Ok(Passed { slots: Some(slots), rest: Value::NULL, placed: true })
    }

    /// Converts `taken` back to passed values. A single value is written into the bottom frame, as [`Outer::pass`] does. A list becomes the rest list.
    pub(crate) fn repass(&mut self, taken: Taken<'gc>) -> Result<Passed<'gc>, Fault> {
        match taken {
            Taken::One(value) => self.pass(&[value]),
            Taken::List(list) => Ok(Passed::list(list)),
        }
    }
}
