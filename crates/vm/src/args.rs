//! [`Args`]: what a call the outer loop makes gets, read where they are rather than copied out.
//!
//! A request's arguments are still in its registers once the frame is kept: in the slots just
//! above the stack's base, or for a tail request, in the frame the chain no longer needs. The
//! frame of what it calls starts at or below them, so they're copied into it from there. The
//! stack voids those slots once it moves to another segment, so they're [detached](Args::detach)
//! before it does.

use ragwort_types::gc::{Frame, Mutation, Slots, Stack, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::frame::ARGS;
use crate::intrinsic::values;
use crate::run::MAX_ARGS;
use crate::objects::{MultiValue, MultiValueFields};

/// The arguments of a call the outer loop makes: values held in slots, as a request's registers
/// left them, or inline, then the elements of `rest`, a list or a [`MultiValue`].
#[derive(Clone, Copy)]
pub(crate) struct Args<'gc> {
    held: Held<'gc>,
    pub(crate) rest: Value<'gc>,
}

#[derive(Clone, Copy)]
enum Held<'gc> {
    Slots(Slots<'gc>),
    Inline([Value<'gc>; 2], u8),
}

impl<'gc> Args<'gc> {
    pub(crate) fn none() -> Self {
        Args { held: Held::Inline([Value::VOID; 2], 0), rest: Value::NIL }
    }

    pub(crate) fn one(a: Value<'gc>) -> Self {
        Args { held: Held::Inline([a, Value::VOID], 1), rest: Value::NIL }
    }

    pub(crate) fn two(a: Value<'gc>, b: Value<'gc>) -> Self {
        Args { held: Held::Inline([a, b], 2), rest: Value::NIL }
    }

    /// `first`, then the elements of `rest`, a list or a [`MultiValue`].
    pub(crate) fn before(first: Value<'gc>, rest: Value<'gc>) -> Self {
        Args { held: Held::Inline([first, Value::VOID], 1), rest }
    }

    /// The elements of `rest`, a list or a [`MultiValue`].
    pub(crate) fn list(rest: Value<'gc>) -> Self {
        Args { held: Held::Inline([Value::VOID; 2], 0), rest }
    }

    /// The values in `slots`, then the elements of `rest`.
    pub(crate) fn slots(slots: Slots<'gc>, rest: Value<'gc>) -> Self {
        Args { held: Held::Slots(slots), rest }
    }

    fn held(self) -> usize {
        match self.held {
            Held::Slots(slots) => slots.len(),
            Held::Inline(_, n) => usize::from(n),
        }
    }

    fn held_get(self, i: usize) -> Value<'gc> {
        match self.held {
            Held::Slots(slots) => slots.get(i),
            Held::Inline(values, _) => values[i],
        }
    }

    /// How many there are. Faults if `rest` isn't a proper list.
    pub(crate) fn len(self, mc: &Mutation<'gc>) -> Result<usize, Fault> {
        if let Some(mv) = self.rest.downcast::<MultiValue>(mc) {
            return Ok(self.held() + mv.items(mc).len());
        }
        let (mut n, mut at) = (self.held(), self.rest);
        while let Some(pair) = Pair::of(at) {
            (n, at) = (n + 1, pair.tail(mc));
        }
        if at != Value::NIL {
            return Err(Fault::WrongType);
        }
        Ok(n)
    }

    /// Argument `i`.
    pub(crate) fn get(self, mc: &Mutation<'gc>, i: usize) -> Result<Value<'gc>, Fault> {
        if i < self.held() {
            return Ok(self.held_get(i));
        }
        let i = i - self.held();
        if let Some(mv) = self.rest.downcast::<MultiValue>(mc) {
            let items = mv.items(mc);
            return if i < items.len() { Ok(items.get(i)) } else { Err(Fault::Arity) };
        }
        let mut at = self.rest;
        for _ in 0..i {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Pair::of(at).ok_or(Fault::Arity)?.head(mc))
    }

    /// The arguments from `k` on.
    pub(crate) fn tail(self, mc: &Mutation<'gc>, k: usize) -> Result<Self, Fault> {
        let held = self.held();
        if k <= held {
            let held = match self.held {
                Held::Slots(slots) => Held::Slots(slots.slice(k..held).ok_or(Fault::Malformed)?),
                Held::Inline(values, n) => match k {
                    0 => Held::Inline(values, n),
                    1 => Held::Inline([values[1], Value::VOID], n - 1),
                    _ => Held::Inline([Value::VOID; 2], 0),
                },
            };
            return Ok(Args { held, rest: self.rest });
        }
        if self.rest.downcast::<MultiValue>(mc).is_some() {
            return Err(Fault::Malformed);
        }
        let mut at = self.rest;
        for _ in held..k {
            at = Pair::of(at).ok_or(Fault::Arity)?.tail(mc);
        }
        Ok(Args::list(at))
    }

    /// These, with the last, a list, spread in its place, as `apply` takes them.
    pub(crate) fn spread_last(self, mc: &Mutation<'gc>) -> Result<Self, Fault> {
        if self.rest == Value::NIL {
            let n = self.held().checked_sub(1).ok_or(Fault::Arity)?;
            let held = match self.held {
                Held::Slots(slots) => Held::Slots(slots.slice(0..n).ok_or(Fault::Malformed)?),
                Held::Inline(values, _) => Held::Inline([values[0], Value::VOID], n as u8),
            };
            return Ok(Args { held, rest: self.held_get(n) });
        }
        let mut before = Vec::new();
        let mut at = Pair::of(self.rest).ok_or(Fault::Malformed)?;
        while let Some(next) = Pair::of(at.tail(mc)) {
            before.push(at.head(mc));
            at = next;
        }
        let pairs = Pairs::new(mc);
        let mut rest = at.head(mc);
        for &v in before.iter().rev() {
            rest = pairs.cons(v, rest)?.value(mc);
        }
        Ok(Args { held: self.held, rest })
    }

    /// Writes the held values to the argument registers of `frame`, at `fp` on `stack`, which
    /// may overlap the slots they're in, and returns how many there are: the rest are in `rest`.
    pub(crate) fn write(self, mc: &Mutation<'gc>, stack: &Stack, frame: Frame<'_, 'gc>, fp: usize) -> Result<u8, Fault> {
        let argc = u8::try_from(self.held()).ok().filter(|&n| usize::from(n) <= MAX_ARGS).ok_or(Fault::Malformed)?;
        match self.held {
            Held::Slots(slots) => {
                if !stack.write(mc, fp + usize::from(ARGS), slots) {
                    return Err(Fault::Malformed);
                }
            }
            Held::Inline(values, n) => (ARGS..).zip(&values[..usize::from(n)]).for_each(|(r, &v)| frame.set(r, v)),
        }
        Ok(argc)
    }

    /// What `(values arg ...)` of them returns.
    pub(crate) fn values(self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Fault> {
        match (self.held(), self.rest) {
            (1, Value::NIL) => Ok(self.held_get(0)),
            (n, Value::NIL) => values(mc, (0..n).map(|i| self.held_get(i))),
            (0, rest) if rest.downcast::<MultiValue>(mc).is_some() => Ok(rest),
            _ => values(mc, self.iter(mc)?),
        }
    }

    /// These, held so they don't depend on the slots they're in, which the stack voids once it
    /// moves to another segment.
    pub(crate) fn detach(self, mc: &Mutation<'gc>) -> Result<Self, Fault> {
        let Held::Slots(slots) = self.held else { return Ok(self) };
        Ok(match slots.len() {
            0 => Args::list(self.rest),
            1 => Args { held: Held::Inline([slots.get(0), Value::VOID], 1), rest: self.rest },
            2 => Args { held: Held::Inline([slots.get(0), slots.get(1)], 2), rest: self.rest },
            _ => Args::list(self.to_list(mc)?),
        })
    }

    /// All of them, as a list.
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

    /// All of them, in order.
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
        let i = self.i;
        self.i += 1;
        let held = self.args.held();
        if i < held {
            return Some(self.args.held_get(i));
        }
        if let Some(items) = self.items {
            return Some(items.get(i - held));
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
