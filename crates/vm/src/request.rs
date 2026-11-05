//! A [`Request`] calls a procedure or changes the continuation, so the outer loop carries it
//! out. It reads its arguments out of the frame, keeps the continuation it returns to if
//! [`Request::keeps`] says so, then runs, and what it leads to is a [`Then`].
//!
//! These are only what the prelude can't write itself: marks, prompts and composable
//! continuations, as Racket has them. `call/cc`, exceptions, the default prompt tag and its
//! handler are the prelude's, written in terms of them.

use ragwort_types::gc::Value;
use ragwort_types::named;

use crate::Fault;
use crate::machine::{Outer, Then, list};
use crate::objects::{MultiValue, MultiValueFields};
use crate::prompts::{self, tag_of};

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Request {
        /// `(apply f x ... list)`: calls `f` with the `x`s, then the elements of `list`: as many as
        /// fill `f`'s required parameters, the rest as its rest list, so a list of any length fits.
        /// The inner loop makes it a call itself, as it's already laid out as one.
        Apply = "apply",
        /// `(apply-values f v)`: calls `f` with the values in `v` if it's a [`MultiValue`], or
        /// with `v` alone.
        ApplyValues = "apply-values",
        /// `(with-mark key value f arg ...)`: calls `f` with the `arg`s, with a mark of `value`
        /// for `key` on its continuation. In tail position, it replaces the frame's mark for
        /// `key`, if it has one, so a loop that sets a mark stays in constant space.
        WithMark = "with-mark",
        /// `(mark-value key default)`: the value of the nearest mark for `key`, or `default`.
        MarkValue = "mark-value",
        /// `(call-with-prompt tag handler f arg ...)`: calls `f` with the `arg`s under a prompt for
        /// `tag`, which an abort to it calls `handler` in place of.
        CallWithPrompt = "call-with-prompt",
        /// `(abort tag value ...)`: drops the continuation up to the nearest prompt for `tag`, and
        /// the prompt, and calls its handler with the values in their place.
        Abort = "abort",
        /// `(capture tag f)`: calls `f` with the composable continuation up to the nearest prompt
        /// for `tag`, a procedure that goes on with it on top of the continuation it's called in.
        Capture = "capture",
    }
}

impl Request {
    /// Whether it takes `args` arguments. Bytecode that passes another number is malformed.
    pub fn takes(self, args: usize) -> bool {
        let (least, most) = match self {
            Request::Apply => (2, None),
            Request::WithMark | Request::CallWithPrompt => (3, None),
            Request::ApplyValues | Request::MarkValue | Request::Capture => (2, Some(2)),
            Request::Abort => (1, None),
        };
        args >= least && most.is_none_or(|most| args <= most)
    }

    /// Whether what it leads to returns to the instruction after it, or for a tail request, to
    /// the frame's caller. An abort drops the continuation instead.
    pub(crate) fn keeps(self) -> bool {
        self != Request::Abort
    }

    /// Runs it on `args`, as many as it [takes](Request::takes).
    pub(crate) fn run<'gc>(self, outer: &mut Outer<'_, 'gc>, args: &[Value<'gc>]) -> Result<Then<'gc>, Fault> {
        let (mc, task) = (outer.mc(), outer.task());
        Ok(match self {
            Request::Apply => {
                let (&spread, before) = args[1..].split_last().ok_or(Fault::Malformed)?;
                Then::Call(args[0], before.iter().copied().chain(list(mc, spread)?).collect())
            }
            Request::ApplyValues => {
                let values = match args[1].downcast::<MultiValue>(mc) {
                    Some(mv) => {
                        let items = mv.items(mc);
                        (0..items.len()).map(|i| items.get(i)).collect()
                    }
                    None => vec![args[1]],
                };
                Then::Call(args[0], values)
            }
            Request::WithMark => {
                outer.segments.set_mark(args[0], args[1])?;
                Then::Call(args[2], args[3..].to_vec())
            }
            Request::MarkValue => Then::Return(prompts::mark(mc, task, args[0], args[1])?),
            Request::CallWithPrompt => {
                prompts::push(mc, task, tag_of(mc, args[0])?, args[1])?;
                Then::Call(args[2], args[3..].to_vec())
            }
            Request::Abort => match prompts::abort(mc, task, tag_of(mc, args[0])?)? {
                Some(handler) => Then::Call(handler, args[1..].to_vec()),
                None => {
                    let (&thunk, rest) = args[1..].split_first().ok_or(Fault::Arity)?;
                    Then::Call(thunk, rest.to_vec())
                }
            },
            Request::Capture => {
                let k = prompts::capture(mc, task, tag_of(mc, args[0])?)?;
                Then::Call(args[1], vec![k])
            }
        })
    }
}
