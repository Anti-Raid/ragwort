//! Work that would recurse as deeply as what it works on nests, as the front ends' expansion
//! into [`Core`](crate::Core) would, done from a stack of its own instead.
//!
//! A step is done, with what it makes, or needs what a call makes first: it goes on with that
//! once it's made, or, if it makes just what the call does, it's the call's. What goes on after
//! each call waits on a stack in the heap, so the machine's stack holds one step at a time, and
//! the work is done in the order the recursion would have done it.

/// What a step of work over a state `S` does next, with calls `C` that each make a `T`.
pub enum Step<'k, S: ?Sized, C, T, E> {
    Done(T),
    /// Makes what `C` does, then goes on with it.
    Call(C, Then<'k, S, C, T, E>),
    /// Makes just what `C` does.
    Tail(C),
    /// Makes what each of the calls does, in order, then goes on with all they made.
    All(Vec<C>, Gathered<'k, S, C, T, E>),
}

/// What goes on once a call is done, with what it made.
pub type Then<'k, S, C, T, E> = Box<dyn FnOnce(&mut S, T) -> Result<Step<'k, S, C, T, E>, E> + 'k>;

/// What goes on once each of some calls is done, with all they made.
pub type Gathered<'k, S, C, T, E> = Box<dyn FnOnce(&mut S, Vec<T>) -> Result<Step<'k, S, C, T, E>, E> + 'k>;

impl<'k, S: ?Sized, C, T, E> Step<'k, S, C, T, E> {
    /// Makes what `call` does, then goes on with `then`.
    pub fn then(call: C, then: impl FnOnce(&mut S, T) -> Result<Self, E> + 'k) -> Self {
        Step::Call(call, Box::new(then))
    }
}

/// Makes what each of `calls` does, in order, then goes on with all they made: a step, as a
/// step's work gives one.
pub fn all<'k, S: ?Sized, C, T, E>(calls: Vec<C>, then: impl FnOnce(&mut S, Vec<T>) -> Result<Step<'k, S, C, T, E>, E> + 'k) -> Result<Step<'k, S, C, T, E>, E> {
    Ok(Step::All(calls, Box::new(then)))
}

/// What's waiting on the call being made: what goes on with it, or the calls after it of an
/// [`Step::All`], with what those before it made.
enum Waiting<'k, S: ?Sized, C, T, E> {
    Then(Then<'k, S, C, T, E>),
    All { calls: std::vec::IntoIter<C>, made: Vec<T>, then: Gathered<'k, S, C, T, E> },
}

/// What `call` makes, each call done by `step`.
pub fn run<'k, S: ?Sized, C, T, E>(state: &mut S, call: C, mut step: impl FnMut(&mut S, C) -> Result<Step<'k, S, C, T, E>, E>) -> Result<T, E> {
    let mut waiting: Vec<Waiting<'k, S, C, T, E>> = Vec::new();
    let mut next = Step::Tail(call);
    loop {
        next = match next {
            Step::Tail(call) => step(state, call)?,
            Step::Call(call, then) => {
                waiting.push(Waiting::Then(then));
                step(state, call)?
            }
            Step::All(calls, then) => {
                let mut calls = calls.into_iter();
                match calls.next() {
                    Some(call) => {
                        waiting.push(Waiting::All { made: Vec::with_capacity(calls.len() + 1), calls, then });
                        step(state, call)?
                    }
                    None => then(state, Vec::new())?,
                }
            }
            Step::Done(value) => match waiting.last_mut() {
                None => return Ok(value),
                Some(Waiting::All { calls, made, .. }) => {
                    made.push(value);
                    match calls.next() {
                        Some(call) => step(state, call)?,
                        None => {
                            let Some(Waiting::All { made, then, .. }) = waiting.pop() else { unreachable!("the gather just looked at") };
                            then(state, made)?
                        }
                    }
                }
                Some(Waiting::Then(_)) => {
                    let Some(Waiting::Then(then)) = waiting.pop() else { unreachable!("the continuation just looked at") };
                    then(state, value)?
                }
            },
        };
    }
}
