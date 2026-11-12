//! An explicit continuation stack for work that would otherwise recurse with input depth, such as
//! expansion into [`Core`](crate::Core).
//!
//! Each step returns a result, requests a call followed by a continuation, delegates to a tail
//! call, or requests several calls in order. Pending continuations live on a heap-allocated stack.
//! The driver preserves recursive execution order while using a bounded machine stack.

/// The next action over state `S`, where calls of type `C` produce results of type `T`.
pub enum Step<'k, S: ?Sized, C, T, E> {
    Done(T),
    /// Runs a call, then passes its result to the continuation.
    Call(C, Then<'k, S, C, T, E>),
    /// Delegates to a call and returns its result directly.
    Tail(C),
    /// Runs calls in order, then passes all results to the continuation.
    All(Vec<C>, Gathered<'k, S, C, T, E>),
}

/// A continuation that receives a completed call's result.
pub type Then<'k, S, C, T, E> = Box<dyn FnOnce(&mut S, T) -> Result<Step<'k, S, C, T, E>, E> + 'k>;

/// A continuation that receives the results of a completed sequence of calls.
pub type Gathered<'k, S, C, T, E> = Box<dyn FnOnce(&mut S, Vec<T>) -> Result<Step<'k, S, C, T, E>, E> + 'k>;

impl<'k, S: ?Sized, C, T, E> Step<'k, S, C, T, E> {
    /// Schedules `call`, then resumes with `then`.
    pub fn then(call: C, then: impl FnOnce(&mut S, T) -> Result<Self, E> + 'k) -> Self {
        Step::Call(call, Box::new(then))
    }
}

/// Schedules `calls` in order, then passes their results to a continuation that produces the next
/// step.
pub fn all<'k, S: ?Sized, C, T, E>(calls: Vec<C>, then: impl FnOnce(&mut S, Vec<T>) -> Result<Step<'k, S, C, T, E>, E> + 'k) -> Result<Step<'k, S, C, T, E>, E> {
    Ok(Step::All(calls, Box::new(then)))
}

/// A suspended continuation, or the remaining calls and accumulated results of a [`Step::All`].
enum Waiting<'k, S: ?Sized, C, T, E> {
    Then(Then<'k, S, C, T, E>),
    All { calls: std::vec::IntoIter<C>, made: Vec<T>, then: Gathered<'k, S, C, T, E> },
}

/// Runs `call` to completion, using `step` to execute each requested call.
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
