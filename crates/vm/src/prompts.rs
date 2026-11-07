//! Prompts, as Racket CS builds them over Chez's continuations: a task's continuation is its
//! chain of records, then a list of [`Prompt`]s, its metacontinuation. A prompt keeps the
//! continuation it returns to, and its body runs on an empty one, so the chain only ever runs
//! up to the nearest prompt. When the chain runs out, the prompt on top is popped and its
//! continuation goes on.
//!
//! Capturing up to a prompt takes the chain as it is, and the prompts above that one; calling
//! what's captured puts the current continuation in a prompt of its own and goes on with the
//! captured one. No record is copied for either.

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::objects::{Continuation, ContinuationFields, Prompt, PromptFields, Tag, Task, TaskFields, Winder};
use crate::segments::promote;

/// The default continuation prompt tag.
pub(crate) const fn default_tag<'gc>() -> Value<'gc> {
    Value::from_bits(4 << 32 | 0b1101)
}

/// The key of the marks that hold the procedure a raise calls, or `#f` for none.
pub(crate) const fn handler_key<'gc>() -> Value<'gc> {
    Value::from_bits(5 << 32 | 0b1101)
}

/// Puts the current continuation in a prompt for `tag`, with `handler` for aborts to it, and
/// starts an empty one.
pub(crate) fn push<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>, handler: Value<'gc>) -> Result<(), Fault> {
    let prompt = Prompt::new(mc, tag, handler, task.chain(mc), task.attachments(mc), task.winders(mc))?;
    task.set_prompts(mc, Pairs::new(mc).cons(Value::object(mc, prompt), task.prompts(mc))?.value(mc));
    empty(mc, task);
    Ok(())
}

/// Goes on with the continuation of the prompt on top, for a chain that has run out. Returns
/// `false` if there's none, and the task is done.
pub(crate) fn pop<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<bool, Fault> {
    let Some(cell) = Pair::of(task.prompts(mc)) else { return Ok(false) };
    restore(mc, task, prompt(mc, cell.head(mc))?);
    task.set_prompts(mc, cell.tail(mc));
    Ok(true)
}

/// Drops the continuation up to the nearest prompt for `tag`, and the prompt, so it goes on
/// with that prompt's continuation. Returns the prompt's handler, or `None` for the implicit
/// default prompt at the bottom of the stack.
pub(crate) fn abort<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>) -> Result<Option<Value<'gc>>, Fault> {
    match find(mc, task, tag)? {
        Some(found) => {
            restore(mc, task, found.prompt);
            task.set_prompts(mc, found.under);
            Ok(Some(found.prompt.handler(mc)))
        }
        None => {
            empty(mc, task);
            task.set_prompts(mc, Value::NIL);
            Ok(None)
        }
    }
}

/// The continuation up to the nearest prompt for `tag`, composable or an `escape`. What it holds
/// is only ever copied from then on.
pub(crate) fn capture<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>, escape: bool) -> Result<Value<'gc>, Fault> {
    let prompts = match find(mc, task, tag)? {
        Some(found) => {
            found.above.iter().for_each(|p| promote(mc, p.chain(mc)));
            list(mc, &found.above, Value::NIL)?
        }
        None => {
            let mut at = task.prompts(mc);
            while let Some(cell) = Pair::of(at) {
                promote(mc, prompt(mc, cell.head(mc))?.chain(mc));
                at = cell.tail(mc);
            }
            task.prompts(mc)
        }
    };
    promote(mc, task.chain(mc));
    Ok(Value::object(mc, Continuation::new(mc, task.chain(mc), task.attachments(mc), task.winders(mc), prompts, escape)?))
}

/// Goes on with `k` on top of the current continuation, which a prompt with no tag keeps, unless
/// it's empty, as it is in tail position under a prompt.
pub(crate) fn compose<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, k: Gc<'gc, Continuation>) -> Result<(), Fault> {
    if task.chain(mc) != Value::FALSE || task.attachments(mc) != Value::NIL || task.winders(mc) != Value::NIL {
        push(mc, task, Value::VOID, Value::VOID)?;
    }
    let mut above = Vec::new();
    let mut at = k.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        above.push(prompt(mc, cell.head(mc))?);
        at = cell.tail(mc);
    }
    task.set_prompts(mc, list(mc, &above, task.prompts(mc))?);
    task.set_chain(mc, k.chain(mc));
    task.set_attachments(mc, k.attachments(mc));
    task.set_winders(mc, k.winders(mc));
    Ok(())
}

/// Drops the continuation up to the nearest prompt for the default tag, which stays, as calling
/// an escape continuation does.
pub(crate) fn clear_to_default<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<(), Fault> {
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        if prompt(mc, cell.head(mc))?.tag(mc) == default_tag() {
            break;
        }
        at = cell.tail(mc);
    }
    task.set_prompts(mc, at);
    empty(mc, task);
    Ok(())
}

/// The value of the nearest mark for `key`, in the current continuation or under any prompt,
/// or `default` if there's none.
pub(crate) fn mark<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, key: Value<'gc>, default: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if let Some(value) = nearest(mc, task.attachments(mc), key)? {
        return Ok(value);
    }
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        if let Some(value) = nearest(mc, prompt(mc, cell.head(mc))?.attachments(mc), key)? {
            return Ok(value);
        }
        at = cell.tail(mc);
    }
    Ok(default)
}

/// The value of the nearest mark for `key` up to the nearest prompt, or `default`.
pub(crate) fn frame_mark<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, key: Value<'gc>, default: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(nearest(mc, task.attachments(mc), key)?.unwrap_or(default))
}

/// The value of the nearest mark for `key` in each prompt's part of the continuation, innermost
/// first, or `default` for a part with none: from the current part to the one just inside the
/// nearest prompt for `tag`, or to the bottom if it's `None`.
pub(crate) fn part_marks<'gc>(
    mc: &Mutation<'gc>,
    task: Gc<'gc, Task>,
    key: Value<'gc>,
    default: Value<'gc>,
    tag: Option<Value<'gc>>,
) -> Result<Value<'gc>, Fault> {
    nearest_each(mc, &parts(mc, task, tag)?, key, default)
}

/// The [`Winder`]s of the continuation of `task`, up to the nearest prompt for `tag` or all of
/// them, innermost first, each with the list of those outside it in its prompt's part.
pub(crate) fn winds<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Option<Value<'gc>>) -> Result<Vec<Wind<'gc>>, Fault> {
    winds_in(mc, task.winders(mc), task.prompts(mc), tag)
}

/// [`winds`] of the continuation `k`, all of it.
pub(crate) fn winds_of<'gc>(mc: &Mutation<'gc>, k: Gc<'gc, Continuation>) -> Result<Vec<Wind<'gc>>, Fault> {
    winds_in(mc, k.winders(mc), k.prompts(mc), None)
}

/// The winds of the first `parts` prompt parts of the continuation of `task`, then those of the
/// next part down to the list `winders`, whose own stay.
pub(crate) fn winds_above<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, parts: usize, winders: Value<'gc>) -> Result<Vec<Wind<'gc>>, Fault> {
    let (mut winds, mut at, mut prompts) = (Vec::new(), task.winders(mc), task.prompts(mc));
    for part in 0..=parts {
        let stop = if part == parts { winders } else { Value::NIL };
        while at != stop {
            let cell = Pair::of(at).ok_or(Fault::Malformed)?;
            winds.push((cell.head(mc).downcast::<Winder>(mc).ok_or(Fault::Malformed)?, cell.tail(mc)));
            at = cell.tail(mc);
        }
        if part < parts {
            let cell = Pair::of(prompts).ok_or(Fault::Malformed)?;
            (at, prompts) = (prompt(mc, cell.head(mc))?.winders(mc), cell.tail(mc));
        }
    }
    Ok(winds)
}

/// A [`Winder`], and the list of those outside it in its prompt's part of the continuation.
pub(crate) type Wind<'gc> = (Gc<'gc, Winder>, Value<'gc>);

/// The winds of `winders`, then of those under each of `prompts`, up to the nearest prompt for
/// `tag`, or all of them.
fn winds_in<'gc>(mc: &Mutation<'gc>, mut winders: Value<'gc>, mut prompts: Value<'gc>, tag: Option<Value<'gc>>) -> Result<Vec<Wind<'gc>>, Fault> {
    let mut winds = Vec::new();
    loop {
        while let Some(cell) = Pair::of(winders) {
            winds.push((cell.head(mc).downcast::<Winder>(mc).ok_or(Fault::Malformed)?, cell.tail(mc)));
            winders = cell.tail(mc);
        }
        let Some(cell) = Pair::of(prompts) else { break };
        let prompt = prompt(mc, cell.head(mc))?;
        if tag.is_some_and(|tag| prompt.tag(mc) == tag) {
            return Ok(winds);
        }
        (winders, prompts) = (prompt.winders(mc), cell.tail(mc));
    }
    match tag {
        Some(tag) if tag != default_tag() => Err(Fault::NoPrompt),
        _ => Ok(winds),
    }
}

/// The marks of each prompt's part of the continuation of `task`, innermost first, up to the
/// nearest prompt for `tag`, or all of them.
fn parts<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Option<Value<'gc>>) -> Result<Vec<Value<'gc>>, Fault> {
    let mut parts = vec![task.attachments(mc)];
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        let prompt = prompt(mc, cell.head(mc))?;
        if tag.is_some_and(|tag| prompt.tag(mc) == tag) {
            return Ok(parts);
        }
        parts.push(prompt.attachments(mc));
        at = cell.tail(mc);
    }
    match tag {
        Some(tag) if tag != default_tag() => Err(Fault::NoPrompt),
        _ => Ok(parts),
    }
}

fn nearest<'gc>(mc: &Mutation<'gc>, mut marks: Value<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Fault> {
    while let Some(cell) = Pair::of(marks) {
        let mark = Pair::of(cell.head(mc)).ok_or(Fault::Malformed)?;
        if mark.head(mc) == key {
            return Ok(Some(mark.tail(mc)));
        }
        marks = cell.tail(mc);
    }
    Ok(None)
}

fn nearest_each<'gc>(mc: &Mutation<'gc>, parts: &[Value<'gc>], key: Value<'gc>, default: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut list = Value::NIL;
    for &marks in parts.iter().rev() {
        list = pairs.cons(nearest(mc, marks, key)?.unwrap_or(default), list)?.value(mc);
    }
    Ok(list)
}

/// `value`, if it's a prompt tag.
pub(crate) fn tag_of<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if value == default_tag() || value.downcast::<Tag>(mc).is_some() {
        Ok(value)
    } else {
        Err(Fault::WrongType)
    }
}

/// The nearest prompt for a tag, the ones above it, and the list under it.
struct Found<'gc> {
    above: Vec<Gc<'gc, Prompt>>,
    prompt: Gc<'gc, Prompt>,
    under: Value<'gc>,
}

fn find<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>) -> Result<Option<Found<'gc>>, Fault> {
    let mut above = Vec::new();
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        let prompt = prompt(mc, cell.head(mc))?;
        if prompt.tag(mc) == tag {
            return Ok(Some(Found { above, prompt, under: cell.tail(mc) }));
        }
        above.push(prompt);
        at = cell.tail(mc);
    }
    if tag == default_tag() {
        return Ok(None);
    }
    Err(Fault::NoPrompt)
}

fn restore<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, prompt: Gc<'gc, Prompt>) {
    task.set_chain(mc, prompt.chain(mc));
    task.set_attachments(mc, prompt.attachments(mc));
    task.set_winders(mc, prompt.winders(mc));
}

/// Starts an empty continuation, up to the nearest prompt.
fn empty<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) {
    task.set_chain(mc, Value::FALSE);
    task.set_attachments(mc, Value::NIL);
    task.set_winders(mc, Value::NIL);
}

fn prompt<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Gc<'gc, Prompt>, Fault> {
    value.downcast::<Prompt>(mc).ok_or(Fault::Malformed)
}

/// `prompts`, innermost first, on top of the list `under`.
fn list<'gc>(mc: &Mutation<'gc>, prompts: &[Gc<'gc, Prompt>], under: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut list = under;
    for &prompt in prompts.iter().rev() {
        list = pairs.cons(Value::object(mc, prompt), list)?.value(mc);
    }
    Ok(list)
}
