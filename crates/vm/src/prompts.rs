//! Delimited continuation prompts, structured as in Racket CS on Chez Scheme. A task's full
//! continuation consists of its active chain of frame records followed by a list of [`Prompt`]s (the
//! metacontinuation). Each prompt encapsulates the continuation to which it returns, while its inner
//! body executes with an empty continuation chain, ensuring the active chain extends only to the
//! nearest prompt. When the chain underflows, the topmost prompt is popped and its outer continuation
//! resumes.
//!
//! Capturing a continuation up to a prompt extracts the active chain along with any intermediate
//! prompts above the target. Invoking a captured composable continuation encloses the caller's
//! continuation in a fresh prompt and reinstates the captured segments without copying records.

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::objects::{Continuation, ContinuationFields, Prompt, PromptFields, Tag, Task, TaskFields, Winder};
use crate::segments::promote;

/// Returns the default continuation prompt tag used by root prompts and `call/cc`.
pub(crate) const fn default_tag<'gc>() -> Value<'gc> {
    Value::from_bits(4 << 32 | 0b1101)
}

/// Returns the continuation mark key used to store active exception handlers (or `#f` if none are
/// installed).
pub(crate) const fn handler_key<'gc>() -> Value<'gc> {
    Value::from_bits(5 << 32 | 0b1101)
}

/// Pushes a delimited prompt for `tag` with the specified abort `handler` onto the metacontinuation,
/// saving the active continuation and starting an empty continuation chain for the prompt's body.
pub(crate) fn push<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>, handler: Value<'gc>) -> Result<(), Fault> {
    let prompt = Prompt::new(mc, tag, handler, task.chain(mc), task.attachments(mc), task.winders(mc))?;
    task.set_prompts(mc, Pairs::new(mc).cons(Value::object(mc, prompt), task.prompts(mc))?.value(mc));
    empty(mc, task);
    Ok(())
}

/// Pops the topmost prompt and reinstates its continuation when the active continuation chain
/// exhausts. Returns `Ok(false)` if no prompts remain, indicating the task has completed.
pub(crate) fn pop<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) -> Result<bool, Fault> {
    let Some(cell) = Pair::of(task.prompts(mc)) else { return Ok(false) };
    restore(mc, task, prompt(mc, cell.head(mc))?);
    task.set_prompts(mc, cell.tail(mc));
    Ok(true)
}

/// Aborts to the nearest prompt matching `tag`, discarding the delimited continuation up to and
/// including that prompt, and resuming the prompt's outer continuation. Returns the prompt's handler
/// procedure, or `None` if aborting to the root default prompt.
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

/// Captures the delimited continuation up to the nearest prompt matching `tag` as either a composable
/// continuation or an escape continuation. Promotes captured one-shot records so they are copied on
/// subsequent multi-shot resumptions.
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

/// Composes continuation `k` on top of the current continuation. Preserves the active continuation in
/// an untagged prompt unless the current continuation is already empty (such as in tail position under
/// a prompt).
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

/// Discards all continuation frames and intermediate prompts up to the nearest default prompt while
/// leaving that default prompt intact, matching escape continuation invocation behavior.
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

/// Retrieves the value of the nearest continuation mark associated with `key` across all prompt
/// segments, returning `default` if no matching mark is found.
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

/// Retrieves the value of the nearest continuation mark for `key` within the current prompt slice (up
/// to the nearest prompt boundary), or returns `default` if absent.
pub(crate) fn frame_mark<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, key: Value<'gc>, default: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(nearest(mc, task.attachments(mc), key)?.unwrap_or(default))
}

/// Collects the nearest mark for `key` within each prompt segment (innermost first) up to the prompt
/// matching `tag` (or to the bottom of the stack if `tag` is `None`), substituting `default` for
/// segments containing no mark for `key`.
pub(crate) fn part_marks<'gc>(
    mc: &Mutation<'gc>,
    task: Gc<'gc, Task>,
    key: Value<'gc>,
    default: Value<'gc>,
    tag: Option<Value<'gc>>,
) -> Result<Value<'gc>, Fault> {
    nearest_each(mc, &parts(mc, task, tag)?, key, default)
}

/// Collects all active [`Winder`]s in `task` up to the nearest prompt matching `tag` (or all winders
/// if `tag` is `None`), ordered innermost first, pairing each winder with the enclosing winders in its
/// prompt segment.
pub(crate) fn winds<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Option<Value<'gc>>) -> Result<Vec<Wind<'gc>>, Fault> {
    winds_in(mc, task.winders(mc), task.prompts(mc), tag)
}

/// Retrieves the complete list of [`Winder`] pairs throughout continuation `k`.
pub(crate) fn winds_of<'gc>(mc: &Mutation<'gc>, k: Gc<'gc, Continuation>) -> Result<Vec<Wind<'gc>>, Fault> {
    winds_in(mc, k.winders(mc), k.prompts(mc), None)
}

/// Collects winders across the innermost `parts` prompt segments of `task`, plus the winders of the
/// subsequent segment down to `winders` (retaining the entries in `winders` themselves).
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

/// Represents a [`Winder`] paired with the list of outer winders enclosing it within its prompt
/// segment.
pub(crate) type Wind<'gc> = (Gc<'gc, Winder>, Value<'gc>);

/// Gathers winders starting from `winders` and descending through enclosing `prompts` up to the
/// nearest prompt matching `tag` (or through all prompts if `tag` is `None`).
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

/// Extracts the continuation marks from each prompt segment of `task` (innermost first) up to the
/// prompt matching `tag`, or across all prompts if `tag` is `None`.
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

/// Validates that `value` is a valid continuation prompt tag (either the default tag or a `Tag`
/// object), returning it or `Err(Fault::WrongType)`.
pub(crate) fn tag_of<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if value == default_tag() || value.downcast::<Tag>(mc).is_some() {
        Ok(value)
    } else {
        Err(Fault::WrongType)
    }
}

/// Search result locating a target prompt: contains the prompt itself, intermediate prompts above it,
/// and the remaining prompt list below it.
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

/// Clears the active continuation chain, marks, and winders in `task`, establishing an empty
/// delimited continuation up to the nearest prompt.
fn empty<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>) {
    task.set_chain(mc, Value::FALSE);
    task.set_attachments(mc, Value::NIL);
    task.set_winders(mc, Value::NIL);
}

fn prompt<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Gc<'gc, Prompt>, Fault> {
    value.downcast::<Prompt>(mc).ok_or(Fault::Malformed)
}

/// Constructs a Scheme list prepending `prompts` (innermost first) onto the tail list `under`.
fn list<'gc>(mc: &Mutation<'gc>, prompts: &[Gc<'gc, Prompt>], under: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut list = under;
    for &prompt in prompts.iter().rev() {
        list = pairs.cons(Value::object(mc, prompt), list)?.value(mc);
    }
    Ok(list)
}
