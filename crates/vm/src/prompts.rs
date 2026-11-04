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
use crate::objects::{Continuation, ContinuationFields, Prompt, PromptFields, Tag, Task, TaskFields};
use crate::segments::promote;

/// Puts the current continuation in a prompt for `tag`, with `handler` for aborts to it, and
/// starts an empty one.
pub(crate) fn push<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>, handler: Value<'gc>) -> Result<(), Fault> {
    let prompt = Prompt::new(mc, tag, handler, task.chain(mc), task.attachments(mc))?;
    task.set_prompts(mc, Pairs::new(mc).cons(Value::object(mc, prompt), task.prompts(mc))?.value(mc));
    task.set_chain(mc, Value::FALSE);
    task.set_attachments(mc, Value::NIL);
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
/// with that prompt's continuation. Returns the prompt's handler.
pub(crate) fn abort<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let found = find(mc, task, tag)?;
    restore(mc, task, found.prompt);
    task.set_prompts(mc, found.under);
    Ok(found.prompt.handler(mc))
}

/// The composable continuation up to the nearest prompt for `tag`. What it holds is only ever
/// copied from then on.
pub(crate) fn capture<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let above = find(mc, task, tag)?.above;
    promote(mc, task.chain(mc));
    above.iter().for_each(|p| promote(mc, p.chain(mc)));
    let prompts = list(mc, &above, Value::NIL)?;
    Ok(Value::object(mc, Continuation::new(mc, task.chain(mc), prompts)?))
}

/// Goes on with `k` on top of the current continuation, which a prompt with no tag keeps, unless
/// it's empty, as it is in tail position under a prompt.
pub(crate) fn compose<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, k: Gc<'gc, Continuation>) -> Result<(), Fault> {
    if task.chain(mc) != Value::FALSE || task.attachments(mc) != Value::NIL {
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
    task.set_attachments(mc, Value::NIL);
    Ok(())
}

/// The value of the nearest mark for `key`, in the current continuation or under any prompt,
/// or `default` if there's none.
pub(crate) fn mark<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, key: Value<'gc>, default: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let find = |mut marks: Value<'gc>| -> Result<Option<Value<'gc>>, Fault> {
        while let Some(cell) = Pair::of(marks) {
            let mark = Pair::of(cell.head(mc)).ok_or(Fault::Malformed)?;
            if mark.head(mc) == key {
                return Ok(Some(mark.tail(mc)));
            }
            marks = cell.tail(mc);
        }
        Ok(None)
    };
    if let Some(value) = find(task.attachments(mc))? {
        return Ok(value);
    }
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        if let Some(value) = find(prompt(mc, cell.head(mc))?.attachments(mc))? {
            return Ok(value);
        }
        at = cell.tail(mc);
    }
    Ok(default)
}

/// `value`, if it's a prompt tag.
pub(crate) fn tag_of<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Value<'gc>, Fault> {
    value.downcast::<Tag>(mc).map(|_| value).ok_or(Fault::WrongType)
}

/// The nearest prompt for a tag, the ones above it, and the list under it.
struct Found<'gc> {
    above: Vec<Gc<'gc, Prompt>>,
    prompt: Gc<'gc, Prompt>,
    under: Value<'gc>,
}

fn find<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, tag: Value<'gc>) -> Result<Found<'gc>, Fault> {
    let mut above = Vec::new();
    let mut at = task.prompts(mc);
    while let Some(cell) = Pair::of(at) {
        let prompt = prompt(mc, cell.head(mc))?;
        if prompt.tag(mc) == tag {
            return Ok(Found { above, prompt, under: cell.tail(mc) });
        }
        above.push(prompt);
        at = cell.tail(mc);
    }
    Err(Fault::NoPrompt)
}

fn restore<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, prompt: Gc<'gc, Prompt>) {
    task.set_chain(mc, prompt.chain(mc));
    task.set_attachments(mc, prompt.attachments(mc));
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
