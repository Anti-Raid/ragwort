//! Implements keyword procedures created by `lambda` forms with keyword parameters. Represented by [`KeywordProcedure`], which wraps two procedures: a `core` procedure (which takes arguments corresponding to all accepted keywords sorted lexicographically by name—substituting [`Value::UNSUPPLIED`] for omitted optional keywords—followed by positional arguments) and a `plain` procedure (called when no keywords are supplied, or `#f` if at least one keyword is required). The `keyword-apply` procedure dynamically binds a call's supplied keyword arguments to the core procedure's parameter list.

use std::cmp::Ordering;

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Keyword;

use crate::Fault;
use crate::args::Args;
use crate::frame::Shape;
use crate::machine::{Then, condition};
use crate::objects::{BytecodeFields, Closure, ClosureFields, KeywordProcedure, KeywordProcedureFields};

/// Orders two keywords lexicographically by their string names, matching the behavior of Racket's `keyword<?`.
pub fn order<'gc>(mc: &Mutation<'gc>, a: Keyword<'gc>, b: Keyword<'gc>) -> Ordering {
    let strings = Strings::new(mc);
    string::compare(&strings, a.symbol(mc).name(mc), b.symbol(mc).name(mc)).unwrap_or(Ordering::Equal)
}

/// Returns the signature of procedure `f` if it is a [`KeywordProcedure`]: a sorted list of accepted keywords (each paired with a boolean indicating whether it is required) and the [`Shape`] of its positional parameters.
pub fn signature<'gc>(mc: &Mutation<'gc>, f: Value<'gc>) -> Option<(Vec<(Keyword<'gc>, bool)>, Shape)> {
    let f = f.downcast::<KeywordProcedure>(mc)?;
    let pairs = Pairs::new(mc);
    let required: Vec<Value<'gc>> = pairs.elements(f.required(mc)).collect();
    let keywords: Vec<_> = pairs.elements(f.keywords(mc)).map(|k| Some((Keyword::of(k)?, required.contains(&k)))).collect::<Option<_>>()?;
    let mut shape = Shape::of(f.core(mc).downcast::<Closure>(mc)?.code(mc)?.arity(mc));
    shape.required = shape.required.checked_sub(keywords.len() as u64)?;
    Some((keywords, shape))
}

/// Dispatches a call to keyword procedure `f` when no keyword arguments are supplied, passing positional `args`.
pub(crate) fn positional<'gc>(mc: &Mutation<'gc>, f: Gc<'gc, KeywordProcedure>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
    match f.plain(mc) {
        Value::FALSE => apply(mc, Value::object(mc, f), Value::NIL, Value::NIL, args),
        plain => Ok(Then::Call(plain, args)),
    }
}

/// Implements `(keyword-apply f kws vals arg ...)`: invokes `f` with keyword arguments `kws` (which must be sorted and distinct) and corresponding values `vals`, followed by positional arguments `args`. Raises a keyword fault if an unexpected keyword is supplied or if a required keyword is missing.
pub(crate) fn apply<'gc>(mc: &Mutation<'gc>, f: Value<'gc>, kws: Value<'gc>, vals: Value<'gc>, args: Args<'gc>) -> Result<Then<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut given = Vec::new();
    for (kw, val) in pairs.elements(kws).zip(pairs.elements(vals)) {
        let kw = Keyword::of(kw).ok_or(Fault::WrongType)?;
        if given.last().is_some_and(|&(last, _)| order(mc, last, kw).is_ge()) {
            return raise(mc, "keywords must be sorted and distinct", kw.value(mc));
        }
        given.push((kw, val));
    }
    if pairs.list_len(kws) != Some(given.len() as u64) || pairs.list_len(vals) != Some(given.len() as u64) {
        return Err(Fault::WrongType);
    }
    let Some(f) = f.downcast::<KeywordProcedure>(mc) else {
        return match given.first() {
            Some(&(kw, _)) => raise(mc, "procedure takes no keywords", kw.value(mc)),
            None => Ok(Then::Call(f, args)),
        };
    };
    let accepted: Vec<Keyword<'gc>> = pairs.elements(f.keywords(mc)).map(Keyword::of).collect::<Option<_>>().ok_or(Fault::Malformed)?;
    // Report unknown keywords before missing required ones, as an unexpected keyword often indicates a misspelled parameter name.
    if let Some(&(kw, _)) = given.iter().find(|(kw, _)| !accepted.contains(kw)) {
        return raise(mc, "procedure doesn't take keyword", kw.value(mc));
    }
    let required: Vec<_> = pairs.elements(f.required(mc)).collect();
    let mut given = given.into_iter().peekable();
    let mut values = Vec::with_capacity(accepted.len());
    for accepted in accepted {
        match given.next_if(|&(kw, _)| kw == accepted) {
            Some((_, val)) => values.push(val),
            None if required.contains(&accepted.value(mc)) => return raise(mc, "missing required keyword", accepted.value(mc)),
            None => values.push(Value::UNSUPPLIED),
        }
    }
    let list = pairs.list_with_tail(values, args.to_list(mc)?)?;
    Ok(Then::Call(f.core(mc), Args::list(list)))
}

fn raise<'gc>(mc: &Mutation<'gc>, message: &str, kw: Value<'gc>) -> Result<Then<'gc>, Fault> {
    let message = string::from_str(&Strings::new(mc), message)?.value();
    let irritants = Pairs::new(mc).cons(kw, Value::NIL)?.value(mc);
    Ok(Then::Raise(condition(mc, Fault::Keyword, message, irritants)?, false))
}
