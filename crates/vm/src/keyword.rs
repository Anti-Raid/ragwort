//! Implements keyword procedures, which `lambda` forms with keyword parameters create. A keyword procedure is a [`KeywordProcedure`] object that wraps two procedures:
//!
//! - The `core` procedure takes one argument for each accepted keyword, sorted lexicographically by keyword name, followed by the positional arguments. An optional keyword that the call omits is passed as [`Value::UNSUPPLIED`].
//! - The `plain` procedure is called when the call supplies no keywords. It is `#f` if at least one keyword is required.
//!
//! The `keyword-apply` procedure binds the keyword arguments that a call supplies to the parameters of the core procedure.

use std::cmp::Ordering;

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Keyword;

use crate::Fault;
use crate::passed::Passed;
use crate::frame::Shape;
use crate::machine::{Then, condition};
use crate::objects::{BytecodeFields, Closure, ClosureFields, KeywordProcedure, KeywordProcedureFields};

/// Orders two keywords lexicographically by their string names, matching the behavior of Racket's `keyword<?`.
pub fn order<'gc>(mc: &Mutation<'gc>, left: Keyword<'gc>, right: Keyword<'gc>) -> Ordering {
    let strings = Strings::new(mc);
    string::compare(&strings, left.symbol(mc).name(mc), right.symbol(mc).name(mc)).unwrap_or(Ordering::Equal)
}

/// Returns the signature of procedure `callee` if it is a [`KeywordProcedure`]. The signature is the sorted list of accepted keywords and the [`Shape`] of the positional parameters. Each keyword is paired with a boolean that tells whether it is required.
pub fn signature<'gc>(mc: &Mutation<'gc>, callee: Value<'gc>) -> Option<(Vec<(Keyword<'gc>, bool)>, Shape)> {
    let callee = callee.downcast::<KeywordProcedure>(mc)?;
    let pairs = Pairs::new(mc);
    let required: Vec<Value<'gc>> = pairs.elements(callee.required(mc)).collect();
    let keywords: Vec<_> = pairs.elements(callee.keywords(mc)).map(|keyword| Some((Keyword::of(keyword)?, required.contains(&keyword)))).collect::<Option<_>>()?;
    let mut shape = Shape::of(callee.core(mc).downcast::<Closure>(mc)?.code(mc)?.arity(mc));
    shape.required = shape.required.checked_sub(keywords.len() as u64)?;
    Some((keywords, shape))
}

/// Dispatches a call to keyword procedure `callee` when no keyword arguments are supplied, passing positional `args`.
pub(crate) fn positional<'gc>(mc: &Mutation<'gc>, callee: Gc<'gc, KeywordProcedure>, args: Passed<'gc>) -> Result<Then<'gc>, Fault> {
    match callee.plain(mc) {
        Value::FALSE => apply(mc, Value::object(mc, callee), Value::NULL, Value::NULL, args),
        plain => Ok(Then::Call(plain, args)),
    }
}

/// Implements `(keyword-apply f kws vals arg ...)`: invokes `callee` with keyword arguments `kws` (which must be sorted and distinct) and corresponding values `vals`, followed by positional arguments `args`. Raises a keyword fault if an unexpected keyword is supplied or if a required keyword is missing.
pub(crate) fn apply<'gc>(mc: &Mutation<'gc>, callee: Value<'gc>, kws: Value<'gc>, vals: Value<'gc>, args: Passed<'gc>) -> Result<Then<'gc>, Fault> {
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
    let Some(callee) = callee.downcast::<KeywordProcedure>(mc) else {
        return match given.first() {
            Some(&(kw, _)) => raise(mc, "procedure takes no keywords", kw.value(mc)),
            None => Ok(Then::Call(callee, args)),
        };
    };
    let accepted: Vec<Keyword<'gc>> = pairs.elements(callee.keywords(mc)).map(Keyword::of).collect::<Option<_>>().ok_or(Fault::Malformed)?;
    // Report unknown keywords before missing required ones, as an unexpected keyword often indicates a misspelled parameter name.
    if let Some(&(kw, _)) = given.iter().find(|(kw, _)| !accepted.contains(kw)) {
        return raise(mc, "procedure doesn't take keyword", kw.value(mc));
    }
    let required: Vec<_> = pairs.elements(callee.required(mc)).collect();
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
    Ok(Then::Call(callee.core(mc), Passed::list(list)))
}

fn raise<'gc>(mc: &Mutation<'gc>, message: &str, kw: Value<'gc>) -> Result<Then<'gc>, Fault> {
    let message = string::from_str(&Strings::new(mc), message)?.value();
    let irritants = Pairs::new(mc).cons(kw, Value::NULL)?.value(mc);
    Ok(Then::Raise(condition(mc, Fault::Keyword, message, irritants)?, false))
}
