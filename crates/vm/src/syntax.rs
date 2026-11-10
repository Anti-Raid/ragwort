//! Syntax objects, as the intrinsics that take them apart and make them see them: what the reader
//! makes, and what the expander hands a macro's transformer. A list's syntax holds a list of
//! syntax, and a vector's a vector of it; an identifier's holds a symbol, and its scopes.

use ragwort_types::gc::{Charge, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxContext, SyntaxKind, SyntaxMeta, SyntaxScope, SyntaxSpan};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::equal::PER_FUEL;
use crate::op::Fuel;

pub(crate) fn is_identifier<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> bool {
    Syntax::of(x).is_some_and(|s| s.kind(mc) == Some(SyntaxKind::Identifier))
}

/// What `x` wraps: a symbol, a list or vector of syntax, or a literal.
pub(crate) fn unwrap<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Syntax::of(x).ok_or(Fault::WrongType)?.datum(mc))
}

/// The datum `x` stands for: its syntax unwrapped, all the way down.
pub(crate) fn to_datum<'gc>(mc: &Mutation<'gc>, x: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let mut walk = Walk::new(mc, *fuel);
    let mut todo = vec![Step::Visit(x)];
    while let Some(step) = todo.pop() {
        let x = match step {
            Step::Visit(x) => x,
            Step::List(n, tail) => {
                walk.list(mc, n, tail, None)?;
                continue;
            }
            Step::Vector(n) => {
                walk.vector(mc, n, None)?;
                continue;
            }
        };
        walk.charge(1)?;
        let x = Syntax::of(x).map_or(x, |s| s.datum(mc));
        if Pair::of(x).is_some() {
            let at = todo.len();
            let mut rest = x;
            let mut n = 0;
            while let Some(pair) = Pair::of(rest) {
                walk.charge(1)?;
                todo.push(Step::Visit(pair.head(mc)));
                rest = Syntax::of(pair.tail(mc)).map_or(pair.tail(mc), |s| s.datum(mc));
                n += 1;
            }
            let tail = rest != Value::NIL;
            if tail {
                todo.push(Step::Visit(rest));
            }
            todo.push(Step::List(n, tail));
            todo[at..].reverse();
            walk.fit(todo.len())?;
        } else if let Some(vector) = AnyVector::of(x) {
            let at = todo.len();
            todo.extend((0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).map(Step::Visit));
            todo.push(Step::Vector(todo.len() - at));
            todo[at..].reverse();
            walk.fit(todo.len())?;
        } else {
            walk.done.push(x);
        }
    }
    walk.finish(fuel)
}

/// What's left to do in walking data: a value to visit, or a list or vector to make of the
/// last values made, `n` of them, and a tail after them if the list has one.
enum Step<'gc> {
    Visit(Value<'gc>),
    List(usize, bool),
    Vector(usize),
}

/// The values a walk of data has made, and what it's spent, which it charges as it goes, so
/// one of data that contains itself runs out of fuel, and the room its stacks take, which it
/// charges to the arena's budget, so one with fuel to spare runs out of that.
struct Walk<'gc> {
    done: Vec<Value<'gc>>,
    count: u64,
    most: u64,
    room: usize,
    charge: Charge<'gc>,
}

impl<'gc> Walk<'gc> {
    fn new(mc: &Mutation<'gc>, fuel: Fuel) -> Self {
        Self { done: Vec::new(), count: 0, most: fuel.left().saturating_mul(PER_FUEL), room: 0, charge: mc.charge() }
    }

    /// Charges for room for `todo` steps still to take and the values made so far.
    fn fit(&mut self, todo: usize) -> Result<(), Fault> {
        let needed = todo + self.done.len();
        if needed > self.room {
            let room = needed.max(self.room * 2).max(64);
            self.charge.grow((room - self.room) * size_of::<Step>())?;
            self.room = room;
        }
        Ok(())
    }

    fn charge(&mut self, n: u64) -> Result<(), Fault> {
        self.count = self.count.saturating_add(n);
        if self.count > self.most { Err(Fault::OutOfFuel) } else { Ok(()) }
    }

    /// A list of the last `n` values made, after the tail before them if `tail`, as syntax of
    /// `meta` if any.
    fn list(&mut self, mc: &Mutation<'gc>, n: usize, tail: bool, meta: Option<(SyntaxSpan<'gc>, SyntaxMeta<'gc>)>) -> Result<(), Fault> {
        let tail = if tail { self.done.pop().expect("a tail") } else { Value::NIL };
        let items = self.done.split_off(self.done.len() - n);
        let list = Pairs::new(mc).list_with_tail(items, tail)?;
        self.made(mc, list, meta)
    }

    fn vector(&mut self, mc: &Mutation<'gc>, n: usize, meta: Option<(SyntaxSpan<'gc>, SyntaxMeta<'gc>)>) -> Result<(), Fault> {
        let items = self.done.split_off(self.done.len() - n);
        let vector = Vectors::new(mc).immutable_from_slice(&items)?.value(mc);
        self.made(mc, vector, meta)
    }

    fn made(&mut self, mc: &Mutation<'gc>, datum: Value<'gc>, meta: Option<(SyntaxSpan<'gc>, SyntaxMeta<'gc>)>) -> Result<(), Fault> {
        let made = match meta {
            Some((span, meta)) => Syntax::new(mc, datum, span, Some(meta))?.value(mc),
            None => datum,
        };
        self.done.push(made);
        Ok(())
    }

    fn finish(mut self, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        fuel.spend(self.count / PER_FUEL)?;
        Ok(self.done.pop().expect("the root's made"))
    }
}

/// `datum` as syntax, with the scopes and span of `context`, syntax or `#f` for none: its
/// symbols as identifiers, and its pairs and vectors as lists and vectors of syntax. What's
/// syntax already stays as it is.
pub(crate) fn to_syntax<'gc>(mc: &Mutation<'gc>, context: Value<'gc>, datum: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let (scopes, span) = match Syntax::of(context) {
        Some(s) => (s.context(mc), s.span(mc)),
        None if context == Value::FALSE => (None, SyntaxSpan::default()),
        None => return Err(Fault::WrongType),
    };
    let meta = |kind| SyntaxMeta::new(mc, kind, scopes, None);
    let named = Syntax::of(context).filter(|_| is_identifier(mc, context)).and_then(|s| Some((s.datum(mc), s.binding(mc)?)));
    let (id, list, vector) = (meta(SyntaxKind::Identifier)?, meta(SyntaxKind::List)?, meta(SyntaxKind::Vector)?);
    let mut walk = Walk::new(mc, *fuel);
    let mut todo = vec![Step::Visit(datum)];
    while let Some(step) = todo.pop() {
        let x = match step {
            Step::Visit(x) => x,
            Step::List(n, tail) => {
                walk.list(mc, n, tail, Some((span, list)))?;
                continue;
            }
            Step::Vector(n) => {
                walk.vector(mc, n, Some((span, vector)))?;
                continue;
            }
        };
        walk.charge(1)?;
        if Syntax::of(x).is_some() {
            walk.done.push(x);
        } else if Symbol::of(x).is_some() {
            let binding = named.filter(|&(name, _)| name == x).map(|(_, binding)| binding);
            walk.done.push(Syntax::bound(mc, x, span, Some(id), binding)?.value(mc));
        } else if Pair::of(x).is_some() {
            let at = todo.len();
            let (mut rest, mut n) = (x, 0);
            while let Some(pair) = Pair::of(rest) {
                walk.charge(1)?;
                todo.push(Step::Visit(pair.head(mc)));
                rest = pair.tail(mc);
                n += 1;
            }
            let tail = rest != Value::NIL;
            if tail {
                todo.push(Step::Visit(rest));
            }
            todo.push(Step::List(n, tail));
            todo[at..].reverse();
            walk.fit(todo.len())?;
        } else if let Some(v) = AnyVector::of(x) {
            let at = todo.len();
            todo.extend((0..v.len(mc)).filter_map(|i| v.get(mc, i)).map(Step::Visit));
            todo.push(Step::Vector(todo.len() - at));
            todo[at..].reverse();
            walk.fit(todo.len())?;
        } else {
            walk.done.push(Syntax::new(mc, x, span, None)?.value(mc));
        }
    }
    walk.finish(fuel)
}

/// Whether the identifiers `a` and `b` have the same name and scopes, so that a binding of one
/// would bind the other.
pub(crate) fn same_identifier<'gc>(mc: &Mutation<'gc>, a: Value<'gc>, b: Value<'gc>, fuel: &mut Fuel) -> Result<bool, Fault> {
    if !is_identifier(mc, a) || !is_identifier(mc, b) {
        return Err(Fault::WrongType);
    }
    let (a, b) = (Syntax::of(a).ok_or(Fault::WrongType)?, Syntax::of(b).ok_or(Fault::WrongType)?);
    if a.datum(mc) != b.datum(mc) {
        return Ok(false);
    }
    let scopes = |c: Option<SyntaxContext<'gc>>| c.map(|c| c.scopes(mc).collect::<Vec<_>>()).unwrap_or_default();
    let (x, y) = (a.context(mc), b.context(mc));
    if x == y {
        return Ok(true);
    }
    let (x, y) = (scopes(x), scopes(y));
    // Contexts made apart can list the same scopes in another order.
    if x.len() != y.len() || x == y {
        return Ok(x == y);
    }
    let compared = (x.len() as u64).saturating_mul(y.len() as u64);
    fuel.spend(compared / PER_FUEL)?;
    Ok(x.iter().all(|scope| y.contains(scope)))
}

/// Whether the identifiers `a` and `b` refer to the same binding. The expander gives what it
/// makes a value standing for its binding: an object of the binding's own, a keyword's name, or
/// for a module's variable, or a name it doesn't bind, a pair of the module's name and the name
/// the module gives it.
pub(crate) fn same_binding<'gc>(mc: &Mutation<'gc>, a: Value<'gc>, b: Value<'gc>) -> Result<bool, Fault> {
    if !is_identifier(mc, a) || !is_identifier(mc, b) {
        return Err(Fault::WrongType);
    }
    let (a, b) = (Syntax::of(a).ok_or(Fault::WrongType)?, Syntax::of(b).ok_or(Fault::WrongType)?);
    Ok(match (a.binding(mc), b.binding(mc)) {
        (Some(x), Some(y)) => match (Pair::of(x), Pair::of(y)) {
            (Some(x), Some(y)) => x.head(mc) == y.head(mc) && x.tail(mc) == y.tail(mc),
            _ => x == y,
        },
        (None, None) => a.datum(mc) == b.datum(mc),
        _ => false,
    })
}

/// An identifier for each element of `list`, each in a new scope of its own: named as the
/// element is if it's an identifier, or else `name`, a symbol, and where it is if it's syntax.
pub(crate) fn temporaries<'gc>(mc: &Mutation<'gc>, list: Value<'gc>, name: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    if Symbol::of(name).is_none() {
        return Err(Fault::WrongType);
    }
    let (mut temporaries, mut at) = (Vec::new(), list);
    loop {
        if let Some(pair) = Pair::of(at) {
            let item = pair.head(mc);
            let syntax = Syntax::of(item);
            let named = if is_identifier(mc, item) { syntax.map_or(name, |s| s.datum(mc)) } else { name };
            let context = SyntaxContext::new(mc, &[SyntaxScope::new(mc)?])?;
            let meta = SyntaxMeta::new(mc, SyntaxKind::Identifier, Some(context), None)?;
            let span = syntax.map(|s| s.span(mc)).unwrap_or_default();
            temporaries.push(Syntax::new(mc, named, span, Some(meta))?.value(mc));
            at = pair.tail(mc);
        } else if let Some(rest) = Syntax::of(at).filter(|s| s.kind(mc) == Some(SyntaxKind::List)) {
            at = rest.datum(mc);
        } else if at == Value::NIL {
            break;
        } else {
            return Err(Fault::WrongType);
        }
    }
    fuel.spend(temporaries.len() as u64 / PER_FUEL)?;
    Ok(Pairs::new(mc).list(&temporaries)?)
}
