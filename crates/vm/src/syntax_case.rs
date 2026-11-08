//! `syntax-case`'s patterns and `syntax`'s templates, as values code holds as constants:
//! [`SyntaxPattern`]s, which `syntax-match` matches syntax with, giving a vector of what their
//! variables matched, a list of those for each ellipsis a variable's under, and
//! [`SyntaxTemplate`]s, which `syntax-build` makes syntax of, from what its pattern variables
//! matched. Each is a shape, with the syntax and data it refers to in its items, by index.
//!
//! What's matched and made is a transformer's syntax: lists of syntax, or the syntax of lists, as
//! a pattern's rest is a list of the rest of the syntax it matched.

use std::ops::Range;

use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::syntax::{Syntax, SyntaxKind};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::equal::{self, PER_FUEL};
use crate::objects::{SyntaxPattern, SyntaxPatternFields, SyntaxTemplate, SyntaxTemplateFields};
use crate::op::Fuel;
use crate::syntax;

/// A pattern, its literals and data the items of the [`SyntaxPattern`] it's in.
#[derive(Clone, Debug)]
pub enum Pattern {
    /// `_`.
    Any,
    /// The variable matched into this slot.
    Var(u32),
    /// An identifier that refers to what the identifier in this item does.
    Literal(u32),
    /// A datum `equal?` to the one in this item.
    Datum(u32),
    /// A list, or a vector, of items that match `before`, then any number that match `repeat`,
    /// then items that match `after`, and for a list, what's left matching `tail`, or nothing.
    Seq { before: Box<[Pattern]>, repeat: Option<Box<Repeat>>, after: Box<[Pattern]>, tail: Option<Box<Pattern>>, vector: bool },
}

/// A pattern under an ellipsis, and the slots of its variables.
#[derive(Clone, Debug)]
pub struct Repeat {
    pub each: Pattern,
    pub slots: Range<u32>,
}

/// A pattern, and how many variables it has.
#[derive(Clone, Debug)]
pub struct PatternShape {
    pub pattern: Pattern,
    pub vars: u32,
}

/// A template, its constants the items of the [`SyntaxTemplate`] it's in.
#[derive(Clone, Debug)]
pub enum Template {
    /// The syntax in this item.
    Const(u32),
    /// What the variable passed in this place matched.
    Var(u32),
    /// A list or vector of items, a tail for a list, made with the scopes and span of the
    /// syntax in item `like`.
    Seq { items: Box<[Item]>, tail: Option<Box<Template>>, vector: bool, like: u32 },
}

/// An item of a list or vector template, made once for each match of the pattern variables in
/// it under `ellipses` ellipses, which are in `slots`.
#[derive(Clone, Debug)]
pub struct Item {
    pub template: Template,
    pub ellipses: u32,
    pub slots: Box<[u32]>,
}

/// A template, and how many ellipses each pattern variable it's passed is under in its pattern.
#[derive(Clone, Debug)]
pub struct TemplateShape {
    pub template: Template,
    pub depths: Box<[u32]>,
}

/// A pattern for `syntax-match`.
pub fn pattern<'gc>(mc: &Mutation<'gc>, shape: PatternShape, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
    let pattern = SyntaxPattern::new(mc, mc.frozen(Box::new(shape))?, items.len(), Value::FALSE)?;
    let slots = pattern.items(mc);
    for (i, &item) in items.iter().enumerate() {
        slots.set(mc, i, item);
    }
    Ok(Value::object(mc, pattern))
}

/// A template for `syntax-build`.
pub fn template<'gc>(mc: &Mutation<'gc>, shape: TemplateShape, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
    let template = SyntaxTemplate::new(mc, mc.frozen(Box::new(shape))?, items.len(), Value::FALSE)?;
    let slots = template.items(mc);
    for (i, &item) in items.iter().enumerate() {
        slots.set(mc, i, item);
    }
    Ok(Value::object(mc, template))
}

/// `(syntax-match pattern input)`.
pub(crate) fn matched<'gc>(mc: &Mutation<'gc>, pattern: Value<'gc>, input: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let pattern = pattern.downcast::<SyntaxPattern>(mc).ok_or(Fault::WrongType)?;
    let shape = pattern.shape(mc).ok_or(Fault::Malformed)?;
    let mut matcher = Matcher { mc, pattern, out: vec![Value::VOID; shape.vars as usize], count: 0, most: fuel.left().saturating_mul(PER_FUEL) };
    let matched = matcher.matches(&shape.pattern, input)?;
    fuel.spend(matcher.count / PER_FUEL)?;
    if !matched {
        return Ok(Value::FALSE);
    }
    Ok(Vectors::new(mc).immutable_from_slice(&matcher.out)?.value(mc))
}

struct Matcher<'m, 'gc> {
    mc: &'m Mutation<'gc>,
    pattern: Gc<'gc, SyntaxPattern>,
    out: Vec<Value<'gc>>,
    /// How much it's compared, and the most it can.
    count: u64,
    most: u64,
}

impl<'gc> Matcher<'_, 'gc> {
    fn item(&self, i: u32) -> Result<Value<'gc>, Fault> {
        let items = self.pattern.items(self.mc);
        if i as usize >= items.len() {
            return Err(Fault::Malformed);
        }
        Ok(items.get(i as usize))
    }

    fn charge(&mut self, n: u64) -> Result<(), Fault> {
        self.count = self.count.saturating_add(n);
        if self.count > self.most { Err(Fault::OutOfFuel) } else { Ok(()) }
    }

    fn slot(&mut self, slot: u32) -> Result<&mut Value<'gc>, Fault> {
        self.out.get_mut(slot as usize).ok_or(Fault::Malformed)
    }

    fn matches(&mut self, p: &Pattern, v: Value<'gc>) -> Result<bool, Fault> {
        let mc = self.mc;
        self.charge(1)?;
        Ok(match p {
            Pattern::Any => true,
            Pattern::Var(slot) => {
                *self.slot(*slot)? = v;
                true
            }
            Pattern::Literal(i) => syntax::is_identifier(mc, v) && syntax::same_binding(mc, self.item(*i)?, v)?,
            Pattern::Datum(i) => {
                let v = Syntax::of(v).map_or(v, |s| s.datum(mc));
                let (same, compared) = equal::equal(mc, v, self.item(*i)?, self.most.saturating_sub(self.count))?;
                self.charge(compared)?;
                same
            }
            Pattern::Seq { before, repeat, after, tail, vector } => {
                let items = if *vector { vector_items(mc, v) } else { list_items(mc, v) };
                let Some((items, rests)) = items else { return Ok(false) };
                self.charge(items.len() as u64)?;
                let (k, m, n) = (before.len(), after.len(), items.len());
                let end = rests[n];
                let fits = match (repeat, tail) {
                    (None, None) => n == k && end == Value::NIL,
                    (None, Some(_)) => n >= k,
                    (Some(_), None) => n >= k + m && end == Value::NIL,
                    (Some(_), Some(_)) => n >= k + m,
                };
                if !fits {
                    return Ok(false);
                }
                for (p, &item) in before.iter().zip(&items) {
                    if !self.matches(p, item)? {
                        return Ok(false);
                    }
                }
                if let Some(repeat) = repeat {
                    let slots = repeat.slots.start as usize..repeat.slots.end as usize;
                    if slots.end > self.out.len() {
                        return Err(Fault::Malformed);
                    }
                    let mut lists = vec![Vec::new(); slots.len()];
                    for &item in &items[k..n - m] {
                        if !self.matches(&repeat.each, item)? {
                            return Ok(false);
                        }
                        for (list, slot) in lists.iter_mut().zip(slots.clone()) {
                            list.push(self.out[slot]);
                        }
                    }
                    for (list, slot) in lists.into_iter().zip(slots) {
                        self.out[slot] = Pairs::new(mc).list(&list)?;
                    }
                    for (p, &item) in after.iter().zip(&items[n - m..]) {
                        if !self.matches(p, item)? {
                            return Ok(false);
                        }
                    }
                }
                match tail {
                    Some(tail) => self.matches(tail, rests[if repeat.is_some() { n } else { k }])?,
                    None => true,
                }
            }
        })
    }
}

/// The items of the list `v` is, or is the syntax of, and what's left of it from each, and
/// after the last; `None` if it's neither.
fn list_items<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
    let mut at = match Syntax::of(v) {
        Some(s) if s.kind(mc) == Some(SyntaxKind::List) => s.datum(mc),
        Some(_) => return None,
        None => v,
    };
    if at != Value::NIL && Pair::of(at).is_none() {
        return None;
    }
    let (mut items, mut rests) = (Vec::new(), Vec::new());
    loop {
        if let Some(pair) = Pair::of(at) {
            items.push(pair.head(mc));
            rests.push(at);
            at = pair.tail(mc);
        } else if let Some(datum) = Syntax::of(at).filter(|s| s.kind(mc) == Some(SyntaxKind::List)).map(|s| s.datum(mc)) {
            at = datum;
        } else {
            break;
        }
    }
    rests.push(at);
    Some((items, rests))
}

fn vector_items<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
    let v = match Syntax::of(v) {
        Some(s) if s.kind(mc) == Some(SyntaxKind::Vector) => s.datum(mc),
        Some(_) => return None,
        None => v,
    };
    let vector = AnyVector::of(v)?;
    let items: Vec<_> = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).collect();
    let rests = vec![Value::NIL; items.len() + 1];
    Some((items, rests))
}

/// `(syntax-build template value ...)`. Variables under ellipses that are repeated together
/// have to have matched as many times, or it's a syntax error.
pub(crate) fn build<'gc>(mc: &Mutation<'gc>, template: Value<'gc>, values: &[Value<'gc>], fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let template = template.downcast::<SyntaxTemplate>(mc).ok_or(Fault::WrongType)?;
    let shape = template.shape(mc).ok_or(Fault::Malformed)?;
    if values.len() != shape.depths.len() {
        return Err(Fault::Arity);
    }
    let env = values.iter().copied().zip(shape.depths.iter().copied()).collect();
    let mut builder = Builder { mc, template, env, count: 0, most: fuel.left().saturating_mul(PER_FUEL) };
    let built = builder.make(&shape.template)?;
    fuel.spend(builder.count / PER_FUEL)?;
    Ok(built)
}

struct Builder<'m, 'gc> {
    mc: &'m Mutation<'gc>,
    template: Gc<'gc, SyntaxTemplate>,
    /// What each variable's matched, and how many ellipses that's under.
    env: Vec<(Value<'gc>, u32)>,
    count: u64,
    most: u64,
}

impl<'gc> Builder<'_, 'gc> {
    fn item(&self, i: u32) -> Result<Value<'gc>, Fault> {
        let items = self.template.items(self.mc);
        if i as usize >= items.len() {
            return Err(Fault::Malformed);
        }
        Ok(items.get(i as usize))
    }

    fn var(&self, slot: u32) -> Result<(Value<'gc>, u32), Fault> {
        self.env.get(slot as usize).copied().ok_or(Fault::Malformed)
    }

    fn make(&mut self, t: &Template) -> Result<Value<'gc>, Fault> {
        let mc = self.mc;
        self.count = self.count.saturating_add(1);
        if self.count > self.most {
            return Err(Fault::OutOfFuel);
        }
        Ok(match t {
            Template::Const(i) => self.item(*i)?,
            Template::Var(slot) => self.var(*slot)?.0,
            Template::Seq { items, tail, vector, like } => {
                let like = Syntax::of(self.item(*like)?).ok_or(Fault::Malformed)?;
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    self.repeat(item, item.ellipses, &mut out)?;
                }
                let datum = if *vector {
                    Vectors::new(mc).immutable_from_slice(&out)?.value(mc)
                } else {
                    let tail = tail.as_deref().map_or(Ok(Value::NIL), |tail| self.make(tail))?;
                    Pairs::new(mc).list_with_tail(out, tail)?
                };
                Syntax::new(mc, datum, like.span(mc), like.metadata(mc))?.value(mc)
            }
        })
    }

    /// Makes `item` under `ellipses` of its ellipses, once for each match of the variables in it
    /// with matches left, adding what it makes to `out`.
    fn repeat(&mut self, item: &Item, ellipses: u32, out: &mut Vec<Value<'gc>>) -> Result<(), Fault> {
        if ellipses == 0 {
            out.push(self.make(&item.template)?);
            return Ok(());
        }
        let mut drivers = Vec::new();
        for &slot in &item.slots {
            if self.var(slot)?.1 > 0 {
                drivers.push(slot as usize);
            }
        }
        let lists = drivers.iter().map(|&slot| list_items(self.mc, self.env[slot].0).map(|(items, _)| items)).collect::<Option<Vec<_>>>();
        let lists = lists.ok_or(Fault::WrongType)?;
        let Some(len) = lists.first().map(Vec::len) else { return Err(Fault::Malformed) };
        if lists.iter().any(|list| list.len() != len) {
            return Err(Fault::Syntax);
        }
        let saved: Vec<_> = drivers.iter().map(|&slot| self.env[slot]).collect();
        for i in 0..len {
            for ((&slot, list), &(_, depth)) in drivers.iter().zip(&lists).zip(&saved) {
                self.env[slot] = (list[i], depth - 1);
            }
            self.repeat(item, ellipses - 1, out)?;
        }
        for (&slot, &was) in drivers.iter().zip(&saved) {
            self.env[slot] = was;
        }
        Ok(())
    }
}
