//! `syntax-case`'s patterns and `syntax`'s templates, as values code holds as constants:
//! [`SyntaxPattern`]s, which `syntax-match` matches syntax with, giving a vector of what their
//! variables matched, a list of those for each ellipsis a variable's under, and
//! [`SyntaxTemplate`]s, which `syntax-build` makes syntax of, from what its pattern variables
//! matched. Each is a shape, with the syntax and data it refers to in its items, by index.
//!
//! What's matched and made is a transformer's syntax: lists of syntax, or the syntax of lists, as
//! a pattern's rest is a list of the rest of the syntax it matched.

use std::ops::Range;

use ragwort_types::Wire;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::syntax::{Syntax, SyntaxKind};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::equal::{self, PER_FUEL};
use crate::objects::{SyntaxPattern, SyntaxPatternFields, SyntaxTemplate, SyntaxTemplateFields};
use crate::op::Fuel;
use crate::syntax;

/// A pattern, its literals and data the items of the [`SyntaxPattern`] it's in. Its parts are
/// nodes of the [`PatternShape`] it's in, by index, and lists of them its ranges of `lists`.
#[derive(Clone, Debug, Wire)]
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
    Seq { before: Range<u32>, repeat: Option<Repeat>, after: Range<u32>, tail: Option<u32>, vector: bool },
}

/// A pattern under an ellipsis, and the slots of its variables.
#[derive(Clone, Debug, Wire)]
pub struct Repeat {
    pub each: u32,
    pub slots: Range<u32>,
}

/// A pattern, its last node, the nodes of its parts before it, and how many variables it has.
#[derive(Clone, Debug, Default, Wire)]
pub struct PatternShape {
    pub nodes: Vec<Pattern>,
    pub lists: Vec<u32>,
    pub vars: u32,
}

impl PatternShape {
    /// `p`'s node, the last so far.
    pub fn add(&mut self, p: Pattern) -> u32 {
        self.nodes.push(p);
        index(self.nodes.len() - 1)
    }

    /// The list of `nodes`.
    pub fn list(&mut self, nodes: impl IntoIterator<Item = u32>) -> Range<u32> {
        let start = index(self.lists.len());
        self.lists.extend(nodes);
        start..index(self.lists.len())
    }

    fn of(&self, list: &Range<u32>) -> &[u32] {
        &self.lists[list.start as usize..list.end as usize]
    }
}

/// A template, its constants the items of the [`SyntaxTemplate`] it's in. Its parts are nodes of
/// the [`TemplateShape`] it's in, by index, and its items a range of its `items`.
#[derive(Clone, Debug, Wire)]
pub enum Template {
    /// The syntax in this item.
    Const(u32),
    /// What the variable passed in this place matched.
    Var(u32),
    /// A list or vector of items, a tail for a list, made with the scopes and span of the
    /// syntax in item `like`.
    Seq { items: Range<u32>, tail: Option<u32>, vector: bool, like: u32 },
}

/// An item of a list or vector template, made once for each match of the pattern variables in
/// it under `ellipses` ellipses, which are in `slots`, a range of the shape's.
#[derive(Clone, Debug, Wire)]
pub struct Item {
    pub template: u32,
    pub ellipses: u32,
    pub slots: Range<u32>,
}

/// A template, its last node, the nodes of its parts before it, and how many ellipses each
/// pattern variable it's passed is under in its pattern.
#[derive(Clone, Debug, Default, Wire)]
pub struct TemplateShape {
    pub nodes: Vec<Template>,
    pub items: Vec<Item>,
    pub slots: Vec<u32>,
    pub depths: Box<[u32]>,
}

impl TemplateShape {
    /// `t`'s node, the last so far.
    pub fn add(&mut self, t: Template) -> u32 {
        self.nodes.push(t);
        index(self.nodes.len() - 1)
    }

    /// The items `items`, each a template, how many ellipses it's under, and its slots.
    pub fn items(&mut self, items: impl IntoIterator<Item = (u32, u32, Vec<u32>)>) -> Range<u32> {
        let start = index(self.items.len());
        for (template, ellipses, slots) in items {
            let at = index(self.slots.len());
            self.slots.extend(slots);
            self.items.push(Item { template, ellipses, slots: at..index(self.slots.len()) });
        }
        start..index(self.items.len())
    }

    /// Forgets the nodes, items and slots from these on.
    pub fn truncate(&mut self, nodes: usize, items: usize, slots: usize) {
        self.nodes.truncate(nodes);
        self.items.truncate(items);
        self.slots.truncate(slots);
    }
}

fn index(n: usize) -> u32 {
    u32::try_from(n).expect("fewer than 2^32 parts")
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
    let matched = match shape.nodes.len().checked_sub(1) {
        Some(root) => matcher.matches(shape, index(root), input)?,
        None => return Err(Fault::Malformed),
    };
    fuel.spend(matcher.count / PER_FUEL)?;
    if !matched {
        return Ok(Value::FALSE);
    }
    Ok(Vectors::new(mc).immutable_from_slice(&matcher.out)?.value(mc))
}

/// What's left of a match: a node to match a value with, or what to do once a repeated
/// pattern's matched an item, or all of them.
enum Match<'p, 'gc> {
    Node(u32, Value<'gc>),
    /// What the repeated pattern's variables matched, added to their lists.
    Each(&'p Range<u32>),
    /// The lists, into the variables' slots.
    Lists(&'p Range<u32>),
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

    /// Whether `v` matches node `root` of `shape`, any pattern in which that doesn't match
    /// failing the whole of it. A repeated pattern's lists are made innermost first, on a stack.
    fn matches(&mut self, shape: &PatternShape, root: u32, v: Value<'gc>) -> Result<bool, Fault> {
        let mc = self.mc;
        let mut todo = vec![Match::Node(root, v)];
        let mut lists: Vec<Vec<Vec<Value<'gc>>>> = Vec::new();
        while let Some(task) = todo.pop() {
            let (p, v) = match task {
                Match::Node(p, v) => (shape.nodes.get(p as usize).ok_or(Fault::Malformed)?, v),
                Match::Each(slots) => {
                    let top = lists.last_mut().expect("a repeat's lists");
                    for (list, slot) in top.iter_mut().zip(slots.clone()) {
                        list.push(self.out[slot as usize]);
                    }
                    continue;
                }
                Match::Lists(slots) => {
                    for (list, slot) in lists.pop().expect("a repeat's lists").into_iter().zip(slots.clone()) {
                        self.out[slot as usize] = Pairs::new(mc).list(&list)?;
                    }
                    continue;
                }
            };
            self.charge(1)?;
            let matched = match p {
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
                    let (before, after) = (shape.of(before), shape.of(after));
                    let (k, m, n) = (before.len(), after.len(), items.len());
                    let end = rests[n];
                    let fits = match (repeat, tail) {
                        (None, None) => n == k && end == Value::NIL,
                        (None, Some(_)) => n >= k,
                        (Some(_), None) => n >= k + m && end == Value::NIL,
                        (Some(_), Some(_)) => n >= k + m,
                    };
                    if fits {
                        let at = todo.len();
                        todo.extend(before.iter().zip(&items).map(|(&p, &item)| Match::Node(p, item)));
                        if let Some(repeat) = repeat {
                            if repeat.slots.end as usize > self.out.len() {
                                return Err(Fault::Malformed);
                            }
                            lists.push(vec![Vec::new(); repeat.slots.len()]);
                            for &item in &items[k..n - m] {
                                todo.extend([Match::Node(repeat.each, item), Match::Each(&repeat.slots)]);
                            }
                            todo.push(Match::Lists(&repeat.slots));
                            todo.extend(after.iter().zip(&items[n - m..]).map(|(&p, &item)| Match::Node(p, item)));
                        }
                        if let Some(tail) = tail {
                            todo.push(Match::Node(*tail, rests[if repeat.is_some() { n } else { k }]));
                        }
                        todo[at..].reverse();
                    }
                    fits
                }
            };
            if !matched {
                return Ok(false);
            }
        }
        Ok(true)
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
    let root = shape.nodes.len().checked_sub(1).ok_or(Fault::Malformed)?;
    let built = builder.make(shape, index(root))?;
    fuel.spend(builder.count / PER_FUEL)?;
    Ok(built)
}

/// What's left of making a template: a node to make, an item to make under so many of its
/// ellipses, what its variables stand for in a run of it, or a list or vector to make of what's
/// been made since it was reached.
enum Build<'gc> {
    Node(u32),
    Item(u32, u32),
    Bind(Vec<(usize, (Value<'gc>, u32))>),
    Seq(u32, usize),
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

    /// Makes node `root` of `shape`. An item under ellipses is made once for each match of
    /// the variables in it, each of those binding them to what they matched in it.
    fn make(&mut self, shape: &TemplateShape, root: u32) -> Result<Value<'gc>, Fault> {
        let mc = self.mc;
        let mut todo = vec![Build::Node(root)];
        let mut made = Vec::new();
        while let Some(task) = todo.pop() {
            match task {
                Build::Node(t) => {
                    self.count = self.count.saturating_add(1);
                    if self.count > self.most {
                        return Err(Fault::OutOfFuel);
                    }
                    match shape.nodes.get(t as usize).ok_or(Fault::Malformed)? {
                        Template::Const(i) => made.push(self.item(*i)?),
                        Template::Var(slot) => made.push(self.var(*slot)?.0),
                        Template::Seq { items, tail, vector, .. } => {
                            todo.push(Build::Seq(t, made.len()));
                            if let Some(tail) = tail.filter(|_| !vector) {
                                todo.push(Build::Node(tail));
                            }
                            for i in items.clone().rev() {
                                let item = shape.items.get(i as usize).ok_or(Fault::Malformed)?;
                                todo.push(Build::Item(i, item.ellipses));
                            }
                        }
                    }
                }
                Build::Item(i, 0) => todo.push(Build::Node(shape.items[i as usize].template)),
                Build::Item(i, ellipses) => self.repeat(shape, i, ellipses, &mut todo)?,
                Build::Bind(bound) => bound.into_iter().for_each(|(slot, was)| self.env[slot] = was),
                Build::Seq(t, start) => {
                    let Template::Seq { tail, vector, like, .. } = shape.nodes[t as usize] else { unreachable!("a sequence's node") };
                    let like = Syntax::of(self.item(like)?).ok_or(Fault::Malformed)?;
                    let tail = if tail.is_some() && !vector { made.pop().expect("a tail") } else { Value::NIL };
                    let out = made.split_off(start);
                    let datum = if vector { Vectors::new(mc).immutable_from_slice(&out)?.value(mc) } else { Pairs::new(mc).list_with_tail(out, tail)? };
                    made.push(Syntax::new(mc, datum, like.span(mc), like.metadata(mc))?.value(mc));
                }
            }
        }
        Ok(made.pop().expect("the root's made"))
    }

    /// Item `i` under `ellipses` of its ellipses, once for each match of the variables in it
    /// with matches left, each binding them to what they matched in it, then as they were.
    fn repeat(&mut self, shape: &TemplateShape, i: u32, ellipses: u32, todo: &mut Vec<Build<'gc>>) -> Result<(), Fault> {
        let item = &shape.items[i as usize];
        let mut drivers = Vec::new();
        for &slot in shape.slots.get(item.slots.start as usize..item.slots.end as usize).ok_or(Fault::Malformed)? {
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
        let saved: Vec<_> = drivers.iter().map(|&slot| (slot, self.env[slot])).collect();
        todo.push(Build::Bind(saved.clone()));
        for k in (0..len).rev() {
            todo.push(Build::Item(i, ellipses - 1));
            todo.push(Build::Bind(saved.iter().zip(&lists).map(|(&(slot, (_, depth)), list)| (slot, (list[k], depth - 1))).collect()));
        }
        Ok(())
    }

}
