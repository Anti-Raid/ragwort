//! Compiled pattern and template representations for `syntax-case` and `syntax` forms.
//!
//! Provides two constant structures:
//! - [`SyntaxPattern`]: Compiled pattern structure matched against input syntax via `syntax-match`,
//!   yielding a vector of matched pattern variable bindings (nested in lists for variables bound under ellipses).
//! - [`SyntaxTemplate`]: Compiled template structure used by `syntax-build` to construct output syntax
//!   by substituting matched pattern variable bindings into the template shape.
//!
//! Literals, constants, and nested pattern/template nodes are stored in indexed item arrays.
//! Matched inputs and generated outputs maintain transformer syntax representation invariants
//! (nested lists of syntax objects or syntax objects wrapping lists).

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

/// A compiled pattern matching node. Literals and datums are referenced by index into the
/// enclosing [`SyntaxPattern`] item table, while sub-pattern nodes and sequences are referenced
/// by index ranges in [`PatternShape`].
#[derive(Clone, Debug, Wire)]
pub enum Pattern {
    /// Wildcard pattern (`_`), matching any syntax input without binding a pattern variable.
    Any,
    /// Pattern variable node, binding the matched syntax into output vector slot `u32`.
    Var(u32),
    /// Literal identifier pattern, matching any input identifier that resolves to the same binding as the identifier at constant index `u32`.
    Literal(u32),
    /// Constant datum pattern, matching any input whose unwrapped datum is `equal?` to the constant datum at index `u32`.
    Datum(u32),
    /// Sequence pattern (matching a list or vector) with three segments: fixed elements before an ellipsis (`before`),
    /// an optional repeated pattern under an ellipsis (`repeat`), fixed elements following the ellipsis (`after`),
    /// and an optional improper list tail pattern (`tail`).
    Seq { before: Range<u32>, repeat: Option<Repeat>, after: Range<u32>, tail: Option<u32>, vector: bool },
}

/// Describes an ellipsized sub-pattern: the node index `each` to match repeatedly, and the slot range `slots` receiving accumulated match lists.
#[derive(Clone, Debug, Wire)]
pub struct Repeat {
    pub each: u32,
    pub slots: Range<u32>,
}

/// The AST layout of a compiled pattern, containing a flat vector of pattern `nodes`, sequence element index ranges in `lists`,
/// and the total count of pattern variables `vars`.
#[derive(Clone, Debug, Default, Wire)]
pub struct PatternShape {
    pub nodes: Vec<Pattern>,
    pub lists: Vec<u32>,
    pub vars: u32,
}

impl PatternShape {
    /// Appends pattern node `pattern` to `nodes` and returns its 0-based node index.
    pub fn add(&mut self, pattern: Pattern) -> u32 {
        self.nodes.push(pattern);
        index(self.nodes.len() - 1)
    }

    /// Appends an iterator of pattern node indices to `lists` and returns the corresponding index range.
    pub fn list(&mut self, nodes: impl IntoIterator<Item = u32>) -> Range<u32> {
        let start = index(self.lists.len());
        self.lists.extend(nodes);
        start..index(self.lists.len())
    }

    fn of(&self, list: &Range<u32>) -> &[u32] {
        &self.lists[list.start as usize..list.end as usize]
    }
}

/// A compiled syntax template node. Constant syntax objects are stored in the enclosing [`SyntaxTemplate`]
/// item table, and composite sequence items are stored in [`TemplateShape`].
#[derive(Clone, Debug, Wire)]
pub enum Template {
    /// Emits the constant syntax object stored at item index `u32`.
    Const(u32),
    /// Emits the value bound to the pattern variable in slot `u32`.
    Var(u32),
    /// Constructs a list or vector from template `items` (with an optional improper `tail` for lists),
    /// transferring source spans and lexical scopes from the prototype syntax object at item index `like`.
    Seq { items: Range<u32>, tail: Option<u32>, vector: bool, like: u32 },
}

/// An element within a sequence template, instantiated once per iteration across the pattern variables
/// in `slots` nested under `ellipses` ellipsis levels.
#[derive(Clone, Debug, Wire)]
pub struct Item {
    pub template: u32,
    pub ellipses: u32,
    pub slots: Range<u32>,
}

/// The structural layout of a compiled syntax template, containing template nodes (`nodes`), sequence items (`items`),
/// variable slot ranges (`slots`), and the ellipsis nesting depth (`depths`) of each pattern variable.
#[derive(Clone, Debug, Default, Wire)]
pub struct TemplateShape {
    pub nodes: Vec<Template>,
    pub items: Vec<Item>,
    pub slots: Vec<u32>,
    pub depths: Box<[u32]>,
}

impl TemplateShape {
    /// Appends template node `template` to `nodes` and returns its 0-based node index.
    pub fn add(&mut self, template: Template) -> u32 {
        self.nodes.push(template);
        index(self.nodes.len() - 1)
    }

    /// Appends sequence template items and their associated variable slots to `items` and `slots`, returning the allocated index range in `items`.
    pub fn items(&mut self, items: impl IntoIterator<Item = (u32, u32, Vec<u32>)>) -> Range<u32> {
        let start = index(self.items.len());
        for (template, ellipses, slots) in items {
            let at = index(self.slots.len());
            self.slots.extend(slots);
            self.items.push(Item { template, ellipses, slots: at..index(self.slots.len()) });
        }
        start..index(self.items.len())
    }

    /// Truncates the `nodes`, `items`, and `slots` vectors back to the specified lengths (used during template compilation rollbacks).
    pub fn truncate(&mut self, nodes: usize, items: usize, slots: usize) {
        self.nodes.truncate(nodes);
        self.items.truncate(items);
        self.slots.truncate(slots);
    }
}

fn index(count: usize) -> u32 {
    u32::try_from(count).expect("fewer than 2^32 parts")
}

/// Constructs a heap-allocated [`SyntaxPattern`] object containing frozen `shape` metadata and constant `items`.
pub fn pattern<'gc>(mc: &Mutation<'gc>, shape: PatternShape, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
    let pattern = SyntaxPattern::new(mc, mc.frozen(Box::new(shape))?, items.len(), Value::FALSE)?;
    let slots = pattern.items(mc);
    for (i, &item) in items.iter().enumerate() {
        slots.set(mc, i, item);
    }
    Ok(Value::object(mc, pattern))
}

/// Constructs a heap-allocated [`SyntaxTemplate`] object containing frozen `shape` metadata and constant `items`.
pub fn template<'gc>(mc: &Mutation<'gc>, shape: TemplateShape, items: &[Value<'gc>]) -> Result<Value<'gc>, OutOfMemory> {
    let template = SyntaxTemplate::new(mc, mc.frozen(Box::new(shape))?, items.len(), Value::FALSE)?;
    let slots = template.items(mc);
    for (i, &item) in items.iter().enumerate() {
        slots.set(mc, i, item);
    }
    Ok(Value::object(mc, template))
}

/// Matches syntax `input` against compiled `pattern` (implements the `syntax-match` intrinsic).
/// Returns an immutable vector of matched variable values on success, or `#f` if the pattern does not match.
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

/// A task on the pattern-matcher work stack: match a pattern node against a syntax value (`Node`),
/// append repeated variable matches into intermediate lists (`Each`), or finalize repeated lists into output slots (`Lists`).
enum Match<'p, 'gc> {
    Node(u32, Value<'gc>),
    /// Appends current iteration values of pattern variables in `slots` to their respective accumulation lists.
    Each(&'p Range<u32>),
    /// Converts accumulated repeated match lists for variables in `slots` into Scheme lists and stores them into the corresponding output slots.
    Lists(&'p Range<u32>),
}

struct Matcher<'m, 'gc> {
    mc: &'m Mutation<'gc>,
    pattern: Gc<'gc, SyntaxPattern>,
    out: Vec<Value<'gc>>,
    /// Cumulative number of matching comparisons performed, bounded by `most` to enforce fuel limits.
    count: u64,
    most: u64,
}

impl<'gc> Matcher<'_, 'gc> {
    fn item(&self, index: u32) -> Result<Value<'gc>, Fault> {
        let items = self.pattern.items(self.mc);
        if index as usize >= items.len() {
            return Err(Fault::Malformed);
        }
        Ok(items.get(index as usize))
    }

    fn charge(&mut self, amount: u64) -> Result<(), Fault> {
        self.count = self.count.saturating_add(amount);
        if self.count > self.most { Err(Fault::OutOfFuel) } else { Ok(()) }
    }

    fn slot(&mut self, slot: u32) -> Result<&mut Value<'gc>, Fault> {
        self.out.get_mut(slot as usize).ok_or(Fault::Malformed)
    }

    /// Recursively matches input value `input` against the pattern node at `root` in `shape`.
    /// Populates matched variable slots in `self.out` and returns `true` on success, or `false` on mismatch.
    /// Manages nested ellipsis repetition via an evaluation stack of accumulated list vectors.
    fn matches(&mut self, shape: &PatternShape, root: u32, input: Value<'gc>) -> Result<bool, Fault> {
        let mc = self.mc;
        let mut todo = vec![Match::Node(root, input)];
        let mut lists: Vec<Vec<Vec<Value<'gc>>>> = Vec::new();
        while let Some(task) = todo.pop() {
            let (pattern, value) = match task {
                Match::Node(node, value) => (shape.nodes.get(node as usize).ok_or(Fault::Malformed)?, value),
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
            let matched = match pattern {
                Pattern::Any => true,
                Pattern::Var(slot) => {
                    *self.slot(*slot)? = value;
                    true
                }
                Pattern::Literal(index) => syntax::is_identifier(mc, value) && syntax::same_binding(mc, self.item(*index)?, value)?,
                Pattern::Datum(index) => {
                    let datum = Syntax::of(value).map_or(value, |syntax| syntax.datum(mc));
                    let (same, compared) = equal::equal(mc, datum, self.item(*index)?, self.most.saturating_sub(self.count))?;
                    self.charge(compared)?;
                    same
                }
                Pattern::Seq { before, repeat, after, tail, vector } => {
                    let items = if *vector { vector_items(mc, value) } else { list_items(mc, value) };
                    let Some((items, rests)) = items else { return Ok(false) };
                    self.charge(items.len() as u64)?;
                    let (before, after) = (shape.of(before), shape.of(after));
                    let (before_len, after_len, len) = (before.len(), after.len(), items.len());
                    let end = rests[len];
                    let fits = match (repeat, tail) {
                        (None, None) => len == before_len && end == Value::NIL,
                        (None, Some(_)) => len >= before_len,
                        (Some(_), None) => len >= before_len + after_len && end == Value::NIL,
                        (Some(_), Some(_)) => len >= before_len + after_len,
                    };
                    if fits {
                        let at = todo.len();
                        todo.extend(before.iter().zip(&items).map(|(&node, &item)| Match::Node(node, item)));
                        if let Some(repeat) = repeat {
                            if repeat.slots.end as usize > self.out.len() {
                                return Err(Fault::Malformed);
                            }
                            lists.push(vec![Vec::new(); repeat.slots.len()]);
                            for &item in &items[before_len..len - after_len] {
                                todo.extend([Match::Node(repeat.each, item), Match::Each(&repeat.slots)]);
                            }
                            todo.push(Match::Lists(&repeat.slots));
                            todo.extend(after.iter().zip(&items[len - after_len..]).map(|(&node, &item)| Match::Node(node, item)));
                        }
                        if let Some(tail) = tail {
                            todo.push(Match::Node(*tail, rests[if repeat.is_some() { len } else { before_len }]));
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

/// Deconstructs a Scheme list or syntax-wrapped list `value` into a pair of vectors `(items, rests)`,
/// where `items` contains the list elements and `rests` contains the successive tail values at each step
/// and after the final element; returns `None` if `value` is neither a list nor list syntax.
fn list_items<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
    let mut at = match Syntax::of(value) {
        Some(syntax) if syntax.kind(mc) == Some(SyntaxKind::List) => syntax.datum(mc),
        Some(_) => return None,
        None => value,
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
        } else if let Some(datum) = Syntax::of(at).filter(|syntax| syntax.kind(mc) == Some(SyntaxKind::List)).map(|syntax| syntax.datum(mc)) {
            at = datum;
        } else {
            break;
        }
    }
    rests.push(at);
    Some((items, rests))
}

fn vector_items<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Option<(Vec<Value<'gc>>, Vec<Value<'gc>>)> {
    let datum = match Syntax::of(value) {
        Some(syntax) if syntax.kind(mc) == Some(SyntaxKind::Vector) => syntax.datum(mc),
        Some(_) => return None,
        None => value,
    };
    let vector = AnyVector::of(datum)?;
    let items: Vec<_> = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).collect();
    let rests = vec![Value::NIL; items.len() + 1];
    Some((items, rests))
}

/// Instantiates syntax from `template` using pattern variable bindings in `values` (implements the `syntax-build` intrinsic).
/// Raises [`Fault::Syntax`] if synchronized pattern variables under the same ellipsis level have mismatched iteration lengths.
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

/// A task on the template construction work stack: instantiate a template node (`Node`),
/// expand an ellipsized item at a given nesting depth (`Item`), restore previous variable bindings after an iteration (`Bind`),
/// or assemble constructed elements into a list or vector sequence (`Seq`).
enum Build<'gc> {
    Node(u32),
    Item(u32, u32),
    Bind(Vec<(usize, (Value<'gc>, u32))>),
    Seq(u32, usize),
}

struct Builder<'m, 'gc> {
    mc: &'m Mutation<'gc>,
    template: Gc<'gc, SyntaxTemplate>,
    /// Evaluation environment mapping each pattern variable slot to its currently bound value and remaining ellipsis nesting depth.
    env: Vec<(Value<'gc>, u32)>,
    count: u64,
    most: u64,
}

impl<'gc> Builder<'_, 'gc> {
    fn item(&self, index: u32) -> Result<Value<'gc>, Fault> {
        let items = self.template.items(self.mc);
        if index as usize >= items.len() {
            return Err(Fault::Malformed);
        }
        Ok(items.get(index as usize))
    }

    fn var(&self, slot: u32) -> Result<(Value<'gc>, u32), Fault> {
        self.env.get(slot as usize).copied().ok_or(Fault::Malformed)
    }

    /// Evaluates template node `root` of `shape`, returning the constructed syntax object.
    /// Sub-items under ellipses are iteratively expanded for each element of their driver variable lists.
    fn make(&mut self, shape: &TemplateShape, root: u32) -> Result<Value<'gc>, Fault> {
        let mc = self.mc;
        let mut todo = vec![Build::Node(root)];
        let mut made = Vec::new();
        while let Some(task) = todo.pop() {
            match task {
                Build::Node(node) => {
                    self.count = self.count.saturating_add(1);
                    if self.count > self.most {
                        return Err(Fault::OutOfFuel);
                    }
                    match shape.nodes.get(node as usize).ok_or(Fault::Malformed)? {
                        Template::Const(index) => made.push(self.item(*index)?),
                        Template::Var(slot) => made.push(self.var(*slot)?.0),
                        Template::Seq { items, tail, vector, .. } => {
                            todo.push(Build::Seq(node, made.len()));
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
                Build::Item(index, 0) => todo.push(Build::Node(shape.items[index as usize].template)),
                Build::Item(index, ellipses) => self.repeat(shape, index, ellipses, &mut todo)?,
                Build::Bind(bound) => bound.into_iter().for_each(|(slot, was)| self.env[slot] = was),
                Build::Seq(node, start) => {
                    let Template::Seq { tail, vector, like, .. } = shape.nodes[node as usize] else { unreachable!("a sequence's node") };
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

    /// Expands repeated template item `index` at ellipsis depth `ellipses`. Validates that all active driver variables
    /// have matching list lengths (raising [`Fault::Syntax`] on mismatch), and schedules iterations on the `todo` stack
    /// to bind sub-elements and restore bindings.
    fn repeat(&mut self, shape: &TemplateShape, index: u32, ellipses: u32, todo: &mut Vec<Build<'gc>>) -> Result<(), Fault> {
        let item = &shape.items[index as usize];
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
        for iteration in (0..len).rev() {
            todo.push(Build::Item(index, ellipses - 1));
            todo.push(Build::Bind(saved.iter().zip(&lists).map(|(&(slot, (_, depth)), list)| (slot, (list[iteration], depth - 1))).collect()));
        }
        Ok(())
    }

}
