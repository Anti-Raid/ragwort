//! Syntax as the expander works on it: a tree of nodes on the host, in storage charged to the
//! arena's budget, each node with its scopes and the span of text it came from. A [`Stx`] is a
//! node and the scope changes pending on it, which reach its parts as they're taken apart.
//!
//! The nodes hold arena values untraced, so a tree must be used and dropped within the step
//! that made it.

use ragwort_types::gc::{Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxSpan};
use ragwort_types::vector::Vectors;

use crate::scope::{Op, Ops, Scope, Scopes, Set};

/// Syntax: a node and the scope changes it has yet to pass on.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Stx {
    node: u32,
    ops: Ops,
}

#[derive(Clone, Copy)]
enum Shape<'gc> {
    Id(Symbol<'gc>),
    Datum(Value<'gc>),
    /// Items `kids[first..first + len]`, the last of them the tail if `dotted`.
    List { first: u32, len: u32, dotted: bool },
    Vector { first: u32, len: u32 },
}

#[derive(Clone, Copy)]
struct Node<'gc> {
    shape: Shape<'gc>,
    scopes: Set,
    span: SyntaxSpan<'gc>,
}

/// A node's shape, with its parts as syntax.
pub(crate) enum View<'gc> {
    Id,
    Datum(Value<'gc>),
    List(Vec<Stx>, Option<Stx>),
    Vector(Vec<Stx>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TreeError {
    TooDeep,
    OutOfMemory,
}

impl From<OutOfMemory> for TreeError {
    fn from(_: OutOfMemory) -> Self {
        TreeError::OutOfMemory
    }
}

pub(crate) struct Tree<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    nodes: ScratchVec<'gc, Node<'gc>>,
    kids: ScratchVec<'gc, Stx>,
    pub(crate) scopes: Scopes<'gc>,
    /// The symbols each of the reader's abbreviations stands for, in order.
    abbreviations: Vec<Symbol<'gc>>,
}

impl<'a, 'gc> Tree<'a, 'gc> {
    pub(crate) fn new(mc: &'a Mutation<'gc>, abbreviations: Vec<Symbol<'gc>>) -> Self {
        Self { mc, nodes: ScratchVec::new(mc), kids: ScratchVec::new(mc), scopes: Scopes::new(mc), abbreviations }
    }

    fn node(&self, stx: Stx) -> Node<'gc> {
        self.nodes[stx.node as usize]
    }

    fn make(&mut self, shape: Shape<'gc>, scopes: Set, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        let node = u32::try_from(self.nodes.len()).map_err(|_| OutOfMemory)?;
        self.nodes.push(Node { shape, scopes, span })?;
        Ok(Stx { node, ops: Ops::NONE })
    }

    fn parts(&mut self, parts: impl IntoIterator<Item = Stx>) -> Result<(u32, u32), OutOfMemory> {
        let first = self.kids.len();
        for part in parts {
            self.kids.push(part)?;
        }
        let len = self.kids.len() - first;
        Ok((u32::try_from(first).map_err(|_| OutOfMemory)?, len as u32))
    }

    pub(crate) fn id(&mut self, symbol: Symbol<'gc>, scopes: Set, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        self.make(Shape::Id(symbol), scopes, span)
    }

    pub(crate) fn datum(&mut self, value: Value<'gc>, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        self.make(Shape::Datum(value), Set::EMPTY, span)
    }

    pub(crate) fn list(&mut self, items: &[Stx], tail: Option<Stx>, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        let (first, len) = self.parts(items.iter().copied().chain(tail))?;
        self.make(Shape::List { first, len, dotted: tail.is_some() }, Set::EMPTY, span)
    }

    pub(crate) fn vector(&mut self, items: &[Stx], span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        let (first, len) = self.parts(items.iter().copied())?;
        self.make(Shape::Vector { first, len }, Set::EMPTY, span)
    }

    pub(crate) fn span(&self, stx: Stx) -> SyntaxSpan<'gc> {
        self.node(stx).span
    }

    /// `stx` with `scope` added, or flipped: removed if it has it, else added.
    pub(crate) fn with(&mut self, stx: Stx, scope: Scope, op: Op) -> Result<Stx, OutOfMemory> {
        let op = self.scopes.op(scope, op)?;
        Ok(Stx { node: stx.node, ops: self.scopes.compose(stx.ops, op)? })
    }

    /// The scopes of `stx`, with its pending changes made.
    pub(crate) fn scopes_of(&mut self, stx: Stx) -> Result<Set, OutOfMemory> {
        self.scopes.apply(self.node(stx).scopes, stx.ops)
    }

    pub(crate) fn symbol(&self, stx: Stx) -> Option<Symbol<'gc>> {
        match self.node(stx).shape {
            Shape::Id(symbol) => Some(symbol),
            _ => None,
        }
    }

    pub(crate) fn view(&mut self, stx: Stx) -> Result<View<'gc>, OutOfMemory> {
        Ok(match self.node(stx).shape {
            Shape::Id(_) => View::Id,
            Shape::Datum(value) => View::Datum(value),
            Shape::List { first, len, dotted } => {
                let mut items = self.kids_of(stx, first, len)?;
                let tail = if dotted { items.pop() } else { None };
                View::List(items, tail)
            }
            Shape::Vector { first, len } => View::Vector(self.kids_of(stx, first, len)?),
        })
    }

    fn kids_of(&mut self, stx: Stx, first: u32, len: u32) -> Result<Vec<Stx>, OutOfMemory> {
        let range = first as usize..(first + len) as usize;
        let mut kids = self.kids[range].to_vec();
        for kid in &mut kids {
            kid.ops = self.scopes.compose(kid.ops, stx.ops)?;
        }
        Ok(kids)
    }

    /// The tree of what the reader read, its nodes in no scopes.
    pub(crate) fn read(&mut self, node: Syntax<'gc>, depth: usize) -> Result<Stx, TreeError> {
        let depth = depth.checked_sub(1).ok_or(TreeError::TooDeep)?;
        let mc = self.mc;
        let span = node.span(mc);
        let part = |this: &mut Self, v: Value<'gc>| this.read(Syntax::of(v).expect("the reader wraps every part"), depth);
        let shape = match node.kind(mc) {
            Some(SyntaxKind::Identifier) => Shape::Id(Symbol::of(node.datum(mc)).expect("identifiers are symbols")),
            Some(SyntaxKind::List) => {
                let mut elements = Pairs::new(mc).elements(node.datum(mc));
                let mut items = elements.by_ref().map(|v| part(self, v)).collect::<Result<Vec<_>, _>>()?;
                let tail = elements.rest();
                let dotted = tail != Value::NIL;
                if dotted {
                    items.push(part(self, tail)?);
                }
                let (first, len) = self.parts(items)?;
                Shape::List { first, len, dotted }
            }
            Some(SyntaxKind::Vector) => {
                let vector = Vectors::new(mc).vector(node.datum(mc)).expect("vector nodes hold vectors");
                let items = (0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).map(|v| part(self, v)).collect::<Result<Vec<_>, _>>()?;
                let (first, len) = self.parts(items)?;
                Shape::Vector { first, len }
            }
            Some(SyntaxKind::Abbreviation(a)) => {
                let name = self.abbreviations[a as usize];
                let name = self.id(name, Set::EMPTY, span)?;
                let inner = part(self, node.datum(mc))?;
                let (first, len) = self.parts([name, inner])?;
                Shape::List { first, len, dotted: false }
            }
            Some(SyntaxKind::Literal) | None => Shape::Datum(node.datum(mc)),
        };
        Ok(self.make(shape, Set::EMPTY, span)?)
    }

    /// The datum `stx` stands for, without its scopes and spans.
    pub(crate) fn strip(&mut self, stx: Stx, depth: usize) -> Result<Value<'gc>, TreeError> {
        let depth = depth.checked_sub(1).ok_or(TreeError::TooDeep)?;
        let mc = self.mc;
        Ok(match self.node(stx).shape {
            Shape::Id(symbol) => symbol.value(mc),
            Shape::Datum(value) => value,
            Shape::List { first, len, dotted } => {
                let mut items = Vec::with_capacity(len as usize);
                for i in first..first + len {
                    items.push(self.strip(self.kids[i as usize], depth)?);
                }
                let tail = if dotted { items.pop().expect("a dotted list has a tail") } else { Value::NIL };
                Pairs::new(mc).list_with_tail(items, tail)?
            }
            Shape::Vector { first, len } => {
                let mut items = Vec::with_capacity(len as usize);
                for i in first..first + len {
                    items.push(self.strip(self.kids[i as usize], depth)?);
                }
                Vectors::new(mc).immutable_from_slice(&items)?.value(mc)
            }
        })
    }
}
