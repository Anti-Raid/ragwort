//! Syntax as the expander works on it: a tree of nodes on the host, in storage charged to the
//! arena's budget, each node with its scopes and the span of text it came from. A [`Stx`] is a
//! node and the scope changes pending on it, which reach its parts as they're taken apart.
//!
//! The nodes hold arena values untraced, so a tree must be used and dropped within the step
//! that made it.

use ragwort_types::gc::{Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::{Keyword, Symbol};
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

    /// The keyword `stx` is, if it's one, as `#:name` reads.
    pub(crate) fn keyword(&self, stx: Stx) -> Option<Keyword<'gc>> {
        match self.node(stx).shape {
            Shape::Datum(value) => Keyword::of(value),
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

    /// The tree of what the reader read, its nodes in no scopes. Each node's parts are made
    /// before it, from a stack of their own.
    pub(crate) fn read(&mut self, root: Syntax<'gc>) -> Result<Stx, OutOfMemory> {
        enum Task<'gc> {
            Visit(Syntax<'gc>),
            /// A list or vector of the last parts made, after the tail if it's dotted.
            Make(Syntax<'gc>, usize, bool),
        }
        let mc = self.mc;
        let part = |v: Value<'gc>| Task::Visit(Syntax::of(v).expect("the reader wraps every part"));
        let (mut todo, mut done) = (vec![Task::Visit(root)], Vec::new());
        while let Some(task) = todo.pop() {
            let node = match task {
                Task::Visit(node) => node,
                Task::Make(node, n, dotted) => {
                    let items = done.split_off(done.len() - n);
                    let (first, len) = self.parts(items)?;
                    let shape = match node.kind(mc) {
                        Some(SyntaxKind::Vector) => Shape::Vector { first, len },
                        _ => Shape::List { first, len, dotted },
                    };
                    done.push(self.make(shape, Set::EMPTY, node.span(mc))?);
                    continue;
                }
            };
            let at = todo.len();
            match node.kind(mc) {
                Some(SyntaxKind::Identifier) => {
                    let symbol = Symbol::of(node.datum(mc)).expect("identifiers are symbols");
                    done.push(self.make(Shape::Id(symbol), Set::EMPTY, node.span(mc))?);
                }
                Some(SyntaxKind::List) => {
                    let mut elements = Pairs::new(mc).elements(node.datum(mc));
                    todo.extend(elements.by_ref().map(part));
                    let tail = elements.rest();
                    let dotted = tail != Value::NIL;
                    if dotted {
                        todo.push(part(tail));
                    }
                    todo.push(Task::Make(node, todo.len() - at, dotted));
                }
                Some(SyntaxKind::Vector) => {
                    let vector = Vectors::new(mc).vector(node.datum(mc)).expect("vector nodes hold vectors");
                    todo.extend((0..vector.len(mc)).filter_map(|i| vector.get(mc, i)).map(part));
                    todo.push(Task::Make(node, todo.len() - at, false));
                }
                Some(SyntaxKind::Abbreviation(a)) => {
                    let name = self.abbreviations[a as usize];
                    done.push(self.id(name, Set::EMPTY, node.span(mc))?);
                    // A list of the abbreviation's name, made already, and what it abbreviates.
                    todo.extend([part(node.datum(mc)), Task::Make(node, 2, false)]);
                }
                Some(SyntaxKind::Literal) | None => done.push(self.make(Shape::Datum(node.datum(mc)), Set::EMPTY, node.span(mc))?),
            }
            todo[at..].reverse();
        }
        Ok(done.pop().expect("the root's made"))
    }

    /// The datum `stx` stands for, without its scopes and spans. Each list or vector is made of
    /// its items' data, from a stack of their own.
    pub(crate) fn strip(&mut self, root: Stx) -> Result<Value<'gc>, OutOfMemory> {
        enum Task {
            Visit(Stx),
            /// A list of the last items stripped, the last of them its tail if it's dotted.
            List(u32, bool),
            Vector(u32),
        }
        let mc = self.mc;
        let (mut todo, mut done) = (vec![Task::Visit(root)], Vec::new());
        while let Some(task) = todo.pop() {
            let stx = match task {
                Task::Visit(stx) => stx,
                Task::List(len, dotted) => {
                    let mut items = done.split_off(done.len() - len as usize);
                    let tail = if dotted { items.pop().expect("a dotted list has a tail") } else { Value::NIL };
                    done.push(Pairs::new(mc).list_with_tail(items, tail)?);
                    continue;
                }
                Task::Vector(len) => {
                    let items = done.split_off(done.len() - len as usize);
                    done.push(Vectors::new(mc).immutable_from_slice(&items)?.value(mc));
                    continue;
                }
            };
            let (first, len, made) = match self.node(stx).shape {
                Shape::Id(symbol) => {
                    done.push(symbol.value(mc));
                    continue;
                }
                Shape::Datum(value) => {
                    done.push(value);
                    continue;
                }
                Shape::List { first, len, dotted } => (first, len, Task::List(len, dotted)),
                Shape::Vector { first, len } => (first, len, Task::Vector(len)),
            };
            todo.push(made);
            todo.extend((first..first + len).rev().map(|i| Task::Visit(self.kids[i as usize])));
        }
        Ok(done.pop().expect("the root's stripped"))
    }
}
