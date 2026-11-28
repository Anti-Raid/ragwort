//! The expander's representation of syntax: a tree of nodes stored on the host. The storage is
//! charged to the arena's budget. Each node has a scope set and the source span it came from. A [`Stx`] is a
//! node index with pending scope operations. `Tree::view` passes the operations on to the node's children.
//!
//! The collector does not trace the arena values that the nodes hold. So a tree must be used and
//! dropped within the step that created it.

use ragwort_types::gc::{Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::{Keyword, Symbol};
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxSpan};
use ragwort_types::vector::Vectors;

use crate::scope::{Map, Op, Ops, Scope, Scopes, Set};

/// A piece of syntax: the index of a node, and the scope operations pending on the node and its children.
#[derive(Clone, Copy, Debug)]
pub struct Stx {
    node: u32,
    ops: Ops,
}

#[derive(Clone, Copy)]
enum Shape<'gc> {
    Id(Symbol<'gc>),
    Datum(Value<'gc>),
    /// The items are `kids[first..first + len]`. If `dotted`, the last item is the tail of an improper list.
    List { first: u32, len: u32, dotted: bool },
    Vector { first: u32, len: u32 },
}

#[derive(Clone, Copy)]
struct Node<'gc> {
    shape: Shape<'gc>,
    scopes: Set,
    span: SyntaxSpan<'gc>,
}

/// The shape of a node, with its children as [`Stx`] values. `List` holds the items and the tail of an improper list.
pub enum View<'gc> {
    Id,
    Datum(Value<'gc>),
    List(Vec<Stx>, Option<Stx>),
    Vector(Vec<Stx>),
}

pub struct Tree<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    nodes: ScratchVec<'gc, Node<'gc>>,
    kids: ScratchVec<'gc, Stx>,
    pub scopes: Scopes<'gc>,
    /// The symbol that each reader abbreviation stands for, indexed by the abbreviation's number.
    abbreviations: Vec<Symbol<'gc>>,
    /// The binding value of each identifier that came from the expansion of another module, keyed by the identifier's node. See [`Tree::origin`].
    origins: Map<u32, Value<'gc>>,
}

impl<'a, 'gc> Tree<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>, abbreviations: Vec<Symbol<'gc>>) -> Self {
        Self { mc, nodes: ScratchVec::new(mc), kids: ScratchVec::new(mc), scopes: Scopes::new(mc), abbreviations, origins: Map::default() }
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

    pub fn id(&mut self, symbol: Symbol<'gc>, scopes: Set, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        self.make(Shape::Id(symbol), scopes, span)
    }

    /// Records `binding` as the origin of the identifier `id`.
    pub fn set_origin(&mut self, id: Stx, binding: Value<'gc>) -> Result<(), OutOfMemory> {
        self.scopes.charge(size_of::<(u32, Value<'gc>)>())?;
        self.origins.insert(id.node, binding);
        Ok(())
    }

    /// Returns the origin of the identifier `id`, if it has one. The origin is the binding value that the identifier's syntax object carried
    /// when a macro of another module introduced it. It says what the identifier refers to in that module.
    pub fn origin(&self, id: Stx) -> Option<Value<'gc>> {
        self.origins.get(&id.node).copied()
    }

    pub fn datum(&mut self, value: Value<'gc>, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        self.make(Shape::Datum(value), Set::EMPTY, span)
    }

    pub fn list(&mut self, items: &[Stx], tail: Option<Stx>, span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        let (first, len) = self.parts(items.iter().copied().chain(tail))?;
        self.make(Shape::List { first, len, dotted: tail.is_some() }, Set::EMPTY, span)
    }

    pub fn vector(&mut self, items: &[Stx], span: SyntaxSpan<'gc>) -> Result<Stx, OutOfMemory> {
        let (first, len) = self.parts(items.iter().copied())?;
        self.make(Shape::Vector { first, len }, Set::EMPTY, span)
    }

    pub fn span(&self, stx: Stx) -> SyntaxSpan<'gc> {
        self.node(stx).span
    }

    /// Returns `stx` with the operation `op` on `scope` pending. `Op::Flip` removes `scope` if the syntax has it, and adds it otherwise.
    pub fn with(&mut self, stx: Stx, scope: Scope, op: Op) -> Result<Stx, OutOfMemory> {
        let op = self.scopes.op(scope, op)?;
        Ok(Stx { node: stx.node, ops: self.scopes.compose(stx.ops, op)? })
    }

    /// Returns the scope set of `stx`, with its pending operations applied.
    pub fn scopes_of(&mut self, stx: Stx) -> Result<Set, OutOfMemory> {
        self.scopes.apply(self.node(stx).scopes, stx.ops)
    }

    pub fn symbol(&self, stx: Stx) -> Option<Symbol<'gc>> {
        match self.node(stx).shape {
            Shape::Id(symbol) => Some(symbol),
            _ => None,
        }
    }

    /// Returns the keyword if `stx` is a keyword datum, such as `#:name`.
    pub fn keyword(&self, stx: Stx) -> Option<Keyword<'gc>> {
        match self.node(stx).shape {
            Shape::Datum(value) => Keyword::of(value),
            _ => None,
        }
    }

    pub fn view(&mut self, stx: Stx) -> Result<View<'gc>, OutOfMemory> {
        Ok(match self.node(stx).shape {
            Shape::Id(_) => View::Id,
            Shape::Datum(value) => View::Datum(value),
            Shape::List { first, len, dotted } => {
                let mut items = self.kids_of(stx, first, len)?;
                let tail = if dotted {
                    items.pop()
                } else {
                    None
                };
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

    /// Converts `root`, a syntax object from the reader, into nodes with empty scope sets. The
    /// traversal uses an explicit stack, and creates the children of a node before the node.
    pub fn read(&mut self, root: Syntax<'gc>) -> Result<Stx, OutOfMemory> {
        enum Task<'gc> {
            Visit(Syntax<'gc>),
            /// Creates the list or vector of a reader node from the last `count` nodes created. If the list is dotted, the last of them is its tail.
            Make(Syntax<'gc>, usize, bool),
        }
        let mc = self.mc;
        fn part<'gc>(value: Value<'gc>) -> Task<'gc> {
            Task::Visit(Syntax::of(value).expect("the reader wraps every part"))
        }
        let (mut todo, mut done) = (vec![Task::Visit(root)], Vec::new());
        while let Some(task) = todo.pop() {
            let node = match task {
                Task::Visit(node) => node,
                Task::Make(node, count, dotted) => {
                    let items = done.split_off(done.len() - count);
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
                    let dotted = tail != Value::NULL;
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
                Some(SyntaxKind::Abbreviation(abbreviation)) => {
                    let name = self.abbreviations[abbreviation as usize];
                    done.push(self.id(name, Set::EMPTY, node.span(mc))?);
                    // An abbreviation becomes a list of two items: its name, which is created above, and the abbreviated datum.
                    todo.extend([part(node.datum(mc)), Task::Make(node, 2, false)]);
                }
                Some(SyntaxKind::Literal) | None => done.push(self.make(Shape::Datum(node.datum(mc)), Set::EMPTY, node.span(mc))?),
            }
            todo[at..].reverse();
        }
        Ok(done.pop().expect("the root's made"))
    }

    /// Returns the datum of `root`, without scopes and spans. The traversal uses an explicit
    /// stack, and builds each list or vector from the data of its items.
    pub fn strip(&mut self, root: Stx) -> Result<Value<'gc>, OutOfMemory> {
        enum Task {
            Visit(Stx),
            /// Builds a list from the last `len` data produced. If the list is dotted, the last datum is its tail.
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
                    let tail = if dotted {
                        items.pop().expect("a dotted list has a tail")
                    } else {
                        Value::NULL
                    };
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
