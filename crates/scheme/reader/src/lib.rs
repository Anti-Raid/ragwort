//! The reader: source text to [`Syntax`] nodes, from the tokens of `ragwort-parser-scheme`. It
//! reads identifiers, `|`-quoted ones too, lists
//! in `()` or `[]`, dotted tails as in `(a b . c)`, vectors as `#(a b)`, the `'`, `` ` ``, `,`
//! and `,@` abbreviations, and as literals booleans, numbers (complex ones too), strings,
//! characters and bytevectors as `#u8(1 2)`, as R7RS writes them. `;` line comments, nested
//! `#| |#` block comments and `#;` datum comments are skipped, and after `#!fold-case`,
//! identifiers and character names are read in lower case until `#!no-fold-case`.
//!
//! `#n=datum` labels a datum, and a later `#n#` in the same top-level datum is the same node.
//! A label can't be used inside the datum it labels, as nothing after the reader takes cycles.
//!
//! Anything else is an [`ErrorKind::Unsupported`] error.
//!
//! Open lists are kept in vectors rather than on the native stack, so deep nesting can't
//! overflow it.

mod error;

#[cfg(test)]
#[path = "tests/reader.rs"]
mod tests;

pub use error::{ErrorKind, ReadError};

use std::collections::HashMap;

use ragwort_parser_scheme::{Bracket, Lexer, Prefix, Token, number};

use ragwort_types::bytevector::Bytevectors;
use ragwort_types::gc::{Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::num::Nums;
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind, SyntaxMeta, SyntaxSession, SyntaxSource, SyntaxSpan};
use ragwort_types::vector::Vectors;

/// A list, vector or prefix still waiting for its end.
enum Open<'gc> {
    /// `items[first..]` are the list's so far.
    List { start: usize, close: Bracket, first: usize, tail: Tail<'gc>, shape: Shape },
    /// A quote or other abbreviation, which wraps the next datum.
    Prefix { start: usize, end: usize, meta: SyntaxMeta<'gc> },
    /// A `#;` comment, which drops the next datum.
    Skip { start: usize, end: usize },
    /// A `#n=` label, which names the next datum.
    Label { start: usize, end: usize, n: u64 },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    List,
    Vector,
    Bytevector,
}

/// Why a list's datum couldn't be made: an item it can't hold, or the arena.
enum Grow<'gc> {
    Item(Syntax<'gc>),
    Arena(ragwort_types::Error),
}

impl From<OutOfMemory> for Grow<'_> {
    fn from(e: OutOfMemory) -> Self {
        Grow::Arena(e.into())
    }
}

#[derive(Clone, Copy)]
enum Tail<'gc> {
    None,
    /// A `.` at this byte, waiting for the tail.
    Dot(usize),
    Datum(Value<'gc>),
}

/// Reads the data in a session's text one at a time, as an iterator. An error ends the text.
pub struct Reader<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    strings: Strings<'a, 'gc>,
    pairs: Pairs<'a, 'gc>,
    nums: Nums<'a, 'gc>,
    symbols: Symbols<'gc>,
    source: SyntaxSource<'gc>,
    lexer: Lexer<'gc>,
    /// Where the token being read ends.
    at: usize,
    /// The nodes the reader makes have no context or origin, so each kind shares one.
    identifier: SyntaxMeta<'gc>,
    literal: SyntaxMeta<'gc>,
    list: SyntaxMeta<'gc>,
    vector: SyntaxMeta<'gc>,
    /// Each [`Abbreviation`]'s metadata, in order.
    abbreviations: Vec<SyntaxMeta<'gc>>,
    /// Innermost last. Both count against the arena's budget, so deep nesting can't use
    /// memory past it.
    open: ScratchVec<'gc, Open<'gc>>,
    /// The items of every open list, each list's after those of the list around it.
    items: ScratchVec<'gc, Value<'gc>>,
    /// The labelled data of the top-level datum being read, `None` while still being read.
    labels: HashMap<u64, Option<Syntax<'gc>>>,
}

impl<'a, 'gc> Reader<'a, 'gc> {
    /// A reader of `session`'s text that interns identifiers in `symbols`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, session: &SyntaxSession) -> Result<Self, ReadError> {
        let foreign = |_| ReadError::new(ErrorKind::ForeignSession, 0, 0);
        let source = session.source(mc).map_err(foreign)?;
        let bytes = session.text(mc).map_err(foreign)?.bytes(mc);
        let text = std::str::from_utf8(bytes).map_err(|e| {
            let at = e.valid_up_to();
            ReadError::new(ErrorKind::InvalidUtf8, at, e.error_len().map_or(bytes.len(), |n| at + n))
        })?;
        let oom = |e| ReadError::new(e, 0, 0);
        let meta = |kind| SyntaxMeta::new(mc, kind, None, None).map_err(oom);
        let abbreviation = |a| meta(SyntaxKind::Abbreviation(a));
        Ok(Self {
            mc,
            strings: Strings::new(mc),
            pairs: Pairs::new(mc),
            nums: Nums::new(mc),
            symbols,
            source,
            lexer: Lexer::new(text),
            at: 0,
            identifier: meta(SyntaxKind::Identifier)?,
            literal: meta(SyntaxKind::Literal)?,
            list: meta(SyntaxKind::List)?,
            vector: meta(SyntaxKind::Vector)?,
            abbreviations: Abbreviation::ALL.iter().map(|&a| abbreviation(a)).collect::<Result<_, _>>()?,
            open: ScratchVec::new(mc),
            items: ScratchVec::new(mc),
            labels: HashMap::new(),
        })
    }

    pub fn source(&self) -> SyntaxSource<'gc> {
        self.source
    }

    /// The next datum, or `None` once the text is read.
    pub fn read(&mut self) -> Result<Option<Syntax<'gc>>, ReadError> {
        let read = self.read_datum();
        if read.is_err() {
            self.open.clear();
            self.items.clear();
            self.labels.clear();
            self.lexer.finish();
        }
        read
    }

    fn read_datum(&mut self) -> Result<Option<Syntax<'gc>>, ReadError> {
        loop {
            let lexeme = self.lexer.next_token().map_err(|e| ReadError::new(e.kind, e.start, e.end))?;
            let Some(lexeme) = lexeme else { return self.end() };
            let start = lexeme.start;
            self.at = lexeme.end;
            let node = match lexeme.token {
                Token::Open(close) => {
                    self.open_list(start, close, Shape::List)?;
                    continue;
                }
                Token::OpenVector => {
                    self.open_list(start, Bracket::Round, Shape::Vector)?;
                    continue;
                }
                Token::OpenBytevector => {
                    self.open_list(start, Bracket::Round, Shape::Bytevector)?;
                    continue;
                }
                Token::Close(close) => self.close(start, close)?,
                Token::Prefix(prefix) => {
                    let meta = self.abbreviations[abbreviation(prefix) as usize];
                    self.push(Open::Prefix { start, end: self.at, meta }, start)?;
                    continue;
                }
                Token::DatumComment => {
                    self.push(Open::Skip { start, end: self.at }, start)?;
                    continue;
                }
                Token::Label(n) => {
                    if self.labels.contains_key(&n) {
                        return Err(ReadError::new(ErrorKind::DuplicateLabel, start, self.at));
                    }
                    self.labels.insert(n, None);
                    self.push(Open::Label { start, end: self.at, n }, start)?;
                    continue;
                }
                Token::LabelRef(n) => match self.labels.get(&n) {
                    Some(&Some(node)) => node,
                    Some(None) => return Err(ReadError::new(ErrorKind::CyclicLabel, start, self.at)),
                    None => return Err(ReadError::new(ErrorKind::UnknownLabel, start, self.at)),
                },
                Token::Dot => {
                    self.dot(start)?;
                    continue;
                }
                Token::Boolean(b) => self.node(if b { Value::TRUE } else { Value::FALSE }, self.literal, start)?,
                Token::Char(c) => self.node(Value::char(c), self.literal, start)?,
                Token::String(text) => {
                    let s = string::from_str(&self.strings, &text).map_err(|e| ReadError::new(e, start, self.at))?;
                    self.node(s.value(), self.literal, start)?
                }
                Token::Identifier(name) => self.identifier(&name, start)?,
                Token::Number(text) => {
                    let number = self.number(text, start)?.ok_or(ReadError::new(ErrorKind::BadNumber, start, self.at))?;
                    self.node(number, self.literal, start)?
                }
                Token::NumberOr { text, name } => match self.number(text, start)? {
                    Some(number) => self.node(number, self.literal, start)?,
                    None => self.identifier(&name, start)?,
                },
            };
            if let Some(done) = self.finish(node)? {
                return Ok(Some(done));
            }
        }
    }

    fn open_list(&mut self, start: usize, close: Bracket, shape: Shape) -> Result<(), ReadError> {
        self.push(Open::List { start, close, first: self.items.len(), tail: Tail::None, shape }, start)
    }

    fn push(&mut self, open: Open<'gc>, start: usize) -> Result<(), ReadError> {
        self.open.push(open).map_err(|e| ReadError::new(e, start, self.at))
    }

    fn number(&self, text: &str, start: usize) -> Result<Option<Value<'gc>>, ReadError> {
        let number = number::parse(&self.nums, text).map_err(|e| ReadError::new(e, start, self.at))?;
        Ok(number.map(|z| z.value()))
    }

    fn identifier(&self, name: &str, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let symbol = self.symbols.intern_str(&self.strings, name).map_err(|e| ReadError::new(e, start, self.at))?;
        self.node(symbol.value(self.mc), self.identifier, start)
    }

    fn dot(&mut self, at: usize) -> Result<(), ReadError> {
        let len = self.items.len();
        if let Some(Open::List { first, tail: tail @ Tail::None, shape: Shape::List, .. }) = self.open.last_mut()
            && len > *first
        {
            *tail = Tail::Dot(at);
            return Ok(());
        }
        Err(ReadError::new(ErrorKind::BadDot, at, at + 1))
    }

    /// The list or vector a `byte` at `start` closes.
    fn close(&mut self, start: usize, bracket: Bracket) -> Result<Syntax<'gc>, ReadError> {
        match self.open.pop() {
            Some(Open::List { start: open, close, first, tail, shape }) if close == bracket => {
                let tail = match tail {
                    Tail::None => Value::NIL,
                    Tail::Datum(tail) => tail,
                    Tail::Dot(dot) => return Err(ReadError::new(ErrorKind::BadDot, dot, dot + 1)),
                };
                let items = &self.items[first..];
                let (datum, meta) = match shape {
                    Shape::List => (self.pairs.list_with_tail(items.iter().copied(), tail).map_err(Grow::from), self.list),
                    Shape::Vector => (Vectors::new(self.mc).immutable_from_slice(items).map(|v| v.value(self.mc)).map_err(Grow::from), self.vector),
                    Shape::Bytevector => (self.bytes(items).and_then(|b| Ok(Bytevectors::new(self.mc).immutable_from_slice(&b)?.value(self.mc))), self.literal),
                };
                let datum = datum.map_err(|e| match e {
                    Grow::Item(node) => ReadError::new(ErrorKind::BadByte, node.span(self.mc).start() as usize, node.span(self.mc).end() as usize),
                    Grow::Arena(e) => ReadError::new(e, open, self.at),
                })?;
                self.items.truncate(first);
                self.node(datum, meta, open)
            }
            Some(Open::List { start: open, .. }) => {
                Err(ReadError::new(ErrorKind::Mismatched { open: open as u32 }, start, start + 1))
            }
            Some(Open::Prefix { start, end, .. } | Open::Skip { start, end } | Open::Label { start, end, .. }) => {
                Err(ReadError::new(ErrorKind::EmptyQuote, start, end))
            }
            None => Err(ReadError::new(ErrorKind::UnexpectedClose, start, start + 1)),
        }
    }

    /// Hands a datum to the prefixes and list it's in, or back if it's in none.
    fn finish(&mut self, mut node: Syntax<'gc>) -> Result<Option<Syntax<'gc>>, ReadError> {
        loop {
            match self.open.last_mut() {
                Some(&mut Open::Prefix { start, meta, .. }) => {
                    self.open.pop();
                    node = self.node(node.value(self.mc), meta, start)?;
                }
                Some(Open::Skip { .. }) => {
                    self.open.pop();
                    return Ok(None);
                }
                Some(&mut Open::Label { n, .. }) => {
                    self.open.pop();
                    self.labels.insert(n, Some(node));
                }
                Some(Open::List { tail, .. }) => {
                    let value = node.value(self.mc);
                    let span = node.span(self.mc);
                    let at = |kind: ErrorKind| ReadError::new(kind, span.start() as usize, span.end() as usize);
                    match *tail {
                        Tail::None => self.items.push(value).map_err(|e| at(e.into()))?,
                        Tail::Dot(_) => *tail = Tail::Datum(value),
                        Tail::Datum(_) => return Err(at(ErrorKind::BadDot)),
                    }
                    return Ok(None);
                }
                None => {
                    self.labels.clear();
                    return Ok(Some(node));
                }
            }
        }
    }

    /// The text ran out: an error inside a list or after a prefix.
    fn end(&self) -> Result<Option<Syntax<'gc>>, ReadError> {
        match self.open.last() {
            None => Ok(None),
            Some(&Open::List { start, .. }) => Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)),
            Some(&(Open::Prefix { start, end, .. } | Open::Skip { start, end } | Open::Label { start, end, .. })) => {
                Err(ReadError::new(ErrorKind::EmptyQuote, start, end))
            }
        }
    }

    /// The bytes a bytevector's `items` are, or the first that isn't an exact integer from 0
    /// to 255.
    fn bytes(&self, items: &[Value<'gc>]) -> Result<Vec<u8>, Grow<'gc>> {
        items
            .iter()
            .map(|&v| {
                let node = Syntax::of(v).expect("list items are syntax");
                let byte = node.datum(self.mc).as_fixnum().and_then(|n| u8::try_from(n).ok());
                byte.filter(|_| node.kind(self.mc) == Some(SyntaxKind::Literal)).ok_or(Grow::Item(node))
            })
            .collect()
    }

    /// A node for `datum`, from `start` to the reader's position.
    fn node(&self, datum: Value<'gc>, meta: SyntaxMeta<'gc>, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let span = SyntaxSpan::new(self.mc, self.source, start as u32, self.at as u32).expect("spans lie in the text");
        Syntax::new(self.mc, datum, span, Some(meta)).map_err(|e| ReadError::new(e, start, self.at))
    }
}

/// The abbreviation `prefix` writes.
fn abbreviation(prefix: Prefix) -> Abbreviation {
    match prefix {
        Prefix::Quote => Abbreviation::Quote,
        Prefix::Quasiquote => Abbreviation::Quasiquote,
        Prefix::Unquote => Abbreviation::Unquote,
        Prefix::UnquoteSplicing => Abbreviation::UnquoteSplicing,
        Prefix::Syntax => Abbreviation::Syntax,
        Prefix::Quasisyntax => Abbreviation::Quasisyntax,
        Prefix::Unsyntax => Abbreviation::Unsyntax,
        Prefix::UnsyntaxSplicing => Abbreviation::UnsyntaxSplicing,
    }
}

impl<'gc> Iterator for Reader<'_, 'gc> {
    type Item = Result<Syntax<'gc>, ReadError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.read().transpose()
    }
}

/// Every datum in `session`'s text.
pub fn read_all<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, session: &SyntaxSession) -> Result<Vec<Syntax<'gc>>, ReadError> {
    Reader::new(mc, symbols, session)?.collect()
}
