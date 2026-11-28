//! The reader turns source text into [`Syntax`] nodes. It builds the nodes from the tokens of
//! `ragwort-parser-scheme`.
//!
//! The reader accepts the syntax of R7RS, and keywords as Racket writes them:
//!
//! - identifiers, including `|`-quoted identifiers
//! - lists in `()` or `[]`, with dotted tails as in `(a b . c)`
//! - vectors, written `#(a b)`
//! - the abbreviations `'`, `` ` ``, `,` and `,@`, and the syntax abbreviations `#'`, `` #` ``, `#,` and `#,@`
//! - literals: booleans, `#nil`, `#none`, numbers (including complex numbers), strings, characters,
//!   bytevectors written `#u8(1 2)`, and keywords written `#:name`
//!
//! `;` line comments, nested `#| |#` block comments and `#;` datum comments are skipped. After
//! `#!fold-case`, identifiers, keywords and character names are read in lower case until `#!no-fold-case`.
//!
//! `#n=datum` labels a datum. A later `#n#` in the same top-level datum is the same node.
//! A label cannot be referenced inside the datum that it labels, because no later stage accepts cyclic syntax.
//!
//! Any other syntax is an [`ErrorKind::Unsupported`] error.
//!
//! Open lists are kept in vectors, not on the native stack, so deep nesting cannot overflow
//! the stack.

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

/// A construct that is open and not complete yet. A list, vector or bytevector waits for its closing bracket. A prefix, datum comment or label waits for its datum.
enum Open<'gc> {
    /// `items[first..]` holds the items read so far for this list.
    List { start: usize, close: Bracket, first: usize, tail: Tail<'gc>, shape: Shape },
    /// A quote or other abbreviation, which wraps the next datum.
    Prefix { start: usize, end: usize, meta: SyntaxMeta<'gc> },
    /// A `#;` comment, which discards the next datum.
    Skip { start: usize, end: usize },
    /// A `#n=` label, which labels the next datum.
    Label { start: usize, end: usize, n: u64 },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    List,
    Vector,
    Bytevector,
}

/// The reason the datum of a list, vector or bytevector could not be built. `Item` is a bytevector item that is not a byte. `Arena` is an error from the arena.
enum Grow<'gc> {
    Item(Syntax<'gc>),
    Arena(ragwort_types::Error),
}

impl From<OutOfMemory> for Grow<'_> {
    fn from(error: OutOfMemory) -> Self {
        Grow::Arena(error.into())
    }
}

#[derive(Clone, Copy)]
enum Tail<'gc> {
    None,
    /// A `.` was read at this byte offset, and the tail datum has not been read yet.
    Dot(usize),
    Datum(Value<'gc>),
}

/// Reads the data in a session's text one at a time. It is also an iterator. After an error, the reader returns no more data.
pub struct Reader<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    strings: Strings<'a, 'gc>,
    pairs: Pairs<'a, 'gc>,
    nums: Nums<'a, 'gc>,
    symbols: Symbols<'gc>,
    source: SyntaxSource<'gc>,
    lexer: Lexer<'gc>,
    /// The byte offset where the current token ends.
    at: usize,
    /// Nodes built by the reader have no lexical context and no expansion origin. So all nodes of one kind share one [`SyntaxMeta`].
    identifier: SyntaxMeta<'gc>,
    literal: SyntaxMeta<'gc>,
    list: SyntaxMeta<'gc>,
    vector: SyntaxMeta<'gc>,
    /// The metadata for each [`Abbreviation`], in the order of `Abbreviation::ALL`.
    abbreviations: Vec<SyntaxMeta<'gc>>,
    /// The open constructs, innermost last. `open` and `items` are both charged to the arena's budget, so deep nesting cannot use
    /// more memory than the budget allows.
    open: ScratchVec<'gc, Open<'gc>>,
    /// The items of every open list. The items of an inner list follow the items of the list that encloses it.
    items: ScratchVec<'gc, Value<'gc>>,
    /// The labelled data of the top-level datum being read, keyed by label number. An entry is `None` while its datum is still being read.
    labels: HashMap<u64, Option<Syntax<'gc>>>,
}

impl<'a, 'gc> Reader<'a, 'gc> {
    /// Creates a reader of `session`'s text. Identifiers are interned in `symbols`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: Symbols<'gc>, session: &SyntaxSession) -> Result<Self, ReadError> {
        let source = session.source(mc).map_err(|_| ReadError::new(ErrorKind::ForeignSession, 0, 0))?;
        let bytes = session.text(mc).map_err(|_| ReadError::new(ErrorKind::ForeignSession, 0, 0))?.bytes(mc);
        let text = std::str::from_utf8(bytes).map_err(|error| {
            let at = error.valid_up_to();
            ReadError::new(ErrorKind::InvalidUtf8, at, error.error_len().map_or(bytes.len(), |length| at + length))
        })?;
        fn meta<'gc>(mc: &Mutation<'gc>, kind: SyntaxKind) -> Result<SyntaxMeta<'gc>, ReadError> {
            SyntaxMeta::new(mc, kind, None, None).map_err(|error| ReadError::new(error, 0, 0))
        }
        Ok(Self {
            mc,
            strings: Strings::new(mc),
            pairs: Pairs::new(mc),
            nums: Nums::new(mc),
            symbols,
            source,
            lexer: Lexer::new(text),
            at: 0,
            identifier: meta(mc, SyntaxKind::Identifier)?,
            literal: meta(mc, SyntaxKind::Literal)?,
            list: meta(mc, SyntaxKind::List)?,
            vector: meta(mc, SyntaxKind::Vector)?,
            abbreviations: Abbreviation::ALL.iter().map(|&kind| meta(mc, SyntaxKind::Abbreviation(kind))).collect::<Result<_, _>>()?,
            open: ScratchVec::new(mc),
            items: ScratchVec::new(mc),
            labels: HashMap::new(),
        })
    }

    pub fn source(&self) -> SyntaxSource<'gc> {
        self.source
    }

    /// Returns the next datum, or `None` at the end of the text. After an error, every later call returns `None`.
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
            let lexeme = self.lexer.next_token().map_err(|error| ReadError::new(error.kind, error.start, error.end))?;
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
                Token::Label(label) => {
                    if self.labels.contains_key(&label) {
                        return Err(ReadError::new(ErrorKind::DuplicateLabel, start, self.at));
                    }
                    self.labels.insert(label, None);
                    self.push(Open::Label { start, end: self.at, n: label }, start)?;
                    continue;
                }
                Token::LabelRef(label) => match self.labels.get(&label) {
                    Some(&Some(node)) => node,
                    Some(None) => return Err(ReadError::new(ErrorKind::CyclicLabel, start, self.at)),
                    None => return Err(ReadError::new(ErrorKind::UnknownLabel, start, self.at)),
                },
                Token::Dot => {
                    self.dot(start)?;
                    continue;
                }
                Token::Boolean(boolean) => {
                    let value = if boolean {
                        Value::TRUE
                    } else {
                        Value::FALSE
                    };
                    self.node(value, self.literal, start)?
                }
                Token::Nil => self.node(Value::NIL, self.literal, start)?,
                Token::NoneValue => self.node(Value::NONE, self.literal, start)?,
                Token::Char(character) => self.node(Value::char(character), self.literal, start)?,
                Token::String(text) => {
                    let string = string::from_str(&self.strings, &text).map_err(|error| ReadError::new(error, start, self.at))?;
                    self.node(string.value(), self.literal, start)?
                }
                Token::Identifier(name) => self.identifier(&name, start)?,
                Token::Keyword(name) => {
                    let symbol = self.symbols.intern_str(&self.strings, &name).map_err(|error| ReadError::new(error, start, self.at))?;
                    let keyword = self.symbols.keyword(self.mc, symbol).map_err(|error| ReadError::new(error, start, self.at))?;
                    self.node(keyword.value(self.mc), self.literal, start)?
                }
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
        self.open.push(open).map_err(|error| ReadError::new(error, start, self.at))
    }

    fn number(&self, text: &str, start: usize) -> Result<Option<Value<'gc>>, ReadError> {
        let number = number::parse(&self.nums, text).map_err(|error| ReadError::new(error, start, self.at))?;
        Ok(number.map(|parsed| parsed.value()))
    }

    fn identifier(&self, name: &str, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let symbol = self.symbols.intern_str(&self.strings, name).map_err(|error| ReadError::new(error, start, self.at))?;
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

    /// Returns the node for the list, vector or bytevector that the closing `bracket` at `start` completes.
    fn close(&mut self, start: usize, bracket: Bracket) -> Result<Syntax<'gc>, ReadError> {
        match self.open.pop() {
            Some(Open::List { start: open, close, first, tail, shape }) if close == bracket => {
                let tail = match tail {
                    Tail::None => Value::NULL,
                    Tail::Datum(tail) => tail,
                    Tail::Dot(dot) => return Err(ReadError::new(ErrorKind::BadDot, dot, dot + 1)),
                };
                let items = &self.items[first..];
                let (datum, meta) = match shape {
                    Shape::List => (self.pairs.list_with_tail(items.iter().copied(), tail).map_err(Grow::from), self.list),
                    Shape::Vector => (Vectors::new(self.mc).immutable_from_slice(items).map(|vector| vector.value(self.mc)).map_err(Grow::from), self.vector),
                    Shape::Bytevector => (self.bytes(items).and_then(|bytes| Ok(Bytevectors::new(self.mc).immutable_from_slice(&bytes)?.value(self.mc))), self.literal),
                };
                let datum = datum.map_err(|error| match error {
                    Grow::Item(node) => ReadError::new(ErrorKind::BadByte, node.span(self.mc).start() as usize, node.span(self.mc).end() as usize),
                    Grow::Arena(error) => ReadError::new(error, open, self.at),
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

    /// Delivers the finished datum `node` to the constructs that enclose it. Each enclosing prefix wraps it. An enclosing `#;` discards it, an enclosing label records it,
    /// and an enclosing list takes it as an item or as its tail. Returns the datum if it is at the top level, and `None` otherwise.
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
                Some(&mut Open::Label { n: label, .. }) => {
                    self.open.pop();
                    self.labels.insert(label, Some(node));
                }
                Some(Open::List { tail, .. }) => {
                    let value = node.value(self.mc);
                    let span = node.span(self.mc);
                    match *tail {
                        Tail::None => self.items.push(value).map_err(|error| ReadError::new(error, span.start() as usize, span.end() as usize))?,
                        Tail::Dot(_) => *tail = Tail::Datum(value),
                        Tail::Datum(_) => return Err(ReadError::new(ErrorKind::BadDot, span.start() as usize, span.end() as usize)),
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

    /// Handles the end of the text. Returns `None` at the top level. Fails if a list is still open, or if a prefix, `#;` or label has no datum after it.
    fn end(&self) -> Result<Option<Syntax<'gc>>, ReadError> {
        match self.open.last() {
            None => Ok(None),
            Some(&Open::List { start, .. }) => Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)),
            Some(&(Open::Prefix { start, end, .. } | Open::Skip { start, end } | Open::Label { start, end, .. })) => {
                Err(ReadError::new(ErrorKind::EmptyQuote, start, end))
            }
        }
    }

    /// Returns the bytes of a bytevector whose items are `items`. Fails with the first item that is not an exact integer from 0
    /// to 255.
    fn bytes(&self, items: &[Value<'gc>]) -> Result<Vec<u8>, Grow<'gc>> {
        items
            .iter()
            .map(|&item| {
                let node = Syntax::of(item).expect("list items are syntax");
                let byte = node.datum(self.mc).as_fixnum().and_then(|number| u8::try_from(number).ok());
                byte.filter(|_| node.kind(self.mc) == Some(SyntaxKind::Literal)).ok_or(Grow::Item(node))
            })
            .collect()
    }

    /// Creates a node for `datum` with the metadata `meta`. Its span runs from `start` to the end of the current token.
    fn node(&self, datum: Value<'gc>, meta: SyntaxMeta<'gc>, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let span = SyntaxSpan::new(self.mc, self.source, start as u32, self.at as u32).expect("spans lie in the text");
        Syntax::new(self.mc, datum, span, Some(meta)).map_err(|error| ReadError::new(error, start, self.at))
    }
}

/// Returns the [`Abbreviation`] that the token `prefix` stands for.
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

/// Reads every datum in `session`'s text. Identifiers are interned in `symbols`.
pub fn read_all<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, session: &SyntaxSession) -> Result<Vec<Syntax<'gc>>, ReadError> {
    Reader::new(mc, symbols, session)?.collect()
}
