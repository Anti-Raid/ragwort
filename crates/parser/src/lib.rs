//! The reader: source text to [`Syntax`] nodes. For now it reads identifiers, lists in `()` or
//! `[]`, dotted tails as in `(a b . c)`, and `'` quotes. Anything else it might later read as
//! something other than an identifier, such as `42`, is an [`ErrorKind::Unsupported`] error.
//!
//! Open lists are kept in vectors rather than on the native stack, so deep nesting can't
//! overflow it.

mod error;

#[cfg(test)]
#[path = "tests/reader.rs"]
mod tests;

pub use error::{ErrorKind, ReadError};

use ragwort_types::gc::{Gc, Member, Mutation, Value};
use ragwort_types::gc_prims::ScratchVec;
use ragwort_types::pair::Pairs;
use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind, SyntaxMeta, SyntaxSession, SyntaxSource, SyntaxSpan};

fn is_space(b: u8) -> bool {
    const SPACES: u64 = 1 << b' ' | 1 << b'\t' | 1 << b'\n' | 1 << b'\r' | 1 << 0x0b | 1 << 0x0c;
    b < 64 && SPACES >> b & 1 != 0
}

/// Whitespace and the bytes that end an identifier.
const ENDS_NAME: [bool; 256] = byte_set(b" \t\n\r\x0b\x0c()[]{}\"';`,");

/// A lookup table, faster here than `matches!`. `for` isn't allowed in `const fn`.
const fn byte_set(bytes: &[u8]) -> [bool; 256] {
    let mut set = [false; 256];
    let mut i = 0;
    while i < bytes.len() {
        set[bytes[i] as usize] = true;
        i += 1;
    }
    set
}

/// A list or quote still waiting for its end.
enum Open<'gc> {
    /// `items[first..]` are the list's so far.
    List { start: usize, close: u8, first: usize, tail: Tail<'gc> },
    Quote { start: usize },
}

#[derive(Clone, Copy)]
enum Tail<'gc> {
    None,
    /// A `.` at this byte, waiting for the tail.
    Dot(usize),
    Datum(Value<'gc>),
}

type Meta<'gc> = Member<'gc, SyntaxMeta<'gc>>;

/// Reads the data in a session's text one at a time, as an iterator. An error ends the text.
pub struct Reader<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    strings: Strings<'a, 'gc>,
    pairs: Pairs<'a, 'gc>,
    symbols: &'a Symbols<'gc>,
    source: Gc<'gc, SyntaxSource<'gc>>,
    text: &'gc str,
    at: usize,
    /// The nodes the reader makes have no context or origin, so each kind shares one.
    identifier: Meta<'gc>,
    list: Meta<'gc>,
    quote: Meta<'gc>,
    /// Innermost last. Both count against the arena's budget, so deep nesting can't use
    /// memory past it.
    open: ScratchVec<'gc, Open<'gc>>,
    /// The items of every open list, each list's after those of the list around it.
    items: ScratchVec<'gc, Value<'gc>>,
}

impl<'a, 'gc> Reader<'a, 'gc> {
    /// A reader of `session`'s text that interns identifiers in `symbols`.
    pub fn new(mc: &'a Mutation<'gc>, symbols: &'a Symbols<'gc>, session: &SyntaxSession) -> Result<Self, ReadError> {
        let foreign = |_| ReadError::new(ErrorKind::ForeignSession, 0, 0);
        let source = session.source(mc).map_err(foreign)?;
        let bytes = session.text(mc).map_err(foreign)?.items();
        let text = std::str::from_utf8(bytes).map_err(|e| {
            let at = e.valid_up_to();
            ReadError::new(ErrorKind::InvalidUtf8, at, e.error_len().map_or(bytes.len(), |n| at + n))
        })?;
        let oom = |e| ReadError::new(e, 0, 0);
        let meta = |kind| Ok(Member::new(mc, mc.alloc(SyntaxMeta::new(kind)).map_err(oom)?));
        Ok(Self {
            mc,
            strings: Strings::new(mc).map_err(oom)?,
            pairs: Pairs::new(mc).map_err(oom)?,
            symbols,
            source,
            text,
            at: 0,
            identifier: meta(SyntaxKind::Identifier)?,
            list: meta(SyntaxKind::List)?,
            quote: meta(SyntaxKind::Abbreviation(Abbreviation::Quote))?,
            open: ScratchVec::new(mc),
            items: ScratchVec::new(mc),
        })
    }

    pub fn source(&self) -> Gc<'gc, SyntaxSource<'gc>> {
        self.source
    }

    /// The next datum, or `None` once the text is read.
    pub fn read(&mut self) -> Result<Option<Gc<'gc, Syntax<'gc>>>, ReadError> {
        let read = self.read_datum();
        if read.is_err() {
            self.open.clear();
            self.items.clear();
            self.at = self.text.len();
        }
        read
    }

    fn read_datum(&mut self) -> Result<Option<Gc<'gc, Syntax<'gc>>>, ReadError> {
        loop {
            self.skip_space();
            let start = self.at;
            let Some(&byte) = self.text.as_bytes().get(start) else { return self.end() };
            self.at += 1;
            let node = match byte {
                b'(' | b'[' => {
                    let close = if byte == b'(' { b')' } else { b']' };
                    let list = Open::List { start, close, first: self.items.len(), tail: Tail::None };
                    self.open.push(list).map_err(|e| ReadError::new(e, start, start + 1))?;
                    continue;
                }
                b'\'' => {
                    self.open.push(Open::Quote { start }).map_err(|e| ReadError::new(e, start, start + 1))?;
                    continue;
                }
                b')' | b']' => self.close(start, byte)?,
                b'"' | b'`' | b',' | b'#' | b'|' | b'{' | b'}' => {
                    return Err(ReadError::new(ErrorKind::Unsupported, start, start + 1));
                }
                _ => {
                    let rest = &self.text.as_bytes()[start..];
                    self.at = start + rest.iter().position(|&b| ENDS_NAME[b as usize]).unwrap_or(rest.len());
                    match self.token(start)? {
                        Some(node) => node,
                        None => continue,
                    }
                }
            };
            if let Some(done) = self.finish(node)? {
                return Ok(Some(done));
            }
        }
    }

    fn skip_space(&mut self) {
        let bytes = self.text.as_bytes();
        while let Some(&b) = bytes.get(self.at) {
            if is_space(b) {
                self.at += 1;
            } else if b == b';' {
                self.at = bytes[self.at..].iter().position(|&b| b == b'\n').map_or(bytes.len(), |n| self.at + n + 1);
            } else {
                break;
            }
        }
    }

    /// The identifier from `start` to the reader's position, or `None` for a dot.
    fn token(&mut self, start: usize) -> Result<Option<Gc<'gc, Syntax<'gc>>>, ReadError> {
        let token = &self.text[start..self.at];
        if token == "." {
            self.dot(start)?;
            return Ok(None);
        }
        if matches!(token.as_bytes(), [b'0'..=b'9', ..] | [b'+' | b'-' | b'.', b'0'..=b'9', ..]) {
            return Err(ReadError::new(ErrorKind::Unsupported, start, self.at));
        }
        let symbol = self.symbols.intern_str(&self.strings, token).map_err(|e| ReadError::new(e, start, self.at))?;
        self.node(symbol.value(), self.identifier, start).map(Some)
    }

    fn dot(&mut self, at: usize) -> Result<(), ReadError> {
        let len = self.items.len();
        if let Some(Open::List { first, tail: tail @ Tail::None, .. }) = self.open.last_mut()
            && len > *first
        {
            *tail = Tail::Dot(at);
            return Ok(());
        }
        Err(ReadError::new(ErrorKind::BadDot, at, at + 1))
    }

    /// The list a `byte` at `start` closes.
    fn close(&mut self, start: usize, byte: u8) -> Result<Gc<'gc, Syntax<'gc>>, ReadError> {
        match self.open.pop() {
            Some(Open::List { start: open, close, first, tail }) if close == byte => {
                let tail = match tail {
                    Tail::None => Value::NIL,
                    Tail::Datum(tail) => tail,
                    Tail::Dot(dot) => return Err(ReadError::new(ErrorKind::BadDot, dot, dot + 1)),
                };
                let items = self.items[first..].iter().copied();
                let datum = self.pairs.list_with_tail(items, tail).map_err(|e| ReadError::new(e, open, self.at))?;
                self.items.truncate(first);
                self.node(datum, self.list, open)
            }
            Some(Open::List { start: open, .. }) => {
                Err(ReadError::new(ErrorKind::Mismatched { open: open as u32 }, start, start + 1))
            }
            Some(Open::Quote { start }) => Err(ReadError::new(ErrorKind::EmptyQuote, start, start + 1)),
            None => Err(ReadError::new(ErrorKind::UnexpectedClose, start, start + 1)),
        }
    }

    /// Hands a datum to the quotes and list it's in, or back if it's in none.
    fn finish(&mut self, mut node: Gc<'gc, Syntax<'gc>>) -> Result<Option<Gc<'gc, Syntax<'gc>>>, ReadError> {
        loop {
            match self.open.last_mut() {
                Some(Open::Quote { start }) => {
                    let start = *start;
                    self.open.pop();
                    node = self.node(Value::object(self.mc, node), self.quote, start)?;
                }
                Some(Open::List { tail, .. }) => {
                    let value = Value::object(self.mc, node);
                    let span = node.span();
                    let at = |kind: ErrorKind| ReadError::new(kind, span.start() as usize, span.end() as usize);
                    match *tail {
                        Tail::None => self.items.push(value).map_err(|e| at(e.into()))?,
                        Tail::Dot(_) => *tail = Tail::Datum(value),
                        Tail::Datum(_) => return Err(at(ErrorKind::BadDot)),
                    }
                    return Ok(None);
                }
                None => return Ok(Some(node)),
            }
        }
    }

    /// The text ran out: an error inside a list or after a quote.
    fn end(&self) -> Result<Option<Gc<'gc, Syntax<'gc>>>, ReadError> {
        match self.open.last() {
            None => Ok(None),
            Some(&Open::List { start, .. }) => Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)),
            Some(&Open::Quote { start }) => Err(ReadError::new(ErrorKind::EmptyQuote, start, start + 1)),
        }
    }

    /// A node for `datum`, from `start` to the reader's position.
    fn node(&self, datum: Value<'gc>, meta: Meta<'gc>, start: usize) -> Result<Gc<'gc, Syntax<'gc>>, ReadError> {
        let span = SyntaxSpan::new(self.mc, self.source, start as u32, self.at as u32).expect("spans lie in the text");
        self.mc.alloc(Syntax::new(datum, span).with_metadata(Some(meta))).map_err(|e| ReadError::new(e, start, self.at))
    }
}

impl<'gc> Iterator for Reader<'_, 'gc> {
    type Item = Result<Gc<'gc, Syntax<'gc>>, ReadError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.read().transpose()
    }
}

/// Every datum in `session`'s text.
pub fn read_all<'gc>(
    mc: &Mutation<'gc>,
    symbols: &Symbols<'gc>,
    session: &SyntaxSession,
) -> Result<Vec<Gc<'gc, Syntax<'gc>>>, ReadError> {
    Reader::new(mc, symbols, session)?.collect()
}
