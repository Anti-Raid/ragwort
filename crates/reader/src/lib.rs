//! The reader: source text to [`Syntax`] nodes. It reads identifiers, `|`-quoted ones too, lists
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
mod number;

#[cfg(test)]
#[path = "tests/reader.rs"]
mod tests;

pub use error::{ErrorKind, ReadError};

use std::collections::HashMap;

use ragwort_types::bytevector::Bytevectors;
use ragwort_types::gc::{Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::num::Nums;
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind, SyntaxMeta, SyntaxSession, SyntaxSource, SyntaxSpan};
use ragwort_types::vector::Vectors;

fn is_space(b: u8) -> bool {
    const SPACES: u64 = 1 << b' ' | 1 << b'\t' | 1 << b'\n' | 1 << b'\r' | 1 << 0x0b | 1 << 0x0c;
    b < 64 && SPACES >> b & 1 != 0
}

/// Whitespace and the bytes that end an identifier.
const ENDS_NAME: [bool; 256] = byte_set(b" \t\n\r\x0b\x0c()[]{}\"';`,|");

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

/// A list, vector or prefix still waiting for its end.
enum Open<'gc> {
    /// `items[first..]` are the list's so far.
    List { start: usize, close: u8, first: usize, tail: Tail<'gc>, shape: Shape },
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
    text: &'gc str,
    at: usize,
    /// The nodes the reader makes have no context or origin, so each kind shares one.
    identifier: SyntaxMeta<'gc>,
    literal: SyntaxMeta<'gc>,
    list: SyntaxMeta<'gc>,
    vector: SyntaxMeta<'gc>,
    /// Quote, quasiquote, unquote and unquote-splicing.
    abbreviations: [SyntaxMeta<'gc>; 4],
    /// Innermost last. Both count against the arena's budget, so deep nesting can't use
    /// memory past it.
    open: ScratchVec<'gc, Open<'gc>>,
    /// The items of every open list, each list's after those of the list around it.
    items: ScratchVec<'gc, Value<'gc>>,
    /// The labelled data of the top-level datum being read, `None` while still being read.
    labels: HashMap<u64, Option<Syntax<'gc>>>,
    /// Whether `#!fold-case` is in effect.
    fold: bool,
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
            text,
            at: 0,
            identifier: meta(SyntaxKind::Identifier)?,
            literal: meta(SyntaxKind::Literal)?,
            list: meta(SyntaxKind::List)?,
            vector: meta(SyntaxKind::Vector)?,
            abbreviations: [
                abbreviation(Abbreviation::Quote)?,
                abbreviation(Abbreviation::Quasiquote)?,
                abbreviation(Abbreviation::Unquote)?,
                abbreviation(Abbreviation::UnquoteSplicing)?,
            ],
            open: ScratchVec::new(mc),
            items: ScratchVec::new(mc),
            labels: HashMap::new(),
            fold: false,
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
            self.at = self.text.len();
        }
        read
    }

    fn read_datum(&mut self) -> Result<Option<Syntax<'gc>>, ReadError> {
        loop {
            self.skip_space()?;
            let start = self.at;
            let Some(&byte) = self.text.as_bytes().get(start) else { return self.end() };
            self.at += 1;
            let node = match byte {
                b'(' | b'[' => {
                    let close = if byte == b'(' { b')' } else { b']' };
                    self.push(Open::List { start, close, first: self.items.len(), tail: Tail::None, shape: Shape::List }, start)?;
                    continue;
                }
                b'\'' | b'`' | b',' => {
                    let which = match byte {
                        b'\'' => 0,
                        b'`' => 1,
                        _ if self.text.as_bytes().get(self.at) == Some(&b'@') => {
                            self.at += 1;
                            3
                        }
                        _ => 2,
                    };
                    self.push(Open::Prefix { start, end: self.at, meta: self.abbreviations[which] }, start)?;
                    continue;
                }
                b')' | b']' => self.close(start, byte)?,
                b'"' => self.string(start)?,
                b'#' => match self.hash(start)? {
                    Some(node) => node,
                    None => continue,
                },
                b'|' => {
                    let name = self.quoted(start, '|')?;
                    let symbol = self.symbols.intern_str(&self.strings, &name).map_err(|e| ReadError::new(e, start, self.at))?;
                    self.node(symbol.value(self.mc), self.identifier, start)?
                }
                b'{' | b'}' => return Err(ReadError::new(ErrorKind::Unsupported, start, start + 1)),
                _ => {
                    self.at = self.name_end(start);
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

    fn push(&mut self, open: Open<'gc>, start: usize) -> Result<(), ReadError> {
        self.open.push(open).map_err(|e| ReadError::new(e, start, self.at))
    }

    /// Where the name starting at `start` ends: at the next delimiter, or the end.
    fn name_end(&self, start: usize) -> usize {
        let rest = &self.text.as_bytes()[start..];
        start + rest.iter().position(|&b| ENDS_NAME[b as usize]).unwrap_or(rest.len())
    }

    fn skip_space(&mut self) -> Result<(), ReadError> {
        let bytes = self.text.as_bytes();
        while let Some(&b) = bytes.get(self.at) {
            if is_space(b) {
                self.at += 1;
            } else if b == b';' {
                self.at = bytes[self.at..].iter().position(|&b| b == b'\n').map_or(bytes.len(), |n| self.at + n + 1);
            } else if b == b'#' && bytes.get(self.at + 1) == Some(&b'|') {
                self.block_comment()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    /// Skips a `#| |#` comment, and those nested in it.
    fn block_comment(&mut self) -> Result<(), ReadError> {
        let (bytes, start) = (self.text.as_bytes(), self.at);
        let (mut depth, mut at) = (0usize, start);
        while at + 1 < bytes.len() {
            match (bytes[at], bytes[at + 1]) {
                (b'#', b'|') => (depth, at) = (depth + 1, at + 2),
                (b'|', b'#') => {
                    (depth, at) = (depth - 1, at + 2);
                    if depth == 0 {
                        self.at = at;
                        return Ok(());
                    }
                }
                _ => at += 1,
            }
        }
        Err(ReadError::new(ErrorKind::Unclosed, start, start + 2))
    }

    /// What follows a `#` at `start`: a vector's or bytevector's opening, a datum comment, a
    /// label or a use of one, a directive, a character, a boolean or a number with prefixes.
    fn hash(&mut self, start: usize) -> Result<Option<Syntax<'gc>>, ReadError> {
        let rest = &self.text.as_bytes()[self.at..];
        let shape = match rest {
            [b'(', ..] => Some((Shape::Vector, 1)),
            [b'u' | b'U', b'8', b'(', ..] => Some((Shape::Bytevector, 3)),
            _ => None,
        };
        if let Some((shape, len)) = shape {
            self.at += len;
            self.push(Open::List { start, close: b')', first: self.items.len(), tail: Tail::None, shape }, start)?;
            return Ok(None);
        }
        let digits = rest.iter().take_while(|b| b.is_ascii_digit()).count();
        if digits > 0 && matches!(rest.get(digits), Some(b'=' | b'#')) {
            return self.label(start, digits);
        }
        match self.text.as_bytes().get(self.at) {
            Some(b';') => {
                self.at += 1;
                self.push(Open::Skip { start, end: self.at }, start)?;
                return Ok(None);
            }
            Some(b'\\') => return self.character(start).map(Some),
            _ => {}
        }
        self.at = self.name_end(self.at);
        let token = &self.text[start..self.at];
        let is = |names: &[&str]| names.iter().any(|name| token.eq_ignore_ascii_case(name));
        let value = match () {
            () if is(&["#t", "#true"]) => Value::TRUE,
            () if is(&["#f", "#false"]) => Value::FALSE,
            () if is(&["#!fold-case", "#!no-fold-case"]) => {
                self.fold = token.len() == "#!fold-case".len();
                return Ok(None);
            }
            _ if matches!(token.as_bytes()[1..].first(), Some(b'x' | b'X' | b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'e' | b'E' | b'i' | b'I')) => {
                let number = number::parse(&self.nums, token).map_err(|e| ReadError::new(e, start, self.at))?;
                number.ok_or(ReadError::new(ErrorKind::BadNumber, start, self.at))?
            }
            _ => return Err(ReadError::new(ErrorKind::Unsupported, start, self.at)),
        };
        self.node(value, self.literal, start).map(Some)
    }

    /// `#n=`, which labels the datum after it, or `#n#`, which is the datum labelled so, with
    /// the `n` of `digits` digits after the `#` at `start`.
    fn label(&mut self, start: usize, digits: usize) -> Result<Option<Syntax<'gc>>, ReadError> {
        let n = self.text[self.at..self.at + digits].parse::<u64>();
        let define = self.text.as_bytes()[self.at + digits] == b'=';
        self.at += digits + 1;
        let error = |kind| Err(ReadError::new(kind, start, self.at));
        let Ok(n) = n else { return error(ErrorKind::UnknownLabel) };
        if define {
            if self.labels.contains_key(&n) {
                return error(ErrorKind::DuplicateLabel);
            }
            self.labels.insert(n, None);
            self.push(Open::Label { start, end: self.at, n }, start)?;
            return Ok(None);
        }
        match self.labels.get(&n) {
            Some(&Some(node)) => Ok(Some(node)),
            Some(None) => error(ErrorKind::CyclicLabel),
            None => error(ErrorKind::UnknownLabel),
        }
    }

    /// A `#\` character at `start`: the character after it, or the name of one.
    fn character(&mut self, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let from = start + 2;
        let Some(first) = self.text[from..].chars().next() else { return Err(ReadError::new(ErrorKind::BadChar, start, from)) };
        self.at = from + first.len_utf8();
        if first.is_alphanumeric() {
            self.at = self.name_end(self.at);
        }
        let folded = (self.fold && self.at - from > first.len_utf8()).then(|| self.text[from..self.at].to_lowercase());
        let name = folded.as_deref().unwrap_or(&self.text[from..self.at]);
        let hex = |digits: &str| u32::from_str_radix(digits, 16).ok().and_then(char::from_u32);
        let c = match name {
            _ if name.len() == first.len_utf8() => Some(first),
            "alarm" => Some('\x07'),
            "backspace" => Some('\x08'),
            "delete" | "rubout" => Some('\x7f'),
            "escape" => Some('\x1b'),
            "newline" | "linefeed" => Some('\n'),
            "null" | "nul" => Some('\0'),
            "return" => Some('\r'),
            "space" => Some(' '),
            "tab" => Some('\t'),
            "vtab" => Some('\x0b'),
            "page" => Some('\x0c'),
            _ => name.strip_prefix(['x', 'u']).and_then(hex),
        };
        let c = c.ok_or(ReadError::new(ErrorKind::BadChar, start, self.at))?;
        self.node(Value::char(c), self.literal, start)
    }

    /// A string whose opening `"` is at `start`.
    fn string(&mut self, start: usize) -> Result<Syntax<'gc>, ReadError> {
        let out = self.quoted(start, '"')?;
        let s = string::from_str(&self.strings, &out).map_err(|e| ReadError::new(e, start, self.at))?;
        self.node(s.value(), self.literal, start)
    }

    /// The characters up to the `quote` that closes the one at `start`, with escapes as in
    /// strings, and in strings, line continuations.
    fn quoted(&mut self, start: usize, quote: char) -> Result<String, ReadError> {
        let text = self.text;
        let mut out = String::new();
        let mut chars = text[self.at..].char_indices().map(|(i, c)| (self.at + i, c)).peekable();
        let end = loop {
            let Some((at, c)) = chars.next() else { return Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)) };
            match c {
                _ if c == quote => break at + 1,
                '\\' => {
                    let bad = |to: usize| ReadError::new(ErrorKind::BadEscape, at, to);
                    let Some((next, e)) = chars.next() else { return Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)) };
                    match e {
                        'a' => out.push('\x07'),
                        'b' => out.push('\x08'),
                        't' => out.push('\t'),
                        'n' => out.push('\n'),
                        'r' => out.push('\r'),
                        'e' => out.push('\x1b'),
                        'f' => out.push('\x0c'),
                        'v' => out.push('\x0b'),
                        '0' => out.push('\0'),
                        '"' | '\\' | '|' => out.push(e),
                        'x' => {
                            let digits: String = std::iter::from_fn(|| chars.next_if(|&(_, c)| c.is_ascii_hexdigit()).map(|(_, c)| c)).collect();
                            let semicolon = chars.next_if(|&(_, c)| c == ';');
                            let to = semicolon.map_or(next + 1 + digits.len(), |(i, _)| i + 1);
                            let c = u32::from_str_radix(&digits, 16).ok().and_then(char::from_u32).filter(|_| semicolon.is_some());
                            out.push(c.ok_or(bad(to))?);
                        }
                        // A line ending, \n, \r\n or \r, with the spaces and tabs around it, is dropped.
                        ' ' | '\t' | '\n' | '\r' if quote == '"' => {
                            let mut e = e;
                            while e == ' ' || e == '\t' {
                                match chars.next() {
                                    Some((_, c)) => e = c,
                                    None => return Err(ReadError::new(ErrorKind::Unclosed, start, start + 1)),
                                }
                            }
                            match e {
                                '\r' => _ = chars.next_if(|&(_, c)| c == '\n'),
                                '\n' => {}
                                _ => return Err(bad(next + 1)),
                            }
                            while chars.next_if(|&(_, c)| c == ' ' || c == '\t').is_some() {}
                        }
                        _ => return Err(bad(next + e.len_utf8())),
                    }
                }
                c => out.push(c),
            }
        };
        self.at = end;
        Ok(out)
    }

    /// The identifier or number from `start` to the reader's position, or `None` for a dot.
    fn token(&mut self, start: usize) -> Result<Option<Syntax<'gc>>, ReadError> {
        let token = &self.text[start..self.at];
        if token == "." {
            self.dot(start)?;
            return Ok(None);
        }
        let parse = |this: &Self| number::parse(&this.nums, token).map_err(|e| ReadError::new(e, start, this.at));
        // A token that starts as a number must be one. One that starts as `+i` or an infinity
        // might be an identifier instead, as `+inf.0x` is.
        let numeric = matches!(token.as_bytes(), [b'0'..=b'9', ..] | [b'+' | b'-' | b'.', b'0'..=b'9', ..] | [b'+' | b'-', b'.', b'0'..=b'9', ..]);
        if numeric {
            let number = parse(self)?.ok_or(ReadError::new(ErrorKind::BadNumber, start, self.at))?;
            return self.node(number, self.literal, start).map(Some);
        }
        let after_sign = token.strip_prefix(['+', '-']).unwrap_or("");
        let special = |s: &str| after_sign.get(..s.len()).is_some_and(|t| t.eq_ignore_ascii_case(s));
        if (after_sign.eq_ignore_ascii_case("i") || special("inf.0") || special("nan.0"))
            && let Some(number) = parse(self)?
        {
            return self.node(number, self.literal, start).map(Some);
        }
        let folded = self.fold.then(|| token.to_lowercase());
        let name = folded.as_deref().unwrap_or(token);
        let symbol = self.symbols.intern_str(&self.strings, name).map_err(|e| ReadError::new(e, start, self.at))?;
        self.node(symbol.value(self.mc), self.identifier, start).map(Some)
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
    fn close(&mut self, start: usize, byte: u8) -> Result<Syntax<'gc>, ReadError> {
        match self.open.pop() {
            Some(Open::List { start: open, close, first, tail, shape }) if close == byte => {
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
