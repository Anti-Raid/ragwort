//! Scheme text as tokens, with no heap of its own: brackets, abbreviations, datum comments and
//! labels, dots, and atoms with their escapes decoded, as R7RS writes them. `;` line comments,
//! nested `#| |#` block comments and the `#!fold-case` and `#!no-fold-case` directives are
//! skipped, and after `#!fold-case`, identifiers and character names come in lower case.
//! [`number`] reads number tokens, with any host of `ragwort-num`.
//!
//! What the tokens make, and whether brackets match, is for what reads them.

pub mod number;

#[cfg(test)]
#[path = "tests/lexer.rs"]
mod tests;

use std::borrow::Cow;
use std::fmt;

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

/// Whether `b` ends an identifier: whitespace, a bracket, a quote or `|`.
pub fn ends_name(b: u8) -> bool {
    ENDS_NAME[b as usize]
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bracket {
    /// `(` and `)`.
    Round,
    /// `[` and `]`.
    Square,
}

/// An abbreviation, which stands for a list of its form and the datum after it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prefix {
    /// `'`
    Quote,
    /// `` ` ``
    Quasiquote,
    /// `,`
    Unquote,
    /// `,@`
    UnquoteSplicing,
    /// `#'`
    Syntax,
    /// `` #` ``
    Quasisyntax,
    /// `#,`
    Unsyntax,
    /// `#,@`
    UnsyntaxSplicing,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'a> {
    Open(Bracket),
    /// `#(`, closed by `)`.
    OpenVector,
    /// `#u8(`, closed by `)`.
    OpenBytevector,
    Close(Bracket),
    Prefix(Prefix),
    /// `#;`, which drops the datum after it.
    DatumComment,
    /// `#n=`, which labels the datum after it.
    Label(u64),
    /// `#n#`, the datum labelled `n`.
    LabelRef(u64),
    /// A `.` on its own, before a list's tail.
    Dot,
    Boolean(bool),
    Char(char),
    String(Cow<'a, str>),
    Identifier(Cow<'a, str>),
    /// `#:name`, the keyword named `name`.
    Keyword(Cow<'a, str>),
    /// Text that starts as a number does, and must be one.
    Number(&'a str),
    /// Text that's a number if it reads as one, as `+i` and `-inf.0` do, or else the
    /// identifier `name`, as `+inf.0x` is.
    NumberOr { text: &'a str, name: Cow<'a, str> },
}

/// A token, and the bytes `start..end` of the text it's read from.
#[derive(Clone, PartialEq, Debug)]
pub struct Lexeme<'a> {
    pub token: Token<'a>,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// The text ended inside the string, `|`-quoted identifier or block comment that opened
    /// here.
    Unclosed,
    /// Syntax this doesn't read: braces, and `#` forms other than those R7RS has.
    Unsupported,
    /// A `#\` character name that isn't one.
    BadChar,
    /// A backslash in a string or `|`-quoted identifier that doesn't start an escape.
    BadEscape,
    /// A `#n=` or `#n#` whose `n` is too big to be a label.
    BadLabel,
}

/// What went wrong, and the bytes `start..end` of the text where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LexError {
    pub kind: ErrorKind,
    pub start: usize,
    pub end: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::Unclosed => "a string or comment that's never closed",
            ErrorKind::Unsupported => "syntax that isn't supported yet",
            ErrorKind::BadChar => "an unknown character name",
            ErrorKind::BadEscape => "an unknown escape",
            ErrorKind::BadLabel => "a datum label too big to be one",
        };
        write!(f, "{what} at bytes {}..{}", self.start, self.end)
    }
}

impl std::error::Error for LexError {}

/// The tokens of a text, one at a time.
pub struct Lexer<'a> {
    text: &'a str,
    at: usize,
    /// Whether `#!fold-case` is in effect.
    fold: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(text: &'a str) -> Self {
        Self { text, at: 0, fold: false }
    }

    /// Where the next token's search starts.
    pub fn position(&self) -> usize {
        self.at
    }

    /// Skips the rest of the text, so there are no more tokens.
    pub fn finish(&mut self) {
        self.at = self.text.len();
    }

    fn error(&self, kind: ErrorKind, start: usize, end: usize) -> LexError {
        LexError { kind, start, end }
    }

    /// The next token, or `None` once the text is read.
    #[inline]
    pub fn next_token(&mut self) -> Result<Option<Lexeme<'a>>, LexError> {
        loop {
            self.skip_space()?;
            let start = self.at;
            let Some(&byte) = self.text.as_bytes().get(start) else { return Ok(None) };
            self.at += 1;
            let token = match byte {
                b'(' => Token::Open(Bracket::Round),
                b'[' => Token::Open(Bracket::Square),
                b')' => Token::Close(Bracket::Round),
                b']' => Token::Close(Bracket::Square),
                b'\'' | b'`' | b',' => Token::Prefix(self.prefix(byte, [Prefix::Quote, Prefix::Quasiquote, Prefix::Unquote, Prefix::UnquoteSplicing])),
                b'"' => Token::String(self.quoted(start, '"')?),
                b'|' => Token::Identifier(self.quoted(start, '|')?),
                b'#' => match self.hash(start)? {
                    Some(token) => token,
                    None => continue,
                },
                b'{' | b'}' => return Err(self.error(ErrorKind::Unsupported, start, start + 1)),
                _ => {
                    self.at = self.name_end(start);
                    self.atom(start)
                }
            };
            return Ok(Some(Lexeme { token, start, end: self.at }));
        }
    }

    /// Where the name starting at `start` ends: at the next delimiter, or the end.
    #[inline]
    fn name_end(&self, start: usize) -> usize {
        let rest = &self.text.as_bytes()[start..];
        start + rest.iter().position(|&b| ENDS_NAME[b as usize]).unwrap_or(rest.len())
    }

    #[inline]
    fn skip_space(&mut self) -> Result<(), LexError> {
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
    fn block_comment(&mut self) -> Result<(), LexError> {
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
        Err(self.error(ErrorKind::Unclosed, start, start + 2))
    }

    /// The abbreviation `byte` starts: one of `'`, `` ` ``, `,` or `,@`, which stand for
    /// `which`'s four, in that order.
    fn prefix(&mut self, byte: u8, which: [Prefix; 4]) -> Prefix {
        match byte {
            b'\'' => which[0],
            b'`' => which[1],
            _ if self.text.as_bytes().get(self.at) == Some(&b'@') => {
                self.at += 1;
                which[3]
            }
            _ => which[2],
        }
    }

    /// What follows a `#` at `start`: a vector's or bytevector's opening, a datum comment, a
    /// label or a use of one, a character, a keyword, a boolean or a number with prefixes, or
    /// `None` for a directive.
    fn hash(&mut self, start: usize) -> Result<Option<Token<'a>>, LexError> {
        let rest = &self.text.as_bytes()[self.at..];
        let (token, len) = match *rest {
            [byte @ (b'\'' | b'`' | b','), ..] => {
                self.at += 1;
                return Ok(Some(Token::Prefix(self.prefix(byte, [Prefix::Syntax, Prefix::Quasisyntax, Prefix::Unsyntax, Prefix::UnsyntaxSplicing]))));
            }
            [b'(', ..] => (Token::OpenVector, 1),
            [b'u' | b'U', b'8', b'(', ..] => (Token::OpenBytevector, 3),
            [b';', ..] => (Token::DatumComment, 1),
            [b'\\', ..] => return self.character(start).map(Some),
            [b':', ..] => return self.keyword(start).map(Some),
            _ => {
                let digits = rest.iter().take_while(|b| b.is_ascii_digit()).count();
                if digits > 0 && matches!(rest.get(digits), Some(b'=' | b'#')) {
                    return self.label(start, digits).map(Some);
                }
                return self.hash_name(start);
            }
        };
        self.at += len;
        Ok(Some(token))
    }

    /// `#n=` or `#n#`, with `digits` digits after the `#` at `start`.
    fn label(&mut self, start: usize, digits: usize) -> Result<Token<'a>, LexError> {
        let n = self.text[self.at..self.at + digits].parse::<u64>();
        let define = self.text.as_bytes()[self.at + digits] == b'=';
        self.at += digits + 1;
        let n = n.map_err(|_| self.error(ErrorKind::BadLabel, start, self.at))?;
        Ok(if define { Token::Label(n) } else { Token::LabelRef(n) })
    }

    /// A boolean, a directive or a number after a `#` at `start`.
    fn hash_name(&mut self, start: usize) -> Result<Option<Token<'a>>, LexError> {
        self.at = self.name_end(self.at);
        let token = &self.text[start..self.at];
        let is = |names: &[&str]| names.iter().any(|name| token.eq_ignore_ascii_case(name));
        Ok(Some(match () {
            () if is(&["#t", "#true"]) => Token::Boolean(true),
            () if is(&["#f", "#false"]) => Token::Boolean(false),
            () if is(&["#!fold-case", "#!no-fold-case"]) => {
                self.fold = token.len() == "#!fold-case".len();
                return Ok(None);
            }
            _ if matches!(token.as_bytes()[1..].first(), Some(b'x' | b'X' | b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'e' | b'E' | b'i' | b'I')) => {
                Token::Number(token)
            }
            _ => return Err(self.error(ErrorKind::Unsupported, start, self.at)),
        }))
    }

    /// A `#:` keyword at `start`, its name read as an identifier's is, or between `|`s.
    fn keyword(&mut self, start: usize) -> Result<Token<'a>, LexError> {
        let from = start + 2;
        if self.text.as_bytes().get(from) == Some(&b'|') {
            self.at = from + 1;
            return Ok(Token::Keyword(self.quoted(from, '|')?));
        }
        self.at = self.name_end(from);
        if self.at == from {
            return Err(self.error(ErrorKind::Unsupported, start, self.at));
        }
        let name = &self.text[from..self.at];
        Ok(Token::Keyword(if self.fold { Cow::Owned(name.to_lowercase()) } else { Cow::Borrowed(name) }))
    }

    /// A `#\` character at `start`: the character after it, or the name of one.
    fn character(&mut self, start: usize) -> Result<Token<'a>, LexError> {
        let from = start + 2;
        let Some(first) = self.text[from..].chars().next() else { return Err(self.error(ErrorKind::BadChar, start, from)) };
        self.at = from + first.len_utf8();
        if first.is_alphanumeric() {
            self.at = self.name_end(self.at);
        }
        let folded = (self.fold && self.at - from > first.len_utf8()).then(|| self.text[from..self.at].to_lowercase());
        let name = folded.as_deref().unwrap_or(&self.text[from..self.at]);
        let c = match name {
            _ if name.len() == first.len_utf8() => Some(first),
            _ => named_char(name),
        };
        c.map(Token::Char).ok_or(self.error(ErrorKind::BadChar, start, self.at))
    }

    /// The characters up to the `quote` that closes the one at `start`, with escapes as in
    /// strings, and in strings, line continuations. Borrowed from the text if it has no escapes.
    fn quoted(&mut self, start: usize, quote: char) -> Result<Cow<'a, str>, LexError> {
        let text = self.text;
        let from = self.at;
        let plain = text.as_bytes()[from..].iter().position(|&b| b == quote as u8 || b == b'\\');
        if let Some(n) = plain
            && text.as_bytes()[from + n] == quote as u8
        {
            self.at = from + n + 1;
            return Ok(Cow::Borrowed(&text[from..from + n]));
        }
        let unclosed = || LexError { kind: ErrorKind::Unclosed, start, end: start + 1 };
        let mut out = String::new();
        let mut chars = text[from..].char_indices().map(|(i, c)| (from + i, c)).peekable();
        let end = loop {
            let Some((at, c)) = chars.next() else { return Err(unclosed()) };
            match c {
                _ if c == quote => break at + 1,
                '\\' => {
                    let bad = |to: usize| LexError { kind: ErrorKind::BadEscape, start: at, end: to };
                    let Some((next, e)) = chars.next() else { return Err(unclosed()) };
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
                                    None => return Err(unclosed()),
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
        Ok(Cow::Owned(out))
    }

    /// The dot, identifier or number from `start` to the lexer's position.
    #[inline]
    fn atom(&self, start: usize) -> Token<'a> {
        let token = &self.text[start..self.at];
        if token == "." {
            return Token::Dot;
        }
        // A token that starts as a number must be one. One that starts as `+i` or an infinity
        // might be an identifier instead, as `+inf.0x` is.
        if starts_numeric(token) {
            return Token::Number(token);
        }
        let name = if self.fold { Cow::Owned(token.to_lowercase()) } else { Cow::Borrowed(token) };
        if might_be_number(token) { Token::NumberOr { text: token, name } } else { Token::Identifier(name) }
    }
}

/// Whether `token` starts as only a number can.
#[inline]
pub fn starts_numeric(token: &str) -> bool {
    matches!(token.as_bytes(), [b'0'..=b'9', ..] | [b'+' | b'-' | b'.', b'0'..=b'9', ..] | [b'+' | b'-', b'.', b'0'..=b'9', ..])
}

/// Whether `token` starts as `+i`, `-i` or a signed infinity or NaN, and so might be a number.
#[inline]
pub fn might_be_number(token: &str) -> bool {
    let after_sign = token.strip_prefix(['+', '-']).unwrap_or("");
    let special = |s: &str| after_sign.get(..s.len()).is_some_and(|t| t.eq_ignore_ascii_case(s));
    after_sign.eq_ignore_ascii_case("i") || special("inf.0") || special("nan.0")
}

/// The character named `name` after `#\`, as a name or as `x` and hex digits.
pub fn named_char(name: &str) -> Option<char> {
    let hex = |digits: &str| u32::from_str_radix(digits, 16).ok().and_then(char::from_u32);
    match name {
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
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Lexeme<'a>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().transpose()
    }
}
