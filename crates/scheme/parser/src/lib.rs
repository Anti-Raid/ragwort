//! A lexer that turns Scheme text into tokens. It does not need an arena.
//!
//! The tokens are brackets, abbreviations, datum comments, datum labels, dots and atoms, in the
//! syntax of R7RS. Escapes in strings and `|`-quoted identifiers are decoded.
//!
//! - `;` line comments and nested `#| |#` block comments are skipped.
//! - The `#!fold-case` and `#!no-fold-case` directives are skipped. After `#!fold-case`,
//!   identifiers, keywords and character names are returned in lower case.
//! - [`number`] parses number tokens. It works with any `ragwort-num` host.
//!
//! The lexer does not build data from the tokens and does not check that brackets match. The
//! reader that consumes the tokens does both.

pub use ragwort_num::literal as number;

#[cfg(test)]
#[path = "tests/lexer.rs"]
mod tests;

use std::borrow::Cow;
use std::fmt;

fn is_space(byte: u8) -> bool {
    const SPACES: u64 = 1 << b' ' | 1 << b'\t' | 1 << b'\n' | 1 << b'\r' | 1 << 0x0b | 1 << 0x0c;
    byte < 64 && SPACES >> byte & 1 != 0
}

/// Lookup table of the bytes that end an identifier. See [`ends_name`].
const ENDS_NAME: [bool; 256] = byte_set(b" \t\n\r\x0b\x0c()[]{}\"';`,|");

/// Builds a lookup table that is true for each of `bytes`. A table is faster here than `matches!`. The loop is a `while` because `for` is not allowed in a `const fn`.
const fn byte_set(bytes: &[u8]) -> [bool; 256] {
    let mut set = [false; 256];
    let mut i = 0;
    while i < bytes.len() {
        set[bytes[i] as usize] = true;
        i += 1;
    }
    set
}

/// Returns whether `byte` ends an identifier. The bytes that do are whitespace, brackets, braces, `"`, `'`, `;`, a backquote, `,` and `|`.
pub fn ends_name(byte: u8) -> bool {
    ENDS_NAME[byte as usize]
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bracket {
    /// `(` and `)`.
    Round,
    /// `[` and `]`.
    Square,
}

/// An abbreviation prefix. The prefix and the datum after it stand for a two-element list: `'x` stands for `(quote x)`.
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
    /// `#;`, which comments out the datum after it.
    DatumComment,
    /// `#n=`, which labels the datum after it.
    Label(u64),
    /// `#n#`, a reference to the datum labelled `n`.
    LabelRef(u64),
    /// A `.` on its own, before a list's tail.
    Dot,
    Boolean(bool),
    /// `#nil`, which denotes the absence of a value.
    Nil,
    /// `#none`, a value that is present and means "none".
    NoneValue,
    Char(char),
    String(Cow<'a, str>),
    Identifier(Cow<'a, str>),
    /// `#:name`, the keyword named `name`.
    Keyword(Cow<'a, str>),
    /// A token that must be a number. It starts as only a number can (see [`starts_numeric`]), or with a radix or exactness prefix such as `#x`. The reader reports an error if the text is not a valid number.
    Number(&'a str),
    /// A token that is a number if `text` parses as one, as `+i` and `-inf.0` do. Otherwise it is
    /// the identifier `name`, as `+inf.0x` is.
    NumberOr { text: &'a str, name: Cow<'a, str> },
}

/// A token and the byte range `start..end` of the text that it was read from.
#[derive(Clone, PartialEq, Debug)]
pub struct Lexeme<'a> {
    pub token: Token<'a>,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// The text ended inside a string, a `|`-quoted identifier or a block comment. The error's
    /// range is where that string, identifier or comment opened.
    Unclosed,
    /// The text used syntax that the lexer does not support: a brace, or a `#` form that the lexer does not know.
    Unsupported,
    /// A `#\` was followed by a name that is not a character name.
    BadChar,
    /// A backslash in a string or a `|`-quoted identifier did not start a valid escape.
    BadEscape,
    /// The number `n` of a `#n=` or `#n#` was too large for a label, which is a `u64`.
    BadLabel,
}

/// A lexical error: its kind, and the byte range `start..end` of the text where it occurred.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LexError {
    pub kind: ErrorKind,
    pub start: usize,
    pub end: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::Unclosed => "unclosed string or comment",
            ErrorKind::Unsupported => "unsupported syntax",
            ErrorKind::BadChar => "unknown character name",
            ErrorKind::BadEscape => "unknown escape sequence",
            ErrorKind::BadLabel => "datum label out of range",
        };
        write!(formatter, "{what} at bytes {}..{}", self.start, self.end)
    }
}

impl std::error::Error for LexError {}

/// Produces the tokens of a text one at a time. It is also an iterator over the tokens.
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

    /// Returns the byte offset at which the search for the next token starts.
    pub fn position(&self) -> usize {
        self.at
    }

    /// Skips the rest of the text, so the lexer returns no more tokens.
    pub fn finish(&mut self) {
        self.at = self.text.len();
    }

    fn error(&self, kind: ErrorKind, start: usize, end: usize) -> LexError {
        LexError { kind, start, end }
    }

    /// Returns the next token, or `None` at the end of the text.
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

    /// Returns the offset where the name that starts at `start` ends. That is the next delimiter, or the end of the text.
    #[inline]
    fn name_end(&self, start: usize) -> usize {
        let rest = &self.text.as_bytes()[start..];
        start + rest.iter().position(|&byte| ENDS_NAME[byte as usize]).unwrap_or(rest.len())
    }

    #[inline]
    fn skip_space(&mut self) -> Result<(), LexError> {
        let bytes = self.text.as_bytes();
        while let Some(&byte) = bytes.get(self.at) {
            if is_space(byte) {
                self.at += 1;
            } else if byte == b';' {
                self.at = bytes[self.at..].iter().position(|&byte| byte == b'\n').map_or(bytes.len(), |offset| self.at + offset + 1);
            } else if byte == b'#' && bytes.get(self.at + 1) == Some(&b'|') {
                self.block_comment()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    /// Skips a `#| |#` block comment, including the block comments nested in it.
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

    /// Returns the abbreviation that `byte` starts. `which` holds the prefixes for `'`, `` ` ``, `,` and `,@`,
    /// in that order. For `,@`, the `@` is consumed too.
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

    /// Lexes the token that begins with the `#` at `start`. The token is an abbreviation such as `#'`, the opening of a vector or
    /// bytevector, a datum comment, a datum label or a reference to one, a character, a keyword, a boolean, `#nil`, `#none`, or a
    /// number with prefixes. Returns `None` for a directive, which produces no token.
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
                let digits = rest.iter().take_while(|byte| byte.is_ascii_digit()).count();
                if digits > 0 && matches!(rest.get(digits), Some(b'=' | b'#')) {
                    return self.label(start, digits).map(Some);
                }
                return self.hash_name(start);
            }
        };
        self.at += len;
        Ok(Some(token))
    }

    /// Lexes a `#n=` or `#n#`. Its `#` is at `start`, and `n` has `digits` digits.
    fn label(&mut self, start: usize, digits: usize) -> Result<Token<'a>, LexError> {
        let number = self.text[self.at..self.at + digits].parse::<u64>();
        let define = self.text.as_bytes()[self.at + digits] == b'=';
        self.at += digits + 1;
        let number = number.map_err(|_| self.error(ErrorKind::BadLabel, start, self.at))?;
        let token = if define {
            Token::Label(number)
        } else {
            Token::LabelRef(number)
        };
        Ok(token)
    }

    /// Lexes a boolean, `#nil`, `#none`, a directive or a prefixed number that begins with the `#` at `start`. Returns `None` for a directive.
    fn hash_name(&mut self, start: usize) -> Result<Option<Token<'a>>, LexError> {
        self.at = self.name_end(self.at);
        let token = &self.text[start..self.at];
        fn is(token: &str, names: &[&str]) -> bool {
            names.iter().any(|name| token.eq_ignore_ascii_case(name))
        }
        if is(token, &["#!fold-case", "#!no-fold-case"]) {
            self.fold = token.len() == "#!fold-case".len();
            return Ok(None);
        }
        let token = if is(token, &["#t", "#true"]) {
            Token::Boolean(true)
        } else if is(token, &["#f", "#false"]) {
            Token::Boolean(false)
        } else if is(token, &["#nil"]) {
            Token::Nil
        } else if is(token, &["#none"]) {
            Token::NoneValue
        } else if matches!(token.as_bytes()[1..].first(), Some(b'x' | b'X' | b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'e' | b'E' | b'i' | b'I')) {
            Token::Number(token)
        } else {
            return Err(self.error(ErrorKind::Unsupported, start, self.at));
        };
        Ok(Some(token))
    }

    /// Lexes the `#:` keyword at `start`. The keyword's name is read as an identifier is, or it is quoted between `|`s.
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
        let folded = if self.fold {
            Cow::Owned(name.to_lowercase())
        } else {
            Cow::Borrowed(name)
        };
        Ok(Token::Keyword(folded))
    }

    /// Lexes the `#\` character at `start`. The text after `#\` is a single character or a character name.
    fn character(&mut self, start: usize) -> Result<Token<'a>, LexError> {
        let from = start + 2;
        let Some(first) = self.text[from..].chars().next() else { return Err(self.error(ErrorKind::BadChar, start, from)) };
        self.at = from + first.len_utf8();
        if first.is_alphanumeric() {
            self.at = self.name_end(self.at);
        }
        let folded = if self.fold && self.at - from > first.len_utf8() {
            Some(self.text[from..self.at].to_lowercase())
        } else {
            None
        };
        let name = folded.as_deref().unwrap_or(&self.text[from..self.at]);
        let character = match name {
            _ if name.len() == first.len_utf8() => Some(first),
            _ => named_char(name),
        };
        character.map(Token::Char).ok_or(self.error(ErrorKind::BadChar, start, self.at))
    }

    /// Returns the characters between the opening `quote` at `start` and the closing `quote`, with escapes decoded.
    /// A string also allows line continuations. The result borrows from the text if the text has no escapes.
    fn quoted(&mut self, start: usize, quote: char) -> Result<Cow<'a, str>, LexError> {
        let text = self.text;
        let from = self.at;
        let plain = text.as_bytes()[from..].iter().position(|&byte| byte == quote as u8 || byte == b'\\');
        if let Some(length) = plain
            && text.as_bytes()[from + length] == quote as u8
        {
            self.at = from + length + 1;
            return Ok(Cow::Borrowed(&text[from..from + length]));
        }
        let unclosed = LexError { kind: ErrorKind::Unclosed, start, end: start + 1 };
        let mut out = String::new();
        let mut chars = text[from..].char_indices().map(|(offset, character)| (from + offset, character)).peekable();
        let end = loop {
            let Some((at, character)) = chars.next() else { return Err(unclosed) };
            match character {
                _ if character == quote => break at + 1,
                '\\' => {
                    let Some((next, escape)) = chars.next() else { return Err(unclosed) };
                    match escape {
                        'a' => out.push('\x07'),
                        'b' => out.push('\x08'),
                        't' => out.push('\t'),
                        'n' => out.push('\n'),
                        'r' => out.push('\r'),
                        'e' => out.push('\x1b'),
                        'f' => out.push('\x0c'),
                        'v' => out.push('\x0b'),
                        '0' => out.push('\0'),
                        '"' | '\\' | '|' => out.push(escape),
                        'x' => {
                            let digits: String = std::iter::from_fn(|| chars.next_if(|&(_, character)| character.is_ascii_hexdigit()).map(|(_, character)| character)).collect();
                            let semicolon = chars.next_if(|&(_, character)| character == ';');
                            let to = semicolon.map_or(next + 1 + digits.len(), |(position, _)| position + 1);
                            let character = u32::from_str_radix(&digits, 16).ok().and_then(char::from_u32).filter(|_| semicolon.is_some());
                            out.push(character.ok_or(self.error(ErrorKind::BadEscape, at, to))?);
                        }
                        // A line continuation is dropped: the backslash, the spaces and tabs after it, one line ending (\n, \r\n or \r), and the spaces and tabs after that.
                        ' ' | '\t' | '\n' | '\r' if quote == '"' => {
                            let mut escape = escape;
                            while escape == ' ' || escape == '\t' {
                                match chars.next() {
                                    Some((_, character)) => escape = character,
                                    None => return Err(unclosed),
                                }
                            }
                            match escape {
                                '\r' => _ = chars.next_if(|&(_, character)| character == '\n'),
                                '\n' => {}
                                _ => return Err(self.error(ErrorKind::BadEscape, at, next + 1)),
                            }
                            while chars.next_if(|&(_, character)| character == ' ' || character == '\t').is_some() {}
                        }
                        _ => return Err(self.error(ErrorKind::BadEscape, at, next + escape.len_utf8())),
                    }
                }
                character => out.push(character),
            }
        };
        self.at = end;
        Ok(Cow::Owned(out))
    }

    /// Returns the token for the text from `start` to the lexer's position: a dot, an identifier or a number.
    #[inline]
    fn atom(&self, start: usize) -> Token<'a> {
        let token = &self.text[start..self.at];
        if token == "." {
            return Token::Dot;
        }
        // A token that starts as only a number can must be a number. A token that is `+i` or `-i`, or that starts
        // with a signed infinity or NaN, might be an identifier instead, as `+inf.0x` is.
        if starts_numeric(token) {
            return Token::Number(token);
        }
        let name = if self.fold {
            Cow::Owned(token.to_lowercase())
        } else {
            Cow::Borrowed(token)
        };
        if might_be_number(token) {
            Token::NumberOr { text: token, name }
        } else {
            Token::Identifier(name)
        }
    }
}

/// Returns whether `token` starts as only a number can: with a digit, optionally preceded by a sign, a `.`, or a sign and a `.`.
#[inline]
pub fn starts_numeric(token: &str) -> bool {
    matches!(token.as_bytes(), [b'0'..=b'9', ..] | [b'+' | b'-' | b'.', b'0'..=b'9', ..] | [b'+' | b'-', b'.', b'0'..=b'9', ..])
}

/// Returns whether `token` is `+i` or `-i`, or starts with a signed `inf.0` or `nan.0`. Such a token might be a number or an identifier.
#[inline]
pub fn might_be_number(token: &str) -> bool {
    let after_sign = token.strip_prefix(['+', '-']).unwrap_or("");
    fn special(after_sign: &str, name: &str) -> bool {
        after_sign.get(..name.len()).is_some_and(|prefix| prefix.eq_ignore_ascii_case(name))
    }
    after_sign.eq_ignore_ascii_case("i") || special(after_sign, "inf.0") || special(after_sign, "nan.0")
}

/// Returns the character that `name` denotes after `#\`. `name` is a character name such as `space`, or `x` or `u` followed by hex digits.
pub fn named_char(name: &str) -> Option<char> {
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
        _ => name.strip_prefix(['x', 'u']).and_then(|digits| u32::from_str_radix(digits, 16).ok().and_then(char::from_u32)),
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Lexeme<'a>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().transpose()
    }
}
