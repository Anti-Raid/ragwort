use std::fmt;

use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory};
use ragwort_types::syntax::{SyntaxLocation, SyntaxSource};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A `)` or `]` with no list open.
    UnexpectedClose,
    /// A list closed with the other bracket. It opened at byte `open`.
    Mismatched { open: u32 },
    /// The text ended inside the list, string, `|`-quoted identifier or block comment that
    /// opened here.
    Unclosed,
    /// A quote, quasiquote, unquote, `#;` datum comment or `#n=` label with no datum after it.
    EmptyQuote,
    /// A `.` that doesn't sit between a list's items and exactly one last datum.
    BadDot,
    /// Syntax the reader doesn't read: braces, and `#` forms other than those R7RS has.
    Unsupported,
    /// A token that starts as a number does but isn't one, such as `1x` or `1/0`.
    BadNumber,
    /// A `#\` character name that isn't one.
    BadChar,
    /// A backslash in a string or `|`-quoted identifier that doesn't start an escape.
    BadEscape,
    /// A bytevector item that isn't an exact integer from 0 to 255.
    BadByte,
    /// A `#n#` with no `#n=` before it in the same top-level datum.
    UnknownLabel,
    /// A `#n=` or `#n#` whose `n` is too big to be a label.
    BadLabel,
    /// A `#n#` inside the datum `#n=` labels, which would make it a cycle.
    CyclicLabel,
    /// A second `#n=` of one `n` in one top-level datum.
    DuplicateLabel,
    /// The text isn't UTF-8 from here.
    InvalidUtf8,
    /// The session belongs to another arena.
    ForeignSession,
    /// The arena couldn't make a value the reader needed: it ran out of memory, or a name was too
    /// long for a string.
    Arena(Error),
}

impl From<ragwort_parser_scheme::ErrorKind> for ErrorKind {
    fn from(e: ragwort_parser_scheme::ErrorKind) -> Self {
        use ragwort_parser_scheme::ErrorKind as Lex;
        match e {
            Lex::Unclosed => Self::Unclosed,
            Lex::Unsupported => Self::Unsupported,
            Lex::BadChar => Self::BadChar,
            Lex::BadEscape => Self::BadEscape,
            Lex::BadLabel => Self::BadLabel,
        }
    }
}

impl From<OutOfMemory> for ErrorKind {
    fn from(e: OutOfMemory) -> Self {
        Self::Arena(e.into())
    }
}

impl From<Error> for ErrorKind {
    fn from(e: Error) -> Self {
        Self::Arena(e)
    }
}

/// What went wrong, and the bytes `start..end` of the text where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReadError {
    pub kind: ErrorKind,
    pub start: u32,
    pub end: u32,
}

impl ReadError {
    pub(crate) fn new(kind: impl Into<ErrorKind>, start: usize, end: usize) -> Self {
        Self { kind: kind.into(), start: start as u32, end: end as u32 }
    }

    /// The line and column where the error starts.
    pub fn location<'gc>(&self, mc: &Mutation<'gc>, source: SyntaxSource<'gc>) -> Option<SyntaxLocation> {
        source.location(mc, self.start)
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ErrorKind::UnexpectedClose => "a closing bracket with no list open",
            ErrorKind::Mismatched { .. } => "a list closed with the wrong bracket",
            ErrorKind::Unclosed => "a list, string or comment that's never closed",
            ErrorKind::EmptyQuote => "a quote or datum comment with nothing after it",
            ErrorKind::BadDot => "a misplaced dot",
            ErrorKind::Unsupported => "syntax the reader doesn't support yet",
            ErrorKind::BadNumber => "a malformed number",
            ErrorKind::BadChar => "an unknown character name",
            ErrorKind::BadEscape => "an unknown escape",
            ErrorKind::BadByte => "a bytevector item that isn't a byte",
            ErrorKind::UnknownLabel => "a datum label used before it's defined",
            ErrorKind::BadLabel => "a datum label too big to be one",
            ErrorKind::CyclicLabel => "a datum label used inside the datum it labels",
            ErrorKind::DuplicateLabel => "a datum label defined twice",
            ErrorKind::InvalidUtf8 => "text that isn't UTF-8",
            ErrorKind::ForeignSession => "a session from another arena",
            ErrorKind::Arena(Error::OutOfMemory) => "running out of memory",
            ErrorKind::Arena(_) => "a value the arena couldn't make",
        })
    }
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at bytes {}..{}", self.kind, self.start, self.end)
    }
}

impl std::error::Error for ReadError {}
