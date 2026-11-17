use std::fmt;

use ragwort_types::Error;
use ragwort_types::gc::{Mutation, OutOfMemory};
use ragwort_types::syntax::{SyntaxLocation, SyntaxSource};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A `)` or `]` appeared with no list open.
    UnexpectedClose,
    /// A list was closed with the wrong kind of bracket. The list opened at byte `open`.
    Mismatched { open: u32 },
    /// The text ended inside a list, a string, a `|`-quoted identifier or a block comment. The
    /// error's range is where that list, string, identifier or comment opened.
    Unclosed,
    /// An abbreviation such as a quote, a `#;` datum comment or a `#n=` label had no datum after it.
    EmptyQuote,
    /// A `.` was misplaced. A `.` is valid only in a list, after at least one item and before exactly one last datum.
    BadDot,
    /// The text used syntax that the reader does not support: a brace, or a `#` form that the lexer does not know.
    Unsupported,
    /// A token that must be a number is not a valid number, such as `1x` or `1/0`.
    BadNumber,
    /// A `#\` was followed by a name that is not a character name.
    BadChar,
    /// A backslash in a string or a `|`-quoted identifier did not start a valid escape.
    BadEscape,
    /// A bytevector item was not an exact integer from 0 to 255.
    BadByte,
    /// A `#n#` had no `#n=` before it in the same top-level datum.
    UnknownLabel,
    /// The number `n` of a `#n=` or `#n#` was too large for a label, which is a `u64`.
    BadLabel,
    /// A `#n#` appeared inside the datum that `#n=` labels, which would create a cycle.
    CyclicLabel,
    /// One top-level datum had two `#n=` labels with the same `n`.
    DuplicateLabel,
    /// The text is not valid UTF-8. The error's range starts at the first invalid byte.
    InvalidUtf8,
    /// The session belongs to another arena.
    ForeignSession,
    /// The arena could not create a value that the reader needed. Either it ran out of memory, or a name was too
    /// long for a string.
    Arena(Error),
}

impl From<ragwort_parser_scheme::ErrorKind> for ErrorKind {
    fn from(kind: ragwort_parser_scheme::ErrorKind) -> Self {
        use ragwort_parser_scheme::ErrorKind as Lex;
        match kind {
            Lex::Unclosed => Self::Unclosed,
            Lex::Unsupported => Self::Unsupported,
            Lex::BadChar => Self::BadChar,
            Lex::BadEscape => Self::BadEscape,
            Lex::BadLabel => Self::BadLabel,
        }
    }
}

impl From<OutOfMemory> for ErrorKind {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

impl From<Error> for ErrorKind {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

/// A read error: its kind, and the byte range `start..end` of the text where it occurred.
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

    /// Returns the line and column in `source` where the error starts.
    pub fn location<'gc>(&self, mc: &Mutation<'gc>, source: SyntaxSource<'gc>) -> Option<SyntaxLocation> {
        source.location(mc, self.start)
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at bytes {}..{}", self.kind, self.start, self.end)
    }
}

impl std::error::Error for ReadError {}
