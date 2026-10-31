use std::fmt;

use ragwort_types::Error;
use ragwort_types::gc::{Gc, OutOfMemory};
use ragwort_types::syntax::{SyntaxLocation, SyntaxSource};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A `)` or `]` with no list open.
    UnexpectedClose,
    /// A list closed with the other bracket. It opened at byte `open`.
    Mismatched { open: u32 },
    /// The text ended inside the list that opened here.
    Unclosed,
    /// A `'` with no datum after it.
    EmptyQuote,
    /// A `.` that doesn't sit between a list's items and exactly one last datum.
    BadDot,
    /// Syntax the reader doesn't read yet: numbers, strings, `#` forms, quasiquote and
    /// unquote, `|` and braces.
    Unsupported,
    /// The text isn't UTF-8 from here.
    InvalidUtf8,
    /// The session belongs to another arena.
    ForeignSession,
    /// Interning or allocating failed.
    Value(Error),
}

impl From<OutOfMemory> for ErrorKind {
    fn from(e: OutOfMemory) -> Self {
        Self::Value(e.into())
    }
}

impl From<Error> for ErrorKind {
    fn from(e: Error) -> Self {
        Self::Value(e)
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
    pub fn location<'gc>(&self, source: Gc<'gc, SyntaxSource<'gc>>) -> Option<SyntaxLocation> {
        SyntaxSource::location(source, self.start)
    }
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::UnexpectedClose => "a closing bracket with no list open",
            ErrorKind::Mismatched { .. } => "a list closed with the wrong bracket",
            ErrorKind::Unclosed => "a list that's never closed",
            ErrorKind::EmptyQuote => "a quote with nothing after it",
            ErrorKind::BadDot => "a misplaced dot",
            ErrorKind::Unsupported => "syntax the reader doesn't support yet",
            ErrorKind::InvalidUtf8 => "text that isn't UTF-8",
            ErrorKind::ForeignSession => "a session from another arena",
            ErrorKind::Value(Error::OutOfMemory) => "running out of memory",
            ErrorKind::Value(_) => "a failure to make a value",
        };
        write!(f, "{what} at bytes {}..{}", self.start, self.end)
    }
}

impl std::error::Error for ReadError {}
