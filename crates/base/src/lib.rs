//! Ragwort's base language: Scheme, as R7RS and Racket write it, expanded to the compiler's core
//! forms and compiled.
//!
//! The expander knows `quote`, `if`, `lambda`, `define`, `set!`, `begin`, `let` (named too),
//! `letrec` and `letrec*` itself. `let*`, `and`, `or`, `when`, `unless`, `cond`, `case`, `do` and
//! `quasiquote` are macros, written in Rust for now, that expand hygienically by sets of scopes,
//! as `syntax-rules` and `syntax-case` macros will.
//!
//! Procedures such as `car` and `+` are globals the [`PRELUDE`] defines, in native ragwort. Code
//! can define its own globals of the same names, which then shadow the prelude's in what's loaded
//! after, but can't assign the prelude's.
//!
//! Each [`load`] is like a module body: its top-level definitions are all bound before any of its
//! expressions expand, so they can refer to each other in any order.

mod derived;
mod expand;
mod scope;
mod tree;

#[cfg(test)]
#[path = "tests/base.rs"]
mod tests;

use std::fmt;

use ragwort_compiler::{CompileError, compile};
use ragwort_native::Globals;
use ragwort_reader::{ReadError, Reader};
use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;

use crate::expand::Expander;

/// The prelude, in native ragwort.
pub const PRELUDE: &str = include_str!("prelude.rg");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandErrorKind {
    /// A form whose parts aren't the ones it takes, or a keyword used as a variable.
    BadSyntax,
    /// Two bindings of one identifier in one binding form or body.
    Duplicate,
    /// A definition where only expressions go.
    Definition,
    /// A body with no expression after its definitions.
    NoExpression,
    /// A `set!` of a global of the prelude's.
    Immutable,
    /// An identifier that two bindings could be, neither of whose scopes include the other's.
    Ambiguous,
    /// Syntax the expander doesn't support yet: defining macros, `syntax` and its kin, and
    /// unquoting in a vector.
    Unsupported,
    /// Expressions nested more than 256 deep, or data more than 1024.
    TooDeep,
    /// The arena couldn't make a value expanding needed.
    Arena(ragwort_types::Error),
}

impl From<OutOfMemory> for ExpandErrorKind {
    fn from(e: OutOfMemory) -> Self {
        Self::Arena(e.into())
    }
}

impl From<ragwort_types::Error> for ExpandErrorKind {
    fn from(e: ragwort_types::Error) -> Self {
        Self::Arena(e)
    }
}

/// What went wrong, and the bytes `start..end` of the text where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpandError {
    pub kind: ExpandErrorKind,
    pub start: u32,
    pub end: u32,
}

impl From<OutOfMemory> for ExpandError {
    fn from(e: OutOfMemory) -> Self {
        Self { kind: e.into(), start: 0, end: 0 }
    }
}

impl From<ragwort_types::Error> for ExpandError {
    fn from(e: ragwort_types::Error) -> Self {
        Self { kind: e.into(), start: 0, end: 0 }
    }
}

impl fmt::Display for ExpandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            ExpandErrorKind::BadSyntax => "bad syntax",
            ExpandErrorKind::Duplicate => "an identifier bound twice",
            ExpandErrorKind::Definition => "a definition where an expression goes",
            ExpandErrorKind::NoExpression => "a body with no expression",
            ExpandErrorKind::Immutable => "an assignment of a prelude global",
            ExpandErrorKind::Ambiguous => "an identifier with more than one binding",
            ExpandErrorKind::Unsupported => "syntax that isn't supported yet",
            ExpandErrorKind::TooDeep => "forms nested too deeply",
            ExpandErrorKind::Arena(_) => "running out of memory",
        };
        write!(f, "{what} at bytes {}..{}", self.start, self.end)
    }
}

impl std::error::Error for ExpandError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Read(ReadError),
    Expand(ExpandError),
    Compile(CompileError),
}

impl From<ReadError> for Error {
    fn from(e: ReadError) -> Self {
        Error::Read(e)
    }
}

impl From<ExpandError> for Error {
    fn from(e: ExpandError) -> Self {
        Error::Expand(e)
    }
}

impl From<CompileError> for Error {
    fn from(e: CompileError) -> Self {
        Error::Compile(e)
    }
}

/// Compiles the [`PRELUDE`], defining its globals in `prelude`. Returns a procedure of no
/// arguments for each of its forms, to run in order before any code [`load`]s.
pub fn prelude<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, prelude: Globals<'gc>) -> Result<Vec<Value<'gc>>, ragwort_native::Error> {
    let session = SyntaxSession::named(mc, "prelude", PRELUDE).map_err(|e| ragwort_native::LowerError::from(ragwort_types::Error::from(e)))?;
    ragwort_native::load(mc, symbols, prelude, &session)
}

/// Reads `session`'s text, interning names in `symbols`, and expands and compiles each form in
/// it. Its globals are named in `globals`, and those it doesn't define there are the prelude's,
/// in `prelude`. Returns a procedure of no arguments for each top-level form, to run in order.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    globals: Globals<'gc>,
    prelude: Globals<'gc>,
    session: &SyntaxSession,
) -> Result<Vec<Value<'gc>>, Error> {
    let mut expander = Expander::new(mc, symbols, globals, prelude)?;
    let mut tops = Vec::new();
    for node in Reader::new(mc, symbols, session)? {
        let form = expander.read(node?)?;
        expander.top(form, &mut tops)?;
    }
    let mut thunks = Vec::with_capacity(tops.len());
    for top in tops {
        let core = expander.lower(top)?;
        thunks.push(compile(mc, &core)?);
    }
    Ok(thunks)
}
