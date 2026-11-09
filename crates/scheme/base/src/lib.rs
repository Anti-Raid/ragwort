//! Ragwort's base language: Scheme, as R7RS and Racket write it, expanded to the compiler's core
//! forms and compiled.
//!
//! The expander knows `quote`, `if`, `lambda`, `define`, `set!`, `begin`, `let` (named too),
//! `letrec` and `letrec*` itself. `let*`, `and`, `or`, `when`, `unless`, `cond`, `case`, `do`,
//! `quasiquote`, `guard`, `syntax-rules` and `with-syntax` are macros written in Rust, which
//! expand hygienically by sets of scopes, as the code's own do.
//!
//! The code defines macros with `define-syntax`, `let-syntax` and `letrec-syntax`, as R6RS has
//! them: a transformer is a procedure of the syntax of a use, which `syntax-case` takes apart
//! and `syntax` makes, and the expander runs it in a machine as it goes; `quote-syntax` is the
//! syntax of what it's given, as it is. Macros last as long as
//! the module that defines them, and their transformers see what it requires, but not its own
//! variables, which haven't been defined yet.
//!
//! Code is [`load`]ed as a module, whose files are one body: its top-level definitions are all
//! bound before any of its expressions expand, so they can refer to each other in any order, from
//! any of its files. An [`Expander`] expands a module's Scheme files into a
//! [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder) that
//! other front ends can build the module with too, so a module can have files in more than one
//! language. A name that's no local, definition or import is an error. `(require spec ...)` and `(provide spec ...)` go at the top level and take the specs
//! native ragwort's `%require` and `%provide` do.
//!
//! Procedures such as `car` and `+` are what the [`PRELUDE`] module, in native ragwort, exports,
//! which every Scheme module requires implicitly, and which must have run before one's expanded. A module can define its own of the same names, which
//! shadow the prelude's, but can't assign the prelude's.

mod case;
mod convert;
mod derived;
mod expand;
mod formals;
mod matching;
mod scope;
mod transformer;
mod tree;

#[cfg(test)]
#[path = "tests/base.rs"]
mod tests;

use std::fmt;

use ragwort_compiler::CompileError;
use ragwort_compiler::module::{Loaded, Resolver};
use ragwort_reader_scheme::{ReadError, Reader};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::Module;

pub use crate::expand::{Expander, Top};

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
    /// A `set!` of an import.
    Immutable,
    /// A name that's no local, definition of the module's or import, or an import of a module
    /// that hasn't defined it yet.
    Unbound,
    /// A name the module both defines and requires, or requires as two different things.
    Conflict,
    /// A module the resolver doesn't have, or one it gave that no
    /// [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder) built.
    Resolve,
    /// A require of a name the module doesn't export.
    NotProvided,
    /// A provide of a name the module doesn't define.
    NotDefined,
    /// An identifier that two bindings could be, neither of whose scopes include the other's.
    Ambiguous,
    /// Syntax the expander doesn't support yet: `quasisyntax` and its unquotes, a `syntax-rules`
    /// with an ellipsis of its own, and unquoting in a vector.
    Unsupported,
    /// A macro's transformer that raised, ran out of fuel, isn't a procedure, or made what isn't
    /// syntax.
    Transformer,
    /// A macro's transformer that refers to a variable of the code around it, which doesn't
    /// exist yet when the transformer runs, as the code is still being expanded.
    Phase,
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
            ExpandErrorKind::Immutable => "an assignment of an import",
            ExpandErrorKind::Unbound => "a name nothing defines",
            ExpandErrorKind::Conflict => "a name both defined and required",
            ExpandErrorKind::Resolve => "a module that can't be found",
            ExpandErrorKind::NotProvided => "a name the module doesn't provide",
            ExpandErrorKind::NotDefined => "a provide of a name that isn't defined",
            ExpandErrorKind::Ambiguous => "an identifier with more than one binding",
            ExpandErrorKind::Unsupported => "syntax that isn't supported yet",
            ExpandErrorKind::Transformer => "a macro's transformer that failed",
            ExpandErrorKind::Phase => "a macro's transformer that refers to a variable that doesn't exist yet",
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

impl From<OutOfMemory> for Error {
    fn from(e: OutOfMemory) -> Self {
        Error::Expand(e.into())
    }
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

/// The name of the [`PRELUDE`]'s module.
pub const PRELUDE_NAME: &str = "ragwort/prelude";

/// Builds the module named `name` from the Scheme in `files`, one body across them all,
/// interning names in `symbols`, and expands and compiles each of its forms. It requires the
/// `prelude` module, which has run, implicitly, then each of `implicit`, whose exports shadow what
/// those before it export, and the modules `resolver` finds as it says.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    prelude: Gc<'gc, Module>,
    name: &str,
    files: &[&SyntaxSession],
    implicit: &[Gc<'gc, Module>],
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Error> {
    let mut expander = Expander::new(mc, symbols, prelude, name, &[], implicit)?;
    let mut tops = Vec::new();
    for session in files {
        for node in Reader::new(mc, symbols, session)? {
            let first = u32::try_from(tops.len()).map_err(|_| OutOfMemory)?;
            expander.declare(node?, first, &mut tops, resolver)?;
        }
    }
    expander.provide()?;
    expander.builder().start(mc)?;
    let mut thunks = Vec::with_capacity(tops.len());
    for (i, top) in tops.into_iter().enumerate() {
        let core = expander.lower(top, u32::try_from(i).map_err(|_| OutOfMemory)?)?;
        thunks.push(expander.builder().compile(mc, &core)?);
    }
    let module = expander.finish()?;
    Ok(Loaded { module, thunks })
}
