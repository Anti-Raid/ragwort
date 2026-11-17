//! Ragwort's base language: Scheme in the style of R7RS and Racket. This crate expands it to the
//! compiler's core forms and compiles it.
//!
//! The expander handles `quote`, `if`, `lambda`, `define`, `set!`, `begin`, `let`, `letrec` and
//! `letrec*` directly. Named `let`, `let*`, `and`, `or`, `when`, `unless`, `cond`, `case`, `do`,
//! `quasiquote`, `guard`, `match`, `struct-copy`, `with-continuation-mark`, `syntax-rules` and
//! `with-syntax` are built-in macros written in Rust. They expand hygienically with sets of scopes,
//! in the same way as the macros that a program defines.
//!
//! `struct` defines a struct type, as Racket's `struct` does: `(struct point (x y))` defines the
//! constructor `point`, the predicate `point?` and the accessors `point-x` and `point-y`. A
//! struct is printed with its fields. Two instances of one type are `equal?` when their fields
//! are `equal?`, unless the type is declared `#:identity-eq?`. A struct type can have subtypes.
//! `match` destructures a struct, and `struct-copy` copies one with some fields changed. The
//! `structs` module's documentation describes the form in full.
//!
//! A program defines macros with `define-syntax`, `let-syntax` and `letrec-syntax`, as in R6RS.
//! A transformer is a procedure that takes the syntax object of a macro use and returns syntax.
//! `syntax-case` destructures a syntax object and `syntax` builds one. `quote-syntax` returns its
//! argument as a syntax object, unchanged. The expander runs each transformer in a VM machine
//! during expansion. A macro exists only during the expansion of the module that defines it. Its
//! transformer can refer to the names that the module requires. It cannot refer to the module's
//! own variables, because they are not defined yet when the transformer runs.
//!
//! [`load`] loads code as a module. The files of a module form one body. All top-level
//! definitions are bound before any expression is expanded, so definitions can refer to each
//! other in any order and across files. An [`Expander`] expands a module's Scheme files into a
//! [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder). Other front ends can add to the
//! same builder, so a module can have files in more than one
//! language. A name that is not a local variable, a definition or an import is an error. `(require spec ...)` and `(provide spec ...)` are allowed only at the top level. They take the same
//! specs as `%require` and `%provide` in native ragwort.
//!
//! Procedures such as `car` and `+` are exports of the [`PRELUDE`] module, which is written in
//! native ragwort. Every Scheme module requires the prelude implicitly, and the prelude must have run before a Scheme module is expanded. A module can define a name that
//! the prelude also exports. The module's definition then shadows the prelude's. A module cannot assign a prelude export.

mod case;
mod convert;
mod derived;
mod expand;
mod formals;
mod matching;
mod scope;
mod structs;
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

/// The source text of the prelude module, written in native ragwort.
pub const PRELUDE: &str = include_str!("prelude.rg");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandErrorKind {
    /// A form does not have the parts that its syntax requires, or a syntactic keyword such as `if` is used as a variable.
    BadSyntax,
    /// One binding form or body binds the same identifier twice. Also reported when one form gives the same keyword or struct field twice.
    Duplicate,
    /// A definition appears where only an expression is allowed, or a `struct`, `require` or
    /// `provide` form is not at the top level.
    Definition,
    /// A body does not end with an expression.
    NoExpression,
    /// A `set!` assigns an import.
    Immutable,
    /// A name is not a local variable, a definition of the module or an import. Also reported for
    /// an import that its module has not defined yet.
    Unbound,
    /// The module both defines and requires a name, or requires the name as two different imports.
    Conflict,
    /// The resolver did not find a required module, or it returned a module that was not built by a
    /// [`ModuleBuilder`](ragwort_compiler::module::ModuleBuilder).
    Resolve,
    /// A `require` names something that the required module does not export.
    NotProvided,
    /// A `provide` names something that the module does not define.
    NotDefined,
    /// A struct name is called, used as a value or used in `struct-copy`, but its module provides
    /// the struct without its constructor. Such a name is valid only in a `match` pattern.
    NoConstructor,
    /// An identifier has two candidate bindings, and neither binding's scope set is a subset of the other's.
    Ambiguous,
    /// The expander does not support this syntax yet. Examples are `quasisyntax` and its unquotes, a
    /// `syntax-rules` form with a custom ellipsis, and an unquote inside a quasiquoted vector.
    Unsupported,
    /// A macro transformer failed: it raised an error, ran out of fuel, or yielded to the host. Also
    /// reported when a transformer expression does not evaluate to a procedure.
    Transformer,
    /// A macro transformer refers to a variable of the surrounding code. The variable does not
    /// exist when the transformer runs, because the code is still being expanded.
    Phase,
    /// An arena operation that expansion needed failed, for example because the arena ran out of memory.
    Arena(ragwort_types::Error),
}

impl From<OutOfMemory> for ExpandErrorKind {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

impl From<ragwort_types::Error> for ExpandErrorKind {
    fn from(error: ragwort_types::Error) -> Self {
        Self::Arena(error)
    }
}

/// An expansion error: its kind, and the byte range `start..end` of the source text where it occurred.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpandError {
    pub kind: ExpandErrorKind,
    pub start: u32,
    pub end: u32,
}

impl From<OutOfMemory> for ExpandError {
    fn from(error: OutOfMemory) -> Self {
        Self { kind: error.into(), start: 0, end: 0 }
    }
}

impl From<ragwort_types::Error> for ExpandError {
    fn from(error: ragwort_types::Error) -> Self {
        Self { kind: error.into(), start: 0, end: 0 }
    }
}

impl fmt::Display for ExpandErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
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
            ExpandErrorKind::NoConstructor => "a struct whose constructor its module doesn't provide",
            ExpandErrorKind::Ambiguous => "an identifier with more than one binding",
            ExpandErrorKind::Unsupported => "syntax that isn't supported yet",
            ExpandErrorKind::Transformer => "a macro's transformer that failed",
            ExpandErrorKind::Phase => "a macro's transformer that refers to a variable that doesn't exist yet",
            ExpandErrorKind::Arena(ragwort_types::Error::OutOfMemory) => "running out of memory",
            ExpandErrorKind::Arena(other) => ragwort_vm::Fault::from(*other).message(),
        })
    }
}

impl fmt::Display for ExpandError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at bytes {}..{}", self.kind, self.start, self.end)
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
    fn from(error: OutOfMemory) -> Self {
        Error::Expand(error.into())
    }
}

impl From<ReadError> for Error {
    fn from(error: ReadError) -> Self {
        Error::Read(error)
    }
}

impl From<ExpandError> for Error {
    fn from(error: ExpandError) -> Self {
        Error::Expand(error)
    }
}

impl From<CompileError> for Error {
    fn from(error: CompileError) -> Self {
        Error::Compile(error)
    }
}

/// The name of the [`PRELUDE`] module.
pub const PRELUDE_NAME: &str = "ragwort/prelude";

/// Builds the module named `name` from the Scheme source in `files`, and expands and compiles each
/// of its forms. The files form one body. Names are interned in `symbols`. The module implicitly
/// requires `prelude`, which must have run, then each module of `implicit` in order. An export of a later
/// module shadows the same name from an earlier one. `resolver` finds the modules that `require` forms name.
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
    let mut declared = Vec::new();
    for session in files {
        for node in Reader::new(mc, symbols, session)? {
            let first = u32::try_from(tops.len()).map_err(|_| OutOfMemory)?;
            expander.declare(node?, first, &mut declared, resolver)?;
            tops.append(&mut declared);
        }
    }
    expander.provide()?;
    expander.builder().start(mc)?;
    let mut thunks = Vec::with_capacity(tops.len());
    for (i, top) in tops.into_iter().enumerate() {
        let i = u32::try_from(i).map_err(|_| OutOfMemory)?;
        let form = expander.lower(top, i)?;
        thunks.push(expander.builder().compile(mc, i, form)?);
    }
    let module = expander.finish()?;
    Ok(Loaded { module, thunks })
}
