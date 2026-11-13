//! Native ragwort: the language the prelude is written in, read by the reader and lowered to the
//! compiler's core forms. It has no macros, just the core forms, each spelled with a `%`:
//!
//! ```text
//! (%quote datum)  'datum
//! (%if test then else)
//! (%let ((name init) ...) body ...)
//! (%let* ((name init) ...) body ...)
//! (%letrec ((name init) ...) body ...)
//! (%set! name value)
//! (%define name value)
//! (%struct name (field ...) option ...)   (%struct name super (field ...) option ...)
//! (%require spec ...)
//! (%provide spec ...)
//! (%lambda (name ... . rest) body ...)   (%lambda rest body ...)
//! (%app f arg ...)
//! (%intrinsic name arg ...)
//! (%apply-intrinsic name arg ... list)
//! (%call-host name arg ...)
//! ```
//!
//! An `%apply-intrinsic`'s last argument is a list of more. A `%call-host` calls one of the
//! [`HostDef`]s the code was loaded with, which only native ragwort can: other code calls the
//! native procedures that wrap them, which pass on what they need, such as a mark.
//!
//! An `%intrinsic` can't name an [internal intrinsic](ragwort_vm::Intrinsic::is_internal):
//! `(%intrinsic struct-ref s type 0)` is an error, as a struct's fields are read with the
//! accessors `%struct` defines. Only a [`Lowerer`] made for code the embedder wrote itself
//! takes them.
//!
//! Code is loaded as a module, whose files' top-level forms are one body. A `%define`, which
//! only goes at the top level, defines one of its variables, which code anywhere in the module
//! can refer to, as it can to what a `%require` imports, and a `%provide` exports some. A require
//! spec is a module's name, an identifier or a string, or `(only-in spec name ...)`,
//! `(except-in spec name ...)`, `(prefix-in prefix spec)` or `(rename-in spec (old new) ...)`. A
//! provide spec is a name, `(rename-out (name external) ...)`, `(all-defined-out)`, or
//! `(struct-out name)`, which exports everything the struct form for `name` defines.
//! `(struct-out name #:omit-constructor)` leaves out the form's constructors: see Scheme's
//! `struct` for what the name is then.
//!
//! `%struct` defines a struct type the way Scheme's `struct` does, with the same syntax for
//! fields and options. It only goes at the top level. `(%struct point (x y))` defines
//! `struct:point`, `point`, `point?`, `point-x` and `point-y`, which code in any of the module's
//! languages can use.
//!
//! A name is the innermost local of that name in scope, or else the module's variable of that
//! name, or else its import of it. A body's expressions run in order, and the last one's value is
//! the body's. A list that doesn't start with one of the forms is an error, as calls are
//! `%app`s.

mod lower;

#[cfg(test)]
#[path = "tests/lower.rs"]
mod tests;

pub use lower::{LowerError, LowerErrorKind, Lowerer};

use ragwort_compiler::CompileError;
use ragwort_compiler::module::{BuildError, Description, Loaded, Locals, Resolver};
use ragwort_reader_scheme::{ReadError, Reader};
use ragwort_types::gc::Mutation;
use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::HostDef;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Read(ReadError),
    Lower(LowerError),
    Compile(CompileError),
}

impl From<ReadError> for Error {
    fn from(e: ReadError) -> Self {
        Error::Read(e)
    }
}

impl From<LowerError> for Error {
    fn from(e: LowerError) -> Self {
        Error::Lower(e)
    }
}

impl From<BuildError<'_>> for Error {
    fn from(e: BuildError<'_>) -> Self {
        match e {
            BuildError::Declare(e, span) => Error::Lower(LowerError::declared(e, span)),
            BuildError::Compile(e) => e.into(),
        }
    }
}

impl From<CompileError> for Error {
    fn from(e: CompileError) -> Self {
        match LowerError::located(e) {
            Some(lower) => Error::Lower(lower),
            None => Error::Compile(e),
        }
    }
}

/// Builds the module named `name` from the native ragwort in `files`, one body across them all,
/// interning names in `symbols`. Its code can call the host functions in `hosts`, and it requires
/// the modules `resolver` finds.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    name: &str,
    hosts: &'static [HostDef],
    files: &[&SyntaxSession],
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Error> {
    let name = symbols.intern_str(&Strings::new(mc), name).map_err(LowerError::from)?;
    let mut lowerer = Lowerer::new(mc, symbols, hosts, false).map_err(LowerError::from)?;
    let mut locals = Locals::default();
    let mut items = Vec::new();
    for session in files {
        for node in Reader::new(mc, symbols, session)? {
            items.push(lowerer.item(&mut locals, node?)?);
        }
    }
    Ok(Description { name: name.value(mc), hosts, locals, items }.build(mc, resolver)?)
}
