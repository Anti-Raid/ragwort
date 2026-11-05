//! Native ragwort: the language the prelude is written in, read by the reader and lowered to the
//! compiler's core forms. It has no macros, just the core forms, each spelled with a `%`:
//!
//! ```text
//! (%quote datum)  'datum
//! (%if test then else)
//! (%let ((name init) ...) body ...)
//! (%letrec ((name init) ...) body ...)
//! (%set! name value)
//! (%define-global name value)
//! (%lambda (name ... . rest) body ...)   (%lambda rest body ...)
//! (%app f arg ...)
//! (%intrinsic name arg ...)
//! (%apply-intrinsic name arg ... list)
//! ```
//!
//! An `%apply-intrinsic`'s last argument is a list of more.
//!
//! A name is the innermost local of that name in scope, or else the global of that name. A
//! body's expressions run in order, and the last one's value is the body's. A list that doesn't
//! start with one of the forms is an error, as calls are `%app`s.

mod lower;

#[cfg(test)]
#[path = "tests/lower.rs"]
mod tests;

pub use lower::{LowerError, LowerErrorKind, Lowerer};

use ragwort_compiler::{CompileError, compile};
use ragwort_reader::{ReadError, Reader};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::{Box as Cell, BoxFields, Global, GlobalFields};

/// The globals native code names: a cell holding a list of [`Global`]s, each named by its
/// symbol. Keep it in a root to keep the globals from one load to the next.
#[derive(Clone, Copy, Debug)]
pub struct Globals<'gc>(Gc<'gc, Cell>);

impl<'gc> Globals<'gc> {
    pub fn new(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self(Cell::new(mc, Value::NIL)?))
    }

    pub fn of(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<Self> {
        v.downcast::<Cell>(mc).map(Self)
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// The global named `name`, if code has named it.
    pub fn get(self, mc: &Mutation<'gc>, name: Symbol<'gc>) -> Option<Gc<'gc, Global>> {
        self.iter(mc).find(|g| g.name(mc) == name.value(mc))
    }

    pub fn iter(self, mc: &Mutation<'gc>) -> impl Iterator<Item = Gc<'gc, Global>> {
        Pairs::new(mc).elements(self.0.value(mc)).filter_map(|g| g.downcast::<Global>(mc))
    }

    pub fn add(self, mc: &Mutation<'gc>, global: Gc<'gc, Global>) -> Result<(), OutOfMemory> {
        let list = Pairs::new(mc).cons(Value::object(mc, global), self.0.value(mc))?;
        self.0.set_value(mc, list.value(mc));
        Ok(())
    }
}

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

impl From<CompileError> for Error {
    fn from(e: CompileError) -> Self {
        Error::Compile(e)
    }
}

/// Reads `session`'s text, interning names in `symbols`, and compiles each form in it, naming
/// globals in `globals`. Returns a procedure of no arguments for each, to run in order.
pub fn load<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, globals: Globals<'gc>, session: &SyntaxSession) -> Result<Vec<Value<'gc>>, Error> {
    let mut lowerer = Lowerer::new(mc, symbols, globals).map_err(LowerError::from)?;
    let mut thunks = Vec::new();
    for node in Reader::new(mc, symbols, session)? {
        let core = lowerer.lower(node?)?;
        thunks.push(compile(mc, &core)?);
    }
    Ok(thunks)
}
