//! Native ragwort is the language that the prelude is written in. The Scheme reader reads it, and
//! this crate lowers it to the compiler's core forms. Its forms are the core forms of the shared expander. See [`ragwort_expander::forms`]. The name of each form starts with `%`:
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
//! (%loop name body ...)
//! (%break name)   (%continue name)
//! (%begin form ...)
//! (%define-syntax name transformer)
//! (%syntax-rules (literal ...) (pattern template) ...)
//! (%syntax-case input (literal ...) clause ...)
//! (%syntax template)  #'template
//! ```
//!
//! `'datum` is short for `(quote datum)`, which is the same form as `(%quote datum)`. `#'template` is short for `(syntax template)`, which is the same form as `(%syntax template)`.
//!
//! # Macros
//!
//! `%define-syntax` defines a macro. It is allowed only at the top level. The transformer is a procedure that takes the syntax
//! object of a macro use and returns the syntax to lower in its place. `%syntax-rules` creates such a procedure from patterns and
//! templates, as Scheme's `syntax-rules` does. A transformer can also be a `%lambda` that takes the use apart with `%syntax-case`
//! and builds its result with `%syntax`.
//!
//! ```text
//! (%define-syntax while
//!   (%syntax-rules ()
//!     ((_ test body ...) (%loop again (%if test (%begin body ...) (%break again))))))
//! ```
//!
//! Macros are hygienic. A variable or a loop name that a macro's output binds is apart from the names of the macro's use. A name in a macro's
//! output that the output does not bind refers to the binding of the macro's own module.
//!
//! - A transformer runs while the module is being lowered. It can call what the module requires. It cannot refer to the module's own variables.
//! - `%begin` at the top level stands for the forms inside it, so a macro can define several things. In an expression, `%begin` evaluates its expressions in order.
//! - A `%define` whose name comes from the macro's use defines a variable of the module. A `%define` whose name the macro itself introduces defines a variable that only that use of the macro refers to.
//! - A macro's output can define further macros. A macro whose name the output introduces is known only to that output, like a variable that it defines.
//! - `(%provide name)` exports a macro as it exports a variable. A module of any language can require the macro, because the macro's output is made of core forms. The parts of a use are then expressions of the using module's language.
//! - The output of a macro is checked like code of the module that uses the macro. A `%call-host` in it must name a host function of that module, and an `%intrinsic` in it can name an internal intrinsic only if that module can.
//!
//! The last argument of `%apply-intrinsic` is a list of further arguments:
//! `(%apply-intrinsic + 1 2 '(3 4))` computes the same as `(%intrinsic + 1 2 3 4)`.
//!
//! `%loop` evaluates its body again and again, and has the value `#<void>` when it ends.
//! `(%break name)` ends the loop of that name, and `(%continue name)` starts its next round.
//! Both can be any statement of the loop body, also inside an `%if`, a `%let` or an inner loop:
//!
//! ```text
//! (%let ((i 0))
//!   (%loop count
//!     (%set! i (%intrinsic + i 1))
//!     (%if (%intrinsic eq? i 3) (%continue count) #f)
//!     (%if (%intrinsic < 5 i) (%break count) #f)
//!     (%app show i)))
//! ```
//!
//! They cannot be where a value is needed, such as an argument of a call, and not in a `%lambda`
//! inside the loop. A loop name is apart from the variables: a loop and a variable can have the same name.
//!
//! `%call-host` calls one of the [`HostDef`]s that the code was loaded with. Only native ragwort
//! can call a host function directly. Other code calls a native procedure that wraps the host call.
//! The wrapper passes the host function the values that it needs, such as the value of a continuation mark.
//!
//! `%intrinsic` cannot name an [internal intrinsic](ragwort_vm::Intrinsic::is_internal).
//! `(%intrinsic struct-ref s type 0)` is an error, because code reads a struct's fields with the
//! accessors that `%struct` defines. A [`Lowerer`] accepts internal intrinsics only if it was created
//! with `internals` set, which is meant for code that the embedder wrote itself.
//!
//! Code is loaded as a module. The top-level forms of all the module's files make up one body.
//! `%define`, `%define-syntax`, `%struct`, `%require` and `%provide` are allowed only at the top level.
//!
//! - `%define` defines a module variable. Code anywhere in the module can refer to the variable.
//! - `%require` imports bindings from other modules. Code anywhere in the module can refer to them too.
//! - `%provide` exports some of the module's variables.
//!
//! A require spec is one of:
//!
//! - a module's name, written as an identifier or a string
//! - `(only-in spec name ...)`
//! - `(except-in spec name ...)`
//! - `(prefix-in prefix spec)`
//! - `(rename-in spec (old new) ...)`
//!
//! A provide spec is one of:
//!
//! - a name: a variable or a macro that the module defines, or a binding that it requires. The module passes on a binding that it requires, and a module that gets it this way has the same binding as one that requires the defining module.
//! - `(rename-out (name external) ...)`
//! - `(all-defined-out)`, which exports every variable and every macro that the module defines
//! - `(all-var-defined-out)`, which exports every variable that the module defines and none of its macros. A module keeps a macro in memory only if another module can reach it, so this form keeps helper macros out of the arenas that load the module.
//! - `(all-from-out module ...)`, which passes on every binding that the module requires from each of the named modules, under the name that the module itself uses for it
//! - `(struct-out name)`, which exports every binding that the struct form for `name` defines
//! - `(struct-out name #:omit-constructor)`, which exports the same bindings without the form's
//!   constructors. An importing module then cannot use the struct's name as a value. See Scheme's
//!   `struct` for the uses of the name that remain.
//!
//! `%struct` defines a struct type as Scheme's `struct` does, with the same syntax for
//! fields and options. `(%struct point (x y))` defines `struct:point`, `point`, `point?`,
//! `point-x` and `point-y`. Code in any of the module's languages can use these bindings.
//!
//! A name refers to the innermost local variable of that name in scope. If there is none, the name
//! refers to the module variable of that name, and otherwise to the import of that name. The
//! expressions of a body run in order, and the body's value is the value of the last expression.
//! A list that does not start with a form's name is an error, because a call is written with `%app`.

mod lower;

#[cfg(test)]
#[path = "tests/lower.rs"]
mod tests;

pub use lower::{LowerError, LowerErrorKind, Lowerer, NoKeyword};

use ragwort_compiler::CompileError;
use ragwort_compiler::module::{BuildError, Item, Loaded, ModuleBuilder, Resolver};
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
    fn from(error: ReadError) -> Self {
        Error::Read(error)
    }
}

impl From<LowerError> for Error {
    fn from(error: LowerError) -> Self {
        Error::Lower(error)
    }
}

impl From<BuildError<'_>> for Error {
    fn from(error: BuildError<'_>) -> Self {
        match error {
            BuildError::Declare(error, span) => Error::Lower(LowerError::declared(error, span)),
            BuildError::Compile(error) => error.into(),
        }
    }
}

impl From<CompileError> for Error {
    fn from(error: CompileError) -> Self {
        match LowerError::located(error) {
            Some(lower) => Error::Lower(lower),
            None => Error::Compile(error),
        }
    }
}

/// Builds the module named `name` from the native ragwort source in `files`. The forms of all the
/// files make up one body. Names are interned in `symbols`. The code can call the host functions in
/// `hosts`, and `resolver` finds the modules that the code requires.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    name: &str,
    hosts: &'static [HostDef],
    files: &[&SyntaxSession],
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Error> {
    let name = symbols.intern_str(&Strings::new(mc), name).map_err(LowerError::from)?;
    let mut builder = ModuleBuilder::new(name.value(mc), hosts);
    let mut lowerer = Lowerer::new(mc, symbols, false)?;
    let mut items: Vec<Item<'gc>> = Vec::new();
    for session in files {
        for node in Reader::new(mc, symbols, session)? {
            let first = index(items.len())?;
            items.extend(lowerer.declare(&mut builder, resolver, node?, first)?);
        }
    }
    builder.provide_items(mc).map_err(BuildError::from)?;
    builder.start(mc).map_err(CompileError::from)?;
    let mut thunks = Vec::with_capacity(items.len());
    for (position, item) in items.into_iter().enumerate() {
        thunks.extend(builder.compile_item(mc, index(position)?, item)?);
    }
    let sealed = lowerer.seal(&mut builder);
    let module = builder.finish(mc).map_err(CompileError::from)?;
    sealed.patch(mc, module);
    Ok(Loaded { module, thunks })
}

/// Returns `position`, the position of a top-level form in its module, as the form's index.
fn index(position: usize) -> Result<u32, CompileError> {
    u32::try_from(position).map_err(|_| CompileError::OutOfMemory)
}
