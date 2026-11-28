//! The expander that ragwort's front ends share. It gives a language hygienic macros.
//!
//! A front end reads its source into the expander's tree of syntax, and expands the tree to the compiler's core forms. This crate has
//! the parts of that work that do not depend on the language:
//!
//! - [`scope`]: sets of scopes. Hygiene uses them, as in Racket. A binding form adds a fresh scope to the identifiers that it binds and to
//!   its body. Each macro step flips a fresh scope on its input and on its output. An identifier refers to the binding of its name whose
//!   scope set is the largest subset of the identifier's own.
//! - [`tree`]: the syntax tree, with scope operations that stay pending until a node is taken apart.
//! - [`Engine`]: the state of one expansion. It binds identifiers and resolves them, converts between the tree and the arena's syntax
//!   objects, and creates and runs the transformers of macros.
//! - [`Expand`]: the operations that expand expressions of the language: `syntax-case`, and the transformer of a macro definition.
//! - [`forms`]: the core forms, which are the forms of native ragwort. The expander of every language expands them.
//!
//! # How a front end uses it
//!
//! A front end has a type of its own that holds an [`Engine`] and dereferences to it. The type implements [`Host`]: it names the type of
//! the language's keywords, and it expands one expression. The front end's forms are methods of that type. They call the engine for
//! everything in the list above, and the engine calls [`Host::expand`] for the expressions inside the forms that it handles.
//!
//! The engine does not know the forms of a language, except the core forms. A keyword is a value of the front end's own type, bound to a name.
//!
//! # Macros across modules
//!
//! A module can provide a macro that it defines at the top level. The module keeps the macro's transformer in a variable slot, and its
//! export says which language the macro's output is in. See [`Export::transformer`](ragwort_compiler::module::Export::transformer).
//! Another module can use the macro if the output is made of core forms, or if both modules have the same language.
//!
//! The output of a macro refers to bindings of the macro's own module. This works as follows:
//!
//! - Each identifier in a syntax object carries a binding value. For a module-level name, the value names the module that binds it. See [`Engine::binding_value`].
//! - A module's own names get their module when the module is finished. See [`Engine::seal`]. The module also keeps the binding of each such name, even if it does not export it.
//! - When another module expands the macro's output, an identifier that the macro introduced lacks that module's own scope. The engine then resolves
//!   it by its binding value. See [`Engine::origin`].

mod case;
mod convert;
mod engine;
mod expand;
pub mod forms;
mod macros;
pub mod scope;
mod table;
pub mod tree;

use std::fmt;

use ragwort_types::gc::OutOfMemory;

pub use crate::engine::{Binding, Engine, MACRO_FUEL, Sealed, Stamp};
pub use crate::table::{Ambiguous, Table};
pub use crate::expand::{Call, Ex, Expand, Host, Work};
pub use crate::forms::{CoreForm, Forms};

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
    /// A list is where an expression goes, and it does not start with the name of a form. Reported by a language that writes a call with a form.
    NotAForm,
    /// An `%intrinsic` or `%apply-intrinsic` names something that is not an intrinsic available to the code.
    UnknownIntrinsic,
    /// A `%call-host` names something that is not one of the host functions given to the module.
    UnknownHost,
    /// An `%intrinsic` or `%call-host` has a number of arguments that the intrinsic or host function does not accept.
    Arity,
    /// A `%break` or `%continue` names a loop that is not around it.
    Label,
    /// The code uses a macro of another language. The macro's output is not made of core forms, so only its own language can expand it.
    Language,
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
            ExpandErrorKind::NotAForm => "a list that doesn't start with a form's name",
            ExpandErrorKind::UnknownIntrinsic => "an intrinsic the code can't name",
            ExpandErrorKind::UnknownHost => "a host function the module wasn't given",
            ExpandErrorKind::Arity => "an intrinsic or host call with the wrong number of arguments",
            ExpandErrorKind::Label => "a break or continue of a loop that isn't around it",
            ExpandErrorKind::Language => "a macro of another language",
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
