//! The compiler: core forms, as lowering will make them from ragwort, to the VM's bytecode.
//!
//! It doesn't optimize yet. A local variable lives in a register of its frame, unless a lambda
//! captures it: then it's boxed where it's bound, and closures share the box, whether or not
//! anything assigns it. Globals are [`Global`] cells, kept in the module's constants.

mod analyze;
mod compile;

#[cfg(test)]
#[path = "tests/compile.rs"]
mod tests;

pub use compile::{CompileError, compile};

use ragwort_types::gc::{Gc, Value};
use ragwort_vm::objects::Global;
use ragwort_vm::{Intrinsic, Request};

/// A local variable. Lowering numbers each binding apart, so no two binders in what's compiled
/// share one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Var(pub u32);

/// What a reference or a `%set!` names.
#[derive(Clone, Copy, Debug)]
pub enum Place<'gc> {
    Local(Var),
    Global(Gc<'gc, Global>),
}

/// What [`Core::Intrinsic`] calls: an intrinsic, which runs in place, or a request, which the
/// VM's outer loop carries out.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    Intrinsic(Intrinsic),
    Request(Request),
}

#[derive(Debug)]
pub enum Core<'gc> {
    /// `(%quote datum)`: the value, from the module's constants.
    Quote(Value<'gc>),
    /// The value of a variable.
    Ref(Place<'gc>),
    /// `(%if test then else)`.
    If(Box<Core<'gc>>, Box<Core<'gc>>, Box<Core<'gc>>),
    /// `(%let ((var init) ...) body)`: the inits, in order, then the body with the variables
    /// bound to them. Sequencing is a `Let` of a variable nothing reads.
    Let(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// `(%letrec ((var init) ...) body)`: the variables bound, to void, then the inits run in
    /// order and assigned to them, then the body.
    Letrec(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// `(%set! place value)`, which returns void.
    Set(Place<'gc>, Box<Core<'gc>>),
    /// `(%define-global global value)`, which returns void.
    DefineGlobal(Gc<'gc, Global>, Box<Core<'gc>>),
    /// `(%app f arg ...)`.
    App(Box<Core<'gc>>, Vec<Core<'gc>>),
    Lambda(Lambda<'gc>),
    /// `(%intrinsic name arg ...)`: a call of a built-in, with as many arguments as it takes.
    Intrinsic(Prim, Vec<Core<'gc>>),
    /// `(%apply-intrinsic name arg ... list)`: an `Intrinsic` whose last argument is a list of
    /// more. A built-in that takes a fixed number checks it as it runs.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>),
}

/// `(%lambda (param ... . rest) body)`. Lowering numbers each lambda apart, as it does variables,
/// so what the compiler finds out about one is kept by its `id`.
#[derive(Debug)]
pub struct Lambda<'gc> {
    pub id: u32,
    pub params: Vec<Var>,
    pub rest: Option<Var>,
    pub body: Box<Core<'gc>>,
}
