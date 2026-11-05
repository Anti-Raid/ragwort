//! A Chez-style micropass compiler from [`Core`] forms to [` ragwort_vm`]'s [`Bytecode`].
//!
//! Each pass either simplifies within an intermediate representation or reduces the grammar by
//! eliminating forms:
//! 1. [`lower`]: validates [`Core`] and lowers `DefineGlobal`, `Place::Global`, and
//!    `Place::Import` to explicit intrinsics and constants, producing [`ir::L1`].
//! 2. [`letrec`]: Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing (`L1 -> L2`), replacing
//!    `Letrec` with `Let`, `Fix` (SCCs of unassigned mutually recursive lambdas), `Seq`, and `Set`.
//! 3. [`cp0`]: source-level optimizer (`L2 -> L2`) performing copy/constant propagation, prelude
//!    procedure call lowering, pure intrinsic constant folding, beta-reduction, local procedure
//!    inlining, conditional simplification, and dead-binding elimination.
//! 4. [`assign`]: assignment conversion (`L2 -> L3`), rewriting only mutated (`Set`) variables into
//!    explicit `MakeBox` / `Unbox` / `SetBox` intrinsics so all variables in [`ir::L3`] are
//!    immutable.
//! 5. [`closure`]: closure conversion (`L3 -> L4`), resolving lexical references into
//!    [`ir::VarRef::Local`] vs [`ir::VarRef::Upvalue`] and computing each closure's capture table.
//! 6. [`codegen`]: scoped virtual register allocation and bytecode emission (`L4 -> Closure`).

mod assign;
mod closure;
mod codegen;
mod cp0;
pub mod ir;
mod letrec;
mod lower;

#[cfg(test)]
#[path = "tests/compile.rs"]
mod tests;

use std::fmt;

use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_vm::objects::Global;
use ragwort_vm::{Intrinsic, Request};

/// A local variable, numbered by the expander so no two bindings share one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Var(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Place<'gc> {
    Local(Var),
    Global(Gc<'gc, Global>),
    /// A global of the prelude's, which code outside the prelude cannot assign or redefine.
    Import(Gc<'gc, Global>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prim {
    Intrinsic(Intrinsic),
    Request(Request),
}

/// A function parameterization and body parameterized over an IR expression type `E`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Func<E> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub id: u32,
    pub params: Vec<Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub rest: Option<Var>,
    pub body: Box<E>,
}

/// A lambda expression in [`Core`].
pub type Lambda<'gc> = Func<Core<'gc>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Core<'gc> {
    Quote(Value<'gc>),
    Ref(Place<'gc>),
    If(Box<Core<'gc>>, Box<Core<'gc>>, Box<Core<'gc>>),
    /// Parallel bindings: none of the `Var`s are in scope in the right-hand sides.
    Let(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Recursive bindings (`letrec` / `letrec*`): all of the `Var`s are in scope in the
    /// right-hand sides and the body.
    Letrec(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Evaluates to void.
    Set(Place<'gc>, Box<Core<'gc>>),
    /// Sets the [`Global`] and marks it defined, evaluating to void.
    DefineGlobal(Gc<'gc, Global>, Box<Core<'gc>>),
    App(Box<Core<'gc>>, Vec<Core<'gc>>),
    Lambda(Lambda<'gc>),
    Intrinsic(Prim, Vec<Core<'gc>>),
    /// Like `Intrinsic`, with the last argument a list of the rest, as `apply` takes them.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// A [`Var`] used where no enclosing binding bound it.
    Unbound(Var),
    /// A [`Var`] bound more than once.
    Rebound(Var),
    /// Two [`Lambda`]s with the same `id`.
    SameLambda(u32),
    /// A [`Core::Intrinsic`] with a number of arguments the [`Prim`] doesn't take.
    Arity(Prim),
    /// More constants than a [`u32`] index can name.
    TooManyConstants,
    /// More parameters or spilled locals than a [`u32`] can count.
    TooManyRegisters,
    /// Expressions nested more than 1024 deep.
    TooDeep,
    OutOfMemory,
}

impl From<OutOfMemory> for CompileError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<ragwort_types::Error> for CompileError {
    fn from(_: ragwort_types::Error) -> Self {
        Self::OutOfMemory
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unbound(v) => write!(f, "unbound variable {}", v.0),
            Self::Rebound(v) => write!(f, "variable {} bound more than once", v.0),
            Self::SameLambda(id) => write!(f, "lambda {id} appears more than once"),
            Self::Arity(Prim::Intrinsic(i)) => write!(f, "wrong number of arguments to {}", i.name()),
            Self::Arity(Prim::Request(r)) => write!(f, "wrong number of arguments to {}", r.name()),
            Self::TooManyConstants => write!(f, "more than 2^32 constants"),
            Self::TooManyRegisters => write!(f, "more than 2^32 locals"),
            Self::TooDeep => write!(f, "expressions nested too deeply"),
            Self::OutOfMemory => write!(f, "out of memory"),
        }
    }
}

impl std::error::Error for CompileError {}

/// Compiles `core` through the micropass pipeline into a [`Closure`](ragwort_vm::objects::Closure)
/// of no arguments, ready to pass to [`ragwort_vm::Machine::new`].
pub fn compile<'gc>(mc: &Mutation<'gc>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
    let (l1, supply) = lower::lower_globals(mc, core)?;
    let (l2, supply) = letrec::fix_letrec(l1, supply);
    let (l2, supply) = cp0::optimize(mc, l2, supply);
    let (l3, _) = assign::assignment_convert(l2, supply);
    let l4 = closure::closure_convert(&l3);
    codegen::emit(mc, &l4)
}
