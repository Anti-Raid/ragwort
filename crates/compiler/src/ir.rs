//! Intermediate representations (IRs) for the micropass compiler pipeline.
//!
//! Each pass either optimizes an IR within the same grammar (e.g. `cp0: L2 -> L2`) or lowers
//! the language by eliminating specific syntactic forms. Each IR is represented as a flat arena
//! table of nodes referencing children by numeric IDs (generated via the `language!` macro in each
//! IR module) rather than as a heap-allocated tree of boxed structures:
//! - [`Core`](crate::Core) (`L0`): Input AST produced by the expander and lowerer.
//! - `L1`: Lowers module-level variable references (`Place::Slot`) into slot access primitives;
//!   all variables are lexical [`Var`] identifiers.
//! - `L2`: Eliminates `Letrec` via Waddell–Sarkar–Dybvig fixing into sequential `Let` bindings
//!   of values, `Fix` groups (mutually recursive unassigned lambdas), sequences, and assignments.
//! - `L3`: Performs assignment conversion, wrapping mutable variables accessed across closure or
//!   continuation boundaries into explicit heap boxes (`MakeBox`, `Unbox`, `SetBox`) after contification.
//!   Remaining assigned variables are mutated in place within frame registers via `Set`. Introduces
//!   `Join` and `Jump` forms from contification.
//! - `L4`: Performs closure conversion, partitioning variable references into [`VarRef::Local`]
//!   and [`VarRef::Upvalue`], with every closure annotated with an [`UpvalSource`] capture table.
//! - `L5`: Represents each function as a control flow graph of basic blocks in SSA form with block
//!   parameters at merge points; see the `l5` module.

#[macro_use]
mod language;
pub(crate) mod l1;
pub(crate) mod l2;
pub(crate) mod l3;
pub(crate) mod l4;

use crate::Var;
/// Generates fresh variable and lambda identifiers, threaded across compiler passes.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Supply {
    pub(crate) next_var: u32,
    pub(crate) next_lambda: u32,
}

impl Supply {
    pub(crate) fn fresh_var(&mut self) -> Var {
        let v = Var(self.next_var);
        self.next_var = self.next_var.checked_add(1).expect("fewer than 2^32 variables");
        v
    }

    pub(crate) fn fresh_lambda(&mut self) -> u32 {
        let id = self.next_lambda;
        self.next_lambda = self.next_lambda.checked_add(1).expect("fewer than 2^32 lambdas");
        id
    }
}

/// The origin of a closure's upvalue within its immediately enclosing function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UpvalSource {
    /// Sourced from a local variable in the enclosing function's frame.
    Local(Var),
    /// Sourced from upvalue slot `index` in the enclosing function's capture table.
    Upvalue(u32),
    /// Sourced from the enclosing function's own closure object (`frame::CLOSURE`, located in register 0).
    SelfClosure,
}

/// A resolved variable reference within a closure-converted expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarRef {
    Local(Var),
    Upvalue(u32),
    /// References the currently executing closure object (`frame::CLOSURE`, located in register 0).
    SelfClosure,
}
