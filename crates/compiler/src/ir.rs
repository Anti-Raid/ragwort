//! Intermediate representations for the micropass compiler pipeline.
//!
//! Each pass either transforms an IR within the same grammar (`cp0: L2 -> L2`) or reduces the
//! grammar by eliminating forms. Each is a table of nodes, which refer to their children by id,
//! made by its module's `language!`, rather than a tree of boxes:
//! - [`Core`](crate::Core) (`L0`): input from the expander/lowerer.
//! - `L1`: module variables (`Place::Slot`) lowered to slot primitives; all variables are
//!   lexical [`Var`]s.
//! - `L2`: `Letrec` eliminated via Waddell–Sarkar–Dybvig fixing in favor of `Let`s of values
//!   and of `Fix` groups (mutually recursive unassigned lambdas), `Seq`, and `Set`.
//! - `L3`: assignment conversion boxes (`MakeBox`, `Unbox`, `SetBox`) the assigned variables a
//!   closure or a re-entered continuation could see, after contification; the rest keep their
//!   `Set`s, assigned in their frame's registers. `Join` and `Jump` come only from contification.
//! - `L4`: closures converted; variable references are split into [`VarRef::Local`] and
//!   [`VarRef::Upvalue`], and every closure carries its [`UpvalSource`] capture table.
//! - `L5`: each function a graph of basic blocks in SSA form, with block parameters where paths
//!   meet; see the `l5` module.

#[macro_use]
mod language;
pub(crate) mod l1;
pub(crate) mod l2;
pub(crate) mod l3;
pub(crate) mod l4;

use crate::Var;
/// Fresh variable and lambda identifier generator threaded across passes.
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

/// Where a closure's upvalue comes from in the immediately enclosing function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UpvalSource {
    /// A local variable of the enclosing function.
    Local(Var),
    /// Upvalue `index` of the enclosing function.
    Upvalue(u32),
    /// The enclosing function's own closure object (`frame::CLOSURE`, register 0).
    SelfClosure,
}

/// A resolved variable reference inside a closure-converted expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarRef {
    Local(Var),
    Upvalue(u32),
    /// The currently executing closure (`frame::CLOSURE`, register 0).
    SelfClosure,
}
