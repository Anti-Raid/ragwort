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

use ragwort_types::gc::Value;

use crate::hash::HashMap;
use crate::{Position, Var};

/// What an error report shows for a lambda: the name it is bound to and where its source form starts.
#[derive(Clone, Copy, Default)]
pub(crate) struct Described<'gc> {
    pub(crate) name: Option<Value<'gc>>,
    pub(crate) at: Option<Position<'gc>>,
}

/// What error reports need to know about the code being compiled: the description of each lambda, keyed by lambda ID, and the source sites that IR nodes refer to. Passes identify a function by its lambda ID and a position by its site number, so this information travels beside the IR tables instead of inside every record.
#[derive(Default)]
pub(crate) struct Origins<'gc> {
    lambdas: HashMap<u32, Described<'gc>>,
    pub(crate) sites: Sites<'gc>,
}

impl<'gc> Origins<'gc> {
    /// Records the name and position of `lambda`, where it has them.
    pub(crate) fn describe(&mut self, lambda: u32, name: Option<Value<'gc>>, at: Option<Position<'gc>>) {
        if name.is_some() || at.is_some() {
            let entry = self.lambdas.entry(lambda).or_default();
            if name.is_some() {
                entry.name = name;
            }
            if at.is_some() {
                entry.at = at;
            }
        }
    }

    pub(crate) fn name(&mut self, lambda: u32, name: Value<'gc>) {
        self.lambdas.entry(lambda).or_default().name = Some(name);
    }

    pub(crate) fn get(&self, lambda: u32) -> Described<'gc> {
        self.lambdas.get(&lambda).copied().unwrap_or_default()
    }

    /// Gives the lambda `to`, a copy of the lambda `from`, the same description.
    pub(crate) fn copy(&mut self, from: u32, to: u32) {
        if let Some(&described) = self.lambdas.get(&from) {
            self.lambdas.insert(to, described);
        }
    }
}

/// An inlined call: the procedure whose body was copied into its caller, and the site of the call it replaced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Inlined<'gc> {
    /// The procedure's name, a symbol.
    pub(crate) name: Value<'gc>,
    pub(crate) call: u32,
}

/// A source site: a position, and the inlined call it is part of. `inlined` is an index into [`Sites::inlined`] plus one, or 0 for code that was written in the function it belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Site<'gc> {
    pub(crate) at: Position<'gc>,
    pub(crate) inlined: u32,
}

/// The source sites of the code being compiled. IR nodes refer to a site by its index plus one, so that 0 can stand for "no known position".
#[derive(Default)]
pub(crate) struct Sites<'gc> {
    pub(crate) sites: Vec<Site<'gc>>,
    pub(crate) inlined: Vec<Inlined<'gc>>,
    /// The site already made for a site moved into an inlined call, keyed by the original site and the inlined call.
    moved: HashMap<(u32, u32), u32>,
}

impl<'gc> Sites<'gc> {
    /// Adds a site for code at `at` that is not part of an inlined call.
    pub(crate) fn add(&mut self, at: Position<'gc>) -> u32 {
        self.sites.push(Site { at, inlined: 0 });
        self.sites.len() as u32
    }

    pub(crate) fn get(&self, site: u32) -> Option<Site<'gc>> {
        self.sites.get((site as usize).checked_sub(1)?).copied()
    }

    /// Adds a site for code at `at` that is part of the inlined call numbered `inlined`.
    pub(crate) fn add_in(&mut self, at: Position<'gc>, inlined: u32) -> u32 {
        self.sites.push(Site { at, inlined });
        self.sites.len() as u32
    }

    /// Records that the body of the procedure named `name` was inlined in place of the call at `call`, and returns the inlined call's number.
    pub(crate) fn inline(&mut self, name: Value<'gc>, call: u32) -> u32 {
        self.inlined.push(Inlined { name, call });
        self.inlined.len() as u32
    }

    /// Returns the site for code at `site` once it is part of the inlined call `within`. Code that was already part of an inlined call keeps that call, which itself becomes part of `within`.
    pub(crate) fn within(&mut self, site: u32, within: u32) -> u32 {
        let Some(original) = self.get(site) else { return 0 };
        if let Some(&moved) = self.moved.get(&(site, within)) {
            return moved;
        }
        let inlined = match self.inlined.get((original.inlined as usize).wrapping_sub(1)).copied() {
            Some(inner) => {
                let call = self.within(inner.call, within);
                self.inline(inner.name, call)
            }
            None => within,
        };
        self.sites.push(Site { at: original.at, inlined });
        let moved = self.sites.len() as u32;
        self.moved.insert((site, within), moved);
        moved
    }
}

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
