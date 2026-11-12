//! A Chez-style micropass compiler compiling [`Core`] forms into [`ragwort_vm`] [`Bytecode`](ragwort_vm::objects::Bytecode).
//!
//! Each pass either optimizes code within an intermediate representation or simplifies the grammar by
//! eliminating forms:
//! 1. `lower`: Validates [`Core`] AST structures and lowers module-level variable references (`Place::Slot`)
//!    into slot primitives, producing `L1`.
//! 2. `letrec`: Implements Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing (`L1 -> L2`), transforming
//!    `Letrec` blocks into flat, sequential `Let` bindings of values and `Fix` groups (strongly connected
//!    components of unassigned mutually recursive lambdas) to prevent deep nesting of definitions.
//! 3. `cp0`: A source-level optimizer (`L2 -> L2`) performing copy and constant propagation, pure intrinsic
//!    constant folding, beta-reduction, local procedure inlining, conditional branch simplification, and dead-binding elimination.
//! 4. `assign`: Performs assignment conversion (`L2 -> L3`), transforming mutated (`Set`) variables into
//!    explicit heap boxes (`MakeBox`, `Unbox`, `SetBox`) so that all remaining variables in `L3` are immutable.
//! 5. `contify`: Contification pass (`L3 -> L3`), converting local functions called exclusively from tail position
//!    at a single call site (including self-recursive loops) into in-frame control-flow joins (`L3::Join` / `L3::Jump`).
//! 6. `closure`: Closure conversion (`L3 -> L4`), resolving lexical variable references into [`ir::VarRef::Local`]
//!    versus [`ir::VarRef::Upvalue`] and computing each closure's upvalue capture table.
//! 7. `l5`: Lowers each function into a control flow graph of basic blocks in SSA form (`L4 -> L5`). Debug builds
//!    verify SSA and block invariants across all compiled functions.
//! 8. `emit`: Performs register allocation and bytecode emission from L5 CFGs (`L5 -> Closure`).
//!
//! Each IR is represented as a flat arena table of nodes. Every pass following `lower` processes expressions
//! iteratively using its own explicit work stack, preventing machine call stack exhaustion regardless of expression
//! nesting or inlining depth. In debug builds, invariant assertions validate the IR tables produced by each pass.

mod assign;
mod closure;
mod contify;
mod cp0;
mod emit;
mod hash;
pub mod ir;
pub mod keyword;
mod l5;
mod letrec;
mod locals;
mod lower;
mod merge;
pub mod module;
pub mod steps;
pub mod structs;

#[cfg(test)]
#[path = "tests/compile.rs"]
mod tests;

use std::fmt;

use ragwort_alloc::Arena;

use ragwort_types::Wire;
use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_vm::objects::Module;
use ragwort_vm::{HostDef, Intrinsic, Request};

/// A local variable identifier, numbered uniquely by the expander so no two bindings share the same ID.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Var(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Place {
    Local(Var),
    /// A reference to module variable slot `slot`. If `checked` is false, the front end has verified
    /// that the slot is already defined wherever this code executes, and any [`Core::Set`] targeting it
    /// acts as its initialization.
    Slot { slot: u32, checked: bool },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub enum Prim {
    Intrinsic(Intrinsic),
    Request(Request),
    /// An invocation of a host function defined in the enclosing module's static host table.
    Host(&'static HostDef),
    /// An access to module variable slot `slot`, lowered from a [`Place::Slot`].
    Slot(SlotOp, u32),
}

/// The operation performed by a [`Prim::Slot`]: load operations take 0 arguments, while store operations
/// take 1 argument (the value to write). Checked variants raise an error at runtime if the slot is uninitialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub enum SlotOp {
    Load,
    LoadChecked,
    Store,
    StoreChecked,
}

impl SlotOp {
    /// Returns the argument arity expected by this slot operation.
    pub fn arity(self) -> usize {
        match self {
            SlotOp::Load | SlotOp::LoadChecked => 0,
            SlotOp::Store | SlotOp::StoreChecked => 1,
        }
    }
}

/// A lambda expression in the [`Core`] AST.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lambda<'gc> {
    /// A unique identifier distinguishing this lambda from all others within the compilation unit.
    pub id: u32,
    /// The number of trailing parameters in `params` that callers may omit, which default to
    /// [`Value::UNSUPPLIED`](ragwort_types::gc::Value::UNSUPPLIED).
    pub optional: u32,
    pub params: Vec<Var>,
    /// An optional rest parameter that receives any excess arguments as a list.
    pub rest: Option<Var>,
    pub body: Box<Core<'gc>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Core<'gc> {
    Quote(Value<'gc>),
    Ref(Place),
    If(Box<Core<'gc>>, Box<Core<'gc>>, Box<Core<'gc>>),
    /// Parallel lexical bindings: none of the bound `Var`s are in scope within the initialization expressions.
    Let(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Recursive lexical bindings (`letrec` / `letrec*`): all bound `Var`s are in scope across all
    /// initialization expressions and the body.
    Letrec(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Mutates a local variable or module slot; evaluates to `#<void>`.
    Set(Place, Box<Core<'gc>>),
    App(Box<Core<'gc>>, Vec<Core<'gc>>),
    Lambda(Lambda<'gc>),
    Intrinsic(Prim, Vec<Core<'gc>>),
    /// Invokes an intrinsic whose final argument is a list that is spread into remaining arguments, analogous to `apply`.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>),
}

impl Core<'_> {
    fn is_leaf(&self) -> bool {
        matches!(self, Core::Quote(_) | Core::Ref(_))
    }

    /// Extracts non-leaf child expressions from `self` and pushes them onto `out`, replacing them with leaf placeholder nodes.
    fn take_parts(&mut self, out: &mut std::vec::Vec<Self>) {
        let mut take = |part: &mut Self| {
            if !part.is_leaf() {
                out.push(std::mem::replace(part, Core::Quote(Value::VOID)));
            }
        };
        match self {
            Core::Quote(_) | Core::Ref(_) => {}
            Core::If(a, b, c) => [a, b, c].into_iter().for_each(|part| take(part)),
            Core::Let(binds, body) | Core::Letrec(binds, body) => {
                binds.iter_mut().for_each(|(_, init)| take(init));
                take(body);
            }
            Core::Set(_, value) => take(value),
            Core::App(f, args) => {
                take(f);
                args.iter_mut().for_each(take);
            }
            Core::Lambda(f) => take(&mut f.body),
            Core::Intrinsic(_, args) | Core::ApplyIntrinsic(_, args) => args.iter_mut().for_each(take),
        }
    }
}

/// Iteratively drops child subexpressions using an explicit heap stack, preventing call stack overflow
/// when deallocating deeply nested AST structures.
impl Drop for Core<'_> {
    fn drop(&mut self) {
        let mut parts = std::vec::Vec::new();
        self.take_parts(&mut parts);
        while let Some(mut part) = parts.pop() {
            part.take_parts(&mut parts);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// A [`Var`] was referenced without an enclosing lexical binding in scope.
    Unbound(Var),
    /// A [`Var`] identifier was bound multiple times within the same scope.
    Rebound(Var),
    /// Multiple [`Lambda`] nodes share the same identifier `id`.
    SameLambda(u32),
    /// A [`Lambda`] specifies an optional parameter count exceeding its total parameter count.
    TooManyOptional(u32),
    /// An intrinsic was invoked with an unsupported number of arguments.
    Arity(Prim),
    /// The number of constants in the compilation unit exceeded the 2^32 indexable limit.
    TooManyConstants,
    /// Attempted to call a host function not registered in the target module's host table.
    UnknownHost(&'static HostDef),
    /// Attempted to access a variable slot not present in the target module.
    UnknownSlot(u32),
    /// The combined count of parameters and spilled local variables exceeded the 2^32 limit.
    TooManyRegisters,
    /// A host function call supplied more arguments than can fit into an execution frame.
    TooManyArguments,
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
            Self::TooManyOptional(id) => write!(f, "lambda {id} has more optional parameters than parameters"),
            Self::Arity(Prim::Intrinsic(i)) => write!(f, "wrong number of arguments to {}", i.name()),
            Self::Arity(Prim::Request(r)) => write!(f, "wrong number of arguments to {}", r.name()),
            Self::Arity(Prim::Host(h)) => write!(f, "wrong number of arguments to host function {}", h.name),
            Self::Arity(Prim::Slot(_, slot)) => write!(f, "wrong number of arguments to an access of module variable {slot}"),
            Self::TooManyConstants => write!(f, "more than 2^32 constants"),
            Self::UnknownHost(h) => write!(f, "host function {} isn't one of the module's", h.name),
            Self::UnknownSlot(slot) => write!(f, "variable {slot} isn't one of the module's"),
            Self::TooManyRegisters => write!(f, "more than 2^32 locals"),
            Self::TooManyArguments => write!(f, "a host call with more arguments than fit a frame"),
            Self::OutOfMemory => write!(f, "out of memory"),
        }
    }
}

impl std::error::Error for CompileError {}

/// Compiles AST expression `core` in the context of `module` through the micropass pipeline into a
/// zero-argument [`Closure`](ragwort_vm::objects::Closure) ready for execution by [`ragwort_vm::Machine::new`].
pub fn compile<'gc>(mc: &Mutation<'gc>, module: Option<Gc<'gc, Module>>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
    let arena = Arena::new();
    let mut l5 = to_l5(mc, &arena, core)?;
    merge::merge(mc, &mut l5);
    #[cfg(debug_assertions)]
    l5::check(&l5);
    emit::emit(mc, module, &l5)
}

/// Transforms `core` through the lowering, fixing, optimization, assignment conversion, and closure conversion passes to produce an L5 SSA program.
fn to_l5<'a, 'gc>(mc: &Mutation<'gc>, arena: &'a Arena, core: &Core<'gc>) -> Result<l5::Program<'a, 'gc>, CompileError> {
    // Each intermediate IR table is deallocated as soon as the subsequent pass completes.
    ir::l1::scope(|mut l1| {
        let (root, supply) = lower::lower(&mut l1, core)?;
        ir::l2::scope(move |mut src| {
            let (root, supply) = letrec::fix_letrec(mc, &l1, root, &mut src, supply);
            drop(l1);
            #[cfg(debug_assertions)]
            src.check(root);
            ir::l2::scope(move |mut l2| {
                let (root, mut supply) = cp0::optimize(mc, &mut src, root, &mut l2, supply);
                drop(src);
                locals::replace(mc, &mut l2, root, &mut supply);
                letrec::prune(mc, &mut l2, root);
                #[cfg(debug_assertions)]
                l2.check(root);
                ir::l3::scope(move |mut l3| {
                    let (root, assigned) = assign::lower(&mut l3, &l2, root);
                    drop(l2);
                    #[cfg(debug_assertions)]
                    l3.check(root);
                    contify::contify(&mut l3, root);
                    #[cfg(debug_assertions)]
                    l3.check(root);
                    assign::convert(&mut l3, root, &assigned, &mut supply);
                    #[cfg(debug_assertions)]
                    l3.check(root);
                    ir::l4::scope(move |mut l4| {
                        let root = closure::closure_convert(&mut l4, &l3, root);
                        drop(l3);
                        #[cfg(debug_assertions)]
                        l4.check(root);
                        l5::lower(arena, &l4, root)
                    })
                })
            })
        })
    })
}
