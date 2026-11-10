//! A Chez-style micropass compiler from [`Core`] forms to [`ragwort_vm`]'s [`Bytecode`](ragwort_vm::objects::Bytecode).
//!
//! Each pass either simplifies within an intermediate representation or reduces the grammar by
//! eliminating forms:
//! 1. `lower`: validates [`Core`] and lowers module variables (`Place::Slot`) to slot
//!    primitives, producing `L1`.
//! 2. `letrec`: Waddell–Sarkar–Dybvig `letrec` / `letrec*` fixing (`L1 -> L2`), replacing
//!    `Letrec` with one `Let` of bindings in order, values and `Fix` groups (SCCs of unassigned
//!    mutually recursive lambdas), so a body's definitions nest no deeper however many there are.
//! 3. `cp0`: source-level optimizer (`L2 -> L2`) performing copy/constant propagation,
//!    pure intrinsic constant folding, beta-reduction, local procedure
//!    inlining, conditional simplification, and dead-binding elimination.
//! 4. `assign`: assignment conversion (`L2 -> L3`), rewriting only mutated (`Set`) variables into
//!    explicit `MakeBox` / `Unbox` / `SetBox` intrinsics so all variables in `L3` are
//!    immutable.
//! 5. `contify`: contification (`L3 -> L3`), turning local functions only ever called in tail
//!    position of one place, loops among them, into in-frame joins (`L3::Join` / `L3::Jump`).
//! 6. `closure`: closure conversion (`L3 -> L4`), resolving lexical references into
//!    [`ir::VarRef::Local`] vs [`ir::VarRef::Upvalue`] and computing each closure's capture table.
//! 7. `l5`: each function as a graph of basic blocks in SSA form (`L4 -> L5`). A debug build
//!    checks the L5 of everything it compiles.
//! 8. `emit`: register allocation and bytecode emission from L5 (`L5 -> Closure`).
//!
//! Each IR is a table of nodes, and every pass after `lower` is a loop over a stack of its own,
//! so how deeply code nests, or inlining makes it nest, takes no more of the machine's stack.
//! A debug build checks each table a pass makes.

mod assign;
mod closure;
mod contify;
mod cp0;
mod emit;
mod hash;
pub mod ir;
mod l5;
mod letrec;
mod lower;
pub mod module;
pub mod steps;

#[cfg(test)]
#[path = "tests/compile.rs"]
mod tests;

use std::fmt;

use ragwort_alloc::Arena;

use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value};
use ragwort_vm::objects::Module;
use ragwort_vm::{HostDef, Intrinsic, Read, Request};

/// A local variable, numbered by the expander so no two bindings share one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Var(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Place {
    Local(Var),
    /// Variable `slot` of the module the code is compiled into. Unless `checked`, the front end
    /// knows it's defined wherever this runs, and a [`Core::Set`] of it is its definition.
    Slot { slot: u32, checked: bool },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prim {
    Intrinsic(Intrinsic),
    Read(Read),
    Request(Request),
    /// A host function, from a static table, which the code's module carries.
    Host(&'static HostDef),
    /// An access of variable `slot` of the code's module, which [`Place::Slot`] lowers to.
    Slot(SlotOp, u32),
}

/// What a [`Prim::Slot`] does: a load takes no arguments and a store one, its value. A checked
/// one faults if the variable isn't defined yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SlotOp {
    Load,
    LoadChecked,
    Store,
    StoreChecked,
}

impl SlotOp {
    /// How many arguments it takes.
    pub fn arity(self) -> usize {
        match self {
            SlotOp::Load | SlotOp::LoadChecked => 0,
            SlotOp::Store | SlotOp::StoreChecked => 1,
        }
    }
}

/// A lambda expression in [`Core`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lambda<'gc> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub id: u32,
    /// How many of the last of `params` a call can leave out, which are then
    /// [`Value::UNSUPPLIED`](ragwort_types::gc::Value::UNSUPPLIED).
    pub optional: u32,
    pub params: Vec<Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub rest: Option<Var>,
    pub body: Box<Core<'gc>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Core<'gc> {
    Quote(Value<'gc>),
    Ref(Place),
    If(Box<Core<'gc>>, Box<Core<'gc>>, Box<Core<'gc>>),
    /// Parallel bindings: none of the `Var`s are in scope in the right-hand sides.
    Let(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Recursive bindings (`letrec` / `letrec*`): all of the `Var`s are in scope in the
    /// right-hand sides and the body.
    Letrec(Vec<(Var, Core<'gc>)>, Box<Core<'gc>>),
    /// Evaluates to void.
    Set(Place, Box<Core<'gc>>),
    App(Box<Core<'gc>>, Vec<Core<'gc>>),
    Lambda(Lambda<'gc>),
    Intrinsic(Prim, Vec<Core<'gc>>),
    /// Like `Intrinsic`, with the last argument a list of the rest, as `apply` takes them.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>),
}

impl Core<'_> {
    fn is_leaf(&self) -> bool {
        matches!(self, Core::Quote(_) | Core::Ref(_))
    }

    /// Moves the parts of `self` that have parts of their own onto `out`, leaving leaves.
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

/// Drops the parts of a form from a stack of its own, so dropping it takes no more of the
/// machine's stack however deeply it nests.
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
    /// A [`Var`] used where no enclosing binding bound it.
    Unbound(Var),
    /// A [`Var`] bound more than once.
    Rebound(Var),
    /// Two [`Lambda`]s with the same `id`.
    SameLambda(u32),
    /// A [`Lambda`], by `id`, with more optional parameters than parameters.
    TooManyOptional(u32),
    /// A [`Core::Intrinsic`] with a number of arguments the [`Prim`] doesn't take.
    Arity(Prim),
    /// More constants than a [`u32`] index can name.
    TooManyConstants,
    /// A call of a host function the module the code is compiled into doesn't have.
    UnknownHost(&'static HostDef),
    /// A variable the module the code is compiled into doesn't have.
    UnknownSlot(u32),
    /// More parameters or spilled locals than a [`u32`] can count.
    TooManyRegisters,
    /// A call of a host function with more arguments than fit a frame.
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
            Self::Arity(Prim::Read(r)) => write!(f, "wrong number of arguments to {}", r.name()),
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

/// Compiles `core`, as code of `module`, if any, through the micropass pipeline into a
/// [`Closure`](ragwort_vm::objects::Closure) of no arguments, ready to pass to
/// [`ragwort_vm::Machine::new`].
pub fn compile<'gc>(mc: &Mutation<'gc>, module: Option<Gc<'gc, Module>>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
    let arena = Arena::new();
    let l5 = to_l5(mc, &arena, core)?;
    #[cfg(debug_assertions)]
    l5::check(&l5);
    emit::emit(mc, module, &l5)
}

/// `core` through the passes to L5.
fn to_l5<'a, 'gc>(mc: &Mutation<'gc>, arena: &'a Arena, core: &Core<'gc>) -> Result<l5::Program<'a, 'gc>, CompileError> {
    // Each table is dropped once the next is made from it.
    ir::l1::scope(|mut l1| {
        let (root, supply) = lower::lower(&mut l1, core)?;
        ir::l2::scope(move |mut src| {
            let (root, supply) = letrec::fix_letrec(&l1, root, &mut src, supply);
            drop(l1);
            #[cfg(debug_assertions)]
            src.check(root);
            ir::l2::scope(move |mut l2| {
                let (root, mut supply) = cp0::optimize(mc, &mut src, root, &mut l2, supply);
                drop(src);
                letrec::prune(&mut l2, root);
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
