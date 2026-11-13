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
//! 4. `assign`: Performs assignment conversion (`L2 -> L3`) in two phases around `contify`. The first phase lowers
//!    `L2` to `L3` and keeps each `Set`. The second phase, which runs after contification, moves a mutated variable
//!    into an explicit heap box (`MakeBox`, `Unbox`, `SetBox`) only if it cannot stay in a frame register, for
//!    example because a closure captures it. Every other mutated variable stays in its register.
//! 5. `contify`: Contification pass (`L3 -> L3`), converting local functions called exclusively from tail position
//!    at a single call site (including self-recursive loops) into in-frame control-flow joins (`L3::Join` / `L3::Jump`).
//! 6. `closure`: Closure conversion (`L3 -> L4`), resolving lexical variable references into [`ir::VarRef::Local`]
//!    versus [`ir::VarRef::Upvalue`] and computing each closure's upvalue capture table.
//! 7. `l5`: Lowers each function into a control flow graph of basic blocks in SSA form (`L4 -> L5`). Debug builds
//!    verify SSA and block invariants across all compiled functions.
//! 8. `emit`: Performs register allocation and bytecode emission from L5 CFGs (`L5 -> Closure`).
//!
//! Three optimizations run between these passes without changing the representation: `locals` replaces local
//! structs with their fields and `letrec::prune` removes the bindings left unused, both on `L2` after `cp0`, and
//! `merge` replaces redundant reads with earlier values on `L5` before `emit`.
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
use ragwort_types::symbol::Keyword;
use ragwort_types::syntax::SyntaxSpan;
use ragwort_types::vector::AnyVector;
use ragwort_vm::objects::{Module, ModuleFields};
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

/// A parameter of an [`OptionalLambda`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Formal<'gc> {
    pub var: Var,
    /// The keyword a call passes the argument by, or `None` for a positional parameter.
    pub keyword: Option<Keyword<'gc>>,
    /// The expression whose value the parameter takes when a call omits the argument, or `None` for a required parameter. It is evaluated inside the procedure, and may refer to the parameters written before this one.
    pub default: Option<Core<'gc>>,
}

/// A lambda with optional or keyword parameters, as Racket's `lambda` takes them.
///
/// For `(lambda (a [b 2] #:k [k 3] . rest) body)`, `params` holds `a`, `b` and `k` in the order written:
///
/// - `a` has no default, so it is required.
/// - `b` is an optional positional parameter. A required positional parameter may not follow one.
/// - `k` is passed by the keyword `#:k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptionalLambda<'gc> {
    /// A unique identifier, as [`Lambda::id`] is, for the plain lambda this one becomes.
    pub id: u32,
    pub params: Vec<Formal<'gc>>,
    /// An optional rest parameter that receives any excess positional arguments as a list.
    pub rest: Option<Var>,
    pub body: Box<Core<'gc>>,
    /// As [`Lambda::name`].
    pub name: Option<Value<'gc>>,
    /// As [`Lambda::at`].
    pub at: Option<Position<'gc>>,
}

/// An argument of a [`Core::KeywordApp`]: its value, and the keyword it is passed by if it is not positional.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arg<'gc> {
    pub keyword: Option<Keyword<'gc>>,
    pub value: Core<'gc>,
}

/// A position in source text: the source it belongs to, as the value of a [`SyntaxSource`](ragwort_types::syntax::SyntaxSource), and a byte offset into that source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position<'gc> {
    pub source: Value<'gc>,
    pub offset: u32,
}

impl<'gc> Position<'gc> {
    /// Returns the position where `span` starts, or `None` for a span that belongs to no source.
    pub fn of(mc: &Mutation<'gc>, span: SyntaxSpan<'gc>) -> Option<Self> {
        Some(Self { source: span.source()?.value(mc), offset: span.start() })
    }
}

impl<'gc> Core<'gc> {
    /// Returns the source position this expression carries, if it is a call or a built-in operation that has one.
    pub fn position(&self) -> Option<Position<'gc>> {
        match self {
            Core::App(_, _, at) | Core::Intrinsic(_, _, at) | Core::ApplyIntrinsic(_, _, at) | Core::KeywordApp(_, _, at) => *at,
            _ => None,
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
    /// The symbol the lambda is bound to by the definition or binding form that created it, if any. Error reports show it as the procedure's name.
    pub name: Option<Value<'gc>>,
    /// Where the lambda's source form starts, if a front end read it from source. Error reports show it as the procedure's location.
    pub at: Option<Position<'gc>>,
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
    /// Calls a procedure with arguments. The last field is the source position of the call, which an error raised by the call reports; it is `None` for a call that a front end or the compiler made up.
    App(Box<Core<'gc>>, Vec<Core<'gc>>, Option<Position<'gc>>),
    Lambda(Lambda<'gc>),
    /// Applies a built-in operation to arguments. The last field is the source position, as for `App`.
    Intrinsic(Prim, Vec<Core<'gc>>, Option<Position<'gc>>),
    /// Invokes an intrinsic whose final argument is a list that is spread into remaining arguments, analogous to `apply`. The last field is the source position, as for `App`.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>, Option<Position<'gc>>),
    /// A lambda with optional or keyword parameters. The compiler turns it into a plain lambda that evaluates the defaults, and into a keyword procedure around that lambda if any parameter has a keyword.
    OptionalLambda(OptionalLambda<'gc>),
    /// A call with keyword arguments, written in the order the call evaluates them. The compiler passes the arguments straight to the core of a keyword procedure it knows, and otherwise leaves the matching of keywords to the call at run time. The last field is the source position, as for `App`.
    KeywordApp(Box<Core<'gc>>, Vec<Arg<'gc>>, Option<Position<'gc>>),
    /// A reference to the binding that the symbol names at the top level of the module being built: one of its variables, or an import. The compiler resolves the name, so a front end only tells local variables from every other name. The span locates the name in the source, for the error of a name that the module does not bind.
    Global(Value<'gc>, SyntaxSpan<'gc>),
    /// An assignment of the module variable that the symbol names, with the span of the name.
    SetGlobal(Value<'gc>, Box<Core<'gc>>, SyntaxSpan<'gc>),
    /// A reference to a binding imported from another module. The compiler reads the binding's value from the module, and expands a call of an imported procedure from the procedure's inline template when it has one.
    Import(module::Import<'gc>),
}

impl Core<'_> {
    fn is_leaf(&self) -> bool {
        matches!(self, Core::Quote(_) | Core::Ref(_) | Core::Import(_) | Core::Global(..))
    }

    /// Extracts non-leaf child expressions from `self` and pushes them onto `out`, replacing them with leaf placeholder nodes.
    fn take_parts(&mut self, out: &mut std::vec::Vec<Self>) {
        let mut take = |part: &mut Self| {
            if !part.is_leaf() {
                out.push(std::mem::replace(part, Core::Quote(Value::VOID)));
            }
        };
        match self {
            Core::Quote(_) | Core::Ref(_) | Core::Import(_) | Core::Global(..) => {}
            Core::If(a, b, c) => [a, b, c].into_iter().for_each(|part| take(part)),
            Core::Let(binds, body) | Core::Letrec(binds, body) => {
                binds.iter_mut().for_each(|(_, init)| take(init));
                take(body);
            }
            Core::Set(_, value) => take(value),
            Core::App(f, args, _) => {
                take(f);
                args.iter_mut().for_each(take);
            }
            Core::SetGlobal(_, value, _) => take(value),
            Core::Lambda(f) => take(&mut f.body),
            Core::OptionalLambda(f) => {
                f.params.iter_mut().filter_map(|formal| formal.default.as_mut()).for_each(&mut take);
                take(&mut f.body);
            }
            Core::KeywordApp(f, args, _) => {
                take(f);
                args.iter_mut().for_each(|arg| take(&mut arg.value));
            }
            Core::Intrinsic(_, args, _) | Core::ApplyIntrinsic(_, args, _) => args.iter_mut().for_each(take),
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
    /// An [`OptionalLambda`] has two parameters with the same keyword, or a required positional parameter after an optional one.
    Formals(u32),
    /// A [`Core::KeywordApp`] passes two arguments by the same keyword.
    SameKeyword,
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
    /// A reference to an import that cannot be used as a value where it appears.
    Import(module::Unusable),
    /// A misuse of the top-level name at bytes `start..end` of its source.
    Global { kind: GlobalError, start: u32, end: u32 },
    OutOfMemory,
}

/// What is wrong with a use of a top-level name, a [`Core::Global`] or [`Core::SetGlobal`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlobalError {
    /// The module neither defines nor imports the name.
    Unbound,
    /// The name is assigned, but it is an import, a struct's binding or a keyword procedure, which cannot change.
    Immutable,
    /// The name is an import that cannot be used as a value.
    Import(module::Unusable),
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
            Self::Import(module::Unusable::Uninitialized) => write!(f, "an import whose module hasn't defined it yet"),
            Self::Import(module::Unusable::MatchOnly) => write!(f, "a struct whose constructor its module doesn't provide"),
            Self::Global { kind: GlobalError::Unbound, .. } => write!(f, "a name nothing defines"),
            Self::Global { kind: GlobalError::Immutable, .. } => write!(f, "an assignment of a name that can't change"),
            Self::Global { kind: GlobalError::Import(unusable), .. } => Self::Import(*unusable).fmt(f),
            Self::Unbound(v) => write!(f, "unbound variable {}", v.0),
            Self::Rebound(v) => write!(f, "variable {} bound more than once", v.0),
            Self::SameLambda(id) => write!(f, "lambda {id} appears more than once"),
            Self::TooManyOptional(id) => write!(f, "lambda {id} has more optional parameters than parameters"),
            Self::Formals(id) => write!(f, "lambda {id} repeats a keyword, or has a required parameter after an optional one"),
            Self::SameKeyword => write!(f, "a call passes the same keyword twice"),
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
    compile_in(mc, module, core, None).map(|(thunk, _)| thunk)
}

/// Compiles `core` as [`compile`] does. With a `unit`, calls of the struct procedures and keyword procedures that the module being built defines are resolved from its declarations, and the inline template of the procedure that the form defines is returned with the thunk, if the procedure has one.
pub(crate) fn compile_in<'gc>(
    mc: &Mutation<'gc>,
    module: Option<Gc<'gc, Module>>,
    core: &Core<'gc>,
    unit: Option<&module::Unit<'_, 'gc>>,
) -> Result<(Value<'gc>, Option<module::Inline>), CompileError> {
    let arena = Arena::new();
    let mut inline = None;
    let mut names = ir::Origins::default();
    let slots = module.and_then(|module| AnyVector::of(module.names(mc)));
    let mut l5 = to_l5(mc, &arena, core, &mut names, &|slot| slots?.get(mc, slot as usize), unit, &mut inline)?;
    merge::merge(mc, &mut l5);
    #[cfg(debug_assertions)]
    l5::check(&l5);
    Ok((emit::emit(mc, module, &l5, &names)?, inline))
}

/// Transforms `core` through the lowering, fixing, optimization, assignment conversion, and closure conversion passes to produce an L5 SSA program.
fn to_l5<'a, 'gc>(
    mc: &Mutation<'gc>,
    arena: &'a Arena,
    core: &Core<'gc>,
    names: &mut ir::Origins<'gc>,
    slot_name: &dyn Fn(u32) -> Option<Value<'gc>>,
    unit: Option<&module::Unit<'_, 'gc>>,
    inline: &mut Option<module::Inline>,
) -> Result<l5::Program<'a, 'gc>, CompileError> {
    // Each intermediate IR table is deallocated as soon as the subsequent pass completes.
    ir::l1::scope(|mut l1| {
        let (root, supply) = lower::lower(mc, &mut l1, core, names, slot_name, unit)?;
        if let Some(fun) = unit.and_then(|unit| unit.defining()).and_then(|slot| lower::defined(&l1, root, slot)) {
            *inline = module::Inline::of_function(mc, &l1, &names.sites, fun, names.get(l1[fun].id).at);
        }
        ir::l2::scope(move |mut src| {
            let (root, supply) = letrec::fix_letrec(mc, &l1, root, &mut src, supply);
            drop(l1);
            #[cfg(debug_assertions)]
            src.check(root);
            ir::l2::scope(move |mut l2| {
                let (root, mut supply) = cp0::optimize(mc, &mut src, root, &mut l2, supply, names);
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
