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
    /// The keyword of a keyword parameter, or `None` for a positional parameter.
    pub keyword: Option<Keyword<'gc>>,
    /// The default value expression, or `None` if the parameter is required. The default is evaluated inside the procedure when a call omits the argument. It may refer to the parameters written before this one.
    pub default: Option<Core<'gc>>,
}

/// A lambda with optional or keyword parameters, as Racket's `lambda` takes them.
///
/// For `(lambda (a [b 2] #:k [k 3] . rest) body)`, `params` holds `a`, `b` and `k` in written order:
///
/// - `a` has no default, so it is required.
/// - `b` has a default, so it is an optional positional parameter. A required positional parameter must not follow an optional one.
/// - `k` is a keyword parameter. A call passes it as `#:k value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptionalLambda<'gc> {
    /// A unique identifier, like [`Lambda::id`]. The plain lambda that the compiler builds from this one uses it.
    pub id: u32,
    pub params: Vec<Formal<'gc>>,
    /// An optional rest parameter that receives any excess positional arguments as a list.
    pub rest: Option<Var>,
    pub body: Box<Core<'gc>>,
    /// The procedure's name, as in [`Lambda::name`].
    pub name: Option<Value<'gc>>,
    /// The position of the definition, as in [`Lambda::at`].
    pub at: Option<Position<'gc>>,
}

/// One argument of a [`Core::KeywordApp`]. `keyword` is `None` for a positional argument.
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
    /// Returns the source position of this expression, if it is a call or a built-in operation that has one.
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
    /// Calls a procedure with arguments. The last field is the source position of the call, which error reports use. It is `None` for a call that a front end or the compiler generated.
    App(Box<Core<'gc>>, Vec<Core<'gc>>, Option<Position<'gc>>),
    Lambda(Lambda<'gc>),
    /// Applies a built-in operation to arguments. The last field is the source position, as for `App`.
    Intrinsic(Prim, Vec<Core<'gc>>, Option<Position<'gc>>),
    /// Invokes an intrinsic whose final argument is a list that is spread into remaining arguments, analogous to `apply`. The last field is the source position, as for `App`.
    ApplyIntrinsic(Prim, Vec<Core<'gc>>, Option<Position<'gc>>),
    /// A lambda with optional or keyword parameters. The compiler turns it into a plain lambda that evaluates the defaults. If any parameter has a keyword, the compiler also wraps that lambda in a keyword procedure.
    OptionalLambda(OptionalLambda<'gc>),
    /// A call with keyword arguments. The arguments are in written order, which is also their evaluation order. The last field is the source position, as for `App`.
    ///
    /// If the compiler knows that the callee is a keyword procedure that accepts the arguments, the call goes directly to its core procedure. Otherwise the keywords are matched when the call runs.
    KeywordApp(Box<Core<'gc>>, Vec<Arg<'gc>>, Option<Position<'gc>>),
    /// A reference to a module-level binding by name. The symbol names a variable of the module being built, or an import. The span covers the name in the source and locates the error if the name is unbound.
    ///
    /// The compiler resolves the name. A front end therefore only has to tell local variables apart from all other names.
    Global(Value<'gc>, SyntaxSpan<'gc>),
    /// An assignment to a module variable by name. The fields are the variable's name (a symbol), the new value, and the span of the name.
    SetGlobal(Value<'gc>, Box<Core<'gc>>, SyntaxSpan<'gc>),
    /// A reference to a binding imported from another module. The compiler reads the value from that module. A call of an imported procedure is inlined if the procedure has an inline template.
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
            Core::If(test, consequent, other) => [test, consequent, other].into_iter().for_each(|part| take(part)),
            Core::Let(binds, body) | Core::Letrec(binds, body) => {
                binds.iter_mut().for_each(|(_, init)| take(init));
                take(body);
            }
            Core::Set(_, value) => take(value),
            Core::App(function, args, _) => {
                take(function);
                args.iter_mut().for_each(take);
            }
            Core::SetGlobal(_, value, _) => take(value),
            Core::Lambda(lambda) => take(&mut lambda.body),
            Core::OptionalLambda(lambda) => {
                lambda.params.iter_mut().filter_map(|formal| formal.default.as_mut()).for_each(&mut take);
                take(&mut lambda.body);
            }
            Core::KeywordApp(function, args, _) => {
                take(function);
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
    /// A module-level name is used incorrectly. The name is at bytes `start..end` of its source.
    Global { kind: GlobalError, start: u32, end: u32 },
    OutOfMemory,
}

/// The kind of error in a [`Core::Global`] or [`Core::SetGlobal`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlobalError {
    /// The module neither defines nor imports the name.
    Unbound,
    /// The name is assigned, but it is immutable: an import, a binding of a struct declaration, or a keyword procedure.
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Import(module::Unusable::Uninitialized) => write!(formatter, "an import whose module hasn't defined it yet"),
            Self::Import(module::Unusable::MatchOnly) => write!(formatter, "a struct whose constructor its module doesn't provide"),
            Self::Global { kind: GlobalError::Unbound, .. } => write!(formatter, "a name nothing defines"),
            Self::Global { kind: GlobalError::Immutable, .. } => write!(formatter, "an assignment of a name that can't change"),
            Self::Global { kind: GlobalError::Import(unusable), .. } => Self::Import(*unusable).fmt(formatter),
            Self::Unbound(var) => write!(formatter, "unbound variable {}", var.0),
            Self::Rebound(var) => write!(formatter, "variable {} bound more than once", var.0),
            Self::SameLambda(id) => write!(formatter, "lambda {id} appears more than once"),
            Self::TooManyOptional(id) => write!(formatter, "lambda {id} has more optional parameters than parameters"),
            Self::Formals(id) => write!(formatter, "lambda {id} repeats a keyword, or has a required parameter after an optional one"),
            Self::SameKeyword => write!(formatter, "a call passes the same keyword twice"),
            Self::Arity(Prim::Intrinsic(intrinsic)) => write!(formatter, "wrong number of arguments to {}", intrinsic.name()),
            Self::Arity(Prim::Request(request)) => write!(formatter, "wrong number of arguments to {}", request.name()),
            Self::Arity(Prim::Host(host)) => write!(formatter, "wrong number of arguments to host function {}", host.name),
            Self::Arity(Prim::Slot(_, slot)) => write!(formatter, "wrong number of arguments to an access of module variable {slot}"),
            Self::TooManyConstants => write!(formatter, "more than 2^32 constants"),
            Self::UnknownHost(host) => write!(formatter, "host function {} isn't one of the module's", host.name),
            Self::UnknownSlot(slot) => write!(formatter, "variable {slot} isn't one of the module's"),
            Self::TooManyRegisters => write!(formatter, "more than 2^32 locals"),
            Self::TooManyArguments => write!(formatter, "a host call with more arguments than fit a frame"),
            Self::OutOfMemory => write!(formatter, "out of memory"),
        }
    }
}

impl std::error::Error for CompileError {}

/// Compiles AST expression `core` in the context of `module` through the micropass pipeline into a
/// zero-argument [`Closure`](ragwort_vm::objects::Closure) ready for execution by [`ragwort_vm::Machine::new`].
pub fn compile<'gc>(mc: &Mutation<'gc>, module: Option<Gc<'gc, Module>>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
    compile_in(mc, module, core, None).map(|(thunk, _)| thunk)
}

/// Compiles `core` like [`compile`], with an optional module context `unit`.
///
/// With a `unit`, the compiler resolves module-level names, and calls of the module's struct and keyword procedures. If the form defines a procedure that has an inline template, the template is returned with the thunk.
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
    let mut l5 = to_l5(mc, &arena, core, &mut names, slots, unit, &mut inline)?;
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
    slot_names: Option<AnyVector<'gc>>,
    unit: Option<&module::Unit<'_, 'gc>>,
    inline: &mut Option<module::Inline>,
) -> Result<l5::Program<'a, 'gc>, CompileError> {
    // Each intermediate IR table is deallocated as soon as the subsequent pass completes.
    ir::l1::scope(|mut l1| {
        let (root, supply) = lower::lower(mc, &mut l1, core, names, slot_names, unit)?;
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
