//! Intermediate representations for the micropass compiler pipeline.
//!
//! Each pass either transforms an IR within the same grammar (`cp0: L2 -> L2`) or reduces the
//! grammar by eliminating forms:
//! - [`Core`](crate::Core) (`L0`): input from the expander/lowerer.
//! - [`L1`]: module variables (`Place::Slot`) lowered to slot primitives; all variables are
//!   lexical [`Var`]s.
//! - [`L2`]: `Letrec` eliminated via Waddell–Sarkar–Dybvig fixing in favor of `Let`s of values
//!   and of [`Bind::Fix`] groups (mutually recursive unassigned lambdas), `Seq`, and `Set`.
//! - [`L3`]: assignment conversion boxes (`MakeBox`, `Unbox`, `SetBox`) the assigned variables a
//!   closure or a re-entered continuation could see, after contification; the rest keep
//!   [`L3::Set`], assigned in their frame's registers.
//! - [`L4`]: closures converted; variable references are split into [`VarRef::Local`] and
//!   [`VarRef::Upvalue`], and every [`Closure`] carries its [`UpvalSource`] capture table.
//! - `L5`: each function a graph of basic blocks in SSA form, with block parameters where paths
//!   meet; see the `l5` module.

use ragwort_alloc::{Arena, Box, CollectIn, Vec};
use ragwort_types::gc::Value;
use ragwort_vm::Purity;

use crate::{Prim, SlotOp, Var};

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

/// A function of the passes' trees, in the compile's arena, over an expression type `E`.
#[derive(Debug, PartialEq, Eq)]
pub struct Func<'a, E> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub id: u32,
    /// How many of the last of `params` a call can leave out, which are then
    /// [`Value::UNSUPPLIED`].
    pub optional: u32,
    pub params: Vec<'a, Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub rest: Option<Var>,
    pub body: Box<'a, E>,
}

/// One of a `Let`'s bindings, of expressions `E` and functions `F`, in scope for those after it
/// and the `Let`'s body, so a body of many definitions is one `Let` however long it is.
#[derive(Debug, PartialEq, Eq)]
pub enum Bind<'a, E, F> {
    /// A variable bound to an expression's value.
    Val(Var, E),
    /// Functions, in scope in each other's code too.
    Fix(Vec<'a, (Var, F)>),
}

impl<E, F> Bind<'_, E, F> {
    /// The variables it binds.
    pub(crate) fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        let (one, group) = match self {
            Bind::Val(v, _) => (Some(*v), &[][..]),
            Bind::Fix(group) => (None, &group[..]),
        };
        one.into_iter().chain(group.iter().map(|(v, _)| *v))
    }
}

/// A binding of [`L2`].
pub type Bind2<'a, 'gc> = Bind<'a, L2<'a, 'gc>, Func<'a, L2<'a, 'gc>>>;
/// A binding of [`L3`].
pub type Bind3<'a, 'gc> = Bind<'a, L3<'a, 'gc>, Func<'a, L3<'a, 'gc>>>;
/// A binding of [`L4`].
pub type Bind4<'a, 'gc> = Bind<'a, L4<'a, 'gc>, Closure<'a, 'gc>>;

/// `L1`: lexical core forms after lowering module variables.
#[derive(Debug, PartialEq, Eq)]
pub enum L1<'a, 'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<'a, L1<'a, 'gc>>, Box<'a, L1<'a, 'gc>>, Box<'a, L1<'a, 'gc>>),
    Let(Vec<'a, (Var, L1<'a, 'gc>)>, Box<'a, L1<'a, 'gc>>),
    Letrec(Vec<'a, (Var, L1<'a, 'gc>)>, Box<'a, L1<'a, 'gc>>),
    Set(Var, Box<'a, L1<'a, 'gc>>),
    App(Box<'a, L1<'a, 'gc>>, Vec<'a, L1<'a, 'gc>>),
    Lambda(Func<'a, L1<'a, 'gc>>),
    Intrinsic(Prim, Vec<'a, L1<'a, 'gc>>),
    ApplyIntrinsic(Prim, Vec<'a, L1<'a, 'gc>>),
}

/// `L2`: after `letrec` fixing (`Letrec` replaced by `Let`s of values and `Fix` groups).
#[derive(Debug, PartialEq, Eq)]
pub enum L2<'a, 'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<'a, L2<'a, 'gc>>, Box<'a, L2<'a, 'gc>>, Box<'a, L2<'a, 'gc>>),
    Seq(Box<'a, L2<'a, 'gc>>, Box<'a, L2<'a, 'gc>>),
    Let(Vec<'a, Bind2<'a, 'gc>>, Box<'a, L2<'a, 'gc>>),
    Set(Var, Box<'a, L2<'a, 'gc>>),
    App(Box<'a, L2<'a, 'gc>>, Vec<'a, L2<'a, 'gc>>),
    Lambda(Func<'a, L2<'a, 'gc>>),
    Intrinsic(Prim, Vec<'a, L2<'a, 'gc>>),
    ApplyIntrinsic(Prim, Vec<'a, L2<'a, 'gc>>),
}

impl<'a, 'gc> Func<'a, L2<'a, 'gc>> {
    pub(crate) fn clone_in(&self, arena: &'a Arena) -> Self {
        let body = arena.boxed(self.body.clone_in(arena));
        Func { id: self.id, optional: self.optional, params: self.params.clone(), rest: self.rest, body }
    }
}

impl<'a, 'gc> L2<'a, 'gc> {
    /// The tree, leaving a constant in its place, for rewriting in place.
    pub(crate) fn take(&mut self) -> Self {
        std::mem::replace(self, L2::Quote(Value::VOID))
    }

    /// A copy, in `arena`.
    pub(crate) fn clone_in(&self, arena: &'a Arena) -> Self {
        let one = |e: &Self| arena.boxed(e.clone_in(arena));
        let all = |es: &Vec<'a, Self>| es.iter().map(|e| e.clone_in(arena)).collect_in(arena);
        match self {
            L2::Quote(v) => L2::Quote(*v),
            L2::Ref(v) => L2::Ref(*v),
            L2::If(a, b, c) => L2::If(one(a), one(b), one(c)),
            L2::Seq(a, b) => L2::Seq(one(a), one(b)),
            L2::Let(binds, body) => {
                let bind = |b: &Bind2<'a, 'gc>| match b {
                    Bind::Val(v, e) => Bind::Val(*v, e.clone_in(arena)),
                    Bind::Fix(group) => Bind::Fix(group.iter().map(|(v, f)| (*v, f.clone_in(arena))).collect_in(arena)),
                };
                L2::Let(binds.iter().map(bind).collect_in(arena), one(body))
            }
            L2::Set(v, e) => L2::Set(*v, one(e)),
            L2::App(f, args) => L2::App(one(f), all(args)),
            L2::Lambda(f) => L2::Lambda(f.clone_in(arena)),
            L2::Intrinsic(prim, args) => L2::Intrinsic(*prim, all(args)),
            L2::ApplyIntrinsic(prim, args) => L2::ApplyIntrinsic(*prim, all(args)),
        }
    }

    /// Whether evaluating `self` cannot fault or cause side effects.
    pub(crate) fn is_pure(&self) -> bool {
        match self {
            L2::Quote(_) | L2::Ref(_) | L2::Lambda(_) => true,
            L2::Seq(a, b) => a.is_pure() && b.is_pure(),
            L2::If(a, b, c) => a.is_pure() && b.is_pure() && c.is_pure(),
            L2::Let(binds, body) => binds.iter().all(|b| !matches!(b, Bind::Val(_, e) if !e.is_pure())) && body.is_pure(),
            L2::Intrinsic(Prim::Intrinsic(i), args) => i.is_discardable() && args.iter().all(Self::is_pure),
            L2::Intrinsic(Prim::Read(r), args) => r.is_discardable() && args.iter().all(Self::is_pure),
            L2::Intrinsic(Prim::Host(h), args) => h.purity == Purity::Discardable && args.iter().all(Self::is_pure),
            L2::Intrinsic(Prim::Slot(SlotOp::Load, _), _) => true,
            L2::Set(_, _) | L2::App(_, _) | L2::Intrinsic(_, _) | L2::ApplyIntrinsic(_, _) => false,
        }
    }

    /// Whether any normal return value of `self` is guaranteed not to be `#f`.
    pub(crate) fn is_always_truthy(&self) -> bool {
        match self {
            L2::Quote(v) => *v != Value::FALSE,
            L2::Lambda(_) | L2::Set(_, _) => true,
            L2::Intrinsic(Prim::Intrinsic(i), _) => i.is_always_truthy(),
            L2::Intrinsic(Prim::Read(r), _) => r.is_always_truthy(),
            L2::Seq(_, b) | L2::Let(_, b) => b.is_always_truthy(),
            L2::If(_, b, c) => b.is_always_truthy() && c.is_always_truthy(),
            L2::Ref(_) | L2::App(_, _) | L2::Intrinsic(_, _) | L2::ApplyIntrinsic(_, _) => false,
        }
    }
}

/// `L3`: assigned variables as [`L3::Set`]s, which assignment conversion leaves, after
/// contification, only for those it doesn't box. `Join` and `Jump` come only from contification.
#[derive(Debug, PartialEq, Eq)]
pub enum L3<'a, 'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<'a, L3<'a, 'gc>>, Box<'a, L3<'a, 'gc>>, Box<'a, L3<'a, 'gc>>),
    Seq(Box<'a, L3<'a, 'gc>>, Box<'a, L3<'a, 'gc>>),
    Let(Vec<'a, Bind3<'a, 'gc>>, Box<'a, L3<'a, 'gc>>),
    App(Box<'a, L3<'a, 'gc>>, Vec<'a, L3<'a, 'gc>>),
    Lambda(Func<'a, L3<'a, 'gc>>),
    Intrinsic(Prim, Vec<'a, L3<'a, 'gc>>),
    ApplyIntrinsic(Prim, Vec<'a, L3<'a, 'gc>>),
    /// `scope`, in which [`L3::Jump`]s to one of `group` go to its code, as they do in the
    /// group's code, as [`L4::Join`].
    Join { group: Vec<'a, (Var, Func<'a, L3<'a, 'gc>>)>, scope: Box<'a, L3<'a, 'gc>> },
    /// A jump to a join of an enclosing `Join` with values for its parameters.
    Jump(Var, Vec<'a, L3<'a, 'gc>>),
    /// An assignment of a variable, which evaluates to void.
    Set(Var, Box<'a, L3<'a, 'gc>>),
}

impl<'a, 'gc> L3<'a, 'gc> {
    /// The tree, leaving a constant in its place, for rewriting in place.
    pub(crate) fn take(&mut self) -> Self {
        std::mem::replace(self, L3::Quote(Value::VOID))
    }
}

/// A join's code: `body`, with `params` bound to the values a jump to `id` has.
#[derive(Debug, PartialEq, Eq)]
pub struct JoinCode<'a, 'gc> {
    pub id: Var,
    pub params: Vec<'a, Var>,
    pub body: L4<'a, 'gc>,
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

/// A closure with an explicit capture list and no implicit free variables.
#[derive(Debug, PartialEq, Eq)]
pub struct Closure<'a, 'gc> {
    pub id: u32,
    pub optional: u32,
    pub params: Vec<'a, Var>,
    pub rest: Option<Var>,
    pub captures: Vec<'a, UpvalSource>,
    pub body: Box<'a, L4<'a, 'gc>>,
}

/// `L4`: after closure conversion and tail-loop contification.
#[derive(Debug, PartialEq, Eq)]
pub enum L4<'a, 'gc> {
    Quote(Value<'gc>),
    Ref(VarRef),
    If(Box<'a, L4<'a, 'gc>>, Box<'a, L4<'a, 'gc>>, Box<'a, L4<'a, 'gc>>),
    Seq(Box<'a, L4<'a, 'gc>>, Box<'a, L4<'a, 'gc>>),
    Let(Vec<'a, Bind4<'a, 'gc>>, Box<'a, L4<'a, 'gc>>),
    /// `scope`, in which [`L4::Jump`]s to one of `group` go to its code, as they do in the group's
    /// code.
    Join { group: Vec<'a, JoinCode<'a, 'gc>>, scope: Box<'a, L4<'a, 'gc>> },
    /// A jump to a join of an enclosing `Join` with values for its parameters.
    Jump(Var, Vec<'a, L4<'a, 'gc>>),
    /// An assignment of a local of the frame, which evaluates to void.
    Set(Var, Box<'a, L4<'a, 'gc>>),
    App(Box<'a, L4<'a, 'gc>>, Vec<'a, L4<'a, 'gc>>),
    Lambda(Closure<'a, 'gc>),
    Intrinsic(Prim, Vec<'a, L4<'a, 'gc>>),
    ApplyIntrinsic(Prim, Vec<'a, L4<'a, 'gc>>),
}
