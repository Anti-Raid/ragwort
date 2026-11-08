//! Intermediate representations for the micropass compiler pipeline.
//!
//! Each pass either transforms an IR within the same grammar (`cp0: L2 -> L2`) or reduces the
//! grammar by eliminating forms:
//! - [`Core`](crate::Core) (`L0`): input from the expander/lowerer.
//! - [`L1`]: globals (`DefineGlobal`, `Place::Global`, `Place::Import`) lowered to intrinsics and
//!   constants; all variables are lexical [`Var`]s.
//! - [`L2`]: `Letrec` eliminated via Waddell–Sarkar–Dybvig fixing in favor of `Let`, `Fix`
//!   (mutually recursive unassigned lambdas), `Seq`, and `Set`.
//! - [`L3`]: `Set` eliminated via assignment conversion (`MakeBox`, `Unbox`, `SetBox`); all
//!   variables are immutable.
//! - [`L4`]: closures converted; variable references are split into [`VarRef::Local`] and
//!   [`VarRef::Upvalue`], and every [`Closure`] carries its [`UpvalSource`] capture table.

use ragwort_types::gc::Value;
use ragwort_vm::Purity;

use crate::{Func, Prim, Var};

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

/// `L1`: lexical core forms after lowering globals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum L1<'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<L1<'gc>>, Box<L1<'gc>>, Box<L1<'gc>>),
    Let(Vec<(Var, L1<'gc>)>, Box<L1<'gc>>),
    Letrec(Vec<(Var, L1<'gc>)>, Box<L1<'gc>>),
    Set(Var, Box<L1<'gc>>),
    App(Box<L1<'gc>>, Vec<L1<'gc>>),
    Lambda(Func<L1<'gc>>),
    Intrinsic(Prim, Vec<L1<'gc>>),
    ApplyIntrinsic(Prim, Vec<L1<'gc>>),
}

/// `L2`: after `letrec` fixing (`Letrec` replaced by `Fix` and `Seq`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum L2<'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<L2<'gc>>, Box<L2<'gc>>, Box<L2<'gc>>),
    Seq(Box<L2<'gc>>, Box<L2<'gc>>),
    Let(Vec<(Var, L2<'gc>)>, Box<L2<'gc>>),
    Fix(Vec<(Var, Func<L2<'gc>>)>, Box<L2<'gc>>),
    Set(Var, Box<L2<'gc>>),
    App(Box<L2<'gc>>, Vec<L2<'gc>>),
    Lambda(Func<L2<'gc>>),
    Intrinsic(Prim, Vec<L2<'gc>>),
    ApplyIntrinsic(Prim, Vec<L2<'gc>>),
}

impl<'gc> L2<'gc> {
    /// Whether evaluating `self` cannot fault or cause side effects.
    pub(crate) fn is_pure(&self) -> bool {
        match self {
            L2::Quote(_) | L2::Ref(_) | L2::Lambda(_) => true,
            L2::Seq(a, b) => a.is_pure() && b.is_pure(),
            L2::If(a, b, c) => a.is_pure() && b.is_pure() && c.is_pure(),
            L2::Let(binds, body) => binds.iter().all(|(_, init)| init.is_pure()) && body.is_pure(),
            L2::Fix(_, body) => body.is_pure(),
            L2::Intrinsic(Prim::Intrinsic(i), args) => i.is_discardable() && args.iter().all(Self::is_pure),
            L2::Intrinsic(Prim::Read(r), args) => r.is_discardable() && args.iter().all(Self::is_pure),
            L2::Intrinsic(Prim::Host(h), args) => h.purity == Purity::Discardable && args.iter().all(Self::is_pure),
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
            L2::Seq(_, b) | L2::Let(_, b) | L2::Fix(_, b) => b.is_always_truthy(),
            L2::If(_, b, c) => b.is_always_truthy() && c.is_always_truthy(),
            L2::Ref(_) | L2::App(_, _) | L2::Intrinsic(_, _) | L2::ApplyIntrinsic(_, _) => false,
        }
    }

    /// Simplifies `first` in an effect context before `second`, dropping pure subexpressions.
    pub(crate) fn seq(first: Self, second: Self) -> Self {
        if first.is_pure() {
            return second;
        }
        match first {
            L2::Seq(a, b) => Self::seq(*a, Self::seq(*b, second)),
            L2::Intrinsic(Prim::Intrinsic(i), args) if i.is_discardable() => {
                args.into_iter().rfold(second, |acc, a| Self::seq(a, acc))
            }
            L2::Intrinsic(Prim::Read(r), args) if r.is_discardable() => args.into_iter().rfold(second, |acc, a| Self::seq(a, acc)),
            L2::Intrinsic(Prim::Host(h), args) if h.purity == Purity::Discardable => {
                args.into_iter().rfold(second, |acc, a| Self::seq(a, acc))
            }
            L2::If(test, then, other) if then.is_pure() && other.is_pure() => Self::seq(*test, second),
            first => L2::Seq(Box::new(first), Box::new(second)),
        }
    }
}

/// `L3`: after assignment conversion (`Set` eliminated; all variables are immutable).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum L3<'gc> {
    Quote(Value<'gc>),
    Ref(Var),
    If(Box<L3<'gc>>, Box<L3<'gc>>, Box<L3<'gc>>),
    Seq(Box<L3<'gc>>, Box<L3<'gc>>),
    Let(Vec<(Var, L3<'gc>)>, Box<L3<'gc>>),
    Fix(Vec<(Var, Func<L3<'gc>>)>, Box<L3<'gc>>),
    App(Box<L3<'gc>>, Vec<L3<'gc>>),
    Lambda(Func<L3<'gc>>),
    Intrinsic(Prim, Vec<L3<'gc>>),
    ApplyIntrinsic(Prim, Vec<L3<'gc>>),
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure<'gc> {
    pub id: u32,
    pub params: Vec<Var>,
    pub rest: Option<Var>,
    pub captures: Vec<UpvalSource>,
    pub body: Box<L4<'gc>>,
}

/// `L4`: after closure conversion and tail-loop contification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum L4<'gc> {
    Quote(Value<'gc>),
    Ref(VarRef),
    If(Box<L4<'gc>>, Box<L4<'gc>>, Box<L4<'gc>>),
    Seq(Box<L4<'gc>>, Box<L4<'gc>>),
    Let(Vec<(Var, L4<'gc>)>, Box<L4<'gc>>),
    Fix(Vec<(Var, Closure<'gc>)>, Box<L4<'gc>>),
    /// An in-frame tail-recursive loop contified from a single-binding `Fix`.
    Loop {
        id: Var,
        params: Vec<(Var, L4<'gc>)>,
        body: Box<L4<'gc>>,
    },
    /// A tail-recursive jump back to the enclosing `Loop` `id` with updated parameter values.
    Recur(Var, Vec<L4<'gc>>),
    App(Box<L4<'gc>>, Vec<L4<'gc>>),
    Lambda(Closure<'gc>),
    Intrinsic(Prim, Vec<L4<'gc>>),
    ApplyIntrinsic(Prim, Vec<L4<'gc>>),
}
