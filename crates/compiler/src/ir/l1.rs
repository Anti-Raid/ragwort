//! `L1`: lexical core forms after module variables have been lowered to slot operations. Uses a
//! node table like [`L2`](super::l2), but still contains `letrec` forms.

use ragwort_types::gc::Value;

use crate::{Prim, Var};

language! {
    table L1;
    node Node {
        Quote(value: Value<'gc>),
        Ref(var: Var),
        If(test: Id<'id>, then: Id<'id>, other: Id<'id>),
        Let(binds: Span<'id, (Var, Id<'id>)>, body: Id<'id>),
        Letrec(binds: Span<'id, (Var, Id<'id>)>, body: Id<'id>),
        Set(var: Var, value: Id<'id>),
        App(callee: Id<'id>, args: Span<'id, Id<'id>>),
        Lambda(fun: Fun<'id>),
        Intrinsic(prim: Prim, args: Span<'id, Id<'id>>),
        ApplyIntrinsic(prim: Prim, args: Span<'id, Id<'id>>),
    }
    functions functions: Function<'id>, Fun, function, body body;
    lists { ids: Id<'id>, binds: (Var, Id<'id>), vars: Var }
    leaves { Value<'gc>, Var, Prim }
}

impl<'id, 'gc> Children<'id, 'gc> for (Var, Id<'id>) {
    fn each(self, _: &L1<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
        visit(self.1);
    }
}

impl<'id, 'gc> Bodies<'id, 'gc> for (Var, Id<'id>) {
    fn bodies(self, _: &L1<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
}

/// A lambda's function record.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Function<'id> {
    /// Distinguishes this lambda from every other in the expression being compiled.
    pub(crate) id: u32,
    /// Number of trailing entries in `params` that a call may omit.
    pub(crate) optional: u32,
    pub(crate) params: Span<'id, Var>,
    /// Receives the arguments past `params` as a list, if any.
    pub(crate) rest: Option<Var>,
    pub(crate) body: Id<'id>,
}
