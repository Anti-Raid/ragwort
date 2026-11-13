//! Scalar replacement of local structs (`L2 -> L2`).
//!
//! Runs after cp0 so uses exposed by inlining can qualify. A struct used only through eligible
//! field reads and writes can be replaced by field variables. For example, `(let ((c (cell 0)))
//! (set-cell-v! c 5) (cell-v c))` becomes a local variable initialized to zero, assigned five, then
//! read.
//!
//! Keep the allocation if any use requires the struct itself, such as a remaining procedure call,
//! return, store, comparison, or truth test.

use ragwort_types::gc::{Gc, Mutation};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Intrinsic, structs};

use crate::hash::{HashMap, HashSet};
use crate::ir::Supply;
use crate::ir::l2::{Bind, Id, L2, Node};
use crate::{Prim, Var};

/// A struct allocation bound by a `let`, recording its type and binding node.
struct Made<'id, 'gc> {
    kind: Gc<'gc, StructType>,
    binder: Id<'id>,
    /// Field reads and writes. Replacement is allowed only when these account for every use of the
    /// struct variable.
    uses: Vec<(Id<'id>, Use<'id>)>,
}

/// A field operation that can be replaced by a read or write of a local variable.
#[derive(Clone, Copy)]
enum Use<'id> {
    Read(usize),
    Write(usize, Id<'id>),
}

/// Replaces eligible structs reachable from `root` when all uses are field reads or writes.
pub(crate) fn replace<'id, 'gc>(mc: &Mutation<'gc>, tree: &mut L2<'id, 'gc>, root: Id<'id>, supply: &mut Supply) {
    let (mut made, mut refs, mut assigned) = (HashMap::<Var, Made<'id, 'gc>>::default(), HashMap::<Var, usize>::default(), HashSet::default());
    for id in tree.deep(root) {
        match tree[id] {
            Node::Ref(var) => *refs.entry(var).or_default() += 1,
            Node::Set(var, _) => _ = assigned.insert(var),
            Node::Let(binds, _) => {
                for &bind in &tree[binds] {
                    if let Bind::Val(var, init) = bind
                        && let Some((kind, _)) = tree.made_struct(mc, init)
                    {
                        made.insert(var, Made { kind, binder: id, uses: Vec::new() });
                    }
                }
            }
            _ => {}
        }
    }
    if made.is_empty() {
        return;
    }
    let found: Vec<(Var, Id<'id>, Use<'id>)> = tree.deep(root).filter_map(|id| Some((id, field_use(mc, tree, &made, id)?))).map(|(id, (var, field))| (var, id, field)).collect();
    for (var, id, field) in found {
        made.get_mut(&var).expect("a struct's variable").uses.push((id, field));
    }
    for (var, struct_made) in made {
        if !assigned.contains(&var) && refs.get(&var).copied().unwrap_or(0) == struct_made.uses.len() {
            fields_for(tree, var, &struct_made, &assigned, supply);
        }
    }
}

/// Recognizes a nonfaulting field operation at `id` on a struct in `made`, returning its variable
/// and field operation.
fn field_use<'id, 'gc>(mc: &Mutation<'gc>, tree: &L2<'id, 'gc>, made: &HashMap<Var, Made<'id, 'gc>>, id: Id<'id>) -> Option<(Var, Use<'id>)> {
    let Node::Intrinsic(Prim::Intrinsic(intrinsic), args) = tree[id] else { return None };
    let args = &tree[args];
    let Node::Ref(var) = tree[*args.first()?] else { return None };
    let made_as = made.get(&var)?.kind;
    let constant = |at: usize| match tree[args[at]] {
        Node::Quote(value) => Some(value),
        _ => None,
    };
    let index = |at: usize| usize::try_from(constant(at)?.as_fixnum()?).ok();
    // A typed field access is valid when the allocated struct derives from the requested type and the
    // index is in range.
    let by_type = |at: usize| {
        let kind = constant(1)?.downcast::<StructType>(mc)?;
        index(at).filter(|&position| structs::derives(mc, made_as, kind) && position < kind.fields(mc) as usize)
    };
    let field = match (intrinsic, args.len()) {
        (Intrinsic::StructField | Intrinsic::StructFixedField, 2) => Use::Read(index(1).filter(|&position| position < made_as.fields(mc) as usize)?),
        (Intrinsic::StructRef, 3) => Use::Read(by_type(2)?),
        (Intrinsic::StructSet, 4) => Use::Write(by_type(2).filter(|&position| structs::is_mutable(mc, made_as, position))?, args[3]),
        _ => return None,
    };
    Some((var, field))
}

/// Replaces the struct bound to `var` with its fields. Creates variables for mutable fields and
/// initializers that require evaluation; reuses other field values directly.
fn fields_for<'id, 'gc>(tree: &mut L2<'id, 'gc>, var: Var, made: &Made<'id, 'gc>, assigned: &HashSet<Var>, supply: &mut Supply) {
    let Node::Let(binds, body) = tree[made.binder] else { unreachable!("a struct's variable is bound by a let") };
    let mut binds = tree[binds].to_vec();
    let at = binds.iter().position(|bind| matches!(bind, Bind::Val(bound, _) if *bound == var)).expect("the let binds the variable");
    let Bind::Val(_, init) = binds[at] else { unreachable!("found as one") };
    let Node::Intrinsic(_, args) = tree[init] else { unreachable!("a struct is made by an intrinsic") };
    let values = tree[args][1..].to_vec();
    let set: HashSet<usize> = made.uses.iter().filter_map(|&(_, field)| if let Use::Write(position, _) = field { Some(position) } else { None }).collect();
    let (mut bound, mut fields) = (Vec::new(), Vec::with_capacity(values.len()));
    for (position, &value) in values.iter().enumerate() {
        let copyable = match tree[value] {
            Node::Quote(_) => true,
            Node::Ref(other) => !assigned.contains(&other),
            _ => false,
        };
        if copyable && !set.contains(&position) {
            fields.push(tree[value]);
        } else {
            let field = supply.fresh_var();
            bound.push(Bind::Val(field, value));
            fields.push(Node::Ref(field));
        }
    }
    for &(id, field) in &made.uses {
        match field {
            Use::Read(position) => tree.set(id, fields[position]),
            Use::Write(position, value) => {
                let Node::Ref(field) = fields[position] else { unreachable!("a field that's set is a variable") };
                tree.set(id, Node::Set(field, value));
            }
        }
    }
    binds.splice(at..=at, bound);
    let binds = tree.list(binds);
    tree.set(made.binder, Node::Let(binds, body));
}
