//! Pass 3b (`L2 -> L2`): a struct that only the code that makes it uses becomes variables.
//!
//! It runs on what cp0 made, so a struct handed to a procedure that cp0 inlined counts as used
//! only by what that procedure did with it.
//!
//! In `(let ((c (cell 0))) (set-cell-v! c 5) (cell-v c))`, nothing but the reads and the set
//! can tell `c` from a variable that holds its field, so that's what it becomes: the `let`
//! binds the variable, the set assigns it, and the read is a reference to it.
//!
//! A struct is left as it is if any use of its variable is something else: it's passed to a
//! procedure that's still called, returned, stored, compared, or tested for being true.

use ragwort_types::gc::{Gc, Mutation};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Intrinsic, structs};

use crate::hash::{HashMap, HashSet};
use crate::ir::Supply;
use crate::ir::l2::{Bind, Id, L2, Node};
use crate::{Prim, Var};

/// A struct a `let` binds a variable to: its type, and the `let`.
struct Made<'id, 'gc> {
    kind: Gc<'gc, StructType>,
    binder: Id<'id>,
    /// The reads and sets of its fields, which are all its variable's uses if it's replaced.
    uses: Vec<(Id<'id>, Use<'id>)>,
}

/// A use of a struct's variable that a variable for the field can stand in for.
#[derive(Clone, Copy)]
enum Use<'id> {
    Read(usize),
    Write(usize, Id<'id>),
}

/// Replaces each struct from `root` that only reads and sets of its fields use.
pub(crate) fn replace<'id, 'gc>(mc: &Mutation<'gc>, tree: &mut L2<'id, 'gc>, root: Id<'id>, supply: &mut Supply) {
    let (mut made, mut refs, mut assigned) = (HashMap::<Var, Made<'id, 'gc>>::default(), HashMap::<Var, usize>::default(), HashSet::default());
    for id in tree.deep(root) {
        match tree[id] {
            Node::Ref(v) => *refs.entry(v).or_default() += 1,
            Node::Set(v, _) => _ = assigned.insert(v),
            Node::Let(binds, _) => {
                for &bind in &tree[binds] {
                    if let Bind::Val(v, init) = bind
                        && let Some((kind, _)) = tree.made_struct(mc, init)
                    {
                        made.insert(v, Made { kind, binder: id, uses: Vec::new() });
                    }
                }
            }
            _ => {}
        }
    }
    if made.is_empty() {
        return;
    }
    let found: Vec<(Var, Id<'id>, Use<'id>)> = tree.deep(root).filter_map(|id| Some((id, field_use(mc, tree, &made, id)?))).map(|(id, (v, field))| (v, id, field)).collect();
    for (v, id, field) in found {
        made.get_mut(&v).expect("a struct's variable").uses.push((id, field));
    }
    for (v, struct_made) in made {
        if !assigned.contains(&v) && refs.get(&v).copied().unwrap_or(0) == struct_made.uses.len() {
            fields_for(tree, v, &struct_made, &assigned, supply);
        }
    }
}

/// What `id` does with a field of one of the `made` structs, and the struct's variable, if it
/// reads or sets one in a way that can't fault.
fn field_use<'id, 'gc>(mc: &Mutation<'gc>, tree: &L2<'id, 'gc>, made: &HashMap<Var, Made<'id, 'gc>>, id: Id<'id>) -> Option<(Var, Use<'id>)> {
    let Node::Intrinsic(Prim::Intrinsic(intrinsic), args) = tree[id] else { return None };
    let args = &tree[args];
    let Node::Ref(v) = tree[*args.first()?] else { return None };
    let made_as = made.get(&v)?.kind;
    let constant = |at: usize| match tree[args[at]] {
        Node::Quote(value) => Some(value),
        _ => None,
    };
    let index = |at: usize| usize::try_from(constant(at)?.as_fixnum()?).ok();
    // A field read or set by a type is one of the struct's if the struct is of the type.
    let by_type = |at: usize| {
        let kind = constant(1)?.downcast::<StructType>(mc)?;
        index(at).filter(|&k| structs::derives(mc, made_as, kind) && k < kind.fields(mc) as usize)
    };
    let field = match (intrinsic, args.len()) {
        (Intrinsic::StructField | Intrinsic::StructFixedField, 2) => Use::Read(index(1).filter(|&k| k < made_as.fields(mc) as usize)?),
        (Intrinsic::StructRef, 3) => Use::Read(by_type(2)?),
        (Intrinsic::StructSet, 4) => Use::Write(by_type(2).filter(|&k| structs::is_mutable(mc, made_as, k))?, args[3]),
        _ => return None,
    };
    Some((v, field))
}

/// Makes the struct `v` is bound to into its fields: a variable for each that's set or whose
/// value has to be evaluated, and the value itself for any other.
fn fields_for<'id, 'gc>(tree: &mut L2<'id, 'gc>, v: Var, made: &Made<'id, 'gc>, assigned: &HashSet<Var>, supply: &mut Supply) {
    let Node::Let(binds, body) = tree[made.binder] else { unreachable!("a struct's variable is bound by a let") };
    let mut binds = tree[binds].to_vec();
    let at = binds.iter().position(|bind| matches!(bind, Bind::Val(bound, _) if *bound == v)).expect("the let binds the variable");
    let Bind::Val(_, init) = binds[at] else { unreachable!("found as one") };
    let Node::Intrinsic(_, args) = tree[init] else { unreachable!("a struct is made by an intrinsic") };
    let values = tree[args][1..].to_vec();
    let set: HashSet<usize> = made.uses.iter().filter_map(|&(_, field)| if let Use::Write(k, _) = field { Some(k) } else { None }).collect();
    let (mut bound, mut fields) = (Vec::new(), Vec::with_capacity(values.len()));
    for (k, &value) in values.iter().enumerate() {
        let copyable = match tree[value] {
            Node::Quote(_) => true,
            Node::Ref(u) => !assigned.contains(&u),
            _ => false,
        };
        if copyable && !set.contains(&k) {
            fields.push(tree[value]);
        } else {
            let field = supply.fresh_var();
            bound.push(Bind::Val(field, value));
            fields.push(Node::Ref(field));
        }
    }
    for &(id, field) in &made.uses {
        match field {
            Use::Read(k) => tree.set(id, fields[k]),
            Use::Write(k, value) => {
                let Node::Ref(field) = fields[k] else { unreachable!("a field that's set is a variable") };
                tree.set(id, Node::Set(field, value));
            }
        }
    }
    binds.splice(at..=at, bound);
    let binds = tree.list(binds);
    tree.set(made.binder, Node::Let(binds, body));
}
