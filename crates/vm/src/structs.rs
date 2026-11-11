//! Structs: what `struct` makes. A type is made once for each form that's evaluated, so two are
//! never the same type. A [`Struct`] is of the [`StructType`] it was made as and of each of that
//! type's supertypes. It's written with its fields, and it's `equal?` to another of its type with
//! `equal?` fields, unless its type is an identity one, whose structs are `equal?` only to
//! themselves, as a subtype of one's are too.
//!
//! Code that has a type can ask it its fields' names, and make, tell, read and write structs of it
//! by them: a field is known by where its name is among them, and by nothing else, so a type needn't
//! keep a field no code reads. There's no asking a value what its type is.
//!
//! A field can be set only if its type says so when it's made: one that can't keeps the value it
//! was made with, whatever code has the type.

use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Gc, Mutation, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Symbol;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::objects::{Struct, StructFields, StructType, StructTypeFields};

/// A type's fields as it keeps them: their names, which of them can be set, and how many there
/// are. They're those of its supertype `above`, if it has one, then those the list `own` names,
/// each a symbol, which can be set if what's at its place in the list `mutable` isn't `#f`.
fn fields_of<'gc>(mc: &Mutation<'gc>, above: Option<Gc<'gc, StructType>>, own: Value<'gc>, mutable: Value<'gc>) -> Result<(Value<'gc>, Value<'gc>, u32), Fault> {
    let pairs = Pairs::new(mc);
    if pairs.list_len(own).is_none() || pairs.list_len(own) != pairs.list_len(mutable) {
        return Err(Fault::WrongType);
    }
    let (mut names, mut flags) = (ScratchVec::new(mc), ScratchVec::new(mc));
    if let Some(above) = above {
        let (above_names, above_flags) = (AnyVector::of(above.names(mc)).ok_or(Fault::Malformed)?, AnyBytevector::of(above.mutable(mc)).ok_or(Fault::Malformed)?);
        for i in 0..above_names.len(mc) {
            names.push(above_names.get(mc, i).ok_or(Fault::Malformed)?)?;
            flags.push(above_flags.get(mc, i).ok_or(Fault::Malformed)?)?;
        }
    }
    for (name, flag) in pairs.elements(own).zip(pairs.elements(mutable)) {
        Symbol::of(name).ok_or(Fault::WrongType)?;
        names.push(name)?;
        flags.push(u8::from(flag != Value::FALSE))?;
    }
    let count = u32::try_from(names.len()).map_err(|_| Fault::OutOfRange)?;
    Ok((Vectors::new(mc).immutable_from_slice(&names)?.value(mc), Bytevectors::new(mc).immutable_from_slice(&flags)?.value(mc), count))
}

/// A new struct type named by the symbol `name`, whose structs have the fields the list `fields`
/// names after those of its supertype `parent`'s, a struct type, or `#f` for none. Each of
/// `fields` can be set if what's at its place in the list `mutable` isn't `#f`. The type is an
/// identity one if `identity` isn't `#f`, or its supertype is one.
pub fn make_type<'gc>(mc: &Mutation<'gc>, name: Value<'gc>, parent: Value<'gc>, fields: Value<'gc>, mutable: Value<'gc>, identity: Value<'gc>) -> Result<Gc<'gc, StructType>, Fault> {
    Symbol::of(name).ok_or(Fault::WrongType)?;
    let identity = identity != Value::FALSE;
    if parent == Value::FALSE {
        let (names, mutable, count) = fields_of(mc, None, fields, mutable)?;
        return Ok(StructType::new(mc, name, names, mutable, count, identity, 0, Value::VOID)?);
    }
    let parent = type_of(mc, parent)?;
    let (names, mutable, count) = fields_of(mc, Some(parent), fields, mutable)?;
    let above = parent.items(mc);
    let made = StructType::new(mc, name, names, mutable, count, identity || parent.identity(mc), above.len() + 1, Value::object(mc, parent))?;
    let supertypes = made.items(mc);
    (0..above.len()).for_each(|i| supertypes.set(mc, i, above.get(i)));
    Ok(made)
}

/// Whether field `k` of `kind`, which it has, can be set.
pub fn is_mutable<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>, k: usize) -> bool {
    AnyBytevector::of(kind.mutable(mc)).and_then(|flags| flags.get(mc, k)) == Some(1)
}

/// `v` as a struct type, which it must be.
pub fn type_of<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Result<Gc<'gc, StructType>, Fault> {
    v.downcast::<StructType>(mc).ok_or(Fault::WrongType)
}

/// A struct of `kind`, with `fields` as its fields, as many as the type has.
pub fn make<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>, fields: impl ExactSizeIterator<Item = Value<'gc>>) -> Result<Gc<'gc, Struct>, Fault> {
    if fields.len() != kind.fields(mc) as usize {
        return Err(Fault::Arity);
    }
    let made = Struct::new(mc, Some(kind), fields.len(), Value::VOID)?;
    let items = made.items(mc);
    fields.enumerate().for_each(|(i, field)| items.set(mc, i, field));
    Ok(made)
}

/// `v` as a struct of `kind` or of a subtype of it, if it's one.
#[inline]
pub fn of<'gc>(mc: &Mutation<'gc>, v: Value<'gc>, kind: Gc<'gc, StructType>) -> Option<Gc<'gc, Struct>> {
    let made = v.downcast::<Struct>(mc)?;
    let made_as = made.kind(mc)?;
    if made_as == kind {
        return Some(made);
    }
    // A subtype has the type among its supertypes, as far in as the type has supertypes itself.
    let (supertypes, depth) = (made_as.items(mc), kind.items(mc).len());
    (depth < supertypes.len() && supertypes.get(depth) == Value::object(mc, kind)).then_some(made)
}
