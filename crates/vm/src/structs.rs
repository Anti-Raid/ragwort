//! Structs: what `struct` makes. A type is made once for each form that's evaluated, so two are
//! never the same type. A [`Struct`] is of the [`StructType`] it was made as and of each of that
//! type's supertypes. It's written with its fields, and it's `equal?` to another of its type with
//! `equal?` fields, unless its type is an identity one, whose structs are `equal?` only to
//! themselves, as a subtype of one's are too.
//!
//! Code that has a type can ask it its fields' names, and make, tell, read and write structs of it
//! by them: a field is known by where its name is among them, and by nothing else, so a type needn't
//! keep a field no code reads. There's no asking a value what its type is.

use ragwort_types::gc::{Gc, Mutation, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Symbol;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::objects::{Struct, StructFields, StructType, StructTypeFields};

/// The names of a type's fields, as it keeps them, and how many there are: those in the vector
/// `above`, if it's one, then those in the list `own`, each a symbol.
fn field_names<'gc>(mc: &Mutation<'gc>, above: Value<'gc>, own: Value<'gc>) -> Result<(Value<'gc>, u32), Fault> {
    let pairs = Pairs::new(mc);
    pairs.list_len(own).ok_or(Fault::WrongType)?;
    let mut names = ScratchVec::new(mc);
    if let Some(above) = AnyVector::of(above) {
        for i in 0..above.len(mc) {
            names.push(above.get(mc, i).ok_or(Fault::Malformed)?)?;
        }
    }
    for name in pairs.elements(own) {
        Symbol::of(name).ok_or(Fault::WrongType)?;
        names.push(name)?;
    }
    let count = u32::try_from(names.len()).map_err(|_| Fault::OutOfRange)?;
    Ok((Vectors::new(mc).immutable_from_slice(&names)?.value(mc), count))
}

/// A new struct type named by the symbol `name`, whose structs have the fields the list `fields`
/// names after those of its supertype `parent`'s, a struct type, or `#f` for none. It's an
/// identity one if `identity` isn't `#f`, or its supertype is one.
pub fn make_type<'gc>(mc: &Mutation<'gc>, name: Value<'gc>, parent: Value<'gc>, fields: Value<'gc>, identity: Value<'gc>) -> Result<Gc<'gc, StructType>, Fault> {
    Symbol::of(name).ok_or(Fault::WrongType)?;
    let identity = identity != Value::FALSE;
    if parent == Value::FALSE {
        let (names, count) = field_names(mc, Value::FALSE, fields)?;
        return Ok(StructType::new(mc, name, names, count, identity, 0, Value::VOID)?);
    }
    let parent = type_of(mc, parent)?;
    let (names, count) = field_names(mc, parent.names(mc), fields)?;
    let above = parent.items(mc);
    let made = StructType::new(mc, name, names, count, identity || parent.identity(mc), above.len() + 1, Value::object(mc, parent))?;
    let supertypes = made.items(mc);
    (0..above.len()).for_each(|i| supertypes.set(mc, i, above.get(i)));
    Ok(made)
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
