//! Struct types and their instances, which the `struct` form creates.
//!
//! - A [`StructType`] is created once each time a `struct` form is evaluated. Two forms never
//!   share a type, even if they have the same name and fields.
//! - A [`Struct`] is an instance. It belongs to the type it was created with and to every
//!   supertype of that type.
//!
//! # Equality and printing
//!
//! An instance is printed with its fields, as `#(struct:point 1 2)`. Two instances are `equal?`
//! when they have the same type and their fields are `equal?`.
//!
//! An identity type is the exception: its instances are `equal?` only to themselves. A subtype
//! of an identity type is an identity type too.
//!
//! # Fields
//!
//! A type records the names of its fields, its supertype's first, and [`FieldFlags`] for each.
//!
//! - A field's index is the position of its name in that list. Only the code a `struct` form
//!   compiles to uses indexes.
//! - Setting a field that is not mutable faults with [`Fault::Immutable`], whatever code asks.
//!
//! # What code can do with a struct
//!
//! Only the procedures a `struct` form defines make an instance, read one field or set one.
//! The intrinsics they are built from are [internal](crate::Intrinsic::is_internal).
//!
//! A read by `struct-ref` checks that the value is an instance of the type it names. Where a
//! compiler has proved that already, as after `(point? p)`, it reads with `struct-field`, which
//! checks nothing about the type.
//!
//! Any code can look at a struct as a whole, without changing it:
//!
//! - `struct-type` gives the type of an instance.
//! - `struct-fields` gives the names of a type's fields.
//! - `struct->list` gives the values of an instance's fields, in the same order.
//!
//! # Sealed types
//!
//! A sealed type cannot be a supertype: making a subtype of one faults.

use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Gc, Mutation, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Symbol;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::objects::{Struct, StructFields, StructType, StructTypeFields};

bitflags::bitflags! {
    /// What a `struct` form declares of its type.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct TypeFlags: u32 {
        /// Instances are `equal?` only to themselves. A subtype inherits this.
        const IDENTITY = 1;
        /// The type cannot be a supertype.
        const SEALED = 1 << 1;
    }

    /// What a `struct` form declares of a field.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct FieldFlags: u8 {
        /// The field can be set.
        const MUTABLE = 1;
    }
}

/// The flags of `kind`.
pub fn type_flags<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>) -> TypeFlags {
    TypeFlags::from_bits_truncate(kind.flags(mc))
}

/// The flags of field `k` of `kind`, or none if it has no such field.
pub fn field_flags<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>, k: usize) -> FieldFlags {
    flags_at(mc, kind.field_flags(mc), k)
}

/// The flags at place `k` of `bytes`, a type's bytevector of them.
fn flags_at<'gc>(mc: &Mutation<'gc>, bytes: Value<'gc>, k: usize) -> FieldFlags {
    FieldFlags::from_bits_truncate(AnyBytevector::of(bytes).and_then(|flags| flags.get(mc, k)).unwrap_or(0))
}

/// A type's fields as it keeps them: their names, their flags, and how many there are. They are
/// those of its supertype `above`, if it has one, then those the list `own` names, each a
/// symbol, whose flags are the fixnums at the same places in the list `flags`.
fn fields_of<'gc>(mc: &Mutation<'gc>, above: Option<Gc<'gc, StructType>>, own: Value<'gc>, flags: Value<'gc>) -> Result<(Value<'gc>, Value<'gc>, u32), Fault> {
    let pairs = Pairs::new(mc);
    if pairs.list_len(own).is_none() || pairs.list_len(own) != pairs.list_len(flags) {
        return Err(Fault::WrongType);
    }
    let (mut names, mut bits) = (ScratchVec::new(mc), ScratchVec::new(mc));
    if let Some(above) = above {
        let (above_names, above_bits) = (AnyVector::of(above.names(mc)).ok_or(Fault::Malformed)?, AnyBytevector::of(above.field_flags(mc)).ok_or(Fault::Malformed)?);
        for i in 0..above_names.len(mc) {
            names.push(above_names.get(mc, i).ok_or(Fault::Malformed)?)?;
            bits.push(above_bits.get(mc, i).ok_or(Fault::Malformed)?)?;
        }
    }
    for (name, flag) in pairs.elements(own).zip(pairs.elements(flags)) {
        Symbol::of(name).ok_or(Fault::WrongType)?;
        let flag = flag.as_fixnum().and_then(|bits| u8::try_from(bits).ok()).and_then(FieldFlags::from_bits).ok_or(Fault::WrongType)?;
        names.push(name)?;
        bits.push(flag.bits())?;
    }
    let count = u32::try_from(names.len()).map_err(|_| Fault::OutOfRange)?;
    Ok((Vectors::new(mc).immutable_from_slice(&names)?.value(mc), Bytevectors::new(mc).immutable_from_slice(&bits)?.value(mc), count))
}

/// A new struct type.
///
/// - `name`: a symbol.
/// - `parent`: the supertype, a struct type that isn't sealed, or `#f` for none.
/// - `fields`: a list of the names of the fields the type adds after its supertype's.
/// - `field_flags`: a list with the bits of the [`FieldFlags`] of each of `fields`, as fixnums.
/// - `flags`: the bits of the [`TypeFlags`] the form declares, as a fixnum. The type is also an
///   identity type if its supertype is one.
pub fn make_type<'gc>(
    mc: &Mutation<'gc>,
    name: Value<'gc>,
    parent: Value<'gc>,
    fields: Value<'gc>,
    field_flags: Value<'gc>,
    flags: Value<'gc>,
) -> Result<Gc<'gc, StructType>, Fault> {
    Symbol::of(name).ok_or(Fault::WrongType)?;
    let mut flags = flags.as_fixnum().and_then(|bits| u32::try_from(bits).ok()).and_then(TypeFlags::from_bits).ok_or(Fault::WrongType)?;
    let parent = if parent == Value::FALSE { None } else { Some(type_of(mc, parent)?) };
    let above = parent.map_or(TypeFlags::empty(), |parent| type_flags(mc, parent));
    if above.contains(TypeFlags::SEALED) {
        return Err(Fault::WrongType);
    }
    flags |= above & TypeFlags::IDENTITY;
    let (names, field_flags, count) = fields_of(mc, parent, fields, field_flags)?;
    let made = |supertypes: usize, last: Value<'gc>| StructType::new(mc, name, names, field_flags, count, flags.bits(), supertypes, last);
    let Some(parent) = parent else { return Ok(made(0, Value::VOID)?) };
    let above = parent.items(mc);
    let kind = made(above.len() + 1, Value::object(mc, parent))?;
    let supertypes = kind.items(mc);
    (0..above.len()).for_each(|i| supertypes.set(mc, i, above.get(i)));
    Ok(kind)
}

/// Whether field `k` of `kind`, which it has, can be set.
pub fn is_mutable<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>, k: usize) -> bool {
    field_flags(mc, kind, k).contains(FieldFlags::MUTABLE)
}

/// Field `k` of `s`, which has to be an instance of the struct type `kind` with that field, as
/// `struct-ref` reads it.
#[inline]
pub fn field_of<'gc>(mc: &Mutation<'gc>, s: Value<'gc>, kind: Value<'gc>, k: usize) -> Result<Value<'gc>, Fault> {
    let kind = type_of(mc, kind)?;
    let fields = of(mc, s, kind).ok_or(Fault::WrongType)?.items(mc);
    // A struct of the type has at least the type's fields.
    if k >= kind.fields(mc) as usize {
        return Err(Fault::OutOfRange);
    }
    Ok(fields.get(k))
}

/// Field `k` of `s`, a struct of any type with that many fields, as `struct-field` reads it.
#[inline]
pub fn field<'gc>(mc: &Mutation<'gc>, s: Value<'gc>, k: usize) -> Result<Value<'gc>, Fault> {
    let fields = s.downcast::<Struct>(mc).ok_or(Fault::WrongType)?.items(mc);
    if k >= fields.len() {
        return Err(Fault::OutOfRange);
    }
    Ok(fields.get(k))
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

/// Whether `kind` is `from` or a subtype of it.
#[inline]
pub fn derives<'gc>(mc: &Mutation<'gc>, kind: Gc<'gc, StructType>, from: Gc<'gc, StructType>) -> bool {
    if kind == from {
        return true;
    }
    // A subtype has the type among its supertypes, as far in as the type has supertypes itself.
    let (supertypes, depth) = (kind.items(mc), from.items(mc).len());
    depth < supertypes.len() && supertypes.get(depth) == Value::object(mc, from)
}

/// `v` as a struct of `kind` or of a subtype of it, if it's one.
#[inline]
pub fn of<'gc>(mc: &Mutation<'gc>, v: Value<'gc>, kind: Gc<'gc, StructType>) -> Option<Gc<'gc, Struct>> {
    let made = v.downcast::<Struct>(mc)?;
    derives(mc, made.kind(mc)?, kind).then_some(made)
}
