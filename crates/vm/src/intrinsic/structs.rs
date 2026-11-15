//! Struct intrinsics.

use ragwort_types::gc::{Mutation, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::vector::AnyVector;

use crate::op::Fuel;
use crate::{Fault, equal};
use crate::objects::{self, StructFields, StructTypeFields};

use super::{Intrinsic, Operands, boolean, index, made};

impl Intrinsic {
    /// Evaluates a struct-related intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn structs<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MakeStructType => made(mc, fuel, Value::object(mc, crate::structs::make_type(mc, operands.get(0), operands.get(1), operands.get(2), operands.get(3), operands.get(4))?)),
            Intrinsic::MakeStruct if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::MakeStruct => {
                let kind = crate::structs::type_of(mc, operands.get(0))?;
                made(mc, fuel, Value::object(mc, crate::structs::make(mc, kind, operands.from(1))?))
            }
            Intrinsic::StructFields => {
                let names = AnyVector::of(crate::structs::type_of(mc, operands.get(0))?.names(mc)).ok_or(Fault::Malformed)?;
                fuel.spend(names.len(mc) as u64 / equal::PER_FUEL)?;
                let mut listed = ScratchVec::new(mc);
                for i in 0..names.len(mc) {
                    listed.push(names.get(mc, i).ok_or(Fault::Malformed)?)?;
                }
                made(mc, fuel, Pairs::new(mc).list(&listed)?)
            }
            Intrinsic::IsStruct => boolean(operands.get(0).downcast::<objects::Struct>(mc).is_some()),
            Intrinsic::IsStructType => boolean(operands.get(0).downcast::<objects::StructType>(mc).is_some()),
            Intrinsic::IsStructFieldMutable => {
                let kind = crate::structs::type_of(mc, operands.get(0))?;
                let field = index(operands.get(1))?;
                if field >= kind.fields(mc) as usize {
                    return Err(Fault::OutOfRange);
                }
                boolean(crate::structs::is_mutable(mc, kind, field))
            }
            Intrinsic::StructType => {
                let made_as = operands.get(0).downcast::<objects::Struct>(mc).and_then(|instance| instance.kind(mc)).ok_or(Fault::WrongType)?;
                Value::object(mc, made_as)
            }
            Intrinsic::StructToList => {
                let fields = operands.get(0).downcast::<objects::Struct>(mc).ok_or(Fault::WrongType)?.items(mc);
                fuel.spend(fields.len() as u64 / equal::PER_FUEL)?;
                let mut listed = ScratchVec::new(mc);
                for i in 0..fields.len() {
                    listed.push(fields.get(i))?;
                }
                made(mc, fuel, Pairs::new(mc).list(&listed)?)
            }
            Intrinsic::StructSet => {
                let kind = crate::structs::type_of(mc, operands.get(1))?;
                let fields = crate::structs::of(mc, operands.get(0), kind).ok_or(Fault::WrongType)?.items(mc);
                // An instance of this struct type is guaranteed to have allocated at least as
                // many fields as specified by the type descriptor.
                let field = index(operands.get(2))?;
                if field >= kind.fields(mc) as usize {
                    return Err(Fault::OutOfRange);
                }
                if !crate::structs::is_mutable(mc, kind, field) {
                    return Err(Fault::Immutable);
                }
                fields.set(mc, field, operands.get(3));
                Value::VOID
            }
            _ => unreachable!("{self:?} isn't a struct procedure"),
        })
    }
}
