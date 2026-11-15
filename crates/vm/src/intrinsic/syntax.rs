//! Syntax-object intrinsics.

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::syntax::Syntax;

use crate::op::Fuel;
use crate::Fault;

use super::{Intrinsic, Operands, boolean, made};

impl Intrinsic {
    /// Evaluates a syntax-object intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn syntax<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::IsSyntax => boolean(Syntax::of(operands.get(0)).is_some()),
            Intrinsic::IsIdentifier => boolean(crate::syntax::is_identifier(mc, operands.get(0))),
            Intrinsic::SyntaxE => crate::syntax::unwrap(mc, operands.get(0))?,
            Intrinsic::SyntaxToDatum => crate::syntax::to_datum(mc, operands.get(0), fuel)?,
            Intrinsic::DatumToSyntax => {
                let syntax = crate::syntax::to_syntax(mc, operands.get(0), operands.get(1), fuel)?;
                made(mc, fuel, syntax)
            }
            Intrinsic::BoundIdentifierEq => boolean(crate::syntax::same_identifier(mc, operands.get(0), operands.get(1), fuel)?),
            Intrinsic::FreeIdentifierEq => boolean(crate::syntax::same_binding(mc, operands.get(0), operands.get(1))?),
            Intrinsic::SyntaxMatch => {
                let matched = crate::syntax_case::matched(mc, operands.get(0), operands.get(1), fuel)?;
                made(mc, fuel, matched)
            }
            Intrinsic::SyntaxBuild if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::SyntaxBuild => {
                let values: Vec<_> = operands.from(1).collect();
                let built = crate::syntax_case::build(mc, operands.get(0), &values, fuel)?;
                made(mc, fuel, built)
            }
            Intrinsic::GenerateTemporaries => {
                let temporaries = crate::syntax::temporaries(mc, operands.get(0), operands.get(1), fuel)?;
                made(mc, fuel, temporaries)
            }
            _ => unreachable!("{self:?} isn't a syntax procedure"),
        })
    }
}
