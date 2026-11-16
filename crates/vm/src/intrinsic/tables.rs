//! Table intrinsics.

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::string::{self, Strings};
use ragwort_types::table::{Table, Tables};
use ragwort_types::vector::Vectors;

use crate::op::Fuel;
use crate::{Fault, equal};

use super::{Intrinsic, Operands, boolean, index, made};

impl Intrinsic {
    /// Evaluates a table intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn table<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MakeTable => {
                let room = match operands.count() {
                    0 => 0,
                    1 => index(operands.get(0))?,
                    _ => return Err(Fault::Arity),
                };
                made(mc, fuel, Tables::new(mc).with_room(room)?.value(mc))
            }
            Intrinsic::MakeTableOf => {
                let count = operands.count();
                if count % 2 != 0 {
                    return Err(Fault::Arity);
                }
                fuel.spend(count as u64 / equal::PER_FUEL)?;
                let table = Tables::new(mc).with_room(count / 2)?;
                for position in (0..count).step_by(2) {
                    let key = operands.get(position);
                    charge(mc, table, key, fuel)?;
                    table.set(mc, key, operands.get(position + 1))?;
                }
                made(mc, fuel, table.value(mc))
            }
            Intrinsic::TableRef => {
                let (table, key) = (table_of(operands.get(0))?, operands.get(1));
                charge(mc, table, key, fuel)?;
                table.get(mc, key)?.unwrap_or(operands.get(2))
            }
            Intrinsic::TableSet => {
                let (table, key) = (table_of(operands.get(0))?, operands.get(1));
                charge(mc, table, key, fuel)?;
                table.set(mc, key, operands.get(2))?;
                made(mc, fuel, Value::VOID)
            }
            Intrinsic::TableDelete => {
                let (table, key) = (table_of(operands.get(0))?, operands.get(1));
                charge(mc, table, key, fuel)?;
                boolean(table.delete(mc, key)?)
            }
            Intrinsic::TableHas => {
                let (table, key) = (table_of(operands.get(0))?, operands.get(1));
                charge(mc, table, key, fuel)?;
                boolean(table.has(mc, key)?)
            }
            Intrinsic::TableLength => Value::fixnum(table_of(operands.get(0))?.len(mc) as i64).expect("lengths are fixnums"),
            Intrinsic::TableClear => {
                table_of(operands.get(0))?.clear(mc)?;
                Value::VOID
            }
            Intrinsic::TableToVector => {
                let table = table_of(operands.get(0))?;
                fuel.spend(table.len(mc) as u64 / equal::PER_FUEL)?;
                // An external table reads its entries from the host here, so they are counted as they come.
                let entries = table.entries(mc)?;
                let vector = Vectors::new(mc).make(2 * entries.count(), Value::VOID)?;
                let items = vector.items(mc);
                for (position, (key, value)) in entries.enumerate() {
                    items.set(mc, 2 * position, key);
                    items.set(mc, 2 * position + 1, value);
                }
                made(mc, fuel, vector.value(mc))
            }
            _ => unreachable!("{self:?} isn't a table procedure"),
        })
    }
}

fn table_of(value: Value<'_>) -> Result<Table<'_>, Fault> {
    Table::of(value).ok_or(Fault::WrongType)
}

/// Spends the fuel that finding `key` in `table` is worth beyond one step. A string key is
/// hashed and compared by all its characters. A table that has to make its index again does
/// so in time proportional to its entries.
fn charge<'gc>(mc: &Mutation<'gc>, table: Table<'gc>, key: Value<'gc>, fuel: &mut Fuel) -> Result<(), Fault> {
    let strings = Strings::new(mc);
    if let Some(text) = strings.string(key) {
        fuel.spend(string::len(&strings, text) as u64 / equal::PER_FUEL)?;
    }
    if table.is_stale(mc) {
        fuel.spend(table.len(mc) as u64 / equal::PER_FUEL)?;
    }
    Ok(())
}
