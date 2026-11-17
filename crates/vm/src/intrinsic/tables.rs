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
            Intrinsic::TableRef | Intrinsic::TableSet | Intrinsic::TableDelete | Intrinsic::TableHas => {
                let table = table_of(operands.get(0))?;
                let key = operands.get(1);
                charge(mc, table, key, fuel)?;
                let result = match self {
                    Intrinsic::TableRef => table.get(mc, key)?.unwrap_or(operands.get(2)),
                    Intrinsic::TableSet => {
                        table.set(mc, key, operands.get(2))?;
                        Value::VOID
                    }
                    Intrinsic::TableDelete => boolean(table.delete(mc, key)?),
                    _ => boolean(table.has(mc, key)?),
                };
                // Each of these operations can allocate. A table rebuilds a stale index, and an external table caches the values it reads from its host.
                made(mc, fuel, result)
            }
            Intrinsic::TableLength => Value::fixnum(table_of(operands.get(0))?.len(mc) as i64).expect("lengths are fixnums"),
            Intrinsic::TableClear => {
                table_of(operands.get(0))?.clear(mc)?;
                Value::VOID
            }
            Intrinsic::TableToVector => {
                let table = table_of(operands.get(0))?;
                fuel.spend(table.len(mc) as u64 / equal::PER_FUEL)?;
                let entries = table.entries(mc)?;
                // The host of an external table can list fewer entries than the table's length, so the listed entries are counted.
                let count = if table.is_external() { entries.count() } else { table.len(mc) };
                let vector = Vectors::new(mc).make(2 * count, Value::VOID)?;
                let items = vector.items(mc);
                for (position, (key, value)) in entries.take(count).enumerate() {
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

/// Spends the fuel that a lookup of `key` in `table` costs beyond one step. Hashing and comparing
/// a string key reads all its characters. A table with a stale index rebuilds the index first,
/// in time proportional to the number of entries.
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
