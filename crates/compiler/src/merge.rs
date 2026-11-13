//! Read reuse (`L5 -> L5`): replaces redundant reads with earlier SSA values.
//!
//! Immutable field reads can reuse a dominating read of the same field on the same struct. For
//! example, `(* (point-x p) (point-x p))` needs only one field read.
//!
//! Module-variable loads can reuse an earlier value only when every incoming path provides that
//! value and no intervening operation could assign the variable. Calls, requests, host calls, and
//! stores invalidate the relevant facts. For example, the branch in `(if (point? origin) (point-x
//! origin) 0)` can reuse the test's load of `origin`.
//!
//! Repeated loads of a captured variable identify the same captured value, allowing field-read
//! reuse across those loads. The upvalue loads themselves are not merged: loading costs as much as
//! moving the reused value, and unused loads are omitted during emission.
//!
//! Cached results remain live until their last use, so each cache is limited to [`MOST`] entries to
//! control register pressure.

use ragwort_types::gc::{Mutation, Value};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Intrinsic, structs};

use crate::hash::HashMap;
use crate::l5::{Function, Inst, Program, Val, dominators};
use crate::{Prim, SlotOp};

/// Maximum number of cached reads per category.
const MOST: usize = 32;

/// Reuses eligible reads in every function of `program`.
pub(crate) fn merge<'gc>(mc: &Mutation<'gc>, program: &mut Program<'_, 'gc>) {
    for function in &mut program.functions {
        merge_in(mc, function);
    }
}

/// Identifies a read whose result remains unchanged throughout the function.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Fixed {
    /// A captured upvalue.
    Upvalue(u32),
    /// An immutable struct field.
    Field(Val, usize),
}

/// Known values of module slots, valid until an operation may assign those slots.
type Slots = HashMap<u32, Val>;

/// A task in the dominator-tree traversal.
enum Step {
    Into(usize),
    /// Leaves a dominator subtree, discarding cached reads added after the first `count` entries because
    /// they do not dominate subsequent sibling subtrees.
    Out(usize),
}

/// Updates `slots` for `inst`. For a reusable load, returns the load's result and its earlier
/// equivalent value.
fn slot_step(slots: &mut Slots, inst: &Inst<'_, '_>) -> Option<(Val, Val)> {
    match inst {
        Inst::Call { .. } | Inst::Prim { prim: Prim::Request(_) | Prim::Host(_), .. } => slots.clear(),
        Inst::Prim { prim: Prim::Slot(SlotOp::Store | SlotOp::StoreChecked, slot), .. } => _ = slots.remove(slot),
        Inst::Prim { dst, prim: Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, slot), .. } => {
            if let Some(&earlier) = slots.get(slot) {
                return Some((*dst, earlier));
            }
            if slots.len() < MOST {
                slots.insert(*slot, *dst);
            }
        }
        _ => {}
    }
    None
}

/// Computes available module-slot values at each block's entry by intersecting predecessor facts.
/// Unreachable blocks have no entry state. After initialization, entry states only lose facts,
/// ensuring convergence.
fn slots_into(function: &Function<'_, '_>) -> Vec<Option<Slots>> {
    let mut into: Vec<Option<Slots>> = vec![None; function.blocks.len()];
    into[0] = Some(Slots::default());
    let mut todo = vec![0];
    while let Some(block) = todo.pop() {
        let mut slots = into[block].clone().expect("a block that's reached");
        for inst in &function.blocks[block].insts {
            slot_step(&mut slots, inst);
        }
        for to in function.blocks[block].end.successors() {
            let to = to.0 as usize;
            let Some(known) = &mut into[to] else {
                into[to] = Some(slots.clone());
                todo.push(to);
                continue;
            };
            let before = known.len();
            known.retain(|slot, value| slots.get(slot) == Some(value));
            if known.len() != before {
                todo.push(to);
            }
        }
    }
    into
}

fn merge_in<'gc>(mc: &Mutation<'gc>, function: &mut Function<'_, 'gc>) {
    let mut constants: Vec<Option<Value<'gc>>> = vec![None; function.values as usize];
    let mut preds = vec![Vec::new(); function.blocks.len()];
    for (index, block) in function.blocks.iter().enumerate() {
        block.end.successors().for_each(|to| preds[to.0 as usize].push(index));
        for inst in &block.insts {
            if let Inst::Const(dst, value) = inst {
                constants[dst.0 as usize] = Some(*value);
            }
        }
    }
    let Ok(before) = dominators(&function.blocks, &preds) else { return };
    let mut under = vec![Vec::new(); function.blocks.len()];
    for (block, &above) in before.iter().enumerate().skip(1) {
        under[above].push(block);
    }
    let mut slots_into = slots_into(function);
    // Replacement values for eliminated reads and the instructions to remove.
    let mut same: Vec<Option<Val>> = vec![None; function.values as usize];
    let mut merged = Vec::new();
    let of = |same: &[Option<Val>], value: Val| same[value.0 as usize].unwrap_or(value);
    // Maps repeated upvalue loads to the first load of that captured variable.
    let mut loaded: Vec<Option<Val>> = vec![None; function.values as usize];
    let fixnum = |value: Val| constants[value.0 as usize].and_then(|constant| constant.as_fixnum()).and_then(|number| usize::try_from(number).ok());
    // Caches immutable reads encountered along the current dominator path.
    let (mut fixed, mut noted) = (HashMap::<Fixed, Val>::default(), Vec::new());
    let mut todo = vec![Step::Into(0)];
    while let Some(step) = todo.pop() {
        let block = match step {
            Step::Into(block) => block,
            Step::Out(count) => {
                noted.drain(count..).for_each(|read| _ = fixed.remove(&read));
                continue;
            }
        };
        todo.push(Step::Out(noted.len()));
        todo.extend(under[block].iter().map(|&child| Step::Into(child)));
        let Some(mut slots) = slots_into[block].take() else { continue };
        for (i, inst) in function.blocks[block].insts.iter().enumerate() {
            let (dst, read, checks) = match inst {
                Inst::Upvalue(dst, index) => (*dst, Fixed::Upvalue(*index), false),
                Inst::Prim { dst, prim: Prim::Intrinsic(Intrinsic::StructFixedField), args, spread: false } => {
                    let &[object, field] = args.as_slice() else { continue };
                    let Some(field) = fixnum(field) else { continue };
                    (*dst, Fixed::Field(of(&loaded, of(&same, object)), field), false)
                }
                // A successful typed read identifies the field, but the instruction must remain to perform its type
                // check.
                Inst::Prim { dst, prim: Prim::Intrinsic(Intrinsic::StructRef), args, spread: false } => {
                    let &[object, kind, field] = args.as_slice() else { continue };
                    let kind = constants[kind.0 as usize].and_then(|kind| kind.downcast::<StructType>(mc));
                    let Some((kind, field)) = kind.zip(fixnum(field)) else { continue };
                    if field >= StructTypeFields::fields(kind, mc) as usize || structs::is_mutable(mc, kind, field) {
                        continue;
                    }
                    (*dst, Fixed::Field(of(&loaded, of(&same, object)), field), true)
                }
                other => {
                    if let Some((dst, earlier)) = slot_step(&mut slots, other) {
                        same[dst.0 as usize] = Some(earlier);
                        merged.push((block, i));
                    }
                    continue;
                }
            };
            let Some(&earlier) = fixed.get(&read) else {
                if fixed.len() < MOST {
                    fixed.insert(read, dst);
                    noted.push(read);
                }
                continue;
            };
            if let Fixed::Upvalue(_) = read {
                loaded[dst.0 as usize] = Some(earlier);
            } else if !checks {
                same[dst.0 as usize] = Some(earlier);
                merged.push((block, i));
            }
        }
    }
    if merged.is_empty() {
        return;
    }
    merged.sort_unstable();
    for &(block, i) in merged.iter().rev() {
        function.blocks[block].insts.remove(i);
        function.blocks[block].sites.remove(i);
    }
    for block in &mut function.blocks {
        block.insts.iter_mut().for_each(|inst| inst.each_use_mut(|value| *value = of(&same, *value)));
        block.end.each_use_mut(|value| *value = of(&same, *value));
    }
}
