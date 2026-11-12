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
    /// Leaves a dominator subtree, discarding cached reads added after the first `n` entries because
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
fn slots_into(f: &Function<'_, '_>) -> Vec<Option<Slots>> {
    let mut into: Vec<Option<Slots>> = vec![None; f.blocks.len()];
    into[0] = Some(Slots::default());
    let mut todo = vec![0];
    while let Some(b) = todo.pop() {
        let mut slots = into[b].clone().expect("a block that's reached");
        for inst in &f.blocks[b].insts {
            slot_step(&mut slots, inst);
        }
        for to in f.blocks[b].end.successors() {
            let to = to.0 as usize;
            let Some(known) = &mut into[to] else {
                into[to] = Some(slots.clone());
                todo.push(to);
                continue;
            };
            let before = known.len();
            known.retain(|slot, v| slots.get(slot) == Some(v));
            if known.len() != before {
                todo.push(to);
            }
        }
    }
    into
}

fn merge_in<'gc>(mc: &Mutation<'gc>, f: &mut Function<'_, 'gc>) {
    let mut constants: Vec<Option<Value<'gc>>> = vec![None; f.values as usize];
    let mut preds = vec![Vec::new(); f.blocks.len()];
    for (b, block) in f.blocks.iter().enumerate() {
        block.end.successors().for_each(|to| preds[to.0 as usize].push(b));
        for inst in &block.insts {
            if let Inst::Const(dst, value) = inst {
                constants[dst.0 as usize] = Some(*value);
            }
        }
    }
    let Ok(before) = dominators(&f.blocks, &preds) else { return };
    let mut under = vec![Vec::new(); f.blocks.len()];
    for (b, &above) in before.iter().enumerate().skip(1) {
        under[above].push(b);
    }
    let mut slots_into = slots_into(f);
    // Replacement values for eliminated reads and the instructions to remove.
    let mut same: Vec<Option<Val>> = vec![None; f.values as usize];
    let mut merged = Vec::new();
    let of = |same: &[Option<Val>], v: Val| same[v.0 as usize].unwrap_or(v);
    // Maps repeated upvalue loads to the first load of that captured variable.
    let mut loaded: Vec<Option<Val>> = vec![None; f.values as usize];
    let fixnum = |v: Val| constants[v.0 as usize].and_then(|k| k.as_fixnum()).and_then(|k| usize::try_from(k).ok());
    // Caches immutable reads encountered along the current dominator path.
    let (mut fixed, mut noted) = (HashMap::<Fixed, Val>::default(), Vec::new());
    let mut todo = vec![Step::Into(0)];
    while let Some(step) = todo.pop() {
        let b = match step {
            Step::Into(b) => b,
            Step::Out(n) => {
                noted.drain(n..).for_each(|read| _ = fixed.remove(&read));
                continue;
            }
        };
        todo.push(Step::Out(noted.len()));
        todo.extend(under[b].iter().map(|&b| Step::Into(b)));
        let Some(mut slots) = slots_into[b].take() else { continue };
        for (i, inst) in f.blocks[b].insts.iter().enumerate() {
            let (dst, read, checks) = match inst {
                Inst::Upvalue(dst, index) => (*dst, Fixed::Upvalue(*index), false),
                Inst::Prim { dst, prim: Prim::Intrinsic(Intrinsic::StructFixedField), args, spread: false } => {
                    let &[s, k] = args.as_slice() else { continue };
                    let Some(k) = fixnum(k) else { continue };
                    (*dst, Fixed::Field(of(&loaded, of(&same, s)), k), false)
                }
                // A successful typed read identifies the field, but the instruction must remain to perform its type
                // check.
                Inst::Prim { dst, prim: Prim::Intrinsic(Intrinsic::StructRef), args, spread: false } => {
                    let &[s, kind, k] = args.as_slice() else { continue };
                    let kind = constants[kind.0 as usize].and_then(|kind| kind.downcast::<StructType>(mc));
                    let Some((kind, k)) = kind.zip(fixnum(k)) else { continue };
                    if k >= StructTypeFields::fields(kind, mc) as usize || structs::is_mutable(mc, kind, k) {
                        continue;
                    }
                    (*dst, Fixed::Field(of(&loaded, of(&same, s)), k), true)
                }
                other => {
                    if let Some((dst, earlier)) = slot_step(&mut slots, other) {
                        same[dst.0 as usize] = Some(earlier);
                        merged.push((b, i));
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
                merged.push((b, i));
            }
        }
    }
    if merged.is_empty() {
        return;
    }
    merged.sort_unstable();
    for &(b, i) in merged.iter().rev() {
        f.blocks[b].insts.remove(i);
        f.blocks[b].sites.remove(i);
    }
    for block in &mut f.blocks {
        block.insts.iter_mut().for_each(|inst| inst.each_use_mut(|v| *v = of(&same, *v)));
        block.end.each_use_mut(|v| *v = of(&same, *v));
    }
}
