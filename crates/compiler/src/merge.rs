//! Pass 8b (`L5 -> L5`): a read that gives what an earlier one gave is that one's value.
//!
//! Two kinds of read are merged:
//!
//! - A field that can't be set, of the same struct. `(* (point-x p) (point-x p))` reads the
//!   field once.
//! - A variable of the module, read again with nothing between the reads that could assign
//!   it: a call, a request, a host call or a store. `(+ (point-x origin) (point-y origin))`
//!   loads `origin` once.
//!
//! # Which earlier read
//!
//! - For a field, one the code always runs before the later read, whatever is between them.
//! - For a variable of the module, one that every way to the later read goes through, with
//!   nothing after it that could assign the variable. In
//!   `(if (point? origin) (point-x origin) 0)` the branch reads what the test loaded.
//!
//! # Captured variables
//!
//! A variable the closure captured is the same for as long as the function runs, so two
//! loads of it give one struct, and a field of it read twice is read once: in
//! `(lambda () (* (point-x p) (point-x p)))`, where each `p` is a load. The loads themselves
//! aren't merged. A load costs what moving the value to where it's used would, and one
//! that's left with no use isn't emitted.
//!
//! A value read earlier is kept in a register till its last use, so at most [`MOST`] of each
//! kind are kept at once.

use ragwort_types::gc::{Mutation, Value};
use ragwort_vm::objects::{StructType, StructTypeFields};
use ragwort_vm::{Intrinsic, structs};

use crate::hash::HashMap;
use crate::l5::{Function, Inst, Program, Val, dominators};
use crate::{Prim, SlotOp};

/// How many earlier reads of a kind later ones are merged with at once.
const MOST: usize = 32;

/// Merges the reads of each of `program`'s functions.
pub(crate) fn merge<'gc>(mc: &Mutation<'gc>, program: &mut Program<'_, 'gc>) {
    for function in &mut program.functions {
        merge_in(mc, function);
    }
}

/// A read that gives the same value however often the function makes it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Fixed {
    /// A variable the closure captured.
    Upvalue(u32),
    /// A field that can't be set, of a struct.
    Field(Val, usize),
}

/// The value of each of the module's variables that's been read, with nothing since that could
/// have assigned it.
type Slots = HashMap<u32, Val>;

/// A step of the walk down the tree of which block runs before which.
enum Step {
    Into(usize),
    /// Out of a block: the reads made in it and the blocks under it, past the first `n` noted,
    /// aren't made on the way to what's next.
    Out(usize),
}

/// What `inst` does to `slots`. A read of a variable that's there is the value there, which
/// this gives after the read's own.
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

/// The [`Slots`] each block starts with: what every way to it ends with. A block no code gets
/// to has none.
///
/// A block's are only ever taken from, each time a way to it turns out to end with less, so
/// this ends.
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
    // What each value merged away is the same as, and the instructions that made them.
    let mut same: Vec<Option<Val>> = vec![None; f.values as usize];
    let mut merged = Vec::new();
    let of = |same: &[Option<Val>], v: Val| same[v.0 as usize].unwrap_or(v);
    // The first load of the captured variable that each later load of it is a load of.
    let mut loaded: Vec<Option<Val>> = vec![None; f.values as usize];
    let fixnum = |v: Val| constants[v.0 as usize].and_then(|k| k.as_fixnum()).and_then(|k| usize::try_from(k).ok());
    // The value of each read that can't change, made in the blocks from the first to this one.
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
                // A read by a type that didn't fault read a field of the type: and it checks
                // the type too, so it's still made.
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
    }
    for block in &mut f.blocks {
        block.insts.iter_mut().for_each(|inst| inst.each_use_mut(|v| *v = of(&same, *v)));
        block.end.each_use_mut(|v| *v = of(&same, *v));
    }
}
