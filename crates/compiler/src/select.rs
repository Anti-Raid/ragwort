//! Pass 8 (`L5 -> L6`): instruction selection and block layout.
//!
//! Chooses the VM instruction that each operation of an [`L5`](crate::l5) function is emitted as, and
//! the order its blocks are emitted in. The result is an [`L6`](crate::l6) function. No registers are
//! assigned here.
//!
//! The choices, each made from the constant arguments and the uses of an instruction:
//!
//! - **Immediate operands.** `(+ x 1)` and struct field reads with a constant index take the constant
//!   inside the instruction. The constant is then no longer read.
//! - **Table hints.** A `table-ref` or `table-set!` with a constant key gets a hint number.
//! - **Fused tests.** A test of one or two arguments whose only use is the branch at the end of its
//!   block becomes [`l6::End::BranchPrim`]. A fused branch reaches only a nearby target, so the caller
//!   turns fusing off with `near` when a function is too long for it.
//! - **Fused returns.** An intrinsic whose only use is the return at the end of its block becomes
//!   [`l6::End::ReturnPrim`].
//! - **Block order.** Blocks that only jump on are skipped, and the rest are ordered so that the
//!   likely next block follows without a jump.

#[cfg(test)]
#[path = "tests/l6.rs"]
mod tests;

use ragwort_alloc::{Arena, CollectIn, Vec as AVec};
use ragwort_types::gc::Value;
use ragwort_types::symbol::Symbol;
use ragwort_vm::Intrinsic;
use ragwort_vm::frame::MAX_PARAMS;

use crate::l5::{self, Val};
use crate::l6::{self, End, Inst, Kind};
use crate::Prim;

/// Selects the instructions of `function`. Tests are fused into branches only if `near` is true.
pub(crate) fn select<'t, 'gc>(arena: &'t Arena, function: &'t l5::Function<'t, 'gc>, near: bool) -> l6::Function<'t, 'gc> {
    let count = function.blocks.len();
    let values = function.values as usize;
    // When the parameters outnumber the argument registers, the last register holds the surplus arguments as a list.
    let total = function.params.len() + usize::from(function.rest.is_some());
    let unpacked = if total <= usize::from(MAX_PARAMS) { &[][..] } else { &function.params[usize::from(MAX_PARAMS - 1)..] };
    let Operands { imms, hinted } = operands(arena, function);
    let mut uses = arena.vec_of(0u32, values);
    for block in &function.blocks {
        for inst in &block.insts {
            count_reads(&mut uses, inst, &imms);
        }
        block.end.each_use(|value| uses[value.0 as usize] += 1);
    }
    let returned: AVec<'_, bool> = function.blocks.iter().map(|block| fused_return(block, &uses, &imms, &hinted)).collect_in(arena);
    let fusable: AVec<'_, bool> = function.blocks.iter().map(|block| near && fused_test(block, &uses, &imms)).collect_in(arena);
    // The value that held the result of a fused instruction no longer exists, so the branch or return no longer reads it.
    for (index, block) in function.blocks.iter().enumerate() {
        if (returned[index] || fusable[index])
            && let Some(fused) = block.insts.last()
        {
            fused.defs().iter().for_each(|def| uses[def.0 as usize] = 0);
        }
    }
    let to = forwards(arena, function);
    let (order, inverted) = layout(arena, function, &to, &fusable);
    // Hints are numbered in the order their instructions are emitted. A function has room for 65,535 hints. A table instruction past that gets none.
    let mut hint_of = arena.vec_of(None, values);
    let mut hints: u16 = 0;
    for &index in order.iter() {
        for inst in &function.blocks[index].insts {
            if let l5::Inst::Prim { dst, .. } = inst
                && hinted[dst.0 as usize]
                && hints < u16::MAX
            {
                hint_of[dst.0 as usize] = Some(hints);
                hints += 1;
            }
        }
    }
    let mut blocks = AVec::with_capacity_in(count, arena);
    for (index, block) in function.blocks.iter().enumerate() {
        let fused = returned[index] || fusable[index];
        let kept = block.insts.len() - usize::from(fused);
        let mut insts = AVec::with_capacity_in(kept, arena);
        for (inst, &site) in block.insts[..kept].iter().zip(&block.sites) {
            insts.push(selected(inst, site, &imms, &hint_of));
        }
        let end = match (block.insts.last(), &block.end) {
            (Some(l5::Inst::Prim { prim, args, spread, .. }), l5::End::Return(_)) if returned[index] => End::ReturnPrim { prim: *prim, args, spread: *spread },
            (Some(l5::Inst::Prim { prim: Prim::Intrinsic(intrinsic), args, .. }), l5::End::Branch { then, other, .. }) if fusable[index] => {
                End::BranchPrim { intrinsic: *intrinsic, args, then: *then, other: *other, branch_if: inverted[index] }
            }
            (_, l5::End::Jump(target, args)) => End::Jump(*target, args),
            (_, l5::End::Branch { test, then, other }) => End::Branch { test: *test, then: *then, other: *other },
            (_, l5::End::Return(value)) => End::Return(*value),
            (_, l5::End::TailCall { f: callee, args }) => End::TailCall { f: *callee, args },
            (_, l5::End::TailPrim { prim, args, spread }) => End::TailPrim { prim: *prim, args, spread: *spread },
        };
        // An instruction fused into the end of the block keeps its own site.
        let end_site = if fused { block.sites[kept] } else { block.end_site };
        blocks.push(l6::BlockData { insts, end, end_site });
    }
    l6::Function { source: function, blocks, unpacked, uses, to, order, hints }
}

/// Returns the L6 form of `inst`.
fn selected<'t, 'gc>(inst: &'t l5::Inst<'t, 'gc>, site: u32, imms: &[Option<Imm<'gc>>], hint_of: &[Option<u16>]) -> Inst<'t, 'gc> {
    let defs = inst.defs();
    let (kind, head, args) = match inst {
        l5::Inst::Const(_, value) => (Kind::Const(*value), None, &[][..]),
        l5::Inst::Upvalue(_, index) => (Kind::Upvalue(*index), None, &[][..]),
        l5::Inst::Prim { prim: Prim::Slot(op, slot), args, .. } => (Kind::Slot(*op, *slot), None, args.as_slice()),
        l5::Inst::Prim { dst, prim, args, spread } => match (imms[dst.0 as usize], hint_of[dst.0 as usize], prim) {
            // An instruction with an immediate operand reads only its first argument.
            (Some(Imm::Add(addend)), _, _) => (Kind::AddImm(addend), None, &args[..1]),
            (Some(Imm::Field(field)), _, _) => (Kind::Field(field), None, &args[..1]),
            (Some(Imm::FieldOf(kind, field)), _, _) => (Kind::FieldOf(kind, field), None, &args[..1]),
            (None, Some(hint), Prim::Intrinsic(Intrinsic::TableRef)) => (Kind::TableRef(hint), None, args.as_slice()),
            (None, Some(hint), _) => (Kind::TableSet(hint), None, args.as_slice()),
            (None, None, _) => (Kind::Prim { prim: *prim, spread: *spread }, None, args.as_slice()),
        },
        l5::Inst::Call { f: callee, args, .. } => (Kind::Call, Some(*callee), args.as_slice()),
        l5::Inst::Closures { codes, .. } => (Kind::Closures(codes), None, &[][..]),
    };
    Inst { kind, defs, head, args, site }
}

/// An immediate constant that an instruction takes in place of an argument register.
#[derive(Clone, Copy)]
enum Imm<'gc> {
    /// The addend of `(+ a k)`.
    Add(i16),
    /// The field index of `(struct-field s k)` or `(struct-fixed-field s k)`.
    Field(u16),
    /// The struct type and the field index of `(struct-ref s type k)`.
    FieldOf(Value<'gc>, u8),
}

/// What `select` derives from the constant arguments of each instruction, indexed by the value that the instruction defines.
struct Operands<'t, 'gc> {
    /// The immediate operand of each instruction, or `None` for an instruction without one.
    imms: AVec<'t, Option<Imm<'gc>>>,
    /// Marks each `table-ref` and `table-set!` whose key is a constant that compares by its value word: a symbol, or a value that needs no object, such as a fixnum or a short string.
    /// Such an instruction is emitted with a hint of where it last found its key. See `Op::TableRefHinted`.
    hinted: AVec<'t, bool>,
}

fn operands<'t, 'gc: 't>(arena: &'t Arena, function: &l5::Function<'_, 'gc>) -> Operands<'t, 'gc> {
    fn fixnum(constants: &[Option<Value<'_>>], value: &Val) -> Option<i64> {
        constants[value.0 as usize].and_then(|constant| constant.as_fixnum())
    }
    let mut constants: AVec<'t, Option<Value<'gc>>> = arena.vec_of(None, function.values as usize);
    let mut imms = arena.vec_of(None, function.values as usize);
    let mut hinted = arena.vec_of(false, function.values as usize);
    for inst in function.blocks.iter().flat_map(|block| &block.insts) {
        match inst {
            l5::Inst::Const(dst, value) => constants[dst.0 as usize] = Some(*value),
            l5::Inst::Prim { dst, prim: Prim::Intrinsic(intrinsic), args, spread: false } => {
                imms[dst.0 as usize] = match (intrinsic, args.as_slice()) {
                    (Intrinsic::Add, [_, addend]) => fixnum(&constants, addend).and_then(|number| i16::try_from(number).ok()).map(Imm::Add),
                    (Intrinsic::StructField | Intrinsic::StructFixedField, [_, field]) => fixnum(&constants, field).and_then(|number| u16::try_from(number).ok()).map(Imm::Field),
                    (Intrinsic::StructRef, [_, kind, field]) => constants[kind.0 as usize].zip(fixnum(&constants, field).and_then(|number| u8::try_from(number).ok())).map(|(kind, field)| Imm::FieldOf(kind, field)),
                    _ => None,
                };
                if let (Intrinsic::TableRef | Intrinsic::TableSet, [_, key, _]) = (intrinsic, args.as_slice()) {
                    hinted[dst.0 as usize] = constants[key.0 as usize].is_some_and(|key| key.immediate().is_some() || Symbol::of(key).is_some());
                }
            }
            _ => {}
        }
    }
    Operands { imms, hinted }
}

/// Counts in `uses` the values that `inst` reads before it defines its own. An instruction with an immediate operand reads only its first argument. The closures of a group do not read each other.
fn count_reads(uses: &mut [u32], inst: &l5::Inst<'_, '_>, imms: &[Option<Imm<'_>>]) {
    match inst {
        l5::Inst::Prim { dst, args, .. } if imms[dst.0 as usize].is_some() => uses[args[0].0 as usize] += 1,
        l5::Inst::Closures { dsts, .. } => inst.each_use(|value| {
            if !dsts.contains(&value) {
                uses[value.0 as usize] += 1;
            }
        }),
        _ => inst.each_use(|value| uses[value.0 as usize] += 1),
    }
}

/// Returns whether `block` ends by returning the result of an intrinsic that has a tail-return form, and nothing else reads that result.
fn fused_return(block: &l5::BlockData<'_, '_>, uses: &[u32], imms: &[Option<Imm<'_>>], hinted: &[bool]) -> bool {
    let (Some(l5::Inst::Prim { dst, prim, spread, .. }), l5::End::Return(returned)) = (block.insts.last(), &block.end) else { return false };
    // `values` has a tail-return form even with a spread argument list: `Op::ReturnSpread` returns the elements of the list as values. No other intrinsic has a tail-return form for a spread argument list.
    let tail = match prim {
        Prim::Intrinsic(Intrinsic::Values) => true,
        // An instruction with an immediate operand or a table hint has no tail-return form. It is emitted as it is and followed by a return.
        Prim::Intrinsic(_) => !spread && imms[dst.0 as usize].is_none() && !hinted[dst.0 as usize],
        _ => false,
    };
    tail && dst == returned && uses[dst.0 as usize] == 1
}

/// Returns whether `block` ends by branching on the result of an intrinsic test of one or two arguments, and nothing else reads that result.
fn fused_test(block: &l5::BlockData<'_, '_>, uses: &[u32], imms: &[Option<Imm<'_>>]) -> bool {
    let (Some(l5::Inst::Prim { dst, prim: Prim::Intrinsic(_), args, spread: false }), l5::End::Branch { test, .. }) = (block.insts.last(), &block.end) else {
        return false;
    };
    dst == test && uses[dst.0 as usize] == 1 && (1..=2).contains(&args.len()) && imms[dst.0 as usize].is_none()
}

/// Computes basic block layout order via depth-first traversal, arranging fall-through jumps along hot edges
/// and inverting loop condition branches so that loop bodies fall through while loop exits branch away.
fn layout<'t>(arena: &'t Arena, function: &l5::Function<'_, '_>, to: &[usize], fusable: &[bool]) -> (AVec<'t, usize>, AVec<'t, bool>) {
    let count = function.blocks.len();
    let (mut order, mut placed, mut inverted) = (AVec::with_capacity_in(count, arena), arena.vec_of(false, count), arena.vec_of(false, count));
    let mut stack = ragwort_alloc::vec_in![arena; 0];
    while let Some(block) = stack.pop() {
        let block = to[block];
        if placed[block] {
            continue;
        }
        placed[block] = true;
        order.push(block);
        match &function.blocks[block].end {
            l5::End::Jump(next, _) => stack.push(next.0 as usize),
            l5::End::Branch { then, other, .. } => {
                let (then, other) = (to[then.0 as usize], to[other.0 as usize]);
                let invert = fusable[block] && recurs(arena, function, to, &placed, other) && !recurs(arena, function, to, &placed, then);
                inverted[block] = invert;
                stack.extend(if invert { [then, other] } else { [other, then] });
            }
            l5::End::Return(_) | l5::End::TailCall { .. } | l5::End::TailPrim { .. } => {}
        }
    }
    (order, inverted)
}

/// Heuristically checks (up to a small bounded depth) whether all outgoing paths from block `start` lead to
/// an already placed block, indicating a backward loop edge.
fn recurs(arena: &Arena, function: &l5::Function<'_, '_>, to: &[usize], placed: &[bool], start: usize) -> bool {
    let mut ways = ragwort_alloc::vec_in![arena; start];
    let mut seen = 0;
    while let Some(block) = ways.pop() {
        let block = to[block];
        if placed[block] {
            continue;
        }
        seen += 1;
        if seen > 64 {
            return false;
        }
        match &function.blocks[block].end {
            l5::End::Jump(next, _) => ways.push(next.0 as usize),
            l5::End::Branch { then, other, .. } => ways.extend([then.0 as usize, other.0 as usize]),
            l5::End::Return(_) | l5::End::TailCall { .. } | l5::End::TailPrim { .. } => return false,
        }
    }
    true
}

/// Computes the effective jump target for each basic block, bypassing intermediate blocks that contain only an unconditional jump.
fn forwards<'t>(arena: &'t Arena, function: &l5::Function<'_, '_>) -> AVec<'t, usize> {
    fn on(function: &l5::Function<'_, '_>, index: usize) -> Option<usize> {
        match &function.blocks[index] {
            block if index > 0 && block.params.is_empty() && block.insts.is_empty() => match &block.end {
                l5::End::Jump(to, args) if args.is_empty() => Some(to.0 as usize),
                _ => None,
            },
            _ => None,
        }
    }
    (0..function.blocks.len())
        .map(|index| {
            if on(function, index).is_none() {
                return index;
            }
            let (mut at, mut seen) = (index, ragwort_alloc::vec_in![arena; index]);
            while let Some(to) = on(function, at) {
                if seen.contains(&to) {
                    return index;
                }
                seen.push(to);
                at = to;
            }
            at
        })
        .collect_in(arena)
}
