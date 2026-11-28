//! Pass 9: register allocation for an [`L6`](crate::l6) function.
//!
//! Gives every value that is read a frame register or a spill slot. The result is a [`Places`], which
//! [`emit`](crate::emit) reads. The function itself is not changed.
//!
//! The steps:
//!
//! 1. **Fixed registers.** The closure and the parameters are where the calling convention puts them.
//! 2. **Liveness.** [`liveness`] finds the values that are live at the end of each block.
//! 3. **Colouring.** [`colour`] walks the blocks in dominator-tree order and gives each value the lowest
//!    colour that no value live at the same time holds. Colours that do not fit in the frame's
//!    registers become slots of a spill array.
//! 4. **Aims.** A value that is read once, as an argument of a call or of a jump in its own block, is
//!    moved to the register the call or jump wants it in, if that register is free in between. This
//!    saves the move at the call.
//! 5. **Call bases.** A non-tail call stages its arguments above every register that is live across
//!    it. The pass records that register for each instruction.

use ragwort_alloc::{Arena, CollectIn, Vec as AVec};
use ragwort_types::gc::WINDOW;
use ragwort_vm::frame::{ARGS, CLOSURE, MAX_PARAMS};

use crate::Prim;
use crate::l5::{self, Val};
use crate::l6::{End, Function, Inst, Kind};

/// The number of scratch registers reserved at the top of the register window (`WINDOW / 4`),
/// which sets the maximum number of arguments that can be staged for an outgoing call in scratch space.
pub(crate) const STAGE: usize = WINDOW / 4;
/// The boundary register index separating general-purpose function registers (`0..LIMIT`) from reserved scratch registers (`LIMIT..WINDOW`).
pub(crate) const LIMIT: u8 = (WINDOW - STAGE) as u8;
pub(crate) const SCRATCH: u8 = LIMIT;

/// The physical storage location assigned to an SSA value (either a frame register or a spill slot).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Loc {
    Reg(u8),
    /// A slot index within the frame's heap-allocated spill array.
    Slot(u32),
}

/// The result of register allocation for one function.
pub(crate) struct Places<'t> {
    locs: AVec<'t, Option<Loc>>,
    /// The register that holds the frame's spill array, or `None` if every value has a register.
    pub(crate) spill: Option<u8>,
    /// The number of slots in the spill array.
    pub(crate) slots: u32,
    /// The first register available to the function's own values, above the closure, the parameters and the link.
    pub(crate) first: u8,
    /// The call base of every instruction, block after block. `starts[block]` is the index of the block's first instruction.
    bases: AVec<'t, u8>,
    starts: AVec<'t, usize>,
}

impl Places<'_> {
    /// Returns the location of `value`, or `None` if nothing reads the value.
    pub(crate) fn loc(&self, value: Val) -> Option<Loc> {
        self.locs[value.0 as usize]
    }

    /// Returns the lowest register at which instruction `inst` of block `block` can stage the arguments of a non-tail call. Every register that is live across the instruction is below it.
    pub(crate) fn base(&self, block: usize, inst: usize) -> u8 {
        self.bases[self.starts[block] + inst]
    }
}

/// Allocates registers and spill slots for the values of `function`. `link` is the register of the frame's link, which follows the parameters.
pub(crate) fn allocate<'t>(arena: &'t Arena, function: &Function<'_, '_>, link: u8) -> Places<'t> {
    let source = function.source;
    let values = source.values as usize;
    let mut fixed = arena.vec_of(None, values);
    fixed[source.this.0 as usize] = Some(CLOSURE);
    if function.unpacked.is_empty() {
        source.params.iter().chain(&source.rest).zip(ARGS..).for_each(|(param, register)| fixed[param.0 as usize] = Some(register));
    } else {
        // The last argument register holds the surplus arguments as a list. The rest parameter is what remains of that list after the function unpacks its surplus parameters.
        let keep = usize::from(MAX_PARAMS - 1);
        source.params[..keep].iter().zip(ARGS..).for_each(|(param, register)| fixed[param.0 as usize] = Some(register));
        source.rest.iter().for_each(|rest| fixed[rest.0 as usize] = Some(ARGS + MAX_PARAMS - 1));
    }
    let live = liveness(arena, function);
    let pinned: AVec<'_, bool> = fixed.iter().map(Option::is_some).collect_in(arena);
    let colours = colour(arena, function, &live, &pinned);

    let own = LIMIT.saturating_sub(link + 1);
    let (spill, first) = if colours.count > u32::from(own) {
        (Some(link + 1), link + 2)
    } else {
        (None, link + 1)
    };
    let own = u32::from(LIMIT.saturating_sub(first));
    let locs = fixed
        .iter()
        .zip(&colours.of)
        .map(|(&register, &colour)| match (register, colour) {
            (Some(register), _) => Some(Loc::Reg(register)),
            (None, Some(colour)) if colour < own => Some(Loc::Reg(first + colour as u8)),
            (None, Some(colour)) => Some(Loc::Slot(colour - own)),
            (None, None) => None,
        })
        .collect_in(arena);
    let mut starts = arena.vec_of(0, function.blocks.len());
    let mut total = 0;
    for (index, block) in function.blocks.iter().enumerate() {
        starts[index] = total;
        total += block.insts.len();
    }
    let mut aiming = Aiming {
        function,
        locs,
        first,
        aims: arena.vec_of(None, values),
        at: arena.vec_of(0, live.words),
        seen: arena.vec(),
        highs: arena.vec(),
        after: arena.vec(),
        bases: arena.vec_of(first, total),
    };
    for &index in function.order.iter() {
        aiming.block(index, &live, starts[index]);
    }
    let Aiming { locs, bases, .. } = aiming;
    Places { locs, spill, slots: colours.count.saturating_sub(own), first, bases, starts }
}

fn has(set: &[u64], value: Val) -> bool {
    set[value.0 as usize / 64] & (1 << (value.0 % 64)) != 0
}

/// Inserts value `value` into bitset `set`, returning `true` if `value` was not previously present.
fn add(set: &mut [u64], value: Val) -> bool {
    let (word, bit) = (&mut set[value.0 as usize / 64], 1 << (value.0 % 64));
    let new = *word & bit == 0;
    *word |= bit;
    new
}

fn remove(set: &mut [u64], value: Val) {
    set[value.0 as usize / 64] &= !(1 << (value.0 % 64));
}

/// A bitset representing a set of physical registers within the register window (`WINDOW`).
type Regs = [u64; WINDOW / 64];

fn has_reg(regs: &Regs, register: u8) -> bool {
    regs[usize::from(register) / 64] & (1 << (register % 64)) != 0
}

fn set_reg(regs: &mut Regs, register: u8, to: bool) {
    let (word, bit) = (&mut regs[usize::from(register) / 64], 1 << (register % 64));
    *word = if to {
        *word | bit
    } else {
        *word & !bit
    };
}

fn highest(regs: &Regs) -> Option<u8> {
    let i = regs.iter().rposition(|&word| word != 0)?;
    Some((i * 64 + 63 - regs[i].leading_zeros() as usize) as u8)
}

/// Live-out variable analysis results: contains the set of SSA values live exiting each basic block
/// and the predecessor list for every block.
struct Live<'t> {
    preds: AVec<'t, AVec<'t, usize>>,
    /// Slice index bounds into `outs`: the live-out values for block `b` are located in `outs[starts[b]..starts[b + 1]]`.
    starts: AVec<'t, usize>,
    outs: AVec<'t, Val>,
    /// The number of 64-bit words required for a bitset spanning all SSA values in the function.
    words: usize,
}

impl Live<'_> {
    fn outs(&self, block: usize) -> &[Val] {
        &self.outs[self.starts[block]..self.starts[block + 1]]
    }
}

/// Sentinel value representing an unassigned block index, or indicating that a value is defined at function entry.
const NOWHERE: u32 = u32::MAX;

/// Computes live-out value sets for each basic block by traversing backwards from each use site
/// to its definition block. This sparse backward traversal avoids the memory overhead of a full dense block-by-value matrix.
fn liveness<'t>(arena: &'t Arena, function: &Function<'_, '_>) -> Live<'t> {
    let source = function.source;
    let (count, values) = (function.blocks.len(), source.values as usize);
    let mut preds = arena.vec_of(arena.vec(), count);
    for (index, block) in source.blocks.iter().enumerate() {
        for to in block.end.successors() {
            preds[to.0 as usize].push(index);
        }
    }
    let mut home = arena.vec_of(NOWHERE, values);
    for (index, block) in function.blocks.iter().enumerate() {
        source.blocks[index].params.iter().for_each(|param| home[param.0 as usize] = index as u32);
        block.insts.iter().flat_map(|inst| inst.defs).for_each(|def| home[def.0 as usize] = index as u32);
    }
    // Identifies upwards-exposed values: values used in a block before being defined in that block.
    let mut exposed = arena.vec();
    for (index, block) in function.blocks.iter().enumerate() {
        for value in block.insts.iter().flat_map(Inst::reads).chain(block.end.reads()) {
            if home[value.0 as usize] != index as u32 {
                exposed.push((value.0, index as u32));
            }
        }
    }
    exposed.sort_unstable();
    // Tracks the most recent SSA value processed for each block's live-in and live-out sets to avoid redundant visits.
    let (mut into, mut out) = (arena.vec_of(NOWHERE, count), arena.vec_of(NOWHERE, count));
    let (mut found, mut stack) = (arena.vec(), arena.vec());
    for &(value, block) in exposed.iter() {
        if into[block as usize] == value {
            continue;
        }
        into[block as usize] = value;
        stack.push(block as usize);
        while let Some(current) = stack.pop() {
            for &pred in &preds[current] {
                if out[pred] != value {
                    out[pred] = value;
                    found.push((pred, Val(value)));
                }
                if home[value as usize] != pred as u32 && into[pred] != value {
                    into[pred] = value;
                    stack.push(pred);
                }
            }
        }
    }
    // Groups live-out values by basic block, sorted by SSA value index to build compact contiguous slices.
    let mut starts = arena.vec_of(0, count + 1);
    found.iter().for_each(|&(block, _)| starts[block + 1] += 1);
    (0..count).for_each(|block| starts[block + 1] += starts[block]);
    let mut next = starts.clone();
    let mut outs = arena.vec_of(Val(0), found.len());
    for &(block, value) in found.iter() {
        outs[next[block]] = value;
        next[block] += 1;
    }
    Live { preds, starts, outs, words: values.div_ceil(64).max(1) }
}

/// Register allocation colors (virtual register indices) assigned to SSA values, along with the total color count.
struct Colours<'t> {
    of: AVec<'t, Option<u32>>,
    count: u32,
}

/// Performs register coloring on all unpinned SSA values in dominator tree order, allocating values defined
/// at function entry first.
fn colour<'t>(arena: &'t Arena, function: &Function<'_, '_>, live: &Live<'_>, pinned: &[bool]) -> Colours<'t> {
    let source = function.source;
    let count = function.blocks.len();
    let mut children = arena.vec_of(arena.vec(), count);
    if count > 1 {
        let idom = l5::dominators(&source.blocks, &live.preds).expect("lowering reaches every block");
        for block in 1..count {
            children[idom[block]].push(block);
        }
    }
    let colours = Colours { of: arena.vec_of(None, source.values as usize), count: 0 };
    let mut colouring = Colouring { colours, taken: arena.vec(), pinned, uses: &function.uses };
    // Bitset of values currently live during backward block scanning, accompanied by an undo log of visited values.
    let (mut at, mut seen) = (arena.vec_of(0, live.words), arena.vec());
    // Records values whose live ranges terminate at instruction `i`, indexed via `dying[spans[i].0..spans[i].1]`.
    let (mut dying, mut spans) = (arena.vec(), arena.vec());
    let mut stack = ragwort_alloc::vec_in![arena; 0];
    while let Some(index) = stack.pop() {
        stack.extend(children[index].iter().rev().copied());
        let block = &function.blocks[index];
        seen.clear();
        for &value in live.outs(index) {
            add(&mut at, value);
            seen.push(value);
        }
        dying.clear();
        for value in block.end.reads() {
            if add(&mut at, value) {
                seen.push(value);
            }
        }
        spans.clear();
        spans.resize(block.insts.len(), (0, 0));
        for (i, inst) in block.insts.iter().enumerate().rev() {
            let start = dying.len();
            for value in inst.reads() {
                if !has(&at, value) && !dying[start..].contains(&value) {
                    dying.push(value);
                }
            }
            spans[i] = (start, dying.len());
            for &def in inst.defs {
                remove(&mut at, def);
            }
            for value in inst.reads() {
                if add(&mut at, value) {
                    seen.push(value);
                }
            }
        }
        // Marks the colours of the values that are live on entry to the block as taken, then assigns colours to the block's parameters.
        colouring.taken.clear();
        colouring.taken.resize(colouring.colours.count as usize, false);
        for &value in seen.iter() {
            if has(&at, value)
                && let Some(colour) = colouring.colours.of[value.0 as usize]
            {
                colouring.taken[colour as usize] = true;
            }
            remove(&mut at, value);
        }
        if index == 0 {
            function.unpacked.iter().for_each(|&value| colouring.take(value));
        }
        source.blocks[index].params.iter().for_each(|&param| colouring.take(param));
        for (inst, &(start, end)) in block.insts.iter().zip(&spans) {
            // The closure object's destination register is defined prior to capturing environment values.
            if let Kind::Closures(_) = inst.kind {
                inst.defs.iter().for_each(|&def| colouring.take(def));
                dying[start..end].iter().for_each(|&value| colouring.free(value));
            } else {
                dying[start..end].iter().for_each(|&value| colouring.free(value));
                inst.defs.iter().for_each(|&def| colouring.take(def));
            }
        }
    }
    colouring.colours
}

/// State for greedy register coloring: maintains assigned colors and tracks which colors are currently occupied.
struct Colouring<'t, 'f> {
    colours: Colours<'t>,
    taken: AVec<'t, bool>,
    pinned: &'f [bool],
    uses: &'f [u32],
}

impl Colouring<'_, '_> {
    /// Assigns the lowest available register color to value `value`, provided `value` is used and not pinned to a fixed register.
    fn take(&mut self, value: Val) {
        if self.pinned[value.0 as usize] || self.uses[value.0 as usize] == 0 {
            return;
        }
        let colour = self.taken.iter().position(|&taken| !taken).unwrap_or(self.taken.len());
        if colour == self.taken.len() {
            self.taken.push(false);
        }
        self.taken[colour] = true;
        self.colours.of[value.0 as usize] = Some(colour as u32);
        self.colours.count = self.colours.count.max(colour as u32 + 1);
    }

    fn free(&mut self, value: Val) {
        if let Some(colour) = self.colours.of[value.0 as usize] {
            self.taken[colour as usize] = false;
        }
    }
}

/// Target register preference for a value with a single use: designates an argument register at an outgoing
/// call base (standard or tail call) or the register assigned to a target block parameter.
#[derive(Clone, Copy)]
enum Aim {
    Base(u8),
    First(u8),
    Reg(u8),
}

/// The state of the pass that moves values to the registers their single use wants them in, and records the call base of each instruction.
struct Aiming<'f, 't, 'gc> {
    function: &'f Function<'f, 'gc>,
    locs: AVec<'t, Option<Loc>>,
    first: u8,
    /// Preferred register targets for singly-used values: records the destination block, instruction index,
    /// and target register position.
    aims: AVec<'t, Option<(u32, u32, Aim)>>,
    /// Reusable scratch buffers retained across blocks.
    /// `at` is a bitset of values active during backward block scanning; `seen` records modified indices for rapid resetting.
    at: AVec<'t, u64>,
    seen: AVec<'t, Val>,
    /// The highest register that is live across each instruction of the block being scanned.
    highs: AVec<'t, Option<u8>>,
    /// The registers that are live after each instruction of the block being scanned.
    after: AVec<'t, Regs>,
    bases: AVec<'t, u8>,
}

impl Aiming<'_, '_, '_> {
    /// Scans block `index` backwards for the registers live at each instruction, then aims its values and records its call bases from `start` on in `bases`.
    fn block(&mut self, index: usize, live: &Live<'_>, start: usize) {
        let function = self.function;
        let block = &function.blocks[index];
        let count = block.insts.len();
        // Computes the set of active registers following each instruction, identifying the highest live register
        // to establish the frame base for nested calls.
        let mut taken = [0; WINDOW / 64];
        self.seen.clear();
        for &value in live.outs(index) {
            add(&mut self.at, value);
            self.seen.push(value);
            self.mark(&mut taken, value, true);
        }
        for value in block.end.reads() {
            if add(&mut self.at, value) {
                self.seen.push(value);
                self.mark(&mut taken, value, true);
            }
        }
        self.aim_end(index);
        self.highs.clear();
        self.highs.resize(count, None);
        self.after.clear();
        self.after.resize(count, taken);
        for (i, inst) in block.insts.iter().enumerate().rev() {
            self.after[i] = taken;
            for &def in inst.defs {
                remove(&mut self.at, def);
                self.mark(&mut taken, def, false);
            }
            self.highs[i] = highest(&taken);
            self.aim_args(index, i, inst);
            for value in inst.reads() {
                if add(&mut self.at, value) {
                    self.seen.push(value);
                    self.mark(&mut taken, value, true);
                }
            }
        }
        for i in 0..self.seen.len() {
            let value = self.seen[i];
            remove(&mut self.at, value);
        }
        for (j, inst) in block.insts.iter().enumerate() {
            if let &[def] = inst.defs
                && !matches!(inst.kind, Kind::Closures(_))
            {
                self.aim(index, j, def);
            }
            self.bases[start + j] = self.highs[j].map_or(self.first, |high| self.first.max(high + 1));
        }
    }

    fn mark(&self, taken: &mut Regs, value: Val, to: bool) {
        if let Some(Loc::Reg(register)) = self.locs[value.0 as usize] {
            set_reg(taken, register, to);
        }
    }

    /// Registers target preferences for argument values staged by `inst` at instruction `at` in block `block`.
    fn aim_args(&mut self, block: usize, at: usize, inst: &Inst<'_, '_>) {
        let staged = match inst.kind {
            Kind::Call => true,
            // An intrinsic with up to three arguments reads them from any registers. Every other call takes its arguments from a row of registers.
            Kind::Prim { prim: Prim::Intrinsic(_), spread: false } => inst.args.len() > 3,
            Kind::Prim { .. } => true,
            _ => false,
        };
        if staged {
            for (position, value) in inst.reads().enumerate() {
                self.wants(value, block, at, Aim::Base(u8::try_from(position).unwrap_or(u8::MAX)));
            }
        }
    }

    /// Registers target preferences for the values that the end of block `index` passes on: the arguments of a jump, or the arguments of a call in tail position.
    fn aim_end(&mut self, index: usize) {
        let function = self.function;
        let block = &function.blocks[index];
        let at = block.insts.len();
        match block.end {
            End::Jump(to, args) => {
                for (param, &arg) in function.source.blocks[to.0 as usize].params.iter().zip(args) {
                    if let Some(Loc::Reg(register)) = self.locs[param.0 as usize] {
                        self.wants(arg, index, at, Aim::Reg(register));
                    }
                }
            }
            End::TailCall { .. } | End::TailPrim { .. } | End::ReturnPrim { .. } => {
                for (position, value) in block.end.reads().enumerate() {
                    self.wants(value, index, at, Aim::First(u8::try_from(position).unwrap_or(u8::MAX)));
                }
            }
            End::Return(_) | End::Branch { .. } | End::BranchPrim { .. } => {}
        }
    }

    fn wants(&mut self, value: Val, block: usize, at: usize, aim: Aim) {
        if self.function.uses[value.0 as usize] == 1 {
            self.aims[value.0 as usize] = Some((block as u32, at as u32, aim));
        }
    }

    /// Pre-assigns `value` (defined at instruction `j` in block `index`) directly to its preferred destination register,
    /// provided that register remains unallocated throughout the intervening range.
    fn aim(&mut self, index: usize, j: usize, value: Val) {
        let Some((block, at, aim)) = self.aims[value.0 as usize] else { return };
        let at = at as usize;
        if block as usize != index || at <= j {
            return;
        }
        let first = usize::from(self.first);
        let target = match aim {
            Aim::Reg(register) => usize::from(register),
            Aim::First(position) => first + usize::from(position),
            Aim::Base(position) => self.highs[at].map_or(first, |high| first.max(usize::from(high) + 1)) + usize::from(position),
        };
        if target < first || target >= usize::from(LIMIT) {
            return;
        }
        let target = target as u8;
        if self.locs[value.0 as usize] == Some(Loc::Reg(target)) || self.after[j..at].iter().any(|regs| has_reg(regs, target)) {
            return;
        }
        self.locs[value.0 as usize] = Some(Loc::Reg(target));
        self.after[j..at].iter_mut().for_each(|regs| set_reg(regs, target, true));
        self.highs[j + 1..at].iter_mut().for_each(|high| *high = Some(high.map_or(target, |current| current.max(target))));
    }
}
