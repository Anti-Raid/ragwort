//! Pass 8 (`L5 -> Closure`): register allocation and bytecode emission from [`L5`](crate::l5).
//!
//! Allocates physical frame registers and spill slots for SSA values via greedy graph coloring in dominator
//! order. Values with overlapping live ranges receive distinct registers, selecting the lowest available
//! register index not currently occupied. Non-tail calls are staged beyond all registers currently live across
//! the call boundary, aligning with the caller-callee overlapping frame window. Jumps and call argument
//! setup emit parallel moves to resolve multi-register assignments without clobbering live values.

use ragwort_alloc::{Arena, CollectIn, Vec as AVec};
use ragwort_types::gc::{Gc, Mutation, Value, WINDOW};
use ragwort_types::vector::Vectors;
use ragwort_vm::frame::{self, ARGS, CLOSURE, MAX_PARAMS, Shape};
use ragwort_vm::objects::{self, Bytecode, BytecodeFields, Closure, ModuleFields, Sites, SitesFields};
use ragwort_vm::report::{Line, Scope, Table};
use ragwort_vm::{Capture, HostDef, Intrinsic, Op, Request};

use crate::hash::HashMap;
use crate::ir::{Inlined, Origins, Site};
use crate::l5::{self, Block, Captured, Code, End, Function, Inst, Program, Val};
use crate::{CompileError, Prim, SlotOp};

/// The number of scratch registers reserved at the top of the register window (`WINDOW / 4`),
/// which sets the maximum number of arguments that can be staged for an outgoing call in scratch space.
pub(crate) const STAGE: usize = WINDOW / 4;
/// The boundary register index separating general-purpose function registers (`0..LIMIT`) from reserved scratch registers (`LIMIT..WINDOW`).
const LIMIT: u8 = (WINDOW - STAGE) as u8;
const SCRATCH: u8 = LIMIT;

pub(crate) fn emit<'gc>(mc: &Mutation<'gc>, owner: Option<Gc<'gc, objects::Module>>, program: &Program<'_, 'gc>, names: &Origins<'gc>) -> Result<Value<'gc>, CompileError> {
    let mut module = Module { mc, owner, names, lines: Vec::new(), items: Vec::new(), item_index: HashMap::default(), constants: Vec::new(), index: HashMap::default(), codes: Vec::new(), pending: Vec::new() };
    let code = module.function(program.root(), &[])?;
    while let Some(Pending { slot, function, captures, closure }) = module.pending.pop() {
        let bytecode = module.function(&program.functions[function as usize], &captures)?;
        let value = if closure { Value::object(mc, Closure::new(mc, Some(bytecode), 0, Value::VOID)?) } else { Value::object(mc, bytecode) };
        module.constants[slot as usize] = value;
        module.index.insert(value.to_bits(), slot);
    }
    let table = Vectors::new(mc).immutable_from_slice(&module.constants)?.value(mc);
    for &bytecode in &module.codes {
        bytecode.set_constants(mc, table);
    }
    if !module.lines.is_empty() {
        let sites = module.sites()?;
        for &bytecode in &module.codes {
            bytecode.set_sites(mc, sites);
        }
    }
    Ok(Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID)?))
}

/// The physical storage location assigned to an SSA value (either a hardware register or a spill slot).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Loc {
    Reg(u8),
    /// A slot index within the frame's heap-allocated spill array.
    Slot(u32),
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
    *word = if to { *word | bit } else { *word & !bit };
}

fn highest(regs: &Regs) -> Option<u8> {
    let i = regs.iter().rposition(|&word| word != 0)?;
    Some((i * 64 + 63 - regs[i].leading_zeros() as usize) as u8)
}

/// Target register preference for a value with a single use: designates an argument register at an outgoing
/// call base (standard or tail call) or the register assigned to a target block parameter.
#[derive(Clone, Copy)]
enum Aim {
    Base(u8),
    First(u8),
    Reg(u8),
}

/// Immediate constants embedded directly within an opcode rather than loaded from registers.
/// Instructions using immediate operands read only their first argument register.
#[derive(Clone, Copy)]
enum Imm<'gc> {
    /// Immediate integer offset for `(+ a k)` represented by `Op::AddImm`.
    Add(i16),
    /// Field index for `(struct-field s k)` or `(struct-fixed-field s k)` encoded in `Op::StructField`.
    Field(u16),
    /// Type descriptor and field index for `(struct-ref s type k)` encoded in `Op::StructRef`.
    FieldOf(Value<'gc>, u8),
}

/// Precomputes embedded immediate constants for each SSA instruction that supports immediate operands.
type Imms<'t, 'gc> = AVec<'t, Option<Imm<'gc>>>;

fn imms<'t, 'gc>(arena: &'t Arena, function: &Function<'_, 'gc>) -> Imms<'t, 'gc> {
    let mut constants: AVec<'t, Option<Value<'gc>>> = arena.vec_of(None, function.values as usize);
    let mut imms = arena.vec_of(None, function.values as usize);
    for inst in function.blocks.iter().flat_map(|block| &block.insts) {
        match inst {
            Inst::Const(dst, value) => constants[dst.0 as usize] = Some(*value),
            Inst::Prim { dst, prim: Prim::Intrinsic(intrinsic), args, spread: false } => {
                let fixnum = |value: &Val| constants[value.0 as usize].and_then(|constant| constant.as_fixnum());
                imms[dst.0 as usize] = match (intrinsic, args.as_slice()) {
                    (Intrinsic::Add, [_, addend]) => fixnum(addend).and_then(|number| i16::try_from(number).ok()).map(Imm::Add),
                    (Intrinsic::StructField | Intrinsic::StructFixedField, [_, field]) => fixnum(field).and_then(|number| u16::try_from(number).ok()).map(Imm::Field),
                    (Intrinsic::StructRef, [_, kind, field]) => constants[kind.0 as usize].zip(fixnum(field).and_then(|number| u8::try_from(number).ok())).map(|(kind, field)| Imm::FieldOf(kind, field)),
                    _ => None,
                };
            }
            _ => {}
        }
    }
    imms
}

/// Iterates over every SSA value read by `inst` before its destination is assigned. Mutual closures
/// capture each other once instantiated, and instructions with immediate constants read only their first argument.
fn each_read(inst: &Inst<'_, '_>, imms: &Imms<'_, '_>, mut visit: impl FnMut(Val)) {
    match inst {
        Inst::Prim { dst, args, .. } if imms[dst.0 as usize].is_some() => visit(args[0]),
        Inst::Closures { dsts, .. } => inst.each_use(|value| {
            if !dsts.contains(&value) {
                visit(value);
            }
        }),
        _ => inst.each_use(visit),
    }
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
fn liveness<'t>(arena: &'t Arena, function: &Function<'_, '_>, imms: &Imms<'_, '_>) -> Live<'t> {
    let (count, values) = (function.blocks.len(), function.values as usize);
    let mut preds = arena.vec_of(arena.vec(), count);
    for (index, block) in function.blocks.iter().enumerate() {
        for to in block.end.successors() {
            preds[to.0 as usize].push(index);
        }
    }
    let mut home = arena.vec_of(NOWHERE, values);
    for (index, block) in function.blocks.iter().enumerate() {
        block.params.iter().for_each(|param| home[param.0 as usize] = index as u32);
        block.insts.iter().flat_map(|inst| inst.defs()).for_each(|def| home[def.0 as usize] = index as u32);
    }
    // Identifies upwards-exposed values: values used in a block before being defined in that block.
    let mut exposed = arena.vec();
    for (index, block) in function.blocks.iter().enumerate() {
        let mut note = |value: Val| {
            if home[value.0 as usize] != index as u32 {
                exposed.push((value.0, index as u32));
            }
        };
        block.insts.iter().for_each(|inst| each_read(inst, imms, &mut note));
        block.end.each_use(&mut note);
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
fn colour<'t>(
    arena: &'t Arena,
    function: &Function<'_, '_>,
    live: &Live<'_>,
    imms: &Imms<'_, '_>,
    pinned: &[bool],
    uses: &[u32],
    defined: &[Val],
) -> Colours<'t> {
    let count = function.blocks.len();
    let mut children = arena.vec_of(arena.vec(), count);
    if count > 1 {
        let idom = l5::dominators(&function.blocks, &live.preds).expect("lowering reaches every block");
        for block in 1..count {
            children[idom[block]].push(block);
        }
    }
    let colours = Colours { of: arena.vec_of(None, function.values as usize), count: 0 };
    let mut colouring = Colouring { colours, taken: arena.vec(), pinned, uses };
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
        block.end.each_use(|value| {
            if add(&mut at, value) {
                seen.push(value);
            }
        });
        dying.clear();
        spans.clear();
        spans.resize(block.insts.len(), (0, 0));
        for (i, inst) in block.insts.iter().enumerate().rev() {
            let start = dying.len();
            each_read(inst, imms, |value| {
                if !has(&at, value) && !dying[start..].contains(&value) {
                    dying.push(value);
                }
            });
            spans[i] = (start, dying.len());
            for &def in inst.defs() {
                remove(&mut at, def);
            }
            each_read(inst, imms, |value| {
                if add(&mut at, value) {
                    seen.push(value);
                }
            });
        }
        // Reclaims colors for values that are live-in to the block, then assigns colors to uncolored block parameters.
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
            defined.iter().for_each(|&value| colouring.take(value));
        }
        block.params.iter().for_each(|&param| colouring.take(param));
        for (inst, &(start, end)) in block.insts.iter().zip(&spans) {
            // The closure object's destination register is defined prior to capturing environment values.
            if let Inst::Closures { .. } = inst {
                inst.defs().iter().for_each(|&def| colouring.take(def));
                dying[start..end].iter().for_each(|&value| colouring.free(value));
            } else {
                dying[start..end].iter().for_each(|&value| colouring.free(value));
                inst.defs().iter().for_each(|&def| colouring.take(def));
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

/// A deferred closure compilation job: function `function` in the program to be emitted into constant pool
/// index `slot`. It is emitted as compiled bytecode, or as a pre-instantiated closure if it captures no upvalues.
struct Pending {
    slot: u32,
    function: u32,
    captures: Vec<Capture>,
    closure: bool,
}

/// Compilation context holding the constant pool and bytecode generated during module code emission.
struct Module<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    /// The owning runtime module whose imported variables and host function tables are accessed.
    owner: Option<Gc<'gc, objects::Module>>,
    names: &'a Origins<'gc>,
    /// The position table rows of every function emitted so far, and the sources and names they refer to by index.
    lines: Vec<Line>,
    items: Vec<Value<'gc>>,
    item_index: HashMap<u64, u32>,
    constants: Vec<Value<'gc>>,
    index: HashMap<u64, u32>,
    codes: Vec<Gc<'gc, Bytecode>>,
    /// Deferred closure functions awaiting bytecode emission, organized as a work stack.
    pending: Vec<Pending>,
}

impl<'a, 'gc> Module<'a, 'gc> {
    fn constant(&mut self, value: Value<'gc>) -> Result<u32, CompileError> {
        if let Some(&i) = self.index.get(&value.to_bits()) {
            return Ok(i);
        }
        let i = u32::try_from(self.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
        self.constants.push(value);
        self.index.insert(value.to_bits(), i);
        Ok(i)
    }

    /// Returns the index of host function `def` in the module's host table, registering it if not yet present.
    fn host(&self, def: &'static HostDef) -> Result<u32, CompileError> {
        let hosts = self.owner.and_then(|module| module.hosts(self.mc)).map_or(&[][..], |table| &table[..]);
        let i = hosts.iter().position(|&host| host == def).ok_or(CompileError::UnknownHost(def))?;
        u32::try_from(i).map_err(|_| CompileError::TooManyConstants)
    }

    /// Allocates a constant pool slot for deferred compilation of `function` (or a constant closure if `closure` is true).
    /// Consecutive closures within a group are allocated sequential constant slots matching `Op::NewClosure` expectations.
    fn defer(&mut self, function: u32, captures: Vec<Capture>, closure: bool) -> Result<u32, CompileError> {
        let slot = u32::try_from(self.constants.len()).map_err(|_| CompileError::TooManyConstants)?;
        self.constants.push(Value::VOID);
        self.pending.push(Pending { slot, function, captures, closure });
        Ok(slot)
    }

    /// Emits bytecode for function `function`, fusing 1- and 2-argument intrinsic tests into conditional branches
    /// unless jump targets exceed the 16-bit signed branch offset limit.
    /// Returns the index of `value` among the items of the position table, adding it if it is new.
    fn item(&mut self, value: Value<'gc>) -> u32 {
        let next = self.items.len() as u32;
        let index = *self.item_index.entry(value.to_bits()).or_insert(next);
        if index == next {
            self.items.push(value);
        }
        index
    }

    /// Returns the source index, byte offset and inlined-call number of `site`, or `None` for a site without a position.
    fn located(&mut self, site: u32) -> Option<(u32, u32, u32)> {
        let Site { at, inlined } = self.names.sites.get(site)?;
        Some((self.item(at.source), at.offset, inlined))
    }

    /// Builds the object that holds the position table of the functions emitted.
    fn sites(&mut self) -> Result<Value<'gc>, CompileError> {
        let mc = self.mc;
        // Inlined calls keep their numbers: the compilation numbers an inlined call after the call that encloses it, and rows refer to those numbers.
        let mut scopes = Vec::with_capacity(self.names.sites.inlined.len());
        for i in 0..self.names.sites.inlined.len() {
            let Inlined { name, call } = self.names.sites.inlined[i];
            let name = self.item(name);
            let (source, offset, inlined) = self.located(call).unwrap_or((u32::MAX, 0, 0));
            scopes.push(Scope { name, source, offset, inlined });
        }
        let table = Table { lines: std::mem::take(&mut self.lines).into(), scopes: scopes.into() };
        let sites = Sites::new(mc, mc.frozen(table)?, self.items.len(), Value::FALSE)?;
        let items = sites.items(mc);
        for (i, &item) in self.items.iter().enumerate() {
            items.set(mc, i, item);
        }
        Ok(Value::object(mc, sites))
    }

    fn function(&mut self, function: &Function<'_, 'gc>, captures: &[Capture]) -> Result<Gc<'gc, Bytecode>, CompileError> {
        let (constants, codes, pending) = (self.constants.len(), self.codes.len(), self.pending.len());
        if let Some(code) = self.attempt(function, captures, true)? {
            return Ok(code);
        }
        for constant in self.constants.drain(constants..) {
            let bits = constant.to_bits();
            if self.index.get(&bits).is_some_and(|&i| i as usize >= constants) {
                self.index.remove(&bits);
            }
        }
        self.codes.truncate(codes);
        self.pending.truncate(pending);
        Ok(self.attempt(function, captures, false)?.expect("without fused branches every jump has an i32 offset"))
    }

    fn attempt(&mut self, function: &Function<'_, 'gc>, captures: &[Capture], near: bool) -> Result<Option<Gc<'gc, Bytecode>>, CompileError> {
        let (count, optional) = (function.params.len() as u64, u64::from(function.optional));
        let shape = Shape { required: count - optional, optional, rest: function.rest.is_some() };
        // Optional parameters must reside in frame registers; reject parameter shapes exceeding `MAX_PARAMS`.
        if optional > 0 && shape.slots() > u64::from(MAX_PARAMS) {
            return Err(CompileError::TooManyRegisters);
        }
        let arity = shape.encode().ok_or(CompileError::TooManyRegisters)?;
        let link = frame::link_slot(arity);
        let values = function.values as usize;
        // Scratch arena for intra-function compiler data structures, deallocated immediately after function emission.
        let scratch = Arena::new();
        let arena = &scratch;
        let mut fixed = arena.vec_of(None, values);
        fixed[function.this.0 as usize] = Some(CLOSURE);
        let all: AVec<'_, Val> = function.params.iter().chain(&function.rest).copied().collect_in(arena);
        let list = ARGS + MAX_PARAMS - 1;
        // When parameter count exceeds available frame registers, the final register stores overflow arguments as a list.
        let unpacked = if all.len() <= usize::from(MAX_PARAMS) {
            all.iter().zip(ARGS..).for_each(|(param, register)| fixed[param.0 as usize] = Some(register));
            &[][..]
        } else {
            let keep = usize::from(MAX_PARAMS - 1);
            function.params[..keep].iter().zip(ARGS..).for_each(|(param, register)| fixed[param.0 as usize] = Some(register));
            function.rest.iter().for_each(|rest| fixed[rest.0 as usize] = Some(list));
            &function.params[keep..]
        };
        let imms = imms(arena, function);
        let mut uses = arena.vec_of(0u32, values);
        for block in &function.blocks {
            block.insts.iter().for_each(|inst| each_read(inst, &imms, |value| uses[value.0 as usize] += 1));
            block.end.each_use(|value| uses[value.0 as usize] += 1);
        }
        let live = liveness(arena, function, &imms);
        let pinned: AVec<'_, bool> = fixed.iter().map(Option::is_some).collect_in(arena);
        let colours = colour(arena, function, &live, &imms, &pinned, &uses, unpacked);

        let own = LIMIT.saturating_sub(link + 1);
        let (spill, first) = if colours.count > u32::from(own) { (Some(link + 1), link + 2) } else { (None, link + 1) };
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
        let to = forwards(arena, function);
        let fusable: AVec<'_, bool> = function.blocks.iter().map(|block| near && fused_test(block, &uses, &imms).is_some()).collect_in(arena);
        let (order, inverted) = layout(arena, function, &to, &fusable);
        let mut emitter = Emitter {
            module: self,
            arena,
            ops: Vec::new(),
            locs,
            uses,
            imms,
            to,
            at: arena.vec_of(0, live.words),
            seen: arena.vec(),
            highs: arena.vec(),
            after: arena.vec(),
            aims: arena.vec_of(None, values),
            fence: 0,
            moves: arena.vec(),
            fusable,
            inverted,
            spill,
            first,
            starts: arena.vec_of(0, function.blocks.len()),
            jumps: arena.vec(),
            sited: Vec::new(),
        };
        if let Some(dst) = spill {
            emitter.ops.push(Op::NewSpill { dst, count: colours.count - own });
        }
        for &param in unpacked {
            if emitter.used(param) {
                emitter.write(param, |dst| Op::CallIntrinsic1 { dst, a: list, intrinsic: Intrinsic::Car });
            }
            emitter.ops.push(Op::CallIntrinsic1 { dst: list, a: list, intrinsic: Intrinsic::Cdr });
        }
        for (i, &block) in order.iter().enumerate() {
            emitter.block(function, block, &live, order.get(i + 1).copied())?;
        }
        let Emitter { mut ops, mut starts, mut jumps, mut sited, .. } = emitter;
        // Eliminates redundant jumps to the immediately following instruction (e.g. blocks where parallel moves collapsed to no-ops).
        loop {
            let gone: AVec<'_, usize> = jumps
                .iter()
                .filter(|&&(at, to)| starts[to.0 as usize] == at + 1 && matches!(ops[at], Op::Jump { .. } | Op::JumpIfFalse { .. }))
                .map(|&(at, _)| at)
                .collect_in(arena);
            if gone.is_empty() {
                break;
            }
            let mut moved = AVec::with_capacity_in(ops.len() + 1, arena);
            let mut left = 0;
            for i in 0..=ops.len() {
                moved.push(i - left);
                if gone.contains(&i) {
                    left += 1;
                }
            }
            ops = ops.into_iter().enumerate().filter(|(i, _)| !gone.contains(i)).map(|(_, op)| op).collect();
            starts.iter_mut().for_each(|start| *start = moved[*start]);
            sited.iter_mut().for_each(|(pc, _)| *pc = moved[*pc]);
            jumps = jumps.into_iter().filter(|(at, _)| !gone.contains(at)).map(|(at, to)| (moved[at], to)).collect_in(arena);
        }
        for (at, to) in jumps {
            let offset = i32::try_from(starts[to.0 as usize] as isize - (at as isize + 1)).expect("functions are shorter than 2^31 ops");
            match &mut ops[at] {
                Op::Jump { offset: jump } | Op::JumpIfFalse { offset: jump, .. } => *jump = offset,
                Op::BranchIntrinsic1 { offset: jump, .. } | Op::BranchIntrinsic2 { offset: jump, .. } => match i16::try_from(offset) {
                    Ok(offset) => *jump = offset,
                    Err(_) => return Ok(None),
                },
                _ => unreachable!("only jumps go to blocks"),
            }
        }
        let mc = self.mc;
        // A function without a lambda ID is the code of a top-level form, which the trace of an error tells apart from a procedure.
        let described = function.id.map(|id| self.names.get(id)).unwrap_or_default();
        let name = match function.id {
            Some(_) => described.name.unwrap_or(Value::FALSE),
            None => Value::VOID,
        };
        let (source, start) = described.at.map_or((Value::FALSE, 0), |at| (at.source, at.offset));
        let lines_start = self.lines.len();
        for (pc, site) in sited {
            // A row without a position ends the range of the row before it.
            let (source, offset, inlined) = self.located(site).unwrap_or((u32::MAX, 0, 0));
            self.lines.push(Line { pc: pc as u32, source, offset, inlined });
        }
        let (lines_start, lines_len) = (lines_start as u32, (self.lines.len() - lines_start) as u32);
        let code = Bytecode::new(mc, mc.frozen(Box::from(ops))?, Value::VOID, mc.frozen(Box::from(captures))?, arity, self.owner, name, source, start, Value::FALSE, lines_start, lines_len)?;
        self.codes.push(code);
        Ok(Some(code))
    }
}

/// Identifies whether the final instruction in `block` is a 1- or 2-argument intrinsic comparison
/// that can be fused directly into the conditional branch terminator.
fn fused_test<'b>(block: &'b l5::BlockData<'_, '_>, uses: &[u32], imms: &Imms<'_, '_>) -> Option<(Intrinsic, &'b [Val])> {
    let (Some(Inst::Prim { dst, prim: Prim::Intrinsic(intrinsic), args, spread: false }), End::Branch { test, .. }) = (block.insts.last(), &block.end) else {
        return None;
    };
    let fusable = dst == test && uses[dst.0 as usize] == 1 && (1..=2).contains(&args.len()) && imms[dst.0 as usize].is_none();
    fusable.then_some((*intrinsic, args.as_slice()))
}

/// Computes basic block layout order via depth-first traversal, arranging fall-through jumps along hot edges
/// and inverting loop condition branches so that loop bodies fall through while loop exits branch away.
fn layout<'t>(arena: &'t Arena, function: &Function<'_, '_>, to: &[usize], fusable: &[bool]) -> (AVec<'t, usize>, AVec<'t, bool>) {
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
            End::Jump(next, _) => stack.push(next.0 as usize),
            End::Branch { then, other, .. } => {
                let (then, other) = (to[then.0 as usize], to[other.0 as usize]);
                let invert = fusable[block] && recurs(arena, function, to, &placed, other) && !recurs(arena, function, to, &placed, then);
                inverted[block] = invert;
                stack.extend(if invert { [then, other] } else { [other, then] });
            }
            End::Return(_) | End::TailCall { .. } | End::TailPrim { .. } => {}
        }
    }
    (order, inverted)
}

/// Heuristically checks (up to a small bounded depth) whether all outgoing paths from block `start` lead to
/// an already placed block, indicating a backward loop edge.
fn recurs(arena: &Arena, function: &Function<'_, '_>, to: &[usize], placed: &[bool], start: usize) -> bool {
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
            End::Jump(next, _) => ways.push(next.0 as usize),
            End::Branch { then, other, .. } => ways.extend([then.0 as usize, other.0 as usize]),
            End::Return(_) | End::TailCall { .. } | End::TailPrim { .. } => return false,
        }
    }
    true
}

/// Computes the effective jump target for each basic block, bypassing intermediate blocks that contain only an unconditional jump.
fn forwards<'t>(arena: &'t Arena, function: &Function<'_, '_>) -> AVec<'t, usize> {
    let on = |index: usize| match &function.blocks[index] {
        block if index > 0 && block.params.is_empty() && block.insts.is_empty() => match &block.end {
            End::Jump(to, args) if args.is_empty() => Some(to.0 as usize),
            _ => None,
        },
        _ => None,
    };
    (0..function.blocks.len())
        .map(|index| {
            if on(index).is_none() {
                return index;
            }
            let (mut at, mut seen) = (index, ragwort_alloc::vec_in![arena; index]);
            while let Some(to) = on(at) {
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

struct Emitter<'m, 'a, 't, 'gc> {
    module: &'m mut Module<'a, 'gc>,
    arena: &'t Arena,
    ops: Vec<Op>,
    /// The instruction index where each run of instructions from one source site starts, with that site. Site 0 marks instructions with no known position.
    sited: Vec<(usize, u32)>,
    locs: AVec<'t, Option<Loc>>,
    uses: AVec<'t, u32>,
    imms: Imms<'t, 'gc>,
    to: AVec<'t, usize>,
    /// Reusable scratch buffers retained across blocks and parallel move sequences.
    /// `at` is a bitset of values active during backward block scanning; `seen` records modified indices for rapid resetting.
    at: AVec<'t, u64>,
    seen: AVec<'t, Val>,
    highs: AVec<'t, Option<u8>>,
    after: AVec<'t, Regs>,
    moves: AVec<'t, (Loc, Loc)>,
    /// Preferred register targets for singly-used values: records the destination block, instruction index,
    /// and target register position.
    aims: AVec<'t, Option<(u32, u32, Aim)>>,
    /// The starting opcode index of the basic block currently being emitted; moves cannot fuse across this boundary.
    fence: usize,
    /// Tracks which basic blocks have their test conditions fused into branch instructions, and which branch conditions are inverted.
    fusable: AVec<'t, bool>,
    inverted: AVec<'t, bool>,
    spill: Option<u8>,
    /// The first register index allocated for this function's local variables, following incoming parameters.
    first: u8,
    /// The bytecode offset where each basic block begins.
    starts: AVec<'t, usize>,
    /// Jump instructions with unresolved target offsets, patched once all block start positions are determined.
    jumps: AVec<'t, (usize, Block)>,
}

impl<'m, 'a, 't, 'gc> Emitter<'m, 'a, 't, 'gc> {
    /// Records that the instructions emitted from here on come from `site`.
    fn site(&mut self, site: u32) {
        if self.sited.last().map_or(0, |&(_, last)| last) != site {
            self.sited.push((self.ops.len(), site));
        }
    }

    fn block(&mut self, function: &Function<'_, 'gc>, index: usize, live: &Live<'_>, next: Option<usize>) -> Result<(), CompileError> {
        self.starts[index] = self.ops.len();
        self.fence = self.ops.len();
        let block = &function.blocks[index];
        let count = block.insts.len();
        let tail = self.tail(block);
        // Computes the set of active registers following each instruction, identifying the highest live register
        // to establish the frame base for nested calls.
        let mut taken = [0; WINDOW / 64];
        let arena = self.arena;
        let (mut at, mut seen, mut highs, mut after) = (
            std::mem::replace(&mut self.at, arena.vec()),
            std::mem::replace(&mut self.seen, arena.vec()),
            std::mem::replace(&mut self.highs, arena.vec()),
            std::mem::replace(&mut self.after, arena.vec()),
        );
        seen.clear();
        for &value in live.outs(index) {
            add(&mut at, value);
            seen.push(value);
            self.mark(&mut taken, value, true);
        }
        block.end.each_use(|value| {
            if add(&mut at, value) {
                seen.push(value);
                self.mark(&mut taken, value, true);
            }
        });
        self.aim_end(function, index);
        highs.clear();
        highs.resize(count, None);
        after.clear();
        after.resize(count, taken);
        for (i, inst) in block.insts.iter().enumerate().rev() {
            after[i] = taken;
            for &def in inst.defs() {
                remove(&mut at, def);
                self.mark(&mut taken, def, false);
            }
            highs[i] = highest(&taken);
            self.aim_args(index, i, inst, tail.is_some() && i + 1 == count);
            each_read(inst, &self.imms, |value| {
                if add(&mut at, value) {
                    seen.push(value);
                    self.mark(&mut taken, value, true);
                }
            });
        }
        seen.iter().for_each(|&value| remove(&mut at, value));
        let test = if self.fusable[index] { fused_test(block, &self.uses, &self.imms) } else { None };
        let insts = &block.insts[..count - usize::from(tail.is_some() || test.is_some())];
        for (j, inst) in insts.iter().enumerate() {
            if let &[def] = inst.defs()
                && !matches!(inst, Inst::Closures { .. })
            {
                self.aim(index, j, def, &mut highs, &mut after);
            }
            let base = highs[j].map_or(self.first, |high| self.first.max(high + 1));
            self.site(block.sites[j]);
            self.inst(inst, base)?;
        }
        (self.at, self.seen, self.highs, self.after) = (at, seen, highs, after);
        // An instruction fused into the end of the block is emitted there, and keeps its own site.
        let fused = tail.is_some() || test.is_some();
        self.site(if fused { block.sites[count - 1] } else { block.end_site });
        match (tail, test, &block.end) {
            (Some((prim, args)), _, _) => self.tail_prim(prim, args),
            (None, Some((intrinsic, args)), End::Branch { then, other, .. }) => {
                let branch_if = self.inverted[index];
                let (target, fall) = if branch_if { (*then, *other) } else { (*other, *then) };
                let op = match *args {
                    [a0] => Op::BranchIntrinsic1 { a: self.read(a0, 0), intrinsic, branch_if, offset: 0 },
                    [a0, a1] => {
                        let (left, right) = (self.read(a0, 0), self.read(a1, 1));
                        Op::BranchIntrinsic2 { a: left, b: right, intrinsic, branch_if, offset: 0 }
                    }
                    _ => unreachable!("a fused test takes 1 or 2 arguments"),
                };
                self.jump(op, target);
                self.go(fall, next);
                Ok(())
            }
            _ => self.end(function, &block.end, next),
        }
    }

    /// If `block` ends by returning the result of an intrinsic instruction, returns the intrinsic and its arguments
    /// so it can be emitted using a specialized tail-return opcode.
    fn tail<'b>(&self, block: &'b l5::BlockData<'_, 'gc>) -> Option<(Prim, &'b [Val])> {
        let (Some(Inst::Prim { dst, prim, args, spread: false }), End::Return(returned)) = (block.insts.last(), &block.end) else { return None };
        let tail = matches!(prim, Prim::Intrinsic(_)) && self.imms[dst.0 as usize].is_none();
        (tail && dst == returned && self.uses[dst.0 as usize] == 1).then_some((*prim, args.as_slice()))
    }

    fn tail_prim(&mut self, prim: Prim, args: &[Val]) -> Result<(), CompileError> {
        let count = args.len() as u8;
        match (prim, self.stage(self.first, None, args, true)) {
            (Prim::Intrinsic(intrinsic), Some(base)) => self.ops.push(Op::TailCallIntrinsic { base, args: count, intrinsic }),
            (Prim::Intrinsic(intrinsic), None) => {
                let base = self.list(args, None);
                self.ops.extend([Op::ApplyIntrinsic { base, args: 1, intrinsic }, Op::LoadAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]);
            }
            _ => unreachable!("only intrinsics return their own values"),
        }
        Ok(())
    }

    fn mark(&self, taken: &mut Regs, value: Val, to: bool) {
        if let Some(Loc::Reg(register)) = self.locs[value.0 as usize] {
            set_reg(taken, register, to);
        }
    }

    /// Registers target preferences for argument values staged by `inst` at instruction `at` in block `block`.
    fn aim_args(&mut self, block: usize, at: usize, inst: &Inst<'_, 'gc>, tail: bool) {
        let (head, args) = match inst {
            Inst::Call { f: callee, args, .. } => (Some(*callee), args),
            Inst::Prim { dst, prim, args, spread } if tail || self.stages(*dst, *prim, args.len(), *spread) => (None, args),
            _ => return,
        };
        for (position, &value) in head.iter().chain(args).enumerate() {
            let position = u8::try_from(position).unwrap_or(u8::MAX);
            self.wants(value, block, at, if tail { Aim::First(position) } else { Aim::Base(position) });
        }
    }

    /// Registers target preferences for values passed as block arguments by block `index`'s terminator.
    fn aim_end(&mut self, function: &Function<'_, 'gc>, index: usize) {
        let block = &function.blocks[index];
        let at = block.insts.len();
        match &block.end {
            End::Jump(to, args) => {
                for (param, &arg) in function.blocks[to.0 as usize].params.iter().zip(args) {
                    if let Some(Loc::Reg(register)) = self.locs[param.0 as usize] {
                        self.wants(arg, index, at, Aim::Reg(register));
                    }
                }
            }
            End::TailCall { f: callee, args } => {
                for (position, &value) in std::iter::once(callee).chain(args).enumerate() {
                    self.wants(value, index, at, Aim::First(u8::try_from(position).unwrap_or(u8::MAX)));
                }
            }
            End::TailPrim { args, .. } => {
                for (position, &value) in args.iter().enumerate() {
                    self.wants(value, index, at, Aim::First(u8::try_from(position).unwrap_or(u8::MAX)));
                }
            }
            End::Return(_) | End::Branch { .. } => {}
        }
    }

    fn wants(&mut self, value: Val, block: usize, at: usize, aim: Aim) {
        if self.uses[value.0 as usize] == 1 {
            self.aims[value.0 as usize] = Some((block as u32, at as u32, aim));
        }
    }

    /// Pre-assigns `value` (defined at instruction `j` in block `index`) directly to its preferred destination register,
    /// provided that register remains unallocated throughout the intervening range.
    fn aim(&mut self, index: usize, j: usize, value: Val, highs: &mut [Option<u8>], after: &mut [Regs]) {
        let Some((block, at, aim)) = self.aims[value.0 as usize] else { return };
        let at = at as usize;
        if block as usize != index || at <= j {
            return;
        }
        let first = usize::from(self.first);
        let target = match aim {
            Aim::Reg(register) => usize::from(register),
            Aim::First(position) => first + usize::from(position),
            Aim::Base(position) => highs[at].map_or(first, |high| first.max(usize::from(high) + 1)) + usize::from(position),
        };
        if target < first || target >= usize::from(LIMIT) {
            return;
        }
        let target = target as u8;
        if self.locs[value.0 as usize] == Some(Loc::Reg(target)) || after[j..at].iter().any(|regs| has_reg(regs, target)) {
            return;
        }
        self.locs[value.0 as usize] = Some(Loc::Reg(target));
        after[j..at].iter_mut().for_each(|regs| set_reg(regs, target, true));
        highs[j + 1..at].iter_mut().for_each(|high| *high = Some(high.map_or(target, |current| current.max(target))));
    }

    /// Determines whether the primitive producing `dst` requires its arguments to be staged in a contiguous sequence of registers.
    fn stages(&self, dst: Val, prim: Prim, args: usize, spread: bool) -> bool {
        match prim {
            Prim::Slot(..) => false,
            _ if self.imms[dst.0 as usize].is_some() => false,
            Prim::Intrinsic(_) if !spread => args > 3,
            _ => true,
        }
    }

    /// Emits bytecode for instruction `inst`. Outgoing calls are staged at or above register index `base`.
    fn inst(&mut self, inst: &Inst<'_, 'gc>, base: u8) -> Result<(), CompileError> {
        match inst {
            Inst::Const(dst, value) => {
                if self.used(*dst) {
                    let index = self.module.constant(*value)?;
                    self.write(*dst, |dst| Op::LoadConst { dst, index });
                }
            }
            Inst::Upvalue(dst, index) => {
                if self.used(*dst) {
                    self.write(*dst, |dst| Op::LoadUpvalue { dst, index: *index });
                }
            }
            Inst::Prim { dst, prim, args, spread } => self.prim(*dst, *prim, args, *spread, base)?,
            Inst::Call { dst, f: callee, args } => {
                if let Some(base) = self.stage(base, Some(*callee), args, false) {
                    self.ops.push(Op::Call { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(*callee));
                    self.ops.push(Op::CallRequest { base: SCRATCH, args: 2, request: Request::Apply });
                }
                self.take(*dst);
            }
            Inst::Closures { dsts, codes } => self.closures(dsts, codes)?,
        }
        Ok(())
    }

    fn prim(&mut self, dst: Val, prim: Prim, args: &[Val], spread: bool, base: u8) -> Result<(), CompileError> {
        if let Prim::Slot(op, slot) = prim {
            return self.slot(dst, op, slot, args);
        }
        if let Some(imm) = self.imms[dst.0 as usize] {
            let kind = match imm {
                Imm::FieldOf(kind, _) => self.module.constant(kind)?,
                Imm::Add(_) | Imm::Field(_) => 0,
            };
            let operand = self.read(args[0], 0);
            self.write(dst, |dst| match imm {
                Imm::Add(imm) => Op::AddImm { dst, a: operand, imm },
                Imm::Field(field) => Op::StructField { dst, a: operand, k: field },
                Imm::FieldOf(_, field) => Op::StructRef { dst, a: operand, k: field, kind },
            });
            return Ok(());
        }
        if !spread {
            match (prim, args) {
                (Prim::Intrinsic(intrinsic), &[a0]) => {
                    let operand = self.read(a0, 0);
                    self.write(dst, |dst| Op::CallIntrinsic1 { dst, a: operand, intrinsic });
                    return Ok(());
                }
                (Prim::Intrinsic(intrinsic), &[a0, a1]) => {
                    let (left, right) = (self.read(a0, 0), self.read(a1, 1));
                    self.write(dst, |dst| Op::CallIntrinsic2 { dst, a: left, b: right, intrinsic });
                    return Ok(());
                }
                (Prim::Intrinsic(intrinsic), &[a0, a1, a2]) => {
                    let (first, second, third) = (self.read(a0, 0), self.read(a1, 1), self.read(a2, 2));
                    self.write(dst, |dst| Op::CallIntrinsic3 { dst, a: first, b: second, c: third, intrinsic });
                    return Ok(());
                }
                _ => {}
            }
        }
        let host = if let Prim::Host(def) = prim { Some(self.module.host(def)?) } else { None };
        let count = args.len() as u8;
        let staged = self.stage(base, None, args, matches!(prim, Prim::Intrinsic(_)));
        let op = match (prim, spread, staged) {
            (Prim::Intrinsic(intrinsic), false, Some(base)) => Op::CallIntrinsic { base, args: count, intrinsic },
            (Prim::Intrinsic(intrinsic), true, Some(base)) => Op::ApplyIntrinsic { base, args: count, intrinsic },
            (Prim::Intrinsic(intrinsic), _, None) => Op::ApplyIntrinsic { base: self.spread(args, spread), args: 1, intrinsic },
            (Prim::Request(request), false, Some(base)) => Op::CallRequest { base, args: count, request },
            (Prim::Request(request), true, Some(base)) => Op::ApplyRequest { base, args: count, request },
            (Prim::Request(request), _, None) => Op::ApplyRequest { base: self.spread(args, spread), args: 1, request },
            (Prim::Host(_), false, Some(base)) => Op::CallHost { base, args: count, host: host.expect("looked up") },
            (Prim::Host(_), false, None) => return Err(CompileError::TooManyArguments),
            (Prim::Host(_) | Prim::Slot(..), true, _) | (Prim::Slot(..), false, _) => {
                unreachable!("lowering spreads no host function or slot access")
            }
        };
        self.ops.push(op);
        self.take(dst);
        Ok(())
    }

    /// Emits a load or store operation for module variable `slot`. For stores, the value to write is provided in `args`.
    fn slot(&mut self, dst: Val, op: SlotOp, slot: u32, args: &[Val]) -> Result<(), CompileError> {
        let len = self.module.owner.map_or(0, |module| module.items(self.module.mc).len());
        if slot as usize >= len {
            return Err(CompileError::UnknownSlot(slot));
        }
        match (op, args) {
            (SlotOp::Load, []) => {
                if self.used(dst) {
                    self.write(dst, |dst| Op::LoadSlot { dst, slot });
                }
            }
            (SlotOp::LoadChecked, []) => self.write(dst, |dst| Op::LoadSlotChecked { dst, slot }),
            (SlotOp::Store | SlotOp::StoreChecked, &[value]) => {
                let src = self.read(value, 0);
                self.ops.push(if op == SlotOp::Store { Op::StoreSlot { src, slot } } else { Op::StoreSlotChecked { src, slot } });
                if self.used(dst) {
                    let index = self.module.constant(Value::VOID)?;
                    self.write(dst, |dst| Op::LoadConst { dst, index });
                }
            }
            _ => unreachable!("lowering checks a slot access's arguments"),
        }
        Ok(())
    }

    #[inline(never)]
    fn closures(&mut self, dsts: &[Val], codes: &[Code<'_>]) -> Result<(), CompileError> {
        // A closure with no captured upvalues is emitted as a compile-time constant closure object.
        if codes.iter().all(|code| code.captures.is_empty()) {
            for (&dst, code) in dsts.iter().zip(codes) {
                if self.used(dst) {
                    let index = self.module.defer(code.function, Vec::new(), true)?;
                    self.write(dst, |dst| Op::LoadConst { dst, index });
                }
            }
            return Ok(());
        }
        if let (&[dst], [code]) = (dsts, codes) {
            let captures = self.captures(&code.captures, &[]);
            let index = self.module.defer(code.function, captures, false)?;
            self.write(dst, |dst| Op::NewClosure { dst, count: 1, code: index });
            return Ok(());
        }
        // Mutually recursive closure groups are staged in scratch registers so they can capture one another's references.
        if codes.len() > STAGE {
            return Err(CompileError::TooManyRegisters);
        }
        let peers: Vec<(Val, u8)> = dsts.iter().copied().zip(SCRATCH..).collect();
        let all: Vec<Vec<Capture>> = codes.iter().map(|code| self.captures(&code.captures, &peers)).collect();
        let mut first = None;
        for (code, captures) in codes.iter().zip(all) {
            let slot = self.module.defer(code.function, captures, false)?;
            first.get_or_insert(slot);
        }
        let code = first.expect("a group has closures");
        self.ops.push(Op::NewClosure { dst: SCRATCH, count: codes.len() as u8, code });
        for (dst, register) in peers {
            if self.used(dst) {
                self.mov(self.loc(dst), Loc::Reg(register));
            }
        }
        Ok(())
    }

    fn captures(&self, captured: &[Captured], peers: &[(Val, u8)]) -> Vec<Capture> {
        let capture = |&source: &Captured| match source {
            Captured::Upvalue(index) => Capture::Upvalue(index),
            Captured::Val(value) => match peers.iter().find(|&&(peer, _)| peer == value) {
                Some(&(_, register)) => Capture::Register(register),
                None => match self.loc(value) {
                    Loc::Reg(register) => Capture::Register(register),
                    Loc::Slot(slot) => Capture::Spill { spill: self.spill_reg(), slot },
                },
            },
        };
        captured.iter().map(capture).collect()
    }

    /// Emits bytecode for block terminator `end`. If the target block matches `next`, redundant jumps can fall through.
    fn end(&mut self, function: &Function<'_, 'gc>, end: &End<'_>, next: Option<usize>) -> Result<(), CompileError> {
        match end {
            End::Return(value) => {
                let src = self.read(*value, 0);
                self.ops.push(Op::Return { src });
            }
            End::Jump(to, args) => {
                let params = &function.blocks[to.0 as usize].params;
                let mut moves = std::mem::replace(&mut self.moves, self.arena.vec());
                moves.clear();
                moves.extend(params.iter().zip(args).filter_map(|(param, &arg)| Some((self.locs[param.0 as usize]?, self.loc(arg)))));
                self.parallel(moves);
                self.go(*to, next);
            }
            End::Branch { test, then, other } => {
                let test = self.read(*test, 0);
                self.jump(Op::JumpIfFalse { test, offset: 0 }, *other);
                self.go(*then, next);
            }
            End::TailCall { f: callee, args } => {
                if let Some(base) = self.stage(self.first, Some(*callee), args, false) {
                    self.ops.push(Op::TailCall { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(*callee));
                    self.ops.push(Op::TailCallRequest { base: SCRATCH, args: 2, request: Request::Apply });
                }
            }
            End::TailPrim { prim: Prim::Request(request), args, spread } => {
                let count = args.len() as u8;
                let request = *request;
                match (self.stage(self.first, None, args, false), spread) {
                    // A guard continuation retains its caller frame; invoking it from that frame allows the VM
                    // to reuse the existing handler in place without creating a new prompt.
                    (Some(base), false) if matches!(request, Request::Guard | Request::GuardQuiet) => self.ops.extend([
                        Op::CallRequest { base, args: count, request },
                        Op::LoadAcc { dst: SCRATCH },
                        Op::Return { src: SCRATCH },
                    ]),
                    (Some(base), false) => self.ops.push(Op::TailCallRequest { base, args: count, request }),
                    (Some(base), true) => self.ops.push(Op::TailApplyRequest { base, args: count, request }),
                    (None, _) => {
                        let base = self.spread(args, *spread);
                        self.ops.push(Op::TailApplyRequest { base, args: 1, request });
                    }
                }
            }
            End::TailPrim { prim: Prim::Host(def), args, .. } => {
                let host = self.module.host(def)?;
                let base = self.stage(self.first, None, args, false).ok_or(CompileError::TooManyArguments)?;
                self.ops.push(Op::TailCallHost { base, args: args.len() as u8, host });
            }
            End::TailPrim { .. } => unreachable!("only requests and host calls are tail ends"),
        }
        Ok(())
    }

    fn jump(&mut self, op: Op, to: Block) {
        self.jumps.push((self.ops.len(), Block(self.to[to.0 as usize] as u32)));
        self.ops.push(op);
    }

    /// Emits an unconditional jump to block `to`, omitting the instruction if execution naturally falls through to `next`.
    fn go(&mut self, to: Block, next: Option<usize>) {
        if Some(self.to[to.0 as usize]) != next {
            self.jump(Op::Jump { offset: 0 }, to);
        }
    }

    /// Stages `head` (if present) followed by `vals` into contiguous registers starting at or above `base`.
    /// If they do not fit in available local registers, attempts staging into scratch registers.
    /// Returns the starting register index, or `None` if argument count exceeds available scratch registers.
    /// Values already arranged consecutively in eligible registers remain in place.
    fn stage(&mut self, base: u8, head: Option<Val>, vals: &[Val], free: bool) -> Option<u8> {
        let count = usize::from(head.is_some()) + vals.len();
        if let Some(start) = self.row(head.iter().chain(vals))
            && (start >= base || free && start >= ARGS)
        {
            return Some(start);
        }
        let base = if usize::from(base) + count <= usize::from(LIMIT) {
            base
        } else if count <= STAGE {
            SCRATCH
        } else {
            return None;
        };
        let mut moves = std::mem::replace(&mut self.moves, self.arena.vec());
        moves.clear();
        moves.extend(head.iter().chain(vals).zip(base..).map(|(&value, register)| (Loc::Reg(register), self.loc(value))));
        self.parallel(moves);
        Some(base)
    }

    /// Returns the starting register index if `vals` already occupy a contiguous sequence of hardware registers, or `None` otherwise.
    fn row<'v>(&self, mut vals: impl Iterator<Item = &'v Val>) -> Option<u8> {
        let Loc::Reg(start) = self.loc(*vals.next()?) else { return None };
        let mut next = start;
        for &value in vals {
            next = next.checked_add(1)?;
            if self.loc(value) != Loc::Reg(next) {
                return None;
            }
        }
        Some(start)
    }

    /// Builds a Scheme list from `args` into a scratch register and returns that register. If `spread` is true,
    /// prepends all leading arguments onto the final argument (which must already evaluate to a list).
    fn spread(&mut self, args: &[Val], spread: bool) -> u8 {
        if spread {
            let (last, rest) = args.split_last().expect("a spread call has a list");
            self.list(rest, Some(*last))
        } else {
            self.list(args, None)
        }
    }

    fn list(&mut self, vals: &[Val], tail: Option<Val>) -> u8 {
        let list = SCRATCH + 1;
        match tail {
            Some(tail) => self.mov(Loc::Reg(list), self.loc(tail)),
            None => {
                let index = self.module.constant(Value::NIL).expect("the constants have room for '()");
                self.ops.push(Op::LoadConst { dst: list, index });
            }
        }
        for &value in vals.iter().rev() {
            self.mov(Loc::Reg(SCRATCH), self.loc(value));
            self.ops.push(Op::CallIntrinsic2 { dst: list, a: SCRATCH, b: list, intrinsic: Intrinsic::Cons });
        }
        list
    }

    /// Emits a sequence of register/slot moves simulating parallel assignment, resolving cycles using a scratch register.
    /// Retains the allocated vector buffer for future reuse.
    fn parallel(&mut self, mut moves: AVec<'t, (Loc, Loc)>) {
        moves.retain(|(to, from)| to != from);
        while !moves.is_empty() {
            if let Some(i) = (0..moves.len()).find(|&i| !moves.iter().any(|&(_, from)| from == moves[i].0)) {
                let (to, from) = moves.remove(i);
                self.mov(to, from);
            } else {
                // Breaks a cyclic dependency permutation by buffering one source location through a scratch register.
                let from = moves[0].1;
                self.mov(Loc::Reg(SCRATCH), from);
                for entry in &mut moves {
                    if entry.1 == from {
                        entry.1 = Loc::Reg(SCRATCH);
                    }
                }
            }
        }
        self.moves = moves;
    }

    fn mov(&mut self, to: Loc, from: Loc) {
        match (to, from) {
            _ if to == from => {}
            (Loc::Reg(dst2), Loc::Reg(src2)) => match (self.ops.len() > self.fence, self.ops.last_mut()) {
                (true, Some(last @ &mut Op::Move { dst: dst1, src: src1 })) if dst1 != dst2 && src2 != dst1 => {
                    *last = Op::Move2 { dst1, src1, dst2, src2 };
                }
                _ => self.ops.push(Op::Move { dst: dst2, src: src2 }),
            },
            (Loc::Reg(dst), Loc::Slot(slot)) => self.ops.push(Op::LoadSpill { dst, spill: self.spill_reg(), slot }),
            (Loc::Slot(slot), Loc::Reg(src)) => self.ops.push(Op::StoreSpill { src, spill: self.spill_reg(), slot }),
            (Loc::Slot(to), Loc::Slot(from)) => {
                let spill = self.spill_reg();
                self.ops.extend([Op::LoadSpill { dst: SCRATCH + 1, spill, slot: from }, Op::StoreSpill { src: SCRATCH + 1, spill, slot: to }]);
            }
        }
    }

    fn used(&self, value: Val) -> bool {
        self.uses[value.0 as usize] > 0
    }

    fn loc(&self, value: Val) -> Loc {
        self.locs[value.0 as usize].expect("a value used has a place")
    }

    fn spill_reg(&self) -> u8 {
        self.spill.expect("only a function with a spill has slots")
    }

    /// Moves the call result from the accumulator register into destination `dst`, if `dst` is used.
    fn take(&mut self, dst: Val) {
        if self.used(dst) {
            self.write(dst, |dst| Op::LoadAcc { dst });
        }
    }

    /// Resolves the physical register holding operand value `value` for instruction input `input`, loading spilled values into scratch if necessary.
    fn read(&mut self, value: Val, input: u8) -> u8 {
        match self.loc(value) {
            Loc::Reg(register) => register,
            Loc::Slot(slot) => {
                let dst = SCRATCH + input;
                self.ops.push(Op::LoadSpill { dst, spill: self.spill_reg(), slot });
                dst
            }
        }
    }

    /// Emits `op` targeting the physical register assigned to `value`, or redirects to a scratch register if `value` is unused.
    fn write(&mut self, value: Val, op: impl FnOnce(u8) -> Op) {
        match self.locs[value.0 as usize].filter(|_| self.used(value)) {
            Some(Loc::Reg(register)) => self.ops.push(op(register)),
            Some(Loc::Slot(slot)) => {
                let spill = self.spill_reg();
                self.ops.extend([op(SCRATCH), Op::StoreSpill { src: SCRATCH, spill, slot }]);
            }
            None => self.ops.push(op(SCRATCH)),
        }
    }
}
