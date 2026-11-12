//! Pass 9 (`L5 -> Closure`): register allocation and bytecode emission from [`L5`](crate::l5).
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
const STAGE: usize = WINDOW / 4;
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
    for &c in &module.codes {
        c.set_constants(mc, table);
    }
    if !module.lines.is_empty() {
        let sites = module.sites()?;
        for &c in &module.codes {
            c.set_sites(mc, sites);
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

fn has(set: &[u64], v: Val) -> bool {
    set[v.0 as usize / 64] & (1 << (v.0 % 64)) != 0
}

/// Inserts value `v` into bitset `set`, returning `true` if `v` was not previously present.
fn add(set: &mut [u64], v: Val) -> bool {
    let (word, bit) = (&mut set[v.0 as usize / 64], 1 << (v.0 % 64));
    let new = *word & bit == 0;
    *word |= bit;
    new
}

fn remove(set: &mut [u64], v: Val) {
    set[v.0 as usize / 64] &= !(1 << (v.0 % 64));
}

/// A bitset representing a set of physical registers within the register window (`WINDOW`).
type Regs = [u64; WINDOW / 64];

fn has_reg(regs: &Regs, r: u8) -> bool {
    regs[usize::from(r) / 64] & (1 << (r % 64)) != 0
}

fn set_reg(regs: &mut Regs, r: u8, to: bool) {
    let (word, bit) = (&mut regs[usize::from(r) / 64], 1 << (r % 64));
    *word = if to { *word | bit } else { *word & !bit };
}

fn highest(regs: &Regs) -> Option<u8> {
    let i = regs.iter().rposition(|&w| w != 0)?;
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

fn imms<'t, 'gc>(arena: &'t Arena, f: &Function<'_, 'gc>) -> Imms<'t, 'gc> {
    let mut constants: AVec<'t, Option<Value<'gc>>> = arena.vec_of(None, f.values as usize);
    let mut imms = arena.vec_of(None, f.values as usize);
    for inst in f.blocks.iter().flat_map(|block| &block.insts) {
        match inst {
            Inst::Const(dst, value) => constants[dst.0 as usize] = Some(*value),
            Inst::Prim { dst, prim: Prim::Intrinsic(intrinsic), args, spread: false } => {
                let fixnum = |v: &Val| constants[v.0 as usize].and_then(|k| k.as_fixnum());
                imms[dst.0 as usize] = match (intrinsic, args.as_slice()) {
                    (Intrinsic::Add, [_, k]) => fixnum(k).and_then(|k| i16::try_from(k).ok()).map(Imm::Add),
                    (Intrinsic::StructField | Intrinsic::StructFixedField, [_, k]) => fixnum(k).and_then(|k| u16::try_from(k).ok()).map(Imm::Field),
                    (Intrinsic::StructRef, [_, kind, k]) => constants[kind.0 as usize].zip(fixnum(k).and_then(|k| u8::try_from(k).ok())).map(|(kind, k)| Imm::FieldOf(kind, k)),
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
fn each_read(inst: &Inst<'_, '_>, imms: &Imms<'_, '_>, mut f: impl FnMut(Val)) {
    match inst {
        Inst::Prim { dst, args, .. } if imms[dst.0 as usize].is_some() => f(args[0]),
        Inst::Closures { dsts, .. } => inst.each_use(|v| {
            if !dsts.contains(&v) {
                f(v);
            }
        }),
        _ => inst.each_use(f),
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
    fn outs(&self, b: usize) -> &[Val] {
        &self.outs[self.starts[b]..self.starts[b + 1]]
    }
}

/// Sentinel value representing an unassigned block index, or indicating that a value is defined at function entry.
const NOWHERE: u32 = u32::MAX;

/// Computes live-out value sets for each basic block by traversing backwards from each use site
/// to its definition block. This sparse backward traversal avoids the memory overhead of a full dense block-by-value matrix.
fn liveness<'t>(arena: &'t Arena, f: &Function<'_, '_>, imms: &Imms<'_, '_>) -> Live<'t> {
    let (n, values) = (f.blocks.len(), f.values as usize);
    let mut preds = arena.vec_of(arena.vec(), n);
    for (b, block) in f.blocks.iter().enumerate() {
        for to in block.end.successors() {
            preds[to.0 as usize].push(b);
        }
    }
    let mut home = arena.vec_of(NOWHERE, values);
    for (b, block) in f.blocks.iter().enumerate() {
        block.params.iter().for_each(|p| home[p.0 as usize] = b as u32);
        block.insts.iter().flat_map(|inst| inst.defs()).for_each(|d| home[d.0 as usize] = b as u32);
    }
    // Identifies upwards-exposed values: values used in a block before being defined in that block.
    let mut exposed = arena.vec();
    for (b, block) in f.blocks.iter().enumerate() {
        let mut note = |u: Val| {
            if home[u.0 as usize] != b as u32 {
                exposed.push((u.0, b as u32));
            }
        };
        block.insts.iter().for_each(|inst| each_read(inst, imms, &mut note));
        block.end.each_use(&mut note);
    }
    exposed.sort_unstable();
    // Tracks the most recent SSA value processed for each block's live-in and live-out sets to avoid redundant visits.
    let (mut into, mut out) = (arena.vec_of(NOWHERE, n), arena.vec_of(NOWHERE, n));
    let (mut found, mut stack) = (arena.vec(), arena.vec());
    for &(v, b) in exposed.iter() {
        if into[b as usize] == v {
            continue;
        }
        into[b as usize] = v;
        stack.push(b as usize);
        while let Some(b) = stack.pop() {
            for &p in &preds[b] {
                if out[p] != v {
                    out[p] = v;
                    found.push((p, Val(v)));
                }
                if home[v as usize] != p as u32 && into[p] != v {
                    into[p] = v;
                    stack.push(p);
                }
            }
        }
    }
    // Groups live-out values by basic block, sorted by SSA value index to build compact contiguous slices.
    let mut starts = arena.vec_of(0, n + 1);
    found.iter().for_each(|&(b, _)| starts[b + 1] += 1);
    (0..n).for_each(|b| starts[b + 1] += starts[b]);
    let mut next = starts.clone();
    let mut outs = arena.vec_of(Val(0), found.len());
    for &(b, v) in found.iter() {
        outs[next[b]] = v;
        next[b] += 1;
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
    f: &Function<'_, '_>,
    live: &Live<'_>,
    imms: &Imms<'_, '_>,
    pinned: &[bool],
    uses: &[u32],
    defined: &[Val],
) -> Colours<'t> {
    let n = f.blocks.len();
    let mut children = arena.vec_of(arena.vec(), n);
    if n > 1 {
        let idom = l5::dominators(&f.blocks, &live.preds).expect("lowering reaches every block");
        for b in 1..n {
            children[idom[b]].push(b);
        }
    }
    let colours = Colours { of: arena.vec_of(None, f.values as usize), count: 0 };
    let mut c = Colouring { colours, taken: arena.vec(), pinned, uses };
    // Bitset of values currently live during backward block scanning, accompanied by an undo log of visited values.
    let (mut at, mut seen) = (arena.vec_of(0, live.words), arena.vec());
    // Records values whose live ranges terminate at instruction `i`, indexed via `dying[spans[i].0..spans[i].1]`.
    let (mut dying, mut spans) = (arena.vec(), arena.vec());
    let mut stack = ragwort_alloc::vec_in![arena; 0];
    while let Some(b) = stack.pop() {
        stack.extend(children[b].iter().rev().copied());
        let block = &f.blocks[b];
        seen.clear();
        for &v in live.outs(b) {
            add(&mut at, v);
            seen.push(v);
        }
        block.end.each_use(|u| {
            if add(&mut at, u) {
                seen.push(u);
            }
        });
        dying.clear();
        spans.clear();
        spans.resize(block.insts.len(), (0, 0));
        for (i, inst) in block.insts.iter().enumerate().rev() {
            let start = dying.len();
            each_read(inst, imms, |u| {
                if !has(&at, u) && !dying[start..].contains(&u) {
                    dying.push(u);
                }
            });
            spans[i] = (start, dying.len());
            for &d in inst.defs() {
                remove(&mut at, d);
            }
            each_read(inst, imms, |u| {
                if add(&mut at, u) {
                    seen.push(u);
                }
            });
        }
        // Reclaims colors for values that are live-in to the block, then assigns colors to uncolored block parameters.
        c.taken.clear();
        c.taken.resize(c.colours.count as usize, false);
        for &v in seen.iter() {
            if has(&at, v)
                && let Some(colour) = c.colours.of[v.0 as usize]
            {
                c.taken[colour as usize] = true;
            }
            remove(&mut at, v);
        }
        if b == 0 {
            defined.iter().for_each(|&v| c.take(v));
        }
        block.params.iter().for_each(|&p| c.take(p));
        for (inst, &(start, end)) in block.insts.iter().zip(&spans) {
            // The closure object's destination register is defined prior to capturing environment values.
            if let Inst::Closures { .. } = inst {
                inst.defs().iter().for_each(|&d| c.take(d));
                dying[start..end].iter().for_each(|&u| c.free(u));
            } else {
                dying[start..end].iter().for_each(|&u| c.free(u));
                inst.defs().iter().for_each(|&d| c.take(d));
            }
        }
    }
    c.colours
}

/// State for greedy register coloring: maintains assigned colors and tracks which colors are currently occupied.
struct Colouring<'t, 'f> {
    colours: Colours<'t>,
    taken: AVec<'t, bool>,
    pinned: &'f [bool],
    uses: &'f [u32],
}

impl Colouring<'_, '_> {
    /// Assigns the lowest available register color to value `v`, provided `v` is used and not pinned to a fixed register.
    fn take(&mut self, v: Val) {
        if self.pinned[v.0 as usize] || self.uses[v.0 as usize] == 0 {
            return;
        }
        let c = self.taken.iter().position(|&t| !t).unwrap_or(self.taken.len());
        if c == self.taken.len() {
            self.taken.push(false);
        }
        self.taken[c] = true;
        self.colours.of[v.0 as usize] = Some(c as u32);
        self.colours.count = self.colours.count.max(c as u32 + 1);
    }

    fn free(&mut self, v: Val) {
        if let Some(c) = self.colours.of[v.0 as usize] {
            self.taken[c as usize] = false;
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
        let hosts = self.owner.and_then(|m| m.hosts(self.mc)).map_or(&[][..], |h| &h[..]);
        let i = hosts.iter().position(|&h| h == def).ok_or(CompileError::UnknownHost(def))?;
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

    /// Emits bytecode for function `f`, fusing 1- and 2-argument intrinsic tests into conditional branches
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
            let Inlined { lambda, call } = self.names.sites.inlined[i];
            let name = self.item(self.names.get(lambda).name.unwrap_or(Value::FALSE));
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

    fn function(&mut self, f: &Function<'_, 'gc>, captures: &[Capture]) -> Result<Gc<'gc, Bytecode>, CompileError> {
        let (constants, codes, pending) = (self.constants.len(), self.codes.len(), self.pending.len());
        if let Some(code) = self.attempt(f, captures, true)? {
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
        Ok(self.attempt(f, captures, false)?.expect("without fused branches every jump has an i32 offset"))
    }

    fn attempt(&mut self, f: &Function<'_, 'gc>, captures: &[Capture], near: bool) -> Result<Option<Gc<'gc, Bytecode>>, CompileError> {
        let (n, optional) = (f.params.len() as u64, u64::from(f.optional));
        let shape = Shape { required: n - optional, optional, rest: f.rest.is_some() };
        // Optional parameters must reside in frame registers; reject parameter shapes exceeding `MAX_PARAMS`.
        if optional > 0 && shape.slots() > u64::from(MAX_PARAMS) {
            return Err(CompileError::TooManyRegisters);
        }
        let arity = shape.encode().ok_or(CompileError::TooManyRegisters)?;
        let link = frame::link_slot(arity);
        let values = f.values as usize;
        // Scratch arena for intra-function compiler data structures, deallocated immediately after function emission.
        let scratch = Arena::new();
        let arena = &scratch;
        let mut fixed = arena.vec_of(None, values);
        fixed[f.this.0 as usize] = Some(CLOSURE);
        let all: AVec<'_, Val> = f.params.iter().chain(&f.rest).copied().collect_in(arena);
        let list = ARGS + MAX_PARAMS - 1;
        // When parameter count exceeds available frame registers, the final register stores overflow arguments as a list.
        let unpacked = if all.len() <= usize::from(MAX_PARAMS) {
            all.iter().zip(ARGS..).for_each(|(v, r)| fixed[v.0 as usize] = Some(r));
            &[][..]
        } else {
            let keep = usize::from(MAX_PARAMS - 1);
            f.params[..keep].iter().zip(ARGS..).for_each(|(v, r)| fixed[v.0 as usize] = Some(r));
            f.rest.iter().for_each(|v| fixed[v.0 as usize] = Some(list));
            &f.params[keep..]
        };
        let imms = imms(arena, f);
        let mut uses = arena.vec_of(0u32, values);
        for block in &f.blocks {
            block.insts.iter().for_each(|inst| each_read(inst, &imms, |u| uses[u.0 as usize] += 1));
            block.end.each_use(|u| uses[u.0 as usize] += 1);
        }
        let live = liveness(arena, f, &imms);
        let pinned: AVec<'_, bool> = fixed.iter().map(Option::is_some).collect_in(arena);
        let colours = colour(arena, f, &live, &imms, &pinned, &uses, unpacked);

        let own = LIMIT.saturating_sub(link + 1);
        let (spill, first) = if colours.count > u32::from(own) { (Some(link + 1), link + 2) } else { (None, link + 1) };
        let own = u32::from(LIMIT.saturating_sub(first));
        let locs = fixed
            .iter()
            .zip(&colours.of)
            .map(|(&r, &c)| match (r, c) {
                (Some(r), _) => Some(Loc::Reg(r)),
                (None, Some(c)) if c < own => Some(Loc::Reg(first + c as u8)),
                (None, Some(c)) => Some(Loc::Slot(c - own)),
                (None, None) => None,
            })
            .collect_in(arena);
        let to = forwards(arena, f);
        let fusable: AVec<'_, bool> = f.blocks.iter().map(|block| near && fused_test(block, &uses, &imms).is_some()).collect_in(arena);
        let (order, inverted) = layout(arena, f, &to, &fusable);
        let mut e = Emitter {
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
            starts: arena.vec_of(0, f.blocks.len()),
            jumps: arena.vec(),
            sited: Vec::new(),
        };
        if let Some(dst) = spill {
            e.ops.push(Op::NewSpill { dst, count: colours.count - own });
        }
        for &v in unpacked {
            if e.used(v) {
                e.write(v, |dst| Op::CallIntrinsic1 { dst, a: list, intrinsic: Intrinsic::Car });
            }
            e.ops.push(Op::CallIntrinsic1 { dst: list, a: list, intrinsic: Intrinsic::Cdr });
        }
        for (i, &b) in order.iter().enumerate() {
            e.block(f, b, &live, order.get(i + 1).copied())?;
        }
        let Emitter { mut ops, mut starts, mut jumps, mut sited, .. } = e;
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
            starts.iter_mut().for_each(|s| *s = moved[*s]);
            sited.iter_mut().for_each(|(pc, _)| *pc = moved[*pc]);
            jumps = jumps.into_iter().filter(|(at, _)| !gone.contains(at)).map(|(at, to)| (moved[at], to)).collect_in(arena);
        }
        for (at, to) in jumps {
            let offset = i32::try_from(starts[to.0 as usize] as isize - (at as isize + 1)).expect("functions are shorter than 2^31 ops");
            match &mut ops[at] {
                Op::Jump { offset: o } | Op::JumpIfFalse { offset: o, .. } => *o = offset,
                Op::BranchIntrinsic1 { offset: o, .. } | Op::BranchIntrinsic2 { offset: o, .. } => match i16::try_from(offset) {
                    Ok(offset) => *o = offset,
                    Err(_) => return Ok(None),
                },
                _ => unreachable!("only jumps go to blocks"),
            }
        }
        let mc = self.mc;
        // A function without a lambda ID is the code of a top-level form, which the trace of an error tells apart from a procedure.
        let described = f.id.map(|id| self.names.get(id)).unwrap_or_default();
        let name = match f.id {
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
fn layout<'t>(arena: &'t Arena, f: &Function<'_, '_>, to: &[usize], fusable: &[bool]) -> (AVec<'t, usize>, AVec<'t, bool>) {
    let n = f.blocks.len();
    let (mut order, mut placed, mut inverted) = (AVec::with_capacity_in(n, arena), arena.vec_of(false, n), arena.vec_of(false, n));
    let mut stack = ragwort_alloc::vec_in![arena; 0];
    while let Some(b) = stack.pop() {
        let b = to[b];
        if placed[b] {
            continue;
        }
        placed[b] = true;
        order.push(b);
        match &f.blocks[b].end {
            End::Jump(next, _) => stack.push(next.0 as usize),
            End::Branch { then, other, .. } => {
                let (then, other) = (to[then.0 as usize], to[other.0 as usize]);
                let invert = fusable[b] && recurs(arena, f, to, &placed, other) && !recurs(arena, f, to, &placed, then);
                inverted[b] = invert;
                stack.extend(if invert { [then, other] } else { [other, then] });
            }
            End::Return(_) | End::TailCall { .. } | End::TailPrim { .. } => {}
        }
    }
    (order, inverted)
}

/// Heuristically checks (up to a small bounded depth) whether all outgoing paths from block `b` lead to
/// an already placed block, indicating a backward loop edge.
fn recurs(arena: &Arena, f: &Function<'_, '_>, to: &[usize], placed: &[bool], b: usize) -> bool {
    let mut ways = ragwort_alloc::vec_in![arena; b];
    let mut seen = 0;
    while let Some(b) = ways.pop() {
        let b = to[b];
        if placed[b] {
            continue;
        }
        seen += 1;
        if seen > 64 {
            return false;
        }
        match &f.blocks[b].end {
            End::Jump(next, _) => ways.push(next.0 as usize),
            End::Branch { then, other, .. } => ways.extend([then.0 as usize, other.0 as usize]),
            End::Return(_) | End::TailCall { .. } | End::TailPrim { .. } => return false,
        }
    }
    true
}

/// Computes the effective jump target for each basic block, bypassing intermediate blocks that contain only an unconditional jump.
fn forwards<'t>(arena: &'t Arena, f: &Function<'_, '_>) -> AVec<'t, usize> {
    let on = |b: usize| match &f.blocks[b] {
        block if b > 0 && block.params.is_empty() && block.insts.is_empty() => match &block.end {
            End::Jump(to, args) if args.is_empty() => Some(to.0 as usize),
            _ => None,
        },
        _ => None,
    };
    (0..f.blocks.len())
        .map(|b| {
            if on(b).is_none() {
                return b;
            }
            let (mut at, mut seen) = (b, ragwort_alloc::vec_in![arena; b]);
            while let Some(to) = on(at) {
                if seen.contains(&to) {
                    return b;
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

    fn block(&mut self, f: &Function<'_, 'gc>, b: usize, live: &Live<'_>, next: Option<usize>) -> Result<(), CompileError> {
        self.starts[b] = self.ops.len();
        self.fence = self.ops.len();
        let block = &f.blocks[b];
        let n = block.insts.len();
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
        for &v in live.outs(b) {
            add(&mut at, v);
            seen.push(v);
            self.mark(&mut taken, v, true);
        }
        block.end.each_use(|u| {
            if add(&mut at, u) {
                seen.push(u);
                self.mark(&mut taken, u, true);
            }
        });
        self.aim_end(f, b);
        highs.clear();
        highs.resize(n, None);
        after.clear();
        after.resize(n, taken);
        for (i, inst) in block.insts.iter().enumerate().rev() {
            after[i] = taken;
            for &d in inst.defs() {
                remove(&mut at, d);
                self.mark(&mut taken, d, false);
            }
            highs[i] = highest(&taken);
            self.aim_args(b, i, inst, tail.is_some() && i + 1 == n);
            each_read(inst, &self.imms, |u| {
                if add(&mut at, u) {
                    seen.push(u);
                    self.mark(&mut taken, u, true);
                }
            });
        }
        seen.iter().for_each(|&v| remove(&mut at, v));
        let test = if self.fusable[b] { fused_test(block, &self.uses, &self.imms) } else { None };
        let insts = &block.insts[..n - usize::from(tail.is_some() || test.is_some())];
        for (j, inst) in insts.iter().enumerate() {
            if let &[d] = inst.defs()
                && !matches!(inst, Inst::Closures { .. })
            {
                self.aim(b, j, d, &mut highs, &mut after);
            }
            let base = highs[j].map_or(self.first, |h| self.first.max(h + 1));
            self.site(block.sites[j]);
            self.inst(inst, base)?;
        }
        (self.at, self.seen, self.highs, self.after) = (at, seen, highs, after);
        // An instruction fused into the end of the block is emitted there, and keeps its own site.
        let fused = tail.is_some() || test.is_some();
        self.site(if fused { block.sites[n - 1] } else { block.end_site });
        match (tail, test, &block.end) {
            (Some((prim, args)), _, _) => self.tail_prim(prim, args),
            (None, Some((intrinsic, args)), End::Branch { then, other, .. }) => {
                let branch_if = self.inverted[b];
                let (target, fall) = if branch_if { (*then, *other) } else { (*other, *then) };
                let op = match *args {
                    [a0] => Op::BranchIntrinsic1 { a: self.read(a0, 0), intrinsic, branch_if, offset: 0 },
                    [a0, a1] => {
                        let (a, b) = (self.read(a0, 0), self.read(a1, 1));
                        Op::BranchIntrinsic2 { a, b, intrinsic, branch_if, offset: 0 }
                    }
                    _ => unreachable!("a fused test takes 1 or 2 arguments"),
                };
                self.jump(op, target);
                self.go(fall, next);
                Ok(())
            }
            _ => self.end(f, &block.end, next),
        }
    }

    /// If `block` ends by returning the result of an intrinsic instruction, returns the intrinsic and its arguments
    /// so it can be emitted using a specialized tail-return opcode.
    fn tail<'b>(&self, block: &'b l5::BlockData<'_, 'gc>) -> Option<(Prim, &'b [Val])> {
        let (Some(Inst::Prim { dst, prim, args, spread: false }), End::Return(v)) = (block.insts.last(), &block.end) else { return None };
        let tail = matches!(prim, Prim::Intrinsic(_)) && self.imms[dst.0 as usize].is_none();
        (tail && dst == v && self.uses[dst.0 as usize] == 1).then_some((*prim, args.as_slice()))
    }

    fn tail_prim(&mut self, prim: Prim, args: &[Val]) -> Result<(), CompileError> {
        let n = args.len() as u8;
        match (prim, self.stage(self.first, None, args, true)) {
            (Prim::Intrinsic(intrinsic), Some(base)) => self.ops.push(Op::TailCallIntrinsic { base, args: n, intrinsic }),
            (Prim::Intrinsic(intrinsic), None) => {
                let base = self.list(args, None);
                self.ops.extend([Op::ApplyIntrinsic { base, args: 1, intrinsic }, Op::LoadAcc { dst: SCRATCH }, Op::Return { src: SCRATCH }]);
            }
            _ => unreachable!("only intrinsics return their own values"),
        }
        Ok(())
    }

    fn mark(&self, taken: &mut Regs, v: Val, to: bool) {
        if let Some(Loc::Reg(r)) = self.locs[v.0 as usize] {
            set_reg(taken, r, to);
        }
    }

    /// Registers target preferences for argument values staged by `inst` at instruction `at` in block `b`.
    fn aim_args(&mut self, b: usize, at: usize, inst: &Inst<'_, 'gc>, tail: bool) {
        let (head, args) = match inst {
            Inst::Call { f, args, .. } => (Some(*f), args),
            Inst::Prim { dst, prim, args, spread } if tail || self.stages(*dst, *prim, args.len(), *spread) => (None, args),
            _ => return,
        };
        for (p, &v) in head.iter().chain(args).enumerate() {
            let p = u8::try_from(p).unwrap_or(u8::MAX);
            self.wants(v, b, at, if tail { Aim::First(p) } else { Aim::Base(p) });
        }
    }

    /// Registers target preferences for values passed as block arguments by block `b`'s terminator.
    fn aim_end(&mut self, f: &Function<'_, 'gc>, b: usize) {
        let block = &f.blocks[b];
        let at = block.insts.len();
        match &block.end {
            End::Jump(to, args) => {
                for (p, &a) in f.blocks[to.0 as usize].params.iter().zip(args) {
                    if let Some(Loc::Reg(r)) = self.locs[p.0 as usize] {
                        self.wants(a, b, at, Aim::Reg(r));
                    }
                }
            }
            End::TailCall { f, args } => {
                for (p, &v) in std::iter::once(f).chain(args).enumerate() {
                    self.wants(v, b, at, Aim::First(u8::try_from(p).unwrap_or(u8::MAX)));
                }
            }
            End::TailPrim { args, .. } => {
                for (p, &v) in args.iter().enumerate() {
                    self.wants(v, b, at, Aim::First(u8::try_from(p).unwrap_or(u8::MAX)));
                }
            }
            End::Return(_) | End::Branch { .. } => {}
        }
    }

    fn wants(&mut self, v: Val, b: usize, at: usize, aim: Aim) {
        if self.uses[v.0 as usize] == 1 {
            self.aims[v.0 as usize] = Some((b as u32, at as u32, aim));
        }
    }

    /// Pre-assigns `v` (defined at instruction `j` in block `b`) directly to its preferred destination register,
    /// provided that register remains unallocated throughout the intervening range.
    fn aim(&mut self, b: usize, j: usize, v: Val, highs: &mut [Option<u8>], after: &mut [Regs]) {
        let Some((block, k, aim)) = self.aims[v.0 as usize] else { return };
        let k = k as usize;
        if block as usize != b || k <= j {
            return;
        }
        let first = usize::from(self.first);
        let t = match aim {
            Aim::Reg(r) => usize::from(r),
            Aim::First(p) => first + usize::from(p),
            Aim::Base(p) => highs[k].map_or(first, |h| first.max(usize::from(h) + 1)) + usize::from(p),
        };
        if t < first || t >= usize::from(LIMIT) {
            return;
        }
        let t = t as u8;
        if self.locs[v.0 as usize] == Some(Loc::Reg(t)) || after[j..k].iter().any(|regs| has_reg(regs, t)) {
            return;
        }
        self.locs[v.0 as usize] = Some(Loc::Reg(t));
        after[j..k].iter_mut().for_each(|regs| set_reg(regs, t, true));
        highs[j + 1..k].iter_mut().for_each(|h| *h = Some(h.map_or(t, |h| h.max(t))));
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
            Inst::Call { dst, f, args } => {
                if let Some(base) = self.stage(base, Some(*f), args, false) {
                    self.ops.push(Op::Call { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(*f));
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
            let a = self.read(args[0], 0);
            self.write(dst, |dst| match imm {
                Imm::Add(imm) => Op::AddImm { dst, a, imm },
                Imm::Field(k) => Op::StructField { dst, a, k },
                Imm::FieldOf(_, k) => Op::StructRef { dst, a, k, kind },
            });
            return Ok(());
        }
        if !spread {
            match (prim, args) {
                (Prim::Intrinsic(intrinsic), &[a0]) => {
                    let a = self.read(a0, 0);
                    self.write(dst, |dst| Op::CallIntrinsic1 { dst, a, intrinsic });
                    return Ok(());
                }
                (Prim::Intrinsic(intrinsic), &[a0, a1]) => {
                    let (a, b) = (self.read(a0, 0), self.read(a1, 1));
                    self.write(dst, |dst| Op::CallIntrinsic2 { dst, a, b, intrinsic });
                    return Ok(());
                }
                (Prim::Intrinsic(intrinsic), &[a0, a1, a2]) => {
                    let (a, b, c) = (self.read(a0, 0), self.read(a1, 1), self.read(a2, 2));
                    self.write(dst, |dst| Op::CallIntrinsic3 { dst, a, b, c, intrinsic });
                    return Ok(());
                }
                _ => {}
            }
        }
        let host = if let Prim::Host(def) = prim { Some(self.module.host(def)?) } else { None };
        let n = args.len() as u8;
        let staged = self.stage(base, None, args, matches!(prim, Prim::Intrinsic(_)));
        let op = match (prim, spread, staged) {
            (Prim::Intrinsic(intrinsic), false, Some(base)) => Op::CallIntrinsic { base, args: n, intrinsic },
            (Prim::Intrinsic(intrinsic), true, Some(base)) => Op::ApplyIntrinsic { base, args: n, intrinsic },
            (Prim::Intrinsic(intrinsic), _, None) => Op::ApplyIntrinsic { base: self.spread(args, spread), args: 1, intrinsic },
            (Prim::Request(request), false, Some(base)) => Op::CallRequest { base, args: n, request },
            (Prim::Request(request), true, Some(base)) => Op::ApplyRequest { base, args: n, request },
            (Prim::Request(request), _, None) => Op::ApplyRequest { base: self.spread(args, spread), args: 1, request },
            (Prim::Host(_), false, Some(base)) => Op::CallHost { base, args: n, host: host.expect("looked up") },
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
        let len = self.module.owner.map_or(0, |m| m.items(self.module.mc).len());
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
        for (dst, r) in peers {
            if self.used(dst) {
                self.mov(self.loc(dst), Loc::Reg(r));
            }
        }
        Ok(())
    }

    fn captures(&self, captured: &[Captured], peers: &[(Val, u8)]) -> Vec<Capture> {
        let capture = |&c: &Captured| match c {
            Captured::Upvalue(u) => Capture::Upvalue(u),
            Captured::Val(v) => match peers.iter().find(|&&(peer, _)| peer == v) {
                Some(&(_, r)) => Capture::Register(r),
                None => match self.loc(v) {
                    Loc::Reg(r) => Capture::Register(r),
                    Loc::Slot(slot) => Capture::Spill { spill: self.spill_reg(), slot },
                },
            },
        };
        captured.iter().map(capture).collect()
    }

    /// Emits bytecode for block terminator `end`. If the target block matches `next`, redundant jumps can fall through.
    fn end(&mut self, f: &Function<'_, 'gc>, end: &End<'_>, next: Option<usize>) -> Result<(), CompileError> {
        match end {
            End::Return(v) => {
                let src = self.read(*v, 0);
                self.ops.push(Op::Return { src });
            }
            End::Jump(to, args) => {
                let params = &f.blocks[to.0 as usize].params;
                let mut moves = std::mem::replace(&mut self.moves, self.arena.vec());
                moves.clear();
                moves.extend(params.iter().zip(args).filter_map(|(p, &a)| Some((self.locs[p.0 as usize]?, self.loc(a)))));
                self.parallel(moves);
                self.go(*to, next);
            }
            End::Branch { test, then, other } => {
                let test = self.read(*test, 0);
                self.jump(Op::JumpIfFalse { test, offset: 0 }, *other);
                self.go(*then, next);
            }
            End::TailCall { f, args } => {
                if let Some(base) = self.stage(self.first, Some(*f), args, false) {
                    self.ops.push(Op::TailCall { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(*f));
                    self.ops.push(Op::TailCallRequest { base: SCRATCH, args: 2, request: Request::Apply });
                }
            }
            End::TailPrim { prim: Prim::Request(request), args, spread } => {
                let n = args.len() as u8;
                let request = *request;
                match (self.stage(self.first, None, args, false), spread) {
                    // A guard continuation retains its caller frame; invoking it from that frame allows the VM
                    // to reuse the existing handler in place without creating a new prompt.
                    (Some(base), false) if matches!(request, Request::Guard | Request::GuardQuiet) => self.ops.extend([
                        Op::CallRequest { base, args: n, request },
                        Op::LoadAcc { dst: SCRATCH },
                        Op::Return { src: SCRATCH },
                    ]),
                    (Some(base), false) => self.ops.push(Op::TailCallRequest { base, args: n, request }),
                    (Some(base), true) => self.ops.push(Op::TailApplyRequest { base, args: n, request }),
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
        let n = usize::from(head.is_some()) + vals.len();
        if let Some(r) = self.row(head.iter().chain(vals))
            && (r >= base || free && r >= ARGS)
        {
            return Some(r);
        }
        let base = if usize::from(base) + n <= usize::from(LIMIT) {
            base
        } else if n <= STAGE {
            SCRATCH
        } else {
            return None;
        };
        let mut moves = std::mem::replace(&mut self.moves, self.arena.vec());
        moves.clear();
        moves.extend(head.iter().chain(vals).zip(base..).map(|(&v, r)| (Loc::Reg(r), self.loc(v))));
        self.parallel(moves);
        Some(base)
    }

    /// Returns the starting register index if `vals` already occupy a contiguous sequence of hardware registers, or `None` otherwise.
    fn row<'v>(&self, mut vals: impl Iterator<Item = &'v Val>) -> Option<u8> {
        let Loc::Reg(r) = self.loc(*vals.next()?) else { return None };
        let mut next = r;
        for &v in vals {
            next = next.checked_add(1)?;
            if self.loc(v) != Loc::Reg(next) {
                return None;
            }
        }
        Some(r)
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
        for &v in vals.iter().rev() {
            self.mov(Loc::Reg(SCRATCH), self.loc(v));
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
                for m in &mut moves {
                    if m.1 == from {
                        m.1 = Loc::Reg(SCRATCH);
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

    fn used(&self, v: Val) -> bool {
        self.uses[v.0 as usize] > 0
    }

    fn loc(&self, v: Val) -> Loc {
        self.locs[v.0 as usize].expect("a value used has a place")
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

    /// Resolves the physical register holding operand value `v` for instruction input `k`, loading spilled values into scratch if necessary.
    fn read(&mut self, v: Val, k: u8) -> u8 {
        match self.loc(v) {
            Loc::Reg(r) => r,
            Loc::Slot(slot) => {
                let dst = SCRATCH + k;
                self.ops.push(Op::LoadSpill { dst, spill: self.spill_reg(), slot });
                dst
            }
        }
    }

    /// Emits `op` targeting the physical register assigned to `v`, or redirects to a scratch register if `v` is unused.
    fn write(&mut self, v: Val, op: impl FnOnce(u8) -> Op) {
        match self.locs[v.0 as usize].filter(|_| self.used(v)) {
            Some(Loc::Reg(r)) => self.ops.push(op(r)),
            Some(Loc::Slot(slot)) => {
                let spill = self.spill_reg();
                self.ops.extend([op(SCRATCH), Op::StoreSpill { src: SCRATCH, spill, slot }]);
            }
            None => self.ops.push(op(SCRATCH)),
        }
    }
}
