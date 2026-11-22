//! Pass 10: bytecode emission from an [`L6`](crate::l6) function and its register allocation.
//!
//! For each function, [`select`] chooses the instructions and [`allocate`] places
//! the values. This pass then writes the bytecode:
//!
//! - It stages the arguments of each call in a row of registers, and falls back to passing them in a
//!   list when a call has more arguments than fit.
//! - It emits parallel moves for the arguments of jumps and for staged arguments, so that no move
//!   overwrites a value that a later move still reads.
//! - It loads spilled operands into scratch registers and stores spilled results.
//! - It resolves jump offsets, removes jumps to the next instruction, and builds the constant pool, the
//!   hint words and the position table of each function.

use ragwort_alloc::{Arena, CollectIn, Vec as AVec};
use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::vector::Vectors;
use ragwort_vm::frame::{self, ARGS, MAX_PARAMS, Shape};
use ragwort_vm::objects::{self, Bytecode, BytecodeFields, Closure, HINT_KEY, HINT_SLOTS, Hints, HintsFields, ModuleFields, Sites, SitesFields};
use ragwort_vm::report::{Line, Scope, Table};
use ragwort_vm::{Capture, HostDef, Intrinsic, Op, Request};

use crate::allocate::{self, LIMIT, Loc, Places, SCRATCH, STAGE};
use crate::hash::HashMap;
use crate::ir::{Inlined, Origins, Site};
use crate::l5::{Block, Captured, Code, Function, Program, Val};
use crate::l6::{self, End, Inst, Kind};
use crate::select;
use crate::{CompileError, Prim, SlotOp};

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
    /// The position table rows of every function emitted so far. The rows refer to sources and procedure names by index into `items`.
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

    /// Returns the index of host function `def` in the host table of the owning module. Returns `CompileError::UnknownHost` if the table does not contain `def`.
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
        // Each inlined call keeps its number, because rows refer to inlined calls by number. The compiler numbers an inlined call after the call that encloses it, so the enclosing call always has the smaller number.
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

    /// Emits bytecode for function `function`, fusing 1- and 2-argument intrinsic tests into conditional branches
    /// unless jump targets exceed the 16-bit signed branch offset limit.
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
        // Scratch arena for intra-function compiler data structures, deallocated immediately after function emission.
        let scratch = Arena::new();
        let arena = &scratch;
        let selected = select::select(arena, function, near);
        let places = allocate::allocate(arena, &selected, frame::link_slot(arity));
        let mut emitter = Emitter {
            module: self,
            arena,
            function: &selected,
            places: &places,
            ops: Vec::new(),
            sited: Vec::new(),
            moves: arena.vec(),
            fence: 0,
            starts: arena.vec_of(0, selected.blocks.len()),
            jumps: arena.vec(),
        };
        if let Some(dst) = places.spill {
            emitter.ops.push(Op::NewSpill { dst, count: places.slots });
        }
        // The last argument register holds the parameters that have no register of their own, as a list.
        let list = ARGS + MAX_PARAMS - 1;
        for &param in selected.unpacked {
            if emitter.used(param) {
                let target = emitter.target(param);
                emitter.ops.push(Op::CallIntrinsic1 { dst: target, a: list, intrinsic: Intrinsic::Car });
                emitter.store(param);
            }
            emitter.ops.push(Op::CallIntrinsic1 { dst: list, a: list, intrinsic: Intrinsic::Cdr });
        }
        for (i, &block) in selected.order.iter().enumerate() {
            emitter.block(block, selected.order.get(i + 1).copied())?;
        }
        let Emitter { mut ops, mut starts, mut jumps, mut sited, .. } = emitter;
        let hint_keys = selected.hints.as_slice();
        // Eliminates redundant jumps to the immediately following instruction (e.g. blocks where parallel moves collapsed to no-ops).
        loop {
            // `gone[pc]` is set for each jump to remove. A flag for every instruction keeps one pass linear in the length of the function.
            let mut gone = arena.vec_of(false, ops.len() + 1);
            let mut removed = 0;
            for &(at, to) in jumps.iter() {
                if starts[to.0 as usize] == at + 1 && matches!(ops[at], Op::Jump { .. } | Op::JumpIfFalse { .. }) {
                    gone[at] = true;
                    removed += 1;
                }
            }
            if removed == 0 {
                break;
            }
            let mut moved = AVec::with_capacity_in(ops.len() + 1, arena);
            let mut left = 0;
            for i in 0..=ops.len() {
                moved.push(i - left);
                if gone[i] {
                    left += 1;
                }
            }
            ops = ops.into_iter().enumerate().filter(|(i, _)| !gone[*i]).map(|(_, op)| op).collect();
            starts.iter_mut().for_each(|start| *start = moved[*start]);
            sited.iter_mut().for_each(|(pc, _)| *pc = moved[*pc]);
            jumps = jumps.into_iter().filter(|(at, _)| !gone[*at]).map(|(at, to)| (moved[at], to)).collect_in(arena);
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
        // A function without a lambda ID is the code of a top-level form. Its name is `Value::VOID`, so that an error traceback can tell it apart from a procedure.
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
        // Each hint remembers a few places where its instruction found its key, all unused at first. It also holds the key.
        let hints = if hint_keys.is_empty() {
            None
        } else {
            let hints = Hints::new(mc, HINT_SLOTS * hint_keys.len(), Value::FALSE)?;
            for (number, &key) in hint_keys.iter().enumerate() {
                hints.items(mc).set(mc, HINT_SLOTS * number + HINT_KEY, key);
            }
            Some(hints)
        };
        let code = Bytecode::new(mc, mc.frozen(Box::from(ops))?, Value::VOID, mc.frozen(Box::from(captures))?, arity, self.owner, name, source, start, Value::FALSE, lines_start, lines_len, hints)?;
        self.codes.push(code);
        Ok(Some(code))
    }
}

struct Emitter<'m, 'a, 't, 'gc> {
    module: &'m mut Module<'a, 'gc>,
    arena: &'t Arena,
    function: &'t l6::Function<'t, 'gc>,
    places: &'t Places<'t>,
    ops: Vec<Op>,
    /// Pairs of an instruction index and a source site. Each pair marks the start of a run of instructions that come from that site. Site 0 marks instructions with no known position.
    sited: Vec<(usize, u32)>,
    /// A buffer for parallel moves, kept between uses.
    moves: AVec<'t, (Loc, Loc)>,
    /// The starting opcode index of the basic block currently being emitted; moves cannot fuse across this boundary.
    fence: usize,
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

    /// Emits block `index`. `next` is the block that is emitted after it, which a jump to it can fall through to.
    fn block(&mut self, index: usize, next: Option<usize>) -> Result<(), CompileError> {
        self.starts[index] = self.ops.len();
        self.fence = self.ops.len();
        let block = &self.function.blocks[index];
        for (j, inst) in block.insts.iter().enumerate() {
            self.site(inst.site);
            self.inst(inst, self.places.base(index, j))?;
        }
        self.site(block.end_site);
        self.end(&block.end, next)
    }

    /// Emits bytecode for instruction `inst`. Outgoing calls are staged at or above register index `base`.
    fn inst(&mut self, inst: &Inst<'t, 'gc>, base: u8) -> Result<(), CompileError> {
        let Kind::Closures(codes) = inst.kind else {
            let &[dst] = inst.defs else { unreachable!("only a closure group defines several values") };
            return self.single(inst, dst, base);
        };
        self.closures(inst.defs, codes)
    }

    /// Emits bytecode for instruction `inst`, which defines the one value `dst`.
    fn single(&mut self, inst: &Inst<'t, 'gc>, dst: Val, base: u8) -> Result<(), CompileError> {
        let args = inst.args;
        match inst.kind {
            Kind::Const(value) => {
                if self.used(dst) {
                    let index = self.module.constant(value)?;
                    let target = self.target(dst);
                    self.ops.push(Op::LoadConst { dst: target, index });
                    self.store(dst);
                }
            }
            Kind::Upvalue(index) => {
                if self.used(dst) {
                    let target = self.target(dst);
                    self.ops.push(Op::LoadUpvalue { dst: target, index });
                    self.store(dst);
                }
            }
            Kind::AddImm(imm) => {
                let operand = self.read(args[0], 0);
                let target = self.target(dst);
                self.ops.push(Op::AddImm { dst: target, a: operand, imm });
                self.store(dst);
            }
            Kind::Field(field) => {
                let operand = self.read(args[0], 0);
                let target = self.target(dst);
                self.ops.push(Op::StructField { dst: target, a: operand, k: field });
                self.store(dst);
            }
            Kind::FieldOf(kind, field) => {
                let kind = self.module.constant(kind)?;
                let operand = self.read(args[0], 0);
                let target = self.target(dst);
                self.ops.push(Op::StructRef { dst: target, a: operand, k: field, kind });
                self.store(dst);
            }
            Kind::TableRef(hint) => {
                let table = self.read(inst.head.expect("a table instruction has a table"), 0);
                // A read whose default is `#f` has no default argument.
                if let Some(&default) = args.first() {
                    let default = self.read(default, 1);
                    let target = self.target(dst);
                    self.ops.push(Op::TableRefOrHinted { dst: target, table, default, hint });
                } else {
                    let target = self.target(dst);
                    self.ops.push(Op::TableRefHinted { dst: target, table, hint });
                }
                self.store(dst);
            }
            Kind::TableSet(hint) => {
                let (table, value) = (self.read(inst.head.expect("a table instruction has a table"), 0), self.read(args[0], 1));
                let target = self.target(dst);
                self.ops.push(Op::TableSetHinted { dst: target, table, value, hint });
                self.store(dst);
            }
            Kind::Slot(op, slot) => self.slot(dst, op, slot, args)?,
            Kind::Prim { prim, spread } => self.prim(dst, prim, args, spread, base)?,
            Kind::Call => {
                let callee = inst.head.expect("a call has a procedure");
                if let Some(base) = self.stage(base, Some(callee), args, false) {
                    self.ops.push(Op::Call { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(callee));
                    self.ops.push(Op::CallRequest { base: SCRATCH, args: 2, request: Request::Apply });
                }
                self.take(dst);
            }
            Kind::Closures(_) => unreachable!("a closure group is emitted by `closures`"),
        }
        Ok(())
    }

    /// Emits an intrinsic, request or host call in its general form.
    fn prim(&mut self, dst: Val, prim: Prim, args: &[Val], spread: bool, base: u8) -> Result<(), CompileError> {
        if !spread && let Prim::Intrinsic(intrinsic) = prim {
            // An intrinsic with up to three arguments reads them from any registers.
            let op = match *args {
                [a0] => Some((self.read(a0, 0), 0, 0)),
                [a0, a1] => Some((self.read(a0, 0), self.read(a1, 1), 0)),
                [a0, a1, a2] => Some((self.read(a0, 0), self.read(a1, 1), self.read(a2, 2))),
                _ => None,
            };
            if let Some((first, second, third)) = op {
                let target = self.target(dst);
                self.ops.push(match args.len() {
                    1 => Op::CallIntrinsic1 { dst: target, a: first, intrinsic },
                    2 => Op::CallIntrinsic2 { dst: target, a: first, b: second, intrinsic },
                    _ => Op::CallIntrinsic3 { dst: target, a: first, b: second, c: third, intrinsic },
                });
                self.store(dst);
                return Ok(());
            }
        }
        let host = if let Prim::Host(def) = prim { Some(self.module.host(def)?) } else { None };
        let count = args.len() as u8;
        let staged = self.stage(base, None, args, matches!(prim, Prim::Intrinsic(_)));
        // A `collect` is a call whose values are loaded as a list.
        if let (Prim::Request(Request::Collect), false, Some(base)) = (prim, spread, staged) {
            self.ops.push(Op::Call { base, args: count - 1 });
            if self.used(dst) {
                let target = self.target(dst);
                self.ops.push(Op::LoadValues { dst: target });
                self.store(dst);
            }
            return Ok(());
        }
        let op = match (prim, spread, staged) {
            // The consumer is staged below the producer. The producer's frame starts above the consumer, so the consumer is still in place when the producer returns.
            (Prim::Request(Request::Receive), false, Some(base)) => {
                self.ops.push(Op::Call { base: base + 1, args: count - 2 });
                Op::CallReceived { base }
            }
            (Prim::Intrinsic(intrinsic), false, Some(base)) => Op::CallIntrinsic { base, args: count, intrinsic },
            (Prim::Intrinsic(intrinsic), true, Some(base)) => Op::ApplyIntrinsic { base, args: count, intrinsic },
            (Prim::Intrinsic(intrinsic), _, None) => Op::ApplyIntrinsic { base: self.spread(args, spread), args: 1, intrinsic },
            (Prim::Request(request), false, Some(base)) => Op::CallRequest { base, args: count, request },
            (Prim::Request(request), true, Some(base)) => Op::ApplyRequest { base, args: count, request },
            (Prim::Request(request), _, None) => Op::ApplyRequest { base: self.spread(args, spread), args: 1, request },
            (Prim::Host(_), false, Some(base)) => Op::CallHost { base, args: count, host: host.expect("looked up") },
            (Prim::Host(_), false, None) => return Err(CompileError::TooManyArguments),
            (Prim::Host(_) | Prim::Slot(..), true, _) | (Prim::Slot(..), false, _) => {
                unreachable!("lowering spreads no host function, and a slot access has its own instruction form")
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
                    let target = self.target(dst);
                    self.ops.push(Op::LoadSlot { dst: target, slot });
                    self.store(dst);
                }
            }
            (SlotOp::LoadChecked, []) => {
                let target = self.target(dst);
                self.ops.push(Op::LoadSlotChecked { dst: target, slot });
                self.store(dst);
            }
            (SlotOp::Store | SlotOp::StoreChecked, &[value]) => {
                let src = self.read(value, 0);
                self.ops.push(if op == SlotOp::Store { Op::StoreSlot { src, slot } } else { Op::StoreSlotChecked { src, slot } });
                if self.used(dst) {
                    let index = self.module.constant(Value::VOID)?;
                    let target = self.target(dst);
                    self.ops.push(Op::LoadConst { dst: target, index });
                    self.store(dst);
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
                    let target = self.target(dst);
                    self.ops.push(Op::LoadConst { dst: target, index });
                    self.store(dst);
                }
            }
            return Ok(());
        }
        if let (&[dst], [code]) = (dsts, codes) {
            let captures = self.captures(&code.captures, &[]);
            let index = self.module.defer(code.function, captures, false)?;
            let target = self.target(dst);
            self.ops.push(Op::NewClosure { dst: target, count: 1, code: index });
            self.store(dst);
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
        captured
            .iter()
            .map(|&source| match source {
                Captured::Upvalue(index) => Capture::Upvalue(index),
                Captured::Val(value) => match peers.iter().find(|&&(peer, _)| peer == value) {
                    Some(&(_, register)) => Capture::Register(register),
                    None => match self.loc(value) {
                        Loc::Reg(register) => Capture::Register(register),
                        Loc::Slot(slot) => Capture::Spill { spill: self.spill_reg(), slot },
                    },
                },
            })
            .collect()
    }

    /// Emits bytecode for block terminator `end`. If the target block matches `next`, redundant jumps can fall through.
    fn end(&mut self, end: &End<'t>, next: Option<usize>) -> Result<(), CompileError> {
        match *end {
            End::Return(value) => {
                // If the last instruction of this block loaded the returned value from the accumulator, drop the load and return the accumulator with `Op::ReturnReceived`. The result of the call is then returned unchanged, even if it is several values.
                let taken = match self.ops.last() {
                    Some(&Op::LoadAcc { dst }) => self.ops.len() > self.fence && self.loc(value) == Loc::Reg(dst),
                    _ => false,
                };
                if taken {
                    self.ops.pop();
                    // The return replaces the load, so it keeps the site of the load. The `sited` entry recorded for the end of the block now points past the last instruction, so remove it.
                    if self.sited.last().is_some_and(|&(at, _)| at > self.ops.len()) {
                        self.sited.pop();
                    }
                    self.ops.push(Op::ReturnReceived);
                } else {
                    let src = self.read(value, 0);
                    self.ops.push(Op::Return { src });
                }
            }
            End::ReturnPrim { prim, args, spread, .. } => self.return_prim(prim, args, spread),
            End::Jump(to, args) => {
                let params = &self.function.source.blocks[to.0 as usize].params;
                let mut moves = std::mem::replace(&mut self.moves, self.arena.vec());
                moves.clear();
                moves.extend(params.iter().zip(args).filter_map(|(param, &arg)| Some((self.places.loc(*param)?, self.loc(arg)))));
                self.parallel(moves);
                self.go(to, next);
            }
            End::Branch { test, then, other } => {
                let test = self.read(test, 0);
                self.jump(Op::JumpIfFalse { test, offset: 0 }, other);
                self.go(then, next);
            }
            End::BranchPrim { intrinsic, args, then, other, branch_if, .. } => {
                let (target, fall) = if branch_if { (then, other) } else { (other, then) };
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
            }
            End::TailCall { f: callee, args } => {
                if let Some(base) = self.stage(self.places.first, Some(callee), args, false) {
                    self.ops.push(Op::TailCall { base, args: args.len() as u8 });
                } else {
                    self.list(args, None);
                    self.mov(Loc::Reg(SCRATCH), self.loc(callee));
                    self.ops.push(Op::TailCallRequest { base: SCRATCH, args: 2, request: Request::Apply });
                }
            }
            End::TailPrim { prim: Prim::Request(request), args, spread } => {
                let count = args.len() as u8;
                match (self.stage(self.places.first, None, args, false), spread) {
                    // A guard continuation retains its caller frame; invoking it from that frame allows the VM
                    // to reuse the existing handler in place without creating a new prompt.
                    (Some(base), false) if matches!(request, Request::Guard | Request::GuardQuiet) => self.ops.extend([Op::CallRequest { base, args: count, request }, Op::ReturnReceived]),
                    (Some(base), false) if request == Request::Collect => self.ops.extend([Op::Call { base, args: count - 1 }, Op::LoadValues { dst: SCRATCH }, Op::Return { src: SCRATCH }]),
                    (Some(base), false) if request == Request::Receive => self.ops.extend([Op::Call { base: base + 1, args: count - 2 }, Op::TailCallReceived { base }]),
                    (Some(base), false) => self.ops.push(Op::TailCallRequest { base, args: count, request }),
                    (Some(base), true) => self.ops.push(Op::TailApplyRequest { base, args: count, request }),
                    (None, _) => {
                        let base = self.spread(args, spread);
                        self.ops.push(Op::TailApplyRequest { base, args: 1, request });
                    }
                }
            }
            End::TailPrim { prim: Prim::Host(def), args, .. } => {
                let host = self.module.host(def)?;
                let base = self.stage(self.places.first, None, args, false).ok_or(CompileError::TooManyArguments)?;
                self.ops.push(Op::TailCallHost { base, args: args.len() as u8, host });
            }
            End::TailPrim { .. } => unreachable!("only requests and host calls are tail ends"),
        }
        Ok(())
    }

    /// Emits an intrinsic whose result the function returns.
    fn return_prim(&mut self, prim: Prim, args: &[Val], spread: bool) {
        let count = args.len() as u8;
        let first = self.places.first;
        // `values` in tail position returns its arguments as values. With one argument, this is an ordinary return.
        if prim == Prim::Intrinsic(Intrinsic::Values) {
            let op = match (self.stage(first, None, args, true), spread) {
                (Some(base), false) => Op::ReturnValues { src: base, count },
                (Some(base), true) => Op::ReturnSpread { base, args: count },
                (None, _) => Op::ReturnSpread { base: self.spread(args, spread), args: 1 },
            };
            self.ops.push(op);
            return;
        }
        match (prim, self.stage(first, None, args, true)) {
            (Prim::Intrinsic(intrinsic), Some(base)) => self.ops.push(Op::TailCallIntrinsic { base, args: count, intrinsic }),
            (Prim::Intrinsic(intrinsic), None) => {
                let base = self.list(args, None);
                self.ops.extend([Op::ApplyIntrinsic { base, args: 1, intrinsic }, Op::ReturnReceived]);
            }
            _ => unreachable!("only intrinsics return their own values"),
        }
    }

    fn jump(&mut self, op: Op, to: Block) {
        self.jumps.push((self.ops.len(), Block(self.function.to[to.0 as usize] as u32)));
        self.ops.push(op);
    }

    /// Emits an unconditional jump to block `to`, omitting the instruction if execution naturally falls through to `next`.
    fn go(&mut self, to: Block, next: Option<usize>) {
        if Some(self.function.to[to.0 as usize]) != next {
            self.jump(Op::Jump { offset: 0 }, to);
        }
    }

    /// Stages `head` (if present) followed by `vals` into contiguous registers starting at or above `base`.
    /// If they do not fit in available local registers, attempts staging into scratch registers.
    /// Returns the starting register index, or `None` if argument count exceeds available scratch registers.
    /// Values already arranged consecutively in eligible registers remain in place.
    fn stage(&mut self, base: u8, head: Option<Val>, vals: &[Val], free: bool) -> Option<u8> {
        let count = usize::from(head.is_some()) + vals.len();
        if let Some(start) = self.row(head, vals)
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

    /// Returns the starting register index if `head` and then `vals` already occupy a contiguous sequence of frame registers, or `None` otherwise.
    fn row(&self, head: Option<Val>, vals: &[Val]) -> Option<u8> {
        let mut values = head.iter().chain(vals);
        let Loc::Reg(start) = self.loc(*values.next()?) else { return None };
        let mut next = start;
        for &value in values {
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
                let index = self.module.constant(Value::NULL).expect("the constants have room for '()");
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
        self.function.uses[value.0 as usize] > 0
    }

    fn loc(&self, value: Val) -> Loc {
        self.places.loc(value).expect("a value used has a place")
    }

    fn spill_reg(&self) -> u8 {
        self.places.spill.expect("only a function with a spill has slots")
    }

    /// Moves the call result from the accumulator register into destination `dst`, if `dst` is used.
    fn take(&mut self, dst: Val) {
        if self.used(dst) {
            let target = self.target(dst);
            self.ops.push(Op::LoadAcc { dst: target });
            self.store(dst);
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

    /// Returns the register that the instruction defining `value` writes its result to. This is the register of `value`, or the scratch register if `value` is spilled or is never read. [`Emitter::store`] must follow the instruction.
    fn target(&self, value: Val) -> u8 {
        match self.places.loc(value).filter(|_| self.used(value)) {
            Some(Loc::Reg(register)) => register,
            Some(Loc::Slot(_)) | None => SCRATCH,
        }
    }

    /// Stores the scratch register in the spill slot of `value`, if `value` is spilled. It completes an instruction that wrote its result to [`Emitter::target`].
    fn store(&mut self, value: Val) {
        if let Some(Loc::Slot(slot)) = self.places.loc(value).filter(|_| self.used(value)) {
            let spill = self.spill_reg();
            self.ops.push(Op::StoreSpill { src: SCRATCH, spill, slot });
        }
    }
}
