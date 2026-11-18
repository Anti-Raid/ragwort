//! L6: the control-flow graph of one function, with a VM instruction chosen for every operation.
//!
//! [`select`](crate::select) builds an L6 function from an [`L5`](crate::l5) function. L6 keeps the
//! blocks and the SSA values of L5. It differs in three ways:
//!
//! - Each instruction names the form the VM runs it in. `(+ x 1)` is an [`Kind::AddImm`], a table
//!   access with a constant key is a [`Kind::TableRef`] with its hint, and so on.
//! - An instruction is fused into the end of its block where the VM has an instruction for the pair:
//!   a test into the branch on its result ([`End::BranchPrim`]), and an intrinsic into the return of
//!   its result ([`End::ReturnPrim`]).
//! - The function records the order its blocks are emitted in.
//!
//! An instruction lists exactly the values it reads. A constant that became an immediate operand is
//! not among them, so the passes after `select` need no knowledge of immediates.
//!
//! [`allocate`](crate::allocate) then gives every value a register or a spill slot, and
//! [`emit`](crate::emit) writes the bytecode.

use std::slice;

use ragwort_alloc::Vec as AVec;
use ragwort_types::gc::Value;
use ragwort_vm::Intrinsic;

use crate::l5::{self, Block, Captured, Code, Val};
use crate::{Prim, SlotOp};

pub(crate) struct Function<'t, 'gc> {
    /// The L5 function that this function was selected from. It gives the parameters, the number of values and the parameters of each block.
    pub(crate) source: &'t l5::Function<'t, 'gc>,
    /// One block for each block of `source`, at the same index.
    pub(crate) blocks: AVec<'t, BlockData<'t, 'gc>>,
    /// The parameters that have no argument register, in order. The caller passes them in a list, and the function unpacks them on entry.
    pub(crate) unpacked: &'t [Val],
    /// The number of reads of each value by the instructions and block ends of the function. A value that nothing reads gets no register.
    pub(crate) uses: AVec<'t, u32>,
    /// The block that a jump to each block arrives at. It differs from the block itself for an empty block that only jumps on.
    pub(crate) to: AVec<'t, usize>,
    /// The blocks to emit, in the order they are emitted.
    pub(crate) order: AVec<'t, usize>,
    /// The number of table hints that the instructions of the function use.
    pub(crate) hints: u16,
}

pub(crate) struct BlockData<'t, 'gc> {
    pub(crate) insts: AVec<'t, Inst<'t, 'gc>>,
    pub(crate) end: End<'t>,
    /// The source site of `end`. For a fused end, this is the site of the instruction that was fused into it.
    pub(crate) end_site: u32,
}

pub(crate) struct Inst<'t, 'gc> {
    pub(crate) kind: Kind<'t, 'gc>,
    /// The values the instruction defines. Only [`Kind::Closures`] defines more than one.
    pub(crate) defs: &'t [Val],
    /// The procedure that a [`Kind::Call`] calls. It is read before `args`.
    pub(crate) head: Option<Val>,
    /// The values the instruction reads, in operand order. A [`Kind::Closures`] reads its captures instead: see [`Inst::reads`].
    pub(crate) args: &'t [Val],
    /// The source site of the instruction: a site number of the compilation's `Sites`, or 0.
    pub(crate) site: u32,
}

#[derive(Clone, Copy)]
pub(crate) enum Kind<'t, 'gc> {
    Const(Value<'gc>),
    Upvalue(u32),
    /// `(+ a imm)`, emitted as `Op::AddImm`.
    AddImm(i16),
    /// `(struct-field s k)` or `(struct-fixed-field s k)` with a constant field index, emitted as `Op::StructField`.
    Field(u16),
    /// `(struct-ref s type k)` with a constant struct type and field index, emitted as `Op::StructRef`.
    FieldOf(Value<'gc>, u8),
    /// `(table-ref table key default)` with a constant key, emitted as `Op::TableRefHinted` with this hint number.
    TableRef(u16),
    /// `(table-set! table key value)` with a constant key, emitted as `Op::TableSetHinted` with this hint number.
    TableSet(u16),
    /// A read or write of a module variable.
    Slot(SlotOp, u32),
    /// An intrinsic, request or host call in its general form. If `spread` is true, the last argument is a list whose elements are passed as arguments.
    Prim { prim: Prim, spread: bool },
    /// A call of `head` with `args`.
    Call,
    /// Makes one closure for each entry, and defines the values in `defs` in the same order.
    Closures(&'t [Code<'t>]),
}

#[derive(Clone, Copy)]
pub(crate) enum End<'t> {
    Jump(Block, &'t [Val]),
    /// Jumps to `other` if `test` is a false value, and to `then` otherwise.
    Branch { test: Val, then: Block, other: Block },
    /// A test of one or two arguments fused with the branch on its result. The VM instruction jumps when the result is true if `branch_if` is set, and when it is false otherwise. The other target is fallen through to.
    BranchPrim { intrinsic: Intrinsic, args: &'t [Val], then: Block, other: Block, branch_if: bool },
    Return(Val),
    /// An intrinsic fused with the return of its result.
    ReturnPrim { prim: Prim, args: &'t [Val], spread: bool },
    TailCall { f: Val, args: &'t [Val] },
    /// A request or a host call in tail position.
    TailPrim { prim: Prim, args: &'t [Val], spread: bool },
}

impl<'t> Inst<'t, '_> {
    /// Returns the values the instruction reads before it defines its own. A closure group reads the values its closures capture, except the closures of the group itself, which capture each other once they exist.
    pub(crate) fn reads(&self) -> Reads<'t> {
        let codes = match self.kind {
            Kind::Closures(codes) => codes,
            _ => &[],
        };
        Reads { head: self.head, args: self.args.iter(), defs: self.defs, codes: codes.iter(), captures: [].iter() }
    }
}

impl<'t> End<'t> {
    /// Returns the values the end of a block reads.
    pub(crate) fn reads(&self) -> Reads<'t> {
        let (head, args) = match *self {
            End::Jump(_, args) | End::BranchPrim { args, .. } | End::ReturnPrim { args, .. } | End::TailPrim { args, .. } => (None, args),
            End::Branch { test: value, .. } | End::Return(value) => (Some(value), &[][..]),
            End::TailCall { f: callee, args } => (Some(callee), args),
        };
        Reads { head, args: args.iter(), defs: &[], codes: [].iter(), captures: [].iter() }
    }
}

/// Iterator over the values that an instruction or the end of a block reads. See [`Inst::reads`].
pub(crate) struct Reads<'t> {
    head: Option<Val>,
    args: slice::Iter<'t, Val>,
    /// The values a closure group defines. They are skipped among its captures.
    defs: &'t [Val],
    codes: slice::Iter<'t, Code<'t>>,
    captures: slice::Iter<'t, Captured>,
}

impl Iterator for Reads<'_> {
    type Item = Val;

    fn next(&mut self) -> Option<Val> {
        if let Some(head) = self.head.take() {
            return Some(head);
        }
        if let Some(&value) = self.args.next() {
            return Some(value);
        }
        loop {
            for captured in self.captures.by_ref() {
                if let Captured::Val(value) = captured
                    && !self.defs.contains(value)
                {
                    return Some(*value);
                }
            }
            self.captures = self.codes.next()?.captures.iter();
        }
    }
}

/// Formats the function as text, one line for each instruction, for tests. A value that nothing reads is marked `unread`.
#[cfg(test)]
impl std::fmt::Display for Function<'_, '_> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use crate::l5::{Constant, PrimName, Vals, args, spread};
        let source = self.source;
        match source.id {
            Some(id) => write!(formatter, "function {id}")?,
            None => write!(formatter, "function")?,
        }
        write!(formatter, " ({}", Vals(&source.params))?;
        if let Some(rest) = source.rest {
            write!(formatter, " . {rest}")?;
        }
        write!(formatter, ") order")?;
        for &index in self.order.iter() {
            write!(formatter, " b{index}")?;
        }
        if !self.unpacked.is_empty() {
            write!(formatter, ", unpacks {}", Vals(self.unpacked))?;
        }
        if self.hints > 0 {
            write!(formatter, ", {} hints", self.hints)?;
        }
        writeln!(formatter, ":")?;
        for (index, block) in self.blocks.iter().enumerate() {
            let params = &source.blocks[index].params;
            write!(formatter, "b{index}")?;
            if !params.is_empty() {
                write!(formatter, "({})", Vals(params))?;
            }
            if self.to[index] != index {
                writeln!(formatter, ": skipped, jumps arrive at b{}", self.to[index])?;
                continue;
            }
            writeln!(formatter, ":")?;
            for inst in &block.insts {
                write!(formatter, "  {} = ", Vals(inst.defs))?;
                match inst.kind {
                    Kind::Const(value) => write!(formatter, "{}", Constant(&value))?,
                    Kind::Upvalue(upvalue) => write!(formatter, "upvalue {upvalue}")?,
                    Kind::AddImm(addend) => write!(formatter, "add-imm{} {addend}", args(inst.args))?,
                    Kind::Field(field) => write!(formatter, "field-imm{} {field}", args(inst.args))?,
                    Kind::FieldOf(kind, field) => write!(formatter, "field-of-imm{} {} {field}", args(inst.args), Constant(&kind))?,
                    Kind::TableRef(hint) => write!(formatter, "table-ref-hinted{} hint {hint}", args(inst.args))?,
                    Kind::TableSet(hint) => write!(formatter, "table-set-hinted{} hint {hint}", args(inst.args))?,
                    Kind::Slot(op, slot) => write!(formatter, "{}{}", PrimName(Prim::Slot(op, slot)), args(inst.args))?,
                    Kind::Prim { prim, spread: applied } => write!(formatter, "{}{}{}", spread(applied), PrimName(prim), args(inst.args))?,
                    Kind::Call => write!(formatter, "call {}{}", inst.head.expect("a call has a procedure"), args(inst.args))?,
                    Kind::Closures(codes) => {
                        write!(formatter, "closures")?;
                        for code in codes {
                            write!(formatter, " [fn{}", code.function)?;
                            for captured in &code.captures {
                                match captured {
                                    Captured::Val(value) => write!(formatter, " {value}")?,
                                    Captured::Upvalue(upvalue) => write!(formatter, " upvalue {upvalue}")?,
                                }
                            }
                            write!(formatter, "]")?;
                        }
                    }
                }
                if inst.defs.iter().all(|def| self.uses[def.0 as usize] == 0) {
                    write!(formatter, " (unread)")?;
                }
                writeln!(formatter)?;
            }
            match block.end {
                End::Jump(to, operands) => writeln!(formatter, "  jump {to}({})", Vals(operands))?,
                End::Branch { test, then, other } => writeln!(formatter, "  branch {test} {then} {other}")?,
                End::BranchPrim { intrinsic, args: operands, then, other, branch_if } => {
                    let jumps = if branch_if { ", jumps if true" } else { "" };
                    writeln!(formatter, "  branch-on {}{} {then} {other}{jumps}", intrinsic.name(), args(operands))?;
                }
                End::Return(value) => writeln!(formatter, "  return {value}")?,
                End::ReturnPrim { prim, args: operands, spread: applied } => writeln!(formatter, "  return-of {}{}{}", spread(applied), PrimName(prim), args(operands))?,
                End::TailCall { f: callee, args: operands } => writeln!(formatter, "  tail-call {callee}{}", args(operands))?,
                End::TailPrim { prim, args: operands, spread: applied } => writeln!(formatter, "  tail {}{}{}", spread(applied), PrimName(prim), args(operands))?,
            }
        }
        Ok(())
    }
}
