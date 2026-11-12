//! The bytecode of a module, as text, for `ragwort compile`.
//!
//! ```text
//! module lib/text
//!   form 0
//!     fn0: arity 0, 0 captured
//!       0  LoadConst { dst: 2, value: closure(fn1) }
//! ```
//!
//! Each top-level form with code is a function of no arguments. The functions it makes are
//! numbered after it, in the order the code first refers to them.

use std::collections::{HashMap, VecDeque};
use std::fmt::Write;

use ragwort_printer_scheme::{Mode, to_string};
use ragwort_types::constant::Constants;
use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_vm::Op;
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure, ClosureFields};

/// The most characters a constant is shown in.
const LIMIT: usize = 200;

/// The functions of one form, numbered as they're first referred to, and those still to list.
#[derive(Default)]
struct Functions<'gc> {
    numbers: HashMap<u64, usize>,
    queue: VecDeque<(usize, Gc<'gc, Bytecode>)>,
}

impl<'gc> Functions<'gc> {
    fn number(&mut self, mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>) -> usize {
        let next = self.numbers.len();
        let number = *self.numbers.entry(Value::object(mc, code).to_bits()).or_insert(next);
        if number == next {
            self.queue.push_back((number, code));
        }
        number
    }

    /// The constant `value`, as an instruction that loads it shows it.
    fn constant(&mut self, mc: &Mutation<'gc>, value: Value<'gc>) -> String {
        if let Some(code) = value.downcast::<Bytecode>(mc) {
            return format!("fn{}", self.number(mc, code));
        }
        if let Some(code) = value.downcast::<Closure>(mc).and_then(|closure| closure.code(mc)) {
            return format!("closure(fn{})", self.number(mc, code));
        }
        to_string(mc, value, Mode::Write, LIMIT).unwrap_or_else(|_| "...".to_string())
    }
}

/// Adds to `out` the bytecode of the module `name`, whose forms with code are `thunks`.
pub fn list<'gc>(mc: &Mutation<'gc>, name: &str, thunks: &[Value<'gc>], out: &mut String) {
    let _ = writeln!(out, "module {name}");
    for (i, thunk) in thunks.iter().enumerate() {
        let _ = writeln!(out, "  form {i}");
        let Some(code) = thunk.downcast::<Closure>(mc).and_then(|closure| closure.code(mc)) else { continue };
        let mut functions = Functions::default();
        functions.number(mc, code);
        while let Some((number, code)) = functions.queue.pop_front() {
            function(mc, number, code, &mut functions, out);
        }
    }
}

fn function<'gc>(mc: &Mutation<'gc>, number: usize, code: Gc<'gc, Bytecode>, functions: &mut Functions<'gc>, out: &mut String) {
    let captured = code.captures(mc).map_or(0, |captures| captures.len());
    let _ = writeln!(out, "    fn{number}: arity {}, {captured} captured", code.arity(mc));
    let constants = Constants::of(code.constants(mc));
    let mut constant = |index: u32| match constants.and_then(|constants| constants.get(mc, index)) {
        Some(value) => functions.constant(mc, value),
        None => format!("constant {index}"),
    };
    let Some(ops) = code.ops(mc) else { return };
    for (at, op) in ops.iter().enumerate() {
        let text = match *op {
            Op::LoadConst { dst, index } => format!("LoadConst {{ dst: {dst}, value: {} }}", constant(index)),
            Op::NewClosure { dst, count, code } => {
                let codes: Vec<String> = (0..u32::from(count)).map(|k| constant(code + k)).collect();
                format!("NewClosure {{ dst: {dst}, codes: [{}] }}", codes.join(", "))
            }
            ref op => format!("{op:?}"),
        };
        let _ = writeln!(out, "      {at:<3} {text}");
    }
}
