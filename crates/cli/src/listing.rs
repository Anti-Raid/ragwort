//! Formats the bytecode of a module as text, for `ragwort compile`.
//!
//! ```text
//! module lib/text
//!   form 0
//!     fn0: arity 0, 0 captured
//!       0  LoadConst { dst: 2, value: closure(fn1) }
//! ```
//!
//! Each top-level form that has code is a function with no arguments, listed as `fn0`. The functions that
//! it creates are numbered after it, in the order in which the code first refers to them.

use std::collections::{HashMap, VecDeque};
use std::fmt::Write;

use ragwort_printer_scheme::{Mode, to_string};
use ragwort_types::constant::Constants;
use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_vm::Op;
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure, ClosureFields};

/// The maximum length, in bytes, of the text shown for a constant.
const LIMIT: usize = 200;

/// The functions of one form. `numbers` gives each function its number, assigned when the function is first referred to. `queue` holds the functions that are not listed yet.
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

    /// Returns the text that an instruction shows for the constant `value` that it loads.
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

/// Appends the bytecode listing of the module `name` to `out`. `thunks` are the module's forms that have code.
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
    fn constant<'gc>(mc: &Mutation<'gc>, constants: Option<Constants<'gc>>, functions: &mut Functions<'gc>, index: u32) -> String {
        match constants.and_then(|constants| constants.get(mc, index)) {
            Some(value) => functions.constant(mc, value),
            None => format!("constant {index}"),
        }
    }
    let constants = Constants::of(code.constants(mc));
    let Some(ops) = code.ops(mc) else { return };
    for (at, op) in ops.iter().enumerate() {
        let text = match *op {
            Op::LoadConst { dst, index } => format!("LoadConst {{ dst: {dst}, value: {} }}", constant(mc, constants, functions, index)),
            Op::NewClosure { dst, count, code } => {
                let codes: Vec<String> = (0..u32::from(count)).map(|offset| constant(mc, constants, functions, code + offset)).collect();
                format!("NewClosure {{ dst: {dst}, codes: [{}] }}", codes.join(", "))
            }
            ref op => format!("{op:?}"),
        };
        let _ = writeln!(out, "      {at:<3} {text}");
    }
}
