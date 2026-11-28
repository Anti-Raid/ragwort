//! Procedures made of Rust closures.
//!
//! A host function of the VM is a plain Rust function in a static table, which only native code can call. This module makes a procedure
//! of any Rust closure, at run time. A program calls the procedure like any other.
//!
//! # How to use it
//!
//! - [`Hosting::install`] sets an arena up, once. Keep the value that it returns alive, for example in a root.
//! - [`Hosting::procedure`] makes a procedure of a closure.
//!
//! The closure runs inside the step of the call, as a host function of the VM does. It gets the same [`HostContext`] and [`HostArgs`], and it
//! returns the same [`Reply`]: a value, a call to make in its place, or a value to raise.
//!
//! ```
//! use ragwort::host::{Arity, Hosting};
//! use ragwort_types::gc::{Arena, Value};
//! use ragwort_types::symbol::Symbols;
//! use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome, Reply};
//!
//! let mut arena = Arena::new(1 << 22, 0);
//! arena.mutate(|mc| {
//!     let symbols = Symbols::of_arena(mc).unwrap();
//!     let hosting = Hosting::install(mc, symbols).unwrap();
//!     let double = hosting
//!         .procedure(mc, None, Arity::Exactly(1), &[], |_, args, _| {
//!             let number = args.get(0).and_then(Value::as_fixnum).ok_or(Fault::WrongType)?;
//!             Ok(Reply::Value(Value::fixnum(number * 2).ok_or(Fault::OutOfRange)?))
//!         })
//!         .unwrap();
//!     let mut machine = Machine::new(mc, MIN_SEGMENT, double, &[Value::fixnum(21).unwrap()]).unwrap();
//!     assert_eq!(machine.run(mc), Ok(Outcome::Done(Value::fixnum(42).unwrap())));
//! });
//! ```
//!
//! # Values that a closure needs
//!
//! Pass the arena values that a closure needs as `captures`. They are stored in the arena with the closure, and the closure reads and writes
//! them through [`Captures`]. The collector sees them, so a procedure and a value that refer to each other are collected together.
//!
//! A closure can also own a [`Handle`](ragwort_types::gc::Handle). The collector cannot see inside a closure, so a handle keeps its value alive
//! as long as the procedure lives. If the value refers back to the procedure, neither is ever collected. Use a capture, or a
//! [`WeakHandle`](ragwort_types::gc::WeakHandle).
//!
//! # How it works
//!
//! A procedure is a closure of the VM over a [`Callback`] object, which holds the Rust closure and the captures. The closure's code is one
//! instruction: a call of one host function, in tail position, with the frame's own registers as the arguments. A frame holds its closure in
//! register 0 and its arguments after it, so the host function gets the closure and the arguments with no copying. It finds the callback in the
//! closure and calls the Rust closure.
//!
//! The code is made here, not compiled. There is one code object for each [`Arity`], made when the arity is first used. A procedure with a name
//! has a copy of the code object, because the code holds the name. The copy shares the instruction.
//!
//! A procedure of a closure cannot be saved in an image.

use ragwort_types::gc::{Gc, Mutation, OutOfMemory, Value, objects};
use ragwort_types::string::Strings;
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::vector::{Vector, Vectors};
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Module, ModuleFields};
use ragwort_vm::{Capture, Fault, HostArgs, HostContext, HostDef, Op, Purity, Reply, host};

#[cfg(test)]
#[path = "tests/host.rs"]
mod tests;

/// The largest number of fixed parameters that a procedure of a closure can have.
pub const MAX_FIXED: usize = 8;

/// The name of the module that the code of the procedures belongs to.
pub const MODULE: &str = "ragwort/host";

/// The number of arities: one with and one without further arguments, for each number of fixed parameters.
const ARITIES: usize = 2 * (MAX_FIXED + 1);

/// A Rust closure as the arena stores it.
pub type HostClosure = Box<dyn for<'s, 'gc> Fn(&mut HostContext<'s, 'gc>, HostArgs<'s, 'gc>, Captures<'gc>) -> Result<Reply<'gc>, Fault>>;

objects! {
    pub kind Embedding after ragwort_vm::objects::Vm;

    /// A Rust closure in the arena. The items are the values that it was made with, which it reads and writes through [`Captures`].
    pub struct Callback { function: Frozen<crate::host::HostClosure> } items Value
}

/// The number of arguments that a procedure of a closure takes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arity {
    /// Exactly this many arguments.
    Exactly(usize),
    /// This many arguments or more. The closure gets one more argument after the fixed ones: a list of the further arguments.
    AtLeast(usize),
}

impl Arity {
    /// Returns the position of the arity's code in a [`Hosting`], or `None` if it has more than [`MAX_FIXED`] fixed parameters.
    fn position(self) -> Option<usize> {
        let (fixed, rest) = match self {
            Arity::Exactly(fixed) => (fixed, 0),
            Arity::AtLeast(fixed) => (fixed, 1),
        };
        if fixed <= MAX_FIXED {
            Some(2 * fixed + rest)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    OutOfMemory,
    /// The arity has more than [`MAX_FIXED`] fixed parameters.
    TooManyParameters,
}

impl From<OutOfMemory> for Error {
    fn from(_: OutOfMemory) -> Self {
        Error::OutOfMemory
    }
}

/// The values that a closure was made with. They live in the arena, where the collector sees them.
#[derive(Clone, Copy)]
pub struct Captures<'gc>(Gc<'gc, Callback>);

impl<'gc> Captures<'gc> {
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.items(mc).len()
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let items = self.0.items(mc);
        if index < items.len() {
            Some(items.get(index))
        } else {
            None
        }
    }

    /// Replaces the value at `index`. Returns `false` if there is no such value.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> bool {
        let items = self.0.items(mc);
        if index < items.len() {
            items.set(mc, index, value);
            true
        } else {
            false
        }
    }
}

static HOSTS: [HostDef; 1] = [host!("call", -2, Purity::Impure, call)];

/// The one host function behind every procedure of a closure. Its first argument is the procedure itself, which holds the [`Callback`]. The rest are
/// the closure's arguments.
fn call<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    let items = args.get(0).and_then(|value| value.downcast::<Closure>(mc)).ok_or(Fault::Malformed)?.items(mc);
    if items.len() != 1 {
        return Err(Fault::Malformed);
    }
    let callback = items.get(0).downcast::<Callback>(mc).ok_or(Fault::Malformed)?;
    let function = callback.function(mc).ok_or(Fault::Malformed)?;
    function(cx, args.after(1), Captures(callback))
}

/// What an arena needs to make procedures of closures. It is a vector:
///
/// - The last slot holds the module that the code belongs to. The module has the host function.
/// - Each slot before it holds the code of one [`Arity`], or `#f` until the arity is first used.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Hosting<'gc>(Vector<'gc>);

impl<'gc> Hosting<'gc> {
    /// Sets the arena up: makes the module [`MODULE`]. The caller keeps the returned value alive, and needs it to make procedures.
    pub fn install(mc: &Mutation<'gc>, symbols: Symbols<'gc>) -> Result<Self, Error> {
        // The only failure of interning this name is the lack of memory.
        let name = symbols.intern_str(&Strings::new(mc), MODULE).map_err(|_| Error::OutOfMemory)?;
        let module = ragwort_vm::module::new(mc, name.value(mc), &[], &HOSTS)?;
        let slots = Vectors::new(mc).make(ARITIES + 1, Value::FALSE)?;
        slots.items(mc).set(mc, ARITIES, Value::object(mc, module));
        Ok(Self(slots))
    }

    /// Returns `value` as a [`Hosting`], if it is the value of one.
    pub fn of(mc: &Mutation<'gc>, value: Value<'gc>) -> Option<Self> {
        let slots = Vector::of(value)?;
        let items = slots.items(mc);
        if items.len() != ARITIES + 1 {
            return None;
        }
        let hosts = items.get(ARITIES).downcast::<Module>(mc)?.hosts(mc)?;
        if hosts.len() == 1 && *hosts[0] == HOSTS[0] {
            Some(Self(slots))
        } else {
            None
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.value(mc)
    }

    /// Returns the code of the procedures of `arity`, whose position is `position`. Makes it if this is the first use of the arity.
    fn code(self, mc: &Mutation<'gc>, arity: Arity, position: usize) -> Result<Gc<'gc, Bytecode>, OutOfMemory> {
        let items = self.0.items(mc);
        if let Some(code) = items.get(position).downcast::<Bytecode>(mc) {
            return Ok(code);
        }
        // `encoded` is the arity as code states it. `passed` counts the registers that the host function gets: the closure, the fixed arguments,
        // and the list of the further arguments if there is one.
        let (encoded, passed) = match arity {
            Arity::Exactly(fixed) => (fixed as i64, fixed + 1),
            Arity::AtLeast(fixed) => (-(fixed as i64) - 1, fixed + 2),
        };
        let ops: Box<[Op]> = Box::new([Op::TailCallHost { base: 0, args: passed as u8, host: 0 }]);
        // The closures are made by `procedure`, not by an instruction, so the code says nothing about where captured values come from.
        let captures: Box<[Capture]> = Box::new([]);
        let constants = Vectors::new(mc).immutable_from_slice(&[])?.value(mc);
        let module = items.get(ARITIES).downcast::<Module>(mc);
        let code = Bytecode::new(mc, mc.frozen(ops)?, constants, mc.frozen(captures)?, encoded, module, Value::FALSE, Value::FALSE, 0, Value::FALSE, 0, 0, None)?;
        items.set(mc, position, Value::object(mc, code));
        Ok(code)
    }

    /// Makes a procedure that calls `function`.
    ///
    /// - `name` is the name that error messages and tracebacks show for the procedure.
    /// - `arity` is the number of arguments that the procedure takes. A call with another number of arguments raises an error, and does not reach `function`.
    /// - `captures` are arena values for `function`. See [`Captures`].
    pub fn procedure<F>(self, mc: &Mutation<'gc>, name: Option<Symbol<'gc>>, arity: Arity, captures: &[Value<'gc>], function: F) -> Result<Value<'gc>, Error>
    where
        F: for<'s, 'g> Fn(&mut HostContext<'s, 'g>, HostArgs<'s, 'g>, Captures<'g>) -> Result<Reply<'g>, Fault> + 'static,
    {
        let position = arity.position().ok_or(Error::TooManyParameters)?;
        let code = self.code(mc, arity, position)?;
        let code = match name {
            Some(name) => renamed(mc, code, name)?,
            None => code,
        };
        let boxed: HostClosure = Box::new(function);
        let callback = Callback::new(mc, mc.frozen(boxed)?, captures.len(), Value::VOID)?;
        let items = callback.items(mc);
        for (index, capture) in captures.iter().enumerate() {
            items.set(mc, index, *capture);
        }
        let closure = Closure::new(mc, Some(code), 1, Value::object(mc, callback))?;
        Ok(Value::object(mc, closure))
    }
}

/// Returns a copy of `code` that has the name `name`. The copy shares the instructions of `code`.
fn renamed<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, name: Symbol<'gc>) -> Result<Gc<'gc, Bytecode>, OutOfMemory> {
    // The code was made by `Hosting::code`, which gives it both frozen values.
    let ops = code.frozen_ref(mc, Bytecode::OPS).expect("the code has instructions");
    let captures = code.frozen_ref(mc, Bytecode::CAPTURES).expect("the code has a capture list");
    Bytecode::new(mc, ops, code.constants(mc), captures, code.arity(mc), code.module(mc), name.value(mc), code.source(mc), code.start(mc), code.sites(mc), code.lines_start(mc), code.lines_len(mc), code.hints(mc))
}
