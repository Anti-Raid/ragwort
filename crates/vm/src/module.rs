//! What modules are made of at run time: the instance that holds a module's variables, the
//! functions the host carries out, and the objects that hold the host's own things.
//!
//! A host function is a plain function the host defines with a [`HostDef`]. A run calls it in
//! the loop, for a [`crate::Op::CallHost`], from the table of them its code's module has, with the
//! arguments and a [`HostContext`], and nothing of the machine's. Only native ragwort calls one,
//! with `%call-host`, so what it needs of the caller's state, such as its coroutine or a mark,
//! or of the host's, as an [`ExternalRef`], is passed by the native procedure that wraps it,
//! which other code calls as it would any other.

use std::any::{Any, TypeId};
use std::fmt;

use ragwort_types::gc::{Frame, Gc, Mutation, OutOfMemory, Value};
use ragwort_types::vector::Vectors;

use crate::objects::{ExternalRef, ExternalRefFields, Module, ModuleFields};
use crate::{Fault, Fuel};

/// A host function.
pub type HostFn = for<'s, 'gc> fn(&mut HostContext<'s, 'gc>, HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault>;

/// A host function as the host defines it, in a static table, a module's, that every machine
/// shares. [`host!`](crate::host!) makes one.
#[derive(Clone, Copy, Debug)]
pub struct HostDef {
    pub name: &'static str,
    /// As [`crate::objects::Bytecode`] counts arguments.
    pub arity: i64,
    pub purity: Purity,
    pub function: HostFn,
    /// What tells `function` apart from other functions: [`HostDef::id_of`] it.
    pub id: TypeId,
}

/// A [`HostDef`]: `host!(name, arity, purity, function)`, with `function` a path to a Rust
/// function, whose `id` it gives.
#[macro_export]
macro_rules! host {
    ($name:expr, $arity:expr, $purity:expr, $function:path $(,)?) => {
        $crate::HostDef { name: $name, arity: $arity, purity: $purity, function: $function, id: $crate::HostDef::id_of(&$function) }
    };
}

impl HostDef {
    /// The id of `function`, a Rust function: its type's, which no other function has.
    pub const fn id_of<F: 'static>(_function: &F) -> TypeId {
        TypeId::of::<F>()
    }

    /// Whether it takes `n` arguments.
    #[inline]
    pub fn takes(&self, n: usize) -> bool {
        takes(self.arity, n)
    }
}

/// The same function, as the same host function.
impl PartialEq for HostDef {
    fn eq(&self, other: &Self) -> bool {
        (self.name, self.arity, self.purity, self.id) == (other.name, other.arity, other.purity, other.id)
    }
}

impl Eq for HostDef {}

/// What the compiler can take a host function's calls to do, given as many arguments as it
/// takes. A function that replies other than with a value is [`Purity::Impure`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Purity {
    /// Anything: each call is kept, in order.
    Impure,
    /// Nothing but read its arguments, which can't have changed, and return a value or fault.
    Pure,
    /// As [`Purity::Pure`], never faulting, so a call whose value goes unused can go.
    Discardable,
}

impl Purity {
    /// Whether calls of it and others like it can be made in any order: one that can fault only
    /// changes which of them faults first.
    pub const fn is_reorderable(self) -> bool {
        !matches!(self, Purity::Impure)
    }
}

/// What a host function's call returns, or does instead.
pub enum Reply<'gc> {
    Value(Value<'gc>),
    /// Calls the procedure with the elements of the list as its arguments, in place of the
    /// host's call, so what it returns is what the host's call does.
    Call(Value<'gc>, Value<'gc>),
    /// Raises the value, as `raise` does, from the host's call.
    Raise(Value<'gc>),
    /// Suspends the machine with [`crate::Outcome::Deferred`], with this, until
    /// [`crate::Machine::reply`] or [`crate::Machine::raise`] answers the call.
    Defer(Box<dyn Any>),
}

/// What a host function gets of the run that calls it.
pub struct HostContext<'s, 'gc> {
    pub(crate) mc: &'s Mutation<'gc>,
    pub(crate) fuel: &'s mut Fuel,
}

impl<'s, 'gc> HostContext<'s, 'gc> {
    #[inline]
    pub fn mc(&self) -> &'s Mutation<'gc> {
        self.mc
    }

    /// Spends `units` of the machine's fuel, for work the call does, or faults with
    /// [`Fault::OutOfFuel`] if there aren't that many.
    #[inline]
    pub fn charge(&mut self, units: u64) -> Result<(), Fault> {
        self.fuel.spend(units)
    }
}

/// A host function's arguments, read where they are, in the caller's registers.
#[derive(Clone, Copy)]
pub struct HostArgs<'s, 'gc> {
    frame: Frame<'s, 'gc>,
    base: u8,
    len: u8,
}

impl<'s, 'gc> HostArgs<'s, 'gc> {
    #[inline]
    pub(crate) fn registers(frame: Frame<'s, 'gc>, base: u8, len: u8) -> Self {
        HostArgs { frame, base, len }
    }

    #[inline]
    pub fn len(self) -> usize {
        usize::from(self.len)
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn get(self, i: usize) -> Option<Value<'gc>> {
        let i = u8::try_from(i).ok().filter(|&i| i < self.len)?;
        Some(self.frame.get(self.base + i))
    }

    #[inline]
    pub fn iter(self) -> impl ExactSizeIterator<Item = Value<'gc>> + use<'s, 'gc> {
        (0..self.len()).map(move |i| self.get(i).expect("an argument below the count"))
    }
}

impl fmt::Debug for HostArgs<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// What a [`Reply::Defer`] left with the machine, which [`crate::Outcome::Deferred`] hands back.
pub struct Deferred(Box<Box<dyn Any>>);

impl Deferred {
    pub(crate) fn new(data: Box<dyn Any>) -> Self {
        Deferred(Box::new(data))
    }

    pub fn into_inner(self) -> Box<dyn Any> {
        *self.0
    }
}

impl fmt::Debug for Deferred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Deferred")
    }
}

/// To any other, as what it holds is the host's, opaque to the machine.
impl PartialEq for Deferred {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for Deferred {}

/// A module named `name`, with a variable for each of `names`, none defined yet, whose code
/// calls `hosts`: those of its own native code, and those the code it inlines from other modules
/// calls.
pub fn new<'gc>(mc: &Mutation<'gc>, name: Value<'gc>, names: &[Value<'gc>], hosts: impl IntoIterator<Item = &'static HostDef>) -> Result<Gc<'gc, Module>, OutOfMemory> {
    let vector = Vectors::new(mc).immutable_from_slice(names)?.value(mc);
    let interface: Box<dyn Any> = Box::new(());
    let hosts: Box<[&'static HostDef]> = hosts.into_iter().collect();
    Module::new(mc, name, vector, mc.frozen(hosts)?, mc.frozen(interface)?, names.len(), Value::UNDEFINED)
}

/// What the compiler knows of what `module` exports, if it's a `T`.
pub fn interface<'gc, T: Any>(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<&'gc T> {
    module.interface(mc)?.downcast_ref()
}

/// Sets what the compiler knows of what `module` exports.
pub fn set_interface<'gc, T: Any>(mc: &Mutation<'gc>, module: Gc<'gc, Module>, interface: T) -> Result<(), OutOfMemory> {
    let interface: Box<dyn Any> = Box::new(interface);
    module.set_interface(mc, mc.frozen(interface)?);
    Ok(())
}

/// An [`ExternalRef`] of `data`, which owns `bytes` outside the arena that it's charged for,
/// holding `held`.
pub fn external<'gc, T: Any>(mc: &Mutation<'gc>, data: T, bytes: usize, held: Value<'gc>) -> Result<Gc<'gc, ExternalRef>, OutOfMemory> {
    let data: Box<dyn Any> = Box::new(data);
    ExternalRef::new(mc, held, mc.frozen_owning(data, bytes)?)
}

/// The data of `external`, if it's an [`ExternalRef`] of a `T`.
pub fn external_data<'gc, T: Any>(mc: &Mutation<'gc>, external: Value<'gc>) -> Option<&'gc T> {
    external.downcast::<ExternalRef>(mc)?.data(mc)?.downcast_ref()
}

/// Whether code that takes `arity` arguments, as [`crate::objects::Bytecode`] counts them,
/// takes `n`.
#[inline]
pub(crate) fn takes(arity: i64, n: usize) -> bool {
    let n = n as i64;
    if arity == n {
        true
    } else if arity < 0 {
        n >= -(arity + 1)
    } else {
        crate::frame::Shape::of(arity).takes(n as u64)
    }
}
