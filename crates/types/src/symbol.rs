//! Symbols: interned strings, which [`string::intern`] keeps one per name, so symbols are
//! equal exactly when they're the same object. Each keeps its name's hash. The table holds
//! them weakly, so a symbol nothing else reaches is collected, and interning its name again
//! makes a new one.

use std::hash::{BuildHasher, RandomState};
use std::marker::PhantomData;

use ragwort_gc::{Gc, Lock, Member, Plain, Trace, Value, Weak};

use crate::Error;
use crate::string::{self, Str, Strings, Table};

#[cfg(test)]
mod tests;

/// A symbol's name, a flat string, and the name's hash.
#[derive(Trace, Plain)]
pub struct Sym<'gc> {
    name: Value<'gc>,
    hash: u64,
}

/// A [`Sym`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Symbol<'gc>(Value<'gc>);

impl<'gc> Symbol<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

#[derive(Trace, Plain)]
struct Slot<'gc> {
    /// The symbol's hash with the low bit set, or zero for a slot never used. A slot keeps
    /// its hash after its symbol dies, so probes go on past it, until the table is rebuilt.
    key: Lock<u64>,
    symbol: Weak<'gc, Sym<'gc>>,
}

impl Slot<'_> {
    fn empty() -> Self {
        Self { key: Lock::new(0), symbol: Weak::empty() }
    }
}

#[derive(Trace, Plain)]
#[gc(items = Slot<'gc>)]
struct Slots<'gc>(PhantomData<&'gc ()>);

/// The intern table, whose probing [`string::intern`] does. It belongs in the arena root, or
/// in an object the root reaches.
#[derive(Trace, Plain)]
pub struct Symbols<'gc> {
    seed: u64,
    slots: Lock<Option<Member<'gc, Slots<'gc>>>>,
    /// Slots with a key: live symbols, and dead ones not yet cleared out.
    used: Lock<u32>,
}

impl<'gc> Symbols<'gc> {
    /// A table whose hashes are seeded at random, so which names collide can't be planned.
    pub fn new() -> Self {
        Self::with_seed(RandomState::new().hash_one(0u8))
    }

    pub fn with_seed(seed: u64) -> Self {
        Self { seed, slots: Lock::new(None), used: Lock::new(0) }
    }

    /// The seed of the hashes the symbols keep.
    pub fn seed(&self) -> u64 {
        self.seed
    }

    pub fn intern(&self, h: &Strings<'_, 'gc>, s: Str<'gc>) -> Result<Symbol<'gc>, Error> {
        Ok(Symbol(Value::object(h.mc, string::intern(h, &Interner(self), s)?)))
    }

    /// The symbol named `s`, made without making a string first unless the name is new.
    pub fn intern_str(&self, h: &Strings<'_, 'gc>, s: &str) -> Result<Symbol<'gc>, Error> {
        Ok(Symbol(Value::object(h.mc, string::intern_str(h, &Interner(self), s)?)))
    }

    #[cfg(test)]
    fn capacity(&self, h: &Strings<'_, 'gc>) -> usize {
        Interner(self).slots(h).len()
    }
}

impl Default for Symbols<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// The table's storage as [`Table`] sees it, kept private so only interning changes it.
struct Interner<'s, 'gc>(&'s Symbols<'gc>);

impl<'gc> Table<Strings<'_, 'gc>> for Interner<'_, 'gc> {
    type Symbol = Gc<'gc, Sym<'gc>>;
    type Slot = Slot<'gc>;

    fn seed(&self) -> u64 {
        self.0.seed
    }

    fn slots<'a>(&'a self, h: &'a Strings<'_, 'gc>) -> &'a [Slot<'gc>] {
        self.0.slots.load(h.mc).map_or(&[], |slots| slots.items())
    }

    fn replace<'a>(&'a self, h: &'a Strings<'_, 'gc>, len: usize) -> Result<&'a [Slot<'gc>], Error> {
        let slots = h.mc.alloc_inline(Slots(PhantomData), len, |_| Slot::empty())?;
        self.0.slots.store(h.mc, Some(slots));
        Ok(slots.items())
    }

    fn key(&self, slot: &Slot<'gc>) -> u64 {
        slot.key.get()
    }

    fn symbol(&self, h: &Strings<'_, 'gc>, slot: &Slot<'gc>) -> Option<Gc<'gc, Sym<'gc>>> {
        slot.symbol.get(h.mc)
    }

    fn set(&self, h: &Strings<'_, 'gc>, slot: &Slot<'gc>, key: u64, symbol: Gc<'gc, Sym<'gc>>) {
        slot.key.set(h.mc, key);
        slot.symbol.set(h.mc, symbol);
    }

    fn used(&self) -> usize {
        self.0.used.get() as usize
    }

    fn set_used(&self, h: &Strings<'_, 'gc>, used: usize) {
        self.0.used.set(h.mc, used as u32);
    }

    fn make(&self, h: &Strings<'_, 'gc>, name: Str<'gc>, hash: u64) -> Result<Gc<'gc, Sym<'gc>>, Error> {
        Ok(h.mc.alloc(Sym { name: name.value(), hash })?)
    }

    fn name(&self, _: &Strings<'_, 'gc>, symbol: Gc<'gc, Sym<'gc>>) -> Str<'gc> {
        Str(symbol.name)
    }
}

impl<'gc> Strings<'_, 'gc> {
    pub fn symbol(&self, v: Value<'gc>) -> Option<Symbol<'gc>> {
        v.downcast_tag(self.mc, self.sym).map(|_| Symbol(v))
    }

    pub fn name(&self, s: Symbol<'gc>) -> Str<'gc> {
        Str(self.sym_of(s).name)
    }

    /// The name's hash, with the seed of the table that made the symbol.
    pub fn symbol_hash(&self, s: Symbol<'gc>) -> u64 {
        self.sym_of(s).hash
    }

    fn sym_of(&self, s: Symbol<'gc>) -> Gc<'gc, Sym<'gc>> {
        s.0.downcast_tag(self.mc, self.sym).expect("a symbol")
    }
}
