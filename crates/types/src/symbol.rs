//! Symbols: interned strings, which [`string::intern`] keeps one per name, so symbols are
//! equal exactly when they're the same object. Each keeps its name's hash. The table holds
//! them weakly, so a symbol nothing else reaches is collected, and interning its name again
//! makes a new one. Keywords, `#:name`, are interned the same way, one for each symbol.

use std::hash::{BuildHasher, RandomState};

use crate::Error;
use crate::gc::table::{Table as GcTable, WeakObjects};
use crate::gc::{Gc, Mutation, OutOfMemory, Value};
use crate::objects::{self, Data, InternedFields, KeywordFields, SymFields};
use crate::string::{self, Str, Strings, Table};

#[cfg(test)]
#[path = "tests/symbol.rs"]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Symbol<'gc>(Gc<'gc, objects::Sym>);

impl<'gc> Symbol<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Sym(s)) => Some(Self(s)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// A flat string.
    pub fn name(self, mc: &Mutation<'gc>) -> Str<'gc> {
        Strings::new(mc).string(self.0.name(mc)).expect("a symbol's name is a string")
    }

    /// The name's hash, with the seed of the table that made the symbol.
    pub fn hash(self, mc: &Mutation<'gc>) -> u64 {
        self.0.hash(mc)
    }
}

/// A keyword: interned, so keywords are equal exactly when they're the same object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Keyword<'gc>(Gc<'gc, objects::Keyword>);

impl<'gc> Keyword<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Keyword(k)) => Some(Self(k)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// The symbol it's named as.
    pub fn symbol(self, mc: &Mutation<'gc>) -> Symbol<'gc> {
        Symbol(self.0.symbol(mc).expect("a keyword has its symbol"))
    }
}

/// An arena's intern table, whose probing [`string::intern`] does. Each arena has one, which
/// it keeps, so a name has one symbol wherever it's interned, the program's code included.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Symbols<'gc>(Gc<'gc, objects::Interned>);

impl<'gc> Symbols<'gc> {
    /// The arena's table. If it has none yet, it's made, its hashes seeded at random so which
    /// names collide can't be planned.
    pub fn of_arena(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Self::with_seed(mc, RandomState::new().hash_one(0u8))
    }

    /// The arena's table, made with `seed` if it has none yet.
    pub fn with_seed(mc: &Mutation<'gc>, seed: u64) -> Result<Self, OutOfMemory> {
        if let Some(symbols) = Self::of(Value::from_bits(mc.interned().get())) {
            return Ok(symbols);
        }
        let table = GcTable::<WeakObjects<objects::Sym>>::new(mc)?;
        let keywords = GcTable::<WeakObjects<objects::Keyword>>::new(mc)?;
        let symbols = Self(objects::Interned::new(mc, seed, Some(table.head()), Some(keywords.head()))?);
        mc.interned().set(symbols.value(mc).to_bits());
        Ok(symbols)
    }

    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Interned(t)) => Some(Self(t)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// The seed of the hashes the symbols keep.
    pub fn seed(self, mc: &Mutation<'gc>) -> u64 {
        self.0.seed(mc)
    }

    pub fn intern(self, h: &Strings<'_, 'gc>, s: Str<'gc>) -> Result<Symbol<'gc>, Error> {
        string::intern(h, &self.interner(h), s).map(Symbol)
    }

    /// The symbol named `s`, made without making a string first unless the name is new.
    #[inline]
    pub fn intern_str(self, h: &Strings<'_, 'gc>, s: &str) -> Result<Symbol<'gc>, Error> {
        string::intern_str(h, &self.interner(h), s).map(Symbol)
    }

    /// The keyword named as `symbol` is.
    pub fn keyword(self, mc: &Mutation<'gc>, symbol: Symbol<'gc>) -> Result<Keyword<'gc>, OutOfMemory> {
        let table = GcTable::<WeakObjects<objects::Keyword>>::of(self.0.keywords(mc).expect("an intern table has its keywords"));
        let same = |keyword: Gc<'gc, objects::Keyword>| Ok::<_, OutOfMemory>(keyword.symbol(mc) == Some(symbol.0));
        table.find_or_insert(mc, symbol.hash(mc), same, || objects::Keyword::new(mc, Some(symbol.0))).map(Keyword)
    }

    #[inline]
    fn interner<'a>(self, h: &Strings<'a, 'gc>) -> Interner<'a, 'gc> {
        let mc = h.mutation();
        let table = GcTable::of(self.0.table(mc).expect("an intern table has its table"));
        Interner { mc, seed: self.0.seed(mc), table }
    }

    #[cfg(test)]
    fn capacity(self, mc: &Mutation<'gc>) -> usize {
        self.interner(&Strings::new(mc)).table.capacity(mc)
    }
}

/// The table as [`Table`] sees it, kept private so only interning changes it.
struct Interner<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    seed: u64,
    table: GcTable<'gc, WeakObjects<objects::Sym>>,
}

impl<'gc> Table<Strings<'_, 'gc>> for Interner<'_, 'gc> {
    type Entry = Gc<'gc, objects::Sym>;

    fn seed(&self) -> u64 {
        self.seed
    }

    #[inline]
    fn find_or_insert(
        &self,
        _: &Strings<'_, 'gc>,
        hash: u64,
        same: impl Fn(Self::Entry) -> Result<bool, Error>,
        make: impl FnOnce() -> Result<Self::Entry, Error>,
    ) -> Result<Self::Entry, Error> {
        self.table.find_or_insert(self.mc, hash, same, make)
    }

    fn make(&self, _: &Strings<'_, 'gc>, name: Str<'gc>, hash: u64) -> Result<Self::Entry, Error> {
        Ok(objects::Sym::new(self.mc, name.value(), hash)?)
    }

    #[inline]
    fn name(&self, h: &Strings<'_, 'gc>, symbol: Self::Entry) -> Str<'gc> {
        h.string(symbol.name(self.mc)).expect("a symbol's name is a string")
    }
}
