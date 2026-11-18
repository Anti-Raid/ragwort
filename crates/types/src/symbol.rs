//! Symbols: interned strings. [`string::intern`] keeps one symbol per name, so two symbols are
//! equal exactly when they are the same object. Each symbol stores the hash of its name. The
//! intern table holds symbols weakly. So a symbol that nothing else references is collected, and
//! interning its name again creates a new symbol. Keywords, `#:name`, are interned the same way,
//! one per symbol.

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
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Sym(sym)) => Some(Self(sym)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// Returns the symbol's name, which is a flat string.
    pub fn name(self, mc: &Mutation<'gc>) -> Str<'gc> {
        Strings::new(mc).string(self.0.name(mc)).expect("a symbol's name is a string")
    }

    /// Returns the hash of the name, seeded with the seed of the intern table that created the symbol.
    pub fn hash(self, mc: &Mutation<'gc>) -> u64 {
        self.0.hash(mc)
    }
}

/// A keyword. Keywords are interned, so two keywords are equal exactly when they are the same object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Keyword<'gc>(Gc<'gc, objects::Keyword>);

impl<'gc> Keyword<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Keyword(keyword)) => Some(Self(keyword)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// Returns the symbol that has the keyword's name.
    pub fn symbol(self, mc: &Mutation<'gc>) -> Symbol<'gc> {
        Symbol(self.0.symbol(mc).expect("a keyword has its symbol"))
    }
}

/// An arena's intern table. [`string::intern`] does the probing. Each arena has one intern table
/// and keeps it alive. So a name has one symbol wherever it is interned, including in the
/// program's code.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Symbols<'gc>(Gc<'gc, objects::Interned>);

impl<'gc> Symbols<'gc> {
    /// Returns the arena's intern table. If the arena has none yet, this creates it with a random
    /// hash seed, so that collisions between names cannot be predicted.
    pub fn of_arena(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        // A random seed is only made for the arena's first table. Making one takes far longer than finding the table.
        if let Some(symbols) = Self::of(Value::from_bits(mc.interned().get())) {
            return Ok(symbols);
        }
        Self::with_seed(mc, RandomState::new().hash_one(0u8))
    }

    /// Returns the arena's intern table. If the arena has none yet, this creates it with `seed`.
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

    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Interned(interned)) => Some(Self(interned)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// Returns the seed of the hashes that the symbols store.
    pub fn seed(self, mc: &Mutation<'gc>) -> u64 {
        self.0.seed(mc)
    }

    pub fn intern(self, strings: &Strings<'_, 'gc>, name: Str<'gc>) -> Result<Symbol<'gc>, Error> {
        string::intern(strings, &self.interner(strings), name).map(Symbol)
    }

    /// Returns the symbol named `name`. A string is allocated for the name only if the symbol is new.
    #[inline]
    pub fn intern_str(self, strings: &Strings<'_, 'gc>, name: &str) -> Result<Symbol<'gc>, Error> {
        string::intern_str(strings, &self.interner(strings), name).map(Symbol)
    }

    /// Returns the keyword that has the name of `symbol`. Creates the keyword if it does not exist.
    pub fn keyword(self, mc: &Mutation<'gc>, symbol: Symbol<'gc>) -> Result<Keyword<'gc>, OutOfMemory> {
        let table = GcTable::<WeakObjects<objects::Keyword>>::of(self.0.keywords(mc).expect("an intern table has its keywords"));
        table
            .find_or_insert(
                mc,
                symbol.hash(mc),
                |keyword: Gc<'gc, objects::Keyword>| Ok::<_, OutOfMemory>(keyword.symbol(mc) == Some(symbol.0)),
                || objects::Keyword::new(mc, Some(symbol.0)),
            )
            .map(Keyword)
    }

    #[inline]
    fn interner<'a>(self, strings: &Strings<'a, 'gc>) -> Interner<'a, 'gc> {
        let mc = strings.mutation();
        let table = GcTable::of(self.0.table(mc).expect("an intern table has its table"));
        Interner { mc, seed: self.0.seed(mc), table }
    }

    #[cfg(test)]
    fn capacity(self, mc: &Mutation<'gc>) -> usize {
        self.interner(&Strings::new(mc)).table.capacity(mc)
    }
}

/// The intern table as an implementation of [`Table`]. It is private, so that only interning can modify the table.
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
    fn name(&self, strings: &Strings<'_, 'gc>, symbol: Self::Entry) -> Str<'gc> {
        strings.string(symbol.name(self.mc)).expect("a symbol's name is a string")
    }
}
