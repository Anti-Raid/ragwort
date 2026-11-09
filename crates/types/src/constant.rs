//! A compilation unit's constants: kept in the arena behind one root, and named by index, so the
//! compiler can hold them across steps. Symbols, strings and numbers are merged by content, as
//! `eqv?` sees numbers and `equal?` strings; any other object gets a slot for each time it's
//! added. Immediates need no slot.

use std::collections::HashMap;
use std::hash::{BuildHasher, Hasher, RandomState};

use crate::Error;
use crate::gc::{GcVec, Immediate, Mutation, Root, Value, VecHead, slot};
use crate::num::{Number, Nums, complex};
use crate::string::{self, Str, Strings};
use crate::symbol::{Keyword, Symbol};
use crate::vector::{ImmutableVector, Vectors};

#[cfg(test)]
#[path = "tests/constant.rs"]
mod tests;

/// A constant's index in its pool.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Const(u32);

impl Const {
    pub fn index(self) -> u32 {
        self.0
    }
}

/// A finished pool, as code reads it: an immutable vector, indexed by `u32` as instructions name
/// constants.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Constants<'gc>(ImmutableVector<'gc>);

impl<'gc> Constants<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        ImmutableVector::of(v).map(Self)
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.value(mc)
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.len(mc)
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.0.is_empty(mc)
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: u32) -> Option<Value<'gc>> {
        self.0.get(mc, index as usize)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Constant {
    Immediate(Immediate),
    Pooled(Const),
}

/// It holds no brand, so it can live between steps, as a [`Root`] does. Using it with another
/// arena panics.
pub struct ConstPool {
    items: Root<VecHead<slot::Value>>,
    seed: u64,
    state: RandomState,
    /// The newest constant merged by each hash.
    heads: HashMap<u64, u32>,
    /// For each constant, the one before it with the same hash.
    older: Vec<Option<u32>>,
}

/// What's compared to merge a constant.
#[derive(Clone, Copy)]
enum Content<'gc> {
    Symbol(Symbol<'gc>),
    Keyword(Keyword<'gc>),
    String(Str<'gc>),
    Number(Number<'gc>),
}

impl ConstPool {
    pub fn new(mc: &Mutation<'_>) -> Result<Self, Error> {
        let items = Root::new(mc, GcVec::<slot::Value>::new(mc)?.head())?;
        let state = RandomState::new();
        Ok(Self { items, seed: state.hash_one(0u8), state, heads: HashMap::new(), older: Vec::new() })
    }

    pub fn len(&self) -> usize {
        self.older.len()
    }

    pub fn is_empty(&self) -> bool {
        self.older.is_empty()
    }

    fn items<'gc>(&self, mc: &Mutation<'gc>) -> GcVec<'gc> {
        GcVec::of(self.items.get(mc).expect("pool belongs to a different arena"))
    }

    /// `v` itself if it's immediate, and otherwise its slot: the one an equal constant has, or
    /// a new one. Failing changes nothing.
    pub fn add<'gc>(&mut self, mc: &Mutation<'gc>, v: Value<'gc>) -> Result<Constant, Error> {
        if let Some(i) = v.immediate() {
            return Ok(Constant::Immediate(i));
        }
        let hash = match content(mc, v) {
            Some(c) => {
                let hash = self.hash(mc, c)?;
                if let Some(old) = self.find(mc, c, hash)? {
                    return Ok(Constant::Pooled(old));
                }
                Some(hash)
            }
            None => None,
        };
        let index = u32::try_from(self.len()).map_err(|_| mc.out_of_memory())?;
        self.items(mc).push(mc, v)?;
        self.older.push(hash.and_then(|hash| self.heads.insert(hash, index)));
        Ok(Constant::Pooled(Const(index)))
    }

    /// The constant with this hash that's the same as `c`, if there's one.
    fn find<'gc>(&self, mc: &Mutation<'gc>, c: Content<'gc>, hash: u64) -> Result<Option<Const>, Error> {
        let items = self.items(mc);
        let mut at = self.heads.get(&hash).copied();
        while let Some(i) = at {
            let old = items.get(mc, i as usize).expect("a pool has the constants it named");
            if same(mc, c, old)? {
                return Ok(Some(Const(i)));
            }
            at = self.older[i as usize];
        }
        Ok(None)
    }

    /// The constant, if `c` is from this pool.
    pub fn get<'gc>(&self, mc: &Mutation<'gc>, c: Const) -> Option<Value<'gc>> {
        self.items(mc).get(mc, c.0 as usize)
    }

    /// The constants as they are now, in a vector the unit's code shares.
    pub fn finish<'gc>(&self, mc: &Mutation<'gc>) -> Result<Constants<'gc>, Error> {
        let items = self.items(mc).items(mc);
        Ok(Constants(Vectors::new(mc).immutable_with(self.len(), |i| items.map_or(Value::NIL, |s| s.get(i)))?))
    }

    fn hash<'gc>(&self, mc: &Mutation<'gc>, c: Content<'gc>) -> Result<u64, Error> {
        Ok(match c {
            Content::Symbol(s) => s.hash(mc),
            Content::Keyword(k) => k.symbol(mc).hash(mc),
            Content::String(s) => string::hash(&Strings::new(mc), s, self.seed)?,
            Content::Number(x) => {
                let mut state = self.state.build_hasher();
                complex::hash(&Nums::new(mc), x, &mut state);
                state.finish()
            }
        })
    }
}

fn content<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<Content<'gc>> {
    if let Some(s) = Symbol::of(v) {
        return Some(Content::Symbol(s));
    }
    if let Some(k) = Keyword::of(v) {
        return Some(Content::Keyword(k));
    }
    if let Some(s) = Strings::new(mc).string(v) {
        return Some(Content::String(s));
    }
    Nums::new(mc).number(v).map(Content::Number)
}

fn same<'gc>(mc: &Mutation<'gc>, c: Content<'gc>, old: Value<'gc>) -> Result<bool, Error> {
    Ok(match (c, content(mc, old)) {
        (Content::Symbol(a), Some(Content::Symbol(b))) => a == b,
        (Content::Keyword(a), Some(Content::Keyword(b))) => a == b,
        (Content::String(a), Some(Content::String(b))) => string::equal(&Strings::new(mc), a, b)?,
        (Content::Number(a), Some(Content::Number(b))) => complex::eqv(&Nums::new(mc), a, b),
        _ => false,
    })
}
