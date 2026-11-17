//! Handles that keep an object alive across steps, from outside the arena.

use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::gc::{Gc, Mutation, OBJECT, Object, OutOfMemory, TAG, Value};

/// The bytes charged for a root.
pub(crate) const ROOT_COST: usize = 32;

/// The collector's record of a rooted object. `word` is the object's value word, which is rewritten when the object moves. The arena holds one reference to the record and each
/// [`Root`] holds another. So the next collection removes a record whose roots were all dropped.
pub(crate) struct RootRecord {
    pub(crate) word: Cell<u64>,
}

/// A handle that keeps an object alive across steps. It has no brand, so it can live outside the arena,
/// such as in a task. [`Root::get`] returns the object inside a step. Once the last
/// clone is dropped, the next collection can free the object.
pub struct Root<T> {
    arena: u64,
    record: Rc<RootRecord>,
    _marker: PhantomData<fn() -> T>,
}

impl<T> Clone for Root<T> {
    fn clone(&self) -> Self {
        Self { arena: self.arena, record: self.record.clone(), _marker: PhantomData }
    }
}

/// The error for a root that is used with an arena other than its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForeignRoot;

impl fmt::Display for ForeignRoot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("root belongs to a different arena")
    }
}

impl std::error::Error for ForeignRoot {}

impl<T: Object> Root<T> {
    pub fn new<'gc>(mc: &Mutation<'gc>, object: Gc<'gc, T>) -> Result<Self, OutOfMemory> {
        let meta = mc.heap.m;
        meta.budget.count_allocation()?;
        meta.budget.charge(ROOT_COST)?;
        let record = Rc::new(RootRecord { word: Cell::new(Value::object(mc, object).to_bits()) });
        meta.handles.borrow_mut().push(record.clone());
        Ok(Self { arena: meta.id, record, _marker: PhantomData })
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>) -> Result<Gc<'gc, T>, ForeignRoot> {
        if self.arena != mc.heap.m.id {
            return Err(ForeignRoot);
        }
        Ok(Value::from_bits(self.record.word.get()).downcast(mc).expect("a root keeps its object"))
    }
}

/// A handle that keeps any value alive across steps, as a [`Root`] does for an object. Use it for code outside the arena that holds values of
/// any kind. A value that is not an object is stored in the handle itself, which costs the
/// arena nothing.
#[derive(Clone)]
pub struct ValueRoot {
    arena: u64,
    held: Held,
}

#[derive(Clone)]
enum Held {
    Word(u64),
    Record(Rc<RootRecord>),
}

impl ValueRoot {
    pub fn new<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Self, OutOfMemory> {
        let (meta, word) = (mc.heap.m, value.to_bits());
        if word & TAG != OBJECT {
            return Ok(Self { arena: meta.id, held: Held::Word(word) });
        }
        meta.budget.count_allocation()?;
        meta.budget.charge(ROOT_COST)?;
        let record = Rc::new(RootRecord { word: Cell::new(word) });
        meta.handles.borrow_mut().push(record.clone());
        Ok(Self { arena: meta.id, held: Held::Record(record) })
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>) -> Result<Value<'gc>, ForeignRoot> {
        if self.arena != mc.heap.m.id {
            return Err(ForeignRoot);
        }
        Ok(Value::from_bits(match &self.held {
            Held::Word(word) => *word,
            Held::Record(record) => record.word.get(),
        }))
    }
}
