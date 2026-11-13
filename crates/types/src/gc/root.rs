//! Handles that keep an object alive across steps, from outside the arena.

use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::gc::{Gc, Mutation, OBJECT, Object, OutOfMemory, TAG, Value};

/// What a root is charged.
pub(crate) const ROOT_COST: usize = 32;

/// The object's value word, rewritten when it moves. The arena holds one reference and each
/// [`Root`] another, so a record whose roots were all dropped is pruned once traced.
pub(crate) struct RootRecord {
    pub(crate) word: Cell<u64>,
}

/// Keeps an object alive across steps. It holds no brand, so it can live outside the arena,
/// such as in a task; [`Root::get`] reads the object back inside a step. Dropping the last
/// clone lets the next collection free the object.
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

/// A root used with an arena other than its own.
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

/// Keeps any value alive across steps, as a [`Root`] keeps an object, for what holds values of
/// any kind outside the arena. One that isn't an object is kept in the handle, which costs the
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
