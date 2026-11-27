//! Handles that keep an object alive across steps, from outside the arena.
//!
//! There are two kinds:
//!
//! - A [`Root`] or a [`ValueRoot`] has a record of its own, which is allocated when the root is made. Clones share the record.
//!   Use one for a value that is rooted once and kept, such as a loaded module.
//! - A [`Handle`] takes a slot in the arena's root table. Making, cloning and dropping one allocates nothing.
//!   Use one for values that come and go, such as the arguments of a call into the host.
//! - A [`WeakHandle`] takes a slot too, and does not keep its value alive.

use std::cell::{Cell, Ref, RefCell};
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

/// The table of the values that [`Handle`]s keep alive. The arena and every handle hold it.
///
/// A slot holds the value word of one handle's value, or 0 while it is free. The collector marks from the slots and rewrites a word when its object moves.
pub(crate) struct RootTable {
    /// The id of the arena that the table belongs to.
    arena: u64,
    /// The slots of the handles. The collector marks from them.
    strong: Slots,
    /// The slots of the weak handles. The collector does not mark from them, and empties the slot of an object that has died.
    weak: Slots,
}

/// Slots of one kind, with the numbers of the free ones. A slot holds the value word of one handle's value, or 0 while it is free or once its object has died.
struct Slots {
    words: RefCell<Vec<Cell<u64>>>,
    free: RefCell<Vec<u32>>,
}

impl Slots {
    fn new() -> Self {
        Self { words: RefCell::new(Vec::new()), free: RefCell::new(Vec::new()) }
    }

    fn bytes(&self) -> usize {
        self.words.borrow().capacity() * size_of::<Cell<u64>>() + self.free.borrow().capacity() * size_of::<u32>()
    }

    /// Puts `word` in a slot and returns the number of the slot. A free slot is used if there is one, and the slots grow otherwise.
    fn take(&self, word: u64) -> u32 {
        if let Some(slot) = self.free.borrow_mut().pop() {
            self.words.borrow()[slot as usize].set(word);
            return slot;
        }
        let mut words = self.words.borrow_mut();
        words.push(Cell::new(word));
        (words.len() - 1) as u32
    }

    fn word(&self, slot: u32) -> u64 {
        self.words.borrow()[slot as usize].get()
    }

    fn release(&self, slot: u32) {
        self.words.borrow()[slot as usize].set(0);
        self.free.borrow_mut().push(slot);
    }
}

impl RootTable {
    pub(crate) fn new(arena: u64) -> Self {
        Self { arena, strong: Slots::new(), weak: Slots::new() }
    }

    /// Returns the slots of the handles, for the collector.
    pub(crate) fn slots(&self) -> Ref<'_, Vec<Cell<u64>>> {
        self.strong.words.borrow()
    }

    /// Returns the slots of the weak handles, for the collector.
    pub(crate) fn weak_slots(&self) -> Ref<'_, Vec<Cell<u64>>> {
        self.weak.words.borrow()
    }

    /// Returns the bytes that the table takes outside the region.
    pub(crate) fn bytes(&self) -> usize {
        self.strong.bytes() + self.weak.bytes()
    }

    /// Returns the number of slots that keep a value alive.
    pub(crate) fn held(&self) -> usize {
        self.strong.words.borrow().len() - self.strong.free.borrow().len()
    }
}

/// A handle that keeps a value alive across steps, in a slot of the arena's root table. It has no brand, so it can live outside the arena.
///
/// Making a handle allocates nothing: it takes a free slot of the table, which grows only when every slot is in use. A clone takes a slot of its own with the same
/// value, and dropping a handle frees its slot at once. A value that is not an object is stored in the handle itself and takes no slot.
///
/// [`Handle::get`] returns the value inside a step. A handle of an object belongs to one arena, and is refused by any other.
pub struct Handle {
    /// The table of the arena, or `None` for a value that is not an object.
    table: Option<Rc<RootTable>>,
    /// The number of the slot, or the value word of a value that is not an object.
    word: u64,
}

impl Handle {
    pub fn new<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Self, OutOfMemory> {
        let (meta, word) = (mc.heap.m, value.to_bits());
        if word & TAG != OBJECT {
            return Ok(Self { table: None, word });
        }
        let table = &meta.rooted;
        // The table grows only if no slot is free. Growth is an allocation outside the region, so it can fail as one does.
        if table.strong.free.borrow().is_empty() {
            meta.budget.count_allocation()?;
            meta.budget.ensure(size_of::<Cell<u64>>())?;
        }
        Ok(Self { table: Some(table.clone()), word: u64::from(table.strong.take(word)) })
    }

    /// Returns the value. Fails if the handle keeps an object of another arena.
    #[inline]
    pub fn get<'gc>(&self, mc: &Mutation<'gc>) -> Result<Value<'gc>, ForeignRoot> {
        let Some(table) = &self.table else { return Ok(Value::from_bits(self.word)) };
        if table.arena != mc.heap.m.id {
            return Err(ForeignRoot);
        }
        Ok(Value::from_bits(table.strong.word(self.word as u32)))
    }

    /// Returns a weak handle of the same value. It does not keep the value alive.
    pub fn downgrade(&self) -> WeakHandle {
        match &self.table {
            Some(table) => WeakHandle { table: Some(table.clone()), word: u64::from(table.weak.take(table.strong.word(self.word as u32))) },
            None => WeakHandle { table: None, word: self.word },
        }
    }

    /// Returns whether the value is an object. An object is kept in the root table of its arena, and any other value is kept in the handle.
    pub fn is_object(&self) -> bool {
        self.table.is_some()
    }

    /// Returns the value word that the handle keeps now. The word of an object changes when a collection moves the object.
    fn current(&self) -> u64 {
        match &self.table {
            Some(table) => table.strong.word(self.word as u32),
            None => self.word,
        }
    }
}

impl Clone for Handle {
    /// Returns a handle of the same value. For an object it takes a slot of its own, so the two handles are dropped independently.
    fn clone(&self) -> Self {
        match &self.table {
            Some(table) => Self { table: Some(table.clone()), word: u64::from(table.strong.take(table.strong.word(self.word as u32))) },
            None => Self { table: None, word: self.word },
        }
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        if let Some(table) = &self.table {
            table.strong.release(self.word as u32);
        }
    }
}

/// A handle that does not keep its value alive. Once nothing else holds the object, a collection frees it, and the weak handle then holds nothing.
///
/// [`WeakHandle::upgrade`] returns a [`Handle`] while the object is alive. A value that is not an object never dies, so its weak handle always upgrades.
///
/// # When to hold a weak handle
///
/// A [`Handle`] keeps its value alive for as long as the handle exists, whatever else happens in the arena. So a handle that is itself owned by an
/// object of the arena can keep that object alive for good. For example, a host function that is stored in a table, and whose Rust code holds a
/// handle of that table, is never collected: the table holds the function, and the function holds the table through a root.
///
/// Code that an arena object owns should hold weak handles, and make a [`Handle`] of one only for as long as it uses the value.
pub struct WeakHandle {
    /// The table of the arena, or `None` for a value that is not an object.
    table: Option<Rc<RootTable>>,
    /// The number of the weak slot, or the value word of a value that is not an object.
    word: u64,
}

impl WeakHandle {
    /// Returns a handle that keeps the value alive, or `None` if the object has been freed. It needs no step.
    pub fn upgrade(&self) -> Option<Handle> {
        let Some(table) = &self.table else { return Some(Handle { table: None, word: self.word }) };
        let word = table.weak.word(self.word as u32);
        if word == 0 {
            return None;
        }
        Some(Handle { table: Some(table.clone()), word: u64::from(table.strong.take(word)) })
    }

    /// Returns the value, or `None` if the object has been freed. Fails if the handle is of an object of another arena.
    pub fn get<'gc>(&self, mc: &Mutation<'gc>) -> Result<Option<Value<'gc>>, ForeignRoot> {
        let Some(table) = &self.table else { return Ok(Some(Value::from_bits(self.word))) };
        if table.arena != mc.heap.m.id {
            return Err(ForeignRoot);
        }
        let word = table.weak.word(self.word as u32);
        if word == 0 { Ok(None) } else { Ok(Some(Value::from_bits(word))) }
    }
}

impl Clone for WeakHandle {
    fn clone(&self) -> Self {
        match &self.table {
            Some(table) => Self { table: Some(table.clone()), word: u64::from(table.weak.take(table.weak.word(self.word as u32))) },
            None => Self { table: None, word: self.word },
        }
    }
}

impl Drop for WeakHandle {
    fn drop(&mut self) {
        if let Some(table) = &self.table {
            table.weak.release(self.word as u32);
        }
    }
}

impl fmt::Debug for WeakHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.table {
            Some(table) => formatter.debug_struct("WeakHandle").field("arena", &table.arena).field("slot", &self.word).finish(),
            None => formatter.debug_struct("WeakHandle").field("word", &self.word).finish(),
        }
    }
}

/// Two handles are equal if they keep the same value: the same object of the same arena, or the same value that is not an object. This is the comparison of `eq?`, and reads nothing in the arena.
impl PartialEq for Handle {
    fn eq(&self, other: &Self) -> bool {
        match (&self.table, &other.table) {
            (Some(first), Some(second)) => first.arena == second.arena && self.current() == other.current(),
            (None, None) => self.word == other.word,
            _ => false,
        }
    }
}

impl Eq for Handle {}

impl fmt::Debug for Handle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.table {
            Some(table) => formatter.debug_struct("Handle").field("arena", &table.arena).field("slot", &self.word).finish(),
            None => formatter.debug_struct("Handle").field("word", &self.word).finish(),
        }
    }
}

