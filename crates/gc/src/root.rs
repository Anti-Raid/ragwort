use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use super::{Mutation, OutOfMemory, Trace, Tracer};

pub(crate) const ROOT_COST: usize = 64;

/// Maps a `'static` marker type to the branded type a [`Root`] holds.
pub trait Rooted: 'static {
    type Of<'gc>: Trace + Copy;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForeignRoot;

impl fmt::Display for ForeignRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("root belongs to a different arena")
    }
}

impl std::error::Error for ForeignRoot {}

pub(crate) trait RootEntry {
    fn trace(&self, t: &mut Tracer<'_>);
}

struct Entry<K: Rooted> {
    // The collector rewrites it when the object moves.
    value: Cell<K::Of<'static>>,
    _marker: PhantomData<K>,
}

impl<K: Rooted> RootEntry for Entry<K> {
    fn trace(&self, t: &mut Tracer<'_>) {
        let mut value = self.value.get();
        value.trace(t);
        self.value.set(value);
    }
}

/// Keeps a value alive across steps. Fetch it again inside a step with [`Mutation::fetch`].
pub struct Root<K: Rooted> {
    arena: u64,
    entry: Rc<Entry<K>>,
}

impl<K: Rooted> Clone for Root<K> {
    fn clone(&self) -> Self {
        Self { arena: self.arena, entry: self.entry.clone() }
    }
}

impl<'gc> Mutation<'gc> {
    pub fn root<K: Rooted>(&self, value: K::Of<'gc>) -> Result<Root<K>, OutOfMemory>
    where
        K::Of<'static>: 'static,
    {
        let budget = &self.heap.budget;
        budget.count_allocation()?;
        let mut roots = self.heap.roots.borrow_mut();
        budget.ensure(ROOT_COST + roots.growth_cost(1))?;
        // SAFETY: [brand] only the brand changes, which changes neither layout nor validity, and
        // the value is `Copy`, so reading it is a plain copy. The entry is traced as a root, and
        // `fetch` only hands it back to a `Mutation` of this arena.
        let value = unsafe { (&raw const value).cast::<K::Of<'static>>().read() };
        let entry = Rc::new(Entry::<K> { value: Cell::new(value), _marker: PhantomData });
        roots.push(budget, entry.clone())?;
        budget.charge(ROOT_COST)?;
        self.heap.demand(ROOT_COST);
        Ok(Root { arena: self.heap.id, entry })
    }

    pub fn fetch<K: Rooted>(&self, root: &Root<K>) -> Result<K::Of<'gc>, ForeignRoot> {
        if root.arena != self.heap.id {
            return Err(ForeignRoot);
        }
        let value = root.entry.value.get();
        // SAFETY: [brand, refs] the root belongs to this arena, checked above, and was traced
        // through every collection since it was made, so its handles are valid under this brand.
        Ok(unsafe { (&raw const value).cast::<K::Of<'gc>>().read() })
    }
}
