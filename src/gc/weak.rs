use std::fmt;

use super::trace::KeyState;
use super::{Gc, Lock, Member, Mutation, Plain, Trace, Tracer};

/// Holds `value` for as long as `key` is reachable from somewhere other than this
/// ephemeron. Once the key dies, both are cleared together, so a value that refers back to
/// its own key doesn't keep it alive.
///
/// An ephemeron must live in arena memory to be weak. Held anywhere else, such as in the arena
/// root, it keeps its key alive.
#[derive(Plain)]
#[repr(C)]
pub struct Ephemeron<'gc, K, V> {
    key: Lock<Option<Member<'gc, K>>>,
    _pad: u32,
    value: Lock<V>,
}

impl<'gc, K: 'gc, V: Trace + Copy + Default + 'gc> Ephemeron<'gc, K, V> {
    pub fn new(mc: &Mutation<'gc>, key: Gc<'gc, K>, value: V) -> Self {
        Self { key: Lock::new(Some(Member::new(mc, key))), value: Lock::new(value), ..Self::empty() }
    }

    /// An ephemeron with no key, as if its key had died.
    pub fn empty() -> Self {
        Self { key: Lock::new(None), _pad: 0, value: Lock::new(V::default()) }
    }

    pub fn key(&self, mc: &Mutation<'gc>) -> Option<Gc<'gc, K>>
    where
        K: Plain<'gc>,
    {
        self.key.load(mc)
    }

    /// The value, or `None` once the key has died.
    pub fn value(&self) -> Option<V> {
        self.key.get().map(|_| self.value.get())
    }

    pub fn set(&self, mc: &Mutation<'gc>, key: Gc<'gc, K>, value: V) {
        self.key.store(mc, Some(key));
        self.value.set(mc, value);
    }

    /// Replaces the value. Returns false, and stores nothing, once the key has died.
    pub fn set_value(&self, mc: &Mutation<'gc>, value: V) -> bool {
        if self.key.get().is_none() {
            return false;
        }
        self.value.set(mc, value);
        true
    }

    pub fn clear(&self, mc: &Mutation<'gc>) {
        self.key.set(mc, None);
        self.value.set(mc, V::default());
    }
}

unsafe impl<K, V: Trace + Copy + Default> Trace for Ephemeron<'_, K, V> {
    fn trace(&mut self, t: &mut Tracer<'_>) {
        // Without a key the value is unreachable, so it isn't traced.
        let key = self.key.get_mut();
        let Some(member) = key else { return };
        match t.ephemeron_key(member.offset_mut()) {
            KeyState::Live => self.value.trace(t),
            KeyState::Pending => {}
            KeyState::Dead => {
                *key = None;
                *self.value.get_mut() = V::default();
            }
        }
    }
}

impl<K, V: Copy + fmt::Debug> fmt::Debug for Ephemeron<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ephemeron").field("key", &self.key.get()).field("value", &self.value.get()).finish()
    }
}

/// A reference that doesn't keep its target alive. It reads as `None` once the target dies.
#[derive(Trace, Plain)]
#[repr(transparent)]
pub struct Weak<'gc, T>(Ephemeron<'gc, T, ()>);

impl<'gc, T: 'gc> Weak<'gc, T> {
    pub fn new(mc: &Mutation<'gc>, target: Gc<'gc, T>) -> Self {
        Self(Ephemeron::new(mc, target, ()))
    }

    pub fn empty() -> Self {
        Self(Ephemeron::empty())
    }

    pub fn get(&self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>>
    where
        T: Plain<'gc>,
    {
        self.0.key(mc)
    }

    pub fn set(&self, mc: &Mutation<'gc>, target: Gc<'gc, T>) {
        self.0.set(mc, target, ());
    }

    pub fn clear(&self, mc: &Mutation<'gc>) {
        self.0.clear(mc);
    }
}

impl<T> fmt::Debug for Weak<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Weak").field(&self.0.key.get()).finish()
    }
}
