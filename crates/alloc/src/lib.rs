//! Boxes and vectors for data that all goes at once, as a compiler's trees for one form do.
//!
//! With the `bumpalo` feature, they're in an [`Arena`], and what they take is freed when it goes;
//! without it, they're the standard ones and an arena is nothing. Code is the same either way.

#[cfg(test)]
#[path = "tests/lib.rs"]
mod tests;

use std::fmt;
#[cfg(not(feature = "bumpalo"))]
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, RangeBounds};

/// Where [`Box`]es and [`Vec`]s made in it are.
#[derive(Default)]
pub struct Arena {
    #[cfg(feature = "bumpalo")]
    bump: bumpalo::Bump,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    /// `x` in a box in the arena.
    pub fn boxed<T>(&self, x: T) -> Box<'_, T> {
        Box::new_in(x, self)
    }

    /// An empty vector in the arena.
    pub fn vec<T>(&self) -> Vec<'_, T> {
        Vec::new_in(self)
    }

    /// A vector in the arena of `n` copies of `x`.
    pub fn vec_of<T: Clone>(&self, x: T, n: usize) -> Vec<'_, T> {
        Vec::from_iter_in(std::iter::repeat_n(x, n), self)
    }

    /// How many bytes it has taken for what's in it.
    pub fn allocated(&self) -> usize {
        #[cfg(feature = "bumpalo")]
        let bytes = self.bump.allocated_bytes();
        #[cfg(not(feature = "bumpalo"))]
        let bytes = 0;
        bytes
    }
}

impl fmt::Debug for Arena {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena").field("allocated", &self.allocated()).finish()
    }
}

/// One `T`, in an arena.
pub struct Box<'a, T> {
    #[cfg(feature = "bumpalo")]
    inner: bumpalo::boxed::Box<'a, T>,
    #[cfg(not(feature = "bumpalo"))]
    inner: std::boxed::Box<T>,
    /// As an arena's box is, unchanging in `T`.
    #[cfg(not(feature = "bumpalo"))]
    arena: PhantomData<&'a mut T>,
}

impl<'a, T> Box<'a, T> {
    pub fn new_in(x: T, arena: &'a Arena) -> Self {
        #[cfg(feature = "bumpalo")]
        let b = Box { inner: bumpalo::boxed::Box::new_in(x, &arena.bump) };
        #[cfg(not(feature = "bumpalo"))]
        let b = {
            let _ = arena;
            Box { inner: std::boxed::Box::new(x), arena: PhantomData }
        };
        b
    }

    /// The `T`, out of the box.
    pub fn into_inner(b: Self) -> T {
        #[cfg(feature = "bumpalo")]
        let x = bumpalo::boxed::Box::into_inner(b.inner);
        #[cfg(not(feature = "bumpalo"))]
        let x = *b.inner;
        x
    }
}

impl<T> Deref for Box<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T> DerefMut for Box<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

impl<T> AsRef<T> for Box<'_, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> AsMut<T> for Box<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: fmt::Debug> fmt::Debug for Box<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: PartialEq> PartialEq for Box<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq> Eq for Box<'_, T> {}

/// A vector, in an arena.
pub struct Vec<'a, T> {
    #[cfg(feature = "bumpalo")]
    inner: bumpalo::collections::Vec<'a, T>,
    #[cfg(not(feature = "bumpalo"))]
    inner: std::vec::Vec<T>,
    #[cfg(not(feature = "bumpalo"))]
    arena: PhantomData<&'a Arena>,
}

impl<'a, T> Vec<'a, T> {
    pub fn new_in(arena: &'a Arena) -> Self {
        Self::with_capacity_in(0, arena)
    }

    pub fn with_capacity_in(capacity: usize, arena: &'a Arena) -> Self {
        #[cfg(feature = "bumpalo")]
        let v = Vec { inner: bumpalo::collections::Vec::with_capacity_in(capacity, &arena.bump) };
        #[cfg(not(feature = "bumpalo"))]
        let v = {
            let _ = arena;
            Vec { inner: std::vec::Vec::with_capacity(capacity), arena: PhantomData }
        };
        v
    }

    pub fn from_iter_in(iter: impl IntoIterator<Item = T>, arena: &'a Arena) -> Self {
        let iter = iter.into_iter();
        let mut v = Self::with_capacity_in(iter.size_hint().0, arena);
        v.extend(iter);
        v
    }

    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.inner
    }

    pub fn push(&mut self, x: T) {
        self.inner.push(x);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    pub fn insert(&mut self, at: usize, x: T) {
        self.inner.insert(at, x);
    }

    pub fn remove(&mut self, at: usize) -> T {
        self.inner.remove(at)
    }

    pub fn swap_remove(&mut self, at: usize) -> T {
        self.inner.swap_remove(at)
    }

    pub fn truncate(&mut self, len: usize) {
        self.inner.truncate(len);
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn reserve(&mut self, more: usize) {
        self.inner.reserve(more);
    }

    pub fn retain(&mut self, keep: impl FnMut(&T) -> bool) {
        self.inner.retain(keep);
    }

    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + '_ {
        self.inner.drain(range)
    }

    /// The elements from `at` on, which it no longer has.
    pub fn split_off(&mut self, at: usize) -> Self {
        Vec {
            inner: self.inner.split_off(at),
            #[cfg(not(feature = "bumpalo"))]
            arena: PhantomData,
        }
    }
}

impl<T: Clone> Vec<'_, T> {
    pub fn extend_from_slice(&mut self, xs: &[T]) {
        self.inner.extend_from_slice(xs);
    }

    /// Grows or shrinks to `len`, with copies of `x` at the end if it grows.
    pub fn resize(&mut self, len: usize, x: T) {
        self.inner.resize(len, x);
    }
}

impl<T> Deref for Vec<'_, T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.inner
    }
}

impl<T> DerefMut for Vec<'_, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.inner
    }
}

impl<T> AsRef<[T]> for Vec<'_, T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for Vec<'_, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T> Extend<T> for Vec<'_, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

impl<T: Clone> Clone for Vec<'_, T> {
    fn clone(&self) -> Self {
        Vec {
            inner: self.inner.clone(),
            #[cfg(not(feature = "bumpalo"))]
            arena: PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: PartialEq> PartialEq for Vec<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Eq> Eq for Vec<'_, T> {}

/// A [`Vec`]'s elements, taken out of it.
pub struct IntoIter<'a, T> {
    #[cfg(feature = "bumpalo")]
    inner: bumpalo::collections::vec::IntoIter<'a, T>,
    #[cfg(not(feature = "bumpalo"))]
    inner: std::vec::IntoIter<T>,
    #[cfg(not(feature = "bumpalo"))]
    arena: PhantomData<&'a Arena>,
}

impl<T> Iterator for IntoIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> DoubleEndedIterator for IntoIter<'_, T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<'_, T> {}

impl<'a, T> IntoIterator for Vec<'a, T> {
    type Item = T;
    type IntoIter = IntoIter<'a, T>;

    fn into_iter(self) -> IntoIter<'a, T> {
        IntoIter {
            inner: self.inner.into_iter(),
            #[cfg(not(feature = "bumpalo"))]
            arena: PhantomData,
        }
    }
}

impl<'v, T> IntoIterator for &'v Vec<'_, T> {
    type Item = &'v T;
    type IntoIter = std::slice::Iter<'v, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'v, T> IntoIterator for &'v mut Vec<'_, T> {
    type Item = &'v mut T;
    type IntoIter = std::slice::IterMut<'v, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Collecting an iterator into a [`Vec`] in an arena.
pub trait CollectIn: Iterator + Sized {
    fn collect_in(self, arena: &Arena) -> Vec<'_, Self::Item> {
        Vec::from_iter_in(self, arena)
    }

    /// The `Ok`s, in a [`Vec`], unless there's an `Err`, which it stops at.
    fn try_collect_in<T, E>(self, arena: &Arena) -> Result<Vec<'_, T>, E>
    where
        Self: Iterator<Item = Result<T, E>>,
    {
        let mut v = Vec::with_capacity_in(self.size_hint().0, arena);
        for x in self {
            v.push(x?);
        }
        Ok(v)
    }
}

impl<I: Iterator> CollectIn for I {}

/// A [`Vec`] in `arena` of the elements given: `vec_in![arena; a, b, c]`.
#[macro_export]
macro_rules! vec_in {
    ($arena:expr; $($x:expr),* $(,)?) => {
        $crate::Vec::from_iter_in([$($x),*], $arena)
    };
}
