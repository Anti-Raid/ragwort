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

    /// `value` in a box in the arena.
    pub fn boxed<T>(&self, value: T) -> Box<'_, T> {
        Box::new_in(value, self)
    }

    /// An empty vector in the arena.
    pub fn vec<T>(&self) -> Vec<'_, T> {
        Vec::new_in(self)
    }

    /// A vector in the arena of `count` copies of `value`.
    pub fn vec_of<T: Clone>(&self, value: T, count: usize) -> Vec<'_, T> {
        Vec::from_iter_in(std::iter::repeat_n(value, count), self)
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_struct("Arena").field("allocated", &self.allocated()).finish()
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
    pub fn new_in(value: T, arena: &'a Arena) -> Self {
        #[cfg(feature = "bumpalo")]
        let boxed = Box { inner: bumpalo::boxed::Box::new_in(value, &arena.bump) };
        #[cfg(not(feature = "bumpalo"))]
        let boxed = {
            let _ = arena;
            Box { inner: std::boxed::Box::new(value), arena: PhantomData }
        };
        boxed
    }

    /// The `T`, out of the box.
    pub fn into_inner(boxed: Self) -> T {
        #[cfg(feature = "bumpalo")]
        let value = bumpalo::boxed::Box::into_inner(boxed.inner);
        #[cfg(not(feature = "bumpalo"))]
        let value = *boxed.inner;
        value
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(formatter)
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
        let vector = Vec { inner: bumpalo::collections::Vec::with_capacity_in(capacity, &arena.bump) };
        #[cfg(not(feature = "bumpalo"))]
        let vector = {
            let _ = arena;
            Vec { inner: std::vec::Vec::with_capacity(capacity), arena: PhantomData }
        };
        vector
    }

    pub fn from_iter_in(iter: impl IntoIterator<Item = T>, arena: &'a Arena) -> Self {
        let iter = iter.into_iter();
        let mut vector = Self::with_capacity_in(iter.size_hint().0, arena);
        vector.extend(iter);
        vector
    }

    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.inner
    }

    pub fn push(&mut self, value: T) {
        self.inner.push(value);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    pub fn insert(&mut self, at: usize, value: T) {
        self.inner.insert(at, value);
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

    /// Grows or shrinks to `len`, with copies of `value` at the end if it grows.
    pub fn resize(&mut self, len: usize, value: T) {
        self.inner.resize(len, value);
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(formatter)
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
        let mut vector = Vec::with_capacity_in(self.size_hint().0, arena);
        for item in self {
            vector.push(item?);
        }
        Ok(vector)
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
