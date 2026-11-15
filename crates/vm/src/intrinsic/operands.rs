//! The operands of an intrinsic call, however the caller holds them.

use std::marker::PhantomData;

use ragwort_types::gc::{Frame, Value};

/// The operands of one intrinsic call. An intrinsic reads them by position, however the caller
/// holds them: in a run of frame registers, in a few values, or in a slice.
pub(crate) trait Operands<'gc>: Copy {
    /// Returns the number of operands.
    fn count(self) -> usize;

    /// Returns operand `position`, which must be below [`Operands::count`].
    fn get(self, position: usize) -> Value<'gc>;

    /// Returns the operands from position `start` on, in order.
    fn from(self, start: usize) -> Rest<'gc, Self> {
        Rest { operands: self, next: start, values: PhantomData }
    }
}

/// Operands held in `count` consecutive registers of `frame`, starting at register `base`.
#[derive(Clone, Copy)]
pub(crate) struct Registers<'f, 'gc> {
    pub(crate) frame: Frame<'f, 'gc>,
    pub(crate) base: u8,
    pub(crate) count: u8,
}

impl<'gc> Operands<'gc> for Registers<'_, 'gc> {
    #[inline(always)]
    fn count(self) -> usize {
        usize::from(self.count)
    }

    #[inline(always)]
    fn get(self, position: usize) -> Value<'gc> {
        self.frame.get(self.base + position as u8)
    }
}

impl<'gc, const N: usize> Operands<'gc> for [Value<'gc>; N] {
    #[inline(always)]
    fn count(self) -> usize {
        N
    }

    #[inline(always)]
    fn get(self, position: usize) -> Value<'gc> {
        self[position]
    }
}

impl<'gc> Operands<'gc> for &[Value<'gc>] {
    #[inline(always)]
    fn count(self) -> usize {
        self.len()
    }

    #[inline(always)]
    fn get(self, position: usize) -> Value<'gc> {
        self[position]
    }
}

/// The operands of a call from one position to the end, as [`Operands::from`] returns them.
pub(crate) struct Rest<'gc, O> {
    operands: O,
    next: usize,
    values: PhantomData<Value<'gc>>,
}

impl<'gc, O: Operands<'gc>> Iterator for Rest<'gc, O> {
    type Item = Value<'gc>;

    #[inline(always)]
    fn next(&mut self) -> Option<Value<'gc>> {
        if self.next >= self.operands.count() {
            return None;
        }
        let value = self.operands.get(self.next);
        self.next += 1;
        Some(value)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = self.operands.count().saturating_sub(self.next);
        (left, Some(left))
    }
}

impl<'gc, O: Operands<'gc>> ExactSizeIterator for Rest<'gc, O> {}
