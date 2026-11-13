//! Bigint algorithms on digit views, after V8's `src/bigint`. A number is a magnitude: a
//! little-endian run of digits. Functions write their result into an [`RWDigits`] the caller
//! sizes, fill the rest of it with zeros, and never allocate: scratch space is passed in.

mod bitwise;
mod div;
mod mul;
mod string;
mod vector;

#[cfg(test)]
#[path = "../tests/bigint.rs"]
mod tests;

pub use bitwise::*;
pub use div::*;
pub use mul::*;
pub use string::*;
pub use vector::*;

use std::cell::Cell;

pub type Digit = u64;
/// Holds the product of two digits plus two more.
pub type TwoDigits = u128;
pub const DIGIT_BITS: usize = Digit::BITS as usize;

/// `a + b + carry`, and the new carry.
#[inline]
pub fn digit_add(a: Digit, b: Digit, carry: Digit) -> (Digit, Digit) {
    let sum = a as TwoDigits + b as TwoDigits + carry as TwoDigits;
    (sum as Digit, (sum >> DIGIT_BITS) as Digit)
}

/// `a - b - borrow`, and the new borrow.
#[inline]
pub fn digit_sub(a: Digit, b: Digit, borrow: Digit) -> (Digit, Digit) {
    let diff = (a as TwoDigits).wrapping_sub(b as TwoDigits).wrapping_sub(borrow as TwoDigits);
    (diff as Digit, (diff >> (2 * DIGIT_BITS - 1)) as Digit)
}

/// `a * b + add + carry`, low digit and high digit.
#[inline]
pub fn digit_mul_add(a: Digit, b: Digit, add: Digit, carry: Digit) -> (Digit, Digit) {
    let total = a as TwoDigits * b as TwoDigits + add as TwoDigits + carry as TwoDigits;
    (total as Digit, (total >> DIGIT_BITS) as Digit)
}

/// A read-only view of digits, in cells so a host can lend the words it keeps them in.
#[derive(Clone, Copy, Debug)]
pub struct Digits<'a> {
    digits: &'a [Cell<Digit>],
}

impl<'a> Digits<'a> {
    #[inline]
    pub fn new(digits: &'a [Cell<Digit>]) -> Self {
        Self { digits }
    }

    /// A view of digits this borrows mutably, so nothing else changes them meanwhile.
    #[inline]
    pub fn of_mut(digits: &'a mut [Digit]) -> Self {
        Self { digits: Cell::from_mut(digits).as_slice_of_cells() }
    }

    #[inline]
    pub fn len(self) -> usize {
        self.digits.len()
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.digits.is_empty()
    }

    /// Without high zero digits.
    #[inline]
    pub fn normalize(self) -> Self {
        let len = self.digits.iter().rposition(|digit| digit.get() != 0).map_or(0, |i| i + 1);
        Self { digits: &self.digits[..len] }
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        self.digits.iter().all(|digit| digit.get() == 0)
    }

    /// The most significant digit, or 0 if there are none.
    #[inline]
    pub fn msd(self) -> Digit {
        self.digits.last().map_or(0, Cell::get)
    }

    /// Digit `i`, or 0 past the end.
    #[inline]
    pub fn get(self, i: usize) -> Digit {
        self.digits.get(i).map_or(0, Cell::get)
    }

    /// Digit `i`, which must be there.
    #[inline]
    pub fn at(self, i: usize) -> Digit {
        self.digits[i].get()
    }

    /// Up to `len` digits from `offset`, as many as there are.
    #[inline]
    pub fn slice(self, offset: usize, len: usize) -> Self {
        let start = offset.min(self.len());
        Self { digits: &self.digits[start..(start + len).min(self.len())] }
    }

    #[inline]
    pub fn iter(self) -> impl DoubleEndedIterator<Item = Digit> + 'a {
        self.digits.iter().map(Cell::get)
    }

    #[inline]
    pub fn bit_len(self) -> usize {
        let x = self.normalize();
        (x.len() * DIGIT_BITS).saturating_sub(x.msd().leading_zeros() as usize)
    }
}

/// A writable view of digits, in cells so a host can lend the words it keeps them in. Like a
/// `&mut`, it's the only view of its digits while it lives.
#[derive(Debug)]
pub struct RWDigits<'a> {
    digits: &'a [Cell<Digit>],
}

impl<'a> RWDigits<'a> {
    #[inline]
    pub fn new(digits: &'a mut [Digit]) -> Self {
        Self { digits: Cell::from_mut(digits).as_slice_of_cells() }
    }

    /// Digits a host keeps in cells, which nothing else may read or write while this lives.
    #[inline]
    pub fn of_cells(digits: &'a [Cell<Digit>]) -> Self {
        Self { digits }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.digits.is_empty()
    }

    /// Digit `i`, which must be there.
    #[inline]
    pub fn at(&self, i: usize) -> Digit {
        self.digits[i].get()
    }

    #[inline]
    pub fn set(&mut self, i: usize, digit: Digit) {
        self.digits[i].set(digit);
    }

    /// Sets digit `i` to the first of `pair`, and returns the second: what a digit operation
    /// carries or borrows.
    #[inline]
    pub fn put(&mut self, i: usize, (digit, carry): (Digit, Digit)) -> Digit {
        self.digits[i].set(digit);
        carry
    }

    #[inline]
    pub fn read(&self) -> Digits<'_> {
        Digits::new(self.digits)
    }

    #[inline]
    pub fn reborrow(&mut self) -> RWDigits<'_> {
        RWDigits { digits: self.digits }
    }

    /// Up to `len` digits from `offset`, as many as there are.
    #[inline]
    pub fn slice(&mut self, offset: usize, len: usize) -> RWDigits<'_> {
        let start = offset.min(self.len());
        let end = (start + len).min(self.len());
        RWDigits { digits: &self.digits[start..end] }
    }

    #[inline]
    pub fn offset(&mut self, offset: usize) -> RWDigits<'_> {
        let start = offset.min(self.len());
        RWDigits { digits: &self.digits[start..] }
    }

    /// The first `len` digits, keeping the borrow.
    #[inline]
    pub fn truncate(self, len: usize) -> RWDigits<'a> {
        let len = len.min(self.digits.len());
        RWDigits { digits: &self.digits[..len] }
    }

    /// Splits into the first `mid` digits and the rest.
    #[inline]
    pub fn split(self, mid: usize) -> (RWDigits<'a>, RWDigits<'a>) {
        let (first, rest) = self.digits.split_at(mid.min(self.digits.len()));
        (RWDigits { digits: first }, RWDigits { digits: rest })
    }

    #[inline]
    pub fn clear(&mut self) {
        self.digits.iter().for_each(|digit| digit.set(0));
    }

    #[inline]
    pub fn copy_from(&mut self, x: Digits<'_>) {
        let n = x.len().min(self.len());
        self.digits[..n].iter().zip(x.iter()).for_each(|(digit, x)| digit.set(x));
        self.digits[n..].iter().for_each(|digit| digit.set(0));
    }
}
