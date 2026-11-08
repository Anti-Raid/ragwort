use std::collections::HashMap;
use std::hash::{BuildHasher, BuildHasherDefault, Hasher, RandomState};

use ragwort_types::bytevector::AnyBytevector;
use ragwort_types::gc::{Charge, Gc, Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::Pair;
use ragwort_types::string::{self, Strings};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::objects::{self, BoxFields};

/// How many values `equal?` compares for each unit of fuel it spends.
pub(crate) const PER_FUEL: u64 = 1024;

/// How many compound values `equal?` compares before it keeps classes, so comparing small
/// values never hashes. It's Chez's `k0`, and the mean length of the stretches between.
const PRECHECK: u64 = 200;
/// How many compound values each stretch that keeps classes takes: Chez's `-kb`.
const SLOW: u64 = 20;

/// What each compound value in [`Classes`] is charged against the arena's budget.
const CLASS_COST: usize = size_of::<(u64, usize, usize, u32)>() + 16;

/// `eqv?`: the same object, or numbers of the same exactness and value.
#[inline]
pub(crate) fn eqv<'gc>(mc: &Mutation<'gc>, a: Value<'gc>, b: Value<'gc>) -> bool {
    if a == b {
        return true;
    }
    // Different fixnums are different numbers.
    if a.as_fixnum().is_some() && b.as_fixnum().is_some() {
        return false;
    }
    let nums = Nums::new(mc);
    match (nums.number(a), nums.number(b)) {
        (Some(x), Some(y)) => complex::eqv(&nums, x, y),
        _ => false,
    }
}

/// `equal?`: [`eqv?`](eqv), or strings of the same characters, or bytevectors of the same
/// bytes, or pairs, vectors or boxes whose contents are `equal?`. A vector's mutability doesn't
/// matter, as in Racket. Also returns how many values it compared, a string or bytevector
/// counting as one plus one per eight characters or bytes, or faults with [`Fault::OutOfFuel`]
/// once that's past `most`.
pub(crate) fn equal<'gc>(mc: &Mutation<'gc>, a: Value<'gc>, b: Value<'gc>, most: u64) -> Result<(bool, u64), Fault> {
    let (strings, vectors) = (Strings::new(mc), Vectors::new(mc));
    let (mut next, mut todo, mut phases) = (Some((a, b)), ScratchVec::new(mc), Phases::new(mc));
    let mut compared = 0;
    loop {
        let (a, b) = match next.take().map(|(a, b)| Work::Values(a, b)).or_else(|| todo.pop()) {
            None => return Ok((true, compared)),
            Some(Work::Values(a, b)) => (a, b),
            Some(Work::Items(x, y, i)) => {
                if i + 1 < x.len(mc) {
                    todo.push(Work::Items(x, y, i + 1))?;
                }
                (x.get(mc, i).ok_or(Fault::Malformed)?, y.get(mc, i).ok_or(Fault::Malformed)?)
            }
        };
        compared += 1;
        if compared > most {
            return Err(Fault::OutOfFuel);
        }
        if eqv(mc, a, b) {
            continue;
        }
        if let (Some(s), Some(t)) = (strings.string(a), strings.string(b)) {
            let (na, nb) = (string::len(&strings, s), string::len(&strings, t));
            if na != nb {
                return Ok((false, compared));
            }
            compared = compared.saturating_add(na as u64 / 8);
            if compared > most {
                return Err(Fault::OutOfFuel);
            }
            if !string::equal(&strings, s, t)? {
                return Ok((false, compared));
            }
            continue;
        }
        if let (Some(x), Some(y)) = (AnyBytevector::of(a), AnyBytevector::of(b)) {
            let (na, nb) = (x.len(mc), y.len(mc));
            if na != nb {
                return Ok((false, compared));
            }
            compared = compared.saturating_add(na as u64 / 8);
            if compared > most {
                return Err(Fault::OutOfFuel);
            }
            if !x.same_bytes(mc, y) {
                return Ok((false, compared));
            }
            continue;
        }
        let (Some(x), Some(y)) = (Compound::of(mc, &vectors, a), Compound::of(mc, &vectors, b)) else { return Ok((false, compared)) };
        let same_shape = match (x, y) {
            (Compound::Vector(x), Compound::Vector(y)) => x.len(mc) == y.len(mc),
            (Compound::Pair(_), Compound::Pair(_)) | (Compound::Box(_), Compound::Box(_)) => true,
            _ => false,
        };
        if !same_shape {
            return Ok((false, compared));
        }
        if phases.seen(a, b)? {
            continue;
        }
        match (x, y) {
            (Compound::Pair(x), Compound::Pair(y)) => {
                todo.push(Work::Values(x.tail(mc), y.tail(mc)))?;
                next = Some((x.head(mc), y.head(mc)));
            }
            (Compound::Vector(x), Compound::Vector(y)) if !x.is_empty(mc) => todo.push(Work::Items(x, y, 0))?,
            (Compound::Box(x), Compound::Box(y)) => next = Some((x.value(mc), y.value(mc))),
            _ => {}
        }
    }
}

/// What's still to compare: two values, or the items of two vectors from an index on.
enum Work<'gc> {
    Values(Value<'gc>, Value<'gc>),
    Items(AnyVector<'gc>, AnyVector<'gc>, usize),
}

/// A value `equal?` compares by its contents.
#[derive(Clone, Copy)]
enum Compound<'gc> {
    Pair(Pair<'gc>),
    Vector(AnyVector<'gc>),
    Box(Gc<'gc, objects::Box>),
}

impl<'gc> Compound<'gc> {
    fn of(mc: &Mutation<'gc>, vectors: &Vectors<'_, 'gc>, v: Value<'gc>) -> Option<Self> {
        if let Some(pair) = Pair::of(v) {
            return Some(Compound::Pair(pair));
        }
        if let Some(vector) = vectors.vector(v) {
            return Some(Compound::Vector(vector));
        }
        v.downcast::<objects::Box>(mc).map(Compound::Box)
    }
}

/// Which stretch a comparison is in: Chez's `k`, counted down by each two compound values
/// compared. Above zero, they're compared as they are; from zero down to `-SLOW`, they're put
/// in one class first, and two already in one aren't compared again.
struct Phases<'gc> {
    k: i64,
    classes: Classes<'gc>,
    random: u64,
}

impl<'gc> Phases<'gc> {
    fn new(mc: &Mutation<'gc>) -> Self {
        Phases {
            k: PRECHECK as i64,
            classes: Classes { index: HashMap::default(), parent: Vec::new(), size: Vec::new(), charge: mc.charge() },
            random: 0,
        }
    }

    /// Whether `a` and `b`, compound values about to be compared by their contents, are
    /// already known to be equal if the rest of the comparison finds so.
    fn seen(&mut self, a: Value<'_>, b: Value<'_>) -> Result<bool, OutOfMemory> {
        if self.k == -(SLOW as i64) {
            self.k = (self.next_random() % (2 * PRECHECK)) as i64;
        }
        self.k -= 1;
        if self.k >= 0 {
            return Ok(false);
        }
        if self.classes.union(a, b)? {
            self.k = 0;
            return Ok(true);
        }
        Ok(false)
    }

    /// A xorshift generator, seeded from the process's random hash keys the first time, so the
    /// stretches can't be lined up with a value made to defeat them.
    fn next_random(&mut self) -> u64 {
        if self.random == 0 {
            self.random = RandomState::new().hash_one(self.classes.parent.len()) | 1;
        }
        let mut x = self.random;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.random = x;
        x
    }
}

/// Classes of compound values met, by identity: a union-find, by size, with path halving.
struct Classes<'gc> {
    index: HashMap<u64, usize, BuildHasherDefault<WordHasher>>,
    parent: Vec<usize>,
    size: Vec<u32>,
    charge: Charge<'gc>,
}

impl Classes<'_> {
    /// Puts `a` and `b` in one class. Returns whether they already were.
    fn union(&mut self, a: Value<'_>, b: Value<'_>) -> Result<bool, OutOfMemory> {
        let (x, y) = (self.find(a)?, self.find(b)?);
        if x == y {
            return Ok(true);
        }
        let (small, large) = if self.size[x] < self.size[y] { (x, y) } else { (y, x) };
        self.parent[small] = large;
        self.size[large] += self.size[small];
        Ok(false)
    }

    fn find(&mut self, v: Value<'_>) -> Result<usize, OutOfMemory> {
        let mut i = match self.index.get(&v.to_bits()) {
            Some(&i) => i,
            None => {
                self.charge.grow(CLASS_COST)?;
                let fresh = self.parent.len();
                self.index.insert(v.to_bits(), fresh);
                self.parent.push(fresh);
                self.size.push(1);
                fresh
            }
        };
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        Ok(i)
    }
}

/// Hashes the word of an object reference, whose index is in the high half and whose low bits
/// are the same for every object of a type, by a folded multiply, which spreads both halves
/// over all the bits.
#[derive(Default)]
struct WordHasher(u64);

impl Hasher for WordHasher {
    fn write(&mut self, bytes: &[u8]) {
        bytes.iter().for_each(|&b| self.write_u64(u64::from(b)));
    }

    fn write_u64(&mut self, n: u64) {
        let m = u128::from(self.0 ^ n) * 0x9E37_79B9_7F4A_7C15;
        self.0 = (m >> 64) as u64 ^ m as u64;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

