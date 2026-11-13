use std::collections::HashMap;
use std::hash::{BuildHasher, BuildHasherDefault, Hasher, RandomState};

use ragwort_types::bytevector::AnyBytevector;
use ragwort_types::gc::{Charge, Gc, Mutation, OutOfMemory, ScratchVec, Value};
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::Pair;
use ragwort_types::string::{self, Strings};
use ragwort_types::vector::{AnyVector, Vectors};

use crate::Fault;
use crate::objects::{self, BoxFields, StructFields};
use crate::structs::{self, TypeFlags};

/// The number of value comparisons performed by `equal?` per unit of VM fuel consumed.
pub(crate) const PER_FUEL: u64 = 1024;

/// Threshold of compound value comparisons performed before activating union-find cycle detection
/// (avoiding hash table overhead when comparing small values). Corresponds to Chez Scheme's `k0`
/// and defines the mean length of fast comparison intervals.
const PRECHECK: u64 = 200;
/// Duration (in compound value comparisons) of each cycle-tracking interval, corresponding to Chez Scheme's `-kb`.
const SLOW: u64 = 20;

/// Memory allocation cost (in bytes) debited from the GC arena budget for each tracked compound value in [`Classes`].
const CLASS_COST: usize = size_of::<(u64, usize, usize, u32)>() + 16;

/// Implements Scheme `eqv?`: returns `true` if `left` and `right` are identical values/objects, or numbers with equal value and identical exactness.
#[inline]
pub(crate) fn eqv<'gc>(mc: &Mutation<'gc>, left: Value<'gc>, right: Value<'gc>) -> bool {
    if left == right {
        return true;
    }
    // Two distinct fixnum bit patterns represent distinct integers and cannot be `eqv?`.
    if left.as_fixnum().is_some() && right.as_fixnum().is_some() {
        return false;
    }
    let nums = Nums::new(mc);
    match (nums.number(left), nums.number(right)) {
        (Some(first), Some(second)) => complex::eqv(&nums, first, second),
        _ => false,
    }
}

/// Implements Scheme `equal?` structural comparison with cycle detection and bounded fuel consumption.
///
/// Returns `Ok((true, compared_count))` if `left` and `right` are:
/// - Equivalent under [`eqv?`](eqv);
/// - Strings with identical character sequences;
/// - Bytevectors with identical byte sequences;
/// - Pairs, vectors, or boxes whose contents are recursively `equal?` (ignoring vector mutability, per Racket semantics);
/// - Struct instances of the same struct type whose fields are pairwise `equal?`, provided the type is not an identity type.
///
/// Tracks fuel consumption (counting strings/bytevectors as 1 plus 1 per 8 characters or bytes)
/// and raises [`Fault::OutOfFuel`] if comparison steps exceed `most`.
pub(crate) fn equal<'gc>(mc: &Mutation<'gc>, left: Value<'gc>, right: Value<'gc>, most: u64) -> Result<(bool, u64), Fault> {
    let (strings, vectors) = (Strings::new(mc), Vectors::new(mc));
    let (mut next, mut todo, mut phases) = (Some((left, right)), ScratchVec::new(mc), Phases::new(mc));
    let mut compared = 0;
    loop {
        let (left, right) = match next.take().map(|(left, right)| Work::Values(left, right)).or_else(|| todo.pop()) {
            None => return Ok((true, compared)),
            Some(Work::Values(left, right)) => (left, right),
            Some(Work::Items(first, second, index)) => {
                if index + 1 < first.len(mc) {
                    todo.push(Work::Items(first, second, index + 1))?;
                }
                (first.get(mc, index).ok_or(Fault::Malformed)?, second.get(mc, index).ok_or(Fault::Malformed)?)
            }
            Some(Work::Fields(first, second, index)) => {
                let (xs, ys) = (first.items(mc), second.items(mc));
                if index + 1 < xs.len() {
                    todo.push(Work::Fields(first, second, index + 1))?;
                }
                (xs.get(index), ys.get(index))
            }
        };
        compared += 1;
        if compared > most {
            return Err(Fault::OutOfFuel);
        }
        if eqv(mc, left, right) {
            continue;
        }
        if let (Some(first), Some(second)) = (strings.string(left), strings.string(right)) {
            let (na, nb) = (string::len(&strings, first), string::len(&strings, second));
            if na != nb {
                return Ok((false, compared));
            }
            compared = compared.saturating_add(na as u64 / 8);
            if compared > most {
                return Err(Fault::OutOfFuel);
            }
            if !string::equal(&strings, first, second)? {
                return Ok((false, compared));
            }
            continue;
        }
        if let (Some(first), Some(second)) = (AnyBytevector::of(left), AnyBytevector::of(right)) {
            let (na, nb) = (first.len(mc), second.len(mc));
            if na != nb {
                return Ok((false, compared));
            }
            compared = compared.saturating_add(na as u64 / 8);
            if compared > most {
                return Err(Fault::OutOfFuel);
            }
            if !first.same_bytes(mc, second) {
                return Ok((false, compared));
            }
            continue;
        }
        let (Some(first), Some(second)) = (Compound::of(mc, &vectors, left), Compound::of(mc, &vectors, right)) else { return Ok((false, compared)) };
        let same_shape = match (first, second) {
            (Compound::Vector(first), Compound::Vector(second)) => first.len(mc) == second.len(mc),
            (Compound::Pair(_), Compound::Pair(_)) | (Compound::Box(_), Compound::Box(_)) => true,
            (Compound::Struct(first), Compound::Struct(second)) => first.kind(mc) == second.kind(mc),
            _ => false,
        };
        if !same_shape {
            return Ok((false, compared));
        }
        if phases.seen(left, right)? {
            continue;
        }
        match (first, second) {
            (Compound::Pair(first), Compound::Pair(second)) => {
                todo.push(Work::Values(first.tail(mc), second.tail(mc)))?;
                next = Some((first.head(mc), second.head(mc)));
            }
            (Compound::Vector(first), Compound::Vector(second)) if !first.is_empty(mc) => todo.push(Work::Items(first, second, 0))?,
            (Compound::Box(first), Compound::Box(second)) => next = Some((first.value(mc), second.value(mc))),
            (Compound::Struct(first), Compound::Struct(second)) if !first.items(mc).is_empty() => todo.push(Work::Fields(first, second, 0))?,
            _ => {}
        }
    }
}

/// Pending comparison tasks on the traversal stack: either a pair of arbitrary values,
/// or corresponding elements of two vectors or struct instances starting from a given index offset.
enum Work<'gc> {
    Values(Value<'gc>, Value<'gc>),
    Items(AnyVector<'gc>, AnyVector<'gc>, usize),
    Fields(Gc<'gc, objects::Struct>, Gc<'gc, objects::Struct>, usize),
}

/// A compound data type compared recursively by content in `equal?` (pair, vector, box, or non-identity struct).
#[derive(Clone, Copy)]
enum Compound<'gc> {
    Pair(Pair<'gc>),
    Vector(AnyVector<'gc>),
    Box(Gc<'gc, objects::Box>),
    Struct(Gc<'gc, objects::Struct>),
}

impl<'gc> Compound<'gc> {
    fn of(mc: &Mutation<'gc>, vectors: &Vectors<'_, 'gc>, value: Value<'gc>) -> Option<Self> {
        if let Some(pair) = Pair::of(value) {
            return Some(Compound::Pair(pair));
        }
        if let Some(vector) = vectors.vector(value) {
            return Some(Compound::Vector(vector));
        }
        // Struct instances belonging to an identity type compare `equal?` strictly by pointer identity (`eq?`).
        if let Some(made) = value.downcast::<objects::Struct>(mc) {
            return made.kind(mc).is_some_and(|kind| !structs::type_flags(mc, kind).contains(TypeFlags::IDENTITY)).then_some(Compound::Struct(made));
        }
        value.downcast::<objects::Box>(mc).map(Compound::Box)
    }
}

/// Tracks comparison phases using Chez Scheme's `k` counter, decremented for each compound pair compared.
///
/// When `k >= 0` (fast phase), values are compared directly without cycle tracking.
/// When `-SLOW <= k < 0` (slow phase), values are merged into union-find equivalence classes
/// to detect cycles and terminate recursion on circular structures.
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

    /// Checks whether compound values `left` and `right` have already been unified into the same equivalence class
    /// during cycle detection, returning `true` to avoid re-comparing cycles.
    fn seen(&mut self, left: Value<'_>, right: Value<'_>) -> Result<bool, OutOfMemory> {
        if self.k == -(SLOW as i64) {
            self.k = (self.next_random() % (2 * PRECHECK)) as i64;
        }
        self.k -= 1;
        if self.k >= 0 {
            return Ok(false);
        }
        if self.classes.union(left, right)? {
            self.k = 0;
            return Ok(true);
        }
        Ok(false)
    }

    /// A 64-bit xorshift pseudo-random number generator, initialized with process-randomized hash keys
    /// on first access to randomize phase transitions and prevent adversarial inputs from triggering worst-case hashing behavior.
    fn next_random(&mut self) -> u64 {
        if self.random == 0 {
            self.random = RandomState::new().hash_one(self.classes.parent.len()) | 1;
        }
        let mut state = self.random;
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        self.random = state;
        state
    }
}

/// Disjoint-set (union-find) data structure maintaining equivalence classes of visited compound values
/// by object address, using union-by-size and path halving.
struct Classes<'gc> {
    index: HashMap<u64, usize, BuildHasherDefault<WordHasher>>,
    parent: Vec<usize>,
    size: Vec<u32>,
    charge: Charge<'gc>,
}

impl Classes<'_> {
    /// Merges the equivalence classes of values `left` and `right`. Returns `true` if they were already in the same equivalence class.
    fn union(&mut self, left: Value<'_>, right: Value<'_>) -> Result<bool, OutOfMemory> {
        let (first, second) = (self.find(left)?, self.find(right)?);
        if first == second {
            return Ok(true);
        }
        let (small, large) = if self.size[first] < self.size[second] { (first, second) } else { (second, first) };
        self.parent[small] = large;
        self.size[large] += self.size[small];
        Ok(false)
    }

    fn find(&mut self, value: Value<'_>) -> Result<usize, OutOfMemory> {
        let mut node = match self.index.get(&value.to_bits()) {
            Some(&node) => node,
            None => {
                self.charge.grow(CLASS_COST)?;
                let fresh = self.parent.len();
                self.index.insert(value.to_bits(), fresh);
                self.parent.push(fresh);
                self.size.push(1);
                fresh
            }
        };
        while self.parent[node] != node {
            self.parent[node] = self.parent[self.parent[node]];
            node = self.parent[node];
        }
        Ok(node)
    }
}

/// A fast 64-bit word hasher for object references whose index bits reside in the upper half and whose
/// lower bits contain common type tags. Uses a 64-bit multiplicative constant with 128-bit XOR-folded products
/// to disperse both high and low bits uniformly.
#[derive(Default)]
struct WordHasher(u64);

impl Hasher for WordHasher {
    fn write(&mut self, bytes: &[u8]) {
        bytes.iter().for_each(|&byte| self.write_u64(u64::from(byte)));
    }

    fn write_u64(&mut self, word: u64) {
        let product = u128::from(self.0 ^ word) * 0x9E37_79B9_7F4A_7C15;
        self.0 = (product >> 64) as u64 ^ product as u64;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

