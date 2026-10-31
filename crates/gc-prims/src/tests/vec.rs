use ragwort_gc::{Arena, Rootable, StepError};

use super::*;

#[derive(Trace, Plain)]
struct Num(i64);

type NumRef<'gc> = Option<Member<'gc, Num>>;

fn num<'gc>(mc: &Mutation<'gc>, n: i64) -> NumRef<'gc> {
    Some(Member::new(mc, mc.alloc(Num(n)).unwrap()))
}

/// Fills memory, a page at a time.
#[derive(Trace, Plain)]
#[gc(items = u8)]
struct Filler;

/// A buffer inside an arena object, so stores into it take the barrier like any other.
#[derive(Trace, Plain)]
struct Holder<'gc> {
    items: GcVec<'gc, NumRef<'gc>>,
}

struct HolderRoot;
impl Rootable for HolderRoot {
    type Root<'gc> = Lock<Option<Member<'gc, Holder<'gc>>>>;
}

fn holder_arena(limit: usize) -> Arena<HolderRoot> {
    Arena::new(limit, |mc| Ok(Lock::new(Some(Member::new(mc, mc.alloc(Holder { items: GcVec::new() })?))))).unwrap()
}

struct WordsRoot;
impl Rootable for WordsRoot {
    type Root<'gc> = GcVec<'gc, u64>;
}

#[test]
fn iterators_keep_their_range_and_storage() {
    let mut arena = Arena::<WordsRoot>::new(1 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, v| {
        assert_eq!(v.iter(mc).len(), 0);
        for i in 0..4 {
            v.push(mc, i).unwrap();
        }
        let mut iter = v.iter(mc);
        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.next_back(), Some(3));
        assert_eq!(iter.len(), 2);
        assert!(v.set(mc, 1, 11));
        assert_eq!(iter.clone().collect::<Vec<_>>(), [11, 2]);
        v.push(mc, 4).unwrap();
        assert!(v.set(mc, 1, 99));
        v.truncate(mc, 1);
        assert_eq!(iter.collect::<Vec<_>>(), [11, 2]);
        assert_eq!(v.iter(mc).collect::<Vec<_>>(), [0]);
    }).unwrap();
}

#[test]
fn buffers_grow_and_are_traced() {
    let n = if cfg!(miri) { 100 } else { 1000 };
    let mut arena = holder_arena(4 << 20);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        for i in 0..n {
            v.push(mc, num(mc, i)).unwrap();
        }
        assert_eq!(v.len(mc), n as usize);
        assert!(!v.is_empty(mc));
        assert!(v.capacity(mc) >= v.len(mc));
        assert_eq!(v.get(mc, 3).unwrap().unwrap().get(mc).0, 3);
        assert!(v.get(mc, n as usize).is_none());
        assert!(!v.set(mc, n as usize, None));
    }).unwrap();
    arena.collect();
    assert_eq!(arena.metrics().objects, n as usize + 2);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        assert_eq!(v.pop(mc).unwrap().unwrap().get(mc).0, n - 1);
        v.truncate(mc, 10);
        assert!(v.set(mc, 0, None));
    }).unwrap();
    arena.collect();
    assert_eq!(arena.metrics().objects, 9 + 2);
}

/// A length past the slots, as damaged memory could hold, reads as the slots' length.
#[test]
fn damaged_lengths_are_bounded() {
    let mut arena = holder_arena(1 << 20);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        for i in 0..8 {
            v.push(mc, num(mc, i)).unwrap();
        }
        v.len.set(mc, u32::MAX);
        assert_eq!((v.len(mc), v.capacity(mc)), (8, 8));
        assert_eq!(v.iter(mc).len(), 8);
        assert_eq!(v.iter(mc).count(), 8);
        assert!(v.get(mc, 1000).is_none());
        v.truncate(mc, 1000);
        assert!((0..8).all(|i| v.get(mc, i).flatten().is_some()), "truncating above the length cleared items");
        assert!(v.pop(mc).is_some());
        v.truncate(mc, 2);
        assert_eq!(v.len(mc), 2);
        v.len.set(mc, u32::MAX);
        v.truncate(mc, 0);
        assert_eq!(v.len(mc), 0);
    }).unwrap();
}

/// Growth a buffer can do without stays out of the reserve, so it grows by what it needs.
#[test]
fn optional_growth_leaves_the_reserve_alone() {
    let mut arena = Arena::<WordsRoot>::new(256 * 1024, |_| Ok(GcVec::new())).unwrap();
    arena.set_reserve(128 * 1024);
    let capacity = arena.mutate(|mc, v| {
        while !mc.collection_due() {
            v.push(mc, 0).unwrap();
        }
        assert!(mc.used() <= 256 * 1024);
        v.capacity(mc)
    }).unwrap();
    assert_eq!(arena.mutate(|mc, v| v.len(mc)).unwrap(), capacity, "the growth that drew on the reserve was exact");
}

#[test]
fn buffers_grow_by_less_when_doubling_does_not_fit() {
    let limit = 1 << 20;
    let mut arena = Arena::<WordsRoot>::new(limit, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, v| {
        for i in 0..32768 {
            v.push(mc, i).unwrap();
        }
        assert_eq!(v.capacity(mc), 32768);
        while mc.limit() - mc.used() > 420 * 1024 {
            mc.alloc_inline(Filler, (16 << 10) - 8, |_| 0).unwrap();
        }
        v.push(mc, 32768).unwrap();
        assert_eq!(v.capacity(mc), 32769);
        assert_eq!(v.get(mc, 32768), Some(32768));
        assert_eq!(v.get(mc, 100), Some(100));
    }).unwrap();
}

#[test]
fn growth_never_fails_when_the_needed_size_fits() {
    let fill = |arena: &mut Arena<WordsRoot>| {
        arena.mutate(|mc, v| {
            for i in 0..2048 {
                v.push(mc, i).unwrap();
            }
            mc.used()
        }).unwrap()
    };
    let used = fill(&mut Arena::<WordsRoot>::new(1 << 20, |_| Ok(GcVec::new())).unwrap());
    let mut capacities = Vec::new();
    for spare in (33_000..54_000).step_by(if cfg!(miri) { 700 } else { 100 }) {
        let mut arena = Arena::<WordsRoot>::new(used + spare, |_| Ok(GcVec::new())).unwrap();
        arena.set_reserve(0);
        fill(&mut arena);
        // With too little spare even the needed size doesn't fit until a collection, so the
        // push is run again. Once it fits, the bigger allocation tried first must never fail
        // the step.
        let mut runs = 0;
        let capacity = loop {
            runs += 1;
            match arena.step(|mc, v| v.push(mc, 2048).map(|_| v.capacity(mc))) {
                Ok(capacity) => break capacity,
                Err(StepError::OutOfMemory) if runs == 1 => {}
                Err(e) => panic!("{e:?}"),
            }
        };
        if runs == 1 || !capacities.is_empty() {
            assert_eq!(runs, 1, "a fallback allocation made the step retry ({spare} bytes spare)");
            capacities.push(capacity);
        }
    }
    assert_eq!(capacities.first(), Some(&2049));
    assert_eq!(capacities.last(), Some(&4096));
    assert!(capacities.is_sorted() && capacities.len() > 100);
}

/// An element so large that fewer than four fit in the region.
#[derive(Trace, Plain, Clone, Copy)]
struct Huge([u64; (17 << 20) / 8]);

impl Default for Huge {
    fn default() -> Self {
        Huge([0; (17 << 20) / 8])
    }
}

struct HugeRoot;
impl Rootable for HugeRoot {
    type Root<'gc> = GcVec<'gc, Huge>;
}

/// Growing a buffer of elements so large that fewer than four fit allocates what it can or
/// fails with `OutOfMemory`, without panicking.
#[test]
#[cfg_attr(miri, ignore = "the region is smaller than one element")]
fn buffers_of_huge_elements_grow_or_fail() {
    assert_eq!(max_items::<Slots<Huge>>(), 3);
    // The elements are built on the stack, which the default test thread is too small for.
    let run = std::thread::Builder::new().stack_size(1 << 30).spawn(|| {
        // With room, growth stops at the three that fit, and a fourth can't be added.
        // Without room for three, it falls back to the one needed.
        for (limit, fits) in [(60 << 20, 3), (40 << 20, 1)] {
            let mut arena = Arena::<HugeRoot>::new(limit, |_| Ok(GcVec::new())).unwrap();
            arena.mutate(|mc, root| {
                for _ in 0..fits {
                    root.push(mc, Huge::default()).unwrap();
                }
                assert_eq!(root.push(mc, Huge::default()), Err(OutOfMemory), "limit {limit}");
                assert_eq!(root.len(mc), fits);
            }).unwrap();
        }
    });
    run.unwrap().join().unwrap();
}
