use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::mem::size_of;
use std::num::NonZeroU32;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use super::heap::{GRAY_BYTES, META};
use super::layout::{self, HEADER, LINE, PAGE, RESERVE, round_up};
use super::*;

#[derive(Trace, Plain)]
struct Node<'gc> {
    value: i64,
    next: Lock<NodeRef<'gc>>,
    _pad: u32,
}

type NodeRef<'gc> = Option<Member<'gc, Node<'gc>>>;

const NODE: usize = 24;

fn node<'gc>(mc: &Mutation<'gc>, value: i64, next: Option<Gc<'gc, Node<'gc>>>) -> Result<Gc<'gc, Node<'gc>>, OutOfMemory> {
    mc.alloc(Node { value, next: Lock::new(next.map(|n| Member::new(mc, n))), _pad: 0 })
}

fn offset<T>(mc: &Mutation<'_>, gc: Gc<'_, T>) -> usize {
    Gc::as_ptr(gc).addr() - mc.base.as_ptr().addr() - HEADER
}

struct NodeRoot;
impl Rootable for NodeRoot {
    type Root<'gc> = Lock<NodeRef<'gc>>;
}

struct PairRoot;
impl Rootable for PairRoot {
    type Root<'gc> = (Lock<NodeRef<'gc>>, Lock<NodeRef<'gc>>);
}

struct Unit;
impl Rootable for Unit {
    type Root<'gc> = ();
}

struct NodeK;
impl Rooted for NodeK {
    type Of<'gc> = Member<'gc, Node<'gc>>;
}

fn node_arena(limit: usize) -> Arena<NodeRoot> {
    Arena::new(limit, |_| Ok(Lock::new(None))).unwrap()
}

fn pair_arena(limit: usize) -> Arena<PairRoot> {
    Arena::new(limit, |_| Ok((Lock::new(None), Lock::new(None)))).unwrap()
}

fn unit_arena(limit: usize) -> Arena<Unit> {
    Arena::new(limit, |_| Ok(())).unwrap()
}

#[derive(Trace, Plain)]
#[gc(items = u8)]
struct Bytes {
    tag: u32,
}

fn bytes_size(len: usize) -> usize {
    round_up(HEADER + 4 + len, 8)
}

/// What an empty arena uses: the gray stack, charged up front.
const BASE: usize = GRAY_BYTES;

#[derive(Trace, Plain)]
#[gc(items = Lock<NodeRef<'gc>>)]
struct Slots<'gc>(PhantomData<&'gc ()>);

fn slot_items<'gc>(slots: Gc<'gc, Slots<'gc>>) -> &'gc [Lock<NodeRef<'gc>>] {
    slots.items()
}

struct SlotsRoot;
impl Rootable for SlotsRoot {
    type Root<'gc> = Lock<Option<Member<'gc, Slots<'gc>>>>;
}

fn slots_arena(limit: usize, len: usize) -> Arena<SlotsRoot> {
    Arena::new(limit, |mc| {
        let slots = mc.alloc_inline(Slots(PhantomData), len, |_| Lock::new(None))?;
        Ok(Lock::new(Some(Member::new(mc, slots))))
    })
    .unwrap()
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn chain<'gc>(mc: &Mutation<'gc>, len: i64, tail: Option<Gc<'gc, Node<'gc>>>) -> Option<Gc<'gc, Node<'gc>>> {
    let mut head = tail;
    for i in 0..len {
        head = Some(node(mc, 1000 + i, head).unwrap());
    }
    head
}

fn last<'gc>(mc: &Mutation<'gc>, mut cur: Gc<'gc, Node<'gc>>) -> Gc<'gc, Node<'gc>> {
    while let Some(next) = cur.next.load(mc) {
        cur = next;
    }
    cur
}

#[test]
fn sizes() {
    assert_eq!(HEADER, 8);
    assert_eq!(size_of::<Member<'static, i64>>(), 4);
    assert_eq!(size_of::<Option<Member<'static, i64>>>(), 4);
    assert_eq!(size_of::<Gc<'static, i64>>(), 8);
    assert_eq!(size_of::<Weak<'static, i64>>(), 8);
    assert_eq!(size_of::<Ephemeron<'static, i64, u64>>(), 16);
    assert_eq!(layout::sized_size::<Node<'static>>(), NODE);
    assert!(Arena::<Unit>::new(GRAY_BYTES - 1, |_| Ok(())).is_err());
}

#[test]
fn allocation_sizes() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, _| {
        let n = node(mc, 7, None).unwrap();
        assert_eq!(mc.used(), BASE + PAGE + META);
        assert_eq!(n.value, 7);

        let b = mc.alloc_inline_from(Bytes { tag: 9 }, b"hello").unwrap();
        assert_eq!((b.tag, b.items(), b.len()), (9, &b"hello"[..], 5));
        let empty = mc.alloc_inline_from(Bytes { tag: 0 }, &[]).unwrap();
        assert!(empty.is_empty());
        assert_eq!(offset(mc, n) % PAGE, 0);
        assert_eq!(offset(mc, b), offset(mc, n) + NODE);
    });
    let m = arena.metrics();
    // The first page is claimed whole for bump allocation.
    assert_eq!((m.objects, m.live, m.pages), (3, PAGE, 1));
}

#[test]
fn collect_frees_unreachable() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| {
        let a = node(mc, 1, None).unwrap();
        let b = node(mc, 2, Some(a)).unwrap();
        root.store(mc, Some(b));
        for i in 0..100 {
            node(mc, i, None).unwrap();
        }
    });
    assert_eq!(arena.metrics().objects, 102);
    arena.collect();
    let m = arena.metrics();
    assert_eq!((m.objects, m.live, m.used, m.collections), (2, LINE, BASE + PAGE + META, 1));

    arena.mutate(|mc, root| {
        let b = root.load(mc).unwrap();
        assert_eq!(b.value, 2);
        assert_eq!(b.next.load(mc).unwrap().value, 1);
        root.set(mc, None);
    });
    arena.collect();
    let m = arena.metrics();
    assert_eq!((m.objects, m.live, m.used, m.pages), (0, 0, BASE, 0));
}

#[test]
fn cycles_are_collected() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| {
        let a = node(mc, 1, None).unwrap();
        let b = node(mc, 2, Some(a)).unwrap();
        a.next.store(mc, Some(b));
        root.store(mc, Some(a));
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, 2);
    arena.mutate(|mc, root| root.set(mc, None));
    arena.collect();
    assert_eq!((arena.metrics().objects, arena.metrics().used), (0, BASE));
}

#[test]
fn deep_chain_marks_without_recursion() {
    let n: i64 = if cfg!(miri) { 1_000 } else { 1_000_000 };
    let mut arena = node_arena(REGION);
    arena.mutate(|mc, root| root.store(mc, chain(mc, n, None)));
    arena.collect();
    assert_eq!(arena.metrics().objects, n as usize);
    arena.mutate(|mc, root| {
        let (mut count, mut cur) = (0, root.load(mc));
        while let Some(node) = cur {
            assert_eq!(node.value, 1000 + n - 1 - count);
            count += 1;
            cur = node.next.load(mc);
        }
        assert_eq!(count, n);
    });
    arena.mutate(|mc, root| root.set(mc, None));
    arena.collect();
    assert_eq!(arena.metrics().used, BASE);
}

#[test]
fn inline_items_are_traced() {
    let mut arena = slots_arena(1 << 20, 3);
    arena.mutate(|mc, root| {
        for (i, slot) in slot_items(root.load(mc).unwrap()).iter().enumerate() {
            slot.store(mc, Some(node(mc, i as i64, None).unwrap()));
        }
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, 4);
    arena.mutate(|mc, root| {
        let items = slot_items(root.load(mc).unwrap());
        assert_eq!(items.iter().map(|s| s.load(mc).unwrap().value).collect::<Vec<_>>(), [0, 1, 2]);
        items[1].set(mc, None);
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, 3);
}

#[test]
fn objects_of_every_size() {
    let mut arena = unit_arena(REGION);
    let step = if cfg!(miri) { 997 } else { 61 };
    let lens: Vec<usize> = (0..20_000).step_by(step).chain([116, 117, 8180, 8181, 16_372, 40_000]).collect();
    arena.mutate(|mc, _| {
        let all: Vec<_> = lens.iter().map(|&len| mc.alloc_inline(Bytes { tag: len as u32 }, len, |i| i as u8).unwrap()).collect();
        for (b, &len) in all.iter().zip(&lens) {
            assert_eq!((b.len(), b.tag), (len, len as u32));
            assert!(b.items().iter().enumerate().all(|(i, &x)| x == i as u8));
            assert!(offset(mc, *b) % PAGE == 0 || bytes_size(len) <= layout::MAX_SMALL);
        }
        mc.heap.check();
    });
    arena.collect();
    let m = arena.metrics();
    assert_eq!((m.objects, m.live, m.pages, m.used), (0, 0, 0, BASE));
}

#[test]
fn freed_slots_are_reused() {
    let mut arena = node_arena(1 << 20);
    let first: Vec<usize> = arena.mutate(|mc, _| (0..10).map(|i| offset(mc, node(mc, i, None).unwrap())).collect());
    arena.collect();
    let second: Vec<usize> = arena.mutate(|mc, _| (0..10).map(|i| offset(mc, node(mc, i, None).unwrap())).collect());
    assert_eq!(first, second);

    arena.mutate(|mc, root| root.store(mc, Some(node(mc, 1, None).unwrap())));
    arena.collect();
    let reused = arena.mutate(|mc, _| offset(mc, node(mc, 2, None).unwrap()));
    assert!(first.contains(&reused));
}

#[test]
fn large_objects_use_page_runs() {
    let mut arena = unit_arena(1 << 20);
    arena.mutate(|mc, _| {
        let b = mc.alloc_inline(Bytes { tag: 0 }, 3 * PAGE, |_| 7).unwrap();
        assert_eq!(offset(mc, b) % PAGE, 0);
        assert!(b.items().iter().all(|&x| x == 7));
        assert_eq!(mc.used(), BASE + 4 * (PAGE + META));
    });
    arena.collect();
    assert_eq!(arena.metrics().used, BASE);
}

#[test]
fn budget_never_exceeds_limit() {
    let limit = 512 * 1024;
    let mut arena = unit_arena(limit);
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for _ in 0..if cfg!(miri) { 2 } else { 20 } {
        arena.mutate(|mc, _| {
            let mut failures = 0;
            while failures < 20 {
                let len = if rng.below(8) == 0 { rng.below(40_000) } else { rng.below(4096) };
                let before = mc.used();
                match mc.alloc_inline(Bytes { tag: 0 }, len, |i| i as u8) {
                    Ok(b) => assert_eq!(b.items().len(), len),
                    Err(OutOfMemory) => {
                        assert_eq!(mc.used(), before);
                        failures += 1;
                    }
                }
                assert!(mc.used() <= limit);
            }
            mc.heap.check();
        });
        arena.collect();
        assert_eq!(arena.metrics().used, BASE);
    }
    assert!(arena.metrics().peak <= limit);
}

#[test]
fn step_retries_after_collecting_garbage() {
    let mut arena = node_arena(64 * 1024);
    arena.mutate(|mc, _| while node(mc, 0, None).is_ok() {});
    assert_eq!(arena.metrics().pages, 3);

    let mut attempts = 0;
    let result = arena.step(|mc, root| {
        attempts += 1;
        let n = node(mc, 5, None)?;
        root.store(mc, Some(n));
        Ok::<_, OutOfMemory>(())
    });
    assert!(result.is_ok());
    assert_eq!(attempts, 2);
    assert_eq!(arena.metrics().objects, 1);
    arena.mutate(|mc, root| assert_eq!(root.load(mc).unwrap().value, 5));
}

#[test]
fn step_reports_real_out_of_memory() {
    let mut arena = node_arena(64 * 1024);
    let result = arena.step(|mc, root| -> Result<(), OutOfMemory> {
        loop {
            let n = node(mc, 0, root.load(mc))?;
            root.store(mc, Some(n));
        }
    });
    assert!(matches!(result, Err(StepError::OutOfMemory)));
    let m = arena.metrics();
    assert!(m.used <= m.limit && m.peak <= m.limit);
}

#[test]
fn step_ignores_swallowed_failures() {
    let mut arena = unit_arena(1 << 20);
    let result = arena.step(|mc, _| {
        let _ = mc.alloc_inline(Bytes { tag: 0 }, 1 << 30, |_| 0);
        Ok::<_, ()>(())
    });
    assert!(matches!(result, Err(StepError::OutOfMemory)));
    assert_eq!(arena.metrics().used, BASE);

    let result = arena.step(|mc, _| mc.alloc(1i64).map(|_| ()).map_err(|_| ()));
    assert!(result.is_ok());
}

#[test]
fn step_passes_through_errors() {
    let mut arena = unit_arena(1 << 20);
    let result: Result<(), _> = arena.step(|_, _| Err("nope"));
    assert!(matches!(result, Err(StepError::Failed("nope"))));
}

#[test]
fn young_garbage_goes_in_a_minor_collection() {
    let mut arena = unit_arena(4 << 20);
    arena
        .step(|mc, _| {
            for _ in 0..200 {
                mc.alloc_inline(Bytes { tag: 0 }, 1024, |_| 0)?;
            }
            Ok::<_, OutOfMemory>(())
        })
        .unwrap();
    let m = arena.metrics();
    assert_eq!((m.minor_collections, m.collections, m.live, m.phase), (1, 0, 0, Phase::Idle));
}

#[test]
fn surviving_data_past_the_threshold_starts_a_major_cycle() {
    let mut arena = unit_arena(4 << 20);
    let roots = arena
        .step(|mc, _| {
            (0..200)
                .map(|_| mc.root::<BytesK>(Member::new(mc, mc.alloc_inline(Bytes { tag: 0 }, 1024, |_| 0)?)))
                .collect::<Result<Vec<_>, _>>()
        })
        .unwrap();
    for _ in 0..10 {
        arena.step(|_, _| Ok::<_, ()>(())).unwrap();
    }
    let m = arena.metrics();
    assert_eq!((m.minor_collections, m.collections, m.objects, m.phase), (1, 1, 200, Phase::Idle));
    drop(roots);
}

#[test]
fn oversized_layouts_fail_cleanly() {
    let mut arena = slots_arena(1 << 20, 0);
    arena.mutate(|mc, _| {
        let used = mc.used();
        assert!(mc.alloc_inline(Bytes { tag: 0 }, usize::MAX, |_| 0).is_err());
        assert!(mc.alloc_inline(Bytes { tag: 0 }, REGION, |_| 0).is_err());
        assert!(mc.alloc_inline(Slots(PhantomData), usize::MAX / 4, |_| Lock::new(None)).is_err());
        assert_eq!(mc.used(), used);
        assert!(mc.ensure((1 << 20) - used).is_ok());
        assert!(mc.ensure((1 << 20) - used + 1).is_err());
    });
}

#[test]
fn panicking_fill_leaks_nothing() {
    let mut arena = unit_arena(1 << 20);
    for len in [10, 3 * PAGE] {
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            arena.mutate(|mc, _| {
                let _ = mc.alloc_inline(Bytes { tag: 0 }, len, |i| if i == 5 { panic!("fill failed") } else { 0 });
            })
        }));
        assert!(result.is_err());
        let m = arena.metrics();
        assert_eq!((m.objects, m.live), (0, 0));
    }
    arena.collect();
    assert_eq!(arena.metrics().used, BASE);
    arena.mutate(|mc, _| assert_eq!(mc.alloc_inline_from(Bytes { tag: 1 }, b"ok").unwrap().items(), b"ok"));
}

static HOST_DROPS: AtomicUsize = AtomicUsize::new(0);

struct HostValue(u32);

impl Drop for HostValue {
    fn drop(&mut self) {
        HOST_DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

#[derive(Trace, Plain)]
struct Holder<'gc> {
    host: Lock<HostRef<'gc, HostValue>>,
}

struct HolderK;
impl Rooted for HolderK {
    type Of<'gc> = Member<'gc, Holder<'gc>>;
}

#[test]
fn host_values_live_while_reachable() {
    let base = HOST_DROPS.load(Ordering::Relaxed);
    let mut arena = unit_arena(1 << 20);
    let root = arena.mutate(|mc, _| {
        for i in 0..5 {
            mc.host(HostValue(i)).unwrap();
        }
        let host = mc.host(HostValue(42)).unwrap();
        assert_eq!(host.get(mc).unwrap().0, 42);
        let holder = mc.alloc(Holder { host: Lock::new(host) }).unwrap();
        mc.root::<HolderK>(Member::new(mc, holder)).unwrap()
    });
    assert_eq!(arena.metrics().hosts, 6);
    arena.collect();
    assert_eq!(HOST_DROPS.load(Ordering::Relaxed) - base, 5);
    arena.mutate(|mc, _| {
        let holder = mc.fetch(&root).unwrap().get(mc);
        assert_eq!(holder.host.get().get(mc).unwrap().0, 42);
    });
    drop(root);
    arena.collect();
    assert_eq!(HOST_DROPS.load(Ordering::Relaxed) - base, 6);
    assert_eq!(arena.metrics().hosts, 0);

    arena.mutate(|mc, _| {
        mc.host(HostValue(7)).unwrap();
    });
    drop(arena);
    assert_eq!(HOST_DROPS.load(Ordering::Relaxed) - base, 7);
}

static INIT_DROPS: AtomicUsize = AtomicUsize::new(0);

struct InitValue;

impl Drop for InitValue {
    fn drop(&mut self) {
        INIT_DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn failed_init_frees_partial_work() {
    let mut made = 0;
    let result = Arena::<Unit>::new(4096, |mc| {
        loop {
            mc.host(InitValue)?;
            made += 1;
        }
    });
    assert!(result.is_err());
    assert_eq!(INIT_DROPS.load(Ordering::Relaxed), made + 1);
}

#[test]
fn roots_keep_values_alive() {
    let mut arena = node_arena(1 << 20);
    let root = arena.mutate(|mc, _| mc.root::<NodeK>(Member::new(mc, node(mc, 42, None).unwrap())).unwrap());
    let copy = root.clone();
    arena.collect();
    assert_eq!(arena.metrics().objects, 1);
    drop(root);
    arena.collect();
    arena.mutate(|mc, _| assert_eq!(mc.fetch(&copy).unwrap().get(mc).value, 42));
    assert_eq!(arena.metrics().used, BASE + PAGE + META + 64 + size_of::<std::rc::Rc<dyn super::root::RootEntry>>());
    drop(copy);
    arena.collect();
    assert_eq!((arena.metrics().objects, arena.metrics().used), (0, BASE));
}

#[test]
fn fetching_from_another_arena_fails() {
    let mut a = node_arena(1 << 20);
    let mut b = node_arena(1 << 20);
    let root = a.mutate(|mc, _| mc.root::<NodeK>(Member::new(mc, node(mc, 1, None).unwrap())).unwrap());
    b.mutate(|mc, _| assert_eq!(mc.fetch(&root).err(), Some(ForeignRoot)));
    a.mutate(|mc, _| assert_eq!(mc.fetch(&root).unwrap().get(mc).value, 1));
}

#[test]
fn roots_outliving_their_arena_are_harmless() {
    let mut arena = node_arena(1 << 20);
    let root = arena.mutate(|mc, _| mc.root::<NodeK>(Member::new(mc, node(mc, 1, None).unwrap())).unwrap());
    drop(arena);
    drop(root);
}

#[test]
fn reflock_borrows_fail_instead_of_panicking() {
    let mut arena = unit_arena(1 << 20);
    arena.mutate(|mc, _| {
        let lock = RefLock::new(1);
        let guard = lock.borrow_mut(mc).unwrap();
        assert!(lock.borrow().is_err());
        assert!(lock.borrow_mut(mc).is_err());
        drop(guard);
        assert_eq!(*lock.borrow().unwrap(), 1);
    });
}

#[derive(Trace, Plain)]
struct VecHolder<'gc> {
    items: GcVec<'gc, NodeRef<'gc>>,
}

struct VecRoot;
impl Rootable for VecRoot {
    type Root<'gc> = Lock<Option<Member<'gc, VecHolder<'gc>>>>;
}

fn vec_arena(limit: usize) -> Arena<VecRoot> {
    Arena::new(limit, |mc| Ok(Lock::new(Some(Member::new(mc, mc.alloc(VecHolder { items: GcVec::new() })?))))).unwrap()
}

#[test]
fn gcvec_grows_and_is_traced() {
    let n = if cfg!(miri) { 100 } else { 1000 };
    let mut arena = vec_arena(4 << 20);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        for i in 0..n {
            v.push(mc, Some(Member::new(mc, node(mc, i, None).unwrap()))).unwrap();
        }
        assert_eq!(v.len(mc), n as usize);
        assert!(v.capacity(mc) >= v.len(mc));
        assert_eq!(v.get(mc, 3).unwrap().unwrap().get(mc).value, 3);
        assert!(v.get(mc, n as usize).is_none());
        assert!(!v.set(mc, n as usize, None));
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, n as usize + 2);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        assert_eq!(v.pop(mc).unwrap().unwrap().get(mc).value, n - 1);
        v.truncate(mc, 10);
        assert!(v.set(mc, 0, None));
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, 9 + 2);
}

#[test]
fn mutate_root_replaces_the_root() {
    let mut arena = node_arena(1 << 20);
    arena.mutate_root(|mc, root| *root = Lock::new(Some(Member::new(mc, node(mc, 3, None).unwrap()))));
    arena.collect();
    arena.mutate(|mc, root| assert_eq!(root.load(mc).unwrap().value, 3));
}

/// Root `.1` holds a node that gets traced first; root `.0` holds a long chain ending in the
/// node that will move. Returns once `.1` is black and the chain's tail is still white.
fn black_and_white(arena: &mut Arena<PairRoot>) {
    arena.mutate(|mc, root| {
        root.0.store(mc, chain(mc, 50, Some(node(mc, 7, None).unwrap())));
        root.1.store(mc, Some(node(mc, 1, None).unwrap()));
    });
    arena.collect_slice(NODE);
    assert_eq!(arena.metrics().phase, Phase::Marking);
}

fn move_tail<'gc>(mc: &Mutation<'gc>, root: &(Lock<NodeRef<'gc>>, Lock<NodeRef<'gc>>)) -> Gc<'gc, Node<'gc>> {
    let mut before = root.0.load(mc).unwrap();
    while before.next.load(mc).unwrap().next.get().is_some() {
        before = before.next.load(mc).unwrap();
    }
    let tail = before.next.load(mc).unwrap();
    before.next.set(mc, None);
    tail
}

fn check_moved(arena: &mut Arena<PairRoot>, objects: usize) {
    arena.heap().check();
    arena.collect();
    arena.heap().check();
    let m = arena.metrics();
    assert!(!m.corrupted);
    assert_eq!(m.objects, objects);
    arena.mutate(|mc, root| assert_eq!(last(mc, root.1.load(mc).unwrap()).value, 7));
}

#[test]
fn barrier_shades_stores_into_black_objects() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        root.1.load(mc).unwrap().next.store(mc, Some(tail));
    });
    check_moved(&mut arena, 52);
}

#[test]
#[should_panic(expected = "gc verify")]
fn verifier_catches_a_missing_barrier() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        unsafe { root.1.load(mc).unwrap().next.set_unbarriered(Some(Member::new(mc, tail))) };
    });
    arena.collect();
}

#[test]
fn retrace_covers_unbarriered_stores() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        let black = root.1.load(mc).unwrap();
        unsafe { black.next.set_unbarriered(Some(Member::new(mc, tail))) };
        mc.retrace(black);
        mc.retrace(black);
    });
    check_moved(&mut arena, 52);
}

#[test]
fn root_stores_are_rescanned() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        root.1.store(mc, Some(node(mc, 1, Some(tail)).unwrap()));
    });
    check_moved(&mut arena, 52);

    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate_root(|mc, root| {
        let tail = move_tail(mc, root);
        root.1 = Lock::new(Some(Member::new(mc, node(mc, 1, Some(tail)).unwrap())));
    });
    check_moved(&mut arena, 52);
}

#[test]
fn objects_allocated_while_marking_are_traced() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        let holder = node(mc, 1, Some(tail)).unwrap();
        root.1.load(mc).unwrap().next.store(mc, Some(holder));
    });
    check_moved(&mut arena, 53);
}

#[test]
fn objects_allocated_while_sweeping_survive() {
    let mut arena = node_arena(4 << 20);
    arena.mutate(|mc, _| {
        for _ in 0..40 {
            mc.alloc_inline(Bytes { tag: 0 }, 9000, |_| 0).unwrap();
        }
        for i in 0..2000 {
            node(mc, i, None).unwrap();
        }
    });
    arena.collect_slice(1);
    arena.collect_slice(1);
    assert_eq!(arena.metrics().phase, Phase::Sweeping);
    arena.collect_slice(5 * PAGE / 8);
    assert_eq!(arena.metrics().phase, Phase::Sweeping);
    arena.mutate(|mc, root| {
        let big = mc.alloc_inline(Bytes { tag: 3 }, 9000, |_| 3).unwrap();
        assert_eq!(big.len(), 9000);
        root.store(mc, chain(mc, 3000, None));
    });
    arena.collect();
    arena.mutate(|mc, root| {
        let mut count = 0;
        let mut cur = root.load(mc);
        while let Some(n) = cur {
            assert_eq!(n.value, 1000 + 2999 - count);
            count += 1;
            cur = n.next.load(mc);
        }
        assert_eq!(count, 3000);
    });
    assert_eq!(arena.metrics().objects, 3000);
}

#[test]
fn stress_random_graph_mutation() {
    const SLOTS: usize = 16;
    let steps = if cfg!(miri) { 150 } else { 4000 };
    for work in [1, 48, 1000] {
        let mut arena = slots_arena(2 << 20, SLOTS);
        arena.set_stress(Some(work));
        let mut rng = Rng(0x2545f4914f6cdd1d ^ work as u64);
        let mut slots: [Option<i64>; SLOTS] = [None; SLOTS];
        let mut next_of: HashMap<i64, Option<i64>> = HashMap::new();
        for id in 0..steps {
            let (a, b) = (rng.below(SLOTS), rng.below(SLOTS));
            let op = rng.below(5);
            arena
                .step(|mc, root| {
                    let items = slot_items(root.load(mc).unwrap());
                    match op {
                        0 | 1 => {
                            let n = node(mc, id, items[b].load(mc))?;
                            items[a].store(mc, Some(n));
                        }
                        2 => {
                            if let Some(n) = items[a].load(mc) {
                                n.next.set(mc, items[b].get());
                            }
                        }
                        3 => items[a].set(mc, items[b].load(mc).and_then(|n| n.next.get())),
                        _ => items[a].set(mc, None),
                    }
                    Ok::<_, OutOfMemory>(())
                })
                .unwrap();
            match op {
                0 | 1 => {
                    next_of.insert(id, slots[b]);
                    slots[a] = Some(id);
                }
                2 => {
                    if let Some(x) = slots[a] {
                        next_of.insert(x, slots[b]);
                    }
                }
                3 => slots[a] = slots[b].and_then(|x| next_of[&x]),
                _ => slots[a] = None,
            }
            arena.heap().check();
            let c = rng.below(SLOTS);
            arena.mutate(|mc, root| {
                let (mut cur, mut want) = (slot_items(root.load(mc).unwrap())[c].load(mc), slots[c]);
                for _ in 0..8 {
                    assert_eq!(cur.map(|n| n.value), want);
                    let Some(n) = cur else { break };
                    cur = n.next.load(mc);
                    want = next_of[&n.value];
                }
            });
        }
        assert!(arena.metrics().collections > 0);
        arena.set_stress(None);
        arena.collect();
        let mut reachable = HashSet::new();
        let mut pending: Vec<i64> = slots.iter().flatten().copied().collect();
        while let Some(x) = pending.pop() {
            if reachable.insert(x) {
                pending.extend(next_of[&x]);
            }
        }
        assert_eq!(arena.metrics().objects, reachable.len() + 1);
    }
}

fn corrupt_u32(arena: &Arena<impl Rootable>, offset: usize, value: u32) {
    unsafe { arena.heap().base.as_ptr().add(offset).cast::<u32>().write_unaligned(value) }
}

#[test]
fn bad_offsets_are_detected() {
    for bits in [3u32, 8, REGION as u32 - 8, PAGE as u32 + 4, 0x10_0000] {
        let mut arena = node_arena(1 << 20);
        arena.mutate(|mc, root| {
            let n = node(mc, 1, None).unwrap();
            root.store(mc, Some(n));
            unsafe { n.next.set_unbarriered(Some(Member::from_bits(NonZeroU32::new(bits).unwrap()))) };
        });
        arena.collect();
        assert!(arena.metrics().corrupted, "{bits:#x}");
        assert!(matches!(arena.step(|_, _| Ok::<_, ()>(())), Err(StepError::Corrupted)));
    }
}

#[test]
fn bad_headers_are_detected() {
    let mut arena = slots_arena(1 << 20, 2);
    let off = arena.mutate(|mc, root| offset(mc, root.load(mc).unwrap()));
    unsafe { (*arena.heap().header_of(off as u32)).len = 1 << 20 };
    arena.collect();
    assert!(arena.metrics().corrupted);

    let mut arena = slots_arena(1 << 20, 2);
    let off = arena.mutate(|mc, root| offset(mc, root.load(mc).unwrap()));
    unsafe { (*arena.heap().header_of(off as u32)).ty = 999 };
    arena.collect();
    assert!(arena.metrics().corrupted);
}

#[test]
fn corrupted_items_stay_inside_the_reservation() {
    let mut arena = slots_arena(1 << 20, 2);
    let off = arena.mutate(|mc, root| offset(mc, root.load(mc).unwrap()));
    unsafe { (*arena.heap().header_of(off as u32)).len = u32::MAX };
    arena.mutate(|mc, root| {
        let slots = root.load(mc).unwrap();
        let base = mc.base.as_ptr().addr();
        let start = slots.items().as_ptr().addr();
        assert!(start >= base && start + slots.len() * 4 <= base + RESERVE);

        let wild = unsafe { Member::<Node<'_>>::from_bits(NonZeroU32::new(u32::MAX).unwrap()) }.get(mc);
        let addr = Gc::as_ptr(wild).addr();
        assert!(addr >= base && addr + size_of::<Node<'_>>() <= base + RESERVE);
    });
}

#[test]
fn random_corruption_never_escapes() {
    let rounds = if cfg!(miri) { 3 } else { 300 };
    let mut rng = Rng(0xdeadbeefcafef00d);
    let mut detected = 0;
    for _ in 0..rounds {
        let mut arena = vec_arena(1 << 20);
        let offsets = arena.mutate(|mc, root| {
            let v = &root.load(mc).unwrap().items;
            let mut offsets = vec![];
            for i in 0..40 {
                let next = v.get(mc, rng.below(v.len(mc).max(1))).flatten().map(|m| m.get(mc));
                let n = node(mc, i, next).unwrap();
                offsets.push(offset(mc, n));
                v.push(mc, Some(Member::new(mc, n))).unwrap();
            }
            offsets
        });
        for _ in 0..1 + rng.below(4) {
            let at = offsets[rng.below(offsets.len())] + rng.below(NODE / 4) * 4;
            let value = match rng.below(3) {
                0 => rng.next() as u32,
                1 => offsets[rng.below(offsets.len())] as u32 + rng.below(3) as u32 * 4,
                _ => rng.next() as u32 & 0xffff,
            };
            corrupt_u32(&arena, at, value);
        }
        arena.collect();
        arena.collect();
        detected += arena.metrics().corrupted as usize;
    }
    assert!(detected > 0);
}

#[test]
fn phases_advance_in_slices() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| root.store(mc, chain(mc, 100, None)));
    assert_eq!(arena.metrics().phase, Phase::Idle);
    arena.collect_slice(NODE * 10);
    assert_eq!(arena.metrics().phase, Phase::Marking);
    let mut slices = 1;
    while arena.metrics().phase != Phase::Idle {
        assert!(slices < 100, "cycle never finished");
        arena.collect_slice(NODE * 10);
        slices += 1;
    }
    assert!((10..=13).contains(&slices), "{slices}");
    assert_eq!((arena.metrics().collections, arena.metrics().objects), (1, 100));
}

static TRACE_PANICS: AtomicBool = AtomicBool::new(false);

struct Bomb;

unsafe impl Trace for Bomb {
    fn trace(&mut self, _: &mut Tracer<'_>) {
        if TRACE_PANICS.load(Ordering::Relaxed) {
            panic!("trace failed");
        }
    }
}

unsafe impl Plain<'_> for Bomb {}

struct BombRoot;
impl Rootable for BombRoot {
    type Root<'gc> = Lock<Option<Member<'gc, Bomb>>>;
}

#[test]
fn panicking_trace_marks_the_arena_corrupted() {
    let mut arena = Arena::<BombRoot>::new(1 << 20, |mc| Ok(Lock::new(Some(Member::new(mc, mc.alloc(Bomb)?))))).unwrap();
    TRACE_PANICS.store(true, Ordering::Relaxed);
    let result = panic::catch_unwind(AssertUnwindSafe(|| arena.collect()));
    TRACE_PANICS.store(false, Ordering::Relaxed);
    assert!(result.is_err());
    assert!(arena.metrics().corrupted);
    assert!(matches!(arena.step(|_, _| Ok::<_, ()>(())), Err(StepError::Corrupted)));
}

#[test]
fn retrace_works_in_every_cycle() {
    let mut arena = pair_arena(1 << 20);
    arena.mutate(|mc, root| root.1.store(mc, Some(node(mc, 1, None).unwrap())));
    for tail in [7, 8, 9] {
        arena.mutate(|mc, root| {
            root.1.load(mc).unwrap().next.set(mc, None);
            root.0.store(mc, chain(mc, 50, Some(node(mc, tail, None).unwrap())));
        });
        arena.collect_slice(NODE);
        assert_eq!(arena.metrics().phase, Phase::Marking);
        arena.mutate(|mc, root| {
            let moved = move_tail(mc, root);
            let black = root.1.load(mc).unwrap();
            unsafe { black.next.set_unbarriered(Some(Member::new(mc, moved))) };
            mc.retrace(black);
        });
        arena.collect();
        arena.heap().check();
        arena.mutate(|mc, root| assert_eq!(last(mc, root.1.load(mc).unwrap()).value, tail));
    }
}

#[derive(Trace, Plain)]
struct Blob<const N: usize>([u64; N]);

macro_rules! blobs {
    ($mc:expr, $out:expr, $($n:literal)*) => {$({
        let b = $mc.alloc(Blob::<$n>([$n; $n])).unwrap();
        $out.push((offset($mc, b) as u32, layout::sized_size::<Blob<$n>>(), $n));
    })*};
}

#[test]
fn many_types_keep_their_own_vtables() {
    let mut arena = unit_arena(4 << 20);
    arena.mutate(|mc, _| {
        let mut out = Vec::new();
        for _ in 0..2 {
            blobs!(mc, out, 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
                33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64
                65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 1000 1022 1023 1024 2048);
        }
        for (off, size, n) in out {
            assert_eq!(mc.heap.vtable_size(off), Some(size), "Blob<{n}>");
            let first = unsafe { mc.base.as_ptr().add(off as usize + HEADER).cast::<u64>().read() };
            assert_eq!(first, n as u64);
        }
        mc.heap.check();
    });
}

struct BytesK;
impl Rooted for BytesK {
    type Of<'gc> = Member<'gc, Bytes>;
}

fn check_bytes(arena: &mut Arena<Unit>, roots: &[(Root<BytesK>, usize)]) {
    arena.mutate(|mc, _| {
        for (root, len) in roots {
            let b = mc.fetch(root).unwrap().get(mc);
            assert_eq!(b.len(), *len);
            assert!(b.items().iter().all(|&x| x == b.tag as u8));
        }
        mc.heap.check();
    });
}

#[test]
fn page_runs_fill_holes_and_exhaust_the_region() {
    let mut arena = unit_arena(REGION);
    let mut roots = Vec::new();
    let mut tag = 0u32;
    let mut alloc = |arena: &mut Arena<Unit>, len: usize| {
        tag += 1;
        let t = tag;
        arena.mutate(|mc, _| {
            let b = mc.alloc_inline(Bytes { tag: t }, len, |_| t as u8).ok()?;
            mc.root::<BytesK>(Member::new(mc, b)).ok().map(|r| (r, len))
        })
    };
    for _ in 0..40 {
        roots.push(alloc(&mut arena, 2 * PAGE - 100).unwrap());
    }
    let mut i = 0;
    roots.retain(|_| {
        i += 1;
        i % 2 == 0
    });
    arena.collect();
    check_bytes(&mut arena, &roots);
    let pages = arena.metrics().pages;
    for _ in 0..20 {
        roots.push(alloc(&mut arena, PAGE + 100).unwrap());
    }
    assert_eq!(arena.metrics().pages, pages + 40);
    roots.push(alloc(&mut arena, 3 * PAGE).unwrap());
    check_bytes(&mut arena, &roots);

    while let Some(r) = alloc(&mut arena, 5 * PAGE) {
        roots.push(r);
    }
    while let Some(r) = alloc(&mut arena, 100) {
        roots.push(r);
    }
    let m = arena.metrics();
    assert!(m.used <= m.limit);
    check_bytes(&mut arena, &roots);
    roots.clear();
    arena.collect();
    arena.heap().check();
    assert_eq!(arena.metrics().used, BASE);
}

/// Runs slices until the arena is in `phase`. The test's heap must make that phase span
/// more than one slice, or it can be skipped.
fn wait_for<R: Rootable>(arena: &mut Arena<R>, phase: Phase, work: usize) {
    for _ in 0..10_000 {
        if arena.metrics().phase == phase {
            return;
        }
        arena.collect_slice(work);
    }
    panic!("never reached {phase:?}");
}

static MID_CYCLE_DROPS: AtomicUsize = AtomicUsize::new(0);

struct Counted;

impl Drop for Counted {
    fn drop(&mut self) {
        MID_CYCLE_DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

#[derive(Trace, Plain)]
struct CountedBox<'gc> {
    host: Lock<HostRef<'gc, Counted>>,
}

struct CountedRoot;
impl Rootable for CountedRoot {
    type Root<'gc> = Lock<Option<Member<'gc, CountedBox<'gc>>>>;
}

#[test]
fn dropping_mid_cycle_frees_everything() {
    let mut expected = 0;
    for phase in [Phase::Marking, Phase::Sweeping] {
        let mut arena = Arena::<CountedRoot>::new(4 << 20, |_| Ok(Lock::new(None))).unwrap();
        arena.mutate(|mc, root| {
            for _ in 0..50 {
                let host = mc.host(Counted).unwrap();
                let b = mc.alloc(CountedBox { host: Lock::new(host) }).unwrap();
                root.store(mc, Some(b));
                mc.alloc_inline(Bytes { tag: 0 }, 9000, |_| 0).unwrap();
            }
        });
        expected += 50;
        wait_for(&mut arena, phase, 16);
        arena.mutate(|mc, _| {
            mc.host(Counted).unwrap();
        });
        expected += 1;
        arena.heap().check();
        drop(arena);
        assert_eq!(MID_CYCLE_DROPS.load(Ordering::Relaxed), expected);
    }
}

#[test]
fn panicking_fill_while_marking_or_sweeping() {
    let mut arena = pair_arena(1 << 20);
    arena.mutate(|mc, _| {
        for _ in 0..10 {
            mc.alloc_inline(Bytes { tag: 0 }, 9000, |_| 0).unwrap();
        }
    });
    black_and_white(&mut arena);
    for len in [10, 3 * PAGE] {
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            arena.mutate(|mc, _| {
                let _ = mc.alloc_inline(Bytes { tag: 0 }, len, |i| if i == 5 { panic!("fill failed") } else { 0 });
            })
        }));
        assert!(result.is_err());
        arena.heap().check();
    }
    wait_for(&mut arena, Phase::Sweeping, 1);
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        arena.mutate(|mc, _| {
            let _ = mc.alloc_inline(Bytes { tag: 0 }, 10, |i| if i == 5 { panic!("fill failed") } else { 0 });
        })
    }));
    assert!(result.is_err());
    arena.heap().check();
    arena.collect();
    arena.heap().check();
    assert!(!arena.metrics().corrupted);
}

#[derive(Trace, Plain)]
#[gc(items = ())]
struct Zs;

#[test]
fn edge_sizes() {
    assert_eq!(unit_arena(usize::MAX).metrics().limit, REGION);
    let mut arena = unit_arena(1 << 20);
    arena.mutate(|mc, _| {
        assert_eq!(mc.alloc_inline(Zs, 1000, |_| ()).unwrap().len(), 1000);
        assert!(mc.alloc_inline(Zs, usize::MAX, |_| ()).is_err());
        assert!(mc.alloc_inline(Zs, u32::MAX as usize + 1, |_| ()).is_err());
        let exact = mc.alloc_inline(Bytes { tag: 1 }, 8192 - 12, |_| 1).unwrap();
        let large = mc.alloc_inline(Bytes { tag: 2 }, 8192 - 11, |_| 2).unwrap();
        assert_eq!(offset(mc, large) % PAGE, 0);
        assert!(exact.items().iter().all(|&x| x == 1) && large.items().iter().all(|&x| x == 2));
        mc.alloc(()).unwrap();
        mc.heap.check();
    });
    // The largest small object still fits the bump page; the next size up gets a page run.
    assert_eq!(arena.metrics().live, 2 * PAGE);
}

#[derive(Trace, Plain)]
#[gc(items = u8)]
struct Obj<'gc> {
    id: i64,
    next: Lock<Option<Member<'gc, Obj<'gc>>>>,
    host: Lock<Option<Member<'gc, HostBox<'gc>>>>,
    weak: Weak<'gc, Obj<'gc>>,
}

#[derive(Trace, Plain)]
struct HostBox<'gc> {
    host: HostRef<'gc, u64>,
}

#[derive(Trace, Plain)]
#[gc(items = Lock<Option<Member<'gc, Obj<'gc>>>>)]
struct Objs<'gc>(PhantomData<&'gc ()>);

struct ObjsRoot;
impl Rootable for ObjsRoot {
    type Root<'gc> = Lock<Option<Member<'gc, Objs<'gc>>>>;
}

struct ObjK;
impl Rooted for ObjK {
    type Of<'gc> = Member<'gc, Obj<'gc>>;
}

#[derive(Clone, Copy)]
struct Model {
    next: Option<i64>,
    len: usize,
    host: bool,
    weak: Option<i64>,
}

fn reachable(objs: &HashMap<i64, Model>, from: impl IntoIterator<Item = i64>) -> HashSet<i64> {
    let mut reachable = HashSet::new();
    let mut pending: Vec<i64> = from.into_iter().collect();
    while let Some(x) = pending.pop() {
        if reachable.insert(x) {
            pending.extend(objs[&x].next);
        }
    }
    reachable
}

/// A weak reference may only ever read as its own target, and must while the target is reachable.
fn check_weak(got: Option<i64>, want: Option<i64>, live: &HashSet<i64>) {
    assert!(got.is_none() || got == want, "weak read {got:?}, expected {want:?}");
    if want.is_some_and(|w| live.contains(&w)) {
        assert_eq!(got, want, "weak ref to a reachable object was cleared");
    }
}

fn verify_obj<'gc>(
    mc: &Mutation<'gc>,
    objs: &HashMap<i64, Model>,
    live: &HashSet<i64>,
    mut cur: Option<Gc<'gc, Obj<'gc>>>,
    mut want: Option<i64>,
    depth: usize,
) {
    for _ in 0..depth {
        assert_eq!(cur.map(|o| o.id), want);
        let (Some(o), Some(id)) = (cur, want) else { return };
        let m = objs[&id];
        let items = o.items();
        assert_eq!(items.len(), m.len, "obj {id}");
        let stride = (m.len / 7).max(1);
        assert!(items.iter().enumerate().step_by(stride).all(|(i, &x)| x == (id as usize + i) as u8), "obj {id} payload");
        let host = o.host.load(mc).map(|b| *b.host.get(mc).unwrap());
        assert_eq!(host, m.host.then_some(id as u64 * 3), "obj {id} host");
        check_weak(o.weak.get(mc).map(|w| w.id), m.weak, live);
        cur = o.next.load(mc);
        want = m.next;
    }
}

#[test]
fn model_fuzz() {
    const SLOTS: usize = 16;
    let ops = if cfg!(miri) { 120 } else { 3000 };
    let mut total_ooms = 0;
    for (seed, limit) in [(1u64, 3 << 20), (2, 192 << 10), (3, 96 << 10)] {
        let mut arena = Arena::<ObjsRoot>::new(limit, |mc| {
            Ok(Lock::new(Some(Member::new(mc, mc.alloc_inline(Objs(PhantomData), SLOTS, |_| Lock::new(None))?))))
        })
        .unwrap();
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ seed.wrapping_mul(0xbf58476d1ce4e5b9));
        let mut objs: HashMap<i64, Model> = HashMap::new();
        let mut slots: [Option<i64>; SLOTS] = [None; SLOTS];
        let mut roots: Vec<(Root<ObjK>, i64)> = Vec::new();
        let (mut ooms, mut next_id) = (0, 0i64);
        for _ in 0..ops {
            let (a, b) = (rng.below(SLOTS), rng.below(SLOTS));
            let op = rng.below(16);
            let id = next_id;
            let len = match rng.below(20) {
                0 => 9000 + rng.below(30_000),
                1..=5 => 64 + rng.below(8000),
                _ => rng.below(64),
            };
            let host = rng.below(3) == 0;
            let r = if roots.is_empty() { 0 } else { rng.below(roots.len()) };
            let live = reachable(&objs, slots.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
            match op {
                10 => arena.collect_slice(1 + rng.below(20_000)),
                11 if rng.below(4) == 0 => arena.collect(),
                11 => arena.collect_minor(),
                12 => arena.set_stress(if rng.below(2) == 0 { None } else { Some(1 + rng.below(500)) }),
                13 => arena.set_evacuate_all(rng.below(3) == 0),
                8 if !roots.is_empty() => drop(roots.swap_remove(r)),
                _ => {
                    let roots_ref = &roots;
                    let result = arena.step(|mc, root| {
                        let items = root.load(mc).unwrap().items();
                        match op {
                            0..=3 => {
                                let obj = mc.alloc_inline(
                                    Obj { id, next: Lock::new(items[b].get()), host: Lock::new(None), weak: Weak::empty() },
                                    len,
                                    |i| (id as usize + i) as u8,
                                )?;
                                if host {
                                    let h = mc.host(id as u64 * 3)?;
                                    let hb = mc.alloc(HostBox { host: h })?;
                                    obj.host.store(mc, Some(hb));
                                }
                                items[a].store(mc, Some(obj));
                                Ok((None, None))
                            }
                            4 => {
                                if let Some(o) = items[a].load(mc) {
                                    o.next.set(mc, items[b].get());
                                }
                                Ok((None, None))
                            }
                            5 => {
                                items[a].set(mc, items[b].load(mc).and_then(|o| o.next.get()));
                                Ok((None, None))
                            }
                            6 => {
                                if let Some(o) = items[a].load(mc) {
                                    match items[b].load(mc) {
                                        Some(target) => o.weak.set(mc, target),
                                        None => o.weak.clear(mc),
                                    }
                                }
                                Ok((None, None))
                            }
                            7 => match items[a].get() {
                                Some(m) => mc.root::<ObjK>(m).map(|r| (Some(r), None)),
                                None => Ok((None, None)),
                            },
                            9 if !roots_ref.is_empty() => {
                                items[a].set(mc, Some(mc.fetch(&roots_ref[r].0).unwrap()));
                                Ok((None, None))
                            }
                            14 => {
                                let target = items[b].load(mc).and_then(|o| o.weak.get(mc));
                                items[a].store(mc, target);
                                Ok((None, target.map(|t| t.id)))
                            }
                            _ => {
                                items[a].set(mc, None);
                                Ok((None, None))
                            }
                        }
                    });
                    match result {
                        Ok((new_root, loaded)) => match op {
                            0..=3 => {
                                objs.insert(id, Model { next: slots[b], len, host, weak: None });
                                slots[a] = Some(id);
                                next_id += 1;
                            }
                            4 => {
                                if let Some(x) = slots[a] {
                                    objs.get_mut(&x).unwrap().next = slots[b];
                                }
                            }
                            5 => slots[a] = slots[b].and_then(|x| objs[&x].next),
                            6 => {
                                if let Some(x) = slots[a] {
                                    objs.get_mut(&x).unwrap().weak = slots[b];
                                }
                            }
                            14 => {
                                check_weak(loaded, slots[b].and_then(|x| objs[&x].weak), &live);
                                slots[a] = loaded;
                            }
                            7 => {
                                if let Some(root) = new_root {
                                    roots.push((root, slots[a].unwrap()));
                                }
                            }
                            9 if !roots.is_empty() => slots[a] = Some(roots[r].1),
                            _ => slots[a] = None,
                        },
                        Err(StepError::OutOfMemory) => ooms += 1,
                        Err(e) => panic!("step failed: {e:?}"),
                    }
                }
            }
            arena.heap().check();
            let live = reachable(&objs, slots.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
            arena.mutate(|mc, root| {
                let items = root.load(mc).unwrap().items();
                for (slot, want) in items.iter().zip(slots) {
                    verify_obj(mc, &objs, &live, slot.load(mc), want, 3);
                }
                for (root, id) in &roots {
                    verify_obj(mc, &objs, &live, Some(mc.fetch(root).unwrap().get(mc)), Some(*id), 2);
                }
            });
        }
        arena.set_stress(None);
        arena.collect();
        arena.heap().check();
        let live = reachable(&objs, slots.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
        let hosts = live.iter().filter(|x| objs[x].host).count();
        let m = arena.metrics();
        assert_eq!((m.objects, m.hosts), (1 + live.len() + hosts, hosts));
        assert!(m.collections > 0 && m.minor_collections > 0);
        eprintln!("seed {seed}: {ooms} ooms, {} + {} minor collections, {} objects", m.collections, m.minor_collections, m.objects);
        total_ooms += ooms;
    }
    assert!(total_ooms > 0, "the tight limits should hit out of memory");
}

#[test]
fn decommits_cover_only_free_os_pages() {
    for os_page in [4096, PAGE, 4 * PAGE, 16 * PAGE] {
        let _os_page = super::region::test_os_page::Override::new(Some(os_page));
        let mut arena = unit_arena(8 << 20);
        let mut rng = Rng(os_page as u64);
        let mut roots: Vec<(Root<BytesK>, usize)> = Vec::new();
        for round in 0..if cfg!(miri) { 3 } else { 30 } {
            for _ in 0..20 {
                let len = if rng.below(3) == 0 { PAGE * (1 + rng.below(3)) } else { 100 + rng.below(3000) };
                let tag = round as u32 + 1;
                let r = arena.mutate(|mc, _| {
                    let b = mc.alloc_inline(Bytes { tag }, len, |_| tag as u8).ok()?;
                    mc.root::<BytesK>(Member::new(mc, b)).ok()
                });
                roots.extend(r.map(|r| (r, len)));
            }
            roots.retain(|_| rng.below(3) != 0);
            arena.collect();
            check_bytes(&mut arena, &roots);
        }
    }
}

#[test]
fn corrupted_gcvec_len_is_bounded() {
    let mut arena = vec_arena(1 << 20);
    let len_at = arena.mutate(|mc, root| {
        let holder = root.load(mc).unwrap();
        for i in 0..8 {
            holder.items.push(mc, Some(Member::new(mc, node(mc, i, None).unwrap()))).unwrap();
        }
        offset(mc, holder) + HEADER
    });
    corrupt_u32(&arena, len_at, u32::MAX);
    arena.mutate(|mc, root| {
        let v = &root.load(mc).unwrap().items;
        assert_eq!((v.len(mc), v.capacity(mc)), (8, 8));
        assert!(v.get(mc, 1000).is_none());
        v.truncate(mc, 1000);
        assert!((0..8).all(|i| v.get(mc, i).flatten().is_some()), "truncating above the length cleared items");
        assert!(v.pop(mc).is_some());
        v.truncate(mc, 2);
        assert_eq!(v.len(mc), 2);
        corrupt_u32_mc(mc, len_at, u32::MAX);
        v.truncate(mc, 0);
        assert_eq!(v.len(mc), 0);
    });
}

fn corrupt_u32_mc(mc: &Mutation<'_>, offset: usize, value: u32) {
    unsafe { mc.base.as_ptr().add(offset).cast::<u32>().write_unaligned(value) }
}

struct U64VecRoot;
impl Rootable for U64VecRoot {
    type Root<'gc> = GcVec<'gc, u64>;
}

#[test]
fn gcvec_grows_by_less_when_doubling_does_not_fit() {
    let limit = 1 << 20;
    let mut arena = Arena::<U64VecRoot>::new(limit, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, v| {
        for i in 0..32768 {
            v.push(mc, i).unwrap();
        }
        assert_eq!(v.capacity(mc), 32768);
        while mc.limit() - mc.used() > 420 * 1024 {
            mc.alloc_inline(Bytes { tag: 0 }, PAGE - 16, |_| 0).unwrap();
        }
        v.push(mc, 32768).unwrap();
        assert_eq!(v.capacity(mc), 32769);
        assert_eq!(v.get(mc, 32768), Some(32768));
        assert_eq!(v.get(mc, 100), Some(100));
        mc.heap.check();
    });
}

#[test]
fn gcvec_growth_never_fails_when_the_needed_size_fits() {
    let fill = |arena: &mut Arena<U64VecRoot>| {
        arena.mutate(|mc, v| {
            for i in 0..2048 {
                v.push(mc, i).unwrap();
            }
            mc.used()
        })
    };
    let used = fill(&mut Arena::<U64VecRoot>::new(1 << 20, |_| Ok(GcVec::new())).unwrap());
    let mut capacities = Vec::new();
    for spare in (33_000..54_000).step_by(if cfg!(miri) { 700 } else { 100 }) {
        let mut arena = Arena::<U64VecRoot>::new(used + spare, |_| Ok(GcVec::new())).unwrap();
        fill(&mut arena);
        let mut runs = 0;
        let result = arena.step(|mc, v| {
            runs += 1;
            v.push(mc, 2048).map(|_| v.capacity(mc))
        });
        // With too little spare even the needed size doesn't fit, so the step retries. Once
        // it fits, the bigger allocation tried first must never cause a retry.
        let capacity = result.unwrap();
        if runs == 1 || !capacities.is_empty() {
            assert_eq!(runs, 1, "a fallback allocation made the step retry ({spare} bytes spare)");
            capacities.push(capacity);
        }
        arena.heap().check();
    }
    assert_eq!(capacities.first(), Some(&2049));
    assert_eq!(capacities.last(), Some(&4096));
    assert!(capacities.is_sorted() && capacities.len() > 100);
}

#[test]
fn panicking_fill_on_a_fresh_page_gives_it_back() {
    let mut arena = unit_arena(1 << 20);
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        arena.mutate(|mc, _| {
            let _ = mc.alloc_inline(Bytes { tag: 0 }, 40, |i| if i == 5 { panic!("fill failed") } else { 0 });
        })
    }));
    assert!(result.is_err());
    arena.heap().check();
    let m = arena.metrics();
    assert_eq!((m.pages, m.used), (0, BASE));
}

#[test]
fn retrace_ignores_interior_offsets() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    arena.mutate(|mc, root| {
        let black = root.1.load(mc).unwrap();
        let bits = Member::new(mc, black).to_bits().get() + 8;
        let interior = unsafe { Member::<Node<'_>>::from_bits(NonZeroU32::new(bits).unwrap()) }.get(mc);
        mc.retrace(interior);
        assert_eq!(black.value, 1);
    });
    arena.collect();
    assert!(!arena.metrics().corrupted);
}

#[test]
fn corrupting_a_black_object_is_detected_not_a_verifier_panic() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    let next_at = arena.mutate(|mc, root| {
        let black = root.1.load(mc).unwrap();
        (&black.next as *const Lock<NodeRef<'_>>).addr() - mc.base.as_ptr().addr()
    });
    corrupt_u32(&arena, next_at, 12345);
    arena.collect();
    assert!(arena.metrics().corrupted);
}

/// Runs `f` as a step and says whether it had to be retried after running out of memory.
fn retried<R: Rootable, T, E>(
    arena: &mut Arena<R>,
    mut f: impl for<'gc> FnMut(&Mutation<'gc>, &R::Root<'gc>) -> Result<T, E>,
) -> bool {
    let mut runs = 0;
    let _ = arena.step(|mc, root| {
        runs += 1;
        f(mc, root)
    });
    runs > 1
}

#[test]
fn every_phase_is_visible_with_a_tiny_slice() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| root.store(mc, chain(mc, 3, None)));
    let mut seen = Vec::new();
    arena.collect_slice(1);
    for _ in 0..100 {
        let phase = arena.metrics().phase;
        if seen.last() != Some(&phase) {
            seen.push(phase);
        }
        if phase == Phase::Idle {
            break;
        }
        arena.collect_slice(1);
    }
    assert_eq!(seen, [Phase::Marking, Phase::Sweeping, Phase::Idle]);
}

#[test]
fn pacing_keeps_up_when_most_of_the_limit_is_live() {
    let (limit, live, steps) = if cfg!(miri) { (128 << 10, 9_000, 200) } else { (1 << 20, 70_000, 2000) };
    let mut arena = Arena::<U64VecRoot>::new(limit, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, v| {
        v.reserve(mc, live).unwrap();
        for i in 0..live {
            v.push(mc, i as u64).unwrap();
        }
    });
    arena.collect();
    let before = arena.metrics().collections;
    for i in 0..steps {
        let retry = retried(&mut arena, |mc, _| mc.alloc_inline(Bytes { tag: 0 }, 2000, |_| 0).map(|_| ()));
        assert!(!retry, "step {i} ran out of memory with {:?}", arena.metrics());
    }
    let m = arena.metrics();
    assert!(m.collections + m.minor_collections > before + 10);
    arena.mutate(|mc, v| assert_eq!(v.get(mc, live - 1), Some(live as u64 - 1)));
}

#[test]
fn pacing_counts_host_values_and_roots() {
    let (hosts, roots) = if cfg!(miri) { (200, 1000) } else { (2000, 20_000) };
    let mut arena = unit_arena(1 << 20);
    for i in 0..hosts {
        assert!(!retried(&mut arena, |mc, _| mc.host([0u8; 4096]).map(|_| ())), "host step {i}");
    }
    let mut arena = node_arena(1 << 20);
    for i in 0..roots {
        let retry = retried(&mut arena, |mc, _| {
            let n = node(mc, i, None)?;
            mc.root::<NodeK>(Member::new(mc, n)).map(drop)
        });
        assert!(!retry, "root step {i}");
    }
    arena.heap().check();
}

#[test]
fn host_table_is_charged_and_shrinks() {
    let limit = 64 << 10;
    let mut arena = Arena::<HostHolder>::new(limit, |_| Ok(Lock::new(None))).unwrap();
    let made = arena.mutate(|mc, root| {
        let mut made = 0;
        while let Ok(host) = mc.host(()) {
            if made == 0 {
                root.set(mc, Some(host));
            }
            made += 1;
        }
        mc.heap.check();
        assert!(mc.used() <= limit);
        made
    });
    assert!(made > 1000 && made <= limit / 32, "{made}");
    arena.collect();
    arena.heap().check();
    assert_eq!(arena.heap().hosts.len(), 1);
    assert!(arena.heap().hosts.capacity() <= 2, "{}", arena.heap().hosts.capacity());
    for _ in 0..if cfg!(miri) { 5 } else { 50 } {
        arena.mutate(|mc, _| {
            for _ in 0..100 {
                mc.host(0u64).unwrap();
            }
        });
        arena.collect();
        arena.heap().check();
    }
    assert!(arena.heap().hosts.capacity() <= 2);
    arena.mutate(|mc, root| assert!(root.get().unwrap().get(mc).is_some()));
}

#[test]
fn stale_host_refs_miss_after_their_slot_is_reused() {
    let mut arena = Arena::<HostHolder>::new(1 << 20, |_| Ok(Lock::new(None))).unwrap();
    let stale = arena.mutate(|mc, _| mc.host(()).unwrap().to_bits_for_test());
    arena.collect();
    arena.mutate(|mc, root| {
        let fresh = mc.host(()).unwrap();
        root.set(mc, Some(fresh));
        assert_eq!(fresh.to_bits_for_test().0, stale.0, "the slot should be reused");
        assert!(HostRef::<()>::from_bits_for_test(stale).get(mc).is_none());
    });
}

#[test]
fn max_items_is_exactly_the_largest_allocatable_length() {
    fn check<T: Inline>() {
        let max = layout::max_items::<T>();
        assert!(layout::inline_size::<T>(max).unwrap() <= layout::REGION - PAGE);
        if size_of::<T::Item>() > 0 {
            assert!(layout::inline_size::<T>(max + 1).unwrap() > layout::REGION - PAGE);
        }
    }
    check::<Bytes>();
    check::<Slots<'static>>();
    check::<Array<u64>>();
    check::<Obj<'static>>();
    let mut arena = unit_arena(1 << 20);
    arena.mutate(|mc, _| {
        assert!(mc.alloc_inline(Bytes { tag: 0 }, layout::max_items::<Bytes>() + 1, |_| 0).is_err());
    });
}

struct HostHolder;
impl Rootable for HostHolder {
    type Root<'gc> = Lock<Option<HostRef<'gc, ()>>>;
}

#[test]
fn minor_collections_free_young_garbage_only() {
    let mut arena = pair_arena(4 << 20);
    arena.mutate(|mc, root| root.0.store(mc, chain(mc, 10, None)));
    arena.collect();
    arena.mutate(|mc, root| {
        for i in 0..100 {
            node(mc, i, None).unwrap();
        }
        root.1.store(mc, chain(mc, 5, None));
        root.0.load(mc).unwrap().next.set(mc, None);
    });
    arena.collect_minor();
    arena.heap().check();
    let m = arena.metrics();
    // The nine old nodes cut off from the chain wait for the next major collection.
    assert_eq!((m.objects, m.minor_collections, m.collections), (15, 1, 1));
    arena.mutate(|mc, root| {
        let young = root.1.load(mc).unwrap();
        assert!(mc.heap.is_old(offset(mc, young) as u32));
        assert_eq!(last(mc, young).value, 1000);
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, 6);
}

#[test]
fn cards_keep_young_objects_reachable_from_old_ones() {
    for len in [4, 5000] {
        let mut arena = slots_arena(4 << 20, len);
        arena.collect();
        arena.mutate(|mc, root| {
            let items = slot_items(root.load(mc).unwrap());
            items[0].store(mc, Some(node(mc, 1, None).unwrap()));
            items[len - 1].store(mc, Some(node(mc, 2, None).unwrap()));
            node(mc, 3, None).unwrap();
        });
        arena.collect_minor();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, 3, "{len} slots");
        arena.mutate(|mc, root| {
            let items = slot_items(root.load(mc).unwrap());
            assert_eq!((items[0].load(mc).unwrap().value, items[len - 1].load(mc).unwrap().value), (1, 2));
        });
    }
}

#[test]
#[should_panic(expected = "gc verify")]
fn verifier_catches_a_missing_card() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| root.store(mc, Some(node(mc, 1, None).unwrap())));
    arena.collect();
    arena.mutate(|mc, root| {
        let young = node(mc, 2, None).unwrap();
        unsafe { root.load(mc).unwrap().next.set_unbarriered(Some(Member::new(mc, young))) };
    });
    arena.collect_minor();
}

#[test]
fn retrace_covers_unbarriered_stores_into_old_objects() {
    let mut arena = slots_arena(1 << 20, 3000);
    arena.collect();
    arena.mutate(|mc, root| {
        let slots = root.load(mc).unwrap();
        for (i, slot) in slot_items(slots).iter().enumerate().step_by(97) {
            unsafe { slot.set_unbarriered(Some(Member::new(mc, node(mc, i as i64, None).unwrap()))) };
        }
        mc.retrace(slots);
    });
    arena.collect_minor();
    arena.heap().check();
    assert_eq!(arena.metrics().objects, 1 + 3000usize.div_ceil(97));
}

#[test]
fn steps_run_minor_collections_for_short_lived_data() {
    let live = if cfg!(miri) { 6_000 } else { 60_000 };
    let mut arena = Arena::<U64VecRoot>::new(4 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, v| {
        for i in 0..live {
            v.push(mc, i).unwrap();
        }
    });
    arena.collect();
    for _ in 0..if cfg!(miri) { 20 } else { 200 } {
        arena
            .step(|mc, _| {
                for _ in 0..100 {
                    mc.alloc_inline(Bytes { tag: 0 }, 1000, |_| 0)?;
                }
                Ok::<_, OutOfMemory>(())
            })
            .unwrap();
    }
    let m = arena.metrics();
    assert!(m.minor_collections >= if cfg!(miri) { 3 } else { 30 }, "{m:?}");
    assert_eq!(m.collections, 1, "{m:?}");
    arena.mutate(|mc, v| assert_eq!(v.get(mc, live as usize - 1), Some(live - 1)));
}

#[test]
fn evacuation_moves_objects_and_fixes_every_reference() {
    let mut arena = slots_arena(4 << 20, 16);
    arena.set_evacuate_all(true);
    let (before, root) = arena.mutate(|mc, root| {
        let items = slot_items(root.load(mc).unwrap());
        for (i, slot) in items.iter().enumerate() {
            slot.store(mc, chain(mc, 20 + i as i64, None));
        }
        let first = items[0].load(mc).unwrap();
        let rooted = mc.root::<NodeK>(Member::new(mc, last(mc, first))).unwrap();
        (offset(mc, first), rooted)
    });
    for round in 0..3 {
        arena.collect();
        arena.heap().check();
        assert!(!arena.metrics().corrupted);
        arena.mutate(|mc, slots| {
            let items = slot_items(slots.load(mc).unwrap());
            let first = items[0].load(mc).unwrap();
            if round == 0 {
                assert_ne!(offset(mc, first), before, "nothing moved");
            }
            for (i, slot) in items.iter().enumerate() {
                let (mut count, mut cur) = (0, slot.load(mc));
                while let Some(n) = cur {
                    assert_eq!(n.value, 1000 + 19 + i as i64 - count);
                    count += 1;
                    cur = n.next.load(mc);
                }
                assert_eq!(count, 20 + i as i64);
            }
            assert!(Gc::ptr_eq(mc.fetch(&root).unwrap().get(mc), last(mc, first)));
        });
    }
    assert_eq!(arena.metrics().objects, 1 + (20..36).sum::<usize>());
}

#[test]
fn sparse_pages_are_compacted() {
    let per_page = PAGE / NODE;
    let pages = if cfg!(miri) { 8 } else { 64 };
    // Big enough to get a page run, which is never compacted, so the references to moved
    // objects sit outside the pages being compacted.
    let mut arena = slots_arena(8 << 20, 5000);
    arena.mutate(|mc, root| {
        let items = slot_items(root.load(mc).unwrap());
        for i in 0..pages * per_page {
            let n = node(mc, i as i64, None).unwrap();
            if i % per_page == per_page / 2 {
                items[i / per_page].store(mc, Some(n));
            }
        }
    });
    arena.collect();
    assert!(arena.metrics().pages >= pages);
    arena.collect();
    arena.heap().check();
    let m = arena.metrics();
    assert!(m.pages <= 3, "{m:?}");
    arena.mutate(|mc, root| {
        for (i, slot) in slot_items(root.load(mc).unwrap())[..pages].iter().enumerate() {
            assert_eq!(slot.load(mc).unwrap().value, (i * per_page + per_page / 2) as i64);
        }
    });
}

#[test]
fn evacuation_without_room_leaves_objects_in_place() {
    let mut arena = node_arena(96 << 10);
    let made = arena.mutate(|mc, root| {
        let mut made = 0;
        while let Ok(n) = node(mc, made, root.load(mc)) {
            root.store(mc, Some(n));
            made += 1;
        }
        made
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.heap().check();
    assert!(!arena.metrics().corrupted);
    assert!(arena.step(|_, _| Ok::<_, ()>(())).is_ok());
    arena.mutate(|mc, root| assert_eq!(last(mc, root.load(mc).unwrap()).value, 0));
    assert_eq!(arena.metrics().objects, made as usize);
}

#[derive(Trace, Plain)]
struct WeakBox<'gc> {
    weak: Weak<'gc, Node<'gc>>,
}

struct WeakRoot;
impl Rootable for WeakRoot {
    type Root<'gc> = (Lock<Option<Member<'gc, WeakBox<'gc>>>>, Lock<NodeRef<'gc>>);
}

fn weak_arena() -> Arena<WeakRoot> {
    Arena::new(1 << 20, |mc| {
        let target = node(mc, 0, None)?;
        Ok((Lock::new(Some(Member::new(mc, mc.alloc(WeakBox { weak: Weak::new(mc, target) })?))), Lock::new(None)))
    })
    .unwrap()
}

fn weak_value(arena: &mut Arena<WeakRoot>) -> Option<i64> {
    arena.mutate(|mc, root| root.0.load(mc).unwrap().weak.get(mc).map(|n| n.value))
}

#[test]
fn weak_refs_clear_once_the_target_dies() {
    for evacuate in [false, true] {
        let mut arena = weak_arena();
        arena.set_evacuate_all(evacuate);
        arena.collect();
        assert_eq!((weak_value(&mut arena), arena.metrics().objects), (None, 1));

        arena.mutate(|mc, root| {
            let target = node(mc, 5, None).unwrap();
            root.0.load(mc).unwrap().weak.set(mc, target);
            root.1.store(mc, Some(target));
        });
        arena.collect();
        assert_eq!(weak_value(&mut arena), Some(5));
        arena.mutate(|mc, root| root.1.set(mc, None));
        arena.collect();
        assert_eq!((weak_value(&mut arena), arena.metrics().objects), (None, 1));
        arena.heap().check();
    }
}

#[test]
fn minor_collections_clear_weak_refs_to_young_objects() {
    let mut arena = weak_arena();
    arena.collect();
    arena.mutate(|mc, root| {
        let target = node(mc, 6, None).unwrap();
        root.0.load(mc).unwrap().weak.set(mc, target);
        root.1.store(mc, Some(target));
    });
    arena.collect_minor();
    assert_eq!(weak_value(&mut arena), Some(6));

    arena.mutate(|mc, root| {
        let target = node(mc, 7, None).unwrap();
        root.0.load(mc).unwrap().weak.set(mc, target);
    });
    arena.collect_minor();
    arena.heap().check();
    assert_eq!((weak_value(&mut arena), arena.metrics().objects), (None, 2));
}

#[test]
fn weak_refs_outside_the_arena_are_strong() {
    struct R;
    impl Rootable for R {
        type Root<'gc> = Weak<'gc, Node<'gc>>;
    }
    let mut arena = Arena::<R>::new(1 << 20, |mc| Ok(Weak::new(mc, node(mc, 3, None)?))).unwrap();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena.mutate(|mc, weak| assert_eq!(weak.get(mc).unwrap().value, 3));
}

type Entry<'gc> = Ephemeron<'gc, Node<'gc>, NodeRef<'gc>>;

#[derive(Trace, Plain)]
#[gc(items = Entry<'gc>)]
struct Entries<'gc>(PhantomData<&'gc ()>);

struct EntriesRoot;
impl Rootable for EntriesRoot {
    type Root<'gc> = (Lock<Option<Member<'gc, Entries<'gc>>>>, Lock<NodeRef<'gc>>);
}

/// Four entries in a ring, each value the next entry's key, ordered so settling them takes
/// several rounds. Only the first key is held strongly.
fn ring(minor: bool, evacuate: bool) -> Arena<EntriesRoot> {
    let mut arena = Arena::<EntriesRoot>::new(1 << 20, |_| Ok((Lock::new(None), Lock::new(None)))).unwrap();
    arena.set_evacuate_all(evacuate);
    arena.mutate(|mc, root| {
        let table = mc.alloc_inline(Entries(PhantomData), 4, |_| Entry::empty()).unwrap();
        root.0.store(mc, Some(table));
    });
    // In a minor collection the table is old, so the entries are found through its cards.
    if minor {
        arena.collect();
    }
    arena.mutate(|mc, root| {
        let [a, b, c, d] = [1, 2, 3, 4].map(|v| node(mc, v, None).unwrap());
        let m = |n| Some(Member::new(mc, n));
        let entries = root.0.load(mc).unwrap().items();
        entries[0].set(mc, c, m(d));
        entries[1].set(mc, b, m(c));
        entries[2].set(mc, a, m(b));
        entries[3].set(mc, d, m(a));
        root.1.store(mc, Some(a));
    });
    arena
}

fn entry_pair<'gc>(mc: &Mutation<'gc>, e: &Entry<'gc>) -> Option<(i64, Option<i64>)> {
    Some((e.key(mc)?.value, e.value()?.map(|v| v.get(mc).value)))
}

fn ring_values(arena: &mut Arena<EntriesRoot>) -> Vec<Option<(i64, Option<i64>)>> {
    arena.mutate(|mc, root| root.0.load(mc).unwrap().items().iter().map(|e| entry_pair(mc, e)).collect())
}

#[test]
fn ephemerons_settle_and_clear_together() {
    for (minor, evacuate) in [(false, false), (false, true), (true, false)] {
        let mut arena = ring(minor, evacuate);
        let collect = |arena: &mut Arena<EntriesRoot>| if minor { arena.collect_minor() } else { arena.collect() };
        collect(&mut arena);
        arena.heap().check();
        let full = [Some((3, Some(4))), Some((2, Some(3))), Some((1, Some(2))), Some((4, Some(1)))];
        assert_eq!(ring_values(&mut arena), full);
        assert_eq!(arena.metrics().objects, 5);

        arena.mutate(|mc, root| root.1.set(mc, None));
        // Old keys only die in a major collection.
        arena.collect();
        arena.heap().check();
        assert_eq!(ring_values(&mut arena), [None; 4]);
        assert_eq!(arena.metrics().objects, 1);
    }
}

#[test]
fn ephemeron_values_are_reachable_only_through_their_keys() {
    let mut arena = ring(false, false);
    arena.mutate(|mc, root| {
        let entries = root.0.load(mc).unwrap();
        let b = entries.items()[2].value().unwrap().unwrap().get(mc);
        root.1.store(mc, Some(b));
        entries.items()[0].set_value(mc, None);
    });
    arena.collect();
    arena.heap().check();
    // b is held, which keeps c (b's value), but c's value was cleared, so d and a are gone.
    assert_eq!(ring_values(&mut arena), [Some((3, None)), Some((2, Some(3))), None, None]);
    assert_eq!(arena.metrics().objects, 3);
}

#[test]
fn gray_overflow_is_rescanned() {
    const CHAIN: i64 = if cfg!(miri) { 0 } else { 3 };
    for len in [200, 5000] {
        let mut arena = slots_arena(4 << 20, len);
        arena.heap().set_gray_limit(2);
        arena.mutate(|mc, root| {
            for (i, slot) in slot_items(root.load(mc).unwrap()).iter().enumerate() {
                slot.store(mc, chain(mc, CHAIN, Some(node(mc, i as i64, None).unwrap())));
            }
        });
        arena.collect();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, 1 + (CHAIN as usize + 1) * len);
        arena.mutate(|mc, root| {
            let items = slot_items(root.load(mc).unwrap());
            assert!(items.iter().enumerate().all(|(i, s)| last(mc, s.load(mc).unwrap()).value == i as i64));
            for slot in items {
                slot.store(mc, Some(node(mc, -1, slot.load(mc)).unwrap()));
            }
        });
        arena.collect_minor();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, 1 + (CHAIN as usize + 2) * len);
    }
}

#[test]
fn unused_lines_of_an_allocation_run_are_freed() {
    let mut arena = node_arena(1 << 20);
    arena.mutate(|mc, root| root.store(mc, Some(node(mc, 1, None).unwrap())));
    assert_eq!(arena.metrics().live, PAGE, "a fresh page is claimed whole");
    arena.collect_slice(0);
    assert_eq!(arena.metrics().phase, Phase::Marking);
    assert_eq!(arena.metrics().live, LINE);
    arena.heap().check();
    arena.collect();
    arena.heap().check();
    arena.mutate(|mc, root| assert_eq!(root.load(mc).unwrap().value, 1));
}

#[test]
fn retrace_while_marking_leaves_the_work_to_slices() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    let tail = arena.mutate(|mc, root| {
        let tail = move_tail(mc, root);
        let black = root.1.load(mc).unwrap();
        unsafe { black.next.set_unbarriered(Some(Member::new(mc, tail))) };
        mc.retrace(black);
        offset(mc, tail) as u32
    });
    assert!(!arena.heap().is_old(tail));
    arena.collect_slice(NODE);
    assert_eq!(arena.metrics().phase, Phase::Marking);
    assert!(arena.heap().is_old(tail), "the retraced object wasn't traced incrementally");
    check_moved(&mut arena, 52);
}

#[derive(Trace, Plain)]
#[gc(items = Value<'gc>)]
struct Values<'gc>(PhantomData<&'gc ()>);

#[test]
fn panicking_init_while_marking() {
    let mut arena = pair_arena(1 << 20);
    black_and_white(&mut arena);
    let objects = arena.metrics().objects;
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        arena.mutate(|mc, _| {
            let _ = mc.alloc_inline_with(Values(PhantomData), 4, Value::NIL, |_| panic!("init failed"));
        })
    }));
    assert!(result.is_err());
    assert_eq!(arena.metrics().objects, objects);
    arena.heap().check();
    arena.collect();
    arena.heap().check();
    assert!(!arena.metrics().corrupted);
}

/// An object shrunk while marking keeps only its kept lines through the cycle.
#[test]
fn shrinking_while_marking_frees_the_tail() {
    let lines_after = |len: usize| {
        let mut arena = pair_arena(1 << 20);
        black_and_white(&mut arena);
        arena.mutate(|mc, _| {
            mc.alloc_inline_with(Bytes { tag: 0 }, len, 0, |items| {
                items[0] = 1;
                1
            })
            .unwrap();
        });
        wait_for(&mut arena, Phase::Idle, 1);
        arena.heap().check();
        arena.heap().used_lines()
    };
    assert_eq!(lines_after(4000), lines_after(1));
}

/// Warm pages that trimming leaves past the end, above pages that were given back, are
/// still the first reused.
#[test]
fn warm_pages_past_a_trimmed_gap_get_reused() {
    let mut arena = unit_arena(512 << 10);
    assert_eq!(arena.heap().warm_pages(), (0, 4));
    let alloc = |arena: &mut Arena<Unit>, len: usize| {
        arena.mutate(|mc, _| {
            let b = mc.alloc_inline(Bytes { tag: 0 }, len, |_| 0).unwrap();
            mc.root::<BytesK>(Member::new(mc, b)).unwrap()
        })
    };
    let (one, two) = (PAGE - 16, PAGE + 100);
    // Pages: a, then b over two, then c over three.
    let a = alloc(&mut arena, one);
    let b = alloc(&mut arena, two);
    let c: Vec<_> = (0..3).map(|_| alloc(&mut arena, one)).collect();
    assert_eq!(arena.heap().page_count(), 6);
    drop((a, c));
    arena.collect();
    assert_eq!((arena.heap().warm_pages().0, arena.heap().page_count()), (4, 3));
    // No warm room is left, so b's pages are given back, and the table trims to nothing.
    drop(b);
    arena.collect();
    assert_eq!((arena.heap().warm_pages().0, arena.heap().page_count()), (4, 0));
    let mut kept = Vec::new();
    for warm in (0..4).rev() {
        kept.push(alloc(&mut arena, one));
        assert_eq!(arena.heap().warm_pages().0, warm, "a new page wasn't a warm one");
        arena.heap().check();
    }
}

/// With OS pages bigger than ours, each OS page of a freed run is warm or given back whole.
#[test]
fn warm_pages_leave_no_os_page_half_kept() {
    for os_page in [PAGE, 4 * PAGE] {
        let _os_page = super::region::test_os_page::Override::new(Some(os_page));
        let mut arena = unit_arena(512 << 10);
        assert_eq!(arena.heap().warm_pages(), (0, 4));
        let big = arena.mutate(|mc, _| {
            let b = mc.alloc_inline(Bytes { tag: 0 }, 5 * PAGE + 100, |_| 0).unwrap();
            mc.root::<BytesK>(Member::new(mc, b)).unwrap()
        });
        assert_eq!(arena.heap().page_count(), 6);
        drop(big);
        arena.collect();
        arena.heap().check();
        assert_eq!(arena.heap().stranded_pages(), 0, "OS pages of {os_page} bytes");
        assert!(arena.heap().warm_pages().0 > 0);
    }
}

/// Pages freed one at a time leave none committed and unaccounted for, whichever order they
/// go in and wherever the warm quota runs out.
#[test]
fn single_page_frees_strand_nothing() {
    for os_page in [PAGE, 2 * PAGE, 4 * PAGE] {
        for reverse in [false, true] {
            let _os_page = super::region::test_os_page::Override::new(Some(os_page));
            let mut arena = unit_arena(512 << 10);
            let mut roots: Vec<_> = (0..12)
                .map(|_| {
                    arena.mutate(|mc, _| {
                        let b = mc.alloc_inline(Bytes { tag: 0 }, PAGE - 16, |_| 0).unwrap();
                        mc.root::<BytesK>(Member::new(mc, b)).unwrap()
                    })
                })
                .collect();
            assert_eq!(arena.heap().page_count(), 12);
            if reverse {
                roots.reverse();
            }
            while let Some(root) = roots.pop() {
                drop(root);
                arena.collect();
                arena.heap().check();
                let (warm, limit) = arena.heap().warm_pages();
                assert!(warm <= limit);
                assert_eq!(arena.heap().stranded_pages(), 0, "OS pages of {os_page} bytes, {} left", roots.len());
            }
        }
    }
}
