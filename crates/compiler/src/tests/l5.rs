use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_vm::Intrinsic::{Add, Cons, Eq};
use ragwort_vm::Request;

use std::vec::Vec;

use ragwort_alloc::{Arena as Trees, CollectIn};

use super::*;
use crate::{Core, Lambda, Place, to_l4};

fn q<'gc>(n: i64) -> Core<'gc> {
    Core::Quote(Value::fixnum(n).unwrap())
}

fn var<'gc>(v: u32) -> Core<'gc> {
    Core::Ref(Place::Local(Var(v)))
}

/// A module variable, whose value the compiler can't know.
fn slot<'gc>(slot: u32) -> Core<'gc> {
    Core::Ref(Place::Slot { slot, checked: false })
}

fn prim<'gc>(prim: Prim, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::Intrinsic(prim, args)
}

fn add<'gc>(a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    prim(Prim::Intrinsic(Add), vec![a, b])
}

fn when<'gc>(test: Core<'gc>, then: Core<'gc>, other: Core<'gc>) -> Core<'gc> {
    Core::If(Box::new(test), Box::new(then), Box::new(other))
}

fn let_<'gc>(binds: Vec<(u32, Core<'gc>)>, body: Core<'gc>) -> Core<'gc> {
    Core::Let(binds.into_iter().map(|(v, e)| (Var(v), e)).collect(), Box::new(body))
}

fn letrec<'gc>(binds: Vec<(u32, Core<'gc>)>, body: Core<'gc>) -> Core<'gc> {
    Core::Letrec(binds.into_iter().map(|(v, e)| (Var(v), e)).collect(), Box::new(body))
}

/// `a`, then `b`, with `a`'s value bound to `v`, which nothing reads.
fn seq<'gc>(v: u32, a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    let_(vec![(v, a)], b)
}

fn lambda<'gc>(id: u32, params: &[u32], body: Core<'gc>) -> Core<'gc> {
    Core::Lambda(Lambda { id, params: params.iter().map(|&v| Var(v)).collect(), optional: 0, rest: None, body: Box::new(body) })
}

fn app<'gc>(f: Core<'gc>, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::App(Box::new(f), args)
}

fn set<'gc>(v: u32, value: Core<'gc>) -> Core<'gc> {
    Core::Set(Place::Local(Var(v)), Box::new(value))
}

/// The L5 that what `build` makes lowers to, checked.
fn l5_of(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> String {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let trees = ragwort_alloc::Arena::new();
        let f = lower(&trees, &to_l4(mc, &trees, &build(mc)).unwrap()).unwrap();
        verify(&f).unwrap_or_else(|e| panic!("{e}\n{f}"));
        f.to_string()
    })
}

/// (let ((total s0)) (let loop ((i 10)) (if (eq? i 0) total (begin (set! total (+ total i)) (loop (+ i -1))))))
fn summed<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let step = seq(3, set(0, add(var(0), var(2))), app(var(1), vec![add(var(2), q(-1))]));
    let loop_ = lambda(0, &[2], when(prim(Prim::Intrinsic(Eq), vec![var(2), q(0)]), var(0), step));
    let_(vec![(0, slot(0))], letrec(vec![(1, loop_)], app(var(1), vec![q(10)])))
}

/// (let ((x 1)) (if s0 (set! x 2) 5) (+ x 1))
fn merged<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let_(vec![(0, q(1))], seq(1, when(slot(0), set(0, q(2)), q(5)), add(var(0), q(1))))
}

/// (+ 1 (let loop ((i s0)) (if (eq? i 0) 10 (loop (+ i -1)))))
fn inner_loop<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let loop_ = lambda(1, &[1], when(prim(Prim::Intrinsic(Eq), vec![var(1), q(0)]), q(10), app(var(0), vec![add(var(1), q(-1))])));
    add(q(1), letrec(vec![(0, loop_)], app(var(0), vec![slot(0)])))
}

/// (let ((x s0)) (letrec ((even (lambda (n) (if (eq? n 0) x (odd (+ n -1))))) (odd (lambda (n) (even (+ n -1))))) (cons even odd)))
fn peers<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let even = lambda(2, &[3], when(prim(Prim::Intrinsic(Eq), vec![var(3), q(0)]), var(0), app(var(2), vec![add(var(3), q(-1))])));
    let odd = lambda(3, &[4], app(var(1), vec![add(var(4), q(-1))]));
    let_(vec![(0, slot(0))], letrec(vec![(1, even), (2, odd)], prim(Prim::Intrinsic(Cons), vec![var(1), var(2)])))
}

/// (let ((n 0)) (+ (let loop ((i s0)) (if (eq? i 0) n (begin (when s1 (set! n (+ n 1))) (loop (+ i -1))))) n))
fn counted<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let step = seq(3, when(slot(1), set(0, add(var(0), q(1))), q(0)), app(var(1), vec![add(var(2), q(-1))]));
    let loop_ = lambda(4, &[2], when(prim(Prim::Intrinsic(Eq), vec![var(2), q(0)]), var(0), step));
    let_(vec![(0, q(0))], add(letrec(vec![(1, loop_)], app(var(1), vec![slot(0)])), var(0)))
}

/// (begin (s0 (call/cc s1)) (call/cc s2))
fn calls<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let call = |s| prim(Prim::Request(Request::CallCc), vec![slot(s)]);
    seq(0, app(slot(0), vec![call(1)]), call(2))
}

#[test]
fn lowers_to_blocks_taking_what_paths_meet_with() {
    // `total` goes round the loop as a parameter of its block.
    assert_eq!(l5_of(summed), "\
function () closure v0:
b0:
  v1 = load-slot 0
  v2 = 10
  jump b1(v2 v1)
b1(v3 v4):
  v5 = 0
  v6 = eq? v3 v5
  branch v6 b2 b3
b2:
  return v4
b3:
  v7 = + v4 v3
  v8 = -1
  v9 = + v3 v8
  jump b1(v9 v7)
");
    // The ways out of the `if` meet with what each gives `x`.
    assert_eq!(l5_of(merged), "\
function () closure v0:
b0:
  v1 = 1
  v2 = load-slot 0
  branch v2 b1 b2
b1:
  v3 = 2
  v4 = #<void>
  jump b3(v4 v3)
b2:
  v5 = 5
  jump b3(v5 v1)
b3(v6 v7):
  v8 = 1
  v9 = + v7 v8
  return v9
");
    // A loop in a value's place goes on to a block taking its value.
    assert_eq!(l5_of(inner_loop), "\
function () closure v0:
b0:
  v1 = load-slot 0
  jump b1(v1)
b1(v2):
  v3 = 0
  v4 = eq? v2 v3
  branch v4 b2 b3
b2:
  v5 = 10
  jump b4(v5)
b3:
  v6 = -1
  v7 = + v2 v6
  jump b1(v7)
b4(v8):
  v9 = 1
  v10 = + v8 v9
  return v10
");
    // Closures made together capture each other.
    assert_eq!(l5_of(peers), "\
function () closure v0:
b0:
  v1 = load-slot 0
  v2 v3 = closures [2 v1 v3] [3 v2]
  v4 = cons v2 v3
  return v4
function 2 (v1) closure v0:
b0:
  v2 = 0
  v3 = eq? v1 v2
  branch v3 b1 b2
b1:
  v4 = upvalue 0
  return v4
b2:
  v5 = upvalue 1
  v6 = -1
  v7 = + v1 v6
  tail-call v5 v7
function 3 (v1) closure v0:
b0:
  v2 = upvalue 0
  v3 = -1
  v4 = + v1 v3
  tail-call v2 v4
");
    // An assigned variable goes round a loop, through an `if`, and out with the loop's value.
    assert_eq!(l5_of(counted), "\
function () closure v0:
b0:
  v1 = 0
  v2 = load-slot 0
  jump b1(v2 v1)
b1(v3 v4):
  v5 = 0
  v6 = eq? v3 v5
  branch v6 b2 b3
b2:
  jump b7(v4 v4)
b3:
  v7 = load-slot 1
  branch v7 b4 b5
b4:
  v8 = 1
  v9 = + v4 v8
  v10 = #<void>
  jump b6(v10 v9)
b5:
  v11 = 0
  jump b6(v11 v4)
b6(v12 v13):
  v14 = -1
  v15 = + v3 v14
  jump b1(v15 v13)
b7(v16 v17):
  v18 = + v16 v17
  return v18
");
    // call/cc as an argument is a call, and in tail position a tail request.
    assert_eq!(l5_of(calls), "\
function () closure v0:
b0:
  v1 = load-slot 0
  v2 = load-slot 1
  v3 = call/cc v2
  v4 = call v1 v3
  v5 = load-slot 2
  tail call/cc v5
");
}

fn function<'a, 'gc>(arena: &'a Trees, values: u32, blocks: Vec<BlockData<'a, 'gc>>) -> Function<'a, 'gc> {
    let blocks = blocks.into_iter().collect_in(arena);
    Function { id: None, this: Val(0), params: arena.vec(), optional: 0, rest: None, upvalues: 0, blocks, values }
}

fn block<'a, 'gc>(arena: &'a Trees, params: &[u32], insts: Vec<Inst<'a, 'gc>>, end: End<'a>) -> BlockData<'a, 'gc> {
    BlockData { params: params.iter().map(|&v| Val(v)).collect_in(arena), insts: insts.into_iter().collect_in(arena), end }
}

#[test]
fn the_verifier_finds_what_is_malformed() {
    let trees = Trees::new();
    let a = &trees;
    let vals = |vs: &[Val]| vs.iter().copied().collect_in(a);
    let one = || Inst::Const(Val(1), Value::fixnum(1).unwrap());
    let ok = function(a, 2, vec![block(a, &[], vec![one()], End::Return(Val(1)))]);
    assert_eq!(verify(&ok), Ok(()));
    let check = |f: Function<'_, '_>| verify(&f).unwrap_err();
    assert_eq!(check(function(a, 2, vec![block(a, &[], vec![], End::Return(Val(1)))])), "v1, used in b0, isn't defined");
    assert_eq!(check(function(a, 2, vec![block(a, &[], vec![one(), one()], End::Return(Val(1)))])), "v1 is defined twice");
    assert_eq!(check(function(a, 1, vec![block(a, &[], vec![one()], End::Return(Val(0)))])), "v1 is past the function's values");
    let used_first = vec![Inst::Prim { dst: Val(2), prim: Prim::Intrinsic(Add), args: vals(&[Val(1), Val(1)]), spread: false }, one()];
    assert_eq!(check(function(a, 3, vec![block(a, &[], used_first, End::Return(Val(2)))])), "v1, used in b0, isn't defined on every way there");
    // b0 branches to b1 and b2, which both go to b3; v2 is defined only in b1.
    let diamond = |returned: u32| {
        let two = Inst::Const(Val(2), Value::fixnum(2).unwrap());
        function(a, 3, vec![
            block(a, &[], vec![one()], End::Branch { test: Val(1), then: Block(1), other: Block(2) }),
            block(a, &[], vec![two], End::Jump(Block(3), vals(&[]))),
            block(a, &[], vec![], End::Jump(Block(3), vals(&[]))),
            block(a, &[], vec![], End::Return(Val(returned))),
        ])
    };
    assert_eq!(verify(&diamond(1)), Ok(()));
    assert_eq!(check(diamond(2)), "v2, used in b3, isn't defined on every way there");
    let jumps = |args: Vec<Val>| function(a, 3, vec![block(a, &[], vec![one()], End::Jump(Block(1), vals(&args))), block(a, &[2], vec![], End::Return(Val(2)))]);
    assert_eq!(verify(&jumps(vec![Val(1)])), Ok(()));
    assert_eq!(check(jumps(vec![])), "b0 jumps to b1 with 0 values, not 1");
    let branch = function(a, 3, vec![
        block(a, &[], vec![one()], End::Branch { test: Val(1), then: Block(1), other: Block(1) }),
        block(a, &[2], vec![], End::Return(Val(2))),
    ]);
    assert_eq!(check(branch), "b0 branches to b1, which takes parameters");
    let unreached = function(a, 2, vec![block(a, &[], vec![one()], End::Return(Val(1))), block(a, &[], vec![], End::Return(Val(1)))]);
    assert_eq!(check(unreached), "b1 can't be reached");
    let entry = function(a, 2, vec![block(a, &[], vec![one()], End::Jump(Block(0), vals(&[])))]);
    assert_eq!(check(entry), "b0 goes to the entry");
    let upvalue = function(a, 2, vec![block(a, &[], vec![Inst::Upvalue(Val(1), 0)], End::Return(Val(1)))]);
    assert_eq!(check(upvalue), "b0 loads upvalue 0 of 0");
}
