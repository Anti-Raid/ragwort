use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_vm::Intrinsic::{Add, Cons, Eq, TableRef, TableSet};
use ragwort_vm::frame::MAX_PARAMS;

use std::vec::Vec;

use super::*;
use crate::{Core, Lambda, Place, Var, to_l5};

fn q<'gc>(n: i64) -> Core<'gc> {
    Core::Quote(Value::fixnum(n).unwrap())
}

fn var<'gc>(v: u32) -> Core<'gc> {
    Core::Ref(Place::Local(Var(v)))
}

/// Builds a module-variable reference whose value is unknown at compile time.
fn slot<'gc>(slot: u32) -> Core<'gc> {
    Core::Ref(Place::Slot { slot, checked: false })
}

fn prim<'gc>(intrinsic: Intrinsic, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::Intrinsic(Prim::Intrinsic(intrinsic), args, None)
}

fn when<'gc>(test: Core<'gc>, then: Core<'gc>, other: Core<'gc>) -> Core<'gc> {
    Core::If(Box::new(test), Box::new(then), Box::new(other))
}

fn lambda<'gc>(id: u32, params: &[u32], body: Core<'gc>) -> Core<'gc> {
    Core::Lambda(Lambda { id, params: params.iter().map(|&v| Var(v)).collect(), optional: 0, rest: None, body: Box::new(body), name: None, at: None })
}

fn app<'gc>(f: Core<'gc>, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::App(Box::new(f), args, None)
}

/// Lowers the expression from `build` to L5, selects the instructions of each function, and returns their text. The top-level function comes last, as in the program.
fn l6_of(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>, near: bool) -> String {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let trees = ragwort_alloc::Arena::new();
        let program = to_l5(mc, &trees, &build(mc), &mut crate::ir::Origins::default(), None, None, &mut None).unwrap();
        let mut text = String::new();
        for function in &program.functions {
            let scratch = ragwort_alloc::Arena::new();
            text.push_str(&select(&scratch, function, near).to_string());
        }
        text
    })
}

/// (let loop ((i s0)) (if (eq? i 0) 10 (loop (+ i -1))))
fn counting<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
    let loop_ = lambda(1, &[1], when(prim(Eq, vec![var(1), q(0)]), q(10), app(var(0), vec![prim(Add, vec![var(1), q(-1)])])));
    Core::Letrec(vec![(Var(0), loop_)], Box::new(app(var(0), vec![slot(0)])))
}

#[test]
fn a_constant_addend_and_a_test_before_a_branch_join_their_instructions() {
    // The addend -1 becomes an immediate operand, so nothing reads its constant. The test `eq?` is fused into the branch, so its result has no instruction of its own.
    // The loop is laid out with its body after the test, and the branch jumps out of the loop when the test is true.
    assert_eq!(l6_of(counting, true), "\
function () order b0 b1 b3 b2:
b0:
  v1 = load-slot 0
  jump b1(v1)
b1(v2):
  v3 = 0
  branch-on eq? v2 v3 b2 b3, jumps if true
b2:
  v5 = 10
  return v5
b3:
  v6 = -1 (unread)
  v7 = add-imm v2 -1
  jump b1(v7)
");
    // A function too long for fused branches keeps the test as an instruction, and branches on its result.
    assert_eq!(l6_of(counting, false), "\
function () order b0 b1 b2 b3:
b0:
  v1 = load-slot 0
  jump b1(v1)
b1(v2):
  v3 = 0
  v4 = eq? v2 v3
  branch v4 b2 b3
b2:
  v5 = 10
  return v5
b3:
  v6 = -1 (unread)
  v7 = add-imm v2 -1
  jump b1(v7)
");
}

#[test]
fn an_intrinsic_whose_result_is_returned_joins_the_return() {
    // (lambda (a b) (cons a b)), and the top-level code that makes the closure.
    assert_eq!(l6_of(|_| lambda(0, &[0, 1], prim(Cons, vec![var(0), var(1)])), true), "\
function 0 (v1 v2) order b0:
b0:
  return-of cons v1 v2
function () order b0:
b0:
  v1 = closures [fn0]
  return v1
");
}

#[test]
fn table_accesses_with_constant_keys_are_numbered_for_hints() {
    // (begin (table-set! s0 7 s1) (cons (table-ref s0 7 0) (cons (table-ref s0 7 #f) (table-ref s0 s1 0)))): the three accesses with the constant key 7 get hints, and the one with a key read from a variable does not.
    // A hinted access does not read its key, so the constant 7 is not loaded. The read whose default is #f does not read its default either.
    fn tables<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let rest = prim(Cons, vec![prim(TableRef, vec![slot(0), q(7), Core::Quote(Value::FALSE)]), prim(TableRef, vec![slot(0), slot(1), q(0)])]);
        let read = prim(Cons, vec![prim(TableRef, vec![slot(0), q(7), q(0)]), rest]);
        Core::Let(vec![(Var(0), prim(TableSet, vec![slot(0), q(7), slot(1)]))], Box::new(read))
    }
    assert_eq!(l6_of(tables, true), "\
function () order b0, 3 hints:
b0:
  v1 = load-slot 0
  v2 = 7 (unread)
  v3 = load-slot 1
  v4 = table-set-hinted v1 v3 key 7 hint 0 (unread)
  v5 = load-slot 0
  v6 = 7 (unread)
  v7 = 0
  v8 = table-ref-hinted v5 v7 key 7 hint 1
  v9 = load-slot 0
  v10 = 7 (unread)
  v11 = #f (unread)
  v12 = table-ref-hinted v9 key 7 hint 2
  v13 = load-slot 0
  v14 = load-slot 1
  v15 = 0
  v16 = table-ref v13 v14 v15
  v17 = cons v12 v16
  return-of cons v8 v17
");
}

#[test]
fn parameters_past_the_argument_registers_are_unpacked() {
    // A function with three more parameters than there are argument registers: the last register carries the last four as a list.
    let count = u32::from(MAX_PARAMS) + 3;
    let params: Vec<u32> = (0..count).collect();
    let text = l6_of(|_| lambda(0, &params, var(count - 1)), true);
    let unpacked: Vec<String> = (u32::from(MAX_PARAMS)..=count).map(|value| format!("v{value}")).collect();
    assert!(text.contains(&format!(", unpacks {}:\n", unpacked.join(" "))), "{text}");
    let fits: Vec<u32> = (0..u32::from(MAX_PARAMS)).collect();
    assert!(!l6_of(|_| lambda(0, &fits, var(0)), true).contains("unpacks"));
}
