use ragwort_types::gc::{Arena, Mutation, Segment, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};
use ragwort_types::constant::Constants;
use ragwort_types::vector::Vectors;

use super::*;
use crate::objects::{BoxFields, MultiValueFields};
use crate::op::Fuel;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

/// `op.step(cx)` out of line: `step` inlines every intrinsic's body, and a debug build gives each
/// inlined copy its own stack, so a test that steps many ops inline overflows the thread's stack.
#[inline(never)]
fn step<'gc>(op: Op, cx: &mut Context<'_, 'gc>) -> Result<Control, Fault> {
    op.step(cx)
}

#[test]
fn steps_run_against_the_frame() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let constants = Constants::of(vectors.immutable_from_slice(&[fix(7)]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[Value::TRUE]).unwrap().items(mc);
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };

        assert_eq!(step(Op::LoadConst { dst: 0, index: 0 }, &mut cx), Ok(Control::Next));
        assert_eq!(step(Op::Move { dst: 1, src: 0 }, &mut cx), Ok(Control::Next));
        assert_eq!(frame.get(1), fix(7));
        frame.set(2, fix(9));
        assert_eq!(step(Op::Move2 { dst1: 1, src1: 2, dst2: 2, src2: 1 }, &mut cx), Ok(Control::Next));
        assert_eq!((frame.get(1), frame.get(2)), (fix(9), fix(7)));
        assert_eq!(step(Op::Move { dst: 1, src: 0 }, &mut cx), Ok(Control::Next));

        frame.set(2, Value::FALSE);
        assert_eq!(step(Op::JumpIfFalse { test: 1, offset: 5 }, &mut cx), Ok(Control::Next));
        assert_eq!(step(Op::JumpIfFalse { test: 2, offset: -3 }, &mut cx), Ok(Control::Jump(-3)));
        assert_eq!(step(Op::Jump { offset: 9 }, &mut cx), Ok(Control::Jump(9)));
        assert_eq!(
            step(Op::BranchIntrinsic1 { a: 2, intrinsic: Intrinsic::IsBoolean, branch_if: true, offset: 4 }, &mut cx),
            Ok(Control::Jump(4))
        );
        assert_eq!(
            step(Op::BranchIntrinsic1 { a: 2, intrinsic: Intrinsic::IsBoolean, branch_if: false, offset: 4 }, &mut cx),
            Ok(Control::Next)
        );
        assert_eq!(
            step(Op::BranchIntrinsic2 { a: 0, b: 1, intrinsic: Intrinsic::Eq, branch_if: true, offset: -2 }, &mut cx),
            Ok(Control::Jump(-2))
        );
        assert_eq!(
            step(Op::CallIntrinsic2 { dst: 4, a: 0, b: 1, intrinsic: Intrinsic::Add }, &mut cx),
            Ok(Control::Next)
        );
        assert_eq!(frame.get(4), fix(14));
        assert_eq!(
            step(Op::CallIntrinsic1 { dst: 5, a: 4, intrinsic: Intrinsic::Sub }, &mut cx),
            Ok(Control::Next)
        );
        assert_eq!(frame.get(5), fix(-14));
        assert_eq!(
            step(Op::CallIntrinsic3 { dst: 6, a: 0, b: 1, c: 4, intrinsic: Intrinsic::Add }, &mut cx),
            Ok(Control::Next)
        );
        assert_eq!(frame.get(6), fix(28));
        // `AddImm`: fixnums in place, past the fixnum edge by the generic add, and faulting on
        // non-numbers.
        assert_eq!(step(Op::AddImm { dst: 7, a: 4, imm: -20 }, &mut cx), Ok(Control::Next));
        assert_eq!(frame.get(7), fix(-6));
        assert_eq!(step(Op::AddImm { dst: 7, a: 7, imm: i16::MAX }, &mut cx), Ok(Control::Next));
        assert_eq!(frame.get(7), fix(i64::from(i16::MAX) - 6));
        frame.set(8, fix(Value::MAX_FIXNUM));
        assert_eq!(step(Op::AddImm { dst: 9, a: 8, imm: 1 }, &mut cx), Ok(Control::Next));
        assert!(frame.get(9).as_fixnum().is_none() && ragwort_types::num::Nums::new(mc).number(frame.get(9)).is_some());
        assert_eq!(step(Op::AddImm { dst: 9, a: 9, imm: -1 }, &mut cx), Ok(Control::Next));
        assert_eq!(frame.get(9), fix(Value::MAX_FIXNUM));
        frame.set(10, Value::TRUE);
        assert_eq!(step(Op::AddImm { dst: 11, a: 10, imm: 1 }, &mut cx), Err(Fault::WrongType));

        step(Op::LoadUpvalue { dst: 3, index: 0 }, &mut cx).unwrap();
        assert_eq!(frame.get(3), Value::TRUE);

        assert_eq!(step(Op::Return { src: 0 }, &mut cx), Ok(Control::Return));
        step(Op::LoadAcc { dst: 7 }, &mut cx).unwrap();
        assert_eq!((cx.acc, frame.get(7)), (fix(7), fix(7)));

        assert_eq!(step(Op::Call { base: 8, args: 2 }, &mut cx), Ok(Control::Call { base: 8, args: 2 }));
        let request = Op::TailCallRequest { base: 8, args: 1, request: Request::Abort };
        assert_eq!(step(request, &mut cx), Ok(Control::TailCallRequest { base: 8, args: 1, request: Request::Abort, spread: false }));
    });
}

#[test]
fn malformed_bytecode_faults() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let constants = Constants::of(vectors.immutable_from_slice(&[]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[]).unwrap().items(mc);
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };
        frame.set(0, fix(1));
        let requests = [
            Op::CallRequest { base: 1, args: 1, request: Request::WithMark },
            Op::CallRead { base: 1, args: 1, read: Read::MarkValue },
            Op::Read1 { dst: 1, a: 0, read: Read::FrameMark },
            Op::Read2 { dst: 1, a: 0, b: 0, read: Read::Running },
            Op::TailCallRequest { base: 1, args: 3, request: Request::Capture },
            Op::CallRequest { base: 1, args: 1, request: Request::Apply },
            Op::CallIntrinsic1 { dst: 1, a: 0, intrinsic: Intrinsic::Cons },
            Op::CallIntrinsic2 { dst: 1, a: 0, b: 0, intrinsic: Intrinsic::Car },
            Op::CallIntrinsic3 { dst: 1, a: 0, b: 0, c: 0, intrinsic: Intrinsic::Cons },
            Op::BranchIntrinsic1 { a: 0, intrinsic: Intrinsic::Cons, branch_if: true, offset: 1 },
            Op::BranchIntrinsic2 { a: 0, b: 0, intrinsic: Intrinsic::Car, branch_if: true, offset: 1 },
        ];
        for op in [Op::LoadConst { dst: 1, index: 0 }, Op::LoadUpvalue { dst: 1, index: 0 }].into_iter().chain(requests) {
            assert_eq!(step(op, &mut cx), Err(Fault::Malformed), "{op:?}");
        }
    });
}

/// Code that does nothing, whose closures capture `captures`.
fn code<'gc>(mc: &Mutation<'gc>, captures: &[Capture]) -> Value<'gc> {
    let ops = mc.frozen(Box::from([Op::Return { src: 0 }])).unwrap();
    let empty = Vectors::new(mc).immutable_from_slice(&[]).unwrap().value(mc);
    Value::object(mc, objects::Bytecode::new(mc, ops, empty, mc.frozen(Box::from(captures)).unwrap(), 0, None).unwrap())
}

#[test]
fn closures_capture_registers_upvalues_and_each_other() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let even = code(mc, &[Capture::Register(0), Capture::Upvalue(0), Capture::Register(2)]);
        let odd = code(mc, &[Capture::Register(1)]);
        let stray = code(mc, &[Capture::Upvalue(9)]);
        let constants = Constants::of(vectors.immutable_from_slice(&[fix(7), even, odd, stray]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[fix(11)]).unwrap().items(mc);
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };

        frame.set(0, fix(5));
        assert_eq!(step(Op::NewClosure { dst: 1, count: 2, code: 1 }, &mut cx), Ok(Control::Next));
        let items = |r: u8| {
            let upvalues = frame.get(r).downcast::<objects::Closure>(mc).unwrap().items(mc);
            (0..upvalues.len()).map(|i| upvalues.get(i)).collect::<Vec<_>>()
        };
        assert_eq!(items(1), [fix(5), fix(11), frame.get(2)]);
        assert_eq!(items(2), [frame.get(1)]);

        for op in [
            Op::NewClosure { dst: 1, count: 1, code: 0 },
            Op::NewClosure { dst: 1, count: 1, code: 3 },
            Op::NewClosure { dst: 255, count: 2, code: 1 },
            Op::NewClosure { dst: 1, count: 2, code: u32::MAX },
        ] {
            assert_eq!(step(op, &mut cx), Err(Fault::Malformed), "{op:?}");
        }
    });
}

/// Runs `f` against a fresh frame with no constants or upvalues.
fn with_frame(f: impl for<'s, 'gc> FnOnce(&mut Context<'s, 'gc>)) {
    let mut arena = Arena::new(1 << 26, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let constants = Constants::of(vectors.immutable_from_slice(&[]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[]).unwrap().items(mc);
        f(&mut Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } });
    });
}

#[test]
fn intrinsics_run_in_place() {
    with_frame(|cx| {
        let (mc, frame) = (cx.mc, cx.frame);
        let call = |cx: &mut Context<'_, '_>, base, args, intrinsic| Op::CallIntrinsic { base, args, intrinsic }.step(cx);
        (0..3).for_each(|i| frame.set(10 + i, fix(i64::from(i) + 1)));
        assert_eq!(call(cx, 10, 3, Intrinsic::Add), Ok(Control::Next));
        assert_eq!(cx.acc, fix(6));
        assert_eq!(call(cx, 10, 0, Intrinsic::Add), Ok(Control::Next));
        assert_eq!(cx.acc, fix(0));

        frame.set(20, fix(Value::MAX_FIXNUM));
        frame.set(21, fix(1));
        call(cx, 20, 2, Intrinsic::Add).unwrap();
        assert!(cx.acc.as_fixnum().is_none() && ragwort_types::num::Nums::new(mc).number(cx.acc).is_some());
        frame.set(21, Value::TRUE);
        assert_eq!(call(cx, 20, 2, Intrinsic::Add), Err(Fault::WrongType));

        call(cx, 10, 2, Intrinsic::Cons).unwrap();
        let pair = Pair::of(cx.acc).unwrap();
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(1), fix(2)));
        frame.set(30, cx.acc);
        call(cx, 30, 1, Intrinsic::Car).unwrap();
        assert_eq!(cx.acc, fix(1));
        call(cx, 30, 1, Intrinsic::Cdr).unwrap();
        assert_eq!(cx.acc, fix(2));
        call(cx, 30, 1, Intrinsic::IsPair).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        assert_eq!(call(cx, 10, 1, Intrinsic::Car), Err(Fault::WrongType));

        frame.set(31, Value::NIL);
        call(cx, 31, 1, Intrinsic::IsNull).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        call(cx, 30, 2, Intrinsic::Eq).unwrap();
        assert_eq!(cx.acc, Value::FALSE);
        frame.set(31, frame.get(30));
        call(cx, 30, 2, Intrinsic::Eq).unwrap();
        assert_eq!(cx.acc, Value::TRUE);

        call(cx, 10, 1, Intrinsic::MakeBox).unwrap();
        frame.set(25, cx.acc);
        frame.set(26, Value::TRUE);
        call(cx, 25, 2, Intrinsic::SetBox).unwrap();
        assert_eq!(cx.acc, Value::VOID);
        call(cx, 25, 1, Intrinsic::Unbox).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        assert_eq!(call(cx, 26, 1, Intrinsic::Unbox), Err(Fault::WrongType));
        assert_eq!(call(cx, 26, 2, Intrinsic::SetBox), Err(Fault::WrongType));

        let tail = Op::TailCallIntrinsic { base: 10, args: 2, intrinsic: Intrinsic::Add };
        assert_eq!(tail.step(cx), Ok(Control::Return));
        assert_eq!(cx.acc, fix(3));

        assert_eq!(call(cx, 10, 2, Intrinsic::Car), Err(Fault::Malformed));
        assert_eq!(call(cx, 255, 2, Intrinsic::Add), Err(Fault::Malformed));
    });
}

#[test]
fn equality_goes_as_deep_as_it_should() {
    with_frame(|cx| {
        let (mc, frame) = (cx.mc, cx.frame);
        let test = |cx: &mut Context<'_, '_>, intrinsic, a, b| {
            frame.set(27, a);
            frame.set(28, b);
            Op::CallIntrinsic { base: 27, args: 2, intrinsic }.step(cx).unwrap();
            cx.acc == Value::TRUE
        };
        let (eqv, equal) = (Intrinsic::Eqv, Intrinsic::Equal);
        let (strings, pairs, vectors) = (Strings::new(mc), Pairs::new(mc), Vectors::new(mc));
        let text = |s: &str| string::from_str(&strings, s).unwrap().value();
        let boxed = |v| Value::object(mc, crate::objects::Box::new(mc, v).unwrap());
        let big = |n: i64| {
            let h = ragwort_types::num::Nums::new(mc);
            let (a, b) = (h.number(fix(Value::MAX_FIXNUM)).unwrap(), h.number(fix(n)).unwrap());
            ragwort_types::num::complex::add(&h, a, b).unwrap().value()
        };

        // Numbers are eqv? by exactness and value, whatever objects hold them.
        assert!(test(cx, eqv, big(1), big(1)) && big(1) != big(1));
        assert!(!test(cx, eqv, big(1), big(2)));
        assert!(test(cx, eqv, Value::flonum(mc, 1e300).unwrap(), Value::flonum(mc, 1e300).unwrap()));
        assert!(!test(cx, eqv, fix(2), Value::flonum(mc, 2.0).unwrap()));
        assert!(!test(cx, equal, fix(2), Value::flonum(mc, 2.0).unwrap()));
        assert!(!test(cx, Intrinsic::Eq, big(1), big(1)));

        // Strings are equal? by their characters, but only eqv? as the same object.
        let long = "a string too long to fit in a value";
        assert!(!test(cx, eqv, text(long), text(long)));
        assert!(test(cx, equal, text(long), text(long)));
        assert!(!test(cx, equal, text(long), text("a string too long to fit in a value!")));
        assert!(!test(cx, equal, text("1"), fix(1)));

        // Pairs, vectors of either kind, and boxes, by their contents.
        let list = |items: &[_]| pairs.list(items).unwrap();
        let tree = |n| list(&[text(long), list(&[big(n), boxed(fix(1))]), vectors.from_slice(&[fix(n), Value::NIL]).unwrap().value(mc)]);
        assert!(!test(cx, eqv, tree(1), tree(1)));
        assert!(test(cx, equal, tree(1), tree(1)));
        assert!(!test(cx, equal, tree(1), tree(2)));
        assert!(!test(cx, equal, list(&[fix(1), fix(2)]), list(&[fix(1)])));
        let items = [fix(1), text(long)];
        assert!(test(cx, equal, vectors.from_slice(&items).unwrap().value(mc), vectors.immutable_from_slice(&items).unwrap().value(mc)));
        assert!(!test(cx, equal, vectors.from_slice(&items).unwrap().value(mc), vectors.from_slice(&items[..1]).unwrap().value(mc)));
        assert!(!test(cx, equal, boxed(fix(1)), list(&[fix(1)])));
        assert!(!test(cx, equal, boxed(fix(1)), boxed(fix(2))));

        // A long list, and one nested deep in its heads, take no Rust stack.
        let long_list = || pairs.list(&(0..200_000).map(fix).collect::<Vec<_>>()).unwrap();
        assert!(test(cx, equal, long_list(), long_list()));
        let deep = || (0..200_000).fold(Value::NIL, |v, _| pairs.cons(v, Value::NIL).unwrap().value(mc));
        assert!(test(cx, equal, deep(), deep()));

        // Cycles end: a box that holds itself, and vectors that hold each other, with a
        // difference far enough in that comparing starts looking for cycles first.
        let cycle = || {
            let b = boxed(Value::VOID);
            b.downcast::<crate::objects::Box>(mc).unwrap().set_value(mc, b);
            b
        };
        assert!(test(cx, equal, cycle(), cycle()));
        let knot = |n| {
            let b = boxed(Value::VOID);
            b.downcast::<crate::objects::Box>(mc).unwrap().set_value(mc, list(&[fix(n), b]));
            b
        };
        assert!(test(cx, equal, knot(1), knot(1)));
        assert!(!test(cx, equal, knot(1), knot(2)));

        // Shared parts are compared once, not once for each way to reach them: 64 levels of
        // `(cons x x)` and `(vector x x)` have 2^64 paths each.
        let shared = |leaf, vector: bool| {
            (0..64).fold(leaf, |x, _| match vector {
                true => vectors.immutable_from_slice(&[x, x]).unwrap().value(mc),
                false => pairs.cons(x, x).unwrap().value(mc),
            })
        };
        for vector in [false, true] {
            assert!(test(cx, equal, shared(fix(1), vector), shared(fix(1), vector)));
            assert!(!test(cx, equal, shared(fix(1), vector), shared(fix(2), vector)));
        }
        let ring = |n: usize, last: i64| {
            let vs: Vec<_> = (0..n).map(|_| vectors.make(2, fix(0)).unwrap()).collect();
            for (i, v) in vs.iter().enumerate() {
                v.items(mc).set(mc, 0, vs[(i + 1) % n].value(mc));
                v.items(mc).set(mc, 1, fix(if i == n - 1 { last } else { 0 }));
            }
            vs[0].value(mc)
        };
        assert!(test(cx, equal, ring(3000, 1), ring(3000, 1)));
        assert!(!test(cx, equal, ring(2, 1), ring(4, 1)));
        assert!(test(cx, equal, ring(3, 0), ring(5, 0)));
        assert!(!test(cx, equal, ring(3000, 1), ring(3000, 2)));

        // A unit of fuel for each 1024 values compared: a list's pairs count as well as its items.
        let spent = |cx: &mut Context<'_, '_>, a, b| {
            cx.fuel = Fuel { run: 100, rest: 0 };
            test(cx, equal, a, b);
            100 - cx.fuel.left()
        };
        let (items, short): (Vec<_>, Vec<_>) = ((0..10_240).map(fix).collect(), (0..100).map(fix).collect());
        let vector = |items: &[_]| vectors.from_slice(items).unwrap().value(mc);
        assert_eq!(spent(cx, vector(&items), vector(&items)), 10);
        assert_eq!(spent(cx, list(&items), list(&items)), 20);
        assert_eq!(spent(cx, list(&short), list(&short)), 0);

        // Past the run's fuel, it spends the rest, and past that it stops.
        cx.fuel = Fuel { run: 3, rest: 20 };
        test(cx, equal, vector(&items), vector(&items));
        assert_eq!(cx.fuel, Fuel { run: 0, rest: 13 });
        cx.fuel = Fuel { run: 3, rest: 6 };
        frame.set(27, vector(&items));
        frame.set(28, vector(&items));
        assert_eq!(Op::CallIntrinsic { base: 27, args: 2, intrinsic: equal }.step(cx), Err(Fault::OutOfFuel));
        cx.fuel = Fuel { run: u64::MAX, rest: 0 };

        frame.set(29, boxed(fix(1)));
        frame.set(30, list(&[]));
        Op::CallIntrinsic { base: 29, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        Op::CallIntrinsic { base: 30, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
        assert_eq!(cx.acc, Value::FALSE);
    });
}

#[test]
fn values_are_an_object() {
    with_frame(|cx| {
        let (mc, frame) = (cx.mc, cx.frame);
        let call = |cx: &mut Context<'_, '_>, base, args, intrinsic| Op::CallIntrinsic { base, args, intrinsic }.step(cx);
        (0..3).for_each(|i| frame.set(20 + i, fix(i64::from(i) + 10)));
        call(cx, 20, 3, Intrinsic::Values).unwrap();
        frame.set(30, cx.acc);
        call(cx, 30, 1, Intrinsic::IsValues).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        call(cx, 30, 1, Intrinsic::ValuesLength).unwrap();
        assert_eq!(cx.acc, fix(3));
        frame.set(31, fix(2));
        call(cx, 30, 2, Intrinsic::ValuesRef).unwrap();
        assert_eq!(cx.acc, fix(12));
        frame.set(31, fix(3));
        assert_eq!(call(cx, 30, 2, Intrinsic::ValuesRef), Err(Fault::OutOfRange));
        frame.set(31, Value::NIL);
        assert_eq!(call(cx, 30, 2, Intrinsic::ValuesRef), Err(Fault::WrongType));

        // One value is itself, and none is an empty object.
        call(cx, 20, 1, Intrinsic::Values).unwrap();
        assert_eq!(cx.acc, fix(10));
        call(cx, 20, 1, Intrinsic::IsValues).unwrap();
        assert_eq!(cx.acc, Value::FALSE);
        assert_eq!(call(cx, 20, 1, Intrinsic::ValuesLength), Err(Fault::WrongType));
        call(cx, 20, 0, Intrinsic::Values).unwrap();
        assert_eq!(cx.acc.downcast::<objects::MultiValue>(mc).map(|v| v.items(mc).len()), Some(0));
    });
}

#[test]
fn every_built_in_is_listed_once_by_name() {
    assert!(crate::Intrinsic::ALL.iter().enumerate().all(|(k, &i)| i as usize == k));
    assert!(crate::Request::ALL.iter().enumerate().all(|(k, &r)| r as usize == k));
    let mut names: Vec<_> = crate::Intrinsic::ALL.iter().map(|i| i.name()).chain(crate::Request::ALL.iter().map(|r| r.name())).collect();
    names.sort_unstable();
    let len = names.len();
    names.dedup();
    assert_eq!(names.len(), len);
    assert!(crate::Intrinsic::ALL.iter().all(|&i| i.name().parse() == Ok(i)));
    assert!(crate::Request::ALL.iter().all(|&r| r.name().parse() == Ok(r)));
    assert_eq!("frob".parse::<crate::Intrinsic>(), Err(ragwort_types::UnknownName));
    assert_eq!(Op::Return { src: 0 }.name(), "return");
    assert_eq!(Op::TailCallRequest { base: 0, args: 0, request: crate::Request::Abort }.name(), "tail-call-request");
}

#[test]
fn intrinsics_run_without_a_frame() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let mut fuel = Fuel { run: u64::MAX, rest: 0 };
        let fix = |n| Value::fixnum(n).unwrap();
        assert_eq!(Intrinsic::Add.run(mc, &[fix(1), fix(2), fix(3)], &mut fuel), Ok(fix(6)));
        assert_eq!(Intrinsic::Add.run(mc, &[], &mut fuel), Ok(fix(0)));
        let list = Pairs::new(mc).list(&[fix(1), fix(2)]).unwrap();
        assert_eq!(Intrinsic::Car.run(mc, &[list], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::Car.run(mc, &[fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::Car.run(mc, &[list, list], &mut fuel), Err(Fault::Arity));
        assert_eq!(Intrinsic::Add.run(mc, &[fix(1); 256], &mut fuel), Ok(fix(256)));
        assert_eq!(Intrinsic::Add.run(mc, &[fix(1); 1000], &mut fuel), Ok(fix(1000)));
    });
}

#[test]
fn every_cxr_follows_its_name_from_the_last_letter() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let mut fuel = Fuel { run: u64::MAX, rest: 0 };
        let pairs = Pairs::new(mc);
        // A tree four deep, each leaf the path to it, written as `c...r` would read it.
        fn tree<'gc>(mc: &Mutation<'gc>, path: String, depth: usize) -> Value<'gc> {
            if depth == 0 {
                return string::from_str(&Strings::new(mc), &path).unwrap().value();
            }
            let head = tree(mc, format!("a{path}"), depth - 1);
            let tail = tree(mc, format!("d{path}"), depth - 1);
            Pairs::new(mc).cons(head, tail).unwrap().value(mc)
        }
        let strings = Strings::new(mc);
        let cxrs: Vec<_> = Intrinsic::ALL.iter().filter(|i| matches!(i.name().as_bytes(), [b'c', middle @ .., b'r'] if !middle.is_empty() && middle.iter().all(|&b| b == b'a' || b == b'd'))).collect();
        assert_eq!(cxrs.len(), 2 + 4 + 8 + 16);
        for cxr in cxrs {
            let path = &cxr.name()[1..cxr.name().len() - 1];
            let x = tree(mc, String::new(), path.len());
            let got = cxr.run(mc, &[x], &mut fuel).unwrap();
            assert!(string::equal_str(&strings, strings.string(got).unwrap(), path).unwrap(), "{}", cxr.name());
        }
        assert_eq!(Intrinsic::Cadddr.run(mc, &[pairs.list(&[fix(1), fix(2)]).unwrap()], &mut fuel), Err(Fault::WrongType));
    });
}

#[test]
fn booleans_void_and_bytevectors() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let mut fuel = Fuel { run: u64::MAX, rest: 0 };
        assert_eq!(Intrinsic::IsBoolean.run(mc, &[Value::FALSE], &mut fuel), Ok(Value::TRUE));
        assert_eq!(Intrinsic::IsBoolean.run(mc, &[Value::NIL], &mut fuel), Ok(Value::FALSE));
        assert_eq!(Intrinsic::Void.run(mc, &[], &mut fuel), Ok(Value::VOID));
        assert_eq!(Intrinsic::Void.run(mc, &[fix(1), fix(2)], &mut fuel), Ok(Value::VOID));
        let h = ragwort_types::bytevector::Bytevectors::new(mc);
        let bytes = h.from_slice(&[1, 2, 3, 4, 5, 6, 7, 8, 9]).unwrap().value(mc);
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(8)], &mut fuel), Ok(fix(9)));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(8), fix(255)], &mut fuel), Ok(Value::VOID));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(8)], &mut fuel), Ok(fix(255)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7)], &mut fuel), Ok(fix(8)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(9)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(-1)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, Value::NIL], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[fix(0), fix(0)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(0), fix(256)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(9), fix(0)], &mut fuel), Err(Fault::OutOfRange));
        let literal = h.immutable_from_slice(&[1]).unwrap().value(mc);
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[literal, fix(0)], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[literal, fix(0), fix(2)], &mut fuel), Err(Fault::Immutable));
    });
}
