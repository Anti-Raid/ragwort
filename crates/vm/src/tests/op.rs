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
            (0..64).fold(leaf, |x, _| {
                if vector { vectors.immutable_from_slice(&[x, x]).unwrap().value(mc) } else { pairs.cons(x, x).unwrap().value(mc) }
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
fn shifts_and_bit_fields_are_charged_for_what_their_counts_make() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let bits = fix(12_800_000);
        let calls = [
            (Intrinsic::ArithmeticShift, vec![fix(1), bits]),
            (Intrinsic::BitField, vec![fix(-1), fix(0), bits]),
            (Intrinsic::BitFieldReplace, vec![fix(-1), fix(0), fix(0), bits]),
        ];
        for (intrinsic, args) in calls {
            let mut fuel = Fuel { run: 100, rest: 0 };
            assert_eq!(intrinsic.run(mc, &args, &mut fuel), Err(Fault::OutOfFuel), "{intrinsic:?}");
            let mut fuel = Fuel { run: 1000, rest: 0 };
            assert!(intrinsic.run(mc, &args, &mut fuel).is_ok(), "{intrinsic:?}");
            assert_eq!(fuel.left(), 1000 - 12_800_000 / 64 / 1024, "{intrinsic:?}");
        }
        // Wide fields of narrow numbers cost nothing past the call.
        let mut fuel = Fuel { run: 100, rest: 0 };
        assert_eq!(Intrinsic::BitField.run(mc, &[fix(5), fix(0), bits], &mut fuel), Ok(fix(5)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(2), fix(0), bits], &mut fuel), Ok(fix(2)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(0), bits, fix(25_600_000)], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(-1), bits, bits], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::ArithmeticShift.run(mc, &[fix(0), bits], &mut fuel), Ok(fix(0)));
        assert_eq!(fuel.left(), 100);
        // -1 is as long as 0, but shifts into a number as long as the count.
        assert_eq!(Intrinsic::ArithmeticShift.run(mc, &[fix(-1), bits], &mut fuel), Err(Fault::OutOfFuel));
    });
}

fn run<'gc>(mc: &Mutation<'gc>, op: Intrinsic, args: &[Value<'gc>]) -> Result<Value<'gc>, Fault> {
    op.run(mc, args, &mut Fuel { run: u64::MAX, rest: 0 })
}

/// A struct is of its type and its type's supertypes, and `equal?` to one of its type with
/// `equal?` fields, unless its type is an identity one, whose structs are `equal?` only to
/// themselves.
#[test]
fn structs_are_of_their_types_and_equal_by_their_fields_or_themselves() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let (symbols, strings, pairs) = (ragwort_types::symbol::Symbols::of_arena(mc).unwrap(), Strings::new(mc), Pairs::new(mc));
        let symbol = |name: &str| symbols.intern_str(&strings, name).unwrap().value(mc);
        let names = |names: &[&str]| pairs.list(&names.iter().map(|n| symbol(n)).collect::<Vec<_>>()).unwrap();
        // The flags of a type's fields, which can all be set, or can't.
        let flags = |n: usize, mutable: bool| pairs.list(&vec![fix(i64::from(mutable)); n]).unwrap();
        let (plain, identity, sealed) = (fix(0), fix(1), fix(2));
        let point = run(mc, Intrinsic::MakeStructType, &[symbol("point"), Value::FALSE, names(&["x", "y"]), flags(2, true), plain]).unwrap();
        let point3 = run(mc, Intrinsic::MakeStructType, &[symbol("point3"), point, names(&["z"]), flags(1, true), plain]).unwrap();
        let point4 = run(mc, Intrinsic::MakeStructType, &[symbol("point4"), point3, names(&["w"]), flags(1, false), plain]).unwrap();
        let other = run(mc, Intrinsic::MakeStructType, &[symbol("point"), Value::FALSE, names(&["x", "y"]), flags(2, false), plain]).unwrap();
        let p = run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap();
        let q = run(mc, Intrinsic::MakeStruct, &[point4, fix(1), fix(2), fix(3), fix(4)]).unwrap();
        // Each is of its type and those above it, and of no other.
        for (v, kind, is) in [(p, point, true), (p, point3, false), (p, other, false), (q, point, true), (q, point3, true), (q, point4, true), (q, other, false), (fix(1), point, false)] {
            assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[v, kind]), Ok(if is { Value::TRUE } else { Value::FALSE }));
        }
        for (v, is) in [(p, true), (q, true), (point, false), (fix(1), false), (pairs.list(&[p]).unwrap(), false)] {
            assert_eq!(run(mc, Intrinsic::IsStruct, &[v]), Ok(if is { Value::TRUE } else { Value::FALSE }));
        }
        for (v, is) in [(point, true), (point4, true), (p, false), (fix(1), false)] {
            assert_eq!(run(mc, Intrinsic::IsStructType, &[v]), Ok(if is { Value::TRUE } else { Value::FALSE }));
        }
        assert_eq!(run(mc, Intrinsic::StructRef, &[q, point, fix(1)]), Ok(fix(2)));
        assert_eq!(run(mc, Intrinsic::StructRef, &[q, point4, fix(3)]), Ok(fix(4)));
        assert_eq!(run(mc, Intrinsic::StructRef, &[q, point, fix(2)]), Err(Fault::OutOfRange), "a field of a subtype");
        assert_eq!(run(mc, Intrinsic::StructRef, &[p, point3, fix(0)]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::StructRef, &[p, other, fix(0)]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::StructRef, &[p, p, fix(0)]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::StructSet, &[q, point3, fix(2), fix(30)]), Ok(Value::VOID));
        assert_eq!(run(mc, Intrinsic::StructRef, &[q, point4, fix(2)]), Ok(fix(30)));
        // A field its type doesn't say can be set can't be, by any type the struct is of.
        assert_eq!(run(mc, Intrinsic::StructSet, &[q, point4, fix(3), fix(40)]), Err(Fault::Immutable));
        assert_eq!(run(mc, Intrinsic::StructSet, &[q, point4, fix(0), fix(10)]), Ok(Value::VOID), "a supertype's that can be");
        assert_eq!(run(mc, Intrinsic::StructSet, &[q, point4, fix(0), fix(1)]), Ok(Value::VOID));
        let fixed = run(mc, Intrinsic::MakeStruct, &[other, fix(1), fix(2)]).unwrap();
        assert_eq!(run(mc, Intrinsic::StructSet, &[fixed, other, fix(0), fix(9)]), Err(Fault::Immutable));
        assert_eq!(run(mc, Intrinsic::StructSet, &[fixed, other, fix(2), fix(9)]), Err(Fault::OutOfRange));
        assert_eq!(run(mc, Intrinsic::StructRef, &[fixed, other, fix(0)]), Ok(fix(1)));
        assert_eq!(run(mc, Intrinsic::MakeStruct, &[point, fix(1)]), Err(Fault::Arity));
        assert_eq!(run(mc, Intrinsic::MakeStruct, &[point3, fix(1), fix(2), fix(3), fix(4)]), Err(Fault::Arity));
        assert_eq!(run(mc, Intrinsic::MakeStruct, &[fix(1), fix(1)]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("bad"), fix(1), Value::NIL, Value::NIL, plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("bad"), Value::FALSE, pairs.list(&[fix(1)]).unwrap(), flags(1, false), plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("bad"), Value::FALSE, names(&["x", "y"]), flags(1, false), plain]), Err(Fault::WrongType), "a flag for each field");
        let same = run(mc, Intrinsic::MakeStruct, &[point, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let alike = run(mc, Intrinsic::MakeStruct, &[point, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let elsewhere = run(mc, Intrinsic::MakeStruct, &[other, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let up = run(mc, Intrinsic::MakeStruct, &[point3, fix(1), pairs.list(&[fix(2)]).unwrap(), fix(3)]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[same, alike]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::Eqv, &[same, alike]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[same, p]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[same, elsewhere]), Ok(Value::FALSE), "another type of the same name");
        assert_eq!(run(mc, Intrinsic::Equal, &[same, up]), Ok(Value::FALSE), "a subtype");
        // A struct that holds itself is compared without end otherwise.
        let (a, b) = (run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap(), run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap());
        run(mc, Intrinsic::StructSet, &[a, point, fix(1), a]).unwrap();
        run(mc, Intrinsic::StructSet, &[b, point, fix(1), b]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[a, b]), Ok(Value::TRUE));

        let listed = run(mc, Intrinsic::StructFields, &[point4]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[listed, names(&["x", "y", "z", "w"])]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::StructFields, &[p]), Err(Fault::WrongType));

        // An identity type's structs, and its subtypes', are `equal?` only to themselves.
        let session = run(mc, Intrinsic::MakeStructType, &[symbol("session"), Value::FALSE, names(&["token", "user"]), flags(2, true), identity]).unwrap();
        let admin = run(mc, Intrinsic::MakeStructType, &[symbol("admin"), session, names(&[]), flags(0, false), plain]).unwrap();
        let (s, t) = (run(mc, Intrinsic::MakeStruct, &[session, fix(1), fix(2)]).unwrap(), run(mc, Intrinsic::MakeStruct, &[session, fix(1), fix(2)]).unwrap());
        let (a, b) = (run(mc, Intrinsic::MakeStruct, &[admin, fix(1), fix(2)]).unwrap(), run(mc, Intrinsic::MakeStruct, &[admin, fix(1), fix(2)]).unwrap());
        assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[s, session]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[a, session]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[p, session]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[s, t]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[s, s]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::Equal, &[a, b]), Ok(Value::FALSE), "a subtype of an identity type");
        assert_eq!(run(mc, Intrinsic::Equal, &[pairs.list(&[s]).unwrap(), pairs.list(&[s]).unwrap()]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::Equal, &[pairs.list(&[s]).unwrap(), pairs.list(&[t]).unwrap()]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::StructRef, &[s, session, fix(1)]), Ok(fix(2)));
        assert_eq!(run(mc, Intrinsic::StructSet, &[s, session, fix(1), fix(9)]), Ok(Value::VOID));
        assert_eq!(run(mc, Intrinsic::StructRef, &[s, session, fix(1)]), Ok(fix(9)));

        // An instance has the type it was made as, and its fields' values as a list.
        assert_eq!(run(mc, Intrinsic::StructType, &[q]), Ok(point4));
        assert_eq!(run(mc, Intrinsic::StructType, &[p]), Ok(point));
        assert_eq!(run(mc, Intrinsic::StructType, &[point]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::StructType, &[fix(1)]), Err(Fault::WrongType));
        let listed = run(mc, Intrinsic::StructToList, &[q]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[listed, pairs.list(&[fix(1), fix(2), fix(30), fix(4)]).unwrap()]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::StructToList, &[point]), Err(Fault::WrongType));
        for internal in [Intrinsic::MakeStructType, Intrinsic::MakeStruct, Intrinsic::StructRef, Intrinsic::StructField, Intrinsic::StructSet] {
            assert!(internal.is_internal(), "{internal:?}");
        }
        for public in [Intrinsic::IsStruct, Intrinsic::IsStructType, Intrinsic::IsStructDerivedFrom, Intrinsic::StructFields, Intrinsic::IsStructFieldMutable, Intrinsic::StructType, Intrinsic::StructToList, Intrinsic::Car] {
            assert!(!public.is_internal(), "{public:?}");
        }

        // A sealed type is no supertype, and flags that aren't a form's to give aren't taken.
        let last = run(mc, Intrinsic::MakeStructType, &[symbol("last"), point, names(&["z"]), flags(1, false), sealed]).unwrap();
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("more"), last, names(&[]), flags(0, false), plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[run(mc, Intrinsic::MakeStruct, &[last, fix(1), fix(2), fix(3)]).unwrap(), point]), Ok(Value::TRUE));
        for bad in [fix(4), fix(-1), Value::FALSE] {
            assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("bad"), Value::FALSE, names(&[]), flags(0, false), bad]), Err(Fault::WrongType));
        }
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol("bad"), Value::FALSE, names(&["x"]), pairs.list(&[fix(2)]).unwrap(), plain]), Err(Fault::WrongType));

    });
}

/// A bytevector whose bytes the host owns reads like any other, and is written to if the
/// host gave a buffer.
#[test]
fn external_bytevectors_read_and_write_like_others() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let mut fuel = Fuel { run: u64::MAX, rest: 0 };
        let h = ragwort_types::bytevector::Bytevectors::new(mc);
        let text = "a message body from outside the arena, long enough to stay there: λ ".repeat(3);
        let external = h.external(text.clone().into_bytes()).unwrap();
        assert!(external.is_external());
        let (external, copy) = (external.value(mc), h.from_slice(text.as_bytes()).unwrap().value(mc));
        assert_eq!(Intrinsic::IsBytevector.run(mc, &[external], &mut fuel), Ok(Value::TRUE));
        assert_eq!(Intrinsic::Equal.run(mc, &[external, copy], &mut fuel), Ok(Value::TRUE));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[external, fix(2), Value::FALSE, fix(1)], &mut fuel), Ok(fix(109)));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[external, fix(0), fix(1), Value::FALSE, fix(1)], &mut fuel), Err(Fault::Immutable));
        let strings = Strings::new(mc);
        let all = Intrinsic::Utf8ToString.run(mc, &[external], &mut fuel).unwrap();
        assert_eq!(string::display(&strings, strings.string(all).unwrap()).to_string(), text);
        let part = Intrinsic::Utf8ToString.run(mc, &[external, fix(2), fix(9)], &mut fuel).unwrap();
        assert_eq!(string::display(&strings, strings.string(part).unwrap()).to_string(), "message");
        let shared = h.external_mutable(b"hello".to_vec()).unwrap().value(mc);
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[shared, fix(0), fix(106), Value::FALSE, fix(1)], &mut fuel), Ok(Value::VOID));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[shared, fix(5), fix(1), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        let jello = Intrinsic::Utf8ToString.run(mc, &[shared], &mut fuel).unwrap();
        assert_eq!(string::display(&strings, strings.string(jello).unwrap()).to_string(), "jello");
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
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(8), Value::FALSE, fix(1)], &mut fuel), Ok(fix(9)));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(8), fix(255), Value::FALSE, fix(1)], &mut fuel), Ok(Value::VOID));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(8), Value::FALSE, fix(1)], &mut fuel), Ok(fix(255)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7), Value::FALSE, fix(1)], &mut fuel), Ok(fix(8)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(9), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(-1), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, Value::NIL, Value::FALSE, fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[fix(0), fix(0), Value::FALSE, fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(0), fix(256), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        // Two bytes across a word, most significant first, and signed.
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7), Value::TRUE, fix(2)], &mut fuel), Ok(fix(0x08ff)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7), Value::FALSE, fix(-2)], &mut fuel), Ok(fix(-248)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::FALSE, fix(0)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::FALSE, fix(9)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::NIL, fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(9), fix(0), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        let literal = h.immutable_from_slice(&[1]).unwrap().value(mc);
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[literal, fix(0), Value::FALSE, fix(1)], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[literal, fix(0), fix(2), Value::FALSE, fix(1)], &mut fuel), Err(Fault::Immutable));
    });
}

#[test]
fn string_comparisons_spend_fuel_for_what_they_compare() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let strings = Strings::new(mc);
        let text = |s: &str| string::from_str(&strings, s).unwrap().value();
        fn spent<'gc>(mc: &Mutation<'gc>, op: Intrinsic, args: &[Value<'gc>]) -> u64 {
            let mut fuel = Fuel { run: 100, rest: 0 };
            op.run(mc, args, &mut fuel).unwrap();
            100 - fuel.left()
        }
        // A unit for each 1024 characters of the shorter of each pair.
        let (long, other) = (text(&"a".repeat(10_240)), text(&"a".repeat(10_240)));
        for op in [Intrinsic::StringEq, Intrinsic::StringLt, Intrinsic::StringGe] {
            assert_eq!(spent(mc, op, &[long, other]), 10, "{op:?}");
        }
        assert_eq!(spent(mc, Intrinsic::StringEq, &[long, other, long]), 20);
        assert_eq!(spent(mc, Intrinsic::StringEq, &[long, text("a")]), 0);
        let mut fuel = Fuel { run: 3, rest: 0 };
        assert_eq!(Intrinsic::StringEq.run(mc, &[long, other], &mut fuel), Err(Fault::OutOfFuel));
    });
}
