use ragwort_types::gc::{Arena, Segment, Value};
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

#[test]
fn steps_run_against_the_frame() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let constants = Constants::of(vectors.immutable_from_slice(&[fix(7)]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[Value::TRUE]).unwrap().items(mc);
        let mut cx = Context { mc, frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };

        assert_eq!(Op::LoadConst { dst: 0, index: 0 }.step(&mut cx), Ok(Control::Next));
        assert_eq!(Op::Move { dst: 1, src: 0 }.step(&mut cx), Ok(Control::Next));
        assert_eq!(frame.get(1), fix(7));

        frame.set(2, Value::FALSE);
        assert_eq!(Op::JumpIfFalse { test: 1, offset: 5 }.step(&mut cx), Ok(Control::Next));
        assert_eq!(Op::JumpIfFalse { test: 2, offset: -3 }.step(&mut cx), Ok(Control::Jump(-3)));
        assert_eq!(Op::Jump { offset: 9 }.step(&mut cx), Ok(Control::Jump(9)));

        Op::LoadUpvalue { dst: 3, index: 0 }.step(&mut cx).unwrap();
        assert_eq!(frame.get(3), Value::TRUE);

        assert_eq!(Op::Return { src: 0 }.step(&mut cx), Ok(Control::Return));
        Op::MoveAcc { dst: 7 }.step(&mut cx).unwrap();
        assert_eq!((cx.acc, frame.get(7)), (fix(7), fix(7)));

        assert_eq!(Op::Call { base: 8, args: 2 }.step(&mut cx), Ok(Control::Call { base: 8, args: 2 }));
        let request = Op::TailCallRequest { base: 8, args: 1, request: Request::Abort };
        assert_eq!(request.step(&mut cx), Ok(Control::TailCallRequest { base: 8, args: 1, request: Request::Abort }));
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
        let mut cx = Context { mc, frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };
        frame.set(0, fix(1));
        let requests = [
            Op::CallRequest { base: 1, args: 1, request: Request::MarkValue },
            Op::TailCallRequest { base: 1, args: 3, request: Request::Capture },
            Op::CallRequest { base: 1, args: 1, request: Request::Apply },
        ];
        for op in [Op::LoadConst { dst: 1, index: 0 }, Op::LoadUpvalue { dst: 1, index: 0 }].into_iter().chain(requests) {
            assert_eq!(op.step(&mut cx), Err(Fault::Malformed), "{op:?}");
        }
    });
}

/// Code that does nothing, whose closures capture `captures`.
fn code<'gc>(mc: &Mutation<'gc>, captures: &[Capture]) -> Value<'gc> {
    let ops = mc.frozen(Box::from([Op::Return { src: 0 }])).unwrap();
    let empty = Vectors::new(mc).immutable_from_slice(&[]).unwrap().value(mc);
    Value::object(mc, objects::Bytecode::new(mc, ops, empty, mc.frozen(Box::from(captures)).unwrap(), 0).unwrap())
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
        let mut cx = Context { mc, frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } };

        frame.set(0, fix(5));
        assert_eq!(Op::NewClosure { dst: 1, count: 2, code: 1 }.step(&mut cx), Ok(Control::Next));
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
            assert_eq!(op.step(&mut cx), Err(Fault::Malformed), "{op:?}");
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
        f(&mut Context { mc, frame, constants, upvalues, acc: Value::VOID, fuel: Fuel { run: u64::MAX, rest: 0 } });
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
        frame.set(40, cx.acc);
        frame.set(41, Value::TRUE);
        call(cx, 40, 2, Intrinsic::SetBox).unwrap();
        assert_eq!(cx.acc, Value::VOID);
        call(cx, 40, 1, Intrinsic::Unbox).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        assert_eq!(call(cx, 41, 1, Intrinsic::Unbox), Err(Fault::WrongType));
        assert_eq!(call(cx, 41, 2, Intrinsic::SetBox), Err(Fault::WrongType));

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
            frame.set(50, a);
            frame.set(51, b);
            Op::CallIntrinsic { base: 50, args: 2, intrinsic }.step(cx).unwrap();
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
        frame.set(50, vector(&items));
        frame.set(51, vector(&items));
        assert_eq!(Op::CallIntrinsic { base: 50, args: 2, intrinsic: equal }.step(cx), Err(Fault::OutOfFuel));
        cx.fuel = Fuel { run: u64::MAX, rest: 0 };

        frame.set(60, boxed(fix(1)));
        frame.set(61, list(&[]));
        Op::CallIntrinsic { base: 60, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        Op::CallIntrinsic { base: 61, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
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
