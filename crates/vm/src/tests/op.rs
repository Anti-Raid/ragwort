use ragwort_types::gc::{Arena, Mutation, Segment, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};
use ragwort_types::constant::Constants;
use ragwort_types::vector::Vectors;

use super::*;
use crate::objects::BoxFields;
use crate::op::Fuel;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn text<'gc>(mc: &Mutation<'gc>, content: &str) -> Value<'gc> {
    string::from_str(&Strings::new(mc), content).unwrap().value()
}

/// Executes `op.step(cx)` out of line (`#[inline(never)]`). In debug builds, inlining `step` causes every intrinsic implementation's stack frame to accumulate on the caller's stack, causing stack overflow in tests executing long operation sequences.
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
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, code: code(mc, &[]).downcast(mc).unwrap(), upvalues, acc: Value::VOID, values: Value::NULL, fuel: Fuel { run: u64::MAX, rest: 0 } };

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
        // Tests `Op::AddImm`: verifies in-place fixnum addition, overflow promotion to generic addition when exceeding fixnum boundaries, and type faults when operating on non-numeric operands.
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
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, code: code(mc, &[]).downcast(mc).unwrap(), upvalues, acc: Value::VOID, values: Value::NULL, fuel: Fuel { run: u64::MAX, rest: 0 } };
        frame.set(0, fix(1));
        let requests = [
            Op::CallRequest { base: 1, args: 1, request: Request::WithMark },
            Op::CallIntrinsic { base: 1, args: 1, intrinsic: Intrinsic::MarkValue },
            Op::CallIntrinsic1 { dst: 1, a: 0, intrinsic: Intrinsic::FrameMark },
            Op::CallIntrinsic2 { dst: 1, a: 0, b: 0, intrinsic: Intrinsic::Running },
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

/// Constructs a no-op bytecode object (`Op::Return { src: 0 }`) whose closure captures the specified `captures`.
fn code<'gc>(mc: &Mutation<'gc>, captures: &[Capture]) -> Value<'gc> {
    let ops = mc.frozen(Box::from([Op::Return { src: 0 }])).unwrap();
    let empty = Vectors::new(mc).immutable_from_slice(&[]).unwrap().value(mc);
    Value::object(mc, objects::Bytecode::new(mc, ops, empty, mc.frozen(Box::from(captures)).unwrap(), 0, None, Value::FALSE, Value::FALSE, 0, Value::FALSE, 0, 0, None).unwrap())
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
        let mut cx = Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, code: code(mc, &[]).downcast(mc).unwrap(), upvalues, acc: Value::VOID, values: Value::NULL, fuel: Fuel { run: u64::MAX, rest: 0 } };

        frame.set(0, fix(5));
        assert_eq!(step(Op::NewClosure { dst: 1, count: 2, code: 1 }, &mut cx), Ok(Control::Next));
        fn items<'gc>(mc: &Mutation<'gc>, closure: Value<'gc>) -> Vec<Value<'gc>> {
            let upvalues = closure.downcast::<objects::Closure>(mc).unwrap().items(mc);
            (0..upvalues.len()).map(|i| upvalues.get(i)).collect::<Vec<_>>()
        }
        assert_eq!(items(mc, frame.get(1)), [fix(5), fix(11), frame.get(2)]);
        assert_eq!(items(mc, frame.get(2)), [frame.get(1)]);

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

/// Initializes an arena and fresh VM execution frame with empty constant and upvalue tables, then executes `f` within that context.
fn with_frame(f: impl for<'s, 'gc> FnOnce(&mut Context<'s, 'gc>)) {
    let mut arena = Arena::new(1 << 26, 0);
    arena.mutate(|mc| {
        let stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
        let frame = stack.frame(mc, 0).unwrap();
        let vectors = Vectors::new(mc);
        let constants = Constants::of(vectors.immutable_from_slice(&[]).unwrap().value(mc)).unwrap();
        let upvalues = vectors.from_slice(&[]).unwrap().items(mc);
        f(&mut Context { mc, task: crate::coroutine::root(mc).unwrap(), frame, constants, code: code(mc, &[]).downcast(mc).unwrap(), upvalues, acc: Value::VOID, values: Value::NULL, fuel: Fuel { run: u64::MAX, rest: 0 } });
    });
}

#[test]
fn intrinsics_run_in_place() {
    with_frame(|cx| {
        let (mc, frame) = (cx.mc, cx.frame);
        fn call(cx: &mut Context<'_, '_>, base: u8, args: u8, intrinsic: Intrinsic) -> Result<Control, Fault> {
            Op::CallIntrinsic { base, args, intrinsic }.step(cx)
        }
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

        frame.set(31, Value::NULL);
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
        fn test<'gc>(cx: &mut Context<'_, 'gc>, intrinsic: Intrinsic, left: Value<'gc>, right: Value<'gc>) -> bool {
            cx.frame.set(27, left);
            cx.frame.set(28, right);
            Op::CallIntrinsic { base: 27, args: 2, intrinsic }.step(cx).unwrap();
            cx.acc == Value::TRUE
        }
        let (eqv, equal) = (Intrinsic::Eqv, Intrinsic::Equal);
        let vectors = Vectors::new(mc);
        fn boxed<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Value<'gc> {
            Value::object(mc, crate::objects::Box::new(mc, value).unwrap())
        }
        fn big<'gc>(mc: &Mutation<'gc>, addend: i64) -> Value<'gc> {
            let nums = ragwort_types::num::Nums::new(mc);
            let (most, addend) = (nums.number(fix(Value::MAX_FIXNUM)).unwrap(), nums.number(fix(addend)).unwrap());
            ragwort_types::num::complex::add(&nums, most, addend).unwrap().value()
        }

        // Under `eqv?`, numbers are equivalent if they have identical exactness and numerical value, irrespective of whether they share the same heap object identity (e.g. comparing separately allocated bignums or flonums).
        assert!(test(cx, eqv, big(mc, 1), big(mc, 1)) && big(mc, 1) != big(mc, 1));
        assert!(!test(cx, eqv, big(mc, 1), big(mc, 2)));
        assert!(test(cx, eqv, Value::flonum(mc, 1e300).unwrap(), Value::flonum(mc, 1e300).unwrap()));
        assert!(!test(cx, eqv, fix(2), Value::flonum(mc, 2.0).unwrap()));
        assert!(!test(cx, equal, fix(2), Value::flonum(mc, 2.0).unwrap()));
        assert!(!test(cx, Intrinsic::Eq, big(mc, 1), big(mc, 1)));

        // A text has one flat string in the arena. So two strings that are made with the same characters are the same value, and are `eq?`, `eqv?` and `equal?`.
        let long = "a string too long to fit in a value";
        assert!(test(cx, eqv, text(mc, long), text(mc, long)) && test(cx, Intrinsic::Eq, text(mc, long), text(mc, long)));
        assert!(test(cx, equal, text(mc, long), text(mc, long)));
        // A string that was joined from two long parts is a rope: another object with the same characters as its flat string. It is `equal?` to that string, and not `eqv?`.
        let strings = ragwort_types::string::Strings::new(mc);
        let (head, tail) = ("x".repeat(600), "y".repeat(40));
        let joined = ragwort_types::string::concat(&strings, strings.string(text(mc, &head)).unwrap(), strings.string(text(mc, &tail)).unwrap()).unwrap().value();
        let whole = text(mc, &format!("{head}{tail}"));
        assert!(!test(cx, eqv, joined, whole) && test(cx, equal, joined, whole) && !test(cx, equal, joined, text(mc, &head)));
        assert!(!test(cx, equal, text(mc, long), text(mc, "a string too long to fit in a value!")));
        assert!(!test(cx, equal, text(mc, "1"), fix(1)));

        // Structural equality `equal?` compares pairs, mutable/immutable vectors, and boxes by recursively comparing their contents.
        fn list<'gc>(mc: &Mutation<'gc>, items: &[Value<'gc>]) -> Value<'gc> {
            Pairs::new(mc).list(items).unwrap()
        }
        fn tree<'gc>(mc: &Mutation<'gc>, long: &str, number: i64) -> Value<'gc> {
            list(mc, &[text(mc, long), list(mc, &[big(mc, number), boxed(mc, fix(1))]), Vectors::new(mc).from_slice(&[fix(number), Value::NULL]).unwrap().value(mc)])
        }
        assert!(!test(cx, eqv, tree(mc, long, 1), tree(mc, long, 1)));
        assert!(test(cx, equal, tree(mc, long, 1), tree(mc, long, 1)));
        assert!(!test(cx, equal, tree(mc, long, 1), tree(mc, long, 2)));
        assert!(!test(cx, equal, list(mc, &[fix(1), fix(2)]), list(mc, &[fix(1)])));
        let items = [fix(1), text(mc, long)];
        assert!(test(cx, equal, vectors.from_slice(&items).unwrap().value(mc), vectors.immutable_from_slice(&items).unwrap().value(mc)));
        assert!(!test(cx, equal, vectors.from_slice(&items).unwrap().value(mc), vectors.from_slice(&items[..1]).unwrap().value(mc)));
        assert!(!test(cx, equal, boxed(mc, fix(1)), list(mc, &[fix(1)])));
        assert!(!test(cx, equal, boxed(mc, fix(1)), boxed(mc, fix(2))));

        // Comparing long lists (200,000 items) and deep left-nested pair spines operates iteratively without consuming host Rust call stack frames.
        fn long_list<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
            Pairs::new(mc).list(&(0..200_000).map(fix).collect::<Vec<_>>()).unwrap()
        }
        assert!(test(cx, equal, long_list(mc), long_list(mc)));
        fn deep<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
            (0..200_000).fold(Value::NULL, |spine, _| Pairs::new(mc).cons(spine, Value::NULL).unwrap().value(mc))
        }
        assert!(test(cx, equal, deep(mc), deep(mc)));

        // Structural equality comparison properly terminates on cyclic structures (such as self-referential boxes and mutually referential vectors) rather than looping infinitely.
        fn cycle<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
            let cell = boxed(mc, Value::VOID);
            cell.downcast::<crate::objects::Box>(mc).unwrap().set_value(mc, cell);
            cell
        }
        assert!(test(cx, equal, cycle(mc), cycle(mc)));
        fn knot<'gc>(mc: &Mutation<'gc>, number: i64) -> Value<'gc> {
            let cell = boxed(mc, Value::VOID);
            cell.downcast::<crate::objects::Box>(mc).unwrap().set_value(mc, list(mc, &[fix(number), cell]));
            cell
        }
        assert!(test(cx, equal, knot(mc, 1), knot(mc, 1)));
        assert!(!test(cx, equal, knot(mc, 1), knot(mc, 2)));

        // Structural equality memoizes visits to shared subgraphs to avoid exponential traversal: a 64-level DAG of `(cons x x)` or `(vector x x)` containing 2^64 paths completes efficiently in linear time.
        fn shared<'gc>(mc: &Mutation<'gc>, leaf: Value<'gc>, vector: bool) -> Value<'gc> {
            (0..64).fold(leaf, |node, _| {
                if vector { Vectors::new(mc).immutable_from_slice(&[node, node]).unwrap().value(mc) } else { Pairs::new(mc).cons(node, node).unwrap().value(mc) }
            })
        }
        for vector in [false, true] {
            assert!(test(cx, equal, shared(mc, fix(1), vector), shared(mc, fix(1), vector)));
            assert!(!test(cx, equal, shared(mc, fix(1), vector), shared(mc, fix(2), vector)));
        }
        fn ring<'gc>(mc: &Mutation<'gc>, count: usize, last: i64) -> Value<'gc> {
            let links: Vec<_> = (0..count).map(|_| Vectors::new(mc).make(2, fix(0)).unwrap()).collect();
            for (i, link) in links.iter().enumerate() {
                link.items(mc).set(mc, 0, links[(i + 1) % count].value(mc));
                link.items(mc).set(mc, 1, fix(if i == count - 1 { last } else { 0 }));
            }
            links[0].value(mc)
        }
        assert!(test(cx, equal, ring(mc, 3000, 1), ring(mc, 3000, 1)));
        assert!(!test(cx, equal, ring(mc, 2, 1), ring(mc, 4, 1)));
        assert!(test(cx, equal, ring(mc, 3, 0), ring(mc, 5, 0)));
        assert!(!test(cx, equal, ring(mc, 3000, 1), ring(mc, 3000, 2)));

        // Equality comparisons consume 1 unit of fuel for every 1,024 values visited (accounting for pair container nodes as well as element values).
        fn spent<'gc>(cx: &mut Context<'_, 'gc>, left: Value<'gc>, right: Value<'gc>) -> u64 {
            cx.fuel = Fuel { run: 100, rest: 0 };
            test(cx, Intrinsic::Equal, left, right);
            100 - cx.fuel.left()
        }
        let (items, short): (Vec<_>, Vec<_>) = ((0..10_240).map(fix).collect(), (0..100).map(fix).collect());
        fn vector<'gc>(mc: &Mutation<'gc>, items: &[Value<'gc>]) -> Value<'gc> {
            Vectors::new(mc).from_slice(items).unwrap().value(mc)
        }
        assert_eq!(spent(cx, vector(mc, &items), vector(mc, &items)), 10);
        assert_eq!(spent(cx, list(mc, &items), list(mc, &items)), 20);
        assert_eq!(spent(cx, list(mc, &short), list(mc, &short)), 0);

        // Once the primary run fuel budget is exhausted, fuel is drawn from the reserve budget (`fuel.rest`); if both are depleted, execution stops with `Fault::OutOfFuel`.
        cx.fuel = Fuel { run: 3, rest: 20 };
        test(cx, equal, vector(mc, &items), vector(mc, &items));
        assert_eq!(cx.fuel, Fuel { run: 0, rest: 13 });
        cx.fuel = Fuel { run: 3, rest: 6 };
        frame.set(27, vector(mc, &items));
        frame.set(28, vector(mc, &items));
        assert_eq!(Op::CallIntrinsic { base: 27, args: 2, intrinsic: equal }.step(cx), Err(Fault::OutOfFuel));
        cx.fuel = Fuel { run: u64::MAX, rest: 0 };

        frame.set(29, boxed(mc, fix(1)));
        frame.set(30, list(mc, &[]));
        Op::CallIntrinsic { base: 29, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
        assert_eq!(cx.acc, Value::TRUE);
        Op::CallIntrinsic { base: 30, args: 1, intrinsic: Intrinsic::IsBox }.step(cx).unwrap();
        assert_eq!(cx.acc, Value::FALSE);
    });
}

#[test]
fn a_load_takes_exactly_one_value() {
    with_frame(|cx| {
        let (mc, frame) = (cx.mc, cx.frame);
        // Every instruction is executed through this one `step` function, so the test contains a single copy of the inlined `Op::step`.
        fn step(cx: &mut Context<'_, '_>, op: Op) -> Result<Control, Fault> {
            op.step(cx)
        }
        fn call(cx: &mut Context<'_, '_>, base: u8, args: u8, intrinsic: Intrinsic) -> Result<Control, Fault> {
            step(cx, Op::CallIntrinsic { base, args, intrinsic })
        }
        (0..3).for_each(|i| frame.set(20 + i, fix(i64::from(i) + 10)));
        // `values` with one argument returns that argument, and a load accepts it. An intrinsic can return only one value, so any other number of arguments fails.
        call(cx, 20, 1, Intrinsic::Values).unwrap();
        assert_eq!(cx.acc, fix(10));
        step(cx, Op::LoadAcc { dst: 30 }).unwrap();
        assert_eq!(frame.get(30), fix(10));
        assert_eq!(call(cx, 20, 3, Intrinsic::Values), Err(Fault::ValueCount));
        assert_eq!(call(cx, 20, 0, Intrinsic::Values), Err(Fault::ValueCount));
        // A return of several values, or of no values, leaves the marker in the accumulator and the list of values beside it. A load fails in both cases.
        assert_eq!(step(cx, Op::ReturnValues { src: 20, count: 3 }), Ok(Control::Return));
        assert_eq!((cx.acc, Pairs::new(mc).elements(cx.values).collect::<Vec<_>>()), (Value::VALUES, vec![fix(10), fix(11), fix(12)]));
        assert_eq!(step(cx, Op::LoadAcc { dst: 30 }), Err(Fault::ValueCount));
        assert_eq!(step(cx, Op::ReturnValues { src: 20, count: 0 }), Ok(Control::Return));
        assert_eq!((cx.acc, cx.values), (Value::VALUES, Value::NULL));
        assert_eq!(step(cx, Op::LoadAcc { dst: 30 }), Err(Fault::ValueCount));
        assert_eq!(frame.get(30), fix(10));
        // A return of exactly one value, spread or not, leaves that value in the accumulator.
        assert_eq!(step(cx, Op::ReturnValues { src: 21, count: 1 }), Ok(Control::Return));
        assert_eq!(cx.acc, fix(11));
        frame.set(23, Pairs::new(mc).list(&[fix(7)]).unwrap());
        assert_eq!(step(cx, Op::ReturnSpread { base: 23, args: 1 }), Ok(Control::Return));
        assert_eq!(cx.acc, fix(7));
        // A spread return puts the register values before the elements of the list. The list must be a proper list.
        assert_eq!(step(cx, Op::ReturnSpread { base: 22, args: 2 }), Ok(Control::Return));
        assert_eq!((cx.acc, Pairs::new(mc).elements(cx.values).collect::<Vec<_>>()), (Value::VALUES, vec![fix(12), fix(7)]));
        frame.set(23, fix(5));
        assert_eq!(step(cx, Op::ReturnSpread { base: 22, args: 2 }), Err(Fault::WrongType));
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
        // Constructs a binary pair tree of depth 4 where each leaf string encodes its traversal path in `c...r` notation (e.g. "caddar").
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
        // Bitfield operations specifying large field widths on small fixnum values incur no additional fuel cost beyond the baseline instruction call.
        let mut fuel = Fuel { run: 100, rest: 0 };
        assert_eq!(Intrinsic::BitField.run(mc, &[fix(5), fix(0), bits], &mut fuel), Ok(fix(5)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(2), fix(0), bits], &mut fuel), Ok(fix(2)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(0), bits, fix(25_600_000)], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::BitFieldReplace.run(mc, &[fix(1), fix(-1), bits, bits], &mut fuel), Ok(fix(1)));
        assert_eq!(Intrinsic::ArithmeticShift.run(mc, &[fix(0), bits], &mut fuel), Ok(fix(0)));
        assert_eq!(fuel.left(), 100);
        // Shifting -1 left by a large bit count allocates a bignum proportional in size to the shift amount, consuming fuel according to allocation size and triggering `Fault::OutOfFuel`.
        assert_eq!(Intrinsic::ArithmeticShift.run(mc, &[fix(-1), bits], &mut fuel), Err(Fault::OutOfFuel));
    });
}

fn run<'gc>(mc: &Mutation<'gc>, op: Intrinsic, args: &[Value<'gc>]) -> Result<Value<'gc>, Fault> {
    op.run(mc, args, &mut Fuel { run: u64::MAX, rest: 0 })
}

/// A type predicate with a sole value holds for that value and for nothing else, and the value leads back to the predicate.
#[test]
fn predicates_that_hold_for_one_value_name_that_value() {
    let sole: Vec<Intrinsic> = Intrinsic::ALL.iter().copied().filter(|predicate| predicate.sole_value().is_some()).collect();
    assert_eq!(sole, [Intrinsic::IsNull, Intrinsic::IsNil, Intrinsic::IsNone]);
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let others = [Value::FALSE, Value::TRUE, Value::VOID, Value::fixnum(0).unwrap()];
        for &predicate in &sole {
            let value = predicate.sole_value().unwrap();
            assert!(predicate.is_type_predicate() && predicate.is_pure_foldable(), "{predicate:?}");
            assert_eq!(Intrinsic::predicate_of(value), Some(predicate));
            assert_eq!(run(mc, predicate, &[value]), Ok(Value::TRUE), "{predicate:?}");
            for &other in &sole {
                if other != predicate {
                    assert_eq!(run(mc, predicate, &[other.sole_value().unwrap()]), Ok(Value::FALSE), "{predicate:?} of the value of {other:?}");
                }
            }
            for other in others {
                assert_eq!(run(mc, predicate, &[other]), Ok(Value::FALSE), "{predicate:?}");
            }
        }
        // No predicate is named for a value that others share a test with: `not` holds for `#f`, `#nil` and `#none`.
        for other in others {
            assert_eq!(Intrinsic::predicate_of(other), None);
        }
    });
}

#[test]
fn intrinsics_on_the_task_need_one_and_are_never_folded_or_moved() {
    let dynamic: Vec<Intrinsic> = Intrinsic::ALL.iter().copied().filter(|i| i.is_dynamic()).collect();
    assert_eq!(dynamic.len(), 6);
    for &i in &dynamic {
        assert!(!i.is_pure_foldable() && !i.is_reorderable() && !i.is_type_predicate() && !i.is_internal(), "{i:?}");
        assert!(i.arity().is_some(), "{i:?}");
    }
    assert!(!Intrinsic::SetWinders.is_discardable() && !Intrinsic::FrameMarks.is_discardable() && Intrinsic::MarkValue.is_discardable());
    // Asserts self-consistency of intrinsic metadata properties: type predicates are unary and discardable (pure); discardable operations are reorderable unless they depend dynamically on the task state.
    for &i in Intrinsic::ALL {
        if i.is_type_predicate() {
            assert!(i.arity() == Some(1) && i.is_discardable(), "{i:?}");
        }
        if i.is_discardable() {
            assert_eq!(i.is_reorderable(), !i.is_dynamic(), "{i:?}");
        }
        if i.is_commutative_binary() {
            assert!(i.arity().is_none_or(|n| n == 2), "{i:?}");
        }
    }
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        for &i in &dynamic {
            let args = vec![Value::NULL; usize::from(i.arity().unwrap())];
            assert_eq!(run(mc, i, &args), Err(Fault::Malformed), "{i:?}");
        }
    });
}

/// Tests struct type inheritance and equality: a struct instance satisfies type predicates for its concrete type and all ancestor supertypes; instances of the same struct type are `equal?` if their corresponding fields are `equal?`, unless the type was declared with identity equality, in which case instances are only equal to themselves.
#[test]
fn structs_are_of_their_types_and_equal_by_their_fields_or_themselves() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let pairs = Pairs::new(mc);
        fn symbol<'gc>(mc: &Mutation<'gc>, name: &str) -> Value<'gc> {
            ragwort_types::symbol::Symbols::of_arena(mc).unwrap().intern_str(&Strings::new(mc), name).unwrap().value(mc)
        }
        fn names<'gc>(mc: &Mutation<'gc>, names: &[&str]) -> Value<'gc> {
            Pairs::new(mc).list(&names.iter().map(|name| symbol(mc, name)).collect::<Vec<_>>()).unwrap()
        }
        // Generates field mutability flags for struct type definition (1 for mutable/settable, 0 for immutable).
        fn flags<'gc>(mc: &Mutation<'gc>, count: usize, mutable: bool) -> Value<'gc> {
            Pairs::new(mc).list(&vec![fix(i64::from(mutable)); count]).unwrap()
        }
        let (plain, identity, sealed) = (fix(0), fix(1), fix(2));
        let point = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "point"), Value::FALSE, names(mc, &["x", "y"]), flags(mc, 2, true), plain]).unwrap();
        let point3 = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "point3"), point, names(mc, &["z"]), flags(mc, 1, true), plain]).unwrap();
        let point4 = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "point4"), point3, names(mc, &["w"]), flags(mc, 1, false), plain]).unwrap();
        let other = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "point"), Value::FALSE, names(mc, &["x", "y"]), flags(mc, 2, false), plain]).unwrap();
        let p = run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap();
        let q = run(mc, Intrinsic::MakeStruct, &[point4, fix(1), fix(2), fix(3), fix(4)]).unwrap();
        // Validates `struct-derived-from?`: verifies that an instance matches its concrete type descriptor and all ancestor supertypes, but does not match unrelated types or non-struct values.
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
        // Fields declared immutable cannot be modified via `struct-set!`, whether targeted through the concrete type or any of its supertypes.
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
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "bad"), fix(1), Value::NULL, Value::NULL, plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "bad"), Value::FALSE, pairs.list(&[fix(1)]).unwrap(), flags(mc, 1, false), plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "bad"), Value::FALSE, names(mc, &["x", "y"]), flags(mc, 1, false), plain]), Err(Fault::WrongType), "a flag for each field");
        let same = run(mc, Intrinsic::MakeStruct, &[point, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let alike = run(mc, Intrinsic::MakeStruct, &[point, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let elsewhere = run(mc, Intrinsic::MakeStruct, &[other, fix(1), pairs.list(&[fix(2)]).unwrap()]).unwrap();
        let up = run(mc, Intrinsic::MakeStruct, &[point3, fix(1), pairs.list(&[fix(2)]).unwrap(), fix(3)]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[same, alike]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::Eqv, &[same, alike]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[same, p]), Ok(Value::FALSE));
        assert_eq!(run(mc, Intrinsic::Equal, &[same, elsewhere]), Ok(Value::FALSE), "another type of the same name");
        assert_eq!(run(mc, Intrinsic::Equal, &[same, up]), Ok(Value::FALSE), "a subtype");
        // Verifies cycle handling in struct equality: mutually recursive and self-referential structs are compared for structural equality without infinite recursion.
        let (a, b) = (run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap(), run(mc, Intrinsic::MakeStruct, &[point, fix(1), fix(2)]).unwrap());
        run(mc, Intrinsic::StructSet, &[a, point, fix(1), a]).unwrap();
        run(mc, Intrinsic::StructSet, &[b, point, fix(1), b]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[a, b]), Ok(Value::TRUE));

        let listed = run(mc, Intrinsic::StructFields, &[point4]).unwrap();
        assert_eq!(run(mc, Intrinsic::Equal, &[listed, names(mc, &["x", "y", "z", "w"])]), Ok(Value::TRUE));
        assert_eq!(run(mc, Intrinsic::StructFields, &[p]), Err(Fault::WrongType));

        // Struct instances of types declared with the identity flag (and any subtypes derived from them) compare `equal?` solely via object identity rather than by comparing field values.
        let session = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "session"), Value::FALSE, names(mc, &["token", "user"]), flags(mc, 2, true), identity]).unwrap();
        let admin = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "admin"), session, names(mc, &[]), flags(mc, 0, false), plain]).unwrap();
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

        // Tests `struct-type`: returns the exact struct type descriptor that created the instance, and asserts that non-struct inputs trigger type faults.
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

        // Asserts that extending a sealed struct type or passing unrecognized property flags to `make-struct-type` fails with a type fault.
        let last = run(mc, Intrinsic::MakeStructType, &[symbol(mc, "last"), point, names(mc, &["z"]), flags(mc, 1, false), sealed]).unwrap();
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "more"), last, names(mc, &[]), flags(mc, 0, false), plain]), Err(Fault::WrongType));
        assert_eq!(run(mc, Intrinsic::IsStructDerivedFrom, &[run(mc, Intrinsic::MakeStruct, &[last, fix(1), fix(2), fix(3)]).unwrap(), point]), Ok(Value::TRUE));
        for bad in [fix(4), fix(-1), Value::FALSE] {
            assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "bad"), Value::FALSE, names(mc, &[]), flags(mc, 0, false), bad]), Err(Fault::WrongType));
        }
        assert_eq!(run(mc, Intrinsic::MakeStructType, &[symbol(mc, "bad"), Value::FALSE, names(mc, &["x"]), pairs.list(&[fix(2)]).unwrap(), plain]), Err(Fault::WrongType));

    });
}

/// Verifies that an external bytevector backed by host-owned memory supports standard bytevector read operations, as well as write operations when backed by a mutable buffer.
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
        assert_eq!(Intrinsic::IsBoolean.run(mc, &[Value::NULL], &mut fuel), Ok(Value::FALSE));
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
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, Value::NULL, Value::FALSE, fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[fix(0), fix(0), Value::FALSE, fix(1)], &mut fuel), Err(Fault::WrongType));
        assert_eq!(Intrinsic::BytevectorSet.run(mc, &[bytes, fix(0), fix(256), Value::FALSE, fix(1)], &mut fuel), Err(Fault::OutOfRange));
        // Tests reading a 2-byte signed integer across word boundaries in big-endian byte order.
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7), Value::TRUE, fix(2)], &mut fuel), Ok(fix(0x08ff)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(7), Value::FALSE, fix(-2)], &mut fuel), Ok(fix(-248)));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::FALSE, fix(0)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::FALSE, fix(9)], &mut fuel), Err(Fault::OutOfRange));
        assert_eq!(Intrinsic::BytevectorRef.run(mc, &[bytes, fix(0), Value::NULL, fix(1)], &mut fuel), Err(Fault::WrongType));
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
        fn spent<'gc>(mc: &Mutation<'gc>, op: Intrinsic, args: &[Value<'gc>]) -> u64 {
            let mut fuel = Fuel { run: 100, rest: 0 };
            op.run(mc, args, &mut fuel).unwrap();
            100 - fuel.left()
        }
        // String comparison operations (`string=?`, `string<?`, `string>=?`) consume 1 unit of fuel per 1,024 characters compared up to the length of the shorter string.
        let (long, other) = (text(mc, &"a".repeat(10_240)), text(mc, &"a".repeat(10_240)));
        for op in [Intrinsic::StringEq, Intrinsic::StringLt, Intrinsic::StringGe] {
            assert_eq!(spent(mc, op, &[long, other]), 10, "{op:?}");
        }
        assert_eq!(spent(mc, Intrinsic::StringEq, &[long, other, long]), 20);
        assert_eq!(spent(mc, Intrinsic::StringEq, &[long, text(mc, "a")]), 0);
        let mut fuel = Fuel { run: 3, rest: 0 };
        assert_eq!(Intrinsic::StringEq.run(mc, &[long, other], &mut fuel), Err(Fault::OutOfFuel));
    });
}
