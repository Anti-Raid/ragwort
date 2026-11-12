use std::sync::atomic::{AtomicU32, Ordering};

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Arena, Gc, Mutation, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_vm::Intrinsic::{Add, Car, Cons, Eq, FrameMarks, MakeBox, MakePromptTag, MarkValue, ModuleRef, Not, Running, SetBox, SetWinders, Unbox};
use ragwort_vm::frame::{ARGS, MAX_PARAMS};
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields};
use ragwort_vm::{Fault, HostDef, Intrinsic, MIN_SEGMENT, Machine, Op, Outcome, Purity, Request};

use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;

use super::*;
use crate::module::{Import, Imports, ModuleBuilder, ModuleError, Unusable};

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn q<'gc>(n: i64) -> Core<'gc> {
    Core::Quote(fix(n))
}

fn var<'gc>(v: u32) -> Core<'gc> {
    Core::Ref(Place::Local(Var(v)))
}

fn prim<'gc>(i: Intrinsic, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::Intrinsic(Prim::Intrinsic(i), args)
}

fn add<'gc>(a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    prim(Add, vec![a, b])
}

fn eq<'gc>(a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    prim(Eq, vec![a, b])
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

/// Builds a sequence that binds `a` to unused variable `v`, then evaluates `b`.
fn seq<'gc>(v: u32, a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    let_(vec![(v, a)], b)
}

/// Builds a lambda with an ID distinct from every other test lambda.
fn lambda<'gc>(params: &[u32], rest: Option<u32>, body: Core<'gc>) -> Core<'gc> {
    optional_lambda(params, 0, rest, body)
}

/// Builds a lambda with `optional` trailing optional parameters.
fn optional_lambda<'gc>(params: &[u32], optional: u32, rest: Option<u32>, body: Core<'gc>) -> Core<'gc> {
    static NEXT: AtomicU32 = AtomicU32::new(0);
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    Core::Lambda(Lambda { id, params: params.iter().map(|&v| Var(v)).collect(), optional, rest: rest.map(Var), body: Box::new(body), name: None, at: None })
}

fn app<'gc>(f: Core<'gc>, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::App(Box::new(f), args)
}

fn set<'gc>(v: u32, value: Core<'gc>) -> Core<'gc> {
    Core::Set(Place::Local(Var(v)), Box::new(value))
}

/// Compiles and runs the expression from `build`, then passes its result or fault to `check`.
fn eval(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>, check: impl for<'gc> FnOnce(&Mutation<'gc>, Result<Value<'gc>, Fault>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let thunk = compile(mc, Some(hosting(mc)), &build(mc)).unwrap();
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let result = loop {
            match machine.run(mc).unwrap() {
                Outcome::Paused => {}
                Outcome::Yielded(_) | Outcome::Deferred(_) => panic!("yielded"),
                Outcome::Done(value) => break Ok(value),
                Outcome::Raised(raised) => break Err(raised.downcast::<Condition>(mc).unwrap().failure(mc).unwrap().fault),
            }
        };
        check(mc, result);
    });
}

/// Compiles and runs the expression from `build`, returning its fixnum result.
fn number(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> Result<i64, Fault> {
    let mut got = Err(Fault::Malformed);
    eval(build, |_, result| got = result.map(|v| v.as_fixnum().unwrap()));
    got
}

fn items<'gc>(mc: &Mutation<'gc>, mut v: Value<'gc>) -> Vec<i64> {
    let mut out = Vec::new();
    while let Some(pair) = Pair::of(v) {
        out.push(pair.head(mc).as_fixnum().unwrap());
        v = pair.tail(mc);
    }
    assert_eq!(v, Value::NIL);
    out
}

fn error(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> CompileError {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| compile(mc, Some(hosting(mc)), &build(mc)).unwrap_err())
}

#[test]
fn quotes_ifs_and_intrinsics() {
    assert_eq!(number(|_| when(eq(q(1), q(1)), add(q(1), q(2)), q(0))), Ok(3));
    assert_eq!(number(|_| when(Core::Quote(Value::FALSE), q(1), q(2))), Ok(2));
    // A quoted datum is the object itself.
    eval(
        |mc| {
            let list = Pairs::new(mc).list(&[fix(1), fix(2), fix(3)]).unwrap();
            prim(Eq, vec![Core::Quote(list), Core::Quote(list)])
        },
        |_, result| assert_eq!(result, Ok(Value::TRUE)),
    );
    eval(|mc| Core::Quote(Pairs::new(mc).list(&[fix(1), fix(2)]).unwrap()), |mc, result| assert_eq!(items(mc, result.unwrap()), [1, 2]));
}

#[test]
fn lets_and_assignments_of_registers() {
    // (let ((x 1) (y 2)) (set! x (+ x y)) (+ x y))
    assert_eq!(number(|_| let_(vec![(0, q(1)), (1, q(2))], seq(2, set(0, add(var(0), var(1))), add(var(0), var(1))))), Ok(5));
    // (let ((x 1)) (set! x 2)) is void.
    eval(|_| let_(vec![(0, q(1))], set(0, q(2))), |_, result| assert_eq!(result, Ok(Value::VOID)));
    // (let ((f (lambda (x) (+ x 1)))) (+ (f 1) (f 2))): calls in arguments.
    assert_eq!(number(|_| let_(vec![(0, lambda(&[1], None, add(var(1), q(1))))], add(app(var(0), vec![q(1)]), app(var(0), vec![q(2)])))), Ok(5));
}

#[test]
fn closures_share_boxes() {
    // (let ((n 0)) (let ((inc (lambda () (set! n (+ n 1)) n))) (inc) (inc) (inc)))
    fn inc<'gc>() -> Core<'gc> {
        lambda(&[], None, seq(2, set(0, add(var(0), q(1))), var(0)))
    }
    assert_eq!(number(|_| let_(vec![(0, q(0))], let_(vec![(1, inc())], seq(3, app(var(1), vec![]), seq(4, app(var(1), vec![]), app(var(1), vec![])))))), Ok(3));

    // ((lambda (x) (let ((get (lambda () x))) (set! x 41) (+ (get) 1))) 0): box the captured parameter
    // on entry so the closure observes later assignments.
    fn get<'gc>() -> Core<'gc> {
        lambda(&[0], None, let_(vec![(1, lambda(&[], None, var(0)))], seq(2, set(0, q(41)), add(app(var(1), vec![]), q(1)))))
    }
    assert_eq!(number(|_| app(get(), vec![q(0)])), Ok(42));

    // ((((lambda (x) (lambda () (lambda () x))) 7))): an upvalue's upvalue.
    fn nested<'gc>() -> Core<'gc> {
        lambda(&[0], None, lambda(&[], None, lambda(&[], None, var(0))))
    }
    assert_eq!(number(|_| app(app(app(nested(), vec![q(7)]), vec![]), vec![])), Ok(7));
}

#[test]
fn letrec_and_tail_calls() {
    // (letrec ((even? (lambda (n) (if (eq? n 0) #t (odd? (+ n -1)))))
    //          (odd? (lambda (n) (if (eq? n 0) #f (even? (+ n -1))))))
    //   (even? 100001))
    eval(
        |_| {
            let even = lambda(&[2], None, when(eq(var(2), q(0)), Core::Quote(Value::TRUE), app(var(1), vec![add(var(2), q(-1))])));
            let odd = lambda(&[3], None, when(eq(var(3), q(0)), Core::Quote(Value::FALSE), app(var(0), vec![add(var(3), q(-1))])));
            letrec(vec![(0, even), (1, odd)], app(var(0), vec![q(100_001)]))
        },
        |_, result| assert_eq!(result, Ok(Value::FALSE)),
    );

    // (letrec ((loop (lambda (n acc) (if (eq? n 0) acc (loop (+ n -1) (+ acc 2)))))) (loop 1000000 0))
    assert_eq!(
        number(|_| {
            let looping = lambda(&[1, 2], None, when(eq(var(1), q(0)), var(2), app(var(0), vec![add(var(1), q(-1)), add(var(2), q(2))])));
            letrec(vec![(0, looping)], app(var(0), vec![q(1_000_000), q(0)]))
        }),
        Ok(2_000_000)
    );

    // (letrec ((sum (lambda (n) (if (eq? n 0) 0 (+ n (sum (+ n -1))))))) (sum 10000)), deep enough
    // to cross segments.
    assert_eq!(
        number(|_| {
            let sum = lambda(&[1], None, when(eq(var(1), q(0)), q(0), add(var(1), app(var(0), vec![add(var(1), q(-1))]))));
            letrec(vec![(0, sum)], app(var(0), vec![q(10_000)]))
        }),
        Ok(50_005_000)
    );
}

/// Builds `(lambda (a) (+ (+ a x) (+ (+ a a) (+ x x))))` with `x` as variable 0. The body exceeds
/// the multi-use inlining budget.
fn big<'gc>(a: u32) -> Core<'gc> {
    lambda(&[a], None, add(add(var(a), var(0)), add(add(var(a), var(a)), add(var(0), var(0)))))
}

#[test]
fn lambdas_only_called_in_tail_position_are_jumps() {
    // Run `(f 0)`, `(f 1)`, and `(f 2)` for the generated recursive `f`, encode their results in base
    // 1000, and count generated closures.
    fn check(name: &str, body: impl for<'gc> Fn(&Mutation<'gc>) -> Core<'gc>, expect: i64, closures: usize) {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| {
            let call = |n| app(var(9), vec![q(n)]);
            let all = add(prim(Intrinsic::Mul, vec![call(0), q(1_000_000)]), add(prim(Intrinsic::Mul, vec![call(1), q(1000)]), call(2)));
            let thunk = compile(mc, None, &letrec(vec![(9, lambda(&[0], None, body(mc)))], all)).unwrap();
            let ops = all_ops(mc, thunk);
            let made = ops.iter().filter(|op| matches!(op, Op::NewClosure { .. })).count();
            assert_eq!(made, closures, "{name}: {ops:?}");
            let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
            let Outcome::Done(value) = machine.run(mc).unwrap() else { panic!("{name}") };
            assert_eq!(value.as_fixnum(), Some(expect), "{name}");
        });
    }
    // `(let ((k big)) (if (eq? x 0) (k 1) (if (eq? x 1) (k 2) other)))`; `(k a)` is `3a + 3x`.
    fn branches<'gc>(k: Core<'gc>, other: Core<'gc>) -> Core<'gc> {
        let_(vec![(1, k)], when(eq(var(0), q(0)), app(var(1), vec![q(1)]), when(eq(var(0), q(1)), app(var(1), vec![q(2)]), other)))
    }
    check("tail", |_| branches(big(2), q(5)), 3_009_005, 0);
    // The calls are in tail position relative to the `let`, not the enclosing function.
    check("in an argument", |_| add(q(100), branches(big(2), q(5))), 103_109_105, 0);
    // `(let loop ((n x)) (let ((k (lambda (m) (if (eq? m 0) 7 (loop (+ m -1)))))) (if (eq? n 0)
    // (k 0) (k n))))`: a loop's body jumps to a join, and the join to the loop.
    check(
        "with a loop",
        |_| {
            let k = lambda(&[3], None, when(eq(var(3), q(0)), q(7), app(var(4), vec![add(var(3), q(-1))])));
            let body = let_(vec![(5, k)], when(eq(var(6), q(0)), app(var(5), vec![q(0)]), app(var(5), vec![var(6)])));
            letrec(vec![(4, lambda(&[6], None, body))], app(var(4), vec![var(0)]))
        },
        7_007_007,
        0,
    );
    // `(let ((k big)) (+ 100 (if ...)))`: calls share the `if`'s tail context, so place the join at the
    // `if`, not at the `let`.
    check("under an argument", |_| let_(vec![(1, big(2))], add(q(100), when(eq(var(0), q(0)), app(var(1), vec![q(1)]), when(eq(var(0), q(1)), app(var(1), vec![q(2)]), q(5))))), 103_109_105, 0);
    // `(let loop ((n 3) (acc 0)) (if (eq? n 0) acc (loop (+ n -1) (+ acc (let ((k big)) (if ...))))))`.
    check(
        "in a loop's argument",
        |_| {
            let k = let_(vec![(1, big(2))], when(eq(var(0), q(0)), app(var(1), vec![q(1)]), when(eq(var(0), q(1)), app(var(1), vec![q(2)]), q(5))));
            let body = when(eq(var(3), q(0)), var(4), app(var(6), vec![add(var(3), q(-1)), add(var(4), k)]));
            letrec(vec![(6, lambda(&[3, 4], None, body))], app(var(6), vec![q(3), q(0)]))
        },
        9_027_015,
        0,
    );
    // Calls in separate arguments have different return destinations.
    check("in two arguments", |_| let_(vec![(1, big(2))], add(app(var(1), vec![q(1)]), app(var(1), vec![q(2)]))), 9_015_021, 1);
    // `(let ((k big)) (let ((g (lambda (z) (if (eq? z c) (k 1) (k 2)))) (h 0)) (set! h g) (+ (h 0)
    // (* 10 (h 1)))))`: `k`'s code can go in `g`, which then captures what it uses instead.
    fn inside<'gc>(k: Core<'gc>, c: Core<'gc>) -> Core<'gc> {
        let g = lambda(&[4], None, when(eq(var(4), c), app(var(1), vec![q(1)]), app(var(1), vec![q(2)])));
        let calls = add(app(var(6), vec![q(0)]), prim(Intrinsic::Mul, vec![app(var(6), vec![q(1)]), q(10)]));
        let_(vec![(1, k)], let_(vec![(3, g), (6, q(0))], seq(10, set(6, var(3)), calls)))
    }
    check("in the lambda that calls it", |_| inside(big(2), q(0)), 63_096_129, 1);
    // `g` already captures `x`, so moving the join does not add that capture.
    check("in a lambda capturing what it does", |_| inside(big(2), var(0)), 63_069_132, 1);
    // With `(let ((w (+ x 1))) ...)` and `k` also using `w`, moving `k` would replace one capture with
    // two. Keep the closure.
    check(
        "not in a lambda that'd capture more",
        |_| {
            let k = lambda(&[2], None, add(add(add(var(2), var(0)), add(var(2), var(2))), add(add(var(0), var(0)), var(5))));
            let_(vec![(5, add(var(0), q(1)))], inside(k, q(0)))
        },
        74_118_162,
        2,
    );
    // Keep a closure when the lambda escapes or lacks a common tail context.
    // `(let ((y 0)) (set! y k) (y 2))`.
    check("escaping", |_| branches(big(2), let_(vec![(3, q(0))], seq(10, set(3, var(1)), app(var(3), vec![q(2)])))), 3_009_012, 1);
    check("not in tail position", |_| branches(big(2), add(q(1), app(var(1), vec![q(2)]))), 3_009_013, 1);
}

#[test]
fn letrec_groups_only_called_in_tail_position_are_jumps() {
    // Runs the generated program through pauses and checks its closure-allocation and call counts.
    fn check(name: &str, build: impl for<'gc> Fn(&Mutation<'gc>) -> Core<'gc>, expect: i64, closures: usize, calls: bool) {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| {
            let thunk = compile(mc, None, &build(mc)).unwrap();
            let ops = all_ops(mc, thunk);
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::NewClosure { .. })).count(), closures, "{name}: {ops:?}");
            assert_eq!(ops.iter().any(|op| matches!(op, Op::Call { .. } | Op::TailCall { .. })), calls, "{name}: {ops:?}");
            assert!(!ops.contains(&Op::Jump { offset: 0 }), "{name}: {ops:?}");
            let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
            let value = loop {
                match machine.run(mc).unwrap() {
                    Outcome::Paused => {}
                    Outcome::Done(value) => break value,
                    _ => panic!("{name}"),
                }
            };
            assert_eq!(value.as_fixnum(), Some(expect), "{name}");
        });
    }
    // `(lambda (n) (if (eq? n 0) done (next (+ n -1))))`, with `n` variable `v`.
    fn state<'gc>(v: u32, done: i64, next: u32) -> Core<'gc> {
        lambda(&[v], None, when(eq(var(v), q(0)), q(done), app(var(next), vec![add(var(v), q(-1))])))
    }
    check("even and odd", |_| letrec(vec![(0, state(2, 1, 1)), (1, state(3, 0, 0))], app(var(0), vec![q(1_000_001)])), 0, 0, false);
    // Run a three-state cycle, a -> b -> c -> a, for one million steps starting at a; the final state
    // is b.
    check("three states", |_| letrec(vec![(0, state(3, 1, 1)), (1, state(4, 2, 2)), (2, state(5, 3, 0))], app(var(0), vec![q(1_000_000)])), 2, 0, false);
    // `(+ 100 (letrec ((lp (lambda (n acc) (if (eq? n 0) (+ acc x) ...)))) (if (eq? x 1) (lp 10 0)
    // (lp 3 0))))`, a loop started from two places, for x of 1 and of 0. It captures `x`, so it'd
    // be a closure made each time if it weren't a join.
    check(
        "a loop started twice",
        |_| {
            let lp = lambda(&[2, 3], None, when(eq(var(2), q(0)), add(var(3), var(0)), app(var(1), vec![add(var(2), q(-1)), add(var(3), var(2))])));
            let started = letrec(vec![(1, lp)], when(eq(var(0), q(1)), app(var(1), vec![q(10), q(0)]), app(var(1), vec![q(3), q(0)])));
            let f = lambda(&[0], None, add(q(100), started));
            letrec(vec![(9, f)], add(prim(Intrinsic::Mul, vec![app(var(9), vec![q(1)]), q(1000)]), app(var(9), vec![q(0)])))
        },
        156_106,
        0,
        true,
    );
    // `(let loop ((x 0)) (if (eq? x 10) x (let ((w (lambda (y) (let ((u (lambda (z) (loop (+ z
    // 1))))) (if (eq? y 3) (u (+ y 1)) (u y)))))) (if (eq? x 5) (w (+ x 1)) (w x)))))`: the loop is
    // called in `u`'s code, which goes in `w`'s, which goes in the loop's.
    check(
        "a loop called from a join in a join",
        |_| {
            // `(+ (+ z z) (+ z 1) (* (+ z z) -1))`, `(+ z 1)` too big to inline.
            let next = add(add(add(var(6), var(6)), add(var(6), q(1))), prim(Intrinsic::Mul, vec![add(var(6), var(6)), q(-1)]));
            let u = lambda(&[6], None, app(var(1), vec![next]));
            let w = lambda(&[4], None, let_(vec![(5, u)], when(eq(var(4), q(3)), app(var(5), vec![add(var(4), q(1))]), app(var(5), vec![var(4)]))));
            let body = when(eq(var(2), q(10)), var(2), let_(vec![(3, w)], when(eq(var(2), q(5)), app(var(3), vec![add(var(2), q(1))]), app(var(3), vec![var(2)]))));
            letrec(vec![(1, lambda(&[2], None, body))], app(var(1), vec![q(0)]))
        },
        10,
        0,
        false,
    );
    // If any function in a recursive group escapes, retain the group's closures.
    check(
        "escaping",
        |_| letrec(vec![(0, state(2, 1, 1)), (1, state(3, 0, 0))], when(prim(Intrinsic::IsProcedure, vec![var(1)]), app(var(0), vec![q(10)]), q(5))),
        1,
        1,
        true,
    );
    // Nontail recursion remains a call.
    check(
        "not in tail position",
        |_| letrec(vec![(0, lambda(&[1], None, when(eq(var(1), q(0)), q(0), add(var(1), app(var(0), vec![add(var(1), q(-1))])))))], app(var(0), vec![q(100)])),
        5050,
        0,
        true,
    );
}

#[test]
fn rest_parameters() {
    // ((lambda (a . rest) (cons a rest)) 1 2 3)
    eval(|_| app(lambda(&[0], Some(1), prim(Cons, vec![var(0), var(1)])), vec![q(1), q(2), q(3)]), |mc, result| assert_eq!(items(mc, result.unwrap()), [1, 2, 3]));
    // (((lambda (a . rest) (lambda () rest)) 1 2 3)): a captured rest list.
    eval(|_| app(app(lambda(&[0], Some(1), lambda(&[], None, var(1))), vec![q(1), q(2), q(3)]), vec![]), |mc, result| assert_eq!(items(mc, result.unwrap()), [2, 3]));
}

#[test]
fn optional_parameters_are_unsupplied_when_left_out() {
    // (lambda (a [b] . rest) (if (eq? b #<unsupplied>) (+ a 100) (+ a b))), called on `args`
    // where cp0 sees the lambda, and through `apply`, where the VM binds them.
    fn f<'gc>(rest: bool) -> Core<'gc> {
        let missing = eq(var(1), Core::Quote(Value::UNSUPPLIED));
        optional_lambda(&[0, 1], 1, rest.then_some(2), when(missing, add(var(0), q(100)), add(var(0), var(1))))
    }
    for rest in [false, true] {
        for (args, expect) in [(vec![1], Ok(101)), (vec![1, 2], Ok(3)), (vec![], Err(Fault::Arity)), (vec![1, 2, 3], if rest { Ok(3) } else { Err(Fault::Arity) })] {
            let direct = number(|_| app(f(rest), args.iter().map(|&n| q(n)).collect()));
            let applied = number(|_| {
                let args = std::iter::once(f(rest)).chain(args.iter().map(|&n| q(n))).chain([Core::Quote(Value::NIL)]).collect();
                Core::Intrinsic(Prim::Request(Request::Apply), args)
            });
            assert_eq!((direct, applied), (expect, expect), "{args:?}, rest {rest}");
        }
    }
    // Optional parameters must fit in the frame's parameter registers.
    let params: Vec<u32> = (0..=u32::from(MAX_PARAMS)).collect();
    assert_eq!(error(|_| optional_lambda(&params, 1, None, q(0))), CompileError::TooManyRegisters);
}

#[test]
fn requests() {
    // (let ((tag (make-continuation-prompt-tag)))
    //   (call-with-prompt tag (lambda (v) (+ v 1)) (lambda () (+ 100 (abort tag 5)))))
    fn request<'gc>(r: Request, args: Vec<Core<'gc>>) -> Core<'gc> {
        Core::Intrinsic(Prim::Request(r), args)
    }
    assert_eq!(
        number(|_| {
            let thunk = lambda(&[], None, add(q(100), request(Request::Abort, vec![var(0), q(5)])));
            let_(vec![(0, prim(MakePromptTag, vec![]))], request(Request::CallWithPrompt, vec![var(0), lambda(&[1], None, add(var(1), q(1))), thunk]))
        }),
        Ok(6)
    );
}

#[test]
fn bad_forms_dont_compile() {
    assert_eq!(error(|_| add(var(0), q(1))), CompileError::Unbound(Var(0)));
    // (let ((_ (let ((x 1)) x))) x): x is out of scope.
    assert_eq!(error(|_| seq(1, let_(vec![(0, q(1))], var(0)), var(0))), CompileError::Unbound(Var(0)));
    assert_eq!(error(|_| let_(vec![(0, q(1))], let_(vec![(0, q(2))], var(0)))), CompileError::Rebound(Var(0)));
    assert_eq!(error(|_| prim(Car, vec![])), CompileError::Arity(Prim::Intrinsic(Car)));
    // ((lambda () 1) (lambda () 2)), both numbered 7.
    fn numbered<'gc>(body: Core<'gc>) -> Core<'gc> {
        Core::Lambda(Lambda { id: 7, params: Vec::new(), optional: 0, rest: None, body: Box::new(body), name: None, at: None })
    }
    assert_eq!(error(|_| app(numbered(q(1)), vec![numbered(q(2))])), CompileError::SameLambda(7));
    // Reject a lambda with one parameter but an optional-parameter count of two.
    assert_eq!(error(|_| Core::Lambda(Lambda { id: 7, params: vec![Var(0)], optional: 2, rest: None, body: Box::new(q(1)), name: None, at: None })), CompileError::TooManyOptional(7));
    assert_eq!(error(|_| Core::Intrinsic(Prim::Request(Request::Capture), vec![q(1)])), CompileError::Arity(Prim::Request(Request::Capture)));
}


fn many<'gc>(n: u32) -> Vec<(u32, Core<'gc>)> {
    (0..n).map(|v| (v, q(i64::from(v)))).collect()
}

fn nums<'gc>(n: i64) -> Vec<Core<'gc>> {
    (0..n).map(q).collect()
}

fn ids(n: u32) -> Vec<u32> {
    (0..n).collect()
}

#[test]
fn big_frames_spill() {
    // (let ((v0 0) ... (v299 299)) (+ v0 v150 v299))
    assert_eq!(number(|_| let_(many(300), prim(Add, vec![var(0), var(150), var(299)]))), Ok(449));
    // (+ 1 1 ... 1), more arguments than a frame has registers.
    assert_eq!(number(|_| prim(Add, (0..300).map(|_| q(1)).collect())), Ok(300));
    // (+ 1 (+ 1 ... 0)), 200 deep: more temporaries than registers.
    assert_eq!(number(|_| (0..200).fold(q(0), |e, _| add(q(1), e))), Ok(200));
    // A call of spilled values: (let ((f (lambda (a b) (+ a b)))) (+ 1 (+ 1 ... (f 1 2))))
    assert_eq!(number(|_| let_(vec![(0, lambda(&[1, 2], None, add(var(1), var(2))))], (0..150).fold(app(var(0), vec![q(1), q(2)]), |e, _| add(q(1), e)))), Ok(153));
    // (f 0 1 ... 299) of a variadic f, through apply.
    eval(|_| app(lambda(&[], Some(0), var(0)), nums(300)), |mc, result| assert_eq!(items(mc, result.unwrap()), (0..300).collect::<Vec<_>>()));
    // A closure sharing spilled boxes: (let (... (v299 299)) (let ((f (lambda () (set! v299 (+ v299 v0 1))))) (f) (f) v299))
    assert_eq!(
        number(|_| {
            let bump = lambda(&[], None, set(299, prim(Add, vec![var(299), var(0), q(1)])));
            let_(many(300), let_(vec![(300, bump)], seq(301, app(var(300), vec![]), seq(302, app(var(300), vec![]), var(299)))))
        }),
        Ok(301)
    );
    // Non-constant spilled bindings (cannot be constant-folded away by cp0), plus a spilled Fix group.
    assert_eq!(
        number(|_| {
            let boxes: Vec<(u32, Core)> = (0..250).map(|v| (v, prim(MakeBox, vec![q(i64::from(v))]))).collect();
            let even = lambda(&[302], None, when(eq(var(302), q(0)), prim(Unbox, vec![var(249)]), app(var(301), vec![add(var(302), q(-1))])));
            let odd = lambda(&[303], None, when(eq(var(303), q(0)), prim(Unbox, vec![var(0)]), app(var(300), vec![add(var(303), q(-1))])));
            let body = letrec(vec![(300, even), (301, odd)], add(prim(Unbox, vec![var(100)]), app(var(300), vec![q(4)])));
            let_(boxes, body)
        }),
        Ok(349)
    );
    // A two-argument intrinsic with a spilled first argument and a second argument computed into spill
    // storage:
    // (let ((k (make-box 0))) (with-mark k 7 (lambda () (let ((v1 (make-box 1)) ... (v250 ...)) (+
    // (mark-value k (unbox v5)) (unbox v1) ... (unbox v250))))))
    assert_eq!(
        number(|_| {
            let boxes: Vec<(u32, Core)> = (1..=250).map(|v| (v, prim(MakeBox, vec![q(i64::from(v))]))).collect();
            let marked = prim(MarkValue, vec![var(0), prim(Unbox, vec![var(5)])]);
            let all = std::iter::once(marked).chain((1..=250).map(|v| prim(Unbox, vec![var(v)]))).collect();
            let thunk = lambda(&[], None, let_(boxes, prim(Add, all)));
            let_(vec![(0, prim(MakeBox, vec![q(0)]))], Core::Intrinsic(Prim::Request(Request::WithMark), vec![var(0), q(7), thunk]))
        }),
        Ok(7 + 250 * 251 / 2)
    );
    // A join group in a spilled frame: (let ((v1 (make-box 1)) ... (v250 ...)) (+ (letrec ((even
    // (lambda (n) (if (eq? n 0) (unbox v250) (odd (+ n -1))))) (odd ...)) (even 4)) (unbox v1) ...
    // (unbox v250)))
    assert_eq!(
        number(|_| {
            let boxes: Vec<(u32, Core)> = (1..=250).map(|v| (v, prim(MakeBox, vec![q(i64::from(v))]))).collect();
            let even = lambda(&[302], None, when(eq(var(302), q(0)), prim(Unbox, vec![var(250)]), app(var(301), vec![add(var(302), q(-1))])));
            let odd = lambda(&[303], None, when(eq(var(303), q(0)), prim(Unbox, vec![var(1)]), app(var(300), vec![add(var(303), q(-1))])));
            let group = letrec(vec![(300, even), (301, odd)], app(var(300), vec![q(4)]));
            let all = std::iter::once(group).chain((1..=250).map(|v| prim(Unbox, vec![var(v)]))).collect();
            let_(boxes, prim(Add, all))
        }),
        Ok(250 + 250 * 251 / 2)
    );
}

/// Tests calls with `argc` arguments while `live` boxes remain live across the call, around the
/// boundary between working registers and scratch registers used for argument staging.
#[test]
fn calls_around_the_last_registers() {
    let stage = WINDOW as u32 / 4;
    for live in WINDOW as u32 / 2..WINDOW as u32 + 8 {
        for argc in [1, stage - 1, stage, stage + 1] {
            eval(
                move |_| {
                    let boxes = (0..live).map(|v| (v, prim(MakeBox, vec![q(i64::from(v))]))).collect();
                    let (f, rest, r) = (live, live + 1, live + 2);
                    let args = (0..argc).map(|i| prim(Unbox, vec![var(i % live)])).collect();
                    let sum = prim(Add, (0..live).map(|v| prim(Unbox, vec![var(v)])).collect());
                    let body = let_(vec![(r, app(var(f), args))], prim(Cons, vec![sum, var(r)]));
                    let_(boxes, let_(vec![(f, lambda(&[], Some(rest), var(rest)))], body))
                },
                move |mc, result| {
                    let mut want = vec![i64::from(live * (live - 1) / 2)];
                    want.extend((0..argc).map(|i| i64::from(i % live)));
                    assert_eq!(items(mc, result.unwrap()), want, "{live} live, {argc} arguments");
                },
            );
        }
    }
}

#[test]
fn lambdas_take_more_parameters_than_registers() {
    let max = u32::from(MAX_PARAMS);
    for n in [max - 1, max, max + 1, 100, 300] {
        let (mid, last) = (n / 2, n - 1);
        let sum = move |args: i64| number(move |_| app(lambda(&ids(n), None, prim(Add, vec![var(0), var(mid), var(last)])), nums(args)));
        assert_eq!(sum(i64::from(n)), Ok(i64::from(mid + last)), "{n} parameters");
        assert_eq!(sum(i64::from(n) - 1), Err(Fault::Arity), "{n} parameters");
        assert_eq!(sum(i64::from(n) + 1), Err(Fault::Arity), "{n} parameters");
        // (lambda (p0 ... . r) r), with 5 more arguments, and with none.
        for more in [0, 5] {
            let args = i64::from(n) + more;
            eval(move |_| app(lambda(&ids(n), Some(n), var(n)), nums(args)), move |mc, result| {
                assert_eq!(items(mc, result.unwrap()), (i64::from(n)..args).collect::<Vec<_>>(), "{n} parameters and a rest");
            });
        }
    }
    // Test captured and assigned parameters beyond the parameter-register range.
    assert_eq!(number(|_| app(app(lambda(&ids(300), None, lambda(&[], None, add(var(0), var(299)))), nums(300)), vec![])), Ok(299));
    assert_eq!(number(|_| app(lambda(&ids(300), None, seq(300, set(299, q(7)), var(299))), nums(300))), Ok(7));
}

#[test]
fn requests_take_any_number_of_arguments() {
    fn request<'gc>(r: Request, args: Vec<Core<'gc>>) -> Core<'gc> {
        Core::Intrinsic(Prim::Request(r), args)
    }
    // (call-with-prompt tag (lambda vs vs) (lambda () (abort tag 0 ... 299))), with the abort in
    // tail position and not.
    for tail in [true, false] {
        eval(
            move |_| {
                let mut args = vec![var(0)];
                args.extend(nums(300));
                let abort = request(Request::Abort, args);
                let thunk = lambda(&[], None, if tail { abort } else { add(q(1), abort) });
                let_(vec![(0, prim(MakePromptTag, vec![]))], request(Request::CallWithPrompt, vec![var(0), lambda(&[], Some(1), var(1)), thunk]))
            },
            |mc, result| assert_eq!(items(mc, result.unwrap()), (0..300).collect::<Vec<_>>()),
        );
    }
}

/// Collects every instruction across a compiled thunk and all nested [`Bytecode`] / [`Closure`]
/// objects in its constant pool.
fn all_ops<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Vec<Op> {
    let closure = thunk.downcast::<Closure>(mc).unwrap();
    let code = closure.code(mc).unwrap();
    let mut ops = code.ops(mc).unwrap().to_vec();
    if let Some(cs) = Constants::of(code.constants(mc)) {
        for i in 0..cs.len(mc) as u32 {
            let v = cs.get(mc, i).unwrap();
            let sub = v
                .downcast::<Bytecode>(mc)
                .or_else(|| v.downcast::<Closure>(mc).and_then(|c| c.code(mc)));
            if let Some(bc) = sub {
                ops.extend_from_slice(bc.ops(mc).unwrap());
            }
        }
    }
    ops
}

fn has_box_op(ops: &[Op]) -> bool {
    ops.iter().any(|op| {
        matches!(
            op,
            Op::CallIntrinsic { intrinsic: MakeBox | Unbox | SetBox, .. }
                | Op::CallIntrinsic1 { intrinsic: MakeBox | Unbox | SetBox, .. }
                | Op::CallIntrinsic2 { intrinsic: MakeBox | Unbox | SetBox, .. }
                | Op::TailCallIntrinsic { intrinsic: MakeBox | Unbox | SetBox, .. }
                | Op::ApplyIntrinsic { intrinsic: MakeBox | Unbox | SetBox, .. }
        )
    })
}

#[test]
fn assigned_variables_stay_in_registers_where_nothing_else_sees_them() {
    fn ops_of(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> Vec<Op> {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| all_ops(mc, compile(mc, Some(hosting(mc)), &build(mc)).unwrap()))
    }
    // An opaque call may capture a continuation.
    fn call<'gc>() -> Core<'gc> {
        app(Core::Ref(Place::Slot { slot: 0, checked: false }), vec![])
    }
    // (let ((x 1) (y 2)) (set! x (+ x y)) (+ x y))
    fn plain<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let_(vec![(0, q(1)), (1, q(2))], seq(2, set(0, add(var(0), var(1))), add(var(0), var(1))))
    }
    assert_eq!(number(plain), Ok(5));
    assert!(!has_box_op(&ops_of(plain)));
    // (let ((total 0)) (let loop ((i 10)) (if (eq? i 0) total (begin (set! total (+ total i)) (loop (+ i -1))))))
    fn summed<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let step = seq(3, set(0, add(var(0), var(2))), app(var(1), vec![add(var(2), q(-1))]));
        let_(vec![(0, q(0))], letrec(vec![(1, lambda(&[2], None, when(eq(var(2), q(0)), var(0), step)))], app(var(1), vec![q(10)])))
    }
    assert_eq!(number(summed), Ok(55));
    let ops = ops_of(summed);
    assert!(!has_box_op(&ops) && !ops.iter().any(|op| matches!(op, Op::NewClosure { .. })), "{ops:?}");
    // (let ((n 0)) (set! n 1) (f) n): assigned only before the call.
    assert!(!has_box_op(&ops_of(|_| let_(vec![(0, q(0))], seq(1, set(0, q(1)), seq(2, call(), var(0)))))));
    // (let ((n 0)) (f) (set! n 1) n): a continuation the call captures holds n as it was.
    assert!(has_box_op(&ops_of(|_| let_(vec![(0, q(0))], seq(1, call(), seq(2, set(0, q(1)), var(0)))))));
    // (let ((n 0)) (let loop ((i 3)) (if (eq? i 0) n (begin (set! n (+ n 1)) (f) (loop (+ i -1)))))):
    // assigned before the call, but again after it, round the loop.
    fn around<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let step = seq(3, set(0, add(var(0), q(1))), seq(4, call(), app(var(1), vec![add(var(2), q(-1))])));
        let_(vec![(0, q(0))], letrec(vec![(1, lambda(&[2], None, when(eq(var(2), q(0)), var(0), step)))], app(var(1), vec![q(3)])))
    }
    assert!(has_box_op(&ops_of(around)));
    // (let ((x 1)) (cons x (begin (set! x 2) x))): an argument read before a later one assigns it.
    fn argument<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let_(vec![(0, q(1))], prim(Cons, vec![var(0), seq(1, set(0, q(2)), var(0))]))
    }
    eval(argument, |mc, result| {
        let pair = Pair::of(result.unwrap()).unwrap();
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(1), fix(2)));
    });
    assert!(has_box_op(&ops_of(argument)));
    // (let ((v0 0) ... (v299 299)) (set! v299 (+ v299 v0 1)) (set! v299 (+ v299 1)) v299), in a spill slot.
    fn spilled<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let body = seq(300, set(299, prim(Add, vec![var(299), var(0), q(1)])), seq(301, set(299, add(var(299), q(1))), var(299)));
        let_(many(300), body)
    }
    assert_eq!(number(spilled), Ok(301));
    assert!(!has_box_op(&ops_of(spilled)));
}

#[test]
fn long_sequences_compile_without_deep_recursion() {
    // (lambda (f) (f) (f) ... 0), as a body of many forms is: one wide `let` of results unused.
    let mut arena = Arena::new(1 << 26, 0);
    arena.mutate(|mc| {
        let calls = (1..100_000).map(|i| (i, app(var(0), vec![]))).collect();
        compile(mc, None, &lambda(&[0], None, let_(calls, q(0)))).unwrap();
    });
}

#[test]
fn many_effects_fold_without_deep_recursion() {
    // (let ((n 0)) (void (set! n (+ n 1)) ...) n): the effects of `void`'s arguments stay flat.
    let n = number(|_| {
        let effects = (0..10_000).map(|_| set(0, add(var(0), q(1)))).collect();
        let_(vec![(0, q(0))], seq(1, prim(Intrinsic::Void, effects), var(0)))
    });
    assert_eq!(n, Ok(10_000));
    // (let ((n 0)) (vector (set! n (+ n 1)) ...) n): a vector unused is only its elements' effects.
    let n = number(|_| {
        let effects = (0..10_000).map(|_| set(0, add(var(0), q(1)))).collect();
        let_(vec![(0, q(0))], seq(1, prim(Intrinsic::MakeVectorOf, effects), var(0)))
    });
    assert_eq!(n, Ok(10_000));
}

#[test]
fn deep_expressions_compile_on_a_small_stack() {
    const N: i64 = 100_000;
    // ((lambda (x) (+ 1 (+ 1 ... (+ 1 x)))) 0), with nothing in it to fold.
    fn sum<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        app(lambda(&[0], None, (0..N).fold(var(0), |e, _| add(q(1), e))), vec![q(0)])
    }
    // ((lambda (x) (if (eq? x 0) (if (eq? x 0) ... 7 1) 1) 1)) 0)
    fn ifs<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        app(lambda(&[0], None, (0..N).fold(q(7), |e, _| when(eq(var(0), q(0)), e, q(1)))), vec![q(0)])
    }
    // (lambda () (lambda () ... (lambda () 0))), each its own closure.
    fn lambdas<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        (0..10_000).fold(q(0), |e, _| lambda(&[], None, e))
    }
    let run = || {
        let mut arena = Arena::new(1 << 26, 0);
        arena.mutate(|mc| {
            for core in [sum(mc), ifs(mc), lambdas(mc)] {
                compile(mc, None, &core).unwrap();
            }
        });
    };
    std::thread::Builder::new().stack_size(256 << 10).spawn(run).expect("spawned").join().expect("ran");
    assert_eq!(number(sum), Ok(N));
    assert_eq!(number(ifs), Ok(7));
}

#[test]
fn long_chains_of_definitions_compile_without_deep_recursion() {
    // (letrec ((f0 (lambda (x) (f1 x))) (f1 (lambda (x) (f2 x))) ... (fn (lambda (x) x))) f0),
    // as a body's definitions are, each referring to the next.
    let n = 20_000;
    let mut arena = Arena::new(1 << 26, 0);
    arena.mutate(|mc| {
        let x = |i: u32| n + 1 + i;
        let mut binds: Vec<_> = (0..n).map(|i| (i, lambda(&[x(i)], None, app(var(i + 1), vec![var(x(i))])))).collect();
        binds.push((n, lambda(&[x(n)], None, var(x(n)))));
        compile(mc, None, &letrec(binds, var(0))).unwrap();
    });
    // (letrec ((f0 (lambda (x) (+ 1 (f1 x)))) ... (fn (lambda (x) x))) (f0 0)): inlining each
    // function into the one before would nest as deep as the chain is long.
    let n = 10_000;
    let x = |i: u32| n + 1 + i;
    let chain = number(move |_| {
        let mut binds: Vec<_> = (0..n).map(|i| (i, lambda(&[x(i)], None, add(q(1), app(var(i + 1), vec![var(x(i))]))))).collect();
        binds.push((n, lambda(&[x(n)], None, var(x(n)))));
        letrec(binds, app(var(0), vec![q(0)]))
    });
    assert_eq!(chain, Ok(i64::from(n)));
    // Each function is called once, so inline the entire chain and fold it to `n`, regardless of the
    // resulting nesting depth.
    let mut arena = Arena::new(1 << 26, 0);
    arena.mutate(|mc| {
        let mut binds: Vec<_> = (0..n).map(|i| (i, lambda(&[x(i)], None, add(q(1), app(var(i + 1), vec![var(x(i))]))))).collect();
        binds.push((n, lambda(&[x(n)], None, var(x(n)))));
        let ops = all_ops(mc, compile(mc, None, &letrec(binds, app(var(0), vec![q(0)]))).unwrap());
        assert!(matches!(ops[..], [Op::LoadConst { .. }, Op::Return { .. }]), "{} ops", ops.len());
    });
    // (letrec ((a0 0) (g0 (lambda (k) (if (eq? k 0) (+ a0 1) (g0 (+ k -1))))) (a1 (g0 1)) (g1 ...)
    // ... (an (g(n-1) 1))) an): values and loops defined in turn, each loop a join.
    let (a, g, k) = (|i: u32| 3 * i, |i: u32| 3 * i + 1, |i: u32| 3 * i + 2);
    let interleaved = number(move |_| {
        let mut binds = vec![(a(0), q(0))];
        for i in 0..n {
            let again = app(var(g(i)), vec![add(var(k(i)), q(-1))]);
            binds.push((g(i), lambda(&[k(i)], None, when(eq(var(k(i)), q(0)), add(var(a(i)), q(1)), again))));
            binds.push((a(i + 1), app(var(g(i)), vec![q(1)])));
        }
        letrec(binds, var(a(n)))
    });
    assert_eq!(interleaved, Ok(i64::from(n)));
}

#[test]
fn deeply_nested_loops_compile_quickly() {
    // (let ((x 0)) (let l0 ((k0 1)) (if (eq? k0 0) (let l1 ((k1 1)) ... (begin (set! x (+ x 1)) x) ...)
    // (l0 (+ k0 -1))))): each loop a join in the one around it's code.`
    // Each nested loop becomes a join inside the enclosing loop's code.
    let x = number(|_| {
        let mut inner = seq(1000, set(0, add(var(0), q(1))), var(0));
        for i in (0..60).rev() {
            let (l, k) = (1 + 2 * i, 2 + 2 * i);
            let body = when(eq(var(k), q(0)), inner, app(var(l), vec![add(var(k), q(-1))]));
            inner = letrec(vec![(l, lambda(&[k], None, body))], app(var(l), vec![q(1)]));
        }
        let_(vec![(0, q(0))], inner)
    });
    assert_eq!(x, Ok(1));
}

#[test]
fn joins_go_where_they_are_called_however_deep() {
    // (let ((x 1)) (set! x 2) (let ((k (lambda (a) (+ x (+ x ... (+ x a)))))) (if (eq? x -1) -1 (if
    // (eq? x -2) -2 ... (if (eq? x 0) (k 1) (k 2)))))): the ifs and k's code each nearly as deep as the
    // front end takes, so k's code is deeper still where it goes, as a join.`
    // Placing `k` as a join combines a deep conditional chain with a deep function body.
    let (ifs, height) = (200, 150);
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let mut code = var(2);
        for _ in 0..height {
            code = add(var(0), code);
        }
        let mut body = when(eq(var(0), q(0)), app(var(1), vec![q(1)]), app(var(1), vec![q(2)]));
        for i in 1..=ifs {
            body = when(eq(var(0), q(-i)), q(-i), body);
        }
        let expr = let_(vec![(0, q(1))], seq(3, set(0, q(2)), let_(vec![(1, lambda(&[2], None, code))], body)));
        let thunk = compile(mc, None, &expr).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!ops.iter().any(|op| matches!(op, Op::NewClosure { .. })) && !has_box_op(&ops), "{ops:?}");
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let Outcome::Done(value) = machine.run(mc).unwrap() else { panic!("the code only adds") };
        assert_eq!(value.as_fixnum(), Some(2 * height + 2));
    });
}

#[test]
fn values_are_made_where_they_go() {
    fn ops_of(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> Vec<Op> {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| all_ops(mc, compile(mc, None, &build(mc)).unwrap()))
    }
    let moves = |ops: &[Op]| ops.iter().filter(|op| matches!(op, Op::Move { .. } | Op::Move2 { .. })).count();
    // (lambda (x) (car x)): the argument is already where the intrinsic takes it.
    let ops = ops_of(|_| lambda(&[0], None, prim(Car, vec![var(0)])));
    assert!(moves(&ops) == 0 && ops.contains(&Op::TailCallIntrinsic { base: ARGS, args: 1, intrinsic: Car }), "{ops:?}");
    // (let loop ((xs '(1 2 3)) (acc '())) (if (null? xs) acc (loop (cdr xs) (cons (car xs) acc)))):
    // reuse each parameter's register for its next value only after all reads of the old value.
    fn reverse<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let nil = || Core::Quote(Value::NIL);
        let list = prim(Cons, vec![q(1), prim(Cons, vec![q(2), prim(Cons, vec![q(3), nil()])])]);
        let step = app(var(0), vec![prim(Intrinsic::Cdr, vec![var(1)]), prim(Cons, vec![prim(Car, vec![var(1)]), var(2)])]);
        let body = when(prim(Intrinsic::IsNull, vec![var(1)]), var(2), step);
        letrec(vec![(0, lambda(&[1, 2], None, body))], app(var(0), vec![list, nil()]))
    }
    eval(reverse, |mc, result| assert_eq!(items(mc, result.unwrap()), [3, 2, 1]));
    let ops = ops_of(reverse);
    assert_eq!(moves(&ops), 0, "{ops:?}");
}

#[test]
fn forwarded_pairs_mean_what_they_did() {
    // (let ((p (cons 1 2))) (+ (car p) (cdr p)))
    fn sum<'gc>() -> Core<'gc> {
        let parts = add(prim(Intrinsic::Car, vec![var(2)]), prim(Intrinsic::Cdr, vec![var(2)]));
        app(lambda(&[0, 1], None, let_(vec![(2, prim(Intrinsic::Cons, vec![var(0), var(1)]))], parts)), vec![q(1), q(2)])
    }
    assert_eq!(number(|_| sum()), Ok(3));
    // ((lambda (f) (car (let ((x (f))) (cons x 1)))) (lambda () 5))
    fn in_let<'gc>() -> Core<'gc> {
        let car = prim(Intrinsic::Car, vec![let_(vec![(1, app(var(0), vec![]))], prim(Intrinsic::Cons, vec![var(1), q(1)]))]);
        app(lambda(&[0], None, car), vec![lambda(&[], None, q(5))])
    }
    assert_eq!(number(|_| in_let()), Ok(5));
    // ((lambda (f) (let ((p (cons (f) 1))) (car p))) (lambda () 7)): a part that isn't a constant
    // or a variable stays where it's evaluated.
    fn called<'gc>() -> Core<'gc> {
        let body = let_(vec![(1, prim(Intrinsic::Cons, vec![app(var(0), vec![]), q(1)]))], prim(Intrinsic::Car, vec![var(1)]));
        app(lambda(&[0], None, body), vec![lambda(&[], None, q(7))])
    }
    assert_eq!(number(|_| called()), Ok(7));
    // ((lambda (a) (let ((p (cons a 0))) (set! a 9) (car p))) 1): a part that's assigned after.
    fn assigned<'gc>() -> Core<'gc> {
        let set = Core::Set(Place::Local(Var(0)), Box::new(q(9)));
        let body = let_(vec![(1, prim(Intrinsic::Cons, vec![var(0), q(0)]))], seq(2, set, prim(Intrinsic::Car, vec![var(1)])));
        app(lambda(&[0], None, body), vec![q(1)])
    }
    assert_eq!(number(|_| assigned()), Ok(1));
    // (let ((b (box 1))) (set-box! b 2) (unbox b)): boxes aren't forwarded through variables.
    fn boxed<'gc>() -> Core<'gc> {
        let body = seq(1, prim(Intrinsic::SetBox, vec![var(0), q(2)]), prim(Intrinsic::Unbox, vec![var(0)]));
        let_(vec![(0, prim(Intrinsic::MakeBox, vec![q(1)]))], body)
    }
    assert_eq!(number(|_| boxed()), Ok(2));
}

#[test]
fn micropass_optimizations() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        // 1. Unmutated captured variables are never boxed (`assign` pass only boxes `Set` vars).
        let unmutated_capture = lambda(&[0], None, lambda(&[], None, var(0)));
        let thunk = compile(mc, None, &unmutated_capture).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!has_box_op(&ops), "immutable captured variable should not be boxed: {ops:?}");

        // 2. Mutually recursive `letrec` lambdas that escape compile to a single
        //    `Op::NewClosure { count: 2 }` with zero heap boxes (`letrec` fixing pass).
        let even = || lambda(&[2], None, when(eq(var(2), q(0)), Core::Quote(Value::TRUE), app(var(1), vec![add(var(2), q(-1))])));
        let odd = || lambda(&[3], None, when(eq(var(3), q(0)), Core::Quote(Value::FALSE), app(var(0), vec![add(var(3), q(-1))])));
        let mutual = letrec(vec![(0, even()), (1, odd())], prim(Cons, vec![var(0), var(1)]));
        let thunk = compile(mc, None, &mutual).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!has_box_op(&ops), "mutually recursive lambdas should not be boxed: {ops:?}");
        assert!(ops.iter().any(|op| matches!(op, Op::NewClosure { count: 2, .. })), "expected batch NewClosure(count: 2): {ops:?}");

        // 3. `cp0` folds constants, inlines local helpers, and eliminates `not` in `if` tests.
        //    (let ((inc (lambda (x) (+ x 1)))) (if (not (eq? (inc 41) 42)) 0 (inc 99))) -> 100
        let inc = lambda(&[1], None, add(var(1), q(1)));
        let test = prim(Not, vec![eq(app(var(0), vec![q(41)]), q(42))]);
        let folded = let_(vec![(0, inc)], when(test, q(0), app(var(0), vec![q(99)])));
        let thunk = compile(mc, None, &folded).unwrap();
        let ops = all_ops(mc, thunk);
        assert_eq!(ops.len(), 2, "expected constant-folded [LoadConst, Return], got {ops:?}");
        assert!(matches!(ops.as_slice(), [Op::LoadConst { .. }, Op::Return { .. }]));
        //    Comparisons fold too: (if (< 1 2 3) (<= 2 1) 0) -> #f
        let compared = when(prim(Intrinsic::Lt, vec![q(1), q(2), q(3)]), prim(Intrinsic::Le, vec![q(2), q(1)]), q(0));
        let ops = all_ops(mc, compile(mc, None, &compared).unwrap());
        assert!(matches!(ops.as_slice(), [Op::LoadConst { .. }, Op::Return { .. }]), "{ops:?}");
        // Fold a small exponentiation, but leave an expensive one for runtime evaluation.
        let ops = all_ops(mc, compile(mc, None, &prim(Intrinsic::Expt, vec![q(2), q(10)])).unwrap());
        assert!(matches!(ops.as_slice(), [Op::LoadConst { .. }, Op::Return { .. }]), "{ops:?}");
        let ops = all_ops(mc, compile(mc, None, &prim(Intrinsic::Expt, vec![q(3), q(1_000_000)])).unwrap());
        assert!(ops.len() > 2, "{ops:?}");

        // 4. Inline imported intrinsic wrappers. `(+ x 1)` and calls to imported `add1` become `AddImm`
        // without procedure calls.
        let lib = exporting(mc, vec![
            ("add", lambda(&[], Some(0), Core::ApplyIntrinsic(Prim::Intrinsic(Add), vec![var(0)])), false),
            ("add1", lambda(&[0], None, add(var(0), q(1))), false),
        ]);
        let mut fresh = fresher();
        let call_import = imported(mc, lib, "add").call(mc, vec![var(0), q(1)], &mut fresh).unwrap();
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0], None, call_import)).unwrap());
        assert!(
            matches!(ops.as_slice(), [.., Op::AddImm { dst, a: 1, imm: 1 }, Op::Return { src }] if dst == src),
            "expected imported `(+ x 1)` to compile to AddImm: {ops:?}"
        );
        let add1 = imported(mc, lib, "add1");
        let inner = add1.call(mc, vec![var(0)], &mut fresh).unwrap();
        let twice = add1.call(mc, vec![inner], &mut fresh).unwrap();
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0], None, twice)).unwrap());
        assert!(!ops.iter().any(|op| matches!(op, Op::Call { .. } | Op::TailCall { .. })), "expected add1 to inline: {ops:?}");
        assert_eq!(ops.iter().filter(|op| matches!(op, Op::AddImm { imm: 1, .. })).count(), 2, "{ops:?}");

        // 4b. `(+ x k)`, `(+ k x)` and `(- x k)` with an `i16` fixnum `k` compile to `AddImm`;
        //     anything else stays a call of `+` or `-`.
        for (expr, imm) in [
            (add(var(0), q(1)), 1),
            (add(q(1), var(0)), 1),
            (prim(Intrinsic::Sub, vec![var(0), q(1)]), -1),
            (prim(Intrinsic::Sub, vec![var(0), q(-1)]), 1),
            (add(var(0), q(2)), 2),
            (prim(Intrinsic::Sub, vec![var(0), q(2)]), -2),
            (add(var(0), q(i64::from(i16::MAX))), i16::MAX),
            (prim(Intrinsic::Sub, vec![var(0), q(i64::from(i16::MAX))]), -i16::MAX),
            (add(var(0), q(i64::from(i16::MIN))), i16::MIN),
        ] {
            let thunk = compile(mc, None, &lambda(&[0], None, expr)).unwrap();
            let ops = all_ops(mc, thunk);
            assert!(
                ops.iter().any(|op| matches!(op, Op::AddImm { imm: i, .. } if *i == imm)),
                "expected AddImm({imm}): {ops:?}"
            );
        }
        for (expr, want) in [
            (add(var(0), q(i64::from(i16::MAX) + 1)), Add),
            (prim(Intrinsic::Sub, vec![var(0), q(i64::from(i16::MIN))]), Add),
            (prim(Intrinsic::Sub, vec![q(1), var(0)]), Intrinsic::Sub),
            (prim(Intrinsic::Sub, vec![var(0), q(0)]), Intrinsic::Sub),
            (add(var(0), var(0)), Add),
        ] {
            let thunk = compile(mc, None, &lambda(&[0], None, expr)).unwrap();
            let ops = all_ops(mc, thunk);
            assert!(!ops.iter().any(|op| matches!(op, Op::AddImm { .. })), "expected no AddImm: {ops:?}");
            assert!(
                ops.iter().any(|op| matches!(op, Op::TailCallIntrinsic { intrinsic, .. } if *intrinsic == want)),
                "expected TailCallIntrinsic({want:?}): {ops:?}"
            );
        }

        // 4c. Preserve a leading effect while exposing the following constant for optimization: `(+ (begin
        // (f) 1) x)` uses `AddImm`; `(+ (begin (f) 2) 3)` returns 5 after calling `f`.
        let effect_first = add(seq(9, app(var(1), vec![]), q(1)), var(0));
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0, 1], None, effect_first)).unwrap());
        assert!(ops.iter().any(|op| matches!(op, Op::AddImm { imm: 1, .. })), "expected AddImm: {ops:?}");
        assert!(!ops.iter().any(|op| matches!(op, Op::TailCallIntrinsic { intrinsic: Add, .. })), "{ops:?}");
        let folds = add(seq(9, app(var(1), vec![]), q(2)), q(3));
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0, 1], None, folds)).unwrap());
        assert!(!ops.iter().any(|op| matches!(op, Op::AddImm { .. } | Op::TailCallIntrinsic { intrinsic: Add, .. })), "{ops:?}");

        // 5. Store-to-load forwarding on `cadr`/`cons` and `unbox`/`box` eliminates allocations.
        //    (lambda (x y) (+ (cadr (cons x (cons y '()))) (unbox (box 1)))) -> (lambda (x y) (+ y 1))
        let cadr_cons = prim(Intrinsic::Cadr, vec![prim(Cons, vec![var(0), prim(Cons, vec![var(1), Core::Quote(Value::NIL)])])]);
        let unbox_box = prim(Unbox, vec![prim(MakeBox, vec![q(1)])]);
        let forwarded = lambda(&[0, 1], None, add(cadr_cons, unbox_box));
        let thunk = compile(mc, None, &forwarded).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!has_box_op(&ops), "expected (unbox (box 1)) to fold away: {ops:?}");
        assert!(
            !ops.iter().any(|op| matches!(
                op,
                Op::CallIntrinsic { intrinsic: Cons | Intrinsic::Cadr, .. }
                    | Op::CallIntrinsic1 { intrinsic: Cons | Intrinsic::Cadr, .. }
                    | Op::CallIntrinsic2 { intrinsic: Cons | Intrinsic::Cadr, .. }
            )),
            "expected (cadr (cons x (cons y '()))) to forward without Cons/Cadr: {ops:?}"
        );
        let conses = |ops: &[Op]| {
            ops.iter()
                .filter(|op| {
                    matches!(
                        op,
                        Op::CallIntrinsic { intrinsic: Cons, .. }
                            | Op::CallIntrinsic1 { intrinsic: Cons, .. }
                            | Op::CallIntrinsic2 { intrinsic: Cons, .. }
                            | Op::TailCallIntrinsic { intrinsic: Cons, .. }
                    )
                })
                .count()
        };
        // Forward fields from a pair bound to a variable, then remove the allocation when no uses remain:
        // (lambda (x y) (let ((p (cons x y))) (+ (car p) (cdr p)))) -> (lambda (x y) (+ x y))
        let parts = |p: u32| add(prim(Intrinsic::Car, vec![var(p)]), prim(Intrinsic::Cdr, vec![var(p)]));
        let bound = lambda(&[0, 1], None, let_(vec![(2, prim(Cons, vec![var(0), var(1)]))], parts(2)));
        let ops = all_ops(mc, compile(mc, None, &bound).unwrap());
        assert_eq!(conses(&ops), 0, "expected the bound pair to go: {ops:?}");
        // Forward through a `let` left by inlining:
        // (lambda (f) (car (let ((x (f))) (cons x 1)))) -> (lambda (f) (f))
        let in_let = lambda(&[0], None, prim(Intrinsic::Car, vec![let_(vec![(1, app(var(0), vec![]))], prim(Cons, vec![var(1), q(1)]))]));
        let ops = all_ops(mc, compile(mc, None, &in_let).unwrap());
        assert_eq!(conses(&ops), 0, "expected the pair in the let to go: {ops:?}");
        // `list?` must reuse the existing pair rather than allocate it again.
        let listy = lambda(&[0], None, let_(vec![(1, prim(Cons, vec![var(0), Core::Quote(Value::NIL)]))], prim(Intrinsic::IsList, vec![var(1)])));
        let ops = all_ops(mc, compile(mc, None, &listy).unwrap());
        assert_eq!(conses(&ops), 1, "{ops:?}");

        // 6. Tail-recursive local loop contifies into an in-frame backward `Jump` with zero closures.
        let looping = lambda(&[1, 2], None, when(eq(var(1), q(0)), var(2), app(var(0), vec![add(var(1), q(-1)), add(var(2), var(1))])));
        let loop_expr = letrec(vec![(0, looping)], app(var(0), vec![q(10), q(0)]));
        let thunk = compile(mc, None, &loop_expr).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(
            !ops.iter().any(|op| matches!(op, Op::NewClosure { .. } | Op::TailCall { .. } | Op::Call { .. })),
            "expected tail-recursive loop to contify without closures or calls: {ops:?}"
        );
        assert!(
            ops.iter().any(|op| matches!(op, Op::Jump { offset } if *offset < 0)),
            "expected backward Jump in contified loop: {ops:?}"
        );
    });

    // 7. `Let` dead-binding elimination and `car`/`cons` forwarding preserve left-to-right side-effect order.
    //    (let ((x 1)) ((lambda (a b) a) x (set! x 2))) -> 1 (not 2!)
    assert_eq!(
        number(|_| {
            let fst = lambda(&[1, 2], None, var(1));
            let_(vec![(0, q(1))], app(fst, vec![var(0), set(0, q(2))]))
        }),
        Ok(1)
    );
    //    (let ((x 1)) (+ (car (cons (begin (set! x (+ x 1)) x) (set! x 100))) x)) -> 2 + 100 = 102
    assert_eq!(
        number(|_| {
            let head = seq(1, set(0, add(var(0), q(1))), var(0));
            let tail = set(0, q(100));
            let_(vec![(0, q(1))], add(prim(Car, vec![prim(Cons, vec![head, tail])]), var(0)))
        }),
        Ok(102)
    );

    // 8. `procedure?` and `continuation?` fold on lambdas and dominating predicate branches.
    arena.mutate(|mc| {
        // (procedure? (lambda (x) x)) -> #t
        let proc_lam = prim(Intrinsic::IsProcedure, vec![lambda(&[0], None, var(0))]);
        let thunk = compile(mc, None, &proc_lam).unwrap();
        let ops = all_ops(mc, thunk);
        assert_eq!(ops.len(), 2, "expected (procedure? (lambda ...)) to fold to #t: {ops:?}");

        // (continuation? (lambda (x) x)) -> #f
        let cont_lam = prim(Intrinsic::IsContinuation, vec![lambda(&[0], None, var(0))]);
        let thunk = compile(mc, None, &cont_lam).unwrap();
        let ops = all_ops(mc, thunk);
        assert_eq!(ops.len(), 2, "expected (continuation? (lambda ...)) to fold to #f: {ops:?}");

        // Dominating `continuation?` implies `procedure?` (#t) and truthiness in `then`,
        // and dominating `procedure?` (#f) implies `continuation?` (#f) in `other`:
        // (lambda (x)
        //   (if (continuation? x)
        //       (if (procedure? x) (if x 1 2) 3)
        //       (if (procedure? x) 4 (if (continuation? x) 5 6))))
        // -> (lambda (x) (if (continuation? x) 1 (if (procedure? x) 4 6)))
        let inner_then = when(prim(Intrinsic::IsProcedure, vec![var(0)]), when(var(0), q(1), q(2)), q(3));
        let inner_else = when(
            prim(Intrinsic::IsProcedure, vec![var(0)]),
            q(4),
            when(prim(Intrinsic::IsContinuation, vec![var(0)]), q(5), q(6)),
        );
        let dom = lambda(&[0], None, when(prim(Intrinsic::IsContinuation, vec![var(0)]), inner_then, inner_else));
        let thunk = compile(mc, None, &dom).unwrap();
        let ops = all_ops(mc, thunk);
        let pred_calls = ops
            .iter()
            .filter(|op| {
                matches!(
                    op,
                    Op::CallIntrinsic { intrinsic: Intrinsic::IsProcedure | Intrinsic::IsContinuation, .. }
                        | Op::CallIntrinsic1 { intrinsic: Intrinsic::IsProcedure | Intrinsic::IsContinuation, .. }
                        | Op::BranchIntrinsic1 { intrinsic: Intrinsic::IsProcedure | Intrinsic::IsContinuation, .. }
                )
            })
            .count();
        assert_eq!(pred_calls, 2, "expected redundant dominating predicate checks to fold away: {ops:?}");

        // 8b. Fused `BranchIntrinsic1`, `CallIntrinsic1`/`2`, and branch inversion compile a
        //     list-length loop body to 4 instructions with zero `Move`s or `LoadAcc`s.
        let list_len_loop = lambda(
            &[0, 1],
            None,
            letrec(
                vec![(
                    2,
                    lambda(
                        &[3, 4],
                        None,
                        when(
                            prim(Intrinsic::IsNull, vec![var(3)]),
                            var(4),
                            app(var(2), vec![prim(Intrinsic::Cdr, vec![var(3)]), add(var(4), var(1))]),
                        ),
                    ),
                )],
                app(var(2), vec![var(0), q(0)]),
            ),
        );
        let thunk = compile(mc, None, &list_len_loop).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(
            ops.windows(5).any(|w| matches!(
                w,
                [
                    Op::BranchIntrinsic1 { intrinsic: Intrinsic::IsNull, branch_if: true, offset: 3, .. },
                    Op::CallIntrinsic1 { intrinsic: Intrinsic::Cdr, .. },
                    Op::CallIntrinsic2 { intrinsic: Add, .. },
                    Op::Jump { offset: -4 },
                    Op::Return { .. },
                ]
            )),
            "expected 4-instruction tight loop body followed by Return: {ops:?}"
        );
    });

    // 9. Nested contified loops compile with zero closures and zero calls (two backward `Jump`s).
    arena.mutate(|mc| {
        // (letrec ((outer (lambda (i total)
        //                   (if (eq? i 0)
        //                       total
        //                       (outer (+ i -1)
        //                              (letrec ((inner (lambda (j acc)
        //                                                (if (eq? j 0)
        //                                                    acc
        //                                                    (inner (+ j -1) (+ acc j))))))
        //                                (inner i total)))))))
        //   (outer 10 0))
        let inner_fn = lambda(
            &[3, 4],
            None,
            when(eq(var(3), q(0)), var(4), app(var(2), vec![add(var(3), q(-1)), add(var(4), var(3))])),
        );
        let inner_loop = letrec(vec![(2, inner_fn)], app(var(2), vec![var(1), var(5)]));
        let outer_fn = lambda(
            &[1, 5],
            None,
            when(eq(var(1), q(0)), var(5), app(var(0), vec![add(var(1), q(-1)), inner_loop])),
        );
        let nested_loops = letrec(vec![(0, outer_fn)], app(var(0), vec![q(10), q(0)]));
        let thunk = compile(mc, None, &nested_loops).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(
            !ops.iter().any(|op| matches!(op, Op::NewClosure { .. } | Op::Call { .. } | Op::TailCall { .. })),
            "expected nested tail loops to contify with zero closures/calls: {ops:?}"
        );
        let back_jumps = ops.iter().filter(|op| matches!(op, Op::Jump { offset } if *offset < 0)).count();
        assert_eq!(back_jumps, 2, "expected 2 backward Jumps for nested contified loops: {ops:?}");
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let Outcome::Done(val) = machine.run(mc).unwrap() else { panic!() };
        assert_eq!(val.as_fixnum(), Some(220));
    });

    // 10. Spilled frame (>256 live variables) containing a contified loop whose body reads both
    //     register-resident and spill-slot-resident outer variables.
    assert_eq!(
        number(|_| {
            // Keep 260 distinct boxes live to force spilling. A contified loop reads the first and last boxes,
            // exercising both register and spill-slot access.
            let binds: Vec<_> = (0..260u32)
                .map(|i| (i, prim(MakeBox, vec![q(1)])))
                .collect();
            let sum_boxes = prim(Add, (0..260u32).map(|i| prim(Unbox, vec![var(i)])).collect());
            let loop_var = 300;
            let iter_var = 301;
            let acc_var = 302;
            let loop_fn = lambda(
                &[iter_var, acc_var],
                None,
                when(
                    eq(var(iter_var), q(0)),
                    var(acc_var),
                    app(
                        var(loop_var),
                        vec![add(var(iter_var), q(-1)), add(var(acc_var), sum_boxes)],
                    ),
                ),
            );
            let_(binds, letrec(vec![(loop_var, loop_fn)], app(var(loop_var), vec![q(3), q(0)])))
        }),
        Ok(260 * 3)
    );

    // 11. A fused branch whose target is past an `i16` offset recompiles with `JumpIfFalse`.
    //     ((lambda (x f) (if (null? x) (+ (f) (f) ... 12000 times) 0)) '() (lambda () 1)) -> 12000
    assert_eq!(
        number(|_| {
            let calls = (0..12_000).map(|_| app(var(1), vec![])).collect();
            let far = lambda(&[0, 1], None, when(prim(Intrinsic::IsNull, vec![var(0)]), prim(Add, calls), q(0)));
            app(far, vec![Core::Quote(Value::NIL), lambda(&[], None, q(1))])
        }),
        Ok(12_000)
    );

    // 12. The literal list-length loop:
    //     (lambda (list) (let loop ((xs list) (len 0)) (if (null? xs) len (loop (cdr xs) (+ len 1)))))
    arena.mutate(|mc| {
        let body = lambda(
            &[3, 4],
            None,
            when(
                prim(Intrinsic::IsNull, vec![var(3)]),
                var(4),
                app(var(2), vec![prim(Intrinsic::Cdr, vec![var(3)]), add(var(4), q(1))]),
            ),
        );
        let length = lambda(&[0], None, letrec(vec![(2, body)], app(var(2), vec![var(0), q(0)])));
        let thunk = compile(mc, None, &length).unwrap();
        let ops = all_ops(mc, thunk);
        // The whole loop: fused `null?` test, `cdr` in place, `(+ len 1)` as `AddImm` in place, back-edge.
        assert!(
            ops.windows(5).any(|w| matches!(
                w,
                [
                    Op::BranchIntrinsic1 { a: xs, intrinsic: Intrinsic::IsNull, branch_if: true, offset: 3 },
                    Op::CallIntrinsic1 { dst: xs2, a: xs3, intrinsic: Intrinsic::Cdr },
                    Op::AddImm { dst: len, a: len2, imm: 1 },
                    Op::Jump { offset: -4 },
                    Op::Return { src: len3 },
                ] if xs == xs2 && xs == xs3 && len == len2 && len == len3
            )),
            "expected the 4-instruction list-length loop: {ops:?}"
        );

        // Run the compiled `length` on lists with 0, 1, and 1000 elements.
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let Outcome::Done(length) = machine.run(mc).unwrap() else { panic!() };
        let pairs = Pairs::new(mc);
        for n in [0, 1, 1000] {
            let list = pairs.list(&(0..n).map(fix).collect::<Vec<_>>()).unwrap();
            let mut machine = Machine::new(mc, MIN_SEGMENT, length, &[list]).unwrap();
            let Outcome::Done(len) = machine.run(mc).unwrap() else { panic!() };
            assert_eq!(len.as_fixnum(), Some(n));
        }
    });
}

/// Supplies fresh local IDs that do not overlap with IDs used explicitly by tests.
fn fresher() -> impl FnMut() -> Var {
    let mut next = 1000;
    move || {
        next += 1;
        Var(next)
    }
}

fn symbol<'gc>(mc: &Mutation<'gc>, name: &str) -> Value<'gc> {
    let symbols = Symbols::with_seed(mc, 1).unwrap();
    symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc)
}

/// Builds and runs a module that defines and exports `defs`, including assignments for definitions
/// marked mutable.
fn exporting<'gc>(mc: &Mutation<'gc>, defs: Vec<(&str, Core<'gc>, bool)>) -> Gc<'gc, ragwort_vm::objects::Module> {
    exporting_with(mc, &[], &[], defs)
}

/// Builds a module as [`exporting`] does, with host functions `hosts` and named dependencies
/// `imports`.
fn exporting_with<'gc>(mc: &Mutation<'gc>, hosts: &'static [HostDef], imports: &[(&str, Import<'gc>)], defs: Vec<(&str, Core<'gc>, bool)>) -> Gc<'gc, ragwort_vm::objects::Module> {
    let mut builder = ModuleBuilder::new(Value::FALSE, hosts);
    let symbols = Symbols::with_seed(mc, 1).unwrap();
    for &(name, import) in imports {
        builder.import(symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc), import).unwrap();
    }
    let names: Vec<_> = defs.iter().map(|(name, _, _)| symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc)).collect();
    for (top, &name) in names.iter().enumerate() {
        builder.define(name, top as u32).unwrap();
    }
    builder.provide_all(mc).unwrap();
    builder.start(mc).unwrap();
    for (slot, (_, value, assigned)) in defs.into_iter().enumerate() {
        let slot = slot as u32;
        builder.defined(slot, &value);
        if assigned {
            builder.assign(slot).unwrap();
        }
        let thunk = builder.compile(mc, &Core::Set(Place::Slot { slot, checked: false }, Box::new(value))).unwrap();
        run_to_end(mc, thunk).unwrap();
    }
    builder.finish(mc).unwrap()
}

fn imported<'gc>(mc: &Mutation<'gc>, module: Gc<'gc, ragwort_vm::objects::Module>, name: &str) -> Import<'gc> {
    let imports = Imports::all(mc, module).unwrap();
    imports.0.into_iter().find(|(n, _)| n == name).unwrap().1
}

fn run_to_end<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(raised.downcast::<Condition>(mc).unwrap().failure(mc).unwrap().fault),
            _ => panic!("yielded"),
        }
    }
}

#[test]
fn modules_export_what_code_that_requires_them_needs() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let spread = |i| Core::ApplyIntrinsic(Prim::Intrinsic(i), vec![var(0)]);
        let lib = exporting(mc, vec![
            ("sum", lambda(&[], Some(0), spread(Add)), false),
            ("sum-not", lambda(&[], Some(0), prim(Not, vec![spread(Add)])), false),
            ("car-cons", lambda(&[], Some(0), prim(Car, vec![spread(Cons)])), false),
            ("counter", q(0), true),
            ("five", q(5), false),
            // An immutable module-variable reference can be replaced with its value.
            ("first", lambda(&[0], None, add(var(0), slot(4))), false),
            // A mutable module-variable reference must read its current value at the call site.
            ("counted", lambda(&[0], None, add(var(0), slot(3))), false),
            // Call a procedure passed as an argument or obtained from a module variable.
            ("applied", lambda(&[0, 1], None, Core::App(Box::new(var(0)), vec![var(1), slot(4)])), false),
        ]);
        let interface = ragwort_compiler_interface(mc, lib);
        assert!(interface.get("sum").unwrap().inline.is_some());
        assert!(interface.get("counter").unwrap().mutable && interface.get("counter").unwrap().inline.is_none());
        assert!(interface.get("first").unwrap().inline.is_some() && interface.get("applied").unwrap().inline.is_some());
        assert!(interface.get("counted").unwrap().inline.is_none() && interface.get("nothing").is_none());
        // Inlining preserves the procedure call and supplies the module variable's value.
        let sum = imported(mc, lib, "sum").reference(mc).unwrap();
        let applied = imported(mc, lib, "applied").call(mc, vec![sum, q(2)], &mut fresher()).unwrap();
        assert!(matches!(&applied, Core::App(..)), "{applied:?}");
        assert_eq!(run_to_end(mc, compile(mc, None, &applied).unwrap()), Ok(fix(7)));
        // Compare inlined execution with the original call's behavior.
        let mut fresh = fresher();
        for (name, want) in [("sum", fix(7)), ("sum-not", Value::FALSE), ("car-cons", fix(3)), ("first", fix(8))] {
            let call = imported(mc, lib, name).call(mc, vec![q(3), q(4)].into_iter().take(if name == "first" { 1 } else { 2 }).collect(), &mut fresh).unwrap();
            assert_eq!(run_to_end(mc, compile(mc, None, &call).unwrap()), Ok(want), "{name}");
        }
        // Immutable exports are their values; mutable ones are read with module-ref.
        assert_eq!(imported(mc, lib, "five").reference(mc), Ok(Core::Quote(fix(5))));
        let counter = imported(mc, lib, "counter").reference(mc).unwrap();
        assert!(matches!(counter, Core::Intrinsic(Prim::Intrinsic(ModuleRef), _)), "{counter:?}");
        ragwort_vm::objects::ModuleFields::items(lib, mc).set(mc, 3, fix(9));
        assert_eq!(run_to_end(mc, compile(mc, None, &counter).unwrap()), Ok(fix(9)));
        // An arity mismatch bypasses the template and remains an ordinary call that faults.
        let wrong = imported(mc, lib, "first").call(mc, vec![], &mut fresh).unwrap();
        assert_eq!(run_to_end(mc, compile(mc, None, &wrong).unwrap()), Err(Fault::Arity));
        // Even when the template uses parameters out of order, evaluate arguments in source order so the
        // first argument's fault occurs first.
        let lib2 = exporting(mc, vec![
            ("swap", lambda(&[0, 1], None, prim(Cons, vec![var(1), var(0)])), false),
            ("rest-first", lambda(&[0], Some(1), prim(Cons, vec![var(1), var(0)])), false),
        ]);
        let faulting = vec![prim(Car, vec![q(1)]), prim(ragwort_vm::Intrinsic::VectorRef, vec![constant(mc, &[]), q(0)])];
        let swapped = imported(mc, lib2, "swap").call(mc, faulting, &mut fresh).unwrap();
        assert_eq!(run_to_end(mc, compile(mc, None, &swapped).unwrap()), Err(Fault::WrongType));
        let ok = imported(mc, lib2, "swap").call(mc, vec![q(1), add(q(1), q(1))], &mut fresh).unwrap();
        assert_eq!(run_to_end(mc, compile(mc, None, &prim(Car, vec![ok])).unwrap()), Ok(fix(2)));
        let rest = imported(mc, lib2, "rest-first").call(mc, vec![q(1), add(q(1), q(1)), q(3)], &mut fresh).unwrap();
        let rest = run_to_end(mc, compile(mc, None, &prim(Car, vec![rest])).unwrap()).unwrap();
        assert_eq!(items(mc, rest), [2, 3]);
        // An omitted optional argument becomes the unsupplied value, allowing its default test to fold:
        // (lambda (a [b]) (let ([c (if (eq? b #<unsupplied>) 100 b)]) (+ a c))).
        let default = when(eq(var(1), Core::Quote(Value::UNSUPPLIED)), q(100), var(1));
        let lib3 = exporting(mc, vec![("plus", optional_lambda(&[0, 1], 1, None, let_(vec![(2, default)], add(var(0), var(2)))), false)]);
        let plus = imported(mc, lib3, "plus");
        assert!(ragwort_compiler_interface(mc, lib3).get("plus").unwrap().inline.is_some());
        for (args, want) in [(vec![3], Ok(fix(103))), (vec![3, 4], Ok(fix(7))), (vec![], Err(Fault::Arity)), (vec![3, 4, 5], Err(Fault::Arity))] {
            let call = plus.call(mc, args.iter().map(|&n| q(n)).collect(), &mut fresh).unwrap();
            assert_eq!(run_to_end(mc, compile(mc, None, &call).unwrap()), want, "{args:?}");
        }
        let one = plus.call(mc, vec![var(0)], &mut fresh).unwrap();
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0], None, one)).unwrap());
        assert!(matches!(ops.as_slice(), [.., Op::AddImm { imm: 100, .. }, Op::Return { .. }]), "expected the default to fold: {ops:?}");
        // Bind an argument used in both an `if` test and a branch so it is evaluated only once.
        let lib4 = exporting(mc, vec![("car-or", lambda(&[0], None, when(prim(ragwort_vm::Intrinsic::IsPair, vec![var(0)]), prim(Car, vec![var(0)]), var(0))), false)]);
        let call = imported(mc, lib4, "car-or").call(mc, vec![prim(Cons, vec![q(1), q(2)])], &mut fresh).unwrap();
        assert_eq!(run_to_end(mc, compile(mc, None, &call).unwrap()), Ok(fix(1)));
        // Reject references to immutable exports that have not been initialized.
        let mut builder = ModuleBuilder::new(Value::FALSE, &[]);
        builder.define(symbol(mc, "x"), 0).unwrap();
        builder.provide_all(mc).unwrap();
        let unrun = builder.finish(mc).unwrap();
        assert_eq!(imported(mc, unrun, "x").reference(mc), Err(Unusable::Uninitialized));
    });
}

#[test]
fn host_calls_inline_into_the_modules_that_require_them() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        // Test transitive host-function imports: the first module exports a host-call wrapper, the second
        // inlines that wrapper, and the third imports only the second with no host functions of its own.
        let host = |args| Core::Intrinsic(Prim::Host(ADD_HOST), args);
        let lib = exporting_with(mc, &HOSTS, &[], vec![("plus", lambda(&[0, 1], None, host(vec![var(0), var(1)])), false)]);
        let plus = imported(mc, lib, "plus");
        let mut fresh = fresher();
        let body = plus.call(mc, vec![var(0), q(10)], &mut fresh).unwrap();
        let mid = exporting_with(mc, &[], &[("plus", plus)], vec![("add10", lambda(&[0], None, body), false)]);
        let add10 = imported(mc, mid, "add10");
        assert!(ragwort_compiler_interface(mc, mid).get("add10").unwrap().inline.is_some());
        let mut user = ModuleBuilder::new(Value::FALSE, &[]);
        user.import(symbol(mc, "add10"), add10).unwrap();
        user.start(mc).unwrap();
        let call = add10.call(mc, vec![q(5)], &mut fresh).unwrap();
        let thunk = user.compile(mc, &call).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(ops.iter().any(|op| matches!(op, Op::CallHost { .. } | Op::TailCallHost { .. })), "{ops:?}");
        assert!(!ops.iter().any(|op| matches!(op, Op::Call { .. } | Op::TailCall { .. })), "{ops:?}");
        assert_eq!(run_to_end(mc, thunk), Ok(fix(15)));
    });
}

fn ragwort_compiler_interface<'gc>(mc: &Mutation<'gc>, module: Gc<'gc, ragwort_vm::objects::Module>) -> &'gc crate::module::Interface {
    crate::module::interface(mc, module).unwrap()
}

#[test]
fn module_builders_check_names_and_where_variables_are_defined() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let lib = exporting(mc, vec![("a", q(1), false), ("b", q(2), false)]);
        let (a, b, c) = (symbol(mc, "a"), symbol(mc, "b"), symbol(mc, "c"));
        let mut builder = ModuleBuilder::new(Value::FALSE, &[]);
        assert_eq!(builder.define(a, 0), Ok(0));
        assert_eq!(builder.define(a, 1), Err(ModuleError::Duplicate));
        assert_eq!(builder.import(a, imported(mc, lib, "a")), Err(ModuleError::Conflict));
        assert_eq!(builder.import(b, imported(mc, lib, "b")), Ok(()));
        assert_eq!(builder.import(b, imported(mc, lib, "b")), Ok(()));
        assert_eq!(builder.import(b, imported(mc, lib, "a")), Err(ModuleError::Conflict));
        assert_eq!(builder.define(b, 1), Err(ModuleError::Conflict));
        assert_eq!(builder.define(c, 2), Ok(1));
        assert_eq!(builder.provide("a", a), Ok(()));
        assert_eq!(builder.provide("a", c), Err(ModuleError::Duplicate));
        assert_eq!(builder.provide("b", b), Err(ModuleError::NotDefined));
        // References after an earlier defining form, or within the defining lambda itself, omit
        // initialization checks.
        assert_eq!(builder.place(0, 1, None), Place::Slot { slot: 0, checked: false });
        assert_eq!(builder.place(0, 0, None), Place::Slot { slot: 0, checked: true });
        assert_eq!(builder.place(1, 1, None), Place::Slot { slot: 1, checked: true });
        assert_eq!(builder.place(1, 2, Some(1)), Place::Slot { slot: 1, checked: false });
        assert_eq!(builder.place(1, 1, Some(0)), Place::Slot { slot: 1, checked: true });
        // Test require-spec selection and renaming.
        let all = Imports::all(mc, lib).unwrap();
        let names = |imports: Imports<'_>| imports.0.into_iter().map(|(n, _)| n).collect::<Vec<_>>();
        let strings = |names: &[&str]| names.iter().map(|n| n.to_string()).collect::<Vec<_>>();
        assert_eq!(names(all.clone()), ["a", "b"]);
        assert_eq!(names(all.clone().only(&strings(&["b"])).unwrap()), ["b"]);
        assert_eq!(names(all.clone().except(&strings(&["b"])).unwrap()), ["a"]);
        assert_eq!(all.clone().only(&strings(&["z"])).err(), Some("z".to_string()));
        assert_eq!(names(all.clone().prefix("lib:")), ["lib:a", "lib:b"]);
        assert_eq!(names(all.clone().rename(&[("a".into(), "x".into())]).unwrap()), ["x", "b"]);
        assert_eq!(all.rename(&[("z".into(), "x".into())]).err(), Some("z".to_string()));
    });
}

/// Counts all bytecode instruction forms that invoke `intrinsic`.
fn calls(ops: &[Op], intrinsic: Intrinsic) -> usize {
    ops.iter()
        .filter(|op| match **op {
            Op::CallIntrinsic { intrinsic: i, .. }
            | Op::CallIntrinsic1 { intrinsic: i, .. }
            | Op::CallIntrinsic2 { intrinsic: i, .. }
            | Op::CallIntrinsic3 { intrinsic: i, .. }
            | Op::TailCallIntrinsic { intrinsic: i, .. }
            | Op::ApplyIntrinsic { intrinsic: i, .. }
            | Op::BranchIntrinsic1 { intrinsic: i, .. }
            | Op::BranchIntrinsic2 { intrinsic: i, .. } => i == intrinsic,
            _ => false,
        })
        .count()
}

/// Builds a vector literal containing `xs`.
fn constant<'gc>(mc: &Mutation<'gc>, xs: &[i64]) -> Core<'gc> {
    let items: Vec<_> = xs.iter().map(|&x| fix(x)).collect();
    Core::Quote(ragwort_types::vector::Vectors::new(mc).immutable_from_slice(&items).unwrap().value(mc))
}

/// Checks whether `core` compiles to a constant load alone.
fn folds<'gc>(mc: &Mutation<'gc>, core: Core<'gc>) -> bool {
    matches!(all_ops(mc, compile(mc, None, &core).unwrap()).as_slice(), [Op::LoadConst { .. }, Op::Return { .. }])
}

/// Counts remaining calls to `asked` in a one-parameter procedure with body `test`.
fn asked_in<'gc>(mc: &Mutation<'gc>, test: Core<'gc>, asked: Intrinsic) -> usize {
    calls(&all_ops(mc, compile(mc, None, &lambda(&[0], None, test)).unwrap()), asked)
}

#[test]
fn reads_of_constant_vectors_fold() {
    use Intrinsic::{IsPair, IsVector, MakeVectorOf, VectorLength, VectorRef};
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        assert!(folds(mc, prim(VectorRef, vec![constant(mc, &[1, 2]), q(1)])));
        assert!(folds(mc, prim(VectorLength, vec![constant(mc, &[1, 2, 3])])));
        assert!(folds(mc, prim(IsVector, vec![constant(mc, &[])])));
        assert!(folds(mc, prim(IsVector, vec![q(1)])));

        // Preserve an out-of-bounds access so it faults at runtime.
        let past = all_ops(mc, compile(mc, None, &prim(VectorRef, vec![constant(mc, &[1]), q(1)])).unwrap());
        assert_eq!(calls(&past, VectorRef), 1, "{past:?}");

        // Vectors created by `vector` are mutable, so their element reads cannot be constant-folded.
        let made = prim(VectorRef, vec![prim(MakeVectorOf, vec![q(1), q(2)]), q(0)]);
        let ops = all_ops(mc, compile(mc, None, &made).unwrap());
        assert_eq!(calls(&ops, VectorRef), 1, "{ops:?}");

        // Under `(pair? x)`, `(vector? x)` is false, and under `(vector? x)`, it's true:
        // (lambda (x) (if (pair? x) (vector? x) (if (vector? x) (vector? x) 0))) has one test left.
        let is = |i: Intrinsic| prim(i, vec![var(0)]);
        let tests = when(is(IsPair), is(IsVector), when(is(IsVector), is(IsVector), q(0)));
        let ops = all_ops(mc, compile(mc, None, &lambda(&[0], None, tests)).unwrap());
        assert_eq!(calls(&ops, IsVector), 1, "{ops:?}");

        // Infer related type predicates: an integer is a real and a number, but not a pair; a non-number
        // cannot be an integer. Integer status alone does not determine exactness, and number status does
        // not imply integer status.
        use Intrinsic::{IsExactInteger, IsIdentifier, IsInteger, IsList, IsNull, IsNumber, IsReal, IsSyntax};
        for (known, asked) in [
            (IsInteger, IsNumber),
            (IsInteger, IsReal),
            (IsExactInteger, IsInteger),
            (IsIdentifier, IsSyntax),
            (IsNull, IsList),
            (IsInteger, IsPair),
            (IsSyntax, IsNumber),
            (Intrinsic::IsStruct, IsPair),
            (IsVector, Intrinsic::IsStruct),
            (Intrinsic::IsStructType, Intrinsic::IsStruct),
            (Intrinsic::IsStruct, Intrinsic::IsStructType),
        ] {
            assert_eq!(asked_in(mc, when(is(known), is(asked), q(0)), asked), 0, "{asked:?} under {known:?}");
        }
        for (known, asked) in [(IsNumber, IsInteger), (IsSyntax, IsIdentifier), (IsReal, IsExactInteger)] {
            assert_eq!(asked_in(mc, when(is(known), q(0), is(asked)), asked), 0, "{asked:?} where not {known:?}");
            assert_eq!(asked_in(mc, when(is(known), is(asked), q(0)), asked), 1, "{asked:?} under {known:?}");
        }
        for (known, asked) in [(IsInteger, IsExactInteger), (IsList, IsPair), (IsPair, IsList)] {
            assert_eq!(asked_in(mc, when(is(known), is(asked), q(0)), asked), 1, "{asked:?} under {known:?}");
        }
    });
    assert_eq!(number(|mc| prim(VectorRef, vec![constant(mc, &[1, 2]), q(1)])), Ok(2));
    assert_eq!(number(|mc| prim(VectorLength, vec![constant(mc, &[1, 2, 3])])), Ok(3));
    assert_eq!(number(|mc| prim(VectorRef, vec![constant(mc, &[1]), q(1)])), Err(Fault::OutOfRange));
    eval(|mc| prim(IsVector, vec![constant(mc, &[])]), |_, v| assert_eq!(v, Ok(Value::TRUE)));
}

fn ops<'gc>(mc: &Mutation<'gc>, core: Core<'gc>) -> Vec<Op> {
    all_ops(mc, compile(mc, Some(hosting(mc)), &core).unwrap())
}

#[test]
fn intrinsics_on_the_task_get_register_forms_and_unused_ones_go() {
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let ops = |core| ops(mc, core);
        let tail = ops(lambda(&[0], None, prim(MarkValue, vec![var(0), q(0)])));
        assert!(tail.iter().any(|op| matches!(op, Op::TailCallIntrinsic { args: 2, intrinsic: MarkValue, .. })), "{tail:?}");
        let used = ops(lambda(&[0], None, prim(Cons, vec![prim(MarkValue, vec![var(0), q(0)]), prim(Running, vec![])])));
        assert!(used.iter().any(|op| matches!(op, Op::CallIntrinsic2 { intrinsic: MarkValue, .. })), "{used:?}");
        assert!(used.iter().any(|op| matches!(op, Op::CallIntrinsic { args: 0, intrinsic: Running, .. })), "{used:?}");
        let unused = ops(lambda(&[0], None, let_(vec![(1, prim(MarkValue, vec![var(0), q(0)]))], q(1))));
        assert!(!unused.iter().any(|op| matches!(op, Op::CallIntrinsic2 { .. } | Op::CallIntrinsic { .. })), "{unused:?}");
        // Retain faulting `FrameMarks` and effectful `SetWinders` operations even when their results are
        // unused.
        let faulting = ops(lambda(&[0], None, let_(vec![(1, prim(FrameMarks, vec![var(0), q(0), var(0)]))], q(1))));
        assert!(faulting.iter().any(|op| matches!(op, Op::CallIntrinsic3 { intrinsic: FrameMarks, .. })), "{faulting:?}");
        let setting = ops(lambda(&[0], None, let_(vec![(1, prim(SetWinders, vec![var(0)]))], q(1))));
        assert!(setting.iter().any(|op| matches!(op, Op::CallIntrinsic1 { intrinsic: SetWinders, .. })), "{setting:?}");
        // Do not fold `MarkValue` even with constant arguments: its result depends on the runtime task.
        let constant = ops(lambda(&[], None, prim(MarkValue, vec![q(1), q(2)])));
        assert!(constant.iter().any(|op| matches!(op, Op::TailCallIntrinsic { intrinsic: MarkValue, .. })), "{constant:?}");
    });
    assert_eq!(error(|_| prim(MarkValue, vec![q(1)])), CompileError::Arity(Prim::Intrinsic(MarkValue)));
}

fn add_host<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    Ok(ragwort_vm::Reply::Value(fix(args.iter().map(|v| v.as_fixnum().unwrap()).sum())))
}

fn call_with<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    Ok(ragwort_vm::Reply::Call(args.get(0).unwrap(), Pairs::new(cx.mc()).list(&[args.get(1).unwrap()])?))
}

static HOSTS: [HostDef; 3] = [
    ragwort_vm::host!("add", -1, Purity::Impure, add_host),
    ragwort_vm::host!("add", -1, Purity::Discardable, add_host),
    ragwort_vm::host!("call-with", 2, Purity::Impure, call_with),
];
static ADD_HOST: &HostDef = &HOSTS[0];
static ADD_DISCARDABLE: &HostDef = &HOSTS[1];
static CALL_WITH: &HostDef = &HOSTS[2];
static ELSEWHERE: HostDef = ragwort_vm::host!("elsewhere", 0, Purity::Impure, add_host);

/// Creates the test module with three uninitialized variables and access to [`HOSTS`].
fn hosting<'gc>(mc: &Mutation<'gc>) -> Gc<'gc, ragwort_vm::objects::Module> {
    ragwort_vm::module::new(mc, Value::FALSE, &[fix(0), fix(1), fix(2)], &HOSTS).unwrap()
}

fn slot<'gc>(slot: u32) -> Core<'gc> {
    Core::Ref(Place::Slot { slot, checked: false })
}

fn checked<'gc>(slot: u32) -> Core<'gc> {
    Core::Ref(Place::Slot { slot, checked: true })
}

fn define<'gc>(slot: u32, value: Core<'gc>) -> Core<'gc> {
    Core::Set(Place::Slot { slot, checked: false }, Box::new(value))
}

fn set_checked<'gc>(slot: u32, value: Core<'gc>) -> Core<'gc> {
    Core::Set(Place::Slot { slot, checked: true }, Box::new(value))
}

#[test]
fn module_variables_are_slots() {
    assert_eq!(number(|_| seq(9, define(0, q(5)), add(slot(0), q(1)))), Ok(6));
    assert_eq!(number(|_| checked(1)), Err(Fault::Unbound));
    assert_eq!(number(|_| set_checked(1, q(1))), Err(Fault::Unbound));
    assert_eq!(number(|_| seq(9, define(1, q(1)), seq(8, set_checked(1, q(2)), checked(1)))), Ok(2));
    // Evaluate a module load at its original position, not later at its use.
    assert_eq!(number(|_| seq(9, define(0, q(5)), let_(vec![(1, slot(0))], seq(8, define(0, q(7)), var(1))))), Ok(5));
    assert_eq!(number(|_| seq(9, define(0, q(5)), let_(vec![(1, checked(0))], seq(8, define(0, q(7)), var(1))))), Ok(5));
    // Closures retain their defining module and can call themselves through its variables.
    fn countdown<'gc>() -> Core<'gc> {
        lambda(&[0], None, when(eq(var(0), q(0)), q(0), app(slot(2), vec![add(var(0), q(-1))])))
    }
    assert_eq!(number(|_| seq(9, define(2, countdown()), app(slot(2), vec![q(10)]))), Ok(0));
    // (define sum (lambda (n) (if (eq? n 0) 0 (+ n (sum (+ n -1)))))) (sum 100)
    fn sum<'gc>() -> Core<'gc> {
        let sum = lambda(&[1], None, when(eq(var(1), q(0)), q(0), add(var(1), app(slot(2), vec![add(var(1), q(-1))]))));
        seq(9, define(2, sum), app(slot(2), vec![q(100)]))
    }
    assert_eq!(number(|_| sum()), Ok(5050));
    assert_eq!(number(|_| seq(9, define(0, lambda(&[0], None, add(var(0), q(1)))), app(checked(0), vec![q(41)]))), Ok(42));
    assert_eq!(error(|_| slot(3)), CompileError::UnknownSlot(3));
    assert_eq!(error(|_| define(3, q(1))), CompileError::UnknownSlot(3));
    assert_eq!(error(|_| Core::Intrinsic(Prim::Slot(SlotOp::Store, 0), vec![])), CompileError::Arity(Prim::Slot(SlotOp::Store, 0)));
    assert_eq!(error(|_| Core::ApplyIntrinsic(Prim::Slot(SlotOp::Load, 0), vec![q(1)])), CompileError::Arity(Prim::Slot(SlotOp::Load, 0)));
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        assert_eq!(compile(mc, None, &slot(0)), Err(CompileError::UnknownSlot(0)));
        // Remove unused unchecked loads, but preserve checked loads because they may fault.
        let unused = |load| ops(mc, lambda(&[0], None, seq(1, load, q(1))));
        assert!(!unused(slot(0)).iter().any(|op| matches!(op, Op::LoadSlot { .. })));
        assert!(unused(checked(0)).iter().any(|op| matches!(op, Op::LoadSlotChecked { slot: 0, .. })));
        let tail = ops(mc, lambda(&[0], None, slot(1)));
        assert!(tail.windows(2).any(|w| matches!(w, [Op::LoadSlot { dst, slot: 1 }, Op::Return { src }] if dst == src)), "{tail:?}");
        let stored = ops(mc, lambda(&[0], None, define(2, var(0))));
        assert!(stored.iter().any(|op| matches!(op, Op::StoreSlot { slot: 2, .. })), "{stored:?}");
    });
}

#[test]
fn other_modules_variables_are_read_with_module_ref() {
    fn module_ref<'gc>(mc: &Mutation<'gc>, defined: bool, k: Core<'gc>) -> Core<'gc> {
        let other = ragwort_vm::module::new(mc, Value::FALSE, &[fix(0)], &[]).unwrap();
        if defined {
            ragwort_vm::objects::ModuleFields::items(other, mc).set(mc, 0, fix(9));
        }
        prim(ModuleRef, vec![Core::Quote(Value::object(mc, other)), k])
    }
    assert_eq!(number(|mc| module_ref(mc, true, q(0))), Ok(9));
    assert_eq!(number(|mc| module_ref(mc, false, q(0))), Err(Fault::Unbound));
    assert_eq!(number(|mc| module_ref(mc, true, q(1))), Err(Fault::OutOfRange));
    assert_eq!(number(|_| prim(ModuleRef, vec![q(0), q(0)])), Err(Fault::WrongType));
}

fn host<'gc>(def: &'static HostDef, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::Intrinsic(Prim::Host(def), args)
}

#[test]
fn host_functions_are_called_in_the_loop() {
    assert_eq!(number(|_| add(q(1), host(ADD_HOST, vec![q(10), q(20)]))), Ok(31));
    assert_eq!(number(|_| host(CALL_WITH, vec![lambda(&[0], None, add(var(0), q(1))), q(10)])), Ok(11));
    // Host functions are called only through direct primitives, so their arguments must fit in a frame
    // and cannot be spread.
    assert_eq!(error(|_| host(ADD_HOST, (1..=60).map(q).collect())), CompileError::TooManyArguments);
    assert_eq!(error(|_| host(CALL_WITH, vec![q(1)])), CompileError::Arity(Prim::Host(CALL_WITH)));
    assert_eq!(error(|_| Core::ApplyIntrinsic(Prim::Host(ADD_HOST), vec![q(1)])), CompileError::Arity(Prim::Host(ADD_HOST)));
    assert_eq!(error(|_| host(&ELSEWHERE, vec![])), CompileError::UnknownHost(&ELSEWHERE));
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| assert_eq!(compile(mc, None, &host(ADD_HOST, vec![])), Err(CompileError::UnknownHost(ADD_HOST))));
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let called = ops(mc, add(q(1), host(ADD_HOST, vec![q(10), q(20)])));
        assert!(called.iter().any(|op| matches!(op, Op::CallHost { args: 2, .. })), "{called:?}");
        let tail = ops(mc, lambda(&[0], None, host(ADD_HOST, vec![var(0)])));
        assert!(tail.iter().any(|op| matches!(op, Op::TailCallHost { args: 1, .. })), "{tail:?}");
        // Remove an unused host call only when its metadata permits discarding it.
        let unused = |def: &'static HostDef| ops(mc, lambda(&[0], None, let_(vec![(1, host(def, vec![var(0)]))], q(1))));
        assert!(unused(ADD_HOST).iter().any(|op| matches!(op, Op::CallHost { .. })));
        assert!(!unused(ADD_DISCARDABLE).iter().any(|op| matches!(op, Op::CallHost { .. })));
    });
}

#[test]
fn argument_order_hazard_boxing_and_deep_calls() {
    fn ops_of(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> Vec<Op> {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| all_ops(mc, compile(mc, Some(hosting(mc)), &build(mc)).expect("compiled")))
    }

    // 1. Correctness of boxing:
    // A) Primitive / intrinsic call: earlier argument reads x, later argument assigns x -> boxed.
    fn earlier_read_later_set<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let_(vec![(0, q(1))], prim(Cons, vec![var(0), seq(1, set(0, q(2)), q(3))]))
    }
    eval(earlier_read_later_set, |mc, result| {
        let pair = Pair::of(result.expect("success")).expect("pair");
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(1), fix(3)));
    });
    assert!(has_box_op(&ops_of(earlier_read_later_set)));

    // Vice versa: earlier argument assigns x, later argument reads x -> NOT boxed.
    fn earlier_set_later_read<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let_(vec![(0, q(1))], prim(Cons, vec![seq(1, set(0, q(2)), q(3)), var(0)]))
    }
    eval(earlier_set_later_read, |mc, result| {
        let pair = Pair::of(result.expect("success")).expect("pair");
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(3), fix(2)));
    });
    assert!(!has_box_op(&ops_of(earlier_set_later_read)));

    // B) Function application (Node::App): earlier argument reads x, later argument assigns x -> boxed.
    fn app_earlier_read_later_set<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        lambda(&[1], None, let_(vec![(0, q(10))], app(var(1), vec![var(0), seq(4, set(0, q(20)), q(30))])))
    }
    assert_eq!(number(|mc| app(app_earlier_read_later_set(mc), vec![lambda(&[2, 3], None, add(var(2), var(3)))])), Ok(40));
    assert!(has_box_op(&ops_of(app_earlier_read_later_set)));

    // Vice versa: earlier argument assigns x, later argument reads x -> NOT boxed.
    fn app_earlier_set_later_read<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        lambda(&[1], None, let_(vec![(0, q(10))], app(var(1), vec![seq(4, set(0, q(20)), q(30)), var(0)])))
    }
    assert_eq!(number(|mc| app(app_earlier_set_later_read(mc), vec![lambda(&[2, 3], None, add(var(2), var(3)))])), Ok(50));
    assert!(!has_box_op(&ops_of(app_earlier_set_later_read)));

    // 2. Wide and deeply nested calls completing rapidly:
    // Depth 250 nested calls with 4 arguments at each level and set! at the base.
    fn deep_nested<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let mut inner = seq(1001, set(0, add(var(0), q(1))), var(0));
        for _ in 0..250 {
            inner = app(var(1), vec![q(1), q(2), q(3), inner]);
        }
        let f = lambda(&[2, 3, 4, 5], None, add(var(2), var(5)));
        let_(vec![(0, q(0)), (1, f)], inner)
    }
    let start = std::time::Instant::now();
    assert_eq!(number(deep_nested), Ok(251));
    assert!(start.elapsed() < std::time::Duration::from_secs(2), "deeply nested calls should complete rapidly");

    // Wide call with 100 arguments where argument 0 reads x and argument 99 assigns x -> boxed.
    fn wide_call<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let mut args = Vec::with_capacity(100);
        args.push(var(0));
        for _ in 1..99 {
            args.push(q(0));
        }
        args.push(seq(1002, set(0, q(42)), q(0)));
        lambda(&[2], None, let_(vec![(0, q(1))], app(var(2), args)))
    }
    let start = std::time::Instant::now();
    let ops = ops_of(wide_call);
    assert!(has_box_op(&ops));
    assert!(start.elapsed() < std::time::Duration::from_secs(2), "wide call should complete rapidly");

    // Wide call vice versa: argument 0 assigns x and argument 99 reads x -> NOT boxed.
    fn wide_vice_versa<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        let mut args = Vec::with_capacity(100);
        args.push(seq(1002, set(0, q(42)), q(0)));
        for _ in 1..99 {
            args.push(q(0));
        }
        args.push(var(0));
        lambda(&[2], None, let_(vec![(0, q(1))], app(var(2), args)))
    }
    let start = std::time::Instant::now();
    let ops = ops_of(wide_vice_versa);
    assert!(!has_box_op(&ops));
    assert!(start.elapsed() < std::time::Duration::from_secs(2), "wide call vice versa should complete rapidly");
}

#[test]
fn argument_hazards_are_found_among_many_assigned_variables() {
    const VARS: u32 = 70;
    const LAST: u32 = VARS - 1;
    // Assigns every variable, then builds `(cons hazard sum)`, where `sum` reads them all.
    fn program<'gc>(hazard: Core<'gc>) -> Core<'gc> {
        let mut sum = var(0);
        for v in 1..VARS {
            sum = add(sum, var(v));
        }
        let mut body = prim(Cons, vec![hazard, sum]);
        for v in 0..LAST {
            body = seq(1000 + v, set(v, q(5)), body);
        }
        let_((0..VARS).map(|v| (v, q(1))).collect(), body)
    }
    fn read_then_set<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        program(prim(Cons, vec![var(LAST), seq(2000, set(LAST, q(2)), q(3))]))
    }
    fn set_then_read<'gc>(_: &Mutation<'gc>) -> Core<'gc> {
        program(prim(Cons, vec![seq(2000, set(LAST, q(2)), q(3)), var(LAST)]))
    }
    fn boxes(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>) -> bool {
        let mut arena = Arena::new(1 << 24, 0);
        arena.mutate(|mc| has_box_op(&all_ops(mc, compile(mc, Some(hosting(mc)), &build(mc)).expect("compiled"))))
    }
    let total = i64::from(LAST) * 5 + 2;
    eval(read_then_set, |mc, result| {
        let outer = Pair::of(result.expect("success")).expect("pair");
        let inner = Pair::of(outer.head(mc)).expect("pair");
        assert_eq!((inner.head(mc), inner.tail(mc), outer.tail(mc)), (fix(1), fix(3), fix(total)));
    });
    eval(set_then_read, |mc, result| {
        let outer = Pair::of(result.expect("success")).expect("pair");
        let inner = Pair::of(outer.head(mc)).expect("pair");
        assert_eq!((inner.head(mc), inner.tail(mc), outer.tail(mc)), (fix(3), fix(2), fix(total)));
    });
    assert!(boxes(read_then_set));
    assert!(!boxes(set_then_read));
}
