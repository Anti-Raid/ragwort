use std::sync::atomic::{AtomicU32, Ordering};

use ragwort_types::constant::Constants;
use ragwort_types::gc::{Arena, Gc, Mutation, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_vm::Intrinsic::{Add, Car, Cons, Eq, MakeBox, MakePromptTag, Not, SetBox, Unbox};
use ragwort_vm::frame::MAX_PARAMS;
use ragwort_vm::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields, Global};
use ragwort_vm::{Fault, Intrinsic, MIN_SEGMENT, Machine, Op, Outcome, Read, Request};

use super::*;

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

/// `a`, then `b`, with `a`'s value bound to `v`, which nothing reads.
fn seq<'gc>(v: u32, a: Core<'gc>, b: Core<'gc>) -> Core<'gc> {
    let_(vec![(v, a)], b)
}

/// A lambda, numbered apart from every other the tests make.
fn lambda<'gc>(params: &[u32], rest: Option<u32>, body: Core<'gc>) -> Core<'gc> {
    static NEXT: AtomicU32 = AtomicU32::new(0);
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    Core::Lambda(Lambda { id, params: params.iter().map(|&v| Var(v)).collect(), rest: rest.map(Var), body: Box::new(body) })
}

fn app<'gc>(f: Core<'gc>, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::App(Box::new(f), args)
}

fn set<'gc>(v: u32, value: Core<'gc>) -> Core<'gc> {
    Core::Set(Place::Local(Var(v)), Box::new(value))
}

fn global<'gc>(mc: &Mutation<'gc>) -> Gc<'gc, Global> {
    Global::new(mc, Value::VOID, Value::VOID, false).unwrap()
}

fn gref<'gc>(g: Gc<'gc, Global>) -> Core<'gc> {
    Core::Ref(Place::Global(g))
}

/// Compiles what `build` makes, runs it to the end, and hands what it returned, or the fault
/// it raised, to `check`.
fn eval(build: impl for<'gc> FnOnce(&Mutation<'gc>) -> Core<'gc>, check: impl for<'gc> FnOnce(&Mutation<'gc>, Result<Value<'gc>, Fault>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let thunk = compile(mc, &build(mc)).unwrap();
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let result = loop {
            match machine.run(mc).unwrap() {
                Outcome::Paused => {}
                Outcome::Yielded(_) | Outcome::Host(_) => panic!("yielded"),
                Outcome::Done(value) => break Ok(value),
                Outcome::Raised(raised) => break Err(*raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap()),
            }
        };
        check(mc, result);
    });
}

/// What `build` returns, as a fixnum.
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
    arena.mutate(|mc| compile(mc, &build(mc)).unwrap_err())
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

    // ((lambda (x) (let ((get (lambda () x))) (set! x 41) (+ (get) 1))) 0): a captured
    // parameter is boxed on entry, and the closure sees it assigned after it was made.
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

#[test]
fn rest_parameters() {
    // ((lambda (a . rest) (cons a rest)) 1 2 3)
    eval(|_| app(lambda(&[0], Some(1), prim(Cons, vec![var(0), var(1)])), vec![q(1), q(2), q(3)]), |mc, result| assert_eq!(items(mc, result.unwrap()), [1, 2, 3]));
    // (((lambda (a . rest) (lambda () rest)) 1 2 3)): a captured rest list.
    eval(|_| app(app(lambda(&[0], Some(1), lambda(&[], None, var(1))), vec![q(1), q(2), q(3)]), vec![]), |mc, result| assert_eq!(items(mc, result.unwrap()), [2, 3]));
}

#[test]
fn globals() {
    // (define sum (lambda (n) (if (eq? n 0) 0 (+ n (sum (+ n -1)))))) (sum 100)
    assert_eq!(
        number(|mc| {
            let g = global(mc);
            let sum = lambda(&[1], None, when(eq(var(1), q(0)), q(0), add(var(1), app(gref(g), vec![add(var(1), q(-1))]))));
            seq(0, Core::DefineGlobal(g, Box::new(sum)), app(gref(g), vec![q(100)]))
        }),
        Ok(5050)
    );
    // (define g 1) (set! g (+ g 1)) g
    assert_eq!(
        number(|mc| {
            let g = global(mc);
            let set = Core::Set(Place::Global(g), Box::new(add(gref(g), q(1))));
            seq(0, Core::DefineGlobal(g, Box::new(q(1))), seq(1, set, gref(g)))
        }),
        Ok(2)
    );
    // A global that isn't defined can't be read or assigned.
    assert_eq!(number(|mc| add(gref(global(mc)), q(1))), Err(Fault::Unbound));
    assert_eq!(number(|mc| Core::Set(Place::Global(global(mc)), Box::new(q(1)))), Err(Fault::Unbound));
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
        Core::Lambda(Lambda { id: 7, params: Vec::new(), rest: None, body: Box::new(body) })
    }
    assert_eq!(error(|_| app(numbered(q(1)), vec![numbered(q(2))])), CompileError::SameLambda(7));
    assert_eq!(error(|_| Core::Intrinsic(Prim::Request(Request::Capture), vec![q(1)])), CompileError::Arity(Prim::Request(Request::Capture)));
    assert_eq!(error(|_| (0..2000).fold(q(0), |e, _| add(q(1), e))), CompileError::TooDeep);
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
}

/// Calls of `argc` values made with `live` boxes held across them, around where the frame's own
/// registers end and its scratch ones, which stage calls, begin.
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
    // Captured and assigned parameters past the registers.
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
fn micropass_optimizations() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        // 1. Unmutated captured variables are never boxed (`assign` pass only boxes `Set` vars).
        let unmutated_capture = lambda(&[0], None, lambda(&[], None, var(0)));
        let thunk = compile(mc, &unmutated_capture).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!has_box_op(&ops), "immutable captured variable should not be boxed: {ops:?}");

        // 2. Mutually recursive `letrec` lambdas compile to a single `Op::NewClosure { count: 2 }`
        //    with zero heap boxes (`letrec` fixing pass).
        let even = lambda(&[2], None, when(eq(var(2), q(0)), Core::Quote(Value::TRUE), app(var(1), vec![add(var(2), q(-1))])));
        let odd = lambda(&[3], None, when(eq(var(3), q(0)), Core::Quote(Value::FALSE), app(var(0), vec![add(var(3), q(-1))])));
        let mutual = letrec(vec![(0, even), (1, odd)], app(var(0), vec![q(10)]));
        let thunk = compile(mc, &mutual).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(!has_box_op(&ops), "mutually recursive lambdas should not be boxed: {ops:?}");
        assert!(ops.iter().any(|op| matches!(op, Op::NewClosure { count: 2, .. })), "expected batch NewClosure(count: 2): {ops:?}");

        // 3. `cp0` folds constants, inlines local helpers, and eliminates `not` in `if` tests.
        //    (let ((inc (lambda (x) (+ x 1)))) (if (not (eq? (inc 41) 42)) 0 (inc 99))) -> 100
        let inc = lambda(&[1], None, add(var(1), q(1)));
        let test = prim(Not, vec![eq(app(var(0), vec![q(41)]), q(42))]);
        let folded = let_(vec![(0, inc)], when(test, q(0), app(var(0), vec![q(99)])));
        let thunk = compile(mc, &folded).unwrap();
        let ops = all_ops(mc, thunk);
        assert_eq!(ops.len(), 2, "expected constant-folded [LoadConst, Return], got {ops:?}");
        assert!(matches!(ops.as_slice(), [Op::LoadConst { .. }, Op::Return { .. }]));

        // 4. `Place::Import` of a defined prelude wrapper lowers to a direct intrinsic, and
        //    `(+ x 1)` then compiles to `AddImm`.
        let add_fn = compile(mc, &lambda(&[], Some(0), Core::ApplyIntrinsic(Prim::Intrinsic(Add), vec![var(0)]))).unwrap();
        let mut machine = Machine::new(mc, MIN_SEGMENT, add_fn, &[]).unwrap();
        let Outcome::Done(add_closure) = machine.run(mc).unwrap() else { panic!() };
        let import_add = Global::new(mc, Value::VOID, add_closure, true).unwrap();
        let call_import = app(Core::Ref(Place::Import(import_add)), vec![var(0), q(1)]);
        let thunk = compile(mc, &lambda(&[0], None, call_import)).unwrap();
        let ops = all_ops(mc, thunk);
        assert!(
            matches!(ops.as_slice(), [.., Op::AddImm { dst, a: 1, imm: 1 }, Op::Return { src }] if dst == src),
            "expected imported `(+ x 1)` to compile to AddImm: {ops:?}"
        );

        // 4a. An imported `add1`-style wrapper, `(lambda (z) (+ z 1))`, compiles to
        //     `[AddImm, Return]`, which `cp0` recognizes and inlines into its callers.
        let add1_fn = compile(mc, &lambda(&[0], None, add(var(0), q(1)))).unwrap();
        let mut machine = Machine::new(mc, MIN_SEGMENT, add1_fn, &[]).unwrap();
        let Outcome::Done(add1_closure) = machine.run(mc).unwrap() else { panic!() };
        let add1_ops = add1_closure.downcast::<Closure>(mc).unwrap().code(mc).unwrap().ops(mc).unwrap().to_vec();
        assert!(matches!(add1_ops.as_slice(), [Op::AddImm { a: 1, imm: 1, .. }, Op::Return { .. }]), "{add1_ops:?}");
        let import_add1 = Global::new(mc, Value::VOID, add1_closure, true).unwrap();
        // (lambda (x) (add1 (add1 x))) -> two AddImms, no calls.
        let twice = app(Core::Ref(Place::Import(import_add1)), vec![app(Core::Ref(Place::Import(import_add1)), vec![var(0)])]);
        let thunk = compile(mc, &lambda(&[0], None, twice)).unwrap();
        let ops = all_ops(mc, thunk);
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
            let thunk = compile(mc, &lambda(&[0], None, expr)).unwrap();
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
            let thunk = compile(mc, &lambda(&[0], None, expr)).unwrap();
            let ops = all_ops(mc, thunk);
            assert!(!ops.iter().any(|op| matches!(op, Op::AddImm { .. })), "expected no AddImm: {ops:?}");
            assert!(
                ops.iter().any(|op| matches!(op, Op::TailCallIntrinsic { intrinsic, .. } if *intrinsic == want)),
                "expected TailCallIntrinsic({want:?}): {ops:?}"
            );
        }

        // 4c. A leading effect floats out of an intrinsic's first argument, so the constant behind
        //     it counts: `(+ (begin (f) 1) x)` compiles to `AddImm`, `(+ (begin (f) 2) 3)` to 5.
        let effect_first = add(seq(9, app(var(1), vec![]), q(1)), var(0));
        let ops = all_ops(mc, compile(mc, &lambda(&[0, 1], None, effect_first)).unwrap());
        assert!(ops.iter().any(|op| matches!(op, Op::AddImm { imm: 1, .. })), "expected AddImm: {ops:?}");
        assert!(!ops.iter().any(|op| matches!(op, Op::TailCallIntrinsic { intrinsic: Add, .. })), "{ops:?}");
        let folds = add(seq(9, app(var(1), vec![]), q(2)), q(3));
        let ops = all_ops(mc, compile(mc, &lambda(&[0, 1], None, folds)).unwrap());
        assert!(!ops.iter().any(|op| matches!(op, Op::AddImm { .. } | Op::TailCallIntrinsic { intrinsic: Add, .. })), "{ops:?}");

        // 5. Store-to-load forwarding on `cadr`/`cons` and `unbox`/`box` eliminates allocations.
        //    (lambda (x y) (+ (cadr (cons x (cons y '()))) (unbox (box 1)))) -> (lambda (x y) (+ y 1))
        let cadr_cons = prim(Intrinsic::Cadr, vec![prim(Cons, vec![var(0), prim(Cons, vec![var(1), Core::Quote(Value::NIL)])])]);
        let unbox_box = prim(Unbox, vec![prim(MakeBox, vec![q(1)])]);
        let forwarded = lambda(&[0, 1], None, add(cadr_cons, unbox_box));
        let thunk = compile(mc, &forwarded).unwrap();
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

        // 6. Tail-recursive local loop contifies into an in-frame backward `Jump` with zero closures.
        let looping = lambda(&[1, 2], None, when(eq(var(1), q(0)), var(2), app(var(0), vec![add(var(1), q(-1)), add(var(2), var(1))])));
        let loop_expr = letrec(vec![(0, looping)], app(var(0), vec![q(10), q(0)]));
        let thunk = compile(mc, &loop_expr).unwrap();
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
        let thunk = compile(mc, &proc_lam).unwrap();
        let ops = all_ops(mc, thunk);
        assert_eq!(ops.len(), 2, "expected (procedure? (lambda ...)) to fold to #t: {ops:?}");

        // (continuation? (lambda (x) x)) -> #f
        let cont_lam = prim(Intrinsic::IsContinuation, vec![lambda(&[0], None, var(0))]);
        let thunk = compile(mc, &cont_lam).unwrap();
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
        let thunk = compile(mc, &dom).unwrap();
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
        let thunk = compile(mc, &list_len_loop).unwrap();
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
        let thunk = compile(mc, &nested_loops).unwrap();
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
            // Bind 260 non-foldable variables `v_0 .. v_259` via `(unbox (box 1))`? Wait: `cp0`
            // folds `(unbox (box 1))`! Use `(car (cdr (list 0 1)))`? `cp0` folds that too!
            // Use `MakeBox(1)` for 260 distinct live boxes and unbox the first and last inside a
            // contified loop!
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
        let thunk = compile(mc, &length).unwrap();
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

        // And it counts: run the compiled `length` on lists of 0, 1, and 1000 elements.
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

#[test]
fn only_imports_that_just_spread_into_an_intrinsic_inline_as_it() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let run = |thunk| match Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap().run(mc).unwrap() {
            Outcome::Done(value) => value,
            _ => panic!(),
        };
        let spread = |i| Core::ApplyIntrinsic(Prim::Intrinsic(i), vec![var(0)]);
        // `(lambda xs (+ . xs))` inlines; `(lambda xs (not (+ . xs)))` and `(lambda xs (car (cons . xs)))`
        // do more with the result than return it, so they must not.
        for (body, want) in [(spread(Add), fix(7)), (prim(Not, vec![spread(Add)]), Value::FALSE), (prim(Car, vec![spread(Cons)]), fix(3))] {
            let closure = run(compile(mc, &lambda(&[], Some(0), body)).unwrap());
            for defined in [Place::Import(Global::new(mc, Value::VOID, closure, true).unwrap()), Place::Global(Global::new(mc, Value::VOID, closure, true).unwrap())] {
                assert_eq!(run(compile(mc, &app(Core::Ref(defined), vec![q(3), q(4)])).unwrap()), want);
            }
        }
    });
}

/// How many ops call `intrinsic`, in any form.
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

/// A vector literal of `xs`.
fn constant<'gc>(mc: &Mutation<'gc>, xs: &[i64]) -> Core<'gc> {
    let items: Vec<_> = xs.iter().map(|&x| fix(x)).collect();
    Core::Quote(ragwort_types::vector::Vectors::new(mc).immutable_from_slice(&items).unwrap().value(mc))
}

/// Whether `core` compiles to just loading a constant.
fn folds<'gc>(mc: &Mutation<'gc>, core: Core<'gc>) -> bool {
    matches!(all_ops(mc, compile(mc, &core).unwrap()).as_slice(), [Op::LoadConst { .. }, Op::Return { .. }])
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

        // An index past the end is left to fault when it runs.
        let past = all_ops(mc, compile(mc, &prim(VectorRef, vec![constant(mc, &[1]), q(1)])).unwrap());
        assert_eq!(calls(&past, VectorRef), 1, "{past:?}");

        // A vector `vector` makes can change, so reading one isn't folded.
        let made = prim(VectorRef, vec![prim(MakeVectorOf, vec![q(1), q(2)]), q(0)]);
        let ops = all_ops(mc, compile(mc, &made).unwrap());
        assert_eq!(calls(&ops, VectorRef), 1, "{ops:?}");

        // Under `(pair? x)`, `(vector? x)` is false, and under `(vector? x)`, it's true:
        // (lambda (x) (if (pair? x) (vector? x) (if (vector? x) (vector? x) 0))) has one test left.
        let is = |i: Intrinsic| prim(i, vec![var(0)]);
        let tests = when(is(IsPair), is(IsVector), when(is(IsVector), is(IsVector), q(0)));
        let ops = all_ops(mc, compile(mc, &lambda(&[0], None, tests)).unwrap());
        assert_eq!(calls(&ops, IsVector), 1, "{ops:?}");
    });
    assert_eq!(number(|mc| prim(VectorRef, vec![constant(mc, &[1, 2]), q(1)])), Ok(2));
    assert_eq!(number(|mc| prim(VectorLength, vec![constant(mc, &[1, 2, 3])])), Ok(3));
    assert_eq!(number(|mc| prim(VectorRef, vec![constant(mc, &[1]), q(1)])), Err(Fault::OutOfRange));
    eval(|mc| prim(IsVector, vec![constant(mc, &[])]), |_, v| assert_eq!(v, Ok(Value::TRUE)));
}

fn read<'gc>(r: Read, args: Vec<Core<'gc>>) -> Core<'gc> {
    Core::Intrinsic(Prim::Read(r), args)
}

fn ops<'gc>(mc: &Mutation<'gc>, core: Core<'gc>) -> Vec<Op> {
    all_ops(mc, compile(mc, &core).unwrap())
}

#[test]
fn reads_get_register_forms_and_unused_ones_go() {
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let ops = |core| ops(mc, core);
        let tail = ops(lambda(&[0], None, read(Read::MarkValue, vec![var(0), q(0)])));
        assert!(tail.iter().any(|op| matches!(op, Op::TailCallRead { args: 2, read: Read::MarkValue, .. })), "{tail:?}");
        let used = ops(lambda(&[0], None, prim(Cons, vec![read(Read::MarkValue, vec![var(0), q(0)]), read(Read::Running, vec![])])));
        assert!(used.iter().any(|op| matches!(op, Op::Read2 { read: Read::MarkValue, .. })), "{used:?}");
        assert!(used.iter().any(|op| matches!(op, Op::CallRead { args: 0, read: Read::Running, .. })), "{used:?}");
        let unused = ops(lambda(&[0], None, let_(vec![(1, read(Read::MarkValue, vec![var(0), q(0)]))], q(1))));
        assert!(!unused.iter().any(|op| matches!(op, Op::Read2 { .. } | Op::CallRead { .. })), "{unused:?}");
        // One that can fault stays.
        let faulting = ops(lambda(&[0], None, let_(vec![(1, read(Read::FrameMarks, vec![var(0), q(0), var(0)]))], q(1))));
        assert!(faulting.iter().any(|op| matches!(op, Op::CallRead { args: 3, read: Read::FrameMarks, .. })), "{faulting:?}");
    });
    assert_eq!(error(|_| read(Read::MarkValue, vec![q(1)])), CompileError::Arity(Prim::Read(Read::MarkValue)));
    assert_eq!(error(|_| Core::ApplyIntrinsic(Prim::Read(Read::Running), vec![q(1)])), CompileError::Arity(Prim::Read(Read::Running)));
}
