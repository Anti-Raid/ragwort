use std::sync::atomic::{AtomicU32, Ordering};

use ragwort_types::gc::{Arena, Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_vm::Intrinsic::{Add, Car, Cons, Eq, MakePromptTag};
use ragwort_vm::objects::{Condition, ConditionFields, Global};
use ragwort_vm::{Fault, Intrinsic, MIN_SEGMENT, Machine, Outcome, Request};

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
}

#[test]
fn lambdas_take_more_parameters_than_registers() {
    for n in [63u32, 64, 65, 100, 300] {
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
