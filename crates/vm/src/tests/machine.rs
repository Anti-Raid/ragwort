use ragwort_types::gc::{Arena, Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::vector::Vectors;

use super::*;
use crate::Intrinsic::{Add, Car, Cdr, Cons, Eq, IsNull, IsValues, MakeBox, MakePromptTag, SetBox, Unbox, Values, ValuesLength, ValuesRef};
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields, MultiValue, MultiValueFields, Tag};
use crate::{Capture, Fault, Op, Request};

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

/// One function of a test module: its arity, capture list and code.
type Func<'a> = (i64, &'a [Capture], &'a [Op]);

/// Functions sharing a constant table of `constants`, then the functions themselves, so
/// function `i` is constant `constants.len() + i`.
fn module<'gc>(mc: &Mutation<'gc>, constants: &[Value<'gc>], funcs: &[Func<'_>]) -> Vec<Gc<'gc, Bytecode>> {
    let codes: Vec<_> = funcs
        .iter()
        .map(|&(arity, captures, ops)| {
            let (ops, captures) = (mc.frozen(Box::from(ops)).unwrap(), mc.frozen(Box::from(captures)).unwrap());
            Bytecode::new(mc, ops, Value::VOID, captures, arity).unwrap()
        })
        .collect();
    let mut table = constants.to_vec();
    table.extend(codes.iter().map(|&c| Value::object(mc, c)));
    let table = Vectors::new(mc).immutable_from_slice(&table).unwrap().value(mc);
    codes.iter().for_each(|c| c.set_constants(mc, table));
    codes
}

/// A constant that [`call`] and [`outcome`] make a prompt tag, the same one each time.
const TAG: i64 = i64::MIN;

fn table<'gc>(mc: &Mutation<'gc>, constants: &[i64]) -> Vec<Value<'gc>> {
    let tag = Value::object(mc, Tag::new(mc, Value::VOID).unwrap());
    constants.iter().map(|&n| if n == TAG { tag } else { fix(n) }).collect()
}

fn closure<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>) -> Value<'gc> {
    Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID).unwrap())
}

fn list<'gc>(mc: &Mutation<'gc>, items: &[i64]) -> Value<'gc> {
    let pairs = Pairs::new(mc);
    items.iter().rev().fold(Value::NIL, |tail, &n| pairs.cons(fix(n), tail).unwrap().value(mc))
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

/// What a task returned, as fixnums: each of a `MultiValue`'s, or the one value.
fn fixnums<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Vec<i64> {
    spread(mc, value).iter().map(|v| v.as_fixnum().unwrap()).collect()
}

fn spread<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Vec<Value<'gc>> {
    let Some(values) = value.downcast::<MultiValue>(mc) else { return vec![value] };
    let items = values.items(mc);
    (0..items.len()).map(|i| items.get(i)).collect()
}

/// The fault behind a raised condition.
fn fault<'gc>(mc: &Mutation<'gc>, raised: Value<'gc>) -> Fault {
    *raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap()
}

/// Runs `machine` to the end within this step, going on past each pause.
fn to_end<'gc>(mc: &Mutation<'gc>, machine: &mut Machine) -> Result<Outcome<'gc>, Fault> {
    loop {
        match machine.run(mc)? {
            Outcome::Paused => {}
            outcome => return Ok(outcome),
        }
    }
}

/// Calls `code` with `args` to the end, in one step. Lists come back as their digits, `(1 2 3)`
/// as 123.
fn run<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, args: &[Value<'gc>]) -> Result<Vec<i64>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), args)?;
    let values = match to_end(mc, &mut machine)? {
        Outcome::Done(value) => spread(mc, value),
        Outcome::Raised(raised) => return Err(fault(mc, raised)),
        Outcome::Paused | Outcome::Yielded(_) => unreachable!(),
    };
    let digits = |v: Value<'gc>| items(mc, v).iter().fold(0, |a, &n| a * 10 + n);
    Ok(values.iter().map(|&v| if Pair::of(v).is_some() { digits(v) } else { v.as_fixnum().unwrap() }).collect())
}

/// Runs the machine to the end a step at a time, so the arena collects as it goes, and returns
/// its values as fixnums, and how many runs it took.
fn finish(arena: &mut Arena, mut machine: Machine) -> Result<(Vec<i64>, usize), Fault> {
    for runs in 1.. {
        let done = arena.step(|mc| -> Result<_, Fault> {
            Ok(match machine.run(mc)? {
                Outcome::Done(value) => Some(fixnums(mc, value)),
                Outcome::Raised(raised) => return Err(fault(mc, raised)),
                Outcome::Paused => None,
                Outcome::Yielded(_) => unreachable!(),
            })
        })??;
        if let Some(values) = done {
            return Ok((values, runs));
        }
    }
    unreachable!()
}

/// Calls function 0 of a module with `args` to the end, in one run.
fn call(constants: &[i64], funcs: &[Func<'_>], args: &[i64]) -> Result<Vec<i64>, Fault> {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let constants = table(mc, constants);
        let codes = module(mc, &constants, funcs);
        let args: Vec<_> = args.iter().map(|&n| fix(n)).collect();
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &args)?;
        match to_end(mc, &mut machine)? {
            Outcome::Done(value) => Ok(fixnums(mc, value)),
            Outcome::Raised(raised) => Err(fault(mc, raised)),
            Outcome::Paused | Outcome::Yielded(_) => unreachable!(),
        }
    })
}

/// Calls function 0 of a module to the end and hands its outcome to `check`.
fn outcome(constants: &[i64], funcs: &[Func<'_>], check: impl for<'gc> FnOnce(&Mutation<'gc>, Outcome<'gc>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let constants = table(mc, constants);
        let codes = module(mc, &constants, funcs);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap();
        check(mc, to_end(mc, &mut machine).unwrap());
    });
}

/// `(define (sum n) (if (eq? 0 n) 0 (+ n (sum (+ n -1)))))`, with constants `0` and `-1`.
const SUM: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::LoadAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::LoadAcc { dst: 9 },
    Op::Move { dst: 8, src: 0 },
    Op::Call { base: 8, args: 1 },
    Op::LoadAcc { dst: 4 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::LoadAcc { dst: 3 },
    Op::Return { src: 3 },
];

#[test]
fn deep_recursion_crosses_segments() {
    assert_eq!(call(&[0, -1], &[(1, &[], SUM)], &[10_000]), Ok(vec![50_005_000]));
    assert_eq!(call(&[0, -1], &[(1, &[], SUM)], &[]), Err(Fault::Arity));
}

#[test]
fn calls_start_past_the_callers_link() {
    // A function of one argument has its link in register 2, so a call there would overwrite it.
    let clobber = [Op::Move { dst: 2, src: 1 }, Op::Call { base: 2, args: 0 }, Op::Return { src: 1 }];
    assert_eq!(call(&[], &[(1, &[], &clobber)], &[0]), Err(Fault::Malformed));
}

#[test]
fn a_finished_machine_stays_finished() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let codes = module(mc, &[fix(0), fix(-1)], &[(1, &[], SUM)]);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[fix(3)]).unwrap();
        assert_eq!(to_end(mc, &mut machine), Ok(Outcome::Done(fix(6))));
        assert_eq!(machine.run(mc), Err(Fault::Finished));
    });
}

#[test]
fn runs_pause_so_the_arena_can_collect() {
    // (let loop ((n 200000) (acc 0)) (if (eq? 0 n) acc (loop (+ n -1) (car (cons (+ acc 1) n))))):
    // 200000 pairs of garbage, several times what the arena holds.
    let main = [
        Op::NewClosure { dst: 2, count: 1, code: 5 },
        Op::LoadConst { dst: 3, index: 3 },
        Op::LoadConst { dst: 4, index: 0 },
        Op::TailCall { base: 2, args: 2 },
    ];
    let looping = [
        Op::LoadConst { dst: 4, index: 0 },
        Op::Move { dst: 5, src: 1 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 6 },
        Op::JumpIfFalse { test: 6, offset: 1 },
        Op::Return { src: 2 },
        Op::Move { dst: 4, src: 2 },
        Op::LoadConst { dst: 5, index: 1 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 4 },
        Op::Move { dst: 5, src: 1 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Cons },
        Op::LoadAcc { dst: 4 },
        Op::CallIntrinsic { base: 4, args: 1, intrinsic: Car },
        Op::LoadAcc { dst: 7 },
        Op::Move { dst: 4, src: 1 },
        Op::LoadConst { dst: 5, index: 2 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 6 },
        Op::Move { dst: 5, src: 0 },
        Op::TailCall { base: 5, args: 2 },
    ];
    let mut arena = Arena::new(1 << 20, 0);
    let machine = arena.mutate(|mc| {
        let codes = module(mc, &[fix(0), fix(1), fix(-1), fix(200_000)], &[(0, &[], &main), (2, &[], &looping)]);
        Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap()
    });
    let (values, runs) = finish(&mut arena, machine).unwrap();
    assert_eq!(values, [200_000]);
    let (majors, minors) = arena.collections();
    assert!(runs > 10 && majors + minors > 10, "{runs} runs, {majors} + {minors} collections");
    assert!(arena.peak() <= (1 << 20) - (1 << 20) / 16, "peak {}", arena.peak());
}

#[test]
fn rest_arguments_and_apply() {
    // (lambda (a . rest) (cons a rest)), (lambda (a b c) (+ a b c)), then tail and non-tail
    // (apply f x list).
    let variadic: Func<'_> = (-2, &[], &[Op::TailCallIntrinsic { base: 1, args: 2, intrinsic: Cons }]);
    let exact: Func<'_> = (3, &[], &[Op::TailCallIntrinsic { base: 1, args: 3, intrinsic: Add }]);
    let tail_apply: Func<'_> = (3, &[], &[Op::TailCallRequest { base: 1, args: 3, request: Request::Apply }]);
    let apply = [
        Op::Move { dst: 5, src: 1 },
        Op::Move { dst: 6, src: 2 },
        Op::Move { dst: 7, src: 3 },
        Op::CallRequest { base: 5, args: 3, request: Request::Apply },
        Op::LoadAcc { dst: 5 },
        Op::Return { src: 5 },
    ];
    let apply: Func<'_> = (3, &[], &apply);
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let codes = module(mc, &[], &[variadic, exact, tail_apply, apply]);
        let (variadic, exact) = (closure(mc, codes[0]), closure(mc, codes[1]));
        assert_eq!(run(mc, codes[0], &[fix(1), fix(2), fix(3)]), Ok(vec![123]));
        assert_eq!(run(mc, codes[0], &[fix(1)]), Ok(vec![1]));
        for entry in [2, 3] {
            assert_eq!(run(mc, codes[entry], &[variadic, fix(1), list(mc, &[2, 3])]), Ok(vec![123]));
            assert_eq!(run(mc, codes[entry], &[variadic, fix(1), Value::NIL]), Ok(vec![1]));
            assert_eq!(run(mc, codes[entry], &[exact, fix(1), list(mc, &[2, 3])]), Ok(vec![6]));
            assert_eq!(run(mc, codes[entry], &[exact, fix(1), list(mc, &[2])]), Err(Fault::Arity));
            assert_eq!(run(mc, codes[entry], &[exact, fix(1), list(mc, &[2, 3, 4])]), Err(Fault::Arity));
            assert_eq!(run(mc, codes[entry], &[exact, fix(1), fix(2)]), Err(Fault::WrongType));
            assert_eq!(run(mc, codes[entry], &[fix(5), fix(1), Value::NIL]), Err(Fault::NotProcedure));
        }
        assert_eq!(run(mc, codes[0], &[]), Err(Fault::Arity));
    });
}

#[test]
fn multiple_values_are_an_object() {
    // (define (three) (values 1 2 3))
    let three: Func<'_> = (
        0,
        &[],
        &[
            Op::LoadConst { dst: 2, index: 0 },
            Op::LoadConst { dst: 3, index: 1 },
            Op::LoadConst { dst: 4, index: 2 },
            Op::TailCallIntrinsic { base: 2, args: 3, intrinsic: Values },
        ],
    );
    let funcs = |main: &'static [Op]| -> [Func<'static>; 2] { [(0, &[], main), three] };
    let constants = [1, 2, 3, 0];

    // The task returns it; (+ 1 (three)) is a type error.
    let tail = &[Op::NewClosure { dst: 3, count: 1, code: 5 }, Op::TailCall { base: 3, args: 0 }];
    assert_eq!(call(&constants, &funcs(tail), &[]), Ok(vec![1, 2, 3]));
    let add = &[
        Op::NewClosure { dst: 5, count: 1, code: 5 },
        Op::Call { base: 5, args: 0 },
        Op::LoadAcc { dst: 2 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    assert_eq!(call(&constants, &funcs(add), &[]), Err(Fault::WrongType));

    // (let ((v (three))) (if (values? v) (+ (values-length v) (values-ref v 0)) v))
    let apart = &[
        Op::NewClosure { dst: 5, count: 1, code: 5 },
        Op::Call { base: 5, args: 0 },
        Op::LoadAcc { dst: 2 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: IsValues },
        Op::LoadAcc { dst: 3 },
        Op::JumpIfFalse { test: 3, offset: 9 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: ValuesLength },
        Op::LoadAcc { dst: 4 },
        Op::Move { dst: 5, src: 2 },
        Op::LoadConst { dst: 6, index: 3 },
        Op::CallIntrinsic { base: 5, args: 2, intrinsic: ValuesRef },
        Op::LoadAcc { dst: 5 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 4 },
        Op::Return { src: 4 },
        Op::Return { src: 2 },
    ];
    assert_eq!(call(&constants, &funcs(apart), &[]), Ok(vec![4]));

    // (values) is an empty one.
    let none = &[Op::TailCallIntrinsic { base: 2, args: 0, intrinsic: Values }];
    assert_eq!(call(&constants, &funcs(none), &[]), Ok(vec![]));
}

/// Upvalues of a test's function 0 under the prelude: its procedures, and its prompt tag.
const CALL_CC: u32 = 0;
const WITH_HANDLER: u32 = 1;
const RAISE_CONTINUABLE: u32 = 2;
const RAISE: u32 = 3;
/// What the prelude's `raise` raises when a handler returns.
const RETURNED: i64 = -7;

/// What this VM leaves to native ragwort, written out in bytecode: a prompt with Racket's
/// default handler, which calls the thunk an abort passes under the prompt again, `call/cc`
/// in terms of it, and exceptions, whose handlers are a mark. Returns `run`, which calls a
/// thunk under the prompt, and the upvalues of a test's function 0.
fn prelude<'gc>(mc: &Mutation<'gc>) -> (Value<'gc>, Vec<Value<'gc>>) {
    let tag = Value::object(mc, Tag::new(mc, Value::VOID).unwrap());
    let key = Value::object(mc, Tag::new(mc, Value::VOID).unwrap());
    // Constants 0..4 are the tag, the handlers' key, '() and RETURNED; function i is 4 + i.
    let default_handler = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 0 },
        Op::Move { dst: 5, src: 1 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
    ];
    let run = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 4 },
        Op::Move { dst: 5, src: 1 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
    ];
    // (call/cc f): (capture tag (lambda (k) (f (lambda (v) (abort tag (lambda () (k v)))))))
    let call_cc = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 7 },
        Op::TailCallRequest { base: 3, args: 2, request: Request::Capture },
    ];
    let receiver = [Op::NewClosure { dst: 4, count: 1, code: 8 }, Op::LoadUpvalue { dst: 3, index: 0 }, Op::TailCall { base: 3, args: 1 }];
    let escape = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 9 },
        Op::TailCallRequest { base: 3, args: 2, request: Request::Abort },
    ];
    let call_upvalue = [Op::LoadUpvalue { dst: 2, index: 0 }, Op::LoadUpvalue { dst: 3, index: 1 }, Op::TailCall { base: 2, args: 1 }];
    // (with-exception-handler h thunk): (with-mark key (cons h (mark-value key '())) thunk)
    let with_handler = [
        Op::LoadConst { dst: 4, index: 1 },
        Op::LoadConst { dst: 5, index: 2 },
        Op::CallRequest { base: 4, args: 2, request: Request::MarkValue },
        Op::LoadAcc { dst: 6 },
        Op::Move { dst: 5, src: 1 },
        Op::CallIntrinsic { base: 5, args: 2, intrinsic: Cons },
        Op::LoadAcc { dst: 5 },
        Op::LoadConst { dst: 4, index: 1 },
        Op::Move { dst: 6, src: 2 },
        Op::TailCallRequest { base: 4, args: 3, request: Request::WithMark },
    ];
    // (let ((hs (mark-value key '())))
    //   (if (null? hs) (abort tag (lambda () obj)) (with-mark key (cdr hs) (lambda () ...))))
    let raising = |thunk| {
        [
            Op::LoadConst { dst: 3, index: 1 },
            Op::LoadConst { dst: 4, index: 2 },
            Op::CallRequest { base: 3, args: 2, request: Request::MarkValue },
            Op::LoadAcc { dst: 3 },
            Op::CallIntrinsic { base: 3, args: 1, intrinsic: IsNull },
            Op::LoadAcc { dst: 4 },
            Op::JumpIfFalse { test: 4, offset: 3 },
            Op::LoadConst { dst: 4, index: 0 },
            Op::NewClosure { dst: 5, count: 1, code: 13 },
            Op::TailCallRequest { base: 4, args: 2, request: Request::Abort },
            Op::CallIntrinsic { base: 3, args: 1, intrinsic: Car },
            Op::LoadAcc { dst: 7 },
            Op::CallIntrinsic { base: 3, args: 1, intrinsic: Cdr },
            Op::LoadAcc { dst: 5 },
            Op::NewClosure { dst: 6, count: 1, code: thunk },
            Op::LoadConst { dst: 4, index: 1 },
            Op::TailCallRequest { base: 4, args: 3, request: Request::WithMark },
        ]
    };
    let (raise_continuable, raise) = (raising(12), raising(15));
    let constant = [Op::LoadUpvalue { dst: 2, index: 0 }, Op::Return { src: 2 }];
    // (lambda () (h obj) (raise RETURNED))
    let raise_thunk = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::LoadUpvalue { dst: 4, index: 1 },
        Op::Call { base: 3, args: 1 },
        Op::LoadUpvalue { dst: 2, index: 2 },
        Op::LoadConst { dst: 3, index: 3 },
        Op::TailCall { base: 2, args: 1 },
    ];
    use Capture::{Register, Upvalue};
    let funcs: [Func<'_>; 12] = [
        (1, &[], &default_handler),
        (1, &[], &run),
        (1, &[], &call_cc),
        (1, &[Register(1)], &receiver),
        (1, &[Register(1)], &escape),
        (0, &[Upvalue(0), Register(1)], &call_upvalue),
        (2, &[], &with_handler),
        (1, &[], &raise_continuable),
        (0, &[Register(7), Register(1)], &call_upvalue),
        (0, &[Register(1)], &constant),
        (1, &[], &raise),
        (0, &[Register(7), Register(1), Register(0)], &raise_thunk),
    ];
    let codes = module(mc, &[tag, key, Value::NIL, fix(RETURNED)], &funcs);
    let close = |i: usize| closure(mc, codes[i]);
    (close(1), vec![close(2), close(6), close(7), close(10), tag])
}

/// Runs function 0 of a module under the prelude's prompt, with the prelude's procedures as its
/// upvalues and its `raise` taking VM faults, and hands the outcome to `check`.
fn prelude_outcome(constants: &[i64], funcs: &[Func<'_>], check: impl for<'gc> FnOnce(&Mutation<'gc>, Outcome<'gc>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let (run, upvalues) = prelude(mc);
        let constants = table(mc, constants);
        let codes = module(mc, &constants, funcs);
        let main = Closure::new(mc, Some(codes[0]), upvalues.len(), Value::VOID).unwrap();
        upvalues.iter().enumerate().for_each(|(i, &v)| main.items(mc).set(mc, i, v));
        let mut machine = Machine::new(mc, MIN_SEGMENT, run, &[Value::object(mc, main)]).unwrap();
        machine.set_fault(mc, upvalues[RAISE as usize]);
        check(mc, to_end(mc, &mut machine).unwrap());
    });
}

fn prelude_call(constants: &[i64], funcs: &[Func<'_>]) -> Vec<i64> {
    let mut values = Vec::new();
    prelude_outcome(constants, funcs, |mc, outcome| {
        let Outcome::Done(value) = outcome else { panic!("{outcome:?}") };
        values = fixnums(mc, value);
    });
    values
}

#[test]
fn prompts_take_aborts() {
    // (+ 1000 (call-with-prompt tag (lambda (a b) (+ a b)) (lambda () (+ 1 (abort tag 5 2)))))
    let main = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 2, code: 6 },
        Op::CallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let handler = [Op::TailCallIntrinsic { base: 1, args: 2, intrinsic: Add }];
    let thunk = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::LoadConst { dst: 5, index: 3 },
        Op::CallRequest { base: 3, args: 3, request: Request::Abort },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 4 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let constants = [TAG, 1000, 5, 2, 1];
    let with = |thunk: &[Op]| call(&constants, &[(0, &[], &main), (2, &[], &handler), (0, &[], thunk)], &[]);
    assert_eq!(with(&thunk), Ok(vec![1007]));

    // A thunk that returns passes its value through the prompt.
    assert_eq!(with(&[Op::LoadConst { dst: 2, index: 4 }, Op::Return { src: 2 }]), Ok(vec![1001]));

    // An abort to a tag with no prompt faults, and one to something that isn't a tag.
    let fresh = [
        Op::CallIntrinsic { base: 3, args: 0, intrinsic: MakePromptTag },
        Op::LoadAcc { dst: 3 },
        Op::CallRequest { base: 3, args: 1, request: Request::Abort },
    ];
    assert_eq!(with(&fresh), Err(Fault::NoPrompt));
    assert_eq!(with(&[Op::LoadConst { dst: 3, index: 1 }, Op::CallRequest { base: 3, args: 1, request: Request::Abort }]), Err(Fault::WrongType));
}

#[test]
fn composable_continuations_go_on_where_theyre_called() {
    // (+ 1000 (call-with-prompt tag h (lambda () (+ 1 (capture tag (lambda (k) (+ (k 1) (k 2))))))))
    let main = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 2, code: 7 },
        Op::CallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let handler = [Op::LoadConst { dst: 3, index: 5 }, Op::Return { src: 3 }];
    let thunk = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 9 },
        Op::CallRequest { base: 3, args: 2, request: Request::Capture },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 2 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let twice = [
        Op::Move { dst: 4, src: 1 },
        Op::LoadConst { dst: 5, index: 2 },
        Op::Call { base: 4, args: 1 },
        Op::LoadAcc { dst: 3 },
        Op::Move { dst: 5, src: 1 },
        Op::LoadConst { dst: 6, index: 3 },
        Op::Call { base: 5, args: 1 },
        Op::LoadAcc { dst: 4 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::Return { src: 3 },
    ];
    let constants = [TAG, 1000, 1, 2, 10, 0];
    let with = |f: &[Op]| call(&constants, &[(0, &[], &main), (-1, &[], &handler), (0, &[], &thunk), (1, &[], f)], &[]);
    assert_eq!(with(&twice), Ok(vec![1006]));
    // (k 10) in tail position.
    assert_eq!(with(&[Op::Move { dst: 3, src: 1 }, Op::LoadConst { dst: 4, index: 4 }, Op::TailCall { base: 3, args: 1 }]), Ok(vec![1012]));

    // (let ((kb (box 0)))
    //   (+ (call-with-prompt tag h (lambda () (+ 1 (capture tag (lambda (k) (set-box! kb k) 0)))))
    //      ((unbox kb) 10)))
    // k goes on after its prompt has returned, outside any prompt.
    let main = [
        Op::LoadConst { dst: 2, index: 5 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: MakeBox },
        Op::LoadAcc { dst: 2 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 2, code: 7 },
        Op::CallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
        Op::LoadAcc { dst: 3 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: Unbox },
        Op::LoadAcc { dst: 4 },
        Op::LoadConst { dst: 5, index: 4 },
        Op::Call { base: 4, args: 1 },
        Op::LoadAcc { dst: 4 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::Return { src: 3 },
    ];
    let keep = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: SetBox },
        Op::LoadConst { dst: 4, index: 5 },
        Op::Return { src: 4 },
    ];
    use Capture::{Register, Upvalue};
    let funcs = [(0, &[][..], &main[..]), (-1, &[], &handler), (0, &[Register(2)], &thunk), (1, &[Upvalue(0)], &keep)];
    assert_eq!(call(&constants, &funcs, &[]), Ok(vec![12]));
}

#[test]
fn marks_are_dropped_on_return_and_replaced_in_tail_position() {
    // (values (with-mark key 1 (lambda () (mark-value key 0))) (mark-value key 0))
    let main = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 6 },
        Op::CallRequest { base: 3, args: 3, request: Request::WithMark },
        Op::LoadAcc { dst: 2 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::CallRequest { base: 3, args: 2, request: Request::MarkValue },
        Op::LoadAcc { dst: 3 },
        Op::TailCallIntrinsic { base: 2, args: 2, intrinsic: Values },
    ];
    let get = [Op::LoadConst { dst: 2, index: 0 }, Op::LoadConst { dst: 3, index: 2 }, Op::TailCallRequest { base: 2, args: 2, request: Request::MarkValue }];
    let constants = [TAG, 1, 0, 100_000, -1];
    assert_eq!(call(&constants, &[(0, &[], &main), (0, &[], &get)], &[]), Ok(vec![1, 0]));

    // (with-mark key 1 (lambda () (call-with-prompt (make-prompt-tag) h (lambda () (mark-value key 0))))):
    // marks are seen through prompts.
    let main = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 6 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::WithMark },
    ];
    let inner = [
        Op::CallIntrinsic { base: 2, args: 0, intrinsic: MakePromptTag },
        Op::LoadAcc { dst: 2 },
        Op::NewClosure { dst: 3, count: 2, code: 7 },
        Op::TailCallRequest { base: 2, args: 3, request: Request::CallWithPrompt },
    ];
    let handler = [Op::LoadConst { dst: 3, index: 2 }, Op::Return { src: 3 }];
    let funcs = [(0, &[][..], &main[..]), (0, &[], &inner), (-1, &[], &handler), (0, &[], &get)];
    assert_eq!(call(&constants, &funcs, &[]), Ok(vec![1]));

    // (let loop ((n 100000)) (if (eq? 0 n) (mark-value key 0) (with-mark key n (lambda () (loop (+ n -1))))))
    // Each mark replaces the last, so it runs in a small arena.
    let main = [Op::NewClosure { dst: 2, count: 1, code: 6 }, Op::LoadConst { dst: 3, index: 3 }, Op::TailCall { base: 2, args: 1 }];
    let looping = [
        Op::LoadConst { dst: 3, index: 2 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 5 },
        Op::JumpIfFalse { test: 5, offset: 3 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::TailCallRequest { base: 3, args: 2, request: Request::MarkValue },
        Op::LoadConst { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 7 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::WithMark },
    ];
    let again = [
        Op::LoadUpvalue { dst: 2, index: 0 },
        Op::LoadUpvalue { dst: 4, index: 1 },
        Op::LoadConst { dst: 5, index: 4 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::TailCall { base: 2, args: 1 },
    ];
    let mut arena = Arena::new(1 << 20, 0);
    let machine = arena.mutate(|mc| {
        let constants = table(mc, &constants);
        let funcs = [(0, &[][..], &main[..]), (1, &[], &looping), (0, &[Capture::Register(0), Capture::Register(1)], &again)];
        Machine::new(mc, MIN_SEGMENT, closure(mc, module(mc, &constants, &funcs)[0]), &[]).unwrap()
    });
    assert_eq!(finish(&mut arena, machine).map(|(v, _)| v), Ok(vec![1]));
}

#[test]
fn deep_continuations_come_back_in_chunks() {
    // sum, but its base case is (capture tag (lambda (k) (set-box! kb k) 0)), under a prompt;
    // main then calls k once with 1000: (let ((r (prompt (sum 3000)))) (if (first time) (k 1000) r)).
    let sum = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 5 },
        Op::JumpIfFalse { test: 5, offset: 3 },
        Op::LoadConst { dst: 6, index: 6 },
        Op::NewClosure { dst: 7, count: 1, code: 10 },
        Op::TailCallRequest { base: 6, args: 2, request: Request::Capture },
        Op::LoadConst { dst: 4, index: 1 },
        Op::Move { dst: 3, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 9 },
        Op::Move { dst: 8, src: 0 },
        Op::Call { base: 8, args: 1 },
        Op::LoadAcc { dst: 4 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::Return { src: 3 },
    ];
    let keep = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: SetBox },
        Op::LoadConst { dst: 4, index: 0 },
        Op::Return { src: 4 },
    ];
    let main = [
        Op::LoadConst { dst: 2, index: 2 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: MakeBox },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 0 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: MakeBox },
        Op::LoadAcc { dst: 4 },
        Op::LoadConst { dst: 7, index: 6 },
        Op::NewClosure { dst: 8, count: 2, code: 8 },
        Op::LoadConst { dst: 10, index: 3 },
        Op::CallRequest { base: 7, args: 4, request: Request::CallWithPrompt },
        Op::LoadAcc { dst: 2 },
        Op::CallIntrinsic { base: 4, args: 1, intrinsic: Unbox },
        Op::LoadAcc { dst: 5 },
        Op::LoadConst { dst: 6, index: 4 },
        Op::CallIntrinsic { base: 5, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 6 },
        Op::Move { dst: 5, src: 4 },
        Op::CallIntrinsic { base: 5, args: 2, intrinsic: SetBox },
        Op::Move { dst: 5, src: 6 },
        Op::LoadConst { dst: 6, index: 4 },
        Op::CallIntrinsic { base: 5, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 5 },
        Op::JumpIfFalse { test: 5, offset: 4 },
        Op::CallIntrinsic { base: 3, args: 1, intrinsic: Unbox },
        Op::LoadAcc { dst: 7 },
        Op::LoadConst { dst: 8, index: 5 },
        Op::TailCall { base: 7, args: 1 },
        Op::Return { src: 2 },
    ];
    let handler = [Op::LoadConst { dst: 3, index: 0 }, Op::Return { src: 3 }];
    let mut arena = Arena::new(1 << 24, 0);
    let machine = arena.mutate(|mc| {
        let tag = Value::object(mc, Tag::new(mc, Value::VOID).unwrap());
        let constants = [fix(0), fix(-1), Value::FALSE, fix(3000), fix(1), fix(1000), tag];
        let funcs: [Func<'_>; 4] =
            [(0, &[], &main), (-1, &[], &handler), (1, &[Capture::Register(3)], &sum), (1, &[Capture::Upvalue(0)], &keep)];
        let codes = module(mc, &constants, &funcs);
        Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap()
    });
    assert_eq!(finish(&mut arena, machine).map(|(v, _)| v), Ok(vec![4_502_500]));
}

#[test]
fn call_cc_from_the_prelude() {
    // (+ 1 (call/cc (lambda (k) (+ 100 (k 5)))))
    let main = [
        Op::LoadUpvalue { dst: 4, index: CALL_CC },
        Op::NewClosure { dst: 5, count: 1, code: 4 },
        Op::Call { base: 4, args: 1 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 0 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let f = [
        Op::LoadConst { dst: 6, index: 1 },
        Op::Move { dst: 5, src: 1 },
        Op::Call { base: 5, args: 1 },
        Op::LoadAcc { dst: 4 },
        Op::LoadConst { dst: 3, index: 2 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::Return { src: 3 },
    ];
    assert_eq!(prelude_call(&[1, 5, 100], &[(0, &[], &main), (1, &[], &f)]), [6]);

    // (let ((n (box 0)) (kb (box 0)))
    //   (let ((v (call/cc (lambda (c) (set-box! kb c) 0))))
    //     (set-box! n (+ (unbox n) 1))
    //     (if (eq? (unbox n) 3) v ((unbox kb) (+ v 10)))))
    let reenter = [
        Op::LoadConst { dst: 2, index: 0 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: MakeBox },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::CallIntrinsic { base: 2, args: 1, intrinsic: MakeBox },
        Op::LoadAcc { dst: 4 },
        Op::LoadUpvalue { dst: 6, index: CALL_CC },
        Op::NewClosure { dst: 7, count: 1, code: 6 },
        Op::Call { base: 6, args: 1 },
        Op::LoadAcc { dst: 5 },
        Op::CallIntrinsic { base: 3, args: 1, intrinsic: Unbox },
        Op::LoadAcc { dst: 8 },
        Op::LoadConst { dst: 9, index: 2 },
        Op::CallIntrinsic { base: 8, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 9 },
        Op::Move { dst: 8, src: 3 },
        Op::CallIntrinsic { base: 8, args: 2, intrinsic: SetBox },
        Op::Move { dst: 8, src: 9 },
        Op::LoadConst { dst: 9, index: 3 },
        Op::CallIntrinsic { base: 8, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 8 },
        Op::JumpIfFalse { test: 8, offset: 1 },
        Op::Return { src: 5 },
        Op::Move { dst: 8, src: 5 },
        Op::LoadConst { dst: 9, index: 4 },
        Op::CallIntrinsic { base: 8, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 12 },
        Op::CallIntrinsic { base: 4, args: 1, intrinsic: Unbox },
        Op::LoadAcc { dst: 11 },
        Op::TailCall { base: 11, args: 1 },
    ];
    let keep = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: SetBox },
        Op::LoadConst { dst: 4, index: 0 },
        Op::Return { src: 4 },
    ];
    assert_eq!(prelude_call(&[0, 0, 1, 3, 10], &[(0, &[], &reenter), (1, &[Capture::Register(4)], &keep)]), [20]);
}

#[test]
fn exceptions_from_the_prelude() {
    use Capture::Upvalue;
    // (+ 1 (with-exception-handler (lambda (e) (+ e 10)) (lambda () (+ 100 (raise-continuable 5)))))
    let main = [
        Op::LoadUpvalue { dst: 4, index: WITH_HANDLER },
        Op::NewClosure { dst: 5, count: 2, code: 5 },
        Op::Call { base: 4, args: 2 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 3 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let handler = [Op::Move { dst: 3, src: 1 }, Op::LoadConst { dst: 4, index: 1 }, Op::TailCallIntrinsic { base: 3, args: 2, intrinsic: Add }];
    let thunk = [
        Op::LoadUpvalue { dst: 4, index: 0 },
        Op::LoadConst { dst: 5, index: 0 },
        Op::Call { base: 4, args: 1 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 2 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let funcs = [(0, &[][..], &main[..]), (1, &[], &handler), (0, &[Upvalue(RAISE_CONTINUABLE)], &thunk)];
    assert_eq!(prelude_call(&[5, 10, 100, 1], &funcs), [116]);

    // (with-exception-handler (lambda (e) 1000)
    //   (lambda () (+ 1 (with-exception-handler (lambda (e) (+ 1 (raise-continuable (+ e 1))))
    //                     (lambda () (+ 1 (raise-continuable 5)))))))
    // The inner handler's raise goes to the outer one.
    let main = [Op::LoadUpvalue { dst: 2, index: WITH_HANDLER }, Op::NewClosure { dst: 3, count: 2, code: 4 }, Op::TailCall { base: 2, args: 2 }];
    let outer = [Op::LoadConst { dst: 3, index: 0 }, Op::Return { src: 3 }];
    let outer_thunk = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 2, code: 6 },
        Op::Call { base: 3, args: 2 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let inner = [
        Op::Move { dst: 4, src: 1 },
        Op::LoadConst { dst: 5, index: 1 },
        Op::CallIntrinsic { base: 4, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 5 },
        Op::LoadUpvalue { dst: 4, index: 0 },
        Op::Call { base: 4, args: 1 },
        Op::LoadAcc { dst: 4 },
        Op::LoadConst { dst: 3, index: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 3 },
        Op::Return { src: 3 },
    ];
    let inner_thunk = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::Call { base: 3, args: 1 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: Add },
        Op::LoadAcc { dst: 2 },
        Op::Return { src: 2 },
    ];
    let funcs = [
        (0, &[][..], &main[..]),
        (1, &[], &outer),
        (0, &[Upvalue(WITH_HANDLER), Upvalue(RAISE_CONTINUABLE)], &outer_thunk),
        (1, &[Upvalue(1)], &inner),
        (0, &[Upvalue(1)], &inner_thunk),
    ];
    assert_eq!(prelude_call(&[1000, 1, 5], &funcs), [1003]);

    // (call/cc (lambda (k) (with-exception-handler k (lambda () (with-exception-handler (lambda (e) 0) (lambda () (raise 5)))))))
    // The inner handler returns from a raise, which is raised to k.
    let main = [Op::LoadUpvalue { dst: 2, index: CALL_CC }, Op::NewClosure { dst: 3, count: 1, code: 3 }, Op::TailCall { base: 2, args: 1 }];
    let f = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 4 },
        Op::TailCall { base: 3, args: 2 },
    ];
    let thunk = [Op::LoadUpvalue { dst: 2, index: 0 }, Op::NewClosure { dst: 3, count: 2, code: 5 }, Op::TailCall { base: 2, args: 2 }];
    let returns = [Op::LoadConst { dst: 3, index: 0 }, Op::Return { src: 3 }];
    let raise = [Op::LoadUpvalue { dst: 2, index: 0 }, Op::LoadConst { dst: 3, index: 1 }, Op::TailCall { base: 2, args: 1 }];
    let funcs = [
        (0, &[][..], &main[..]),
        (1, &[Upvalue(WITH_HANDLER), Upvalue(RAISE)], &f),
        (0, &[Upvalue(0), Upvalue(1)], &thunk),
        (1, &[], &returns),
        (0, &[Upvalue(1)], &raise),
    ];
    assert_eq!(prelude_call(&[0, 5], &funcs), [RETURNED]);

    // (call/cc (lambda (k) (with-exception-handler k (lambda () (car 5))))): VM faults go to
    // the prelude's raise.
    let f = [
        Op::LoadUpvalue { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 3 },
        Op::TailCall { base: 3, args: 2 },
    ];
    let body = [Op::LoadConst { dst: 2, index: 0 }, Op::TailCallIntrinsic { base: 2, args: 1, intrinsic: Car }];
    let main = [Op::LoadUpvalue { dst: 2, index: CALL_CC }, Op::NewClosure { dst: 3, count: 1, code: 2 }, Op::TailCall { base: 2, args: 1 }];
    prelude_outcome(&[5], &[(0, &[], &main), (1, &[Upvalue(WITH_HANDLER)], &f), (0, &[], &body)], |mc, outcome| {
        let Outcome::Done(value) = outcome else { panic!("{outcome:?}") };
        assert_eq!(fault(mc, value), Fault::WrongType);
    });

    // (raise 5) with no handler aborts to the prelude's prompt.
    let main = [Op::LoadUpvalue { dst: 2, index: RAISE }, Op::LoadConst { dst: 3, index: 0 }, Op::TailCall { base: 2, args: 1 }];
    assert_eq!(prelude_call(&[5], &[(0, &[], &main)]), [5]);
}

#[test]
fn faults_go_to_the_fault_procedure() {
    // (car 5), with no fault procedure.
    let main = [Op::LoadConst { dst: 2, index: 0 }, Op::TailCallIntrinsic { base: 2, args: 1, intrinsic: Car }];
    outcome(&[5], &[(0, &[], &main)], |mc, outcome| {
        let Outcome::Raised(value) = outcome else { panic!("{outcome:?}") };
        assert_eq!(fault(mc, value), Fault::WrongType);
    });

    // A fault procedure that isn't one ends the run with that fault.
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let constants = table(mc, &[5]);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, module(mc, &constants, &[(0, &[], &main)])[0]), &[]).unwrap();
        machine.set_fault(mc, fix(3));
        let Outcome::Raised(value) = to_end(mc, &mut machine).unwrap() else { panic!() };
        assert_eq!(fault(mc, value), Fault::NotProcedure);
    });

    // A fault in a nested frame calls the fault procedure in place of the faulting frame,
    // keeping its caller on the active segment so returning from the handler resumes the caller.
    let caller = [
        Op::NewClosure { dst: 3, count: 1, code: 4 },
        Op::Call { base: 3, args: 0 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::TailCallIntrinsic { base: 2, args: 2, intrinsic: Add },
    ];
    let handler = [Op::LoadConst { dst: 3, index: 2 }, Op::Return { src: 3 }];
    arena.mutate(|mc| {
        let constants = table(mc, &[5, 10, 32]);
        let codes = module(mc, &constants, &[(0, &[], &caller), (0, &[], &main), (1, &[], &handler)]);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap();
        machine.set_fault(mc, closure(mc, codes[2]));
        assert_eq!(to_end(mc, &mut machine).unwrap(), Outcome::Done(fix(42)));
    });
}

#[test]
fn equal_spends_fuel_as_it_goes() {
    // (let ((same (equal? v w))) (begin) same), with a jump after the comparison.
    let main = [
        Op::LoadConst { dst: 2, index: 0 },
        Op::LoadConst { dst: 3, index: 1 },
        Op::CallIntrinsic { base: 2, args: 2, intrinsic: crate::Intrinsic::Equal },
        Op::LoadAcc { dst: 4 },
        Op::Jump { offset: 0 },
        Op::Return { src: 4 },
    ];
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let vectors = Vectors::new(mc);
        let items: Vec<_> = (0..10_240).map(fix).collect();
        let vector = || vectors.from_slice(&items).unwrap().value(mc);
        let codes = module(mc, &[vector(), vector()], &[(0, &[], &main)]);
        let start = || Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap();
        // The vectors and their items are 10241 values, 10 units of fuel, and the jump one more.
        let mut machine = start();
        assert_eq!(to_end(mc, &mut machine).unwrap(), Outcome::Done(Value::TRUE));
        assert_eq!(machine.fuel(), u64::MAX - 11);

        // With less fuel than that in all, it stops partway, and the task is finished.
        let mut machine = start();
        machine.set_fuel(9);
        assert_eq!(to_end(mc, &mut machine), Err(Fault::OutOfFuel));
        assert_eq!(machine.run(mc), Err(Fault::Finished));

        // Fuel for the comparison and the jump is enough.
        let mut machine = start();
        machine.set_fuel(11);
        assert_eq!(to_end(mc, &mut machine).unwrap(), Outcome::Done(Value::TRUE));
        assert_eq!(machine.fuel(), 0);
    });
}

#[test]
fn running_out_of_fuel_finishes_the_task() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let codes = module(mc, &[fix(0), fix(-1)], &[(1, &[], SUM)]);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[fix(3000)]).unwrap();
        machine.set_fuel(2000);
        assert_eq!(to_end(mc, &mut machine), Err(Fault::OutOfFuel));
        assert_eq!(machine.fuel(), 0);
        assert_eq!(machine.run(mc), Err(Fault::Finished));
    });
}
