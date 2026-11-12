use ragwort_types::gc::{Arena, Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::vector::Vectors;

use super::*;
use crate::Intrinsic::{Add, Car, Cons, Eq, IsValues, MakeBox, MakePromptTag, MarkValue, SetBox, Unbox, Values, ValuesLength, ValuesRef};
use crate::objects::{Bytecode, BytecodeFields, Closure, ClosureFields, Condition, ConditionFields, MultiValue, MultiValueFields, Tag};
use crate::objects::{ExternalRef, ExternalRefFields, Module};
use crate::{Capture, Fault, HostArgs, HostContext, HostDef, Op, Purity, Reply, Request};

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

/// Definition of a single function within a test module, represented as `(arity, captures, bytecode_ops)`.
type Func<'a> = (i64, &'a [Capture], &'a [Op]);

/// Compiles functions that share a single constant table. The provided `constants` are placed first in the table, followed by the function closures themselves, such that function `i` is located at index `constants.len() + i`.
fn module<'gc>(mc: &Mutation<'gc>, constants: &[Value<'gc>], funcs: &[Func<'_>]) -> Vec<Gc<'gc, Bytecode>> {
    module_in(mc, None, constants, funcs)
}

/// Like [`module`], but sets up the functions within an owner module that has no module-level variables and exposes the specified host function definitions (`hosts`).
fn module_calling<'gc>(mc: &Mutation<'gc>, constants: &[Value<'gc>], hosts: &'static [HostDef], funcs: &[Func<'_>]) -> Vec<Gc<'gc, Bytecode>> {
    module_in(mc, Some(crate::module::new(mc, Value::FALSE, &[], hosts).unwrap()), constants, funcs)
}

/// Like [`module`], but attaches the resulting bytecode functions to the specified owning `Module` (if provided).
fn module_in<'gc>(mc: &Mutation<'gc>, owner: Option<Gc<'gc, Module>>, constants: &[Value<'gc>], funcs: &[Func<'_>]) -> Vec<Gc<'gc, Bytecode>> {
    let codes: Vec<_> = funcs
        .iter()
        .map(|&(arity, captures, ops)| {
            let (ops, captures) = (mc.frozen(Box::from(ops)).unwrap(), mc.frozen(Box::from(captures)).unwrap());
            Bytecode::new(mc, ops, Value::VOID, captures, arity, owner).unwrap()
        })
        .collect();
    let mut table = constants.to_vec();
    table.extend(codes.iter().map(|&c| Value::object(mc, c)));
    let table = Vectors::new(mc).immutable_from_slice(&table).unwrap().value(mc);
    codes.iter().for_each(|c| c.set_constants(mc, table));
    codes
}

/// Sentinel constant value (`i64::MIN`) that [`call`] and [`outcome`] map to a consistent, shared prompt tag object in the constant table.
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

/// Extracts the result of a completed task as a vector of `i64` fixnums, unpacking `MultiValue` instances or wrapping a single scalar return value.
fn fixnums<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Vec<i64> {
    spread(mc, value).iter().map(|v| v.as_fixnum().unwrap()).collect()
}

fn spread<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Vec<Value<'gc>> {
    let Some(values) = value.downcast::<MultiValue>(mc) else { return vec![value] };
    let items = values.items(mc);
    (0..items.len()).map(|i| items.get(i)).collect()
}

/// Retrieves the underlying [`Fault`] code from an active or raised [`Condition`] object.
fn fault<'gc>(mc: &Mutation<'gc>, raised: Value<'gc>) -> Fault {
    *raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap()
}

/// Runs `machine` to completion within a single GC step, automatically resuming execution through any intermediate [`Outcome::Paused`] states.
fn to_end<'gc>(mc: &Mutation<'gc>, machine: &mut Machine) -> Result<Outcome<'gc>, Fault> {
    loop {
        match machine.run(mc)? {
            Outcome::Paused => {}
            outcome => return Ok(outcome),
        }
    }
}

/// Executes `code` with `args` to completion in a single GC step. Fixnum returns are preserved directly, while linked lists representing digit sequences (e.g. `(1 2 3)`) are flattened into integers (e.g. `123`).
fn run<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, args: &[Value<'gc>]) -> Result<Vec<i64>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), args)?;
    let values = match to_end(mc, &mut machine)? {
        Outcome::Done(value) => spread(mc, value),
        Outcome::Raised(raised) => return Err(fault(mc, raised)),
        Outcome::Paused | Outcome::Yielded(_) | Outcome::Deferred(_) => unreachable!(),
    };
    let digits = |v: Value<'gc>| items(mc, v).iter().fold(0, |a, &n| a * 10 + n);
    Ok(values.iter().map(|&v| if Pair::of(v).is_some() { digits(v) } else { v.as_fixnum().unwrap() }).collect())
}

/// Steps the machine to completion across arena collection boundaries, allowing incremental GC between execution steps. Returns the final values as fixnums and the total number of execution steps required.
fn finish(arena: &mut Arena, mut machine: Machine) -> Result<(Vec<i64>, usize), Fault> {
    for runs in 1.. {
        let done = arena.step(|mc| -> Result<_, Fault> {
            Ok(match machine.run(mc)? {
                Outcome::Done(value) => Some(fixnums(mc, value)),
                Outcome::Raised(raised) => return Err(fault(mc, raised)),
                Outcome::Paused => None,
                Outcome::Yielded(_) | Outcome::Deferred(_) => unreachable!(),
            })
        })??;
        if let Some(values) = done {
            return Ok((values, runs));
        }
    }
    unreachable!()
}

/// Initializes an arena and runs function 0 of the module with `args` to completion in a single execution step, returning the resulting values as fixnums.
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
            Outcome::Paused | Outcome::Yielded(_) | Outcome::Deferred(_) => unreachable!(),
        }
    })
}

/// Initializes an arena, runs function 0 of the module to completion, and supplies the final [`Outcome`] to the provided `check` closure.
fn outcome(constants: &[i64], funcs: &[Func<'_>], check: impl for<'gc> FnOnce(&Mutation<'gc>, Outcome<'gc>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let constants = table(mc, constants);
        let codes = module(mc, &constants, funcs);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap();
        check(mc, to_end(mc, &mut machine).unwrap());
    });
}

/// Bytecode implementation of recursive summation: `(define (sum n) (if (eq? 0 n) 0 (+ n (sum (+ n -1)))))`, referencing constant indices for `0` and `-1`.
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
    // In a single-argument function, register 2 stores the caller's return continuation link; setting the call base to register 2 would clobber the link, so the VM rejects it with `Fault::Malformed`.
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
    // Evaluates `(let loop ((n 200000) (acc 0)) (if (eq? 0 n) acc (loop (+ n -1) (car (cons (+ acc 1) n)))))`.
    // This creates 200,000 short-lived cons pairs—exceeding arena capacity multiple times over—verifying that VM execution pauses allow garbage collection to reclaim memory.
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
    // Tests variadic rest arguments `(lambda (a . rest) (cons a rest))` and fixed-arity calls `(lambda (a b c) (+ a b c))`, followed by both non-tail and tail invocations of `(apply f x list)`.
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
    // Defines a procedure returning three values: `(define (three) (values 1 2 3))`.
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

    // Returning multiple values directly from a task succeeds and unpacks them; attempting to pass them to a single-value operation like `(+ 1 (three))` raises a type error.
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

    // Inspects multiple values as a first-class object: `(let ((v (three))) (if (values? v) (+ (values-length v) (values-ref v 0)) v))`.
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

    // Calling `(values)` with zero arguments produces an empty multiple-values object.
    let none = &[Op::TailCallIntrinsic { base: 2, args: 0, intrinsic: Values }];
    assert_eq!(call(&constants, &funcs(none), &[]), Ok(vec![]));
}

/// Upvalue indices provided to function 0 when executing under the prelude, exposing core prelude procedures and the default prompt tag.
const CALL_CC: u32 = 0;
const WITH_HANDLER: u32 = 1;
const RAISE_CONTINUABLE: u32 = 2;
const RAISE: u32 = 3;
/// Bytecode implementation of runtime prelude primitives that Ragwort delegates to native code:
/// sets up a delimited prompt with Racket's default abort handler (which re-invokes an aborted thunk under the prompt),
/// implements `call/cc` via delimited capture and abort, and wraps exception-handling requests.
/// Returns `(run, upvalues)` where `run` evaluates a thunk under the prompt.
fn prelude<'gc>(mc: &Mutation<'gc>) -> (Value<'gc>, Vec<Value<'gc>>) {
    let tag = Value::object(mc, Tag::new(mc, Value::VOID).unwrap());
    // In the prelude constant table, index 0 is reserved for the prompt tag; functions are indexed at `1 + i`.
    let default_handler = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::Move { dst: 4, src: 0 },
        Op::Move { dst: 5, src: 1 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
    ];
    let run = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 1 },
        Op::Move { dst: 5, src: 1 },
        Op::TailCallRequest { base: 3, args: 3, request: Request::CallWithPrompt },
    ];
    // Delimited control encoding of `call/cc`:
    // `(call/cc f) => (capture tag (lambda (k) (f (lambda (v) (abort tag (lambda () (k v)))))))`.
    let call_cc = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 4 },
        Op::TailCallRequest { base: 3, args: 2, request: Request::Capture },
    ];
    let receiver = [Op::NewClosure { dst: 4, count: 1, code: 5 }, Op::LoadUpvalue { dst: 3, index: 0 }, Op::TailCall { base: 3, args: 1 }];
    let escape = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::NewClosure { dst: 4, count: 1, code: 6 },
        Op::TailCallRequest { base: 3, args: 2, request: Request::Abort },
    ];
    let call_upvalue = [Op::LoadUpvalue { dst: 2, index: 0 }, Op::LoadUpvalue { dst: 3, index: 1 }, Op::TailCall { base: 2, args: 1 }];
    let with_handler = [
        Op::Move { dst: 4, src: 1 },
        Op::Move { dst: 5, src: 2 },
        Op::TailCallRequest { base: 4, args: 2, request: Request::WithHandler },
    ];
    let raising = |request| [Op::Move { dst: 3, src: 1 }, Op::TailCallRequest { base: 3, args: 1, request }];
    let (raise_continuable, raise) = (raising(Request::RaiseContinuable), raising(Request::Raise));
    use Capture::{Register, Upvalue};
    let funcs: [Func<'_>; 9] = [
        (1, &[], &default_handler),
        (1, &[], &run),
        (1, &[], &call_cc),
        (1, &[Register(1)], &receiver),
        (1, &[Register(1)], &escape),
        (0, &[Upvalue(0), Register(1)], &call_upvalue),
        (2, &[], &with_handler),
        (1, &[], &raise_continuable),
        (1, &[], &raise),
    ];
    let codes = module(mc, &[tag], &funcs);
    let close = |i: usize| closure(mc, codes[i]);
    (close(1), vec![close(2), close(6), close(7), close(8), tag])
}

/// Executes `thunk` with `handler` installed as the exception handler for raises.
fn with_raise_handler<'gc>(mc: &Mutation<'gc>, handler: Value<'gc>, thunk: Value<'gc>) -> Value<'gc> {
    let code = [
        Op::LoadConst { dst: 2, index: 0 },
        Op::LoadConst { dst: 3, index: 1 },
        Op::TailCallRequest { base: 2, args: 2, request: Request::WithHandler },
    ];
    closure(mc, module(mc, &[handler, thunk], &[(0, &[], &code)])[0])
}

/// Executes function 0 within the prelude's delimited prompt environment—supplying prelude procedures as upvalues and directing VM faults to `raise`—and passes the final [`Outcome`] to `check`.
fn prelude_outcome(constants: &[i64], funcs: &[Func<'_>], check: impl for<'gc> FnOnce(&Mutation<'gc>, Outcome<'gc>)) {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let (run, upvalues) = prelude(mc);
        let constants = table(mc, constants);
        let codes = module(mc, &constants, funcs);
        let main = Closure::new(mc, Some(codes[0]), upvalues.len(), Value::VOID).unwrap();
        upvalues.iter().enumerate().for_each(|(i, &v)| main.items(mc).set(mc, i, v));
        let mut machine = Machine::new(mc, MIN_SEGMENT, run, &[Value::object(mc, main)]).unwrap();
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
    // Tests aborting to a prompt handler with multiple arguments:
    // `(+ 1000 (call-with-prompt tag (lambda (a b) (+ a b)) (lambda () (+ 1 (abort tag 5 2)))))` evaluates to 1007.
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

    // When a thunk enclosed in a prompt returns normally without aborting, its return value passes directly through the prompt.
    assert_eq!(with(&[Op::LoadConst { dst: 2, index: 4 }, Op::Return { src: 2 }]), Ok(vec![1001]));

    // Verifies that aborting to a tag without an active prompt or aborting to a non-tag value results in an appropriate fault.
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
    // Tests invoking a captured delimited continuation `k` multiple times within the body:
    // `(+ 1000 (call-with-prompt tag h (lambda () (+ 1 (capture tag (lambda (k) (+ (k 1) (k 2))))))))`.
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
    // Invokes captured continuation `(k 10)` in tail position.
    assert_eq!(with(&[Op::Move { dst: 3, src: 1 }, Op::LoadConst { dst: 4, index: 4 }, Op::TailCall { base: 3, args: 1 }]), Ok(vec![1012]));

    // Tests escaping and resuming a delimited continuation outside the lifetime of its original prompt:
    // `(let ((kb (box 0))) (+ (call-with-prompt tag h (lambda () (+ 1 (capture tag (lambda (k) (set-box! kb k) 0))))) ((unbox kb) 10)))`.
    // Verifies that `k` resumes execution correctly in the outer caller context without an enclosing prompt.
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
    // Verifies continuation mark scoping:
    // `(values (with-mark key 1 (lambda () (mark-value key 0))) (mark-value key 0))` yields `(1 0)`, showing that the mark is present during evaluation and cleared upon return.
    let main = [
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 1 },
        Op::NewClosure { dst: 5, count: 1, code: 6 },
        Op::CallRequest { base: 3, args: 3, request: Request::WithMark },
        Op::LoadAcc { dst: 2 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: MarkValue },
        Op::LoadAcc { dst: 3 },
        Op::TailCallIntrinsic { base: 2, args: 2, intrinsic: Values },
    ];
    let get = [Op::LoadConst { dst: 2, index: 0 }, Op::LoadConst { dst: 3, index: 2 }, Op::TailCallIntrinsic { base: 2, args: 2, intrinsic: MarkValue }];
    let constants = [TAG, 1, 0, 100_000, -1];
    assert_eq!(call(&constants, &[(0, &[], &main), (0, &[], &get)], &[]), Ok(vec![1, 0]));

    // Verifies that continuation marks set outside a prompt remain visible across prompt boundaries:
    // `(with-mark key 1 (lambda () (call-with-prompt (make-prompt-tag) h (lambda () (mark-value key 0)))))` reads the outer mark value `1`.
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

    // Verifies tail-mark replacement behavior:
    // `(let loop ((n 100000)) (if (eq? 0 n) (mark-value key 0) (with-mark key n (lambda () (loop (+ n -1))))))`.
    // Each tail call replaces the current frame's continuation mark rather than allocating a new mark frame, executing in constant stack space within a small arena.
    let main = [Op::NewClosure { dst: 2, count: 1, code: 6 }, Op::LoadConst { dst: 3, index: 3 }, Op::TailCall { base: 2, args: 1 }];
    let looping = [
        Op::LoadConst { dst: 3, index: 2 },
        Op::Move { dst: 4, src: 1 },
        Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
        Op::LoadAcc { dst: 5 },
        Op::JumpIfFalse { test: 5, offset: 3 },
        Op::LoadConst { dst: 3, index: 0 },
        Op::LoadConst { dst: 4, index: 2 },
        Op::TailCallIntrinsic { base: 3, args: 2, intrinsic: MarkValue },
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
    // Recursively evaluates `sum` down 3,000 stack frames and captures the entire multi-chunk continuation `k` at the base case.
    // The driver routine then resumes `(k 1000)`, verifying that continuations spanning multiple stack chunks are captured and restored correctly.
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
    // Standard `call/cc` test verifying that calling continuation `(k 5)` aborts the intervening computation `(+ 100 ...)`:
    // `(+ 1 (call/cc (lambda (k) (+ 100 (k 5)))))` evaluates to 6.
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

    // Tests re-entering a `call/cc` continuation multiple times:
    // `(let ((n (box 0)) (kb (box 0))) (let ((v (call/cc (lambda (c) (set-box! kb c) 0)))) (set-box! n (+ (unbox n) 1)) (if (eq? (unbox n) 3) v ((unbox kb) (+ v 10)))))`.
    // Re-invokes `kb` until the mutation counter `n` reaches 3, accumulating the result.
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
    // Tests continuable exception handling:
    // `(+ 1 (with-exception-handler (lambda (e) (+ e 10)) (lambda () (+ 100 (raise-continuable 5)))))` returns 116, resuming the thunk after the handler returns.
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

    // Tests cascading exception handling across nested handlers:
    // `(with-exception-handler (lambda (e) 1000) (lambda () (+ 1 (with-exception-handler (lambda (e) (+ 1 (raise-continuable (+ e 1)))) (lambda () (+ 1 (raise-continuable 5)))))))`.
    // Verifies that a `raise-continuable` issued within an active exception handler is intercepted by the enclosing outer handler.
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

    // Tests returning from a non-continuable exception handler:
    // `(call/cc (lambda (k) (with-exception-handler k (lambda () (with-exception-handler (lambda (e) 0) (lambda () (raise 5)))))))`.
    // Because returning from a non-continuable `raise` is prohibited, the VM raises a secondary error condition, which is captured by outer handler `k`.
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
    prelude_outcome(&[0, 5], &funcs, |mc, outcome| {
        let Outcome::Done(value) = outcome else { panic!("{outcome:?}") };
        assert_eq!(fault(mc, value), Fault::Error);
    });

    // Verifies that internal VM faults (such as executing `(car 5)` on a non-pair) are promoted into condition objects and dispatched to the installed exception handler.
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

    // Executing `(raise 5)` with no active exception handler terminates the run and returns `Outcome::Raised(5)`.
    let main = [Op::LoadUpvalue { dst: 2, index: RAISE }, Op::LoadConst { dst: 3, index: 0 }, Op::TailCall { base: 2, args: 1 }];
    prelude_outcome(&[5], &[(0, &[], &main)], |_, outcome| assert_eq!(outcome, Outcome::Raised(fix(5))));
}

#[test]
fn faults_go_to_the_raise_handler() {
    // Triggering a fault via `(car 5)` without an installed exception handler terminates execution, yielding `Outcome::Raised` containing a `Fault::WrongType` condition.
    let main = [Op::LoadConst { dst: 2, index: 0 }, Op::TailCallIntrinsic { base: 2, args: 1, intrinsic: Car }];
    outcome(&[5], &[(0, &[], &main)], |mc, outcome| {
        let Outcome::Raised(value) = outcome else { panic!("{outcome:?}") };
        assert_eq!(fault(mc, value), Fault::WrongType);
    });

    // Attempting to invoke an exception handler that is not a procedure causes the task to fault with `Fault::NotProcedure`.
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let constants = table(mc, &[5]);
        let thunk = with_raise_handler(mc, fix(3), closure(mc, module(mc, &constants, &[(0, &[], &main)])[0]));
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let Outcome::Raised(value) = to_end(mc, &mut machine).unwrap() else { panic!() };
        assert_eq!(fault(mc, value), Fault::NotProcedure);
    });

    // When a fault occurs within a nested call frame, the exception handler replaces the faulting frame on the stack.
    // Because VM faults cannot be resumed, if the handler returns normally, the VM raises a secondary error condition containing the original fault.
    let caller = [
        Op::NewClosure { dst: 3, count: 1, code: 4 },
        Op::Call { base: 3, args: 0 },
        Op::LoadAcc { dst: 3 },
        Op::LoadConst { dst: 2, index: 1 },
        Op::TailCallIntrinsic { base: 2, args: 2, intrinsic: Add },
    ];
    let handler = [Op::LoadConst { dst: 4, index: 2 }, Op::Return { src: 4 }];
    arena.mutate(|mc| {
        let constants = table(mc, &[5, 10, 32]);
        let codes = module(mc, &constants, &[(0, &[], &caller), (0, &[], &main), (1, &[], &handler)]);
        let thunk = with_raise_handler(mc, closure(mc, codes[2]), closure(mc, codes[0]));
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let Outcome::Raised(value) = to_end(mc, &mut machine).unwrap() else { panic!() };
        assert_eq!(fault(mc, value), Fault::Error);
        let irritants = value.downcast::<Condition>(mc).unwrap().irritants(mc);
        assert_eq!(fault(mc, Pair::of(irritants).unwrap().head(mc)), Fault::WrongType);
    });
}

#[test]
fn equal_spends_fuel_as_it_goes() {
    // Structural equality comparison followed by an unconditional jump instruction:
    // `(let ((same (equal? v w))) (begin) same)`.
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
        // The compared vector structures contain 10,241 total elements, which consumes 10 fuel units (1 unit per 1,024 elements), plus 1 fuel unit for the jump instruction (11 fuel units total).
        let mut machine = start();
        assert_eq!(to_end(mc, &mut machine).unwrap(), Outcome::Done(Value::TRUE));
        assert_eq!(machine.fuel(), u64::MAX - 11);

        // With less than 11 fuel units allocated (e.g. 9), comparison halts mid-execution with `Fault::OutOfFuel`, transitioning the task to finished so further runs return `Fault::Finished`.
        let mut machine = start();
        machine.set_fuel(9);
        assert_eq!(to_end(mc, &mut machine), Err(Fault::OutOfFuel));
        assert_eq!(machine.run(mc), Err(Fault::Finished));

        // Providing exactly 11 fuel units supplies the exact amount required for the full comparison and the subsequent jump instruction to complete successfully.
        let mut machine = start();
        machine.set_fuel(11);
        assert_eq!(to_end(mc, &mut machine).unwrap(), Outcome::Done(Value::TRUE));
        assert_eq!(machine.fuel(), 0);
    });
}

#[test]
fn a_branch_whose_test_ends_the_step_runs_it_once() {
    // Evaluates `(if (make-vector 50000 0) 50000 0)`.
    // Allocating the 50,000-element vector exhausts available arena memory, causing the execution step to pause at the branch instruction;
    // resuming execution steps past the branch without re-executing the condition allocation.
    let main = [
        Op::LoadConst { dst: 2, index: 0 },
        Op::LoadConst { dst: 3, index: 1 },
        Op::BranchIntrinsic2 { a: 2, b: 3, intrinsic: crate::Intrinsic::MakeVector, branch_if: true, offset: 1 },
        Op::Return { src: 3 },
        Op::Return { src: 2 },
    ];
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let codes = module(mc, &[fix(50_000), fix(0)], &[(0, &[], &main)]);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[0]), &[]).unwrap();
        assert_eq!(machine.run(mc), Ok(Outcome::Paused));
        assert_eq!(machine.run(mc), Ok(Outcome::Done(fix(50_000))));
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

#[test]
fn module_variables_are_checked_until_defined() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let instance = crate::module::new(mc, Value::FALSE, &[fix(0), fix(1)], &[]).unwrap();
        let constants = [Value::VOID, fix(5), fix(6)];
        let funcs: [Func<'_>; 6] = [
            (0, &[], &[Op::LoadSlotChecked { dst: 2, slot: 0 }, Op::Return { src: 2 }]),
            (0, &[], &[Op::LoadConst { dst: 2, index: 1 }, Op::StoreSlotChecked { src: 2, slot: 0 }, Op::Return { src: 2 }]),
            (
                0,
                &[],
                &[
                    Op::LoadConst { dst: 2, index: 1 },
                    Op::StoreSlot { src: 2, slot: 1 },
                    Op::LoadSlot { dst: 3, slot: 1 },
                    Op::LoadConst { dst: 2, index: 2 },
                    Op::StoreSlotChecked { src: 2, slot: 1 },
                    Op::LoadSlotChecked { dst: 4, slot: 1 },
                    Op::TailCallIntrinsic { base: 3, args: 2, intrinsic: Values },
                ],
            ),
            (0, &[], &[Op::LoadSlot { dst: 2, slot: 2 }, Op::Return { src: 2 }]),
            (0, &[], &[Op::StoreSlot { src: 1, slot: 2 }, Op::Return { src: 1 }]),
            (0, &[], &[Op::LoadSlotChecked { dst: 2, slot: 0 }, Op::Return { src: 2 }]),
        ];
        let mut codes = module_in(mc, Some(instance), &constants, &funcs);
        // Bytecode executed outside any module scope contains no module-level variable definitions.
        codes[5] = module(mc, &constants, &funcs[5..])[0];
        assert_eq!(run(mc, codes[0], &[]), Err(Fault::Unbound));
        assert_eq!(run(mc, codes[1], &[]), Err(Fault::Unbound));
        assert_eq!(run(mc, codes[2], &[]), Ok(vec![5, 6]));
        let slots = crate::objects::ModuleFields::items(instance, mc);
        assert_eq!((slots.get(0), slots.get(1)), (Value::UNDEFINED, fix(6)));
        for code in &codes[3..] {
            assert_eq!(run(mc, *code, &[]), Err(Fault::Malformed));
        }
    });
}


/// Host function implementing variadic addition `(add n ...)`, consuming 1 unit of execution fuel per argument.
fn add_host<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    cx.charge(args.len() as u64)?;
    let sum = args.iter().map(|v| v.as_fixnum().ok_or(Fault::WrongType)).sum::<Result<i64, _>>()?;
    Ok(Reply::Value(fix(sum)))
}

/// Host function implementing `(call-with f x)`: tail-invokes procedure `f` with argument `x`.
fn call_with<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Call(args.get(0).unwrap(), Pairs::new(cx.mc()).list(&[args.get(1).unwrap()])?))
}

fn raise_host<'s, 'gc>(_: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Raise(args.get(0).unwrap()))
}

/// Host function that defers execution, returning its fixnum argument packaged inside [`Outcome::Deferred`].
fn defer_host<'s, 'gc>(_: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Defer(Box::new(args.get(0).unwrap().as_fixnum())))
}

/// Host function implementing `(burn n)`, consuming `n` units of execution fuel.
fn burn<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    cx.charge(args.get(0).unwrap().as_fixnum().unwrap() as u64)?;
    Ok(Reply::Value(Value::VOID))
}

static HOSTS: [HostDef; 5] = [
    crate::host!("add", -1, Purity::Pure, add_host),
    crate::host!("call-with", 2, Purity::Impure, call_with),
    crate::host!("raise", 1, Purity::Impure, raise_host),
    crate::host!("defer", 1, Purity::Impure, defer_host),
    crate::host!("burn", 1, Purity::Impure, burn),
];
const DEFER: u32 = 3;

#[test]
fn host_functions_are_the_same_when_their_functions_are() {
    assert_eq!(HOSTS[0], crate::host!("add", -1, Purity::Pure, add_host));
    assert_ne!(HOSTS[0], crate::host!("add", -1, Purity::Pure, burn));
    assert_ne!(HOSTS[0], crate::host!("add", -1, Purity::Impure, add_host));
}
const BURN: u32 = 4;

#[test]
fn host_functions_run_where_theyre_called() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let constants = [fix(10), fix(20), fix(1)];
        let inc = 3 + 7;
        let funcs: [Func<'_>; 9] = [
            // Tests host addition calls with multiple, single, and zero arguments: `(+ 1 (add 10 20))`, `(add 10)`, and `(add)`.
            (
                0,
                &[],
                &[
                    Op::LoadConst { dst: 2, index: 0 },
                    Op::LoadConst { dst: 3, index: 1 },
                    Op::CallHost { base: 2, args: 2, host: 0 },
                    Op::LoadAcc { dst: 4 },
                    Op::AddImm { dst: 4, a: 4, imm: 1 },
                    Op::Return { src: 4 },
                ],
            ),
            (0, &[], &[Op::LoadConst { dst: 2, index: 0 }, Op::TailCallHost { base: 2, args: 1, host: 0 }]),
            (0, &[], &[Op::TailCallHost { base: 2, args: 0, host: 0 }]),
            // Tests calling `(call-with 10)` with insufficient arguments, expecting a malformed call fault.
            (0, &[], &[Op::LoadConst { dst: 2, index: 0 }, Op::TailCallHost { base: 2, args: 1, host: 1 }]),
            // Tests `(call-with inc 10)` in non-tail position (`(+ 100 ...)`) and in tail position.
            (
                0,
                &[],
                &[
                    Op::NewClosure { dst: 2, count: 1, code: inc },
                    Op::LoadConst { dst: 3, index: 0 },
                    Op::CallHost { base: 2, args: 2, host: 1 },
                    Op::LoadAcc { dst: 4 },
                    Op::AddImm { dst: 4, a: 4, imm: 100 },
                    Op::Return { src: 4 },
                ],
            ),
            (0, &[], &[Op::NewClosure { dst: 2, count: 1, code: inc }, Op::LoadConst { dst: 3, index: 0 }, Op::TailCallHost { base: 2, args: 2, host: 1 }]),
            // Invokes host function `raise_host` with argument 1: `(raise 1)`.
            (0, &[], &[Op::LoadConst { dst: 2, index: 2 }, Op::CallHost { base: 2, args: 1, host: 2 }, Op::Return { src: 2 }]),
            // Bytecode closure incrementing its argument: `(lambda (x) (+ x 1))`.
            (1, &[], &[Op::AddImm { dst: 1, a: 1, imm: 1 }, Op::Return { src: 1 }]),
            // Invokes a host function index that is out of bounds for the current module, expecting a fault.
            (0, &[], &[Op::TailCallHost { base: 2, args: 0, host: 5 }]),
        ];
        let codes = module_calling(mc, &constants, &HOSTS, &funcs);
        assert_eq!(run(mc, codes[0], &[]), Ok(vec![31]));
        assert_eq!(run(mc, codes[1], &[]), Ok(vec![10]));
        assert_eq!(run(mc, codes[2], &[]), Ok(vec![0]));
        assert_eq!(run(mc, codes[3], &[]), Err(Fault::Arity));
        assert_eq!(run(mc, codes[4], &[]), Ok(vec![111]));
        assert_eq!(run(mc, codes[5], &[]), Ok(vec![11]));
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, codes[6]), &[]).unwrap();
        assert_eq!(to_end(mc, &mut machine), Ok(Outcome::Raised(fix(1))));
        assert_eq!(run(mc, codes[8], &[]), Err(Fault::Malformed));
    });
}

#[test]
fn deferred_host_calls_wait_for_the_host() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        // Tests calling a host function that defers execution: `(+ 1 (defer 10))`.
        let code: &[Op] = &[
            Op::LoadConst { dst: 2, index: 0 },
            Op::CallHost { base: 2, args: 1, host: DEFER },
            Op::LoadAcc { dst: 3 },
            Op::AddImm { dst: 3, a: 3, imm: 1 },
            Op::Return { src: 3 },
        ];
        let code = module_calling(mc, &[fix(10)], &HOSTS, &[(0, &[], code)])[0];
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), &[]).unwrap();
        let Ok(Outcome::Deferred(deferred)) = to_end(mc, &mut machine) else { panic!("not deferred") };
        assert_eq!(deferred.into_inner().downcast::<Option<i64>>().ok().map(|b| *b), Some(Some(10)));
        // Resuming execution without supplying a return value for the deferred host call defaults to replying with void, triggering a type fault upon addition.
        let Ok(Outcome::Raised(raised)) = machine.run(mc) else { panic!("not raised") };
        assert_eq!(fault(mc, raised), Fault::WrongType);
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), &[]).unwrap();
        assert!(matches!(to_end(mc, &mut machine), Ok(Outcome::Deferred(_))));
        assert_eq!(machine.reply(mc, fix(41)), Ok(Outcome::Done(fix(42))));
        assert_eq!(machine.raise(mc, fix(1)).err(), Some(Fault::Finished));
        let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), &[]).unwrap();
        assert!(matches!(to_end(mc, &mut machine), Ok(Outcome::Deferred(_))));
        assert_eq!(machine.raise(mc, fix(7)), Ok(Outcome::Raised(fix(7))));
    });
}

#[test]
fn host_functions_spend_the_machines_fuel() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let call = |index| [Op::LoadConst { dst: 2, index }, Op::TailCallHost { base: 2, args: 1, host: BURN }];
        let (fifty, five_hundred) = (call(0), call(1));
        let codes = module_calling(mc, &[fix(50), fix(500)], &HOSTS, &[(0, &[], &fifty), (0, &[], &five_hundred)]);
        for (code, left) in [(codes[0], Some(50)), (codes[1], None)] {
            let mut machine = Machine::new(mc, MIN_SEGMENT, closure(mc, code), &[]).unwrap();
            machine.set_fuel(101);
            let outcome = to_end(mc, &mut machine);
            match left {
                Some(left) => assert_eq!((outcome, machine.fuel()), (Ok(Outcome::Done(Value::VOID)), left)),
                None => assert_eq!(outcome, Err(Fault::OutOfFuel)),
            }
        }
    });
}

#[test]
fn external_refs_hold_the_hosts_data_and_trace_their_value() {
    struct Dropped(std::rc::Rc<std::cell::Cell<bool>>);
    impl Drop for Dropped {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    type State = (Dropped, std::cell::Cell<i64>);
    fn count<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
        let (_, n) = crate::module::external_data::<State>(cx.mc(), args.get(0).unwrap()).ok_or(Fault::WrongType)?;
        n.set(n.get() + 1);
        Ok(Reply::Value(fix(n.get())))
    }
    static COUNT: [HostDef; 1] = [crate::host!("count", 1, Purity::Impure, count)];
    let dropped = std::rc::Rc::new(std::cell::Cell::new(false));
    let mut arena = Arena::new(1 << 24, 1);
    arena.mutate(|mc| {
        let state: State = (Dropped(dropped.clone()), std::cell::Cell::new(0));
        let external = crate::module::external(mc, state, 0, list(mc, &[1, 2])).unwrap();
        mc.set_root(0, Value::object(mc, external));
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let external = mc.root(0);
        let call = |index| [Op::LoadConst { dst: 2, index }, Op::TailCallHost { base: 2, args: 1, host: 0 }];
        let (counted, wrong) = (call(0), call(1));
        let codes = module_calling(mc, &[external, fix(3)], &COUNT, &[(0, &[], &counted), (0, &[], &wrong)]);
        assert_eq!((run(mc, codes[0], &[]), run(mc, codes[0], &[])), (Ok(vec![1]), Ok(vec![2])));
        assert_eq!(run(mc, codes[1], &[]), Err(Fault::WrongType));
        assert_eq!(items(mc, external.downcast::<ExternalRef>(mc).unwrap().held(mc)), [1, 2]);
        assert!(crate::module::external_data::<i64>(mc, external).is_none());
        mc.set_root(0, Value::NIL);
    });
    assert!(!dropped.get());
    arena.collect();
    arena.collect();
    assert!(dropped.get());
}

#[test]
fn what_the_host_raises_goes_to_the_raise_handler() {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let call = |host| [Op::LoadConst { dst: 2, index: 0 }, Op::CallHost { base: 2, args: 1, host }, Op::Return { src: 2 }];
        let (raising, deferring) = (call(2), call(DEFER));
        let handler = [Op::Return { src: 1 }];
        let codes = module_calling(mc, &[fix(1)], &HOSTS, &[(0, &[], &raising), (0, &[], &deferring), (1, &[], &handler)]);
        // Because host raises are non-continuable, an exception handler returning normally raises a secondary error condition containing the originally raised value.
        for (code, raised) in [(codes[0], fix(1)), (codes[1], fix(7))] {
            let thunk = with_raise_handler(mc, closure(mc, codes[2]), closure(mc, code));
            let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
            let mut outcome = to_end(mc, &mut machine).unwrap();
            if let Outcome::Deferred(_) = outcome {
                outcome = machine.raise(mc, raised).unwrap();
            }
            let Outcome::Raised(value) = outcome else { panic!("{outcome:?}") };
            assert_eq!(fault(mc, value), Fault::Error);
            let irritants = value.downcast::<Condition>(mc).unwrap().irritants(mc);
            assert_eq!(Pair::of(irritants).unwrap().head(mc), raised);
        }
    });
}
