//! Times the run loop: a tail-recursive countdown (calls and jumps in one frame), a deep
//! non-tail sum (frames, segment overflow and underflow), and a countdown that calls a closure
//! each time round, against one calling a host function, and one deferring to the host, which
//! replies at once.

use std::hint::black_box;
use std::time::Instant;

use ragwort_types::gc::{Arena, Value};
use ragwort_types::vector::Vectors;
use ragwort_vm::Intrinsic::{Add, Eq};
use ragwort_vm::objects::{Bytecode, Closure};
use ragwort_vm::{Fault, HostArgs, HostContext, HostDef, Machine, Op, Outcome, Purity, Reply, SEGMENT, module};

/// `(define (count n) (if (eq? 0 n) 0 (count (+ n -1))))`
const COUNT: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::LoadAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::LoadAcc { dst: 7 },
    Op::Move { dst: 6, src: 0 },
    Op::TailCall { base: 6, args: 1 },
];

/// `(define (sum n) (if (eq? 0 n) 0 (+ n (sum (+ n -1)))))`
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

/// `(define (count n) (if (eq? 0 n) 0 (begin (f n) (count (+ n -1)))))`, with `f` constant 2.
const CALLS: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::LoadAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::LoadConst { dst: 6, index: 2 },
    Op::Move { dst: 7, src: 1 },
    Op::Call { base: 6, args: 1 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::LoadAcc { dst: 7 },
    Op::Move { dst: 6, src: 0 },
    Op::TailCall { base: 6, args: 1 },
];

/// [`CALLS`], with `f` a host function.
const HOST_CALLS: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::LoadAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::Move { dst: 6, src: 1 },
    Op::CallHost { base: 6, args: 1, host: 0 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::LoadAcc { dst: 7 },
    Op::Move { dst: 6, src: 0 },
    Op::TailCall { base: 6, args: 1 },
];

/// `(lambda (x) x)`
const IDENTITY: &[Op] = &[Op::Return { src: 1 }];

fn identity<'s, 'gc>(_: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Value(args.get(0).ok_or(Fault::Arity)?))
}

fn defer<'s, 'gc>(_: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Defer(Box::new(())))
}

static IDENTITY_HOST: [HostDef; 1] = [HostDef { name: "identity", arity: 1, purity: Purity::Impure, function: identity }];
static DEFER_HOST: [HostDef; 1] = [HostDef { name: "defer", arity: 1, purity: Purity::Impure, function: defer }];

/// What [`CALLS`] or [`HOST_CALLS`] calls.
#[derive(Clone, Copy)]
enum Callee {
    None,
    Closure,
    Host(&'static [HostDef]),
}

/// Best time per call of `ops` with `n`, over a few runs, replying to each deferred call with
/// void.
fn time(name: &str, ops: &'static [Op], callee: Callee, n: i64, runs: usize) {
    let mut arena = Arena::new(1 << 28, 0);
    let mut best = f64::MAX;
    for _ in 0..runs {
        arena.collect();
        let mut machine = arena.mutate(|mc| {
            let fix = |n| Value::fixnum(n).expect("fixnum");
            let empty = Vectors::new(mc).immutable_from_slice(&[]).expect("alloc").value(mc);
            let hosts = match callee {
                Callee::Host(hosts) => hosts,
                _ => &[],
            };
            let owner = Some(module::new(mc, Value::FALSE, &[], hosts).expect("alloc"));
            let closure = |ops: &'static [Op], constants| {
                let captures = mc.frozen(Box::from([])).expect("alloc");
                let code = Bytecode::new(mc, mc.frozen(Box::from(ops)).expect("alloc"), constants, captures, 1, owner).expect("alloc");
                Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID).expect("alloc"))
            };
            let f = match callee {
                Callee::None => Value::VOID,
                Callee::Closure => closure(IDENTITY, empty),
                Callee::Host(_) => Value::VOID,
            };
            let constants = Vectors::new(mc).immutable_from_slice(&[fix(0), fix(-1), f]).expect("alloc");
            Machine::new(mc, SEGMENT, closure(ops, constants.value(mc)), &[fix(n)]).expect("start")
        });
        let start = Instant::now();
        while !arena
            .step(|mc| {
                let mut outcome = machine.run(mc).expect("run");
                loop {
                    match black_box(outcome) {
                        Outcome::Deferred(_) => outcome = machine.reply(mc, Value::VOID).expect("reply"),
                        Outcome::Done(_) => return true,
                        _ => return false,
                    }
                }
            })
            .expect("room")
        {}
        let ns = start.elapsed().as_nanos() as f64 / n as f64;
        best = best.min(ns);
    }
    println!("{name:<36} {best:>8.2} ns/call");
}

fn main() {
    time("tail-recursive countdown (1e7)", COUNT, Callee::None, 10_000_000, 5);
    time("non-tail sum, 1e6 deep", SUM, Callee::None, 1_000_000, 5);
    time("non-tail sum, 1e3 deep", SUM, Callee::None, 1_000, 2000);
    time("countdown calling a closure", CALLS, Callee::Closure, 1_000_000, 5);
    time("countdown calling the host in the loop", HOST_CALLS, Callee::Host(&IDENTITY_HOST), 1_000_000, 5);
    time("countdown deferring to the host", HOST_CALLS, Callee::Host(&DEFER_HOST), 1_000_000, 5);
}
