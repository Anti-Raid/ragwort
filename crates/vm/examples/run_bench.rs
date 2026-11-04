//! Times the run loop: a tail-recursive countdown (calls and jumps in one frame), and a deep
//! non-tail sum (frames, segment overflow and underflow).

use std::hint::black_box;
use std::time::Instant;

use ragwort_types::gc::{Arena, Value};
use ragwort_types::vector::Vectors;
use ragwort_vm::Intrinsic::{Add, Eq};
use ragwort_vm::objects::{Bytecode, Closure};
use ragwort_vm::{Machine, Op, Outcome, SEGMENT};

/// `(define (count n) (if (eq? 0 n) 0 (count (+ n -1))))`
const COUNT: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::MoveAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::MoveAcc { dst: 7 },
    Op::Move { dst: 6, src: 0 },
    Op::TailCall { base: 6, args: 1 },
];

/// `(define (sum n) (if (eq? 0 n) 0 (+ n (sum (+ n -1)))))`
const SUM: &[Op] = &[
    Op::LoadConst { dst: 3, index: 0 },
    Op::Move { dst: 4, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Eq },
    Op::MoveAcc { dst: 5 },
    Op::JumpIfFalse { test: 5, offset: 1 },
    Op::Return { src: 3 },
    Op::LoadConst { dst: 4, index: 1 },
    Op::Move { dst: 3, src: 1 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::MoveAcc { dst: 9 },
    Op::Move { dst: 8, src: 0 },
    Op::Call { base: 8, args: 1 },
    Op::MoveAcc { dst: 4 },
    Op::CallIntrinsic { base: 3, args: 2, intrinsic: Add },
    Op::MoveAcc { dst: 3 },
    Op::Return { src: 3 },
];

/// Best time per call of `ops` with `n`, over a few runs.
fn time(name: &str, ops: &'static [Op], n: i64, runs: usize) {
    let mut arena = Arena::new(1 << 28, 0);
    let mut best = f64::MAX;
    for _ in 0..runs {
        arena.collect();
        let mut machine = arena.mutate(|mc| {
            let fix = |n| Value::fixnum(n).expect("fixnum");
            let constants = Vectors::new(mc).immutable_from_slice(&[fix(0), fix(-1)]).expect("alloc");
            let captures = mc.frozen(Box::from([])).expect("alloc");
            let ops = mc.frozen(Box::from(ops)).expect("alloc");
            let code = Bytecode::new(mc, ops, constants.value(mc), captures, 1).expect("alloc");
            let f = Value::object(mc, Closure::new(mc, Some(code), 0, Value::VOID).expect("alloc"));
            Machine::new(mc, SEGMENT, f, &[fix(n)]).expect("start")
        });
        let start = Instant::now();
        while !arena.step(|mc| matches!(black_box(machine.run(mc).expect("run")), Outcome::Done(_))).expect("room") {}
        let ns = start.elapsed().as_nanos() as f64 / n as f64;
        best = best.min(ns);
    }
    println!("{name:<32} {best:>8.2} ns/call");
}

fn main() {
    time("tail-recursive countdown (1e7)", COUNT, 10_000_000, 5);
    time("non-tail sum, 1e6 deep", SUM, 1_000_000, 5);
    time("non-tail sum, 1e3 deep", SUM, 1_000, 2000);
}
