//! Times loading base code, expanding and compiling it, and running a countdown that calls the
//! prelude's `eqv?` and `+` against one in native ragwort that calls the intrinsics.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_base::{load, prelude};
use ragwort_native::Globals;
use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::{MIN_SEGMENT, Machine, Outcome};

const N: i64 = 10_000_000;

/// Some of everything the expander does, each form different by its number.
fn source(forms: usize) -> String {
    (0..forms)
        .map(|i| {
            format!(
                "(define (f{i} xs n)
                   (let loop ((xs xs) (acc '()))
                     (cond ((null? xs) (reverse acc))
                           ((and (pair? xs) (or (eqv? (car xs) n) (eqv? (car xs) {i})))
                            (loop (cdr xs) (cons `(hit ,(car xs) ,@acc) acc)))
                           (else (let* ((x (car xs)) (y (+ x 1))) (loop (cdr xs) (cons y acc)))))))\n"
            )
        })
        .collect()
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Value<'gc> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).expect("machine");
    loop {
        match machine.run(mc).expect("run") {
            Outcome::Paused => {}
            Outcome::Yielded(_) => panic!("yielded"),
            Outcome::Done(value) => return value,
            Outcome::Raised(_) => panic!("raised"),
        }
    }
}

/// An arena with the symbol table in root 0, the code's globals in 1 and the prelude's in 2.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 28, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).expect("table");
        let base = Globals::new(mc).expect("globals");
        mc.set_root(0, symbols.value(mc));
        mc.set_root(1, Globals::new(mc).expect("globals").value(mc));
        mc.set_root(2, base.value(mc));
        for thunk in prelude(mc, symbols, base).expect("prelude") {
            run(mc, thunk);
        }
    });
    arena
}

/// Best time over a few runs of loading `text`, or if `run_all`, of running what it loads, all
/// but the last form before timing, then the last.
fn time(text: &str, native: bool, run_all: bool) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..5 {
        let mut arena = arena();
        arena.collect();
        let (loaded, mut machine) = arena.mutate(|mc| {
            let symbols = Symbols::of(mc.root(0)).expect("table");
            let (globals, base) = (Globals::of(mc, mc.root(1)).expect("globals"), Globals::of(mc, mc.root(2)).expect("globals"));
            let session = SyntaxSession::new(mc, text).expect("session");
            let start = Instant::now();
            let mut thunks = match native {
                true => ragwort_native::load(mc, symbols, globals, &session).expect("load"),
                false => load(mc, symbols, globals, base, &session).expect("load"),
            };
            let loaded = start.elapsed();
            let last = thunks.pop().expect("a form");
            for thunk in thunks {
                run(mc, thunk);
            }
            (loaded, Machine::new(mc, MIN_SEGMENT, last, &[]).expect("machine"))
        });
        if !run_all {
            best = best.min(loaded);
            continue;
        }
        let start = Instant::now();
        while !arena.step(|mc| matches!(black_box(machine.run(mc).expect("run")), Outcome::Done(_))).expect("room") {}
        best = best.min(start.elapsed());
    }
    best
}

fn main() {
    let forms = 2000;
    let text = source(forms);
    let took = time(&text, false, false);
    let ms = took.as_secs_f64() * 1e3;
    println!("load {forms} forms, {} KiB: {ms:.2} ms, {:.1} us per form", text.len() >> 10, ms * 1e3 / forms as f64);

    let base = format!("(define (count n) (if (eqv? n 0) 0 (count (+ n -1)))) (count {N})");
    let native = format!(
        "(%define-global count (%lambda (n) (%if (%intrinsic eqv? n 0) 0 (%app count (%intrinsic + n -1))))) (%app count {N})"
    );
    let per = |d: Duration| d.as_secs_f64() * 1e9 / N as f64;
    println!("countdown through the prelude: {:.1} ns per iteration", per(time(&base, false, true)));
    println!("countdown on intrinsics:       {:.1} ns per iteration", per(time(&native, true, true)));

    let switch = format!(
        "(define co (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
         (define (drain n) (if (eqv? n 0) 0 (begin (co/resume co) (drain (+ n -1))))) (drain {N})"
    );
    println!("coroutine resume and yield:    {:.1} ns per round trip", per(time(&switch, false, true)));
    let spawn = format!("(define (spawn n) (if (eqv? n 0) 0 (begin (co/resume (make-coroutine (lambda () n))) (spawn (+ n -1))))) (spawn {})", N / 100);
    println!("make and finish a coroutine:   {:.1} ns each", per(time(&spawn, false, true)) * 100.0);
}
