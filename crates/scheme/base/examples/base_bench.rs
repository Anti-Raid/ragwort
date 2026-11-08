//! Times loading base code, expanding and compiling it, and running a countdown that calls the
//! prelude's `eqv?` and `+` against one in native ragwort that calls the intrinsics.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_compiler::module::NoModules;
use ragwort_scheme::{PRELUDE, PRELUDE_NAME, load};
use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::Module;
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

/// Forms that use `cond`, `and`, `or` and `let*`, those of `syntax-rules` macros if `macros`.
/// `forms` definitions using `cond`, `and`, `or` and `let*`: the built-in ones if `macros` is
/// "", or else copies written with `syntax-rules`, if it's "rules", or `syntax-case`.
fn macro_source(forms: usize, macros: &str) -> String {
    let rules = "(define-syntax my-or (syntax-rules () ((_) #f) ((_ e) e) ((_ e r ...) (let ((t e)) (if t t (my-or r ...))))))
                (define-syntax my-and (syntax-rules () ((_) #t) ((_ e) e) ((_ e r ...) (if e (my-and r ...) #f))))
                (define-syntax my-let* (syntax-rules ()
                  ((_ () body ...) (let () body ...))
                  ((_ ((x v) rest ...) body ...) (let ((x v)) (my-let* (rest ...) body ...)))))
                (define-syntax my-cond (syntax-rules (else)
                  ((_ (else e ...)) (begin e ...))
                  ((_ (c e ...) clause ...) (if c (begin e ...) (my-cond clause ...)))))\n";
    let cases = "(define-syntax my-or (lambda (stx) (syntax-case stx () ((_) #'#f) ((_ e) #'e) ((_ e r ...) #'(let ((t e)) (if t t (my-or r ...)))))))
                (define-syntax my-and (lambda (stx) (syntax-case stx () ((_) #'#t) ((_ e) #'e) ((_ e r ...) #'(if e (my-and r ...) #f)))))
                (define-syntax my-let* (lambda (stx) (syntax-case stx ()
                  ((_ () body ...) #'(let () body ...))
                  ((_ ((x v) rest ...) body ...) #'(let ((x v)) (my-let* (rest ...) body ...))))))
                (define-syntax my-cond (lambda (stx) (syntax-case stx (else)
                  ((_ (else e ...)) #'(begin e ...))
                  ((_ (c e ...) clause ...) #'(if c (begin e ...) (my-cond clause ...))))))\n";
    let my = if macros.is_empty() { "" } else { "my-" };
    let forms: String = (0..forms)
        .map(|i| {
            format!(
                "(define (f{i} xs n)
                   (let loop ((xs xs) (acc '()))
                     ({my}cond ((null? xs) (reverse acc))
                           (({my}and (pair? xs) ({my}or (eqv? (car xs) n) (eqv? (car xs) {i})))
                            (loop (cdr xs) (cons (car xs) acc)))
                           (else ({my}let* ((x (car xs)) (y (+ x 1))) (loop (cdr xs) (cons y acc)))))))\n"
            )
        })
        .collect();
    match macros {
        "" => forms,
        "rules" => format!("{rules}{forms}"),
        _ => format!("{cases}{forms}"),
    }
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Value<'gc> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).expect("machine");
    loop {
        match machine.run(mc).expect("run") {
            Outcome::Paused => {}
            Outcome::Yielded(_) | Outcome::Deferred(_) => panic!("yielded"),
            Outcome::Done(value) => return value,
            Outcome::Raised(_) => panic!("raised"),
        }
    }
}

/// An arena with the symbol table in root 0 and the prelude's module in 1, once it's run.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 28, 2);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).expect("table");
        mc.set_root(0, symbols.value(mc));
        let session = SyntaxSession::named(mc, "prelude", PRELUDE).expect("session");
        let loaded = ragwort_native::load(mc, symbols, PRELUDE_NAME, &[], &[&session], &mut NoModules).expect("prelude");
        mc.set_root(1, Value::object(mc, loaded.module));
        for thunk in loaded.thunks {
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
            let prelude = mc.root(1).downcast::<Module>(mc).expect("the prelude");
            let session = SyntaxSession::new(mc, text).expect("session");
            let start = Instant::now();
            let loaded = if native {
                ragwort_native::load(mc, symbols, "main", &[], &[&session], &mut NoModules).expect("load")
            } else {
                load(mc, symbols, prelude, "main", &[&session], &[], &mut NoModules).expect("load")
            };
            let mut thunks = loaded.thunks;
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

    for (name, macros) in [("built-in macros", ""), ("syntax-rules macros", "rules"), ("syntax-case macros", "case")] {
        let text = macro_source(forms, macros);
        let us = time(&text, false, false).as_secs_f64() * 1e6 / forms as f64;
        println!("load {forms} forms, {name}: {us:.1} us per form");
    }

    let base = format!("(define (count n) (if (eqv? n 0) 0 (count (+ n -1)))) (count {N})");
    let native = format!(
        "(%define count (%lambda (n) (%if (%intrinsic eqv? n 0) 0 (%app count (%intrinsic + n -1))))) (%app count {N})"
    );
    let per = |d: Duration| d.as_secs_f64() * 1e9 / N as f64;
    println!("countdown through the prelude: {:.1} ns per iteration", per(time(&base, false, true)));
    println!("countdown on intrinsics:       {:.1} ns per iteration", per(time(&native, true, true)));
    let less = format!("(define (count n) (if (< n 1) 0 (count (- n 1)))) (count {N})");
    println!("countdown testing with <:      {:.1} ns per iteration", per(time(&less, false, true)));
    let append = format!("(define (count n s) (if (eqv? n 0) (string-length s) (count (- n 1) (string-append \"<@\" (symbol->string 'user) \">\")))) (count {N} \"\")");
    println!("string-append of 3 short:      {:.1} ns per iteration", per(time(&append, false, true)));
    let grow = format!("(define (count n s) (if (eqv? n 0) (string-length s) (count (- n 1) (string-append s \"ab\")))) (count {N} \"\")");
    println!("appending to a growing string: {:.1} ns per iteration", per(time(&grow, false, true)));
    let loop_on = |body: &str| format!("(define s \"!ping someone about something\") (define (count n) (if (eqv? n 0) 0 (begin {body} (count (- n 1))))) (count {N})");
    for (name, body) in [
        ("substring of 5", "(substring s 1 6)"),
        ("string-ref", "(string-ref s 3)"),
        ("string=? of a 28-char copy", "(string=? s (string-append \"!ping someone \" \"about something\"))"),
        ("string<? differing at 7", "(string<? s \"!ping sz\")"),
        ("number->string of a fixnum", "(number->string n)"),
        ("string->list of 28", "(string->list s)"),
        ("string-join of 3 with \", \"", "(string-join '(\"alice\" \"bob\" \"carol\") \", \")"),
        ("char<? and char->integer", "(if (char<? #\\a #\\b) (char->integer (string-ref s 2)) 0)"),
    ] {
        println!("{name:<30} {:.1} ns per iteration", per(time(&loop_on(body), false, true)));
    }
    let defs = "(define (pf a b) (+ a b)) (define (of a [b 1]) (+ a b)) (define (kf a #:b [b 1]) (+ a b))
                (define kv (let ([f (lambda (a #:b [b 1]) (+ a b))]) f))";
    let summing = |call: &str| format!("{defs} (define (count n acc) (if (eqv? n 0) acc (count (- n 1) (+ acc {call})))) (count {N} 0)");
    for (name, call) in [
        ("positional call", "(pf n 1)"),
        ("optional left out", "(of n)"),
        ("keyword, direct to the core", "(kf n #:b 1)"),
        ("keyword, matched at run time", "(kv n #:b 1)"),
        ("keyword procedure, no keywords", "(kv n)"),
    ] {
        println!("{name:<30} {:.1} ns per iteration", per(time(&summing(call), false, true)));
    }

    let switch = format!(
        "(define co (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
         (define (drain n) (if (eqv? n 0) 0 (begin (co/resume co) (drain (+ n -1))))) (drain {N})"
    );
    println!("coroutine resume and yield:    {:.1} ns per round trip", per(time(&switch, false, true)));
    let spawn = format!("(define (spawn n) (if (eqv? n 0) 0 (begin (co/resume (make-coroutine (lambda () n))) (spawn (+ n -1))))) (spawn {})", N / 100);
    println!("make and finish a coroutine:   {:.1} ns each", per(time(&spawn, false, true)) * 100.0);

    let each = |name: &str, body: &str| {
        let text = format!("(define (go n) (if (eqv? n 0) 0 (begin {body} (go (+ n -1))))) (go {})", N / 100);
        println!("{name:<31}{:.1} ns each", per(time(&text, false, true)) * 100.0);
    };
    each("try-resume a finishing coro:", "(co/try-resume (make-coroutine (lambda () n)))");
    each("raise-continuable to handler:", "(with-exception-handler (lambda (e) e) (lambda () (raise-continuable n)))");
    each("guard catching a raise:", "(guard (e (#t e)) (raise n))");
    each("guard, nothing raised:", "(guard (e (#t e)) n)");
    each("guard catching a VM fault:", "(guard (e (#t e)) (car n))");
    each("call-with-mark:", "(call-with-mark 'k n (lambda () (mark-value 'k #f)))");
    each("dynamic-wind, nothing raised:", "(dynamic-wind (lambda () 1) (lambda () n) (lambda () 2))");
    each("call/cc escape:", "(call/cc (lambda (k) (k n)))");
    each("call/cc escape from a wind:", "(call/cc (lambda (k) (dynamic-wind (lambda () 1) (lambda () (k n)) (lambda () 2))))");
}
