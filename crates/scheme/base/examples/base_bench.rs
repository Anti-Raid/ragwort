//! Times the loading of base code, which expands and compiles it. Also times a countdown that calls the
//! prelude's `eqv?` and `+`, against a countdown in native ragwort that calls the intrinsics directly.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_compiler::module::NoModules;
use ragwort_scheme::{LIBRARIES, load};
use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::Module;
use ragwort_vm::{MIN_SEGMENT, Machine, Outcome};

const N: i64 = 10_000_000;

/// Returns the source of `forms` definitions that together use most features of the expander. Each definition differs from the others by its number.
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

/// Returns the source of `forms` definitions that use `cond`, `and`, `or` and `let*`. If `macros` is "", they use the built-in macros.
/// Otherwise they use copies of those macros, written with `syntax-rules` if `macros` is "rules", and with `syntax-case` for any other value.
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
    let my = if macros.is_empty() {
        ""
    } else {
        "my-"
    };
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

/// Creates an arena with the symbol table in root 0 and a list of the modules of Scheme's libraries in root 1. The libraries have run.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 28, 2);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).expect("table");
        mc.set_root(0, symbols.value(mc));
        let mut libraries = Value::NULL;
        for (name, source) in LIBRARIES {
            let session = SyntaxSession::named(mc, name, source).expect("session");
            let loaded = ragwort_native::load(mc, symbols, name, &[], &[&session], &mut NoModules).expect("a library");
            for thunk in loaded.thunks {
                run(mc, thunk);
            }
            libraries = ragwort_types::pair::Pairs::new(mc).cons(Value::object(mc, loaded.module), libraries).expect("a pair").value(mc);
        }
        mc.set_root(1, libraries);
    });
    arena
}

/// Creates a fresh arena, loads `text` in it, and runs all forms of `text` but the last. Returns the arena, the time that loading took, and a machine that is ready to run the last form.
fn prepared(text: &str, native: bool) -> (Arena, Duration, Machine) {
    let mut arena = arena();
    arena.collect();
    let (loaded, machine) = arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).expect("table");
        let libraries: Vec<_> = ragwort_types::pair::Pairs::new(mc).elements(mc.root(1)).map(|module| module.downcast::<Module>(mc).expect("a library")).collect();
        let session = SyntaxSession::new(mc, text).expect("session");
        let start = Instant::now();
        let loaded = if native {
            ragwort_native::load(mc, symbols, "main", &[], &[&session], &mut NoModules).expect("load")
        } else {
            load(mc, symbols, "main", &[&session], &libraries, &mut NoModules).expect("load")
        };
        let mut thunks = loaded.thunks;
        let loaded = start.elapsed();
        let last = thunks.pop().expect("a form");
        for thunk in thunks {
            run(mc, thunk);
        }
        (loaded, Machine::new(mc, MIN_SEGMENT, last, &[]).expect("machine"))
    });
    (arena, loaded, machine)
}

/// Returns the best time over a few runs of loading `text`. If `run_all`, returns the best time of running the last form of `text` instead. The forms
/// before the last run before the timing starts.
fn time(text: &str, native: bool, run_all: bool) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..5 {
        let (mut arena, loaded, mut machine) = prepared(text, native);
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

/// Returns the best time over a few runs of the last form of `text`, which yields to the host over and over. The host reads what is yielded and resumes the machine at once, in the same step, until a run pauses. If `answers`, it resumes with one value, and otherwise with none.
fn time_yields(text: &str, answers: bool) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..5 {
        let (mut arena, _, mut machine) = prepared(text, false);
        let start = Instant::now();
        // Whether the machine waits at a yield that the next step has to resume.
        let mut waiting = false;
        let mut done = false;
        while !done {
            done = arena
                .step(|mc| {
                    loop {
                        let outcome = if waiting && answers {
                            machine.resume(mc, &[Value::TRUE])
                        } else {
                            machine.run(mc)
                        };
                        match outcome.expect("run") {
                            Outcome::Yielded(yielded) => {
                                black_box(yielded);
                                waiting = true;
                            }
                            // The machine pauses by itself when the collector is due. An answer it was given is kept, so the next step only runs it.
                            Outcome::Paused => {
                                waiting = false;
                                return false;
                            }
                            Outcome::Done(_) => return true,
                            Outcome::Raised(_) | Outcome::Deferred(_) => panic!("raised or deferred"),
                        }
                    }
                })
                .expect("room");
        }
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
    fn per(elapsed: Duration) -> f64 {
        elapsed.as_secs_f64() * 1e9 / N as f64
    }
    println!("countdown through the prelude: {:.1} ns per iteration", per(time(&base, false, true)));
    println!("countdown on intrinsics:       {:.1} ns per iteration", per(time(&native, true, true)));
    let less = format!("(define (count n) (if (< n 1) 0 (count (- n 1)))) (count {N})");
    println!("countdown testing with <:      {:.1} ns per iteration", per(time(&less, false, true)));
    let summed = format!("(define (sum n) (let ((total 0)) (let loop ((i n)) (if (eqv? i 0) total (begin (set! total (+ total i)) (loop (- i 1))))))) (sum {N})");
    println!("set! in a loop, in a register: {:.1} ns per iteration", per(time(&summed, false, true)));
    let boxed = format!("(define keep #f) (define (sum n) (let ((total 0)) (set! keep (lambda () total)) (let loop ((i n)) (if (eqv? i 0) total (begin (set! total (+ total i)) (loop (- i 1))))))) (sum {N})");
    println!("set! in a loop, boxed:         {:.1} ns per iteration", per(time(&boxed, false, true)));
    let append = format!("(define (count n s) (if (eqv? n 0) (string-length s) (count (- n 1) (string-append \"<@\" (symbol->string 'user) \">\")))) (count {N} \"\")");
    println!("string-append of 3 short:      {:.1} ns per iteration", per(time(&append, false, true)));
    let grow = format!("(define (count n s) (if (eqv? n 0) (string-length s) (count (- n 1) (string-append s \"ab\")))) (count {N} \"\")");
    println!("appending to a growing string: {:.1} ns per iteration", per(time(&grow, false, true)));
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
        let text = format!("(define s \"!ping someone about something\") (define (count n) (if (eqv? n 0) 0 (begin {body} (count (- n 1))))) (count {N})");
        println!("{name:<30} {:.1} ns per iteration", per(time(&text, false, true)));
    }
    // The same kinds of operation on text with an accented letter and an emoji, as chat messages have. `long` is a message of 200 characters.
    for (name, body) in [
        ("emoji text, substring of 5", "(substring s 8 13)"),
        ("emoji text, string-ref", "(string-ref s 20)"),
        ("emoji text, string-length", "(string-length s)"),
        ("emoji text, string=? of a copy", "(string=? s (string-append \"!ping 😀 sömeone \" \"about something\"))"),
        ("emoji text, string-append", "(string-append s \"!\")"),
        ("emoji text, string->list of 29", "(string->list s)"),
        ("emoji text, string-find", "(string-find s \"about\")"),
        ("emoji text, string-upcase", "(string-upcase s)"),
        ("long emoji text, string-ref at 190", "(string-ref long 190)"),
        ("long emoji text, substring of 90", "(substring long 100 190)"),
        ("long emoji text, string-find", "(string-find long \"bbb\")"),
    ] {
        let text = format!("(define s \"!ping 😀 sömeone about something\") (define long (string-append (make-string 150 #\\a) \"😀 é \" (make-string 46 #\\b))) (define (count n) (if (eqv? n 0) 0 (begin {body} (count (- n 1))))) (count {N})");
        println!("{name:<36} {:.1} ns per iteration", per(time(&text, false, true)));
    }
    fn command(body: &str) -> String {
        format!("(define cmd '(\"!echo\" \"a\" \"b\")) (define (count n acc) (if (eqv? n 0) acc (count (- n 1) (+ acc {body})))) (count {N} 0)")
    }
    let matched = r#"(match cmd [(list "!ping") 1] [(list "!echo" args ...) (length args)] [_ 0])"#;
    let by_hand = r#"(cond [(and (pair? cmd) (equal? (car cmd) "!ping") (null? (cdr cmd))) 1] [(and (pair? cmd) (equal? (car cmd) "!echo")) (length (cdr cmd))] [else 0])"#;
    println!("command by match:              {:.1} ns per iteration", per(time(&command(matched), false, true)));
    println!("command by cond:               {:.1} ns per iteration", per(time(&command(by_hand), false, true)));
    let defs = "(define (pf a b) (+ a b)) (define (of a [b 1]) (+ a b)) (define (kf a #:b [b 1]) (+ a b))
                (define kv (let ([f (lambda (a #:b [b 1]) (+ a b))]) f)) (define ap (car (list apply)))
                (define two (car (list (lambda (a) (values a 1)))))";
    for (name, call) in [
        ("positional call", "(pf n 1)"),
        ("optional left out", "(of n)"),
        ("keyword, direct to the core", "(kf n #:b 1)"),
        ("keyword, matched at run time", "(kv n #:b 1)"),
        ("keyword procedure, no keywords", "(kv n)"),
        ("apply through a variable", "(ap pf (list n 1))"),
        ("apply through a variable, one leading", "(ap pf n '(1))"),
        ("call-with-values of 2", "(call-with-values (lambda () (values n 1)) pf)"),
        ("call-with-values through a call", "(call-with-values (lambda () (two n)) pf)"),
    ] {
        let text = format!("{defs} (define (count n acc) (if (eqv? n 0) acc (count (- n 1) (+ acc {call})))) (count {N} 0)");
        println!("{name:<30} {:.1} ns per iteration", per(time(&text, false, true)));
    }

    // A table of 8 entries as a payload has them, and one of 1000 integer keys. Each line reads or writes it once per iteration.
    let tables = "(define t (table 'id 1 'name \"ann\" 'age 3 \"kind\" 4 \"a key that is too long to fit in a word\" 5 7 6 'last 7 'more 8))
                  (define big (let fill ((i 0) (big (make-table))) (if (eqv? i 1000) big (begin (table-set! big i i) (fill (+ i 1) big)))))
                  (define v (vector 1 2 3 4 5 6 7 8))";
    for (name, call) in [
        ("vector-ref, for comparison", "(vector-ref v 6)"),
        ("table-ref, symbol key", "(table-ref t 'last)"),
        ("table-ref, short string key", "(table-ref t \"kind\")"),
        ("table-ref, long string key", "(table-ref t \"a key that is too long to fit in a word\")"),
        ("table-ref, integer key", "(table-ref t 7)"),
        ("table-ref, integer key of 1000", "(table-ref big (modulo n 1000))"),
        ("table-ref, missing key", "(table-ref t 'none 0)"),
        ("table-set!, key that is there", "(begin (table-set! t 'age n) 1)"),
        ("table-set! and table-delete!", "(begin (table-set! t 'new n) (table-delete! t 'new) 1)"),
    ] {
        let text = format!("{tables} (define (count n acc) (if (eqv? n 0) acc (count (- n 1) (+ acc {call})))) (count {N} 0)");
        println!("{name:<31}{:.1} ns per iteration", per(time(&text, false, true)));
    }
    let building = format!("(define (build n) (if (eqv? n 0) 0 (begin (table 'id n 'name \"ann\" 'age 3 'kind 4) (build (+ n -1))))) (build {})", N / 10);
    println!("make a table of 4 entries:     {:.1} ns each", per(time(&building, false, true)) * 10.0);
    let walking = format!(
        "(define big (let fill ((i 0) (big (make-table))) (if (eqv? i 1000) big (begin (table-set! big i i) (fill (+ i 1) big)))))
         (define (walk n sum) (if (eqv? n 0) sum (walk (+ n -1) (let ((sum sum)) (table-for-each (lambda (key value) (set! sum (+ sum value))) big) sum)))) (walk {} 0)",
        N / 10_000
    );
    println!("table-for-each over 1000:      {:.1} ns per entry", per(time(&walking, false, true)) * 10.0);

    let switch = format!(
        "(define co (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
         (define (drain n) (if (eqv? n 0) 0 (begin (co/resume co) (drain (+ n -1))))) (drain {N})"
    );
    println!("coroutine resume and yield:    {:.1} ns per round trip", per(time(&switch, false, true)));
    let turns = format!(
        "(define (gen) (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
         (define a (gen)) (define b (gen))
         (define (drain n) (if (eqv? n 0) 0 (begin (co/resume a) (co/resume b) (drain (+ n -2))))) (drain {N})"
    );
    println!("two coroutines resumed in turn: {:.1} ns per round trip", per(time(&turns, false, true)));
    let hosted = format!("(define (emit n) (if (eqv? n 0) 0 (begin (co/yield n) (emit (+ n -1))))) (emit {N})");
    println!("yield to the host and back:    {:.1} ns per round trip", per(time_yields(&hosted, false)));
    let silent = format!("(define (emit n) (if (eqv? n 0) 0 (begin (co/yield) (emit (+ n -1))))) (emit {N})");
    println!("the same, yielding no values:  {:.1} ns per round trip", per(time_yields(&silent, false)));
    let answered = format!("(define (emit n last) (if (eqv? n 0) last (emit (+ n -1) (co/yield n)))) (emit {N} 0)");
    println!("the same, with a value back:   {:.1} ns per round trip", per(time_yields(&answered, true)));
    let nested = format!(
        "(define (emit n) (if (eqv? n 0) 0 (begin (co/yield n) (emit (+ n -1)))))
         (define (deep d n) (if (eqv? d 0) (emit n) (+ 1 (deep (+ d -1) n)))) (deep 20 {N})"
    );
    println!("the same, 20 calls deep:       {:.1} ns per round trip", per(time_yields(&nested, false)));
    let spawn = format!("(define (spawn n) (if (eqv? n 0) 0 (begin (co/resume (make-coroutine (lambda () n))) (spawn (+ n -1))))) (spawn {})", N / 100);
    println!("make and finish a coroutine:   {:.1} ns each", per(time(&spawn, false, true)) * 100.0);
    let respawn = format!("(define co (make-coroutine (lambda () 0))) (define (respawn n) (if (eqv? n 0) 0 (begin (co/resume (co/reset co (lambda () n))) (respawn (+ n -1))))) (respawn {})", N / 100);
    println!("reset and finish a coroutine:  {:.1} ns each", per(time(&respawn, false, true)) * 100.0);

    fn each(name: &str, body: &str) {
        let text = format!("(define (go n) (if (eqv? n 0) 0 (begin {body} (go (+ n -1))))) (go {})", N / 100);
        println!("{name:<31}{:.1} ns each", per(time(&text, false, true)) * 100.0);
    }
    each("try-resume a finishing coro:", "(co/try-resume (make-coroutine (lambda () n)))");
    each("make, suspend and close a coro:", "(let ((co (make-coroutine (lambda () (co/yield n))))) (co/resume co) (co/close co))");
    each("the same, closing in a wind:", "(let ((co (make-coroutine (lambda () (dynamic-wind (lambda () 1) (lambda () (co/yield n)) (lambda () 2)))))) (co/resume co) (co/close co))");
    each("raise-continuable to handler:", "(with-exception-handler (lambda (e) e) (lambda () (raise-continuable n)))");
    each("guard catching a raise:", "(guard (e (#t e)) (raise n))");
    each("guard, nothing raised:", "(guard (e (#t e)) n)");
    each("guard catching a VM fault:", "(guard (e (#t e)) (car n))");
    each("call-with-mark:", "(call-with-mark 'k n (lambda () (mark-value 'k #f)))");
    each("mark set in tail position:", "(call-with-mark 'k n (lambda () (with-continuation-mark 'k 1 (mark-value 'k #f))))");
    each("abort to a prompt:", "(call-with-continuation-prompt (lambda () (abort-current-continuation (default-continuation-prompt-tag) n)) (default-continuation-prompt-tag) (lambda (x) x))");
    each("dynamic-wind, nothing raised:", "(dynamic-wind (lambda () 1) (lambda () n) (lambda () 2))");
    each("call/cc escape:", "(call/cc (lambda (k) (k n)))");
    each("call/cc escape from a wind:", "(call/cc (lambda (k) (dynamic-wind (lambda () 1) (lambda () (k n)) (lambda () 2))))");
}
