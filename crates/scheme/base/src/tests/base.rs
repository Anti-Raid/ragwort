use ragwort_compiler::module::NoModules;
use ragwort_types::gc::{Arena, Value};
use ragwort_types::pair::Pairs;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use super::*;
use crate::ExpandErrorKind::*;

/// Creates the arena for the tests. Root 0 holds the symbol table. Root 1 holds a list of the loaded modules, newest first. Root 2 holds the
/// prelude's module, which has run. Root 3 holds the modules that other modules can require, as a list
/// of `(name . module)` pairs.
fn arena() -> Arena {
    arena_of(1 << 24)
}

/// Creates an arena of `bytes` bytes, set up as [`arena`] describes.
fn arena_of(bytes: usize) -> Arena {
    let mut arena = Arena::new(bytes, 4);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        mc.set_root(1, Value::NULL);
        mc.set_root(3, Value::NULL);
        let session = SyntaxSession::named(mc, "prelude", PRELUDE).unwrap();
        let loaded = ragwort_native::load(mc, symbols, PRELUDE_NAME, &[], &[&session], &mut NoModules).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        mc.set_root(2, Value::object(mc, loaded.module));
    });
    arena
}

/// Loads `text` as a module and returns the thunks of its forms. The module implicitly requires the modules loaded before it, as the input
/// of a REPL does. It exports all its definitions to the modules loaded after it.
fn load_text<'gc>(mc: &Mutation<'gc>, text: &str) -> Result<Vec<Value<'gc>>, Error> {
    let symbols = Symbols::of(mc.root(0)).unwrap();
    let prelude = mc.root(2).downcast::<Module>(mc).unwrap();
    let session = SyntaxSession::new(mc, text).unwrap();
    let all = SyntaxSession::new(mc, "(provide (all-defined-out))").unwrap();
    let mut earlier: Vec<Gc<Module>> = Pairs::new(mc).elements(mc.root(1)).map(|m| m.downcast::<Module>(mc).unwrap()).collect();
    earlier.reverse();
    let loaded = load(mc, symbols, prelude, "main", &[&session, &all], &earlier, &mut NoModules)?;
    let modules = Pairs::new(mc).cons(Value::object(mc, loaded.module), mc.root(1)).unwrap();
    mc.set_root(1, modules.value(mc));
    Ok(loaded.thunks)
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    run_raising(mc, thunk).map_err(|raised| raised.downcast::<Condition>(mc).expect("a condition").failure(mc).unwrap().fault)
}

/// Runs `thunk`. Returns its value, or the value that it raised and nothing caught.
fn run_raising<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Value<'gc>> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Yielded(_) | Outcome::Deferred(_) => panic!("yielded"),
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(raised),
        }
    }
}

fn raised_text<'gc>(mc: &Mutation<'gc>, raised: Value<'gc>) -> String {
    match raised.downcast::<Condition>(mc) {
        Some(c) => format!("{:?} {}", c.failure(mc).map(|failure| failure.fault), show(mc, c.irritants(mc))),
        None => show(mc, raised),
    }
}

/// Runs `text`, which must be one form that raises a value that nothing catches. Returns the written form of the raised value.
fn uncaught(text: &str) -> String {
    arena().mutate(|mc| {
        let [thunk] = load_text(mc, text).unwrap()[..] else { panic!("one form") };
        show(mc, run_raising(mc, thunk).expect_err("raised"))
    })
}

fn show<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    ragwort_printer_scheme::to_string(mc, v, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap()
}

/// Loads `text` and runs its forms in order. Returns the last one's value, written out, or the
/// fault one raised.
fn eval_in(arena: &mut Arena, text: &str) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let mut last = Value::VOID;
        for thunk in load_text(mc, text)? {
            match run(mc, thunk) {
                Ok(value) => last = value,
                Err(fault) => return Ok(Err(fault)),
            }
        }
        Ok(Ok(show(mc, last)))
    })
}

fn eval(text: &str) -> String {
    eval_in(&mut arena(), text).unwrap().unwrap()
}

/// Returns the kind of the expansion error of `text`, and the part of `text` that the error's span covers.
fn error(text: &str) -> (ExpandErrorKind, &str) {
    match eval_in(&mut arena(), text) {
        Err(Error::Expand(e)) => (e.kind, &text[e.start as usize..e.end as usize]),
        other => panic!("{text} expanded: {other:?}"),
    }
}

#[test]
fn literals_quotes_and_conditionals() {
    assert_eq!(eval("42"), "42");
    assert_eq!(eval("\"hi\""), "\"hi\"");
    assert_eq!(eval("#\\a"), "#\\a");
    assert_eq!(eval("'(a b . c)"), "(a b . c)");
    assert_eq!(eval("''a"), "(quote a)");
    assert_eq!(eval("(if #f 'yes 'no)"), "no");
    assert_eq!(eval("(if '() 'yes 'no)"), "yes");
    assert_eq!(eval("(if #f #f)"), "#<void>");
}

#[test]
fn procedures_and_definitions() {
    assert_eq!(eval("((lambda (x y) (cons y x)) 1 2)"), "(2 . 1)");
    assert_eq!(eval("((lambda args args) 1 2 3)"), "(1 2 3)");
    assert_eq!(eval("((lambda (a . rest) rest) 1 2 3)"), "(2 3)");
    assert_eq!(eval("(define (f x) (+ x 1)) (f 41)"), "42");
    assert_eq!(eval("(define ((adder n) x) (+ n x)) ((adder 2) 40)"), "42");
    assert_eq!(eval("(define (f . xs) xs) (f 1 2)"), "(1 2)");
    assert_eq!(eval("(define x 1) (set! x (+ x 1)) x"), "2");
    assert_eq!(eval("(begin (define a 1) (define b 2)) (+ a b)"), "3");
    // A load's definitions are all bound first, so they can refer to each other in any order.
    assert_eq!(eval("(define (even? n) (if (eqv? n 0) #t (odd? (+ n -1)))) (define (odd? n) (if (eqv? n 0) #f (even? (+ n -1)))) (even? 10)"), "#t");
}

#[test]
fn bodies_bind_their_definitions_as_letrec_star() {
    let body = "(define (f)
                  (define a 1)
                  (define (g) (+ a b))
                  (define b (+ a 1))
                  (g))
                (f)";
    assert_eq!(eval(body), "3");
    assert_eq!(eval("(define x 'global) (define (f) (define x 'local) x) (list (f) x)"), "(local global)");
    assert_eq!(eval("(let () (begin (define a 1) (define b 2)) (+ a b))"), "3");
    assert_eq!(eval("(let () (define a 1) (set! a 5) (define b a) b)"), "5");
    // A definition of a macro's name shadows the macro across the whole body or load, but
    // forms before it in the body are expanded as uses of the macro, as in R6RS.
    assert_eq!(eval("(let ((f #f)) (set! f (lambda () (when))) (define (when) 99) (f))"), "99");
    assert_eq!(error("(let () (when) (define (when) 99) (when))"), (BadSyntax, "(when)"));
}

#[test]
fn lets_of_every_kind() {
    assert_eq!(eval("(let ((x 1) (y 2)) (cons x y))"), "(1 . 2)");
    assert_eq!(eval("(let ((x 1)) (let ((x 2) (y x)) y))"), "1");
    assert_eq!(eval("(let ((x 1)) (let* ((x 2) (y x)) y))"), "2");
    assert_eq!(eval("(let* () 5)"), "5");
    assert_eq!(eval("(letrec ((f (lambda (n) (if (eqv? n 0) 'done (f (+ n -1)))))) (f 10))"), "done");
    assert_eq!(eval("(letrec* ((a 1) (b (+ a 1))) b)"), "2");
    assert_eq!(eval("(let loop ((i 0) (acc '())) (if (eqv? i 3) acc (loop (+ i 1) (cons i acc))))"), "(2 1 0)");
    // A named let's inits are outside its name's scope.
    assert_eq!(eval("(define (f) 'outer) (let f ((x (f))) x)"), "outer");
}

#[test]
fn derived_conditionals() {
    assert_eq!(eval("(list (and) (and 1) (and 1 2) (and #f 2))"), "(#t 1 2 #f)");
    assert_eq!(eval("(list (or) (or 1) (or #f 2) (or #f #f))"), "(#f 1 2 #f)");
    assert_eq!(eval("(list (when #t 1 2) (when #f 1) (unless #f 3) (unless #t 3))"), "(2 #<void> 3 #<void>)");
    assert_eq!(eval("(cond (#f 1) ((eqv? 1 1) 2) (else 3))"), "2");
    assert_eq!(eval("(cond (#f 1) (else 2 3))"), "3");
    assert_eq!(eval("(cond ((memv 2 '(1 2 3)) => cdr) (else 'no))"), "(3)");
    assert_eq!(eval("(cond (#f) ('x))"), "x");
    assert_eq!(eval("(cond (#f 1))"), "#<void>");
    let case = "(define (kind x) (case x ((1 2 3) 'small) ((a b) 'letter) ((10) => (lambda (n) (+ n 1))) (else 'other)))
                (list (kind 2) (kind 'b) (kind 10) (kind \"s\"))";
    assert_eq!(eval(case), "(small letter 11 other)");
    assert_eq!(eval("(case 5 ((1) 'one) (else => (lambda (n) (cons n n))))"), "(5 . 5)");
}

#[test]
fn do_loops() {
    assert_eq!(eval("(do ((i 0 (+ i 1)) (acc '() (cons i acc))) ((eqv? i 4) acc))"), "(3 2 1 0)");
    assert_eq!(eval("(let ((b (box 0))) (do ((i 0 (+ i 1))) ((eqv? i 5) (unbox b)) (set-box! b (+ (unbox b) i))))"), "10");
    assert_eq!(eval("(do ((i 0 (+ i 1))) ((eqv? i 2)))"), "#<void>");
}

#[test]
fn quasiquote_builds_what_it_unquotes() {
    assert_eq!(eval("(let ((x 1) (ys '(2 3))) `(a ,x ,@ys b))"), "(a 1 2 3 b)");
    assert_eq!(eval("`(1 ,@'() 2)"), "(1 2)");
    assert_eq!(eval("(let ((x 1)) `(a . ,x))"), "(a . 1)");
    assert_eq!(eval("`(a b)"), "(a b)");
    assert_eq!(eval("(let ((x 1)) `(a `(b ,(c ,x))))"), "(a (quasiquote (b (unquote (c 1)))))");
    assert_eq!(eval("`(1 ,@(list 2 3))"), "(1 2 3)");
    assert_eq!(eval("(let ((x 'y)) `((,x . ,x) ,(list x)))"), "((y . y) (y))");
    assert_eq!(eval("`#(1 2)"), "#(1 2)");
    assert_eq!(error("(let ((x 1)) `#(1 ,x))"), (Unsupported, "#(1 ,x)"));
    assert_eq!(error("`,@x"), (BadSyntax, ",@x"));
}

#[test]
fn prelude_procedures() {
    assert_eq!(eval("(+ 1 2 3)"), "6");
    assert_eq!(eval("(apply + 1 2 '(3 4))"), "10");
    assert_eq!(eval("(map + '(1 2 3) '(10 20 30))"), "(11 22 33)");
    assert_eq!(eval("(map (lambda (x) (cons x x)) '(1 2))"), "((1 . 1) (2 . 2))");
    assert_eq!(eval("(let ((b (box '()))) (for-each (lambda (x) (set-box! b (cons x (unbox b)))) '(1 2 3)) (unbox b))"), "(3 2 1)");
    assert_eq!(eval("(call-with-values (lambda () (values 1 2 3)) list)"), "(1 2 3)");
    assert_eq!(eval("(call-with-values (lambda () (values 10 20)) (lambda (a b) (+ a b)))"), "30");
    assert_eq!(eval("(call-with-values (lambda () (values)) (lambda () 'none))"), "none");
    assert_eq!(eval("(call-with-values (lambda () 1) list)"), "(1)");
    assert_eq!(eval("(+ 1 (call/cc (lambda (k) (+ 100 (k 5)))))"), "6");
    assert_eq!(eval("(call-with-current-continuation (lambda (k) (k 42)))"), "42");
    assert_eq!(
        eval("(let ((n (box 0)) (kb (box #f))) (let ((v (call/cc (lambda (k) (set-box! kb k) 0)))) (set-box! n (+ (unbox n) 1)) (if (eq? (unbox n) 3) v ((unbox kb) (+ v 10)))))"),
        "20"
    );
    assert_eq!(eval("(call-with-values (lambda () (call/cc (lambda (k) (k 1 2 3)))) list)"), "(1 2 3)");
    let pausable = "
        (let ()
          (define out '())
          (define (emit x) (set! out (cons x out)))
          (define ret-point-k #f)
          (define run-pausable
            (lambda (proc)
              (call/cc
                (lambda (k)
                  (set! ret-point-k k)
                  (let ((res (proc)))
                    (ret-point-k res))))))
          (define resume
            (lambda ()
              (call/cc
                (lambda (k)
                  (let ((goto ret-point-k))
                    (set! ret-point-k k)
                    (goto (void)))))))
          (define pause
            (lambda ()
              (call/cc
                (lambda (k)
                  (let ((goto ret-point-k))
                    (set! ret-point-k k)
                    (goto (void)))))))
          (run-pausable
            (lambda ()
              (emit 1)
              (pause)
              (emit 3)
              (pause)
              (emit 5)
              (pause)
              (emit 7)))
          (emit 2)
          (resume)
          (emit 4)
          (resume)
          (emit 6)
          (resume)
          (emit 8)
          (emit 9)
          (reverse out))
    ";
    assert_eq!(eval(pausable), "(1 2 3 4 5 6 7 8 9)");
    assert_eq!(eval_in(&mut arena(), "(apply + (values 1 2))"), Ok(Err(Fault::ValueCount)));
    assert_eq!(eval_in(&mut arena(), "(call-with-values (lambda () (values 1 2)) (lambda (a) a))"), Ok(Err(Fault::Arity)));
    assert_eq!(eval("(list (length '(1 2 3)) (reverse '(1 2 3)) (append '(1) '(2 3) '() '(4 . 5)))"), "(3 (3 2 1) (1 2 3 4 . 5))");
    assert_eq!(eval("(list (list-tail '(1 2 3) 1) (list-ref '(1 2 3) 2) (memq 'c '(a b c d)) (assv 2 '((1 . a) (2 . b))))"), "((2 3) 3 (c d) (2 . b))");
    assert_eq!(eval("(list (not #f) (not 1) (list? '(1)) (list? '(1 . 2)) (boolean? #f) (equal? '(1 (2)) '(1 (2))))"), "(#t #f #t #f #t #t)");
    assert_eq!(eval("(list (list-tail '(a b . c) 2) (list-ref '(a b . c) 1))"), "(c b)");
    assert_eq!(eval("(list (append) (append 'x) (append '(1 2) '()))"), "(() x (1 2))");
    assert_eq!(eval("(list (member '(2) '((1) (2) (3))) (assq 'b '((a . 1) (b . 2))) (assoc '(k) '(((j) . 1) ((k) . 2))))"), "(((2) (3)) (b . 2) ((k) . 2))");
    assert_eq!(eval_in(&mut arena(), "(reverse '(1 . 2))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(memq 'b '(a . c))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(assq 'b '(1))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(append '(1 . 2) '())"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(length '(1 . 2))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(list-tail '(1 2) 3)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(list-tail '(1 2) -1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(list-ref '(1 2) 2)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(list-ref '(1 . 2) 1)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(car '())"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(apply car '(1 2))"), Ok(Err(Fault::Arity)));
}

#[test]
fn macros_are_hygienic() {
    // `or` binds a temporary, which doesn't capture the code's own `t`.
    assert_eq!(eval("(let ((t 5)) (or #f t))"), "5");
    assert_eq!(eval("(define t 6) (or #f t)"), "6");
    // An identifier that a built-in macro introduces refers to the base binding, even if the code binds the same name.
    assert_eq!(eval("(let ((if list) (begin 'no)) (cond (#f 1) (else 2)))"), "2");
    assert_eq!(eval("(let ((loop 5)) (do ((i 0 (+ i 1))) ((eqv? i 3) loop)))"), "5");
    assert_eq!(eval("(let ((cons #f) (memv #f)) (list `(1 ,(+ 1 1)) (case 2 ((2) 'two))))"), "((1 2) two)");
    // A top-level definition of the code shadows the prelude's binding in the code, but not in the output of a built-in macro.
    assert_eq!(eval("(define (cons a b) 'mine) (list (cons 1 2) `(1 ,2))"), "(mine (1 2))");
    // `else` is auxiliary syntax: bound locally, it's an ordinary variable.
    assert_eq!(eval("(let ((else #f)) (cond (else 'yes)))"), "#<void>");
    // Keywords can be shadowed like any other binding.
    assert_eq!(eval("(let ((if (lambda (a b c) 'shadowed))) (if #t 1 2))"), "shadowed");
    assert_eq!(eval("(define (f list) (list 1)) (f (lambda (x) (cons x x)))"), "(1 . 1)");
}

#[test]
fn each_load_requires_the_ones_before() {
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(define counter 0) (define (bump!) (set! counter (+ counter 1)) counter)"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(bump!) (bump!)"), Ok(Ok("2".into())));
    assert_eq!(eval_in(&mut arena, "(define (car x) 'mine)"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(list (car '(1)) (cadr '(1 2)))"), Ok(Ok("(mine 2)".into())));
    assert!(matches!(eval_in(&mut arena, "nowhere"), Err(Error::Expand(e)) if e.kind == Unbound));
}

#[test]
fn numbers_compare_by_value() {
    let text = "(list (< 1 2 3) (< 1 3 2) (> 3 2 1) (<= 1 1 2) (>= 2 2 3) (= 1 1.0 1) (< 1/3 0.34) (< 1) (= 1+2i 1+2i)
                      (< 1267650600228229401496703205376 1267650600228229401496703205377) (> +inf.0 100000000000000000000000000000000) (< +nan.0 1) (= +nan.0 +nan.0) (>= 2 1 +nan.0))";
    assert_eq!(eval(text), "(#t #f #t #t #f #t #t #t #t #t #t #f #f #f)");
    // Every argument is checked, even an argument after the ones that decide the result.
    assert_eq!(uncaught("(< 2 1 'x)"), "#<error <: wrong type of argument 2 1 x>");
    assert_eq!(uncaught("(< 1+2i 2)"), "#<error <: wrong type of argument 1+2i 2>");
    assert_eq!(uncaught("(<)"), "#<error wrong number of arguments #<procedure <> 0>");
}

#[test]
fn powers_stay_exact_when_they_can() {
    let text = "(list (expt 2 100) (expt 2/3 3) (expt 2 -2) (expt 1.5 2) (expt 4 1/2) (expt 0 0) (expt 0.0 0) (expt -1 (expt 10 30))
                      (expt 1 (expt 10 30)) (expt 0+1i 2) (expt -8 1/3))";
    assert_eq!(eval(text), "(1267650600228229401496703205376 8/27 1/4 2.25 2 1 1 1 1 -1 1.0+1.732050807568877i)");
    assert_eq!(uncaught("(expt 0 -1)"), "#<error expt: division by zero 0 -1>");
    // A result that is too large for the arena is refused before it is computed, which ends the run.
    arena().mutate(|mc| {
        let [thunk] = load_text(mc, "(expt 3 (expt 10 15))").unwrap()[..] else { panic!("one form") };
        assert_eq!(Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap().run(mc), Err(Fault::OutOfMemory));
        // A result that fits is charged for its work before the work is done.
        let [thunk] = load_text(mc, "(expt 3 1000000)").unwrap()[..] else { panic!("one form") };
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        machine.set_fuel(10_000);
        assert_eq!(machine.run(mc), Err(Fault::OutOfFuel));
    });
    assert_eq!(uncaught("(expt 'x 2)"), "#<error expt: wrong type of argument x 2>");
}

#[test]
fn integer_division_keeps_the_sign_it_should() {
    let text = "(list (quotient 17 5) (quotient -17 5) (remainder 17 -5) (remainder -17 5) (modulo -17 5) (modulo 17 -5) (modulo -15 5)
                      (quotient 17.0 5) (modulo -17 5.0) (remainder -0.0 3) (modulo 100000000000000000000 7) (quotient -100000000000000000000 3)
                      (remainder 4611686018427387903 -1) (quotient -4611686018427387904 -1))";
    assert_eq!(eval(text), "(3 -3 2 -2 3 -3 0 3.0 3.0 -0.0 2 -33333333333333333333 0 4611686018427387904)");
    assert_eq!(uncaught("(modulo 1 0)"), "#<error modulo: division by zero 1 0>");
    assert_eq!(uncaught("(remainder 1/2 3)"), "#<error remainder: not an integer 1/2 3>");
    assert_eq!(uncaught("(quotient 1.5 1)"), "#<error quotient: not an integer 1.5 1>");
    assert_eq!(uncaught("(modulo \"1\" 2)"), "#<error modulo: wrong type of argument \"1\" 2>");
}

#[test]
fn a_continuation_reentered_in_a_loop_sees_its_own_spilled_values() {
    // 60 values are live across a `call/cc` in the first pass of the loop, more than a frame's registers
    // hold. When the continuation is called after the loop has run another pass, the first pass must see its own values.
    let names: Vec<String> = (0..60).map(|j| format!("a{j}")).collect();
    let binds: String = names.iter().enumerate().map(|(j, a)| format!("({a} (+ i {j}))")).collect();
    let text = format!(
        "(define k #f) (define again #f)
         (define (f)
           (let loop ((i 0))
             (let ({binds})
               (when (= i 0) (call/cc (lambda (c) (set! k c))))
               (if (or again (= i 3)) (+ {}) (loop (+ i 1))))))
         (let ((result (f))) (if again result (begin (set! again #t) (k #f))))",
        names.join(" ")
    );
    assert_eq!(eval(&text), "1770");
}

#[test]
fn assigned_variables_mean_the_same_kept_in_registers_or_boxes() {
    let text = "(list (let ((total 0)) (let loop ((i 0)) (when (< i 10) (set! total (+ total i)) (loop (+ i 1)))) total)
                      (let ((x 1)) (list x (begin (set! x 2) x)))
                      (let ((n 0) (k #f))
                        (let ((r (call/cc (lambda (c) (set! k c) 0))))
                          (set! n (+ n 1))
                          (if (< n 3) (k r) n))))";
    assert_eq!(eval(text), "(45 (1 2) 3)");
}

#[test]
fn bitwise_operations_work_on_any_exact_integer() {
    let text = "(list (bitwise-and) (bitwise-ior) (bitwise-xor) (bitwise-and 12 10) (bitwise-ior 12 10) (bitwise-xor 12 10 1)
                      (bitwise-not -5) (arithmetic-shift 1 70) (arithmetic-shift -5 -1) (integer-length -256) (bit-count -8)
                      (bit-set? 2 5) (bit-set? 1 5) (bit-set? 100 -1) (bit-field 13 1 3) (bit-field -1 0 70) (bit-field-replace 0 7 2 4)
                      (bitwise-and (arithmetic-shift 1 100) (- (arithmetic-shift 1 101) 1)) (bitwise-and (arithmetic-shift 1 100) 5)
                      (bitwise-xor 4611686018427387903 -4611686018427387904) (bit-field-replace (arithmetic-shift 1 80) -1 0 3))";
    let want = "(-1 0 0 8 14 7 4 1180591620717411303424 -3 8 3 #t #f #t 2 1180591620717411303423 12 \
                1267650600228229401496703205376 0 -1 1208925819614629174706183)";
    assert_eq!(eval(text), want.split_whitespace().collect::<Vec<_>>().join(" "));
    assert_eq!(uncaught("(bitwise-and 1.0 2)"), "#<error bitwise-and: wrong type of argument 1.0 2>");
    assert_eq!(uncaught("(bit-field 5 3 1)"), "#<error bit-field: value out of range 5 3 1>");
    assert_eq!(uncaught("(bit-set? -1 5)"), "#<error bit-set?: value out of range -1 5>");
}

#[test]
fn bit_fields_wider_than_their_numbers_cost_no_more() {
    // Each call would need a mask of 125 MB if it built one, far more than the arena has.
    let text = "(list (bit-field 5 0 1000000000) (bit-field-replace 1 2 0 1000000000) (logical-shift-right 5 0 1000000000)
                      (bit-field-replace 5 -1 1 2) (bit-field-replace -1 0 1 3) (bit-field (arithmetic-shift 1 100) 0 1000000000))";
    assert_eq!(eval(text), "(5 2 5 7 -7 1267650600228229401496703205376)");
    arena().mutate(|mc| {
        let [thunk] = load_text(mc, "(arithmetic-shift 1 (expt 10 15))").unwrap()[..] else { panic!("one form") };
        assert_eq!(Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap().run(mc), Err(Fault::OutOfMemory));
    });
}

#[test]
fn logical_shifts_treat_a_number_as_so_many_bits() {
    let text = "(list (logical-shift-right -1 28 32) (logical-shift-right -16 2 8) (logical-shift-right -1 40 32) (logical-shift-right 5 0 64)
                      (logical-shift-left -1 28 32) (logical-shift-left 255 4 8) (logical-shift-left 1 70 64) (logical-shift-left 3 63 64))";
    assert_eq!(eval(text), "(15 60 0 5 4026531840 240 0 9223372036854775808)");
    assert_eq!(uncaught("(logical-shift-right 1 -1 32)"), "#<error bit-field: value out of range 1 -1 32>");
    assert_eq!(uncaught("(logical-shift-left 1 -1 32)"), "#<error bit-field: value out of range 1 -1 32>");
    for text in ["(logical-shift-right 5 40.0 32)", "(logical-shift-left 5 81/2 32)", "(logical-shift-right 5 40 2.5)", "(logical-shift-left 'x 40 32)"] {
        assert!(uncaught(text).contains(": wrong type of argument "), "{text}");
    }
}

#[test]
fn bytevectors_hold_multibyte_integers_little_or_big_endian() {
    let text = "(let ((b (make-bytevector 12 0)))
                  (bytevector-u16be-set! b 0 #x1234)
                  (bytevector-u32le-set! b 2 #xdeadbeef)
                  (bytevector-u64be-set! b 3 #xfedcba9876543210)
                  (list (bytevector-u8-ref b 0) (bytevector-u8-ref b 1) (bytevector-u16le-ref b 0) (bytevector-u8-ref b 2)
                        (bytevector-u64be-ref b 3) (bytevector-u64le-ref b 3) (bytevector-u32be-ref b 7)
                        (bytevector-u16be-ref b 10) (bytevector-u64be-ref b 4)))";
    let want = "(18 52 13330 239 18364758544493064720 1167088121787636990 1985229328 4096 15905192667998457856)";
    assert_eq!(eval(text), want);
    assert_eq!(eval("(bytevector-u32be-ref #u8(1 2 3 4 5) 1)"), "33752069");
    assert_eq!(eval_in(&mut arena(), "(bytevector-u32be-ref #u8(1 2 3 4) 1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(bytevector-u16be-set! (make-bytevector 2 0) 0 65536)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(bytevector-u16be-set! (make-bytevector 2 0) 0 -1)"), Ok(Err(Fault::OutOfRange)));
    // A fill that is an integer but not a byte is out of range, and anything else is the wrong type.
    for fill in ["256", "-1", "(expt 2 100)"] {
        assert_eq!(eval_in(&mut arena(), &format!("(make-bytevector 2 {fill})")), Ok(Err(Fault::OutOfRange)), "{fill}");
    }
    assert_eq!(eval_in(&mut arena(), "(make-bytevector 2 'x)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(integer->char (expt 2 100))"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(integer->char 1.5)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(bytevector-u16be-set! #u8(1 2) 0 1)"), Ok(Err(Fault::Immutable)));
}

#[test]
fn bytevectors_hold_signed_integers_too() {
    let text = "(let ((b (make-bytevector 16 0)))
                  (bytevector-s32be-set! b 0 -1)
                  (bytevector-s64le-set! b 4 -9223372036854775808)
                  (bytevector-s16be-set! b 12 -32768)
                  (bytevector-s8-set! b 14 -128)
                  (bytevector-u8-set! b 15 127)
                  (list (bytevector-u32be-ref b 0) (bytevector-s64le-ref b 4) (bytevector-u64le-ref b 4)
                        (bytevector-s64be-ref b 4) (bytevector-s16be-ref b 12) (bytevector-s16le-ref b 12)
                        (bytevector-s8-ref b 14) (bytevector-s8-ref b 15) (bytevector-u8-ref b 14) (bytevector-s16be-ref b 0)))";
    let want = "(4294967295 -9223372036854775808 9223372036854775808 128 -32768 128 -128 127 128 -1)";
    assert_eq!(eval(text), want);
    assert_eq!(eval("(bytevector-s16le-ref #u8(255 254) 0)"), "-257");
    for bad in ["(bytevector-s8-set! (make-bytevector 1 0) 0 128)", "(bytevector-s8-set! (make-bytevector 1 0) 0 -129)",
                "(bytevector-u8-set! (make-bytevector 1 0) 0 256)", "(bytevector-s64be-set! (make-bytevector 8 0) 0 (expt 2 63))"] {
        assert_eq!(eval_in(&mut arena(), bad), Ok(Err(Fault::OutOfRange)), "{bad}");
    }
    assert_eq!(eval_in(&mut arena(), "(bytevector-s8-ref #u8(1) 0.0)"), Ok(Err(Fault::WrongType)));
}

#[test]
fn strings_append_and_count_characters() {
    let text = "(list (string-length \"\") (string-length \"héllo\") (string-length \"🦀ab\") (string-append) (string-append \"a\")
                      (string-append \"ab\" \"\" \"cd\" \"é🦀\") (apply string-append (list \"x\" \"y\" \"z\")))";
    assert_eq!(eval(text), "(0 5 3 \"\" \"a\" \"abcdé🦀\" \"xyz\")");
    // Long strings are joined into ropes. A rope has the length of its characters and compares by them.
    let long = "(define (grow s n) (if (eqv? n 0) s (grow (string-append s s \"!\") (- n 1))))
                (define s (grow \"ab\" 12))
                (list (string-length s) (equal? (string-append s \"z\") (string-append s \"z\")) (string-length (string-append s s)))";
    assert_eq!(eval(long), "(12287 #t 24574)");
    assert_eq!(uncaught("(string-append \"a\" 'b)"), "#<error string-append: wrong type of argument \"a\" b>");
    assert_eq!(uncaught("(string-length 'a)"), "#<error string-length: wrong type of argument a>");
}

#[test]
fn strings_slice_index_and_compare() {
    let text = "(list (substring \"hello\" 1 3) (substring \"hello\" 2) (substring \"héllo🦀\" 4 6) (substring \"abc\" 3)
                      (string-ref \"a🦀b\" 1) (string-ref \"abc\" 0)
                      (string->list \"abc\") (string->list \"abcd\" 1) (string->list \"abcd\" 1 3) (string->list \"\"))";
    assert_eq!(eval(text), "(\"el\" \"llo\" \"o🦀\" \"\" #\\🦀 #\\a (#\\a #\\b #\\c) (#\\b #\\c #\\d) (#\\b #\\c) ())");
    let compared = "(list (string=? \"a\" \"a\" \"a\") (string=? \"a\" \"b\") (string<? \"a\" \"b\" \"c\") (string<? \"ab\" \"abc\") (string<? \"b\" \"a\")
                          (string>? \"c\" \"b\" \"a\") (string<=? \"a\" \"a\" \"b\") (string>=? \"b\" \"c\") (string<? \"Z\" \"a\" \"é\" \"🦀\") (string=? \"x\"))";
    assert_eq!(eval(compared), "(#t #f #t #t #f #t #t #f #t #t)");
    assert_eq!(uncaught("(substring \"abc\" 2 1)"), "#<error substring: value out of range \"abc\" 2 1>");
    assert_eq!(uncaught("(substring \"abc\" 0 4)"), "#<error substring: value out of range \"abc\" 0 4>");
    assert_eq!(uncaught("(string-ref \"abc\" 3)"), "#<error string-ref: value out of range \"abc\" 3>");
    assert_eq!(uncaught("(string-ref \"abc\" -1)"), "#<error string-ref: value out of range \"abc\" -1>");
    assert_eq!(uncaught("(string->list \"abc\" 2 1)"), "#<error string->list: value out of range \"abc\" 2 1>");
    // Every argument is checked, even an argument after the ones that decide the result.
    assert_eq!(uncaught("(string<? \"b\" \"a\" 'c)"), "#<error string<?: wrong type of argument \"b\" \"a\" c>");
}

#[test]
fn characters_are_code_points() {
    let text = "(list (char? #\\a) (char? \"a\") (char->integer #\\a) (char->integer #\\🦀) (integer->char 955) (integer->char 1114111)
                      (char=? #\\a #\\a #\\a) (char=? #\\a #\\b) (char<? #\\a #\\b #\\é) (char<? #\\b #\\a) (char>? #\\c #\\b #\\a)
                      (char<=? #\\a #\\a) (char>=? #\\a #\\b) (char=? #\\x) (eqv? (string-ref \"λ\" 0) (integer->char 955)))";
    assert_eq!(eval(text), "(#t #f 97 129408 #\\λ #\\x10ffff #t #f #t #f #t #t #f #t #t)");
    // The printer writes an invisible character as a hex escape, and the reader reads the escape back.
    assert_eq!(eval("(list (char->integer #\\x10ffff) (char->integer #\\x200b) (string->list \"a\\x200b;\\xfeff;\"))"), "(1114111 8203 (#\\a #\\x200b #\\xfeff))");
    assert_eq!(uncaught("(integer->char 55296)"), "#<error integer->char: value out of range 55296>");
    assert_eq!(uncaught("(integer->char 1114112)"), "#<error integer->char: value out of range 1114112>");
    assert_eq!(uncaught("(integer->char -1)"), "#<error integer->char: value out of range -1>");
    assert_eq!(uncaught("(char->integer \"a\")"), "#<error char->integer: wrong type of argument \"a\">");
    assert_eq!(uncaught("(char<? #\\b #\\a 'c)"), "#<error char<?: wrong type of argument #\\b #\\a c>");
}

#[test]
fn strings_join_with_a_separator() {
    let text = "(list (string-join '(\"a\" \"b\" \"c\")) (string-join '(\"a\" \"b\" \"c\") \", \") (string-join '()) (string-join '(\"solo\") \"-\")
                      (string-join '(\"<@\" \">\") \"user\") (string-join '(\"é\" \"🦀\") \"\"))";
    assert_eq!(eval(text), "(\"a b c\" \"a, b, c\" \"\" \"solo\" \"<@user>\" \"é🦀\")");
    let long = "(define (words n acc) (if (eqv? n 0) acc (words (- n 1) (cons (number->string n) acc))))
                (string-length (string-join (words 1000 '()) \", \"))";
    assert_eq!(eval(long), "4891");
    assert_eq!(uncaught("(string-join '(\"a\" b))"), "#<error string-join: wrong type of argument (\"a\" b)>");
    assert_eq!(uncaught("(string-join '(\"a\" . \"b\"))"), "#<error string-join: wrong type of argument (\"a\" . \"b\")>");
    assert_eq!(uncaught("(string-join '(\"a\") 'x)"), "#<error string-join: wrong type of argument (\"a\") x>");
}

#[test]
fn numbers_write_as_they_read() {
    let text = "(list (number->string 42) (number->string -17 16) (number->string 255 16) (number->string 1/3 2) (number->string 1.5)
                      (number->string 1.5 2) (number->string 0.1 16) (number->string -0.0 2) (number->string 1e21) (number->string +nan.0)
                      (number->string 1+2i) (number->string 0-1/2i 2) (number->string (expt 2 100) 16) (number->string 6.0 8))";
    assert_eq!(
        eval(text),
        "(\"42\" \"-11\" \"ff\" \"1/11\" \"1.5\" \"1.1\" \"0.1999999999999a\" \"-0.0\" \"1e21\" \"+nan.0\" \"1+2i\" \"-1/10i\" \"10000000000000000000000000\" \"6.0\")"
    );
    // `number->string` handles fixnums on its own path. The cases include both ends of the fixnum range and the first integer past it.
    let ends = "(list (number->string 0) (number->string 0 2) (number->string -1 16) (number->string 1234567) (number->string 12345678)
                      (number->string 4611686018427387903) (number->string -4611686018427387904 16) (number->string -4611686018427387904 2)
                      (number->string 4611686018427387904))";
    assert_eq!(
        eval(ends),
        "(\"0\" \"0\" \"-1\" \"1234567\" \"12345678\" \"4611686018427387903\" \"-4000000000000000\" \"-100000000000000000000000000000000000000000000000000000000000000\" \"4611686018427387904\")"
    );
    assert_eq!(uncaught("(number->string 10 3)"), "#<error number->string: value out of range 10 3>");
    assert_eq!(uncaught("(number->string 'x)"), "#<error number->string: wrong type of argument x>");
}

#[test]
fn symbols_and_strings_name_each_other() {
    let text = "(list (symbol? 'a) (symbol? \"a\") (symbol? '#:a) (string? \"a\") (string? 'a) (symbol->string 'abc) (eq? 'abc (string->symbol \"abc\"))
                      (string->symbol \"two words\") (eq? (string->symbol (symbol->string 'x)) 'x))";
    assert_eq!(eval(text), "(#t #f #f #t #f \"abc\" #t |two words| #t)");
    assert_eq!(uncaught("(symbol->string \"a\")"), "#<error symbol->string: wrong type of argument \"a\">");
}

#[test]
fn keywords_are_interned_values() {
    let text = "(list '#:when (keyword? '#:when) (keyword? 'when) (eq? '#:a '#:a) (eq? '#:a (string->keyword \"a\"))
                      (keyword->string '#:when) (equal? '(#:x 1) '(#:x 1)) (string->keyword \"two words\"))";
    assert_eq!(eval(text), "(#:when #t #f #t #t \"when\" #t #:|two words|)");
    // As in Racket, a keyword isn't an expression by itself.
    assert_eq!(eval_in(&mut arena(), "(list #:when 1)"), Ok(Err(Fault::Keyword)));
}

#[test]
fn bad_syntax_points_at_itself() {
    assert_eq!(error("(if)"), (BadSyntax, "(if)"));
    assert_eq!(error("(lambda (x 1) x)"), (BadSyntax, "1"));
    assert_eq!(error("(lambda (x y x) x)"), (Duplicate, "x"));
    assert_eq!(error("(let ((a 1) (a 2)) a)"), (Duplicate, "a"));
    assert_eq!(error("(define (f) (define a 1) (define a 2) a)"), (Duplicate, "a"));
    assert_eq!(error("(+ 1 (define x 2))"), (Definition, "(define x 2)"));
    assert_eq!(error("(define (f) (define x 2))"), (NoExpression, "(define (f) (define x 2))"));
    assert_eq!(error("(set! car 1)"), (Immutable, "car"));
    assert_eq!(error("(set! if 1)"), (BadSyntax, "if"));
    assert_eq!(error("(define-syntax m 1)"), (Transformer, "(define-syntax m 1)"));
    assert_eq!(error("(car #`x)"), (Unsupported, "#`x"));
    assert_eq!(error("(define-syntax my (syntax-rules ::: () ((_ a :::) (list a :::))))"), (Unsupported, ":::"));
    assert_eq!(error("(car '(a #`(b #,c)) #`d)"), (Unsupported, "#`d"));
    assert_eq!(error("(cond (else 1) (#t 2))"), (BadSyntax, "(else 1)"));
    assert_eq!(error("(let ((x)) x)"), (BadSyntax, "(x)"));
    assert_eq!(error("()"), (BadSyntax, "()"));
    assert_eq!(error("(f . x)"), (BadSyntax, "(f . x)"));
    assert_eq!(error("else"), (BadSyntax, "else"));
    let deep = format!("{}1{}", "(car ".repeat(20_000), ")".repeat(20_000));
    assert_eq!(eval_in(&mut arena(), &deep), Ok(Err(Fault::WrongType)));
}

/// Deeply nested source is read, expanded, compiled and run on a small native stack, whatever its depth.
#[test]
fn deep_source_runs_on_a_small_stack() {
    let n = 20_000;
    fn nest(open: &str, inner: &str, depth: usize) -> String {
        format!("{}{inner}{}", open.repeat(depth), ")".repeat(depth))
    }
    let cases = vec![
        (nest("(car ", "1", n), Err(Fault::WrongType)),
        // Each `let` adds a scope to everything inside it, so the scope sets grow with the nesting. The same holds for
        // the `let` forms that a nested `list` pattern expands to.
        (format!("{}x{}", "(let ((x 1)) ".repeat(1000), ")".repeat(1000)), Ok("1".to_string())),
        (format!("(match 1 [{}x{} 2] [_ 3])", "(list ".repeat(1000), ")".repeat(1000)), Ok("3".to_string())),
        (format!("(car '{})", nest("(", "x", n)), Ok(nest("(", "x", n)[1..n * 2].to_string())),
        (format!("`{}", nest("(", ",(+ 1 2)", n)), Ok(nest("(", "3", n))),
        (format!("(match 1 [{} 2] [_ 3])", nest("(not ", "_", n)), Ok("2".to_string())),
        (format!("(match 1 [{} 2] [_ 3])", nest("(and ", "x", n)), Ok("2".to_string())),
    ];
    let small = std::thread::Builder::new().stack_size(1 << 20).spawn(move || {
        let mut arena = arena_of(1 << 28);
        cases.into_iter().map(|(text, want)| (eval_in(&mut arena, &text), want)).find(|(got, want)| got.as_ref() != Ok(want))
    });
    let wrong = small.unwrap().join().unwrap();
    assert!(wrong.is_none(), "{:?}", wrong.map(|(got, _)| got.map(|r| r.map(|s| s.len()))));
}

/// Converting cyclic data to syntax stops instead of running forever. It runs out of fuel if the
/// task has only a little. Otherwise it stops when the syntax built so far fills the arena.
#[test]
fn syntax_of_cyclic_data_stops() {
    let cyclic = "(define v (vector 1)) (vector-set! v 0 v)";
    for op in ["(datum->syntax #f v)", "(syntax->datum (datum->syntax #f (vector v)))"] {
        for (fuel, want) in [(Some(20), Fault::OutOfFuel), (None, Fault::OutOfMemory)] {
            arena().mutate(|mc| {
                let thunks = load_text(mc, &format!("{cyclic} {op}")).unwrap();
                let (&last, before) = thunks.split_last().unwrap();
                for &thunk in before {
                    run(mc, thunk).unwrap();
                }
                let mut machine = Machine::new(mc, MIN_SEGMENT, last, &[]).unwrap();
                if let Some(fuel) = fuel {
                    machine.set_fuel(fuel);
                }
                let stopped = loop {
                    match machine.run(mc) {
                        Ok(Outcome::Paused) => {}
                        other => break other.err(),
                    }
                };
                assert_eq!(stopped, Some(want), "{op}");
            });
        }
    }
}

/// A call of the prelude's `list` with more arguments than the compiler inlines stays a call. It does not become
/// `cons` calls nested as deeply as the list is long.
#[test]
fn long_calls_of_inlined_functions_compile() {
    let nums = (0..1000).map(|i| i.to_string()).collect::<Vec<_>>().join(" ");
    assert_eq!(eval(&format!("(length (list {nums}))")), "1000");
    assert_eq!(eval("(list 1 2 3)"), "(1 2 3)");
}

/// The rest lists of the calls to the prelude's `+` are the only garbage that the loop creates. Binding a rest list
/// pauses the run for the collector when a collection is due, so the loop does not run out of memory.
#[test]
fn rest_lists_let_the_collector_keep_up() {
    let mut arena = arena();
    let mut machine = arena.mutate(|mc| {
        let mut thunks = load_text(mc, "(define (count n) (if (eqv? n 0) 'done (count (+ n -1)))) (count 400000)").unwrap();
        let last = thunks.pop().unwrap();
        thunks.into_iter().for_each(|thunk| _ = run(mc, thunk).unwrap());
        Machine::new(mc, MIN_SEGMENT, last, &[]).unwrap()
    });
    while !arena.step(|mc| matches!(machine.run(mc).unwrap(), Outcome::Done(_))).unwrap() {}
}

#[test]
fn every_literal_the_reader_reads_evaluates_to_itself() {
    assert_eq!(eval("(list (equal? #u8(1 2) #u8(1 2)) (equal? #u8(1 2) #u8(1 3)) (eqv? 1+2i 1+2i) (eqv? #e1.5 3/2))"), "(#t #f #t #t)");
    assert_eq!(eval("(define |odd name| 5) (+ |odd name| 1)"), "6");
    assert_eq!(eval("'(#0=(x) #0# . #0#)"), "((x) (x) x)");
    assert_eq!(eval("#!fold-case (DEFINE (F X) (CONS X X)) (f 'A)"), "(a . a)");
}

#[test]
fn prelude_wraps_the_cxrs_booleans_void_and_bytevectors() {
    assert_eq!(eval("(let ((x '((1 2) (3 4) 5 6))) (list (caar x) (cdar x) (cadr x) (caddr x) (cadddr x) (cddddr x) (caadr x) (cdadr x)))"), "(1 (2) (3 4) 5 6 () 3 (4))");
    assert_eq!(eval("(map (lambda (f) (f '(((a))))) (list caaar caar car))"), "(a (a) ((a)))");
    assert_eq!(eval("(list (boolean? #f) (boolean? #t) (boolean? '()) (void) (void 1 2) (for-each car '()))"), "(#t #t #f #<void> #<void> #<void>)");
    assert_eq!(eval("(let ((b #u8(10 20 30))) (+ (bytevector-u8-ref b 0) (bytevector-u8-ref b 2)))"), "40");
    assert_eq!(eval_in(&mut arena(), "(bytevector-u8-ref #u8(1) 1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(bytevector-u8-set! #u8(1) 0 2)"), Ok(Err(Fault::Immutable)));
    assert_eq!(eval_in(&mut arena(), "(cadr '(1))"), Ok(Err(Fault::WrongType)));
}

#[test]
fn arithmetic() {
    assert_eq!(eval("(list (- 5) (- 10 1 2) (*) (* 2 3 4) (/ 12 3) (/ 2) (/ 1 2 3) (- 1/2 1/2))"), "(-5 7 1 24 4 1/2 1/6 0)");
    assert_eq!(eval("(list (eqv? (/ 2) 1/2) (eqv? (/ 1 2 3) 1/6) (eqv? (/ 7 2) 7/2) (eqv? (* 1.5 2) 3.0) (eqv? (- 0.5 1/2) 0.0))"), "(#t #t #t #t #t)");
    // Results that leave the fixnum range become bignums, and results that return to it become fixnums again.
    assert_eq!(eval("(define big (* 4611686018427387903 4611686018427387903)) (list (eqv? (/ big 4611686018427387903) 4611686018427387903) (- big big))"), "(#t 0)");
    assert_eq!(eval("(list (eqv? (- -4611686018427387904) 4611686018427387904) (eqv? (/ -4611686018427387904 -1) 4611686018427387904))"), "(#t #t)");
    assert_eq!(eval("(eqv? (* 1+2i 1-2i) 5)"), "#t");
    assert_eq!(eval_in(&mut arena(), "(/ 1 0)"), Ok(Err(Fault::Num(ragwort_types::num::NumError::DivideByZero))));
    assert_eq!(eval_in(&mut arena(), "(-)"), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), "(/)"), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), "(* 2 'x)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(- 'x)"), Ok(Err(Fault::WrongType)));
}

#[test]
fn number_predicates() {
    let kinds = "(list (number? 1) (number? 1.5) (number? 1+2i) (number? 'a) (complex? 1/2) (real? 1+2i) (real? 1.5) (rational? 1/2) (rational? 1.5)
                       (rational? +inf.0) (rational? +nan.0) (integer? 2) (integer? 2.0) (integer? 2.5) (integer? 1/2) (integer? \"2\")
                       (exact-integer? 2) (exact-integer? 2.0))";
    assert_eq!(eval(kinds), "(#t #t #t #f #t #f #t #t #t #f #f #t #t #f #f #f #t #f)");
    let exactness = "(list (exact? 1/2) (exact? 0.5) (inexact? 0.5) (inexact? 1.0+2.0i) (nan? +nan.0) (nan? 1) (nan? +nan.0+1i)
                           (infinite? -inf.0) (infinite? +nan.0) (finite? 1.5) (finite? +inf.0) (finite? 1/3) (finite? 1+inf.0i))";
    assert_eq!(eval(exactness), "(#t #f #t #t #t #f #t #t #f #t #f #t #f)");
    let signs = "(list (zero? 0) (zero? 0.0) (zero? -0.0) (zero? 1/2) (zero? +i) (positive? 1/2) (positive? -0.0) (negative? -0.0)
                       (negative? -1.5) (positive? +nan.0) (odd? 3) (odd? -3) (even? 0) (even? 4.0) (odd? (expt 2 100)) (even? (+ 1 (expt 2 100))))";
    assert_eq!(eval(signs), "(#t #t #t #f #f #t #f #f #t #f #t #t #t #t #f #f)");
    let not_integer = Ok(Err(Fault::Num(ragwort_types::num::NumError::NotInteger)));
    assert_eq!(eval_in(&mut arena(), "(odd? 1.5)"), not_integer);
    assert_eq!(eval_in(&mut arena(), "(even? 1/2)"), not_integer);
    for wrong in ["(odd? 'x)", "(zero? 'a)", "(positive? +i)", "(exact? \"1\")", "(nan? '())"] {
        assert_eq!(eval_in(&mut arena(), wrong), Ok(Err(Fault::WrongType)), "{wrong}");
    }
}

#[test]
fn numbers_past_arithmetic() {
    let extremes = "(list (max 1 3 2) (min 1 3 2) (max 1 2.0) (min 1 2.0) (max -1/2 -1/3) (abs -5) (abs -5/2) (abs -2.5)
                          (abs -4611686018427387904))";
    assert_eq!(eval(extremes), "(3 1 2.0 1.0 -1/3 5 5/2 2.5 4611686018427387904)");
    let divisors = "(list (gcd) (gcd 12 18) (gcd -12 18) (gcd 0 5) (lcm) (lcm 4 6) (lcm -4 6) (lcm 0 5) (gcd 12.0 18) (lcm (expt 2 70) 3))";
    assert_eq!(eval(divisors), "(0 6 6 5 1 12 12 0 6.0 3541774862152233910272)");
    assert_eq!(eval("(list (numerator 6/4) (denominator 6/4) (denominator 5) (numerator 0.5) (denominator 0.5))"), "(3 2 1 1.0 2.0)");
    let rounding = "(list (floor 2.5) (ceiling 2.5) (truncate -2.5) (round 2.5) (round 3.5) (round -2.5) (floor -7/2) (ceiling -7/2)
                          (round 7/2) (round 5/2) (floor 3))";
    assert_eq!(eval(rounding), "(2.0 3.0 -2.0 2.0 4.0 -2.0 -4 -3 4 2 3)");
    let division = "(list (call-with-values (lambda () (floor/ -7 2)) list) (call-with-values (lambda () (truncate/ -7 2)) list)
                          (floor-quotient 7 -2) (floor-remainder 7 -2) (truncate-quotient 7 -2) (truncate-remainder 7 -2)
                          (floor-quotient -7.0 2) (floor-quotient (expt 2 70) -3))";
    assert_eq!(eval(division), "((-4 1) (-3 -1) -4 -1 -3 1 -4.0 -393530540239137101142)");
    let roots = "(list (call-with-values (lambda () (exact-integer-sqrt 17)) list) (integer-sqrt (expt 10 40)) (square 5) (square 1/2)
                       (sqrt 16) (sqrt 2.25) (sqrt -4) (sqrt 1/4) (sqrt (expt 3 100)))";
    assert_eq!(eval(roots), "((4 1) 100000000000000000000 25 1/4 4 1.5 +2i 1/2 717897987691852588770249)");
    assert_eq!(eval("(list (exact 2.5) (exact 2.0) (inexact 1/4) (exact->inexact 1/3) (inexact->exact 0.5))"), "(5/2 2 0.25 0.3333333333333333 1/2)");
    let parsed = "(list (string->number \"42\") (string->number \"-1/2\") (string->number \"1e3\") (string->number \"#xff\") (string->number \"ff\" 16)
                        (string->number \"101\" 2) (string->number \"1+2i\") (string->number \"abc\") (string->number \"\") (string->number \"1/0\")
                        (string->number \"#e1.5\") (string->number \"12345678901234567890\") (string->number \"#d10\" 16))";
    assert_eq!(eval(parsed), "(42 -1/2 1000.0 255 255 5 1+2i #f #f #f 3/2 12345678901234567890 10)");
    let complex = "(list (make-rectangular 1 2) (make-rectangular 1.5 0) (real-part 1+2i) (imag-part 1+2i) (imag-part 5) (magnitude -3+4i)
                         (magnitude -5) (angle -1) (angle 1))";
    assert_eq!(eval(complex), "(1+2i 1.5 1 2 0 5 5 3.141592653589793 0)");
    // The last digit of `(exp 1)` is the platform's: FreeBSD's is one off the nearest.
    let transcendental = "(list (exp 0) (log 1) (sin 0.0) (cos 0.0) (atan 1 1) (atan 0 1) (< (abs (- (exp 1) 2.718281828459045)) 1e-15) (log 100 10))";
    assert_eq!(eval(transcendental), "(1 0 0.0 1.0 0.7853981633974483 0 #t 2.0)");
    assert_eq!(eval_in(&mut arena(), "(max)"), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), "(log 1 2 3)"), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), "(integer-sqrt -1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(string->number \"1\" 3)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(floor-quotient 1 0)"), Ok(Err(Fault::Num(ragwort_types::num::NumError::DivideByZero))));
    for wrong in ["(max 1 'a)", "(abs +i)", "(gcd 1 'a)", "(floor \"1\")", "(string->number 'a)", "(make-rectangular 1 +i)", "(integer-sqrt 4.0)"] {
        assert_eq!(eval_in(&mut arena(), wrong), Ok(Err(Fault::WrongType)), "{wrong}");
    }
}

#[test]
fn structs() {
    let point = "(struct point (x y))";
    let made = format!("{point} (define p (point 1 2)) (list (point? p) (point? 5) (point-x p) (point-y p) p struct:point)");
    assert_eq!(eval(&made), "(#t #f 1 2 #(struct:point 1 2) #<struct-type:point>)");
    assert_eq!(eval(&format!("{point} (list (equal? (point 1 '(2)) (point 1 '(2))) (eq? (point 1 2) (point 1 2)) (equal? (point 1 2) (point 1 3)))")), "(#t #f #f)");
    // The procedures of a struct are also values. A call with the wrong number of arguments still calls the procedure, which reports the arity error.
    assert_eq!(eval(&format!("{point} (list (map point-x (list (point 1 2) (point 3 4))) (apply point '(5 6)) (procedure? point?))")), "((1 3) #(struct:point 5 6) #t)");
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point 1)")), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x 1 2)")), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x 5)")), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x (vector 1 2))")), Ok(Err(Fault::WrongType)));
    // Code before the `struct` form can call the form's procedures after the form has run. A use before the form has run
    // faults as an unbound variable.
    assert_eq!(eval(&format!("(define (norm p) (+ (point-x p) (point-y p))) {point} (norm (point 3 4))")), "7");
    for early in ["(point 1 2)", "(point-x 5)", "(point? 5)", "point", "struct:point"] {
        assert_eq!(eval_in(&mut arena(), &format!("(define (f) {early}) (define early (f)) {point}")), Ok(Err(Fault::Unbound)), "{early}");
    }
    assert_eq!(eval_in(&mut arena(), &format!("(point 1 2) {point}")), Ok(Err(Fault::Unbound)));
    assert_eq!(eval_in(&mut arena(), "(define (f) (set-cell-v! 1 2)) (define early (f)) (struct cell ([v #:mutable]))"), Ok(Err(Fault::Unbound)));
    assert_eq!(eval("(struct unit ()) (list (unit) (unit? (unit)) (equal? (unit) (unit)))"), "(#(struct:unit) #t #t)");

    let mutable = "(struct counter (n) #:mutable) (define c (counter 0)) (set-counter-n! c 5) (list (counter-n c) c)";
    assert_eq!(eval(mutable), "(5 #(struct:counter 5))");
    let one = "(struct account (id [balance #:mutable]) #:transparent) (define a (account 1 10)) (set-account-balance! a 20) (account-balance a)";
    assert_eq!(eval(one), "20");
    assert_eq!(error("(struct account (id [balance #:mutable])) (set-account-id! 1 2)"), (ExpandErrorKind::Unbound, "set-account-id!"));
    let named = "(struct pt (x) #:constructor-name make-pt #:extra-constructor-name new-pt) (list (pt-x (make-pt 1)) (new-pt 2) (pt 3))";
    assert_eq!(eval(named), "(1 #(struct:pt 2) #(struct:pt 3))");

    let sub = format!("{point} (struct point3 point (z)) (struct point4 point3 ([w #:mutable])) (define q (point4 1 2 3 4)) (set-point4-w! q 40)
                       (list q (point-x q) (point3-z q) (point4-w q) (point? q) (point3? q) (point4? (point3 1 2 3)) (point3? (point 1 2)) (equal? (point3 1 2 3) (point3 1 2 3)))");
    assert_eq!(eval(&sub), "(#(struct:point4 1 2 3 40) 1 3 40 #t #t #f #f #t)");
    assert_eq!(eval_in(&mut arena(), &format!("{point} (struct point3 point (z)) (point3-z (point 1 2))")), Ok(Err(Fault::WrongType)));

    for (bad, at) in [
        ("(struct point)", "(struct point)"),
        ("(struct (point) (x))", "(struct (point) (x))"),
        ("(struct point (x 1))", "1"),
        ("(struct point ([x #:auto]))", "[x #:auto]"),
        ("(struct point (x) #:prefab)", "#:prefab"),
        ("(struct point (x) #:constructor-name)", "#:constructor-name"),
        ("(struct point nope (x))", "nope"),
        ("(define car2 car) (struct point car2 (x))", "car2"),
        ("(struct point (x) #:identity-eq? #t)", "#t"),
    ] {
        assert_eq!(error(bad), (ExpandErrorKind::BadSyntax, at), "{bad}");
    }
    assert_eq!(error("(struct point (x x))"), (ExpandErrorKind::Duplicate, "x"));
    assert_eq!(error("(struct point (x)) (define point? 1)").0, ExpandErrorKind::Duplicate);
    assert_eq!(error("(struct point (x)) (set! point-x car)"), (ExpandErrorKind::Immutable, "point-x"));
    assert_eq!(error("(struct point (x)) (set! struct:point 1)"), (ExpandErrorKind::Immutable, "struct:point"));
}

#[test]
fn structs_equal_only_to_themselves() {
    let session = "(struct session (token [uses #:mutable]) #:identity-eq?)";
    let made = format!("{session} (define s (session \"tok\" 0)) (set-session-uses! s 3)
                        (list s (session? s) (session-token s) (session-uses s) (equal? s s) (equal? s (session \"tok\" 3)) (eqv? s s)
                              (equal? (list s) (list s)) (equal? (list s) (list (session \"tok\" 3))))");
    assert_eq!(eval(&made), r#"(#(struct:session "tok" 3) #t "tok" 3 #t #f #t #t #f)"#);
    // A subtype of an `#:identity-eq?` type is also `#:identity-eq?`. A subtype of an ordinary type can be declared `#:identity-eq?`.
    let sub = format!("{session} (struct admin session (level)) (struct point (x)) (struct pinned point (y) #:identity-eq?)
                       (list (equal? (admin 1 2 3) (admin 1 2 3)) (equal? (point 1) (point 1)) (equal? (pinned 1 2) (pinned 1 2))
                             (let ((p (pinned 1 2))) (equal? p p)) (member (point 1) (list (point 2) (point 1))) (member (session 1 2) (list (session 1 2))))");
    assert_eq!(eval(&sub), "(#f #t #f #t (#(struct:point 1)) #f)");
    assert_eq!(eval("(struct cell (v) #:identity-eq?) (define (f) (define c (cell 7)) (list c (cell-v c) (equal? c (cell 7)) (equal? c c))) (f)"), "(#(struct:cell 7) 7 #f #t)");
    // An `#:identity-eq?` struct is matched and copied like any other struct.
    assert_eq!(eval(&format!("{session} (match (session 1 2) [(session t u) (list t u)])")), "(1 2)");
    assert_eq!(eval(&format!("{session} (define s (session 1 2)) (list (struct-copy session s [uses 9]) (equal? s (struct-copy session s)))")), "(#(struct:session 1 9) #f)");
}

#[test]
fn struct_parts_are_the_forms_alone() {
    let account = "(struct account (id [balance #:mutable] owner))";
    // A macro cannot name `struct-ref`, the field read that `match` and `struct-copy` expand to. That holds even for an identifier with the scopes
    // of syntax that a built-in macro introduced. Such an identifier does reach the prelude's `car`.
    fn borrowed(account: &str, name: &str, args: &str) -> String {
        format!("{account} (define a (account 1 2 \"al\"))
                 (define-syntax borrow (lambda (stx) (syntax-case stx () [(_ t) (with-syntax ([f (datum->syntax #'t '{name})]) #'(f {args}))])))
                 (cond [1 => borrow])")
    }
    assert_eq!(eval(&borrowed(account, "car", "'(1 2)")), "1");
    assert_eq!(error(&borrowed(account, "struct-ref", "a struct:account 0")).0, ExpandErrorKind::Unbound);
    // Only the procedures that a `struct` form defines can create a struct, or read or set a field of one.
    for name in ["make-struct-type", "make-struct", "struct-ref", "struct-field", "struct-set!"] {
        assert_eq!(error(&format!("{account} ({name} struct:account 1 2 3)")), (ExpandErrorKind::Unbound, name), "{name}");
    }
    // A struct has no guard: a procedure that checks what it's given makes one.
    let checked = format!("{account} (define (make-account id balance owner) (if (>= balance 0) (account id balance owner) (error \"negative balance:\" balance)))
                           (list (make-account 1 5 \"al\") (guard (e (#t (error-object-irritants e))) (make-account 1 -5 \"al\")))");
    assert_eq!(eval(&checked), r#"(#(struct:account 1 5 "al") (-5))"#);
    for (bad, at) in [
        ("(struct p (x) #:guard number?)", "#:guard"),
        ("(struct p ([x #:guard number?]))", "[x #:guard number?]"),
        ("(struct p ([x #:nope]))", "[x #:nope]"),
    ] {
        assert_eq!(error(bad), (ExpandErrorKind::BadSyntax, at), "{bad}");
    }
    // The variables that a `struct` form defines cannot be assigned.
    assert_eq!(error("(struct p (x)) (set! p car)"), (ExpandErrorKind::Immutable, "p"));
    assert_eq!(error("(struct p ([x #:mutable])) (define (f) (set! set-p-x! car) 1)"), (ExpandErrorKind::Immutable, "set-p-x!"));
}

#[test]
fn sealed_structs_have_no_subtypes() {
    let sealed = "(struct leaf (v) #:sealed) (struct node (l r)) (struct last node (x) #:sealed) (list (leaf 1) (last 1 2 3) (node? (last 1 2 3)))";
    assert_eq!(eval(sealed), "(#(struct:leaf 1) #(struct:last 1 2 3) #t)");
    assert_eq!(error("(struct leaf (v) #:sealed) (struct more leaf (w))"), (ExpandErrorKind::BadSyntax, "leaf"));
    assert_eq!(error("(begin (struct leaf (v) #:sealed) (struct more leaf (w)))"), (ExpandErrorKind::BadSyntax, "leaf"));
    assert_eq!(error("(struct leaf (v) #:sealed #:what)"), (ExpandErrorKind::BadSyntax, "#:what"));
}

#[test]
fn structs_go_at_the_top_level() {
    assert_eq!(eval("(begin (struct point (x y)) (define p (point 1 2))) (point-y p)"), "2");
    assert_eq!(eval("(define-syntax pair-struct (syntax-rules () [(_ name) (struct name (a b))])) (pair-struct two) (two-b (two 1 2))"), "2");
    for body in ["(define (f) (struct p (x)) 1)", "(let () (struct p (x)) 1)", "(lambda () (struct p (x)) (p 1))", "(define (f) (begin (struct p (x))) 1)"] {
        assert_eq!(error(body), (ExpandErrorKind::Definition, "(struct p (x))"), "{body}");
    }
    assert_eq!(error("(if 1 (struct point (x)) 2)"), (ExpandErrorKind::Definition, "(struct point (x))"));
}

#[test]
fn structs_are_matched_and_copied() {
    let shapes = "(struct point (x y)) (struct point3 point (z)) (struct circle (center r)) (struct secret (v) #:identity-eq?)";
    let area = format!("{shapes}
        (define (describe v)
          (match v
            [(point3 x y z) (list 'point3 x y z)]
            [(point 0 0) 'origin]
            [(point x y) (list 'point x y)]
            [(circle (point x _) r) (list 'circle x r)]
            [(secret v) (list 'secret v)]
            [_ 'other]))
        (map describe (list (point 0 0) (point 1 2) (point3 1 2 3) (circle (point 5 6) 7) (secret 8) (circle 1 2) 9))");
    assert_eq!(eval(&area), "(origin (point 1 2) (point3 1 2 3) (circle 5 7) (secret 8) other other)");
    // A subtype's struct matches its supertype's pattern, by the supertype's fields.
    assert_eq!(eval(&format!("{shapes} (match (point3 1 2 3) [(point x y) (list x y)])")), "(1 2)");
    assert_eq!(error(&format!("{shapes} (match 1 [(point x) x])")), (ExpandErrorKind::BadSyntax, "(point x)"));
    assert_eq!(error("(match 1 [(nope x) x])"), (ExpandErrorKind::BadSyntax, "(nope x)"));

    // A pattern followed by `...` is matched against each field the others leave.
    let row = "(struct row (a b c d e)) (define r (row 1 2 3 4 5))";
    let rest = [
        ("(match r [(row a _ ...) a])", "1"),
        ("(match r [(row a rest ...) (list a rest)])", "(1 (2 3 4 5))"),
        ("(match r [(row a mid ... e) (list a mid e)])", "(1 (2 3 4) 5)"),
        ("(match r [(row all ...) all])", "(1 2 3 4 5)"),
        ("(match r [(row a b c d e none ...) (list a none)])", "(1 ())"),
        ("(match r [(row _ ... d e) (list d e)])", "(4 5)"),
        ("(match r [(row (? string? x) ... e) 'strings] [(row (? number? x) ... e) (list x e)])", "((1 2 3 4) 5)"),
        ("(match (row 1 '(2 a) '(3 b) '(4 c) 5) [(row _ (list n tag) ... last) (list n tag last)])", "((2 3 4) (a b c) 5)"),
        ("(match (point3 1 2 3) [(point x ...) x])", "(1 2)"),
        ("(match (circle (point 1 2) 3) [(circle (point c ...) _ ...) c])", "(1 2)"),
        ("(match 5 [(row a _ ...) a] [_ 'not-a-row])", "not-a-row"),
        ("(match (point 1 2) [(point x y z ...) (list x y z)])", "(1 2 ())"),
    ];
    for (text, expected) in rest {
        assert_eq!(eval_in(&mut arena(), &format!("{shapes} {row} {text}")).map_err(|_| text), Ok(Ok(expected.to_string())), "{text}");
    }
    for (wrong, kind, at) in [
        ("(point ... x)", ExpandErrorKind::BadSyntax, "..."),
        ("(point x ... y ...)", ExpandErrorKind::BadSyntax, "..."),
        ("(point x y z w ...)", ExpandErrorKind::BadSyntax, "(point x y z w ...)"),
        ("(point x x ...)", ExpandErrorKind::Duplicate, "x"),
    ] {
        assert_eq!(error(&format!("{shapes} (match (point 1 2) [{wrong} 1])")), (kind, at), "{wrong}");
    }

    let copied = format!("{shapes} (define p (point3 1 2 3))
        (list (struct-copy point3 p [z 30]) (struct-copy point3 p [x 10] [z 30] [y 20]) (struct-copy point p [y 5]) (struct-copy point3 p) p
              (secret-v (struct-copy secret (secret 1) [v 2])))");
    assert_eq!(eval(&copied), "(#(struct:point3 1 2 30) #(struct:point3 10 20 30) #(struct:point 1 5) #(struct:point3 1 2 3) #(struct:point3 1 2 3) 2)");
    // The struct expression is evaluated first. The field values are then evaluated in the order they are written.
    let order = "(struct p (a b)) (define log '()) (define (note x) (set! log (cons x log)) x)
                 (struct-copy p (note (p 1 2)) [b (note 'b)] [a (note 'a)]) (reverse log)";
    assert_eq!(eval(order), "(#(struct:p 1 2) b a)");
    for wrong in ["(struct-copy point (point3 1 2 3) [x 1] [y 2])", "(struct-copy point3 (point 1 2) [z 1])", "(struct-copy point 5 [x 1] [y 2])", "(struct-copy point 5)"] {
        let expected = if wrong.contains("(point3 1 2 3)") { Ok(Ok("#(struct:point 1 2)".to_string())) } else { Ok(Err(Fault::WrongType)) };
        assert_eq!(eval_in(&mut arena(), &format!("{shapes} {wrong}")), expected, "{wrong}");
    }
    assert_eq!(error(&format!("{shapes} (struct-copy point (point 1 2) [z 1])")), (ExpandErrorKind::BadSyntax, "z"));
    assert_eq!(error(&format!("{shapes} (struct-copy point (point 1 2) [x 1] [x 2])")).0, ExpandErrorKind::Duplicate);
    assert_eq!(error(&format!("{shapes} (struct-copy car (point 1 2))")), (ExpandErrorKind::BadSyntax, "car"));
}

#[test]
fn structs_as_wholes() {
    let shapes = "(struct point (x y)) (struct point3 point (z)) (struct session (token user) #:identity-eq?)";
    let fields = format!("{shapes} (list (struct-fields struct:point) (struct-fields struct:point3) (struct-fields struct:session))");
    assert_eq!(eval(&fields), "((x y) (x y z) (token user))");
    let derived = format!("{shapes} (define q (point3 1 2 3)) (define s (session 'tok 'al))
        (list (struct-derived-from? q struct:point) (struct-derived-from? (point 1 2) struct:point3) (struct-derived-from? s struct:session) (struct-derived-from? q struct:session))");
    assert_eq!(eval(&derived), "(#t #f #t #f)");
    let any = format!("{shapes} (list (struct? (point 1 2)) (struct? (point3 1 2 3)) (struct? (session 1 2)) (struct? struct:point) (struct? 5) (struct? (vector 1)) (struct? point)
                                  (map struct? (list (point 1 2) 'a)))");
    assert_eq!(eval(&any), "(#t #t #t #f #f #f #f (#t #f))");
    let types = format!("{shapes} (list (struct-type? struct:point) (struct-type? struct:point3) (struct-type? (point 1 2)) (struct-type? point) (struct-type? 'point))");
    assert_eq!(eval(&types), "(#t #t #f #f #f)");
    // `struct-type` returns the type that an instance was created as. `struct->list` returns the values of its fields, in the order
    // of `struct-fields` for that type.
    let whole = format!("{shapes} (struct unit ()) (define q (point3 1 2 3))
        (list (eq? (struct-type q) struct:point3) (eq? (struct-type q) struct:point) (struct-type (point 1 2)) (struct->list q) (struct->list (session 'tok 'al))
              (struct-fields (struct-type q)) (struct->list (unit)) (map struct->list (list (point 1 2))))");
    assert_eq!(eval(&whole), "(#t #f #<struct-type:point> (1 2 3) (tok al) (x y z) () ((1 2)))");
    // Each call of `struct->list` returns a new list, with the values that the fields have at the time of the call.
    let cells = "(struct cell (label [value #:mutable])) (struct cell3 cell (extra) #:mutable)";
    let listed = format!("{cells} (define c (cell 'a 1)) (define before (struct->list c)) (set-cell-value! c 2) (list before (struct->list c) (eq? (struct->list c) (struct->list c)))");
    assert_eq!(eval(&listed), "((a 1) (a 2) #f)");
    let mutable = format!("{cells} (list (struct-field-mutable? struct:cell 0) (struct-field-mutable? struct:cell 1) (struct-field-mutable? struct:cell3 0)
                                      (struct-field-mutable? struct:cell3 1) (struct-field-mutable? struct:cell3 2))");
    assert_eq!(eval(&mutable), "(#f #t #f #t #t)");
    // Code that does not know the type of a struct can still list its fields by name.
    let by_name = format!("{shapes}
        (define (struct->alist s) (map cons (struct-fields (struct-type s)) (struct->list s)))
        (list (struct->alist (point3 1 2 3)) (struct->alist (session 'tok 'al)))");
    assert_eq!(eval(&by_name), "(((x . 1) (y . 2) (z . 3)) ((token . tok) (user . al)))");
    assert_eq!(eval("(struct cell (a b)) (define (f) (list (struct-fields struct:cell) (struct->list (cell 1 2)) (eq? (struct-type (cell 1 2)) struct:cell))) (f)"), "((a b) (1 2) #t)");
    for (wrong, fault) in [
        ("(struct-fields 5)", Fault::WrongType),
        ("(struct-field-mutable? struct:point 2)", Fault::OutOfRange),
        ("(struct-field-mutable? (point 1 2) 0)", Fault::WrongType),
        ("(struct-type 5)", Fault::WrongType),
        ("(struct-type struct:point)", Fault::WrongType),
        ("(struct->list 5)", Fault::WrongType),
        ("(struct->list struct:point)", Fault::WrongType),
        ("(struct-derived-from? 1 2)", Fault::WrongType),
    ] {
        assert_eq!(eval_in(&mut arena(), &format!("{shapes} {wrong}")), Ok(Err(fault)), "{wrong}");
    }
}

#[test]
fn characters() {
    let kinds = "(list (char-alphabetic? #\\a) (char-alphabetic? #\\λ) (char-alphabetic? #\\1) (char-numeric? #\\7) (char-numeric? #\\٣)
                       (char-numeric? #\\a) (char-numeric? #\\½) (char-whitespace? #\\space) (char-whitespace? #\\x3000) (char-whitespace? #\\a)
                       (char-upper-case? #\\A) (char-upper-case? #\\a) (char-lower-case? #\\ß) (char-lower-case? #\\1))";
    assert_eq!(eval(kinds), "(#t #t #f #t #t #f #f #t #t #f #t #f #t #f)");
    assert_eq!(eval("(list (digit-value #\\7) (digit-value #\\٣) (digit-value #\\x1E5F9) (digit-value #\\a) (digit-value #\\½))"), "(7 3 8 #f #f)");
    // A character whose case mapping is more than one character is left unchanged.
    let cases = "(string (char-upcase #\\a) (char-upcase #\\ß) (char-downcase #\\Σ) (char-foldcase #\\Σ) (char-foldcase #\\ı) (char-upcase #\\1))";
    assert_eq!(eval(cases), "\"Aßσσı1\"");
    assert_eq!(eval("(list (char-ci=? #\\a #\\A #\\a) (char-ci<? #\\a #\\B #\\c) (char-ci=? #\\a #\\b) (char-ci>=? #\\Z #\\a))"), "(#t #t #f #t)");
    assert_eq!(eval_in(&mut arena(), "(char-upcase \"a\")"), Ok(Err(Fault::WrongType)));
}

#[test]
fn strings_past_the_basics() {
    let made = "(list (make-string 3 #\\x) (make-string 2) (string #\\a #\\b) (list->string '(#\\h #\\i)) (string) (string-upcase \"straße\")
                      (string-downcase \"ÀB\") (string-foldcase \"Straße\"))";
    assert_eq!(eval(made), r#"("xxx" "  " "ab" "hi" "" "STRASSE" "àb" "strasse")"#);
    assert_eq!(eval("(list (string-ci=? \"Straße\" \"STRASSE\") (string-ci<? \"apple\" \"Banana\") (string-ci=? \"a\" \"b\"))"), "(#t #t #f)");
    let vectors = "(list (string->vector \"abc\") (string->vector \"abcd\" 1 3) (vector->string #(#\\a #\\b #\\c)) (vector->string #(#\\a #\\b #\\c) 1))";
    assert_eq!(eval(vectors), r#"(#(#\a #\b #\c) #(#\b #\c) "abc" "bc")"#);
    let utf8 = "(list (string->utf8 \"aé\") (utf8->string #u8(104 105)) (utf8->string (string->utf8 \"λx\")) (string->utf8 \"abc\" 1))";
    assert_eq!(eval(utf8), r#"(#u8(97 195 169) "hi" "λx" #u8(98 99))"#);
    let mapped = "(list (string-map char-upcase \"abc\") (string-map (lambda (a b) (if (char<? a b) a b)) \"adc\" \"bbbb\")
                        (let ((n 0)) (string-for-each (lambda (c) (set! n (+ n 1))) \"hello\") n))";
    assert_eq!(eval(mapped), r#"("ABC" "abb" 5)"#);
    let found = "(list (string-prefix? \"hello\" \"he\") (string-prefix? \"he\" \"hello\") (string-suffix? \"hello\" \"lo\") (string-contains? \"hello\" \"ell\")
                       (string-contains? \"hello\" \"\") (string-contains? \"hello\" \"z\"))";
    assert_eq!(eval(found), "(#t #f #t #t #t #f)");
    let places = "(list (string-find \"hello\" \"l\") (string-find \"hello\" \"l\" 3) (string-find \"hello\" \"l\" 4) (string-find \"hello\" \"\")
                        (string-find-last \"hello\" \"l\") (string-find-last \"hello\" \"l\" 3) (string-find-last \"hello\" \"z\") (string-find \"λxλ\" \"λ\" 1))";
    assert_eq!(eval(places), "(2 3 #f 0 3 2 #f 2)");
    assert_eq!(eval_in(&mut arena(), "(string-find \"abc\" \"a\" 9)"), Ok(Err(Fault::Str(ragwort_types::string::StrError::OutOfRange))));
    let split = "(list (string-split \"  a b  c \") (string-split \"\") (string-split \"a,b,,c\" \",\") (string-split \",a,\" \",\")
                       (string-split \"a,,b\" \",\" #:repeat? #t) (string-split \" a b \" #:trim? #f) (string-split \",a,\" \",\" #:trim? #f) (string-split \"a\" \",\"))";
    assert_eq!(eval(split), r#"(("a" "b" "c") () ("a" "b" "" "c") ("a") ("a" "b") ("" "a" "b" "") ("" "a" "") ("a"))"#);
    let trimmed = "(list (string-trim \"  hi  \") (string-trim \"  hi  \" #:left? #f) (string-trim \"  hi  \" #:right? #f) (string-trim \"--hi--\" \"-\")
                         (string-trim \"--hi--\" \"-\" #:repeat? #t) (string-trim \"aaa\" \"a\" #:repeat? #t))";
    assert_eq!(eval(trimmed), r#"("hi" "  hi" "hi  " "-hi-" "hi" "")"#);
    let replaced = "(list (string-replace \"a-b-c\" \"-\" \"+\") (string-replace \"a-b-c\" \"-\" \"+\" #:all? #f) (string-replace \"abc\" \"\" \"-\")
                          (string-replace \"abc\" \"x\" \"y\") (string-replace \"aaa\" \"aa\" \"b\"))";
    assert_eq!(eval(replaced), r#"("a+b+c" "a+b-c" "-a-b-c-" "abc" "ba")"#);
    assert_eq!(eval_in(&mut arena(), "(string->vector \"abc\" 2 1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(make-string -1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(utf8->string #u8(104 255))"), Ok(Err(Fault::Str(ragwort_types::string::StrError::NotUtf8))));
    assert_eq!(eval_in(&mut arena(), "(string-trim \"a\" #:bogus 1)"), Ok(Err(Fault::Keyword)));
    for wrong in ["(list->string '(1))", "(string-split \"a\" 'x)", "(string-upcase 1)", "(vector->string #(1))", "(string-prefix? \"a\" 1)"] {
        assert_eq!(eval_in(&mut arena(), wrong), Ok(Err(Fault::WrongType)), "{wrong}");
    }
}

#[test]
fn mutable_bytevectors() {
    let fill = "(let ((b (make-bytevector 10 7)))
                  (bytevector-u8-set! b 9 200)
                  (list (bytevector? b) (bytevector-length b) (bytevector-u8-ref b 0) (bytevector-u8-ref b 9)))";
    assert_eq!(eval(fill), "(#t 10 7 200)");
    assert_eq!(eval("(let ((b (make-bytevector 3))) (list (bytevector-u8-ref b 2) (equal? b #u8(0 0 0)) (bytevector-length #u8())))"), "(0 #t 0)");
    assert_eq!(eval("(list (bytevector? #u8()) (bytevector? '(1)) (bytevector? \"s\"))"), "(#t #f #f)");
    assert_eq!(eval_in(&mut arena(), "(make-bytevector -1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(make-bytevector 2 256)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(make-bytevector 2 0 0)"), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), "(bytevector-length '())"), Ok(Err(Fault::WrongType)));
}

#[test]
fn mutable_vectors() {
    let fill = "(let ((v (make-vector 3 'a)))
                  (vector-set! v 1 'b)
                  (list (vector? v) (vector-length v) (vector-ref v 0) (vector-ref v 1) (vector->list v)))";
    assert_eq!(eval(fill), "(#t 3 a b (a b a))");
    assert_eq!(eval("(vector->list (make-vector 2))"), "(0 0)");
    assert_eq!(eval("(let ((v (vector 1 'x \"s\"))) (vector-set! v 0 v) (list (eq? (vector-ref v 0) v) (vector-ref v 1)))"), "(#t x)");
    assert_eq!(eval("(list (vector->list (vector)) (vector-length #()) (vector-ref #(1 #(2)) 0) (vector->list (list->vector '(1 2 3))))"), "(() 0 1 (1 2 3))");
    assert_eq!(eval("(list (vector? #(1)) (vector? (vector)) (vector? '(1)) (vector? #u8(1)) (equal? (vector 1 2) #(1 2)))"), "(#t #t #f #f #t)");
    assert_eq!(eval_in(&mut arena(), "(vector-set! #(1 2) 0 3)"), Ok(Err(Fault::Immutable)));
    assert_eq!(eval_in(&mut arena(), "(vector-ref (vector 1) 1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(vector-set! (vector 1) -1 0)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(vector-ref '(1) 0)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(list->vector '(1 . 2))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(make-vector -1)"), Ok(Err(Fault::OutOfRange)));
    assert_eq!(eval_in(&mut arena(), "(make-vector 1 0 0)"), Ok(Err(Fault::Arity)));
}

#[test]
fn procedure_and_continuation_predicates() {
    assert_eq!(
        eval("(list (procedure? (lambda (x) x))
                    (procedure? car)
                    (procedure? +)
                    (procedure? call/cc)
                    (procedure? procedure?)
                    (procedure? continuation?)
                    (procedure? 42)
                    (procedure? '())
                    (procedure? #t)
                    (procedure? '(1 . 2)))"),
        "(#t #t #t #t #t #t #f #f #f #f)"
    );
    assert_eq!(
        eval("(list (continuation? (lambda (x) x))
                    (continuation? car)
                    (continuation? +)
                    (continuation? 42)
                    (continuation? '()))"),
        "(#f #f #f #f #f)"
    );
    // Both kinds of continuation are `Continuation` objects, `continuation?` and `procedure?`.
    assert_eq!(
        eval("(call-with-composable-continuation (lambda (k) (list (procedure? k) (continuation? k))))"),
        "(#t #t)"
    );
    assert_eq!(eval("(call/cc (lambda (k) (list (procedure? k) (continuation? k))))"), "(#t #t)");
    // Dominating `continuation?` / `procedure?` branch facts in `cp0`.
    let classify = "
        (define (classify x)
          (if (continuation? x)
              (list 'cont (procedure? x) (if x 'truthy 'falsy) (pair? x))
              (if (procedure? x)
                  (list 'proc (continuation? x) (if x 'truthy 'falsy) (null? x))
                  (list 'other (continuation? x) (procedure? x)))))
        (list (call-with-composable-continuation classify)
              (classify (lambda () 1))
              (classify 99))
    ";
    assert_eq!(eval(classify), "((cont #t truthy #f) (proc #f truthy #f) (other #f #f))");
}

#[test]
fn compiler_micropass_stress_cases() {
    // 1. Contified loop where the loop parameter `f` is replaced each iteration by a new closure
    //    capturing both the old `f` and `n` (tests `NewClosure` destination vs. capture register hazard).
    let wrap_loop = "
        (let loop ((f (lambda (x) x)) (n 5))
          (if (eqv? n 0)
              (f 10)
              (loop (lambda (x) (f (+ x n))) (- n 1))))
    ";
    assert_eq!(eval(wrap_loop), "25");

    // 2. Contified loop collecting closures that capture per-iteration immutable and `set!`-mutated
    //    loop variables, verifying each closure gets its own iteration's binding/box.
    let per_iter_closures = "
        (let ()
          (define immut-fns
            (let loop ((i 0) (acc '()))
              (if (eqv? i 4)
                  (reverse acc)
                  (loop (+ i 1) (cons (lambda () i) acc)))))
          (define mut-fns
            (let loop ((i 1) (acc '()))
              (if (eqv? i 5)
                  (reverse acc)
                  (let ((next (+ i 1)))
                    (set! i (* i 10))
                    (loop next (cons (lambda () i) acc))))))
          (list (map (lambda (f) (f)) immut-fns)
                (map (lambda (f) (f)) mut-fns)))
    ";
    assert_eq!(eval(per_iter_closures), "((0 1 2 3) (10 20 30 40))");

    // 3. Nested contified loops: outer loop recurring with the result of an inner contified loop,
    //    plus a 3-deep nested loop computing a triangular sum.
    let nested_loops = "
        (let outer ((i 6) (total 0))
          (if (eqv? i 0)
              total
              (outer (- i 1)
                     (let mid ((j i) (acc total))
                       (if (eqv? j 0)
                           acc
                           (mid (- j 1)
                                (let inner ((k j) (s acc))
                                  (if (eqv? k 0)
                                      s
                                      (inner (- k 1) (+ s k))))))))))
    ";
    assert_eq!(eval(nested_loops), "126");

    // 4. Multi-parameter permutation/rotation in a contified loop (tests parallel-move cycle breaking
    //    in a jump back to a join).
    let permute_loop = "
        (let loop ((a 1) (b 2) (c 3) (d 4) (n 5))
          (if (eqv? n 0)
              (list a b c d)
              (loop b c d (+ a (* b 2) (* c 3) (* d 4)) (- n 1))))
    ";
    assert_eq!(eval(permute_loop), "(140 661 3128 14805)");

    // 5. Complex `letrec*` with mixed pure values, side-effecting initializers, non-recursive
    //    helpers, single-recursive `SelfClosure` functions (returning closures that capture
    //    `SelfClosure`), contified loops, and mutually recursive `Fix` groups.
    let complex_letrec = "
        (let ()
          (define log '())
          (define (record! tag val)
            (set! log (cons (cons tag val) log))
            val)
          (define base (record! 'base 10))
          (define (scale x) (* x base))
          (define bumped (record! 'bumped (scale 3)))
          (define (stream n)
            (cons (+ n base) (lambda () (stream (- n 1)))))
          (define (take-stream s k)
            (if (eqv? k 0)
                '()
                (cons (car s) (take-stream ((cdr s)) (- k 1)))))
          (define (even-sum n acc)
            (if (eqv? n 0) acc (odd-sum (- n 1) (+ acc n))))
          (define (odd-sum n acc)
            (if (eqv? n 0) acc (even-sum (- n 1) (+ acc (* n 2)))))
          (list (take-stream (stream 3) 4)
                bumped
                (even-sum 6 0)
                (reverse log)))
    ";
    assert_eq!(eval(complex_letrec), "((13 12 11 10) 30 30 ((base . 10) (bumped . 30)))");

    // 6. Deep `cxr` store-to-load forwarding on impure `cons` / `list` chains preserves exact
    //    left-to-right side-effect ordering while eliminating intermediate pair allocations.
    let cxr_effects = "
        (let ((trace '()))
          (define (step! x)
            (set! trace (cons x trace))
            (* x 10))
          (let ((picked (cadddr (list (step! 1) (step! 2) (step! 3) (step! 4) (step! 5)))))
            (list picked (reverse trace))))
    ";
    assert_eq!(eval(cxr_effects), "(40 (1 2 3 4 5))");

    // 7. The list-length loop (fused `null?` branch, in-place `cdr` and `+`), on short and long lists.
    let length_loop = "
        (define (len-of list)
          (let loop ((xs list) (len 0))
            (if (null? xs)
                len
                (loop (cdr xs) (+ len 1)))))
        (define (iota n)
          (let loop ((i n) (acc '()))
            (if (eqv? i 0) acc (loop (- i 1) (cons i acc)))))
        (list (len-of '()) (len-of '(a)) (len-of '(a b c)) (len-of (iota 100000)))
    ";
    assert_eq!(eval(length_loop), "(0 1 3 100000)");
    // A non-list still faults where `cdr` reaches the improper tail.
    assert_eq!(
        eval_in(&mut arena(), "(let loop ((xs '(1 2 . 3)) (len 0)) (if (null? xs) len (loop (cdr xs) (+ len 1))))"),
        Ok(Err(Fault::WrongType))
    );

    // 8. `add1`/`sub1`, and the `(+ x 1)` / `(- x 1)` they're rewritten from, across the numeric
    //    tower: past the fixnum edge, on flonums and ratios, and faulting on non-numbers.
    assert_eq!(eval("(list (add1 41) (sub1 43) (add1 -1) (sub1 0) (map add1 '(1 2 3)) (map sub1 '(1 2 3)))"), "(42 42 0 -1 (2 3 4) (0 1 2))");
    assert_eq!(
        eval("(define (inc x) (+ x 1)) (define (dec x) (- x 1))
              (list (eqv? (inc 4611686018427387903) 4611686018427387904)
                    (eqv? (dec -4611686018427387904) -4611686018427387905)
                    (eqv? (dec (inc 4611686018427387903)) 4611686018427387903)
                    (eqv? (inc 1.5) 2.5) (eqv? (dec 1/2) -1/2)
                    (eqv? (add1 4611686018427387903) (inc 4611686018427387903)))"),
        "(#t #t #t #t #t #t)"
    );
    assert_eq!(eval("(define (keep x) (- x 0)) (list (eqv? (keep -0.0) -0.0) (eqv? (- -0.0 0) -0.0))"), "(#t #t)");
    // A leading effect in the first argument still runs first, and once.
    assert_eq!(
        eval("(define t '()) (define (note x) (set! t (cons x t)) x)
              (define (f x) (list (+ (begin (note 'a) 1) x) (+ (begin (note 'b) 2) 3) (+ (begin (note 'c) x) (note 1))))
              (list (f 5) (reverse t))"),
        "((6 5 6) (a b c 1))"
    );
    assert_eq!(eval_in(&mut arena(), "(define (inc x) (+ x 1)) (inc 'a)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(sub1 \"s\")"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(add1 1 2)"), Ok(Err(Fault::Arity)));
}

#[test]
fn coroutines_resume_and_yield_values_both_ways() {
    let round_trip = "(define co (make-coroutine (lambda (a b)
                                (let* ((c (co/yield (+ a b))) (d (co/yield (* c 2)))) (list a b c d)))))
                      (let* ((s0 (co/status co)) (y0 (co/resume co 1 2)) (s1 (co/status co)) (y1 (co/resume co 10))
                             (y2 (co/resume co 'x)) (s2 (co/status co)))
                        (list s0 y0 s1 y1 y2 s2 (coroutine? co) (coroutine? car)))";
    assert_eq!(eval(round_trip), "(pending 3 pending 20 (1 2 10 x) dead #t #f)");
    assert_eq!(eval("(define co (make-coroutine (lambda () (co/status co)))) (co/resume co)"), "running");
    assert_eq!(eval("(call-with-values (lambda () (co/resume (make-coroutine (lambda () (co/yield 1 2))))) list)"), "(1 2)");
    assert_eq!(eval("(call-with-values (lambda () (co/resume (make-coroutine (lambda () (co/yield))))) list)"), "()");
    let back = "(define co (make-coroutine (lambda () (call-with-values (lambda () (co/yield)) list))))
                (co/resume co) (co/resume co 1 2 3)";
    assert_eq!(eval(back), "(1 2 3)");
}

#[test]
fn co_running_is_the_innermost_running_coroutine() {
    assert_eq!(eval("(let ((top (co/running))) (list (eq? top (co/running)) (coroutine? top) (co/status top)))"), "(#t #t running)");
    let nested = "(define inner (make-coroutine (lambda () (eq? (co/running) inner))))
                  (define outer (make-coroutine (lambda ()
                                  (let* ((a (eq? (co/running) outer)) (b (co/resume inner)) (c (eq? (co/running) outer)))
                                    (list a b c (eq? (co/running) inner))))))
                  (let* ((top (co/running)) (r (co/resume outer))) (append r (list (eq? top (co/running)))))";
    assert_eq!(eval(nested), "(#t #t #t #f #t)");
    // A machine's own task is never pending, so it can't be resumed from inside.
    assert_eq!(eval_in(&mut arena(), "(co/resume (co/running))"), Ok(Err(Fault::NotPending)));
    let from_inside = "(define top (co/running)) (co/resume (make-coroutine (lambda () (co/resume top))))";
    assert_eq!(eval_in(&mut arena(), from_inside), Ok(Err(Fault::NotPending)));
    // Each top-level form runs in a machine of its own. That machine has finished when the next form runs.
    assert_eq!(eval("(define top (co/running)) (co/status top)"), "dead");
}

#[test]
fn a_yield_goes_to_what_resumed_the_coroutine() {
    let nested = "(define inner (make-coroutine (lambda () (co/yield 'i1) 'i-done)))
                  (define outer (make-coroutine (lambda ()
                                  (let* ((a (co/resume inner)) (s (co/status outer)) (b (co/yield a)) (c (co/resume inner)))
                                    (list s b c (co/status inner))))))
                  (let* ((first (co/resume outer)) (rest (co/resume outer 'sent))) (list first rest (co/status outer)))";
    assert_eq!(eval(nested), "(i1 (running sent i-done dead) dead)");
    let walk = "(define (walk n) (if (eqv? n 0) 0 (begin (co/yield n) (+ 1 (walk (- n 1))))))
                (define co (make-coroutine (lambda () (walk 20000))))
                (let loop ((sum 0))
                  (let ((v (co/resume co)))
                    (if (eq? (co/status co) 'dead) (list sum v) (loop (+ sum v)))))";
    assert_eq!(eval(walk), "(200010000 20000)");
    let many = "(define cos (let loop ((i 0) (acc '()))
                              (if (eqv? i 200) acc (loop (+ i 1) (cons (make-coroutine (lambda () (co/yield i) (* i 2))) acc)))))
                (define (each f xs) (if (null? xs) '() (cons (f (car xs)) (each f (cdr xs)))))
                (each co/resume cos)
                (let ((done (each co/resume cos))) (list (car done) (length done)))";
    assert_eq!(eval(many), "(398 200)");
}

#[test]
fn coroutines_keep_their_own_prompts_and_continuations() {
    assert_eq!(eval("(co/resume (make-coroutine (lambda () (+ 1 (call/cc (lambda (k) (k 41)))))))"), "42");
    let prompt = "(define co (make-coroutine (lambda () (call-with-continuation-prompt (lambda () (+ 1 (co/yield 'in)))))))
                  (list (co/resume co) (co/resume co 5) (co/status co))";
    assert_eq!(eval(prompt), "(in 6 dead)");
    let escape = "(define co (make-coroutine (lambda () (call/cc (lambda (k) (co/yield 'a) (k 'escaped) 'not)))))
                  (list (co/resume co) (co/resume co))";
    assert_eq!(eval(escape), "(a escaped)");
}

#[test]
fn suspended_frames_survive_being_moved_and_shared() {
    // A continuation is captured in the coroutine and called again after each yield. Other
    // coroutines run in between, on whichever stack segments are free.
    let again = "(define co (make-coroutine (lambda ()
                   (let ((i 0))
                     (let ((k (call/cc (lambda (k) k))))
                       (set! i (+ i 1))
                       (co/yield i)
                       (if (eqv? i 3) 'done (k k)))))))
                 (define (scribble) (co/resume (make-coroutine (lambda () (let f ((d 20)) (if (eqv? d 0) 0 (+ 1 (f (- d 1)))))))))
                 (let* ((a (co/resume co)) (b (scribble)) (c (co/resume co)) (d (scribble)) (e (co/resume co)) (f (scribble)))
                   (list a b c d e f (co/resume co)))";
    assert_eq!(eval(again), "(1 20 2 20 3 20 done)");
    // One generator is resumed alternately from the top level and from inside another coroutine.
    // Each yield returns to whichever of the two resumed it.
    let turns = "(define gen (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
                 (define other (make-coroutine (lambda () (let loop () (co/yield (co/resume gen)) (loop)))))
                 (let loop ((n 0) (top #t) (acc '()))
                   (if (eqv? n 6) (reverse acc) (loop (+ n 1) (not top) (cons (if top (co/resume gen) (co/resume other)) acc))))";
    assert_eq!(eval(turns), "(0 1 2 3 4 5)");
    // A coroutine yields from three call depths. The second yield is made inside a continuation prompt.
    let deep = "(define (down d) (if (eqv? d 0) (co/yield 'bottom) (list d (down (- d 1)))))
                (define co (make-coroutine (lambda ()
                             (list (down 3) (call-with-continuation-prompt (lambda () (down 2))) (down 30)))))
                (let* ((a (co/resume co)) (b (co/resume co 'x)) (c (co/resume co 'y)) (d (co/resume co 'z)))
                  (list a b c (car d) (cadr d) (co/status co)))";
    assert_eq!(eval(deep), "(bottom bottom bottom (3 (2 (1 x))) (2 (1 y)) dead)");
}

#[test]
fn a_failing_coroutine_raises_where_it_was_resumed_unless_protected() {
    assert_eq!(eval_in(&mut arena(), "(co/resume (make-coroutine (lambda () (car 1))))"), Ok(Err(Fault::WrongType)));
    let caught = "(define co (make-coroutine (lambda () (co/yield 1) (car 1))))
                  (define (try) (call-with-values (lambda () (co/try-resume co)) list))
                  (let* ((a (try)) (b (try)) (s (co/status co))) (list a (car b) s))";
    assert_eq!(eval(caught), "((#t 1) #f error)");
    let done = "(call-with-values (lambda () (co/try-resume (make-coroutine (lambda (x) (co/yield x (+ x 1)))) 5)) list)";
    assert_eq!(eval(done), "(#t 5 6)");
    assert_eq!(eval("(call-with-values (lambda () (co/try-resume (make-coroutine (lambda () 'end)))) list)"), "(#t end)");
    // The failure of a coroutine propagates into a coroutine that resumed it with a plain `co/resume`. That coroutine fails too.
    let through = "(define inner (make-coroutine (lambda () (car 1))))
                   (define outer (make-coroutine (lambda () (co/resume inner) 'unreached)))
                   (let ((r (call-with-values (lambda () (co/try-resume outer)) list))) (list (car r) (co/status inner) (co/status outer)))";
    assert_eq!(eval(through), "(#f error error)");
    let finished = "(define co (make-coroutine (lambda () 1))) (co/resume co) (co/resume co)";
    assert_eq!(eval_in(&mut arena(), finished), Ok(Err(Fault::NotPending)));
    assert_eq!(eval_in(&mut arena(), "(define co (make-coroutine (lambda () (co/resume co)))) (co/resume co)"), Ok(Err(Fault::NotPending)));
    let cycle = "(define a (make-coroutine (lambda () (co/resume b))))
                 (define b (make-coroutine (lambda () (co/resume a))))
                 (co/resume a)";
    assert_eq!(eval_in(&mut arena(), cycle), Ok(Err(Fault::NotPending)));
    assert_eq!(eval_in(&mut arena(), "(co/resume 5)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(make-coroutine 5)"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), "(co/status car)"), Ok(Err(Fault::WrongType)));
}

/// Loads `text`, which must be one form, and returns a machine that is ready to run the form's thunk.
fn machine(arena: &mut Arena, text: &str) -> Machine {
    arena.mutate(|mc| {
        let thunks = load_text(mc, text).unwrap();
        let [thunk] = thunks.as_slice() else { panic!("one form") };
        Machine::new(mc, MIN_SEGMENT, *thunk, &[]).unwrap()
    })
}

fn show_outcome<'gc>(mc: &Mutation<'gc>, outcome: Result<Outcome<'gc>, Fault>) -> String {
    match outcome {
        Ok(Outcome::Yielded(v)) => format!("yielded {}", show(mc, v)),
        Ok(Outcome::Done(v)) => format!("done {}", show(mc, v)),
        other => format!("{other:?}"),
    }
}

/// Starts a run with `first` and continues it through any pauses for the collector. Returns the written form of the final outcome.
fn settled<'gc>(mc: &Mutation<'gc>, machine: &mut Machine, first: impl FnOnce(&mut Machine) -> Result<Outcome<'gc>, Fault>) -> String {
    let mut outcome = first(machine);
    while let Ok(Outcome::Paused) = outcome {
        outcome = machine.run(mc);
    }
    show_outcome(mc, outcome)
}

#[test]
fn the_host_resumes_a_machine_that_yields() {
    let mut arena = arena();
    let text = "(let ((co (make-coroutine (lambda (x) (co/yield (list x 'a)) (co/yield (vector x 'b)) (list 'done x)))))
                  (let* ((a (co/yield (co/resume co 1))) (b (co/yield (vector->list (co/resume co)))) (c (co/resume co)))
                    (list a b c)))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[]))), "Err(NotPending)");
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "yielded ((1 a))");
    // The values that the coroutines hold stay alive while the coroutines wait.
    arena.collect();
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.resume(mc, &[Value::fixnum(10).unwrap()]))), "yielded ((1 b))");
    arena.collect();
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.resume(mc, &[Value::fixnum(20).unwrap()]))), "done (10 20 (done 1))");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[]))), "Err(Finished)");
    // A plain `run` resumes a machine that yielded, and passes no values to the yield.
    let mut machine = self::machine(&mut arena, "(call-with-values (lambda () (co/yield 'x)) list)");
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "yielded (x)");
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "done ()");
}

#[test]
fn a_coroutine_two_machines_resume_in_turn_is_copied_where_it_waits() {
    let mut arena = arena();
    // Two machines share one generator. Each machine resumes the generator, then resumes a coroutine
    // of its own, which suspends. So the generator is always resumed by a different machine from
    // the one that resumed it last, and collections run in between.
    let text = "(cons (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1)))))
                      (lambda (gen) (let loop ()
                                      (co/yield (co/resume gen))
                                      (co/resume (make-coroutine (lambda () (co/yield 'x))))
                                      (loop))))";
    let mut machines = {
        let mut made = machine(&mut arena, text);
        arena.mutate(|mc| {
            let Ok(Outcome::Done(pair)) = made.run(mc) else { panic!("the pair") };
            let pair = ragwort_types::pair::Pair::of(pair).unwrap();
            let (generator, driver) = (pair.head(mc), pair.tail(mc));
            [0, 1].map(|_| Machine::new(mc, MIN_SEGMENT, driver, &[generator]).unwrap())
        })
    };
    let mut seen = Vec::new();
    for i in 0..8 {
        if i % 3 == 0 {
            arena.collect();
        }
        let machine = &mut machines[i % 2];
        seen.push(arena.mutate(|mc| show_outcome(mc, if i < 2 { machine.run(mc) } else { machine.resume(mc, &[]) })));
    }
    assert_eq!(seen, (0..8).map(|i| format!("yielded ({i})")).collect::<Vec<_>>());
}

#[test]
fn coroutines_survive_collections_between_steps() {
    let mut arena = arena();
    let text = "(let ((gen (make-coroutine (lambda ()
                             (let loop ((i 0)) (if (eqv? i 30000) 'end (begin (co/yield (list i (vector i))) (loop (+ i 1)))))))))
                  (let loop ((sum 0) (kept '()))
                    (let ((v (co/resume gen)))
                      (if (eq? v 'end)
                          (list sum (length kept) (vector-ref (cadr (car kept)) 0))
                          (loop (+ sum (car v)) (if (eqv? (car v) 29999) (cons v kept) kept))))))";
    let mut machine = machine(&mut arena, text);
    let mut runs = 0;
    let done = loop {
        runs += 1;
        if runs % 64 == 0 {
            arena.collect();
        }
        let outcome = arena.step(|mc| match machine.run(mc).unwrap() {
            Outcome::Paused => None,
            Outcome::Done(v) => Some(show(mc, v)),
            other => panic!("{other:?}"),
        });
        if let Some(done) = outcome.unwrap() {
            break done;
        }
    };
    assert_eq!(done, "(449985000 1 29999)");
    assert!(runs > 1, "expected the run to pause for collections");
}

#[test]
fn a_suspended_coroutine_keeps_little_memory() {
    fn kept(body: &str) -> usize {
        let mut arena = arena();
        let text = format!("(define keep (let loop ((i 0) (acc '())) (if (eqv? i 200) acc (loop (+ i 1) (cons {body} acc)))))");
        eval_in(&mut arena, &text).unwrap().unwrap();
        arena.collect();
        arena.collect();
        arena.used()
    }
    let closures = kept("(lambda () i)");
    let suspended = kept("(let ((c (make-coroutine (lambda () (co/yield i) i)))) (co/resume c) c)");
    let each = (suspended - closures) / 200;
    assert!(each < 512, "{each} bytes per suspended coroutine");
}

#[test]
fn handlers_run_in_the_raise_under_the_handlers_outside_them() {
    assert_eq!(eval("(with-exception-handler (lambda (e) (* e 10)) (lambda () (+ 1 (raise-continuable 5))))"), "51");
    let nested = "(with-exception-handler (lambda (e) (list 'outer e))
                    (lambda () (with-exception-handler (lambda (e) (raise-continuable (list 'inner e)))
                                 (lambda () (raise-continuable 1)))))";
    assert_eq!(eval(nested), "(outer (inner 1))");
    // If the handler of a `raise` returns, an error is raised under the handlers outside that handler.
    let returned = "(guard (e ((error-object? e) (list (error-object-message e) (error-object-irritants e))))
                      (with-exception-handler (lambda (e) 'ignored) (lambda () (raise 'boom))))";
    assert_eq!(eval(returned), r#"("exception handler returned" (boom))"#);
    // A handler that is not a procedure is a fault. The fault is raised under the handlers outside that handler.
    assert_eq!(eval("(guard (e (#t (error-object-kind e))) (with-exception-handler 5 (lambda () (raise 'x))))"), "not-procedure");
    assert_eq!(uncaught("(raise 'nobody)"), "nobody");
    assert_eq!(uncaught("(with-exception-handler (lambda (e) (raise (list 'again e))) (lambda () (raise 1)))"), "(again 1)");
}

#[test]
fn guard_takes_what_its_clauses_match_and_raises_the_rest_again() {
    assert_eq!(eval("(guard (e (#t (list 'caught e))) (raise 'oops))"), "(caught oops)");
    assert_eq!(eval("(guard (e ((assq 'a e) => cdr) ((assq 'b e))) (raise (list (cons 'a 42))))"), "42");
    assert_eq!(eval("(guard (e ((assq 'a e) => cdr) ((assq 'b e))) (raise (list (cons 'b 23))))"), "(b . 23)");
    assert_eq!(eval("(guard (e ((eq? e 'x) 'no) (else (list 'else e))) (raise 'y))"), "(else y)");
    assert_eq!(eval("(guard (e (#t (list 'outer e))) (guard (e ((eq? e 'other) 'no)) (raise 'x)))"), "(outer x)");
    // If no clause matches, the guard raises the value again with `raise-continuable`.
    assert_eq!(eval("(with-exception-handler (lambda (e) 42) (lambda () (+ 1 (guard (e ((eq? e 'other) 'no)) (raise 'x)))))"), "43");
    assert_eq!(eval("(guard (e (#t 'caught)) (define x 1) (+ x 1))"), "2");
    assert_eq!(eval("(let ((e 'outer)) (guard (e (#f e)) e))"), "outer");
    assert_eq!(error("(guard (1 (#t 2)) 3)").0, BadSyntax);
    assert_eq!(error("(guard (e (#t 2)))").0, BadSyntax);
}

#[test]
fn optional_parameters_take_defaults() {
    assert_eq!(eval("(define (f a [b 2]) (list a b)) (list (f 1) (f 1 3))"), "((1 2) (1 3))");
    // Each default sees the parameters before it, and runs only when its argument is left out.
    let text = "(define n 0) (define (g [a (begin (set! n (+ n 1)) 1)] [b (* a 2)] . r) (list a b r)) (list (g) (g 5) (g 5 6 7) n)";
    assert_eq!(eval(text), "((1 2 ()) (5 10 ()) (5 6 (7)) 1)");
    assert_eq!(eval("(let ([f (lambda (a [b 1]) (+ a b))]) (list (f 1) (apply f '(1 2)) (map f '(1 2))))"), "(2 3 (2 3))");
    fn kind(call: &str) -> String {
        eval(&format!("(guard (e (#t (error-object-kind e))) (define (f a [b 1]) a) {call})"))
    }
    assert_eq!((kind("(f)"), kind("(f 1 2 3)")), ("arity".into(), "arity".into()));
    assert_eq!(error("(lambda ([a 1] b) 1)"), (BadSyntax, "b"));
    assert_eq!(error("(lambda ([a]) a)"), (BadSyntax, "[a]"));
}

#[test]
fn keyword_arguments_go_by_name() {
    let text = "(define (g #:x x #:y [y 10] . r) (list x y r)) (list (g #:x 1) (g 5 #:y 2 #:x 1) (g 7 8 #:x 0))";
    assert_eq!(eval(text), "((1 10 ()) (1 2 (5)) (0 10 (7 8)))");
    assert_eq!(eval("(define (h a #:k [k (+ a 1)]) (list a k)) (list (h 1) (h 1 #:k 9) (h 2))"), "((1 2) (1 9) (2 3))");
    assert_eq!(eval("(let () (define (z #:a a #:b b) (- a b)) (list (z #:b 1 #:a 10) (z #:a 1 #:b 10)))"), "(9 -9)");
    // Arguments run in the order they're written, whatever order the keywords sort in.
    assert_eq!(eval("(define (k #:b b #:a a) (list a b)) (define out '()) (define (note x) (set! out (cons x out)) x) (k #:b (note 1) #:a (note 2)) out"), "(2 1)");
    // A keyword procedure that isn't called by its definition's name is matched when it runs.
    let text = "(define h (lambda (a #:k [k 0] . r) (list a k r))) (let ([p h]) (list (p 1 #:k 2) (p 3 4 5) (apply p '(4)) (map p '(1 2))))";
    assert_eq!(eval(text), "((1 2 ()) (3 0 (4 5)) (4 0 ()) ((1 0 ()) (2 0 ())))");
    assert_eq!(eval("(define (r #:n n) (if (eqv? n 0) 'done (r #:n (- n 1)))) (r #:n 100000)"), "done");
    assert_eq!(eval("(list (lambda (#:a a) a) (procedure? (lambda (#:a a) a)))"), "(#<procedure> #t)");
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(define (kf a #:k [k 1] #:m m) (list a k m))"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(list (kf 1 #:m 2) (kf 1 #:k 3 #:m 4))"), Ok(Ok("((1 1 2) (1 3 4))".into())));
    assert_eq!(eval_in(&mut arena, "(kf 1)"), Ok(Err(Fault::Keyword)));
    // A later load requires this one, so it calls the core itself: inlined, here.
    assert_eq!(eval_in(&mut arena, "(define (small a #:k [k 1]) (+ a k)) (define (none) (small 1))"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(list (small 1) (small 1 #:k 5) (none) (map small '(1 2)) (kf 1 #:m 2 #:k 3))"), Ok(Ok("(2 6 2 (2 3) (1 3 2))".into())));
    assert_eq!(eval_in(&mut arena, "(small 1 #:j 2)"), Ok(Err(Fault::Keyword)));
    assert_eq!(eval_in(&mut arena, "(small)"), Ok(Err(Fault::Arity)));
}

#[test]
fn keyword_mistakes_name_the_keyword() {
    fn caught(text: &str) -> String {
        eval(&format!("(guard (e (#t (list (error-object-kind e) (error-object-irritants e)))) {text})"))
    }
    assert_eq!(caught("((lambda (#:a a) a) #:b 1)"), "(keyword (#:b))");
    assert_eq!(caught("(let ([f (lambda (#:a a) a)]) (f))"), "(keyword (#:a))");
    assert_eq!(caught("(define (f #:a a) a) (f #:a 1 2)"), "(arity ())");
    assert_eq!(caught("(car #:a 1)"), "(keyword (#:a))");
    assert_eq!(caught("(keyword-apply list '(#:b #:a) '(1 2) '())"), "(keyword (#:a))");
    assert_eq!(error("(define (f #:k k) k) (set! f 1)"), (Immutable, "f"));
    assert_eq!(eval("(let () (define (f #:k k) k) (define g f) (set! f (lambda (#:k k) (+ k 1))) (list (f #:k 1) (g #:k 1)))"), "(2 1)");
    assert_eq!(error("(define (f #:k k) k) (f #:k 1 #:k 2)"), (Duplicate, "#:k"));
    assert_eq!(error("(lambda (#:k a #:k b) 1)"), (Duplicate, "#:k"));
    assert_eq!(error("(lambda (#:k) 1)"), (BadSyntax, "#:k"));
    assert_eq!(error("(car #:k)"), (BadSyntax, "#:k"));
}

#[test]
fn apply_spreads_only_a_proper_list() {
    fn caught(text: &str) -> String {
        eval(&format!("(define two (car (list (lambda () (values 1 2))))) (define a (car (list apply))) (guard (e (#t (error-object-kind e))) {text})"))
    }
    // The last argument is a proper list, whether or not the procedure takes a rest parameter.
    assert_eq!(caught("(apply list 1 2 '(3 4))"), "(1 2 3 4)");
    assert_eq!(caught("(apply apply list 1 '(2 (3 4)))"), "(1 2 3 4)");
    assert_eq!(caught("(apply (lambda (a . r) (list a r)) '(1 2 3))"), "(1 (2 3))");
    for improper in ["(apply list 1)", "(apply list 1 2 '(3 . 4))", "(apply (lambda (a . r) r) 1 2)", "(apply apply list 1 '(2 3))", "(keyword-apply list '() '() 1 2)"] {
        assert_eq!(caught(improper), "wrong-type", "{improper}");
    }
    // Several values are not a list of arguments, however `apply` is reached. The call that would take them as one argument fails, and the error can be caught.
    for values in ["(apply list (two))", "(a list (two))", "(a apply list (two))", "(a keyword-apply list '() '() (two))", "(a (lambda (x . r) r) 0 (two))"] {
        assert_eq!(caught(values), "value-count", "{values}");
    }
    assert_eq!(caught("(call-with-values (lambda () (values 1 2 3)) (lambda (a . r) (list a r)))"), "(1 (2 3))");
}

#[test]
fn calls_through_a_value_reach_keyword_procedures_and_apply() {
    // `pick` hides each procedure from the compiler, so every call below is resolved while it runs.
    let defs = "(define (greet name [mark 1] #:loud [loud #f]) (list name mark loud))
                (define (needs #:key key) key)
                (define (down n #:step [step 1]) (if (eqv? n 0) 0 (+ 1 ((pick 3) (- n step)))))
                (define procs (vector greet needs apply down list))
                (define (pick i) (vector-ref procs i))";
    fn caught(defs: &str, text: &str) -> String {
        eval(&format!("{defs} (guard (e (#t (list (error-object-kind e) (error-object-irritants e)))) {text})"))
    }
    // A keyword procedure called without keywords, in tail and non-tail position.
    assert_eq!(caught(defs, "((pick 0) 7)"), "(7 1 #f)");
    assert_eq!(caught(defs, "(car ((pick 0) 7 8))"), "7");
    assert_eq!(caught(defs, "((pick 0) 7 #:loud #t)"), "(7 1 #t)");
    assert_eq!(caught(defs, "(apply (pick 0) 7 '(8))"), "(7 8 #f)");
    // Deep enough to continue on further stack segments.
    assert_eq!(caught(defs, "((pick 3) 100000)"), "100000");
    // A call the procedure cannot take names the keyword procedure.
    for wrong in ["((pick 0))", "(car ((pick 0) 1 2 3))", "(apply (pick 0) '())", "((pick 2) (pick 0) '(1 2 3))"] {
        assert_eq!(caught(defs, wrong), "(arity (#<procedure greet>))", "{wrong}");
    }
    assert_eq!(caught(defs, "((pick 1))"), "(keyword (#:key))");
    assert_eq!(caught(defs, "((pick 2) (pick 1) '())"), "(keyword (#:key))");
    // The first-class `apply`, in tail and non-tail position.
    assert_eq!(caught(defs, "((pick 2) (pick 4) '(1 2))"), "(1 2)");
    assert_eq!(caught(defs, "(car ((pick 2) (pick 0) '(7)))"), "7");
    assert_eq!(caught(defs, "((pick 2) (pick 4) '())"), "()");
    assert_eq!(caught(defs, "((pick 2) (pick 4) 1 2 '(3))"), "(1 2 3)");
    assert_eq!(caught(defs, "((pick 2) (pick 2) (pick 4) '((1 2)))"), "(1 2)");
    for improper in ["((pick 2) (pick 4) 5)", "((pick 2) (pick 4) '(1 . 2))"] {
        assert_eq!(caught(defs, improper), "(wrong-type ())", "{improper}");
    }
}

#[test]
fn multiple_values_pass_through_control_forms() {
    fn received(producer: &str) -> String {
        eval(&format!("(call-with-values (lambda () {producer}) list)"))
    }
    assert_eq!(received("(values)"), "()");
    assert_eq!(received("(values 1)"), "(1)");
    assert_eq!(received("(apply values '(1 2 3))"), "(1 2 3)");
    // The body and a clause of `guard`.
    assert_eq!(received("(guard (e (#t 'caught)) (values 1 2))"), "(1 2)");
    assert_eq!(received("(guard (e (#t (values 'a 'b))) (raise 'x))"), "(a b)");
    // A handler's thunk, and the handler of a continuable raise.
    assert_eq!(received("(with-exception-handler (lambda (e) 0) (lambda () (values 1 2)))"), "(1 2)");
    assert_eq!(received("(with-exception-handler (lambda (e) (values 5 6)) (lambda () (raise-continuable 'x)))"), "(5 6)");
    // A marked thunk, a prompt's thunk and a prompt's handler.
    assert_eq!(received("(call-with-mark 'key 1 (lambda () (values 1 2)))"), "(1 2)");
    assert_eq!(received("(call-with-continuation-prompt (lambda () (values 1 2)))"), "(1 2)");
    let tag = "(default-continuation-prompt-tag)";
    assert_eq!(received(&format!("(call-with-continuation-prompt (lambda () (abort-current-continuation {tag} 1 2)) {tag} (lambda (a b) (values a b 3)))")), "(1 2 3)");
    // The thunk of `dynamic-wind`, and a continuation called from inside one.
    assert_eq!(received("(dynamic-wind (lambda () 0) (lambda () (values)) (lambda () 0))"), "()");
    assert_eq!(received("(dynamic-wind (lambda () 0) (lambda () (values 1 2 3)) (lambda () 0))"), "(1 2 3)");
    for (given, got) in [("", "()"), ("1", "(1)"), ("1 2 3", "(1 2 3)")] {
        assert_eq!(received(&format!("(call/cc (lambda (k) (dynamic-wind (lambda () 0) (lambda () (k {given})) (lambda () 0))))")), got, "{given}");
    }
    // A coroutine's yield and its last result.
    let coroutine = "(define co (make-coroutine (lambda () (co/yield 1 2) (values 3 4))))";
    assert_eq!(eval(&format!("{coroutine} (list (call-with-values (lambda () (co/resume co)) list) (call-with-values (lambda () (co/resume co)) list))")), "((1 2) (3 4))");
}

/// Each level returns two values to a receiver one call deeper, so the values cross from one stack
/// segment back to the previous one many times while the collector runs in steps.
#[test]
fn multiple_values_return_across_stack_segments() {
    let mut arena = arena();
    let text = "(let ()
                  (define (deep n) (if (eqv? n 0) (values 1 2) (call-with-values (lambda () (deep (- n 1))) (lambda (a b) (values (+ a 1) (+ b 1))))))
                  (call-with-values (lambda () (deep 100000)) list))";
    let mut machine = machine(&mut arena, text);
    let done = loop {
        let outcome = arena.step(|mc| match machine.run(mc).unwrap() {
            Outcome::Paused => None,
            Outcome::Done(value) => Some(show(mc, value)),
            other => panic!("{other:?}"),
        });
        if let Some(done) = outcome.unwrap() {
            break done;
        }
    };
    assert_eq!(done, "(100001 100002)");
}

#[test]
fn a_place_for_one_value_takes_no_other_number() {
    // The procedures are reached through a list, so the compiler does not see what they return.
    let defs = "(define two (car (list (lambda () (values 1 2))))) (define none (car (list (lambda () (values)))))";
    fn caught(defs: &str, text: &str) -> String {
        eval(&format!("{defs} (guard (e (#t (list (error-object-kind e) (error-object-irritants e)))) {text})"))
    }
    for (several, received) in [("(+ 1 (two))", 2), ("(list (none))", 0), ("(let ((x (two))) (list x))", 2), ("(if (two) 1 2)", 2), ("(vector-ref (vector 1 2) (none))", 0)] {
        assert_eq!(caught(defs, several), format!("(value-count ({received}))"), "{several}");
    }
    assert_eq!(caught(defs, "(let ((k (call/cc (lambda (k) k)))) (if (procedure? k) (k 1 2) k))"), "(value-count (2))");
    // A result that nothing uses is not checked.
    assert_eq!(caught(defs, "(begin (two) 5)"), "5");
    // A call's result is passed on as it is, to its own caller or to a receiver.
    assert_eq!(caught(defs, "(call-with-values (lambda () (two)) list)"), "(1 2)");
    assert_eq!(caught(defs, "(call-with-values (lambda () (if (pair? (list 1)) (two) 3)) list)"), "(1 2)");
    assert_eq!(caught(defs, "(call-with-values (lambda () (guard (e (#f 0)) (two))) list)"), "(1 2)");
    assert_eq!(caught(defs, "(call-with-values none list)"), "()");
}

#[test]
fn values_are_bound_by_let_values_and_define_values() {
    assert_eq!(eval("(let-values (((a b) (values 1 2)) ((c) (values 3)) (all (values 4 5)) ((d . more) (values 6 7 8))) (list a b c all d more))"), "(1 2 3 (4 5) 6 (7 8))");
    assert_eq!(eval("(let-values () 5)"), "5");
    assert_eq!(eval("(let-values (((a b) (values 1 2))) (define c (+ a b)) (list a b c))"), "(1 2 3)");
    // The inits of `let-values` see none of its variables. Those of `let*-values` see the ones before.
    assert_eq!(eval("(let ((a 'outer)) (let-values (((a) (values 1)) ((b) (values a))) (list a b)))"), "(1 outer)");
    assert_eq!(eval("(let ((a 'outer)) (let*-values (((a) (values 1)) ((b c) (values a (+ a 1)))) (list a b c)))"), "(1 1 2)");
    assert_eq!(eval("(let*-values () 5)"), "5");
    // The values can come from any call, and a temporary of the expansion is not visible to the body.
    assert_eq!(eval("(define (two) (values 1 2)) (define t0-0 'mine) (let-values (((a b) (two)) ((c d) (two))) (list a b c d t0-0))"), "(1 2 1 2 mine)");
    // `define-values` defines each variable, at the top level and in a body.
    assert_eq!(eval("(define-values (a b . more) (values 1 2 3 4)) (define-values all (values 5 6)) (define-values () (values)) (list a b more all)"), "(1 2 (3 4) (5 6))");
    assert_eq!(eval("(define (f) (define-values (a b) (values 1 2)) (define c (+ a b)) (list a b c)) (f)"), "(1 2 3)");
    // The number of values must fit the formals.
    fn caught(text: &str) -> String {
        eval(&format!("(guard (e (#t (error-object-kind e))) {text})"))
    }
    assert_eq!(caught("(let-values (((a b) (values 1 2 3))) a)"), "arity");
    assert_eq!(caught("(let-values (((a b) 1) ((c) 2)) a)"), "arity");
    assert_eq!(caught("(let () (define-values (a) (values)) a)"), "arity");
    for bad in ["(let-values ((a)) 1)", "(let-values (((a 1) 2)) 3)", "(let-values (((a) 1)))", "(define-values (a 1) 2)", "(define-values (a))", "(let*-values ((5 1)) 2)"] {
        assert_eq!(error(bad).0, ExpandErrorKind::BadSyntax, "{bad}");
    }
}

#[test]
fn receiving_from_a_known_producer_keeps_its_order_and_checks() {
    // The compiler removes a producer whose body it can see. What runs, and in what order, stays the same.
    let defs = "(define log '()) (define (note x) (set! log (cons x log)) x) (define (two x) (values x (+ x 1)))";
    fn caught(defs: &str, text: &str) -> String {
        eval(&format!("{defs} (guard (e (#t (error-object-kind e))) {text})"))
    }
    assert_eq!(caught(defs, "(call-with-values (lambda () (note 1) (values (note 2) (note 3))) (lambda (a b) (note 4) (list a b (reverse log))))"), "(2 3 (1 2 3 4))");
    assert_eq!(caught(defs, "(call-with-values (lambda () (let ((x (note 1))) (values x (+ x 1)))) list)"), "(1 2)");
    assert_eq!(caught(defs, "(call-with-values (lambda () (two (note 7))) (lambda (a b) (list a b (reverse log))))"), "(7 8 (7))");
    assert_eq!(caught(defs, "(call-with-values (lambda () (two 1)) +)"), "3");
    assert_eq!(caught(defs, "(call-with-values (lambda () 5) (lambda (a) (+ a 1)))"), "6");
    assert_eq!(caught(defs, "(call-with-values (lambda () (note 5)) list)"), "(5)");
    assert_eq!(caught(defs, "(call-with-values (lambda () (values)) (lambda () 'none))"), "none");
    assert_eq!(caught(defs, "(call-with-values (lambda () (values 1 2 3)) (lambda (a . more) (list a more)))"), "(1 (2 3))");
    assert_eq!(caught(defs, "(let ((c (lambda (a b) (- a b)))) (call-with-values (lambda () (values 5 3)) c))"), "2");
    // A producer or consumer that is used again is left alone.
    assert_eq!(caught(defs, "(let ((p (lambda () (values 1 2)))) (list (call-with-values p list) (call-with-values p list)))"), "((1 2) (1 2))");
    assert_eq!(caught(defs, "(let ((c (lambda (a b) (- a b)))) (list (call-with-values (lambda () (values 5 3)) c) (c 1 1)))"), "(2 0)");
    // The number of values is still checked against the consumer.
    for wrong in ["(call-with-values (lambda () (values 1 2 3)) (lambda (a b) a))", "(call-with-values (lambda () 5) (lambda (a b) a))", "(call-with-values (lambda () (two 1)) (lambda (a) a))", "(call-with-values (lambda () (values)) (lambda (a) a))"] {
        assert_eq!(caught(defs, wrong), "arity", "{wrong}");
    }
}

#[test]
fn keyword_calls_through_a_value_match_while_they_run() {
    // `pick` hides each procedure from the compiler, so the keywords of every call below are matched when the call runs.
    let defs = "(define (none a) (list a))
                (define (one a #:x [x 'dx]) (list a x))
                (define (two a b #:x [x 'dx] #:y y) (list a b x y))
                (define (four a #:p [p 1] #:q [q 2] #:r [r 3] #:s [s 4] . more) (list a p q r s more))
                (define (nine #:a [a 1] #:b [b 2] #:c [c 3] #:d [d 4] #:e [e 5] #:f [f 6] #:g [g 7] #:h [h 8] #:i [i 9] z) (list a b c d e f g h i z))
                (define procs (vector none one two four nine))
                (define (pick i) (vector-ref procs i))";
    fn caught(defs: &str, text: &str) -> String {
        eval(&format!("{defs} (guard (e (#t (list (error-object-kind e) (error-object-irritants e)))) {text})"))
    }
    // One, two and more accepted keywords, given in any order, in tail and non-tail position.
    assert_eq!(caught(defs, "((pick 1) 1 #:x 2)"), "(1 2)");
    assert_eq!(caught(defs, "(car ((pick 1) 1 #:x 2))"), "1");
    assert_eq!(caught(defs, "((pick 2) 1 2 #:y 3)"), "(1 2 dx 3)");
    assert_eq!(caught(defs, "((pick 2) #:y 3 1 #:x 4 2)"), "(1 2 4 3)");
    assert_eq!(caught(defs, "((pick 3) 0 #:s 's #:q 'q)"), "(0 1 q 3 s ())");
    assert_eq!(caught(defs, "(cdr ((pick 3) 0 5 6 7 #:r 'r #:p 'p))"), "(p 2 r 4 (5 6 7))");
    assert_eq!(caught(defs, "((pick 4) #:i 'i 0 #:a 'a)"), "(a 2 3 4 5 6 7 8 i 0)");
    // The arguments are evaluated in the order they are written.
    assert_eq!(caught(defs, "(let* ((log '()) (note (lambda (x) (set! log (cons x log)) x))) (list ((pick 2) (note 1) #:y (note 2) (note 3) #:x (note 4)) (reverse log)))"), "((1 3 4 2) (1 2 3 4))");
    // The errors are the ones the general path reports.
    assert_eq!(caught(defs, "((pick 2) 1 2)"), "(keyword (#:y))");
    assert_eq!(caught(defs, "((pick 2) 1 2 #:y 3 #:z 4)"), "(keyword (#:z))");
    assert_eq!(caught(defs, "((pick 0) 1 #:x 2)"), "(keyword (#:x))");
    assert_eq!(caught(defs, "((pick 1) #:x 2)"), "(arity ())");
    assert_eq!(caught(defs, "((pick 1) 1 2 #:x 2)"), "(arity ())");
    assert_eq!(caught(defs, "(5 1 #:x 2)"), "(keyword (#:x))");
}

#[test]
fn marks_set_in_tail_position_stay_on_their_frame() {
    // Each turn of the loop replaces the mark of the same frame, so the loop keeps one mark however long it runs.
    let count = "(define (count n) (if (eqv? n 0) (mark-value 'depth 'none) (with-continuation-mark 'depth n (count (- n 1)))))";
    assert_eq!(eval(&format!("{count} (count 100000)")), "1");
    assert_eq!(eval(&format!("{count} (list (count 3) (mark-value 'depth 'none))")), "(1 none)");
    // A mark set in tail position inside a marked call belongs to that call's frame, and goes when it returns.
    let inner = "(define (inner) (with-continuation-mark 'a 2 (mark-value 'a 0)))";
    assert_eq!(eval(&format!("{inner} (with-continuation-mark 'a 1 (list (inner) (mark-value 'a 0)))")), "(2 1)");
    assert_eq!(eval(&format!("{inner} (with-continuation-mark 'b 1 (list (with-continuation-mark 'a 5 (inner)) (mark-value 'a 0) (mark-value 'b 0)))")), "(2 0 1)");
    // A different key in tail position adds to the frame's marks.
    assert_eq!(eval("(define (both) (with-continuation-mark 'a 1 (with-continuation-mark 'b 2 (list (mark-value 'a 0) (mark-value 'b 0))))) (both)"), "(1 2)");
    // A handler installed in tail position works the same way.
    let handled = "(define (handled) (with-exception-handler (lambda (e) (list 'inner e)) (lambda () (raise-continuable 'x))))";
    assert_eq!(eval(&format!("{handled} (with-exception-handler (lambda (e) (list 'outer e)) (lambda () (list (with-continuation-mark 'a 1 (handled)) (raise-continuable 'y))))")), "((inner x) (outer y))");
}

/// Each level makes one call of every kind the VM builds itself, and then recurses without a tail call. The stack segments are the smallest size, so over the levels each kind of call starts at every distance from the end of a segment, including the ones that need a new segment.
#[test]
fn calls_the_vm_builds_work_at_any_stack_depth() {
    let mut arena = arena();
    let text = "(let ((tag (default-continuation-prompt-tag)))
                  (define (level n)
                    (if (eqv? n 0)
                        0
                        (+ (call/cc (lambda (k) (k 1)))
                           (call/cc (lambda (k) (dynamic-wind (lambda () 0) (lambda () (k 1)) (lambda () 0))))
                           (with-exception-handler (lambda (e) e) (lambda () (raise-continuable 1)))
                           (guard (e (#t e)) (raise 1))
                           (guard (e (#t 1)) (car n))
                           (car (call-with-continuation-prompt (lambda () (abort-current-continuation tag 1 2)) tag list))
                           (call-with-values (lambda () (call/cc (lambda (k) (k 1 2 3)))) (lambda (a b c) a))
                           (co/resume (make-coroutine (lambda (x) x)) 1)
                           (let ((co (make-coroutine (lambda () (co/yield 1 2) 3)))) (call-with-values (lambda () (co/resume co)) (lambda (a b) a)))
                           (car ((car (list apply)) list 1 2 (list 3)))
                           (level (- n 1)))))
                  (level 300))";
    let mut machine = machine(&mut arena, text);
    let done = loop {
        let outcome = arena.step(|mc| match machine.run(mc).unwrap() {
            Outcome::Paused => None,
            Outcome::Done(value) => Some(show(mc, value)),
            other => panic!("{other:?}"),
        });
        if let Some(done) = outcome.unwrap() {
            break done;
        }
    };
    assert_eq!(done, "3000");
}

/// Runs `machine` until it finishes or yields, letting the collector work whenever the run pauses.
fn run_to_outcome(arena: &mut Arena, machine: &mut Machine, mut resume: bool) -> String {
    loop {
        let outcome = arena.step(|mc| {
            let outcome = if std::mem::take(&mut resume) { machine.resume(mc, &[]) } else { machine.run(mc) };
            match outcome.unwrap() {
                Outcome::Paused => None,
                outcome => Some(show_outcome(mc, Ok(outcome))),
            }
        });
        if let Some(outcome) = outcome.unwrap() {
            break outcome;
        }
    }
}

/// A coroutine that waits while several others yield has its frames copied into storage of their own size. The coroutines here wait at different depths, some too deep to be copied. What their frames hold must stay alive: here each holds values nothing else refers to, the collector runs, and new allocations reuse whatever it freed.
#[test]
fn a_waiting_coroutines_frames_keep_what_they_hold() {
    let mut arena = arena();
    let text = "(let ()
                  (define (dig n x) (if (eqv? n 0) (begin (co/yield 0) x) (let ((got (dig (- n 1) x))) (if (pair? got) got #f))))
                  (define (make i) (make-coroutine (lambda () (let ((x (list i (number->string i) (vector i (string-append \"s\" (number->string i)))))) (dig (modulo i 25) x)))))
                  (define (kept? i x) (and (pair? x) (eqv? (car x) i) (equal? (cadr x) (number->string i)) (vector? (caddr x)) (equal? (vector-ref (caddr x) 1) (string-append \"s\" (number->string i)))))
                  (define (churn n acc) (if (eqv? n 0) acc (churn (- n 1) (list n n n))))
                  (let ((waiting (let loop ((i 0) (made '())) (if (eqv? i 100) (reverse made) (loop (+ i 1) (cons (make i) made))))))
                    (for-each (lambda (co) (co/resume co)) waiting)
                    (co/yield 'waiting)
                    (churn 200000 0)
                    (let loop ((i 0) (waiting waiting) (lost 0))
                      (if (null? waiting) lost (loop (+ i 1) (cdr waiting) (if (kept? i (co/resume (car waiting))) lost (+ lost 1)))))))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "yielded (waiting)");
    arena.collect();
    assert_eq!(run_to_outcome(&mut arena, &mut machine, true), "done 0");
}

/// Each level captures a continuation and calls it at once. A reinstated continuation is copied back to the stack a chunk at a time, and what stays behind must not keep the whole stack segment it came from alive, or a recursion of this depth does not fit in the arena.
#[test]
fn continuations_captured_at_every_level_of_a_deep_recursion_fit() {
    let mut arena = arena();
    let text = "(let () (define (level n) (if (eqv? n 0) 0 (+ (call/cc (lambda (k) (k 1))) (level (- n 1))))) (level 5000))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "done 5000");
}

/// Definitions for the coroutine tests below: a log, and `(winding)`, which makes a coroutine that yields inside two nested `dynamic-wind` calls.
const WINDING: &str = "(define log '()) (define (note x) (set! log (cons x log)) x)
    (define (winding)
      (make-coroutine (lambda ()
        (dynamic-wind (lambda () (note 'in1))
                      (lambda () (dynamic-wind (lambda () (note 'in2)) (lambda () (co/yield 'y) (note 'not)) (lambda () (note 'out2))))
                      (lambda () (note 'out1))))))";

/// Evaluates `text` after [`WINDING`]. A raised value is shown as `(raised value)`, with an error object shown by its kind.
fn coroutine_case(text: &str) -> String {
    eval(&format!("{WINDING} (guard (e (#t (list 'raised (if (error-object? e) (error-object-kind e) e)))) {text})"))
}

#[test]
fn closing_a_coroutine_runs_its_afters_and_ends_it() {
    // A coroutine that never started, and one suspended outside any `dynamic-wind`, end without running anything.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (note 'ran))))) (co/close co) (list (co/status co) (reverse log)))"), "(dead ())");
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (co/yield 1) (note 'ran))))) (co/resume co) (co/close co) (list (co/status co) (reverse log)))"), "(dead ())");
    assert_eq!(coroutine_case("(co/close (make-coroutine (lambda () 1)))"), "#<void>");
    // The `after` thunks run once, innermost first. The rest of the body does not run, and the coroutine cannot be resumed.
    assert_eq!(coroutine_case("(let ((co (winding))) (co/resume co) (co/close co) (co/close co) (list (co/status co) (reverse log)))"), "(dead (in1 in2 out2 out1))");
    assert_eq!(coroutine_case("(let ((co (winding))) (co/resume co) (co/close co) (co/resume co))"), "(raised not-pending)");
    // They run in the coroutine's own context: its marks, and itself as the running coroutine, which reports running.
    let own = "(letrec ((co (make-coroutine (lambda ()
                 (with-continuation-mark 'k 'mine
                   (car (list (dynamic-wind (lambda () 0) (lambda () (co/yield 1)) (lambda () (note (list (mark-value 'k 'none) (eq? (co/running) co) (co/status co))))))))))))
                 (co/resume co) (co/close co) (reverse log))";
    assert_eq!(coroutine_case(own), "((mine #t running))");
    // A coroutine whose frames were copied while it waited closes the same way.
    assert_eq!(coroutine_case("(let ((a (winding)) (b (make-coroutine (lambda () (co/yield 0))))) (co/resume a) (co/resume b) (co/close a) (list (co/status a) (co/status b) (reverse log)))"), "(dead pending (in1 in2 out2 out1))");
    // A dead or failed coroutine is left as it is.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (raise 'boom))))) (guard (e (#t e)) (co/resume co)) (co/close co) (co/status co))"), "error");
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () 1)))) (co/resume co) (co/close co) (co/status co))"), "dead");
    // A running coroutine cannot be closed: the root, a coroutine closing itself, or one that is waiting for a coroutine it resumed.
    assert_eq!(coroutine_case("(co/close (co/running))"), "(raised not-pending)");
    assert_eq!(coroutine_case("(co/resume (make-coroutine (lambda () (co/close (co/running)))))"), "(raised not-pending)");
    assert_eq!(coroutine_case("(letrec ((outer (make-coroutine (lambda () (co/resume (make-coroutine (lambda () (co/close outer)))))))) (co/resume outer))"), "(raised not-pending)");
    assert_eq!(coroutine_case("(co/close 5)"), "(raised wrong-type)");
}

#[test]
fn a_close_that_fails_or_yields_fails_the_coroutine() {
    fn failing(after: &str) -> String {
        format!(
            "(let ((co (make-coroutine (lambda ()
                         (dynamic-wind (lambda () (note 'in1))
                                       (lambda () (dynamic-wind (lambda () (note 'in2)) (lambda () (co/yield 'y)) (lambda () (note 'out2) {after})))
                                       (lambda () (note 'out1)))))))
               (co/resume co)
               (list (guard (e (#t (if (error-object? e) (error-object-kind e) e))) (co/close co)) (co/status co) (reverse log)))"
        )
    }
    // An `after` thunk that raises: the outer ones still run, the coroutine fails, and the value is raised at the close.
    assert_eq!(coroutine_case(&failing("(raise 'oops)")), "(oops error (in1 in2 out2 out1))");
    // A coroutine that is being closed cannot yield.
    assert_eq!(coroutine_case(&failing("(co/yield 'late)")), "(not-pending error (in1 in2 out2 out1))");
    // A reset whose close fails raises the value too, and the coroutine is reset all the same.
    let reset = failing("(raise 'oops)").replace("(co/close co)", "(co/reset co (lambda () 'new))").replace("(co/status co) (reverse log)", "(co/status co) (co/resume co) (co/status co) (reverse log)");
    assert_eq!(coroutine_case(&reset), "(oops pending new dead (in1 in2 out2 out1))");
    // An `after` thunk can catch its own errors, and the close then succeeds.
    assert_eq!(coroutine_case(&failing("(guard (e (#t (note 'caught))) (co/yield 'late))")), "(#<void> dead (in1 in2 out2 caught out1))");
}

#[test]
fn a_reset_coroutine_runs_a_new_body() {
    // A coroutine that finished is used again, with new arguments.
    let reused = "(let ((co (make-coroutine (lambda (x) (+ x 1)))))
                    (list (co/resume co 1) (co/status co) (eq? (co/reset co (lambda (x y) (co/yield (* x y)) 'end)) co) (co/status co) (co/resume co 3 4) (co/resume co) (co/status co)))";
    assert_eq!(coroutine_case(reused), "(2 dead #t pending 12 end dead)");
    // A suspended coroutine is closed first. One that never started only gets the new body. One that failed starts again.
    assert_eq!(coroutine_case("(let ((co (winding))) (co/resume co) (co/reset co (lambda () 'new)) (list (reverse log) (co/status co) (co/resume co)))"), "((in1 in2 out2 out1) pending new)");
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (note 'old))))) (co/reset co (lambda () 'new)) (list (co/resume co) (reverse log)))"), "(new ())");
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (raise 'boom))))) (guard (e (#t e)) (co/resume co)) (co/reset co (lambda () 'again)) (list (co/status co) (co/resume co)))"), "(pending again)");
    // The new body must be a procedure. A wrong one leaves the coroutine as it was.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (co/yield 1) 2)))) (co/resume co) (list (guard (e (#t (error-object-kind e))) (co/reset co 5)) (co/status co) (co/resume co)))"), "(wrong-type pending 2)");
    assert_eq!(coroutine_case("(co/reset (co/running) (lambda () 1))"), "(raised not-pending)");
    assert_eq!(coroutine_case("(co/reset 5 (lambda () 1))"), "(raised wrong-type)");
    // One coroutine serves many bodies in turn.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () 0)))) (let loop ((i 0) (sum 0)) (if (eqv? i 1000) sum (begin (co/reset co (lambda () i)) (loop (+ i 1) (+ sum (co/resume co)))))))"), "499500");
}

#[test]
fn a_coroutine_resumed_with_an_error_raises_it_at_its_yield() {
    // The coroutine catches the value where it yielded, and goes on.
    let caught = "(let ((co (make-coroutine (lambda () (let ((got (guard (e (#t (list 'caught e))) (co/yield 'ready)))) (co/yield got) 'end)))))
                    (list (co/resume co) (co/resume-error co 'bad) (co/resume co) (co/status co)))";
    assert_eq!(coroutine_case(caught), "(ready (caught bad) end dead)");
    // Nothing catches it: the `after` thunks run, the coroutine fails, and the value is raised at the call.
    assert_eq!(coroutine_case("(let ((co (winding))) (co/resume co) (list (guard (e (#t (list 'raised e))) (co/resume-error co 'bad)) (co/status co) (reverse log)))"), "((raised bad) error (in1 in2 out2 out1))");
    // A coroutine that has not started fails without running its body.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () (note 'ran))))) (list (guard (e (#t (list 'raised e))) (co/resume-error co 'bad)) (co/status co) (reverse log)))"), "((raised bad) error ())");
    // An error object keeps its identity, and a handler in the coroutine sees it.
    let handled = "(let* ((problem (guard (e (#t e)) (error \"bad input\" 7)))
                          (co (make-coroutine (lambda () (with-exception-handler (lambda (e) (co/yield (eq? e problem)) 0) (lambda () (co/yield 'ready)))))))
                     (list (co/resume co) (co/resume-error co problem)))";
    assert_eq!(coroutine_case(handled), "(ready #t)");
    // Only a pending coroutine can be resumed this way.
    assert_eq!(coroutine_case("(let ((co (make-coroutine (lambda () 1)))) (co/resume co) (co/resume-error co 'bad))"), "(raised not-pending)");
    assert_eq!(coroutine_case("(co/resume-error (co/running) 'bad)"), "(raised not-pending)");
    assert_eq!(coroutine_case("(co/resume-error 5 'bad)"), "(raised wrong-type)");
}

/// Coroutines are made, suspended inside a `dynamic-wind` and closed, over and over. What a closed coroutine held must become free, or this does not fit in the arena.
#[test]
fn closed_coroutines_leave_nothing_behind() {
    let mut arena = arena();
    let text = "(let ((count 0))
                  (define (one) (make-coroutine (lambda () (dynamic-wind (lambda () 0) (lambda () (co/yield (make-vector 64 0))) (lambda () (set! count (+ count 1)))))))
                  (let loop ((i 0))
                    (if (eqv? i 20000)
                        count
                        (let ((co (one))) (co/resume co) (co/close co) (loop (+ i 1))))))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "done 20000");
}

/// A coroutine and its resumer switch back and forth many times while the collector runs. Each keeps values in its frame that nothing else refers to. The coroutine yields in three ways: from its own loop, from a helper that then returns, and from the bottom of a recursion, shallow on odd turns and deep on even ones. Every switch must come back to the frames it left, with what they held.
#[test]
fn switches_come_back_to_the_frames_they_left() {
    let mut arena = arena();
    let text = "(let ()
                  (define (churn n acc) (if (eqv? n 0) acc (churn (- n 1) (list n n n))))
                  (define (emit x) (co/yield x) 'emitted)
                  (define (down n) (if (eqv? n 0) (begin (co/yield 'bottom) 0) (+ 1 (down (- n 1)))))
                  (define gen
                    (make-coroutine
                      (lambda ()
                        (let loop ((i 0) (kept (list 0 \"0\")))
                          (let* ((sent (co/yield (list 'plain i kept)))
                                 (helped (emit (list 'helper sent)))
                                 (depth (down (if (odd? i) 10 400))))
                            (loop (+ i 1) (list depth helped (number->string i))))))))
                  (let loop ((round 0) (good 0))
                    (if (eqv? round 40)
                        good
                        (let* ((mine (list round (number->string round)))
                               (plain (co/resume gen))
                               (garbage1 (churn 3000 0))
                               (helper (co/resume gen (* round 2)))
                               (garbage2 (churn 3000 0))
                               (bottom (co/resume gen))
                               (before (- round 1))
                               (expected (if (eqv? round 0) (list 0 \"0\") (list (if (odd? before) 10 400) 'emitted (number->string before)))))
                          (churn 3000 0)
                          (loop (+ round 1)
                                (if (and (equal? mine (list round (number->string round)))
                                         (equal? plain (list 'plain round expected))
                                         (equal? helper (list 'helper (* round 2)))
                                         (eq? bottom 'bottom))
                                    (+ good 1)
                                    good))))))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "done 40");
}

#[test]
fn a_waiting_resumer_takes_errors_and_closes_like_any_task() {
    // The resumer waits in a frame that holds a value. A failing coroutine raises into that frame, and a guard or a handler there sees it.
    let failing = "(define co (make-coroutine (lambda () (co/yield 1) (raise 'boom))))";
    assert_eq!(eval(&format!("{failing} (co/resume co) (let ((kept (list 1 2))) (list (guard (e (#t (list 'caught e))) (+ 1 (co/resume co))) kept (co/status co)))")), "((caught boom) (1 2) error)");
    assert_eq!(eval(&format!("{failing} (co/resume co) (let ((kept (list 1 2))) (list (with-exception-handler (lambda (e) 5) (lambda () (guard (e (#f 0)) (+ 1 (guard (e ((eq? e 'boom) 41)) (co/resume co)))))) kept))")), "(42 (1 2))");
    // A fault in the request itself, here a resume of something that is not a coroutine, is raised in the frame that made it.
    assert_eq!(eval("(let ((kept (list 1 2))) (list (guard (e (#t (error-object-kind e))) (+ 1 (co/resume 5))) kept))"), "(wrong-type (1 2))");
    assert_eq!(eval("(define co (make-coroutine (lambda () 1))) (co/resume co) (let ((kept (list 1 2))) (list (guard (e (#t (error-object-kind e))) (+ 1 (co/resume co))) kept))"), "(not-pending (1 2))");
    // `co/try-resume` in the middle of an expression catches the failure itself. Nothing is raised in the frame, and what the frame holds stays.
    assert_eq!(eval(&format!("{failing} (co/resume co) (let ((kept (list 1 2))) (co/try-resume co) (co/try-resume 5) (list kept (co/status co)))")), "((1 2) error)");
    assert_eq!(eval(&format!("{failing} (co/resume co) (let ((kept (list 1 2))) (list (guard (e (#t (error-object-kind e))) (+ 1 (co/try-resume co))) kept))")), "(value-count (1 2))");
    // A coroutine that waits at a yield in the middle of an expression is closed, reset and failed from outside like any other.
    let waiting = "(define log '()) (define co (make-coroutine (lambda () (dynamic-wind (lambda () 0) (lambda () (+ 1 (co/yield 'y))) (lambda () (set! log (cons 'out log)))))))";
    assert_eq!(eval(&format!("{waiting} (co/resume co) (co/close co) (list (co/status co) log)")), "(dead (out))");
    assert_eq!(eval(&format!("{waiting} (co/resume co) (co/reset co (lambda () 'new)) (list (co/resume co) log)")), "(new (out))");
    assert_eq!(eval(&format!("{waiting} (co/resume co) (list (guard (e (#t e)) (co/resume-error co 'bad)) (co/status co) log)")), "(bad error (out))");
    assert_eq!(eval(&format!("{waiting} (co/resume co) (list (co/resume co 41) (co/status co) log)")), "(42 dead (out))");
}

/// A switch requested in tail position, by `co/try-resume`, or by a yield to the host comes back to the frames it left, as a plain `co/resume` in the middle of an expression does. The collector runs in between.
#[test]
fn switches_in_every_position_come_back_to_their_frames() {
    let mut arena = arena();
    let text = "(let ()
                  (define (churn n acc) (if (eqv? n 0) acc (churn (- n 1) (list n n n))))
                  (define (step co . args) (apply co/resume co args))
                  (define (tried co x) (co/try-resume co x))
                  (define (emit x) (co/yield x))
                  (define (down n x) (if (eqv? n 0) (emit x) (down (- n 1) x)))
                  (define (under n x) (if (eqv? n 0) (emit x) (+ 1 (under (- n 1) x))))
                  (define gen
                    (make-coroutine
                      (lambda (start)
                        (let loop ((i 0) (kept (list 0 \"0\")))
                          (let* ((sent (emit (list 'tail i kept)))
                                 (deep (under 300 (list 'deep sent)))
                                 (flat (down 300 (list 'flat deep))))
                            (if (eqv? i 30) (raise (list 'over flat)) (loop (+ i 1) (list flat (number->string i)))))))))
                  (let loop ((round 0) (good 0))
                    (let* ((mine (list round (number->string round)))
                           (tail (step gen 'first))
                           (garbage1 (churn 3000 0))
                           (deep (call-with-values (lambda () (co/try-resume gen (* round 2))) list))
                           (told (co/yield (list 'host round mine)))
                           (flat (call-with-values (lambda () (tried gen 3)) list))
                           (garbage2 (churn 3000 0))
                           (before (- round 1))
                           (expected (if (eqv? round 0) (list 0 \"0\") (list 'first (number->string before)))))
                      (if (and (equal? mine (list round (number->string round)))
                               (equal? tail (list 'tail round expected))
                               (equal? deep (list #t (list 'deep (* round 2))))
                               (equal? told (+ round 100))
                               (equal? flat (list #t (list 'flat 303))))
                          (if (eqv? round 30)
                              (list (+ good 1) (call-with-values (lambda () (tried gen 'last)) list) (co/status gen))
                              (loop (+ round 1) (+ good 1)))
                          (list 'bad round tail deep told flat)))))";
    let mut machine = machine(&mut arena, text);
    let mut told: Option<i64> = None;
    let mut hosted = Vec::new();
    let done = loop {
        let outcome = arena.step(|mc| {
            let outcome = if let Some(value) = told.take() { machine.resume(mc, &[Value::fixnum(value).unwrap()]) } else { machine.run(mc) };
            match outcome.unwrap() {
                Outcome::Paused => None,
                outcome => Some((matches!(outcome, Outcome::Yielded(_)), show_outcome(mc, Ok(outcome)))),
            }
        });
        match outcome.unwrap() {
            None => {}
            Some((true, yielded)) => {
                told = Some(100 + hosted.len() as i64);
                hosted.push(yielded);
            }
            Some((false, done)) => break done,
        }
    };
    assert_eq!((hosted.len(), done.as_str()), (31, "done (31 (#f (over last)) error)"));
    assert_eq!(hosted[7], "yielded ((host 7 (7 \"7\")))");
}

#[test]
fn switches_keep_their_place_in_call_traces() {
    let names = "(define (names e) (map car (error-object-traceback e))) (define (body) (+ 1 (error \"bad\")))";
    // The frames of a task that waits for a coroutine follow the coroutine's own in the trace.
    let waiting = "(define (runner co) (+ 1 (co/resume co))) (define (outer co) (+ 1 (runner co)))";
    assert_eq!(eval(&format!("{names} {waiting} (guard (e (#t (names e))) (outer (make-coroutine body)))")), "(body runner outer #f)");
    assert_eq!(eval(&format!("{names} {waiting} (define (late) (co/yield 1) (+ 1 (error \"late\"))) (define co (make-coroutine late)) (co/resume co) (guard (e (#t (names e))) (outer co))")), "(late runner outer #f)");
    // A resume in tail position leaves no entry, as a call in tail position leaves none.
    assert_eq!(eval(&format!("{names} (define (runner co) (co/resume co)) (define (outer co) (+ 1 (runner co))) (guard (e (#t (names e))) (outer (make-coroutine body)))")), "(body outer #f)");
    // `co/try-resume` returns the condition with the trace it had where it was raised. That holds too when the resume itself fails.
    let tried = "(define (try co) (call-with-values (lambda () (co/try-resume co)) (lambda (ok e) (list ok (names e))))) (define (outer co) (cons 'x (try co)))";
    assert_eq!(eval(&format!("{names} {tried} (outer (make-coroutine body))")), "(x #f (body try outer))");
    assert_eq!(eval(&format!("{names} {tried} (outer 5)")), "(x #f (try outer))");
    // More frames wait than a task leaves on its stack, so some are saved when it switches.
    let deep = "(define (deep n co) (if (eqv? n 0) (+ 1 (co/resume co)) (+ 1 (deep (- n 1) co))))";
    assert_eq!(eval(&format!("{names} {deep} (guard (e (#t (length (names e)))) (deep 300 (make-coroutine body)))")), "64");
    assert_eq!(eval(&format!("{deep} (deep 300 (make-coroutine (lambda () (co/yield 1) 5)))")), "302");
}

/// Coroutines that are resumed in turn each come back to what their frames held, however many take part. A few idle coroutines keep their frames in place and the rest are copied out, so the groups here are both smaller and larger than that number. Between groups, some coroutines are closed, some end, and some are left suspended.
#[test]
fn coroutines_run_in_turn_in_any_number() {
    let mut arena = arena();
    let text = "(let ()
                  (define (churn n acc) (if (eqv? n 0) acc (churn (- n 1) (list n n n))))
                  (define (make i rounds)
                    (make-coroutine
                      (lambda ()
                        (let loop ((round 0) (kept (list i \"x\")))
                          (if (eqv? round rounds)
                              'over
                              (begin (co/yield (list i round kept)) (loop (+ round 1) (list i (number->string round)))))))))
                  (define (rotate count rounds)
                    (let ((cos (let build ((i 0) (made '())) (if (eqv? i count) (reverse made) (build (+ i 1) (cons (make i (if (odd? i) rounds (+ rounds 5))) made))))))
                      (let loop ((round 0) (bad 0))
                        (if (eqv? round rounds)
                            (let finish ((rest cos) (i 0) (bad bad))
                              (cond ((null? rest) bad)
                                    ((odd? i) (finish (cdr rest) (+ i 1) (if (eq? (co/resume (car rest)) 'over) bad (+ bad 1))))
                                    ((eqv? (modulo i 4) 0) (co/close (car rest)) (finish (cdr rest) (+ i 1) bad))
                                    (else (finish (cdr rest) (+ i 1) bad))))
                            (loop (+ round 1)
                                  (let each ((rest cos) (i 0) (bad bad))
                                    (if (null? rest)
                                        (begin (churn 500 0) bad)
                                        (let ((got (co/resume (car rest))))
                                          (each (cdr rest) (+ i 1) (if (equal? got (list i round (if (eqv? round 0) (list i \"x\") (list i (number->string (- round 1)))))) bad (+ bad 1)))))))))))
                  (list (rotate 1 40) (rotate 2 40) (rotate 3 40) (rotate 4 40) (rotate 5 40) (rotate 6 40) (rotate 13 40) (rotate 2 40)))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "done (0 0 0 0 0 0 0 0)");
}

#[test]
fn an_ended_coroutine_is_closed_and_reset_where_it_is_asked() {
    let ended = "(define co (make-coroutine (lambda () 1))) (co/resume co)";
    let failed = "(define co (make-coroutine (lambda () (raise 'boom)))) (guard (e (#t e)) (co/resume co))";
    for made in [ended, failed] {
        // In the middle of an expression and in tail position, with values held in the frame around it.
        assert_eq!(eval(&format!("{made} (let ((kept (list 1 2))) (list (eq? co (co/reset co (lambda () 'again))) (co/status co) (co/resume co) (co/status co) kept))")), "(#t pending again dead (1 2))");
        assert_eq!(eval(&format!("{made} (define (renew thunk) (co/reset co thunk)) (define (shut) (co/close co)) (list (eq? co (renew (lambda (x) (+ x 1)))) (co/resume co 41) (begin (shut) (co/status co)) (eq? (shut) (if #f #f)))")), "(#t 42 dead #t)");
        // What is not a procedure is refused, and the coroutine stays as it was.
        assert_eq!(eval(&format!("{made} (define before (co/status co)) (list (guard (e (#t (error-object-kind e))) (co/reset co 5)) (eq? before (co/status co)))")), "(wrong-type #t)");
    }
    // A coroutine that ends and is reset over and over runs its newest body each time.
    assert_eq!(eval("(define co (make-coroutine (lambda () 0))) (let loop ((i 0) (sum 0)) (if (eqv? i 1000) sum (let ((got (co/resume co))) (co/reset co (lambda () (+ i 1))) (loop (+ i 1) (+ sum got)))))"), "499500");
}

/// Frames that were entered with marks, a guard or a handler switch to a coroutine and come back with them, at any depth. So does a coroutine that yields from such a frame, whether it is then resumed, failed, closed or reset.
#[test]
fn marks_and_guards_hold_across_switches() {
    let counter = "(define (gen) (make-coroutine (lambda () (let loop ((i 0)) (if (eqv? i 3) (raise 'boom) (begin (co/yield (list i (mark-value 'k 'none))) (loop (+ i 1))))))))";
    let marked = "(define (marked co) (call-with-mark 'k 'mine (lambda () (let ((got (co/resume co))) (list got (mark-value 'k 'none))))))
                  (define (deep n co) (if (eqv? n 0) (marked co) (cons n (deep (- n 1) co))))";
    assert_eq!(eval(&format!("{counter} {marked} (define co (gen)) (list (marked co) (length (deep 40 co)) (call-with-mark 'k 'outer (lambda () (let ((got (deep 40 co))) (list (length got) (mark-value 'k 'none))))) (guard (e (#t (list 'top e))) (deep 40 co)))")), "(((0 none) mine) 42 (42 outer) (top boom))");
    let guarded = "(define (guarded co) (guard (e (#t (list 'caught e (mark-value 'k 'none)))) (list 'ok (co/resume co) (mark-value 'k 'none))))
                   (define (deep n co) (if (eqv? n 0) (guarded co) (let ((got (deep (- n 1) co))) (if (pair? got) got #f))))
                   (define (outer co) (call-with-mark 'k 'outer (lambda () (let ((got (deep 40 co))) (list got (mark-value 'k 'none))))))";
    assert_eq!(eval(&format!("{counter} {guarded} (define co (gen)) (list (guarded co) (outer co) (outer co) (outer co))")), "((ok (0 none) none) ((ok (1 none) outer) outer) ((ok (2 none) outer) outer) ((caught boom outer) outer))");
    let handled = "(with-exception-handler (lambda (e) 'handled) (lambda () (let* ((first (co/resume co)) (second (co/resume co))) (list first second (guard (e (#t (list 'guarded e))) (co/resume co))))))";
    assert_eq!(eval(&format!("{counter} (define co (gen)) (define (tail-marked co) (call-with-mark 'k 'tail (lambda () (co/resume co)))) (list (tail-marked co) (mark-value 'k 'none) {handled})")), "((0 none) none ((1 none) (2 none) (guarded boom)))");
    let worker = "(define log '())
                  (define (worker) (call-with-mark 'k 'w (lambda () (dynamic-wind (lambda () 0) (lambda () (let dig ((n 40)) (if (eqv? n 0) (list (co/yield (mark-value 'k 'none)) (mark-value 'k 'none)) (cons n (dig (- n 1)))))) (lambda () (set! log (cons (mark-value 'k 'none) log)))))))
                  (define (started) (let ((co (make-coroutine worker))) (co/resume co) co))";
    assert_eq!(eval(&format!("{worker} (define co (started)) (list (length (co/resume co 'in)) (co/status co) log)")), "(42 dead (w))");
    assert_eq!(eval(&format!("{worker} (define co (started)) (list (guard (e (#t e)) (co/resume-error co 'bad)) (co/status co) log)")), "(bad error (w))");
    assert_eq!(eval(&format!("{worker} (define co (started)) (co/close co) (list (co/status co) log)")), "(dead (w))");
    assert_eq!(eval(&format!("{worker} (define co (started)) (co/reset co (lambda () 'fresh)) (list (co/resume co) log)")), "(fresh (w))");
}

/// A host answers each yield at once, in the same step, and ends the step only when a run says it paused. The lists of yielded values add up to more than the arena holds, and the program allocates nothing else that would make it pause. So this only works if the machine pauses for the collector when it is resumed. Each answer reaches its yield, also the ones given when the machine paused instead of going on.
#[test]
fn a_host_that_answers_yields_at_once_still_lets_the_collector_run() {
    let mut arena = arena();
    let text = "(let loop ((i 0) (bad 0))
                  (if (eqv? i 300000)
                      bad
                      (let ((got (co/yield i i i i)))
                        (loop (+ i 1) (if (eqv? got (+ i 1)) bad (+ bad 1))))))";
    let mut machine = machine(&mut arena, text);
    let (mut yields, mut pauses) = (0, 0);
    let mut answer = None;
    let done = loop {
        let done = arena.step(|mc| {
            loop {
                let outcome = match answer.take() {
                    Some(value) => machine.resume(mc, &[Value::fixnum(value).unwrap()]),
                    None => machine.run(mc),
                };
                match outcome.unwrap() {
                    Outcome::Yielded(_) => {
                        yields += 1;
                        answer = Some(yields);
                    }
                    Outcome::Paused => {
                        pauses += 1;
                        return None;
                    }
                    outcome => return Some(show_outcome(mc, Ok(outcome))),
                }
            }
        });
        if let Some(done) = done.unwrap() {
            break done;
        }
    };
    assert_eq!((done.as_str(), yields), ("done 0", 300000));
    assert!(pauses > 0, "expected the machine to pause for collections");
}

#[test]
fn tables_map_keys_to_values_in_the_order_they_were_added() {
    assert_eq!(eval("(define t (make-table)) (list (table? t) (table? '()) (table? (vector)) (table-length t) (table-ref t 'a) (table-ref t 'a 'none) (table-has? t 'a) (table-delete! t 'a))"), "(#t #f #f 0 #f none #f #f)");
    let filled = "(define t (make-table)) (table-set! t 'b 2) (table-set! t 'a 1) (table-set! t 'c 3)";
    assert_eq!(eval(&format!("{filled} (list t (table-length t) (table-ref t 'a) (table-has? t 'c) (table-has? t 'd))")), "(#table((b . 2) (a . 1) (c . 3)) 3 1 #t #f)");
    // Setting a key again keeps its place. Removing it and setting it again puts it last.
    assert_eq!(eval(&format!("{filled} (table-set! t 'b 20) (list (table->list t) (table-delete! t 'b) (table-delete! t 'b) (begin (table-set! t 'b 200) (table->list t)))")), "(((b . 20) (a . 1) (c . 3)) #t #f ((a . 1) (c . 3) (b . 200)))");
    assert_eq!(eval(&format!("{filled} (table-clear! t) (table-set! t 'z 26) (list t (table-length t))")), "(#table((z . 26)) 1)");
    // A stored `#f` is a value like any other: only `table-has?` tells it from a missing key.
    assert_eq!(eval("(define t (table 'off #f)) (list (table-ref t 'off 'none) (table-has? t 'off) (table-ref t 'on 'none) (table-has? t 'on))"), "(#f #t none #f)");
    // `table` takes keys and values in turn, and `make-table` can be told how many entries to make room for.
    assert_eq!(eval("(list (table) (table 'a 1 \"b\" 2 'a 3) (table-length (make-table 100)) (list->table '((x . 1) (y . 2))))"), "(#table() #table((a . 3) (\"b\" . 2)) 0 #table((x . 1) (y . 2)))");
    assert_eq!(eval("(define t (table 'a 1 'b 2 'c 3)) (list (table-keys t) (table-values t) (table->vector t) (table->list (table-copy t)))"), "((a b c) (1 2 3) #(a 1 b 2 c 3) ((a . 1) (b . 2) (c . 3)))");
    // Enough entries for the table to grow many times, added and removed in an order no hash would give.
    let many = "(define t (make-table))
                (let loop ((i 0)) (if (< i 3000) (begin (table-set! t (modulo (* i 7919) 3000) i) (loop (+ i 1)))))
                (let loop ((i 0)) (if (< i 3000) (begin (if (odd? i) (table-delete! t i)) (loop (+ i 1)))))
                (let loop ((keys (table-keys t)) (i 0) (in-order #t))
                  (if (null? keys)
                      (list (table-length t) i in-order (table-ref t 2998) (table-ref t 2999 'gone))
                      (loop (cdr keys) (+ i 1) (and in-order (eqv? (table-ref t (car keys)) (let find ((j 0)) (if (eqv? (modulo (* j 7919) 3000) (car keys)) j (find (+ j 1)))))))))";
    assert_eq!(eval(many), "(1500 1500 #t 2642 gone)");
}

#[test]
fn table_keys_are_the_same_by_value_or_by_identity() {
    // Strings by their characters, however they were made.
    let strings = "(define t (table \"id\" 1 \"a key that is too long to fit in a word\" 2))
                   (list (table-ref t (string-append \"i\" \"d\")) (table-ref t (string-append \"a key that is too long\" \" to fit in a word\")) (table-ref t \"ID\") (table-ref t 'id))";
    assert_eq!(eval(strings), "(1 2 #f #f)");
    // Numbers as `eqv?` has them: by value and exactness.
    let numbers = "(define t (table 1 'one 1.0 'one-inexact 1/2 'half (expt 2 100) 'big -0.0 'minus-zero))
                   (list (table-ref t 1) (table-ref t 1.0) (table-ref t (/ 2 4)) (table-ref t 0.5) (table-ref t (* (expt 2 50) (expt 2 50))) (table-ref t 0.0) (table-ref t (* -1.0 0.0)) (table-length t))";
    assert_eq!(eval(numbers), "(one one-inexact half #f big #f minus-zero 5)");
    // Symbols, characters, booleans and the empty list by what they are.
    let constants = "(define t (table 'a 1 #\\a 2 #t 3 #f 4 '() 5 (string->symbol \"b\") 6))
                     (list (table-ref t (string->symbol \"a\")) (table-ref t #\\a) (table-ref t #t) (table-ref t #f) (table-ref t '()) (table-ref t 'b) (table-ref t \"a\") (table-ref t #\\b))";
    assert_eq!(eval(constants), "(1 2 3 4 5 6 #f #f)");
    // Anything else by identity: a list, a vector, a procedure or a table is the key it is, whatever it holds.
    let identity = "(define p (list 1 2)) (define v (vector 1 2)) (define f (lambda (x) x)) (define inner (table 'k 1))
                    (define t (table p 'pair v 'vector f 'procedure inner 'table))
                    (set-car! p 9) (vector-set! v 0 9) (table-set! inner 'k 2)
                    (list (table-ref t p) (table-ref t v) (table-ref t f) (table-ref t inner) (table-ref t (list 9 2)) (table-ref t (vector 9 2)) (table-ref t (table 'k 2)) (table-ref t (lambda (x) x)))";
    assert_eq!(eval(&identity.replace("(set-car! p 9) ", "")), "(pair vector procedure table #f #f #f #f)");
}

#[test]
fn tables_are_walked_as_they_were_when_the_walk_began() {
    let walked = "(define t (table 'a 1 'b 2 'c 3)) (define seen '())
                  (table-for-each (lambda (key value) (set! seen (cons (list key value (table-length t)) seen)) (table-delete! t 'b) (table-set! t 'd 4) (table-set! t 'c 30)) t)
                  (list (reverse seen) (table->list t))";
    assert_eq!(eval(walked), "(((a 1 3) (b 2 3) (c 3 3)) ((a . 1) (c . 30) (d . 4)))");
    assert_eq!(eval("(define t (table 'n 1)) (table-update! t 'n (lambda (n) (+ n 1))) (table-update! t 'm (lambda (m) (+ m 1)) 10) (table-update! t 'seen (lambda (seen) (not seen))) (table->list t)"), "((n . 2) (m . 11) (seen . #t))");
    // A copy is a table of its own with the same entries in the same order.
    assert_eq!(eval("(define t (table 'a 1 'b 2)) (define u (table-copy t)) (table-set! u 'a 10) (table-set! t 'c 3) (list (table->list t) (table->list u) (eq? t u))"), "(((a . 1) (b . 2) (c . 3)) ((a . 10) (b . 2)) #f)");
}

#[test]
fn tables_are_equal_when_their_entries_are() {
    assert_eq!(eval("(list (equal? (table) (table)) (equal? (table 'a 1 'b 2) (table 'b 2 'a 1)) (equal? (table 'a 1) (table 'a 2)) (equal? (table 'a 1) (table 'b 1)) (equal? (table 'a 1) (table 'a 1 'b 2)) (equal? (table 'a 1) '((a . 1))))"), "(#t #t #f #f #f #f)");
    // Values are compared as `equal?` compares anything. Keys are matched as a table matches them.
    assert_eq!(eval("(list (equal? (table 'a (list 1 \"two\" (vector 3))) (table 'a (list 1 \"two\" (vector 3)))) (equal? (table 'a (table 'b (table 'c 1))) (table 'a (table 'b (table 'c 1)))) (equal? (table \"k\" 1) (table (string-append \"k\") 1)) (equal? (table (list 1) 1) (table (list 1) 1)))"), "(#t #t #t #f)");
    assert_eq!(eval("(define a (table 'x 1)) (define b (table 'x 1)) (list (eq? a b) (eqv? a b) (equal? a b) (eqv? a a) (begin (table-delete! b 'x) (table-set! b 'x 1) (equal? a b)))"), "(#f #f #t #t #t)");
    // Tables that hold themselves are compared without end only if `equal?` did not stop at what it has seen.
    assert_eq!(eval("(define a (table)) (define b (table)) (table-set! a 'self a) (table-set! b 'self b) (list (equal? a b) (begin (table-set! b 'more 1) (equal? a b)))"), "(#t #f)");
}

#[test]
fn table_procedures_say_what_was_wrong() {
    assert_eq!(uncaught("(table-ref 5 'a)"), "#<error table-ref: wrong type of argument 5 a #f>");
    assert_eq!(uncaught("(table-set! (vector) 'a 1)"), "#<error table-set!: wrong type of argument #() a 1>");
    assert_eq!(uncaught("(table-length \"t\")"), "#<error table-length: wrong type of argument \"t\">");
    assert_eq!(eval("(map (lambda (thunk) (guard (e (#t (list (error-object-kind e) (error-object-who e)))) (thunk))) (list (lambda () (table 'a)) (lambda () (make-table 'many)) (lambda () (make-table -1)) (lambda () (table-keys 5)) (lambda () (list->table '(1 2))) (lambda () (table-for-each car 5))))"), "((arity table) (wrong-type make-table) (out-of-range make-table) (wrong-type table->vector) (wrong-type car) (wrong-type table->vector))");
}

/// A table with many entries, with keys of every kind, is read back whole after the collector has run many times while it grew. Keys that are lists and vectors are found by identity, wherever the collector moved them.
#[test]
fn a_large_table_keeps_its_entries_through_collections() {
    let mut arena = arena();
    let text = "(let ()
                  (define t (make-table))
                  (define kept (make-vector 4000 #f))
                  (let fill ((i 0))
                    (if (< i 4000)
                        (let ((key (list i)))
                          (vector-set! kept i key)
                          (table-set! t key i)
                          (table-set! t i (number->string i))
                          (table-set! t (string-append \"key number \" (number->string i)) (list i i))
                          (table-set! t (string->symbol (string-append \"s\" (number->string i))) (* i 1.5))
                          (if (eqv? (modulo i 3) 0) (table-delete! t (- i 1)))
                          (fill (+ i 1)))))
                  (co/yield (table-length t))
                  (let check ((i 0) (bad 0))
                    (if (< i 4000)
                        (check (+ i 1)
                               (if (and (eqv? (table-ref t (vector-ref kept i)) i)
                                        (equal? (table-ref t i 'gone) (if (and (eqv? (modulo (+ i 1) 3) 0) (< (+ i 1) 4000)) 'gone (number->string i)))
                                        (equal? (table-ref t (string-append \"key number \" (number->string i))) (list i i))
                                        (eqv? (table-ref t (string->symbol (string-append \"s\" (number->string i)))) (* i 1.5))
                                        (not (table-has? t (list i))))
                                   bad
                                   (+ bad 1)))
                        (list bad (table-length t) (car (table-keys t)) (table-ref t (car (table-keys t)))))))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "yielded (14667)");
    arena.set_evacuate_all(true);
    arena.collect();
    arena.set_evacuate_all(false);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, true), "done (0 14667 (0) 0)");
}

/// The default prompt tag is a value of its own. A variable that holds it is not taken for one that was never defined, and it is written as a prompt tag.
#[test]
fn the_default_prompt_tag_is_a_value_of_its_own() {
    assert_eq!(eval("(define (late) later) (define later (default-continuation-prompt-tag)) (list (eq? (late) (default-continuation-prompt-tag)) (eq? later (if #f #f)) (late) (if later 'true 'false))"), "(#t #f #<prompt-tag> true)");
    // It is not the value an optional parameter has when no argument is passed for it.
    assert_eq!(eval("(define (tagged [tag (make-continuation-prompt-tag)]) (eq? tag (default-continuation-prompt-tag))) (list (tagged) (tagged (default-continuation-prompt-tag)))"), "(#f #t)");
}

/// A `table` call with constant keys takes its keys from a shape that every table of the call shares. The tables are separate tables in every way a program can see.
#[test]
fn tables_made_by_one_call_are_separate_tables() {
    let made = "(define (make n) (table 'id n 'name \"x\" 7 'seven))
                (define a (make 1)) (define b (make 2))
                (table-set! a 'id 10) (table-set! a 'extra #t) (table-delete! b 'name) (table-set! b 'name \"again\")
                (list (table->list a) (table->list b) (table->list (make 3)) (equal? (make 4) (make 4)) (eq? (make 4) (make 4)) (table-length (make 5)) (make 6))";
    assert_eq!(eval(made), "(((id . 10) (name . \"x\") (7 . seven) (extra . #t)) ((id . 2) (7 . seven) (name . \"again\")) ((id . 3) (name . \"x\") (7 . seven)) #t #f 3 #table((id . 6) (name . \"x\") (7 . seven)))");
    // The values are evaluated in order, and a table made in a loop does not see the changes made to the one before it.
    assert_eq!(eval("(define log '()) (define (note x) (set! log (cons x log)) x) (define t (table 'a (note 1) 'b (note 2) 'c (note 3))) (list (reverse log) (table->list t))"), "((1 2 3) ((a . 1) (b . 2) (c . 3)))");
    assert_eq!(eval("(let loop ((i 0) (seen '())) (if (eqv? i 3) (reverse seen) (let ((t (table 'count 0 'tag 'new))) (table-set! t 'count (+ i 1)) (table-delete! t 'tag) (table-set! t i i) (loop (+ i 1) (cons (table->list t) seen)))))"), "(((count . 1) (0 . 0)) ((count . 2) (1 . 1)) ((count . 3) (2 . 2)))");
    // A call whose keys cannot share a shape still makes its table: a key given twice, a key that is not a constant, and a key that is compared by identity.
    assert_eq!(eval("(define k 'c) (list (table->list (table 'a 1 'a 2 'b 3)) (table->list (table 'a 1 k 2)) (table-length (table '(1 2) 'x \"s\" 'y)) (table-length (table)))"), "(((a . 2) (b . 3)) ((a . 1) (c . 2)) 2 0)");
    assert_eq!(eval("(guard (e (#t (list (error-object-kind e) (error-object-who e)))) (table 'a 1 'b))"), "(arity table)");
    // Keys of every kind that is compared by value, read back by equal keys that are other objects.
    assert_eq!(eval("(define t (table \"a longer string, used as a key\" 1 2.5 2 #\\x 3 #t 4 (expt 10 30) 5 'sym 6)) (list (table-ref t (string-append \"a longer string, \" \"used as a key\")) (table-ref t (/ 5.0 2)) (table-ref t #\\x) (table-ref t #t) (table-ref t (* (expt 10 15) (expt 10 15))) (table-ref t 'sym) (table-ref t 2))"), "(1 2 3 4 5 6 #f)");
}

/// A variable that passed `null?`, `nil?` or `none?` is known to be that one value where the test held.
#[test]
fn a_variable_tested_for_one_value_is_that_value() {
    assert_eq!(eval("(define (which x) (cond ((nil? x) (if x 'true (list 'nil x))) ((none? x) (if x 'true (list 'none x))) ((null? x) (if x (list 'null x) 'false)) (else x))) (map which (list #nil #none '() #f 5))"), "((nil #nil) (none #none) (null ()) #f 5)");
}

#[test]
fn three_values_are_false() {
    // `#f`, `#nil` and `#none` are false in every conditional. Everything else is true, the empty list and void included.
    assert_eq!(eval("(map (lambda (x) (if x 'true 'false)) (list #f #nil #none #t 0 \"\" '() (vector) (if #f #f)))"), "(false false false true true true true true true)");
    assert_eq!(eval("(list (if #nil 1 2) (if #none 1 2) (not #nil) (not #none) (not #f) (not '()) (not 0))"), "(2 2 #t #t #t #f #f)");
    assert_eq!(eval("(list (cond (#nil 1) (#none 2) (else 3)) (when #none 'ran) (unless #nil 'ran) (do ((i 0 (+ i 1)) (seen '() (cons i seen))) ((if (eqv? i 2) 'stop #none) seen) i))"), "(3 #<void> ran (1 0))");
    // Each is a value of its own, written as it is read, and none of them is a boolean or the empty list.
    assert_eq!(eval("(list #nil #none '#nil (list 'a #none) (vector #nil))"), "(#nil #none #nil (a #none) #(#nil))");
    assert_eq!(eval("(list (eq? #nil #none) (eq? #nil #f) (eq? #none #f) (eqv? #nil #nil) (equal? #none #none) (eq? #nil '()) (equal? (list #nil) (list #none)))"), "(#f #f #f #t #t #f #f)");
    assert_eq!(eval("(map (lambda (x) (list (nil? x) (none? x) (boolean? x) (null? x) (symbol? x))) (list #nil #none #f '()))"), "((#t #f #f #f #f) (#f #t #f #f #f) (#f #f #t #f #f) (#f #f #f #t #f))");
    // `and` gives the first false value and `or` the last one, as they are. A procedure keeps the false value it is given.
    assert_eq!(eval("(list (and 1 #none 2) (and #nil 1) (and 1 2 #f) (and 1 2) (and) (or #nil 5) (or #none #nil) (or #f #none) (or))"), "(#none #nil #f 2 #t 5 #nil #none #f)");
    assert_eq!(eval("(define (first-or x y) (or x y)) (define (both x y) (and x y)) (list (first-or #nil #none) (first-or #none 1) (both #none 1) (both 1 #nil) (both 1 2))"), "(#none 1 #none #nil 2)");
    // Procedures that take a flag or an optional value take any false value for "no".
    assert_eq!(eval("(list (string-split \"a b  c\" #nil) (string-split \" a,b \" \",\" #:trim? #none) (string-replace \"aaa\" \"a\" \"b\" #:all? #nil))"), "((\"a\" \"b\" \"c\") (\" a\" \"b \") \"baa\")");
}

/// The compiler folds and reorders conditionals. With three false values it must not treat a false value as `#f`, and must still know what a test tells it.
#[test]
fn the_compiler_keeps_false_values_apart() {
    // In the branch where a variable is false it still holds the false value it had.
    assert_eq!(eval("(define (keep x) (if x 'true x)) (define (deep x) (if x 1 (if x 2 (list x)))) (list (map keep (list #f #nil #none 3)) (map deep (list #f #nil #none 3)))"), "((#f #nil #none true) ((#f) (#nil) (#none) 1))");
    // A comparison with `#f` holds for `#f` only, where `not` holds for all three.
    assert_eq!(eval("(define (is-false x) (eq? x #f)) (define (isnt x) (not x)) (define (pick x) (if (eq? x #f) 'f (if (eqv? #f x) 'f2 'other))) (list (map is-false (list #f #nil #none 0)) (map isnt (list #f #nil #none 0)) (map pick (list #f #nil #none)))"), "((#t #f #f #f) (#t #t #t #f) (f other other))");
    assert_eq!(eval("(define (which x) (cond ((eq? x #nil) 'nil) ((eqv? #none x) 'none) ((not x) 'false) (else 'true))) (map which (list #nil #none #f '()))"), "(nil none false true)");
    // A value known to be `#nil` or `#none` is known to be false, not true.
    assert_eq!(eval("(define (after-nil x) (if (nil? x) (if x 'true 'false) 'other)) (define (after-none x) (if (none? x) (if (not x) 'false 'true) 'other)) (list (map after-nil (list #nil #none 1)) (map after-none (list #nil #none 1)))"), "((false other other) (other false other))");
    // Constants fold to the right branch, alone and inside `and` and `or`.
    assert_eq!(eval("(define (f x) (list (if #nil x 'no) (if #none x 'no) (if (and x #nil) 1 2) (if (or #none x) 1 2) (if (not #nil) 1 2) (and #none x) (or #nil x)))  (list (f 5) (f #f))"), "((no no 2 1 1 #none 5) (no no 2 2 1 #none #f))");
    // `and` and `or` as tests take the same branches as they do as values.
    let tests = "(define (t a b) (list (if (and a b) 'yes 'no) (if (or a b) 'yes 'no) (if (and (car a) b) 'yes 'no) (if (not (and (car a) b)) 'yes 'no)))
                 (list (t (list 1) 2) (t (list #nil) 2) (t (list 1) #none) (t (list #f) #nil))";
    assert_eq!(eval(tests), "((yes yes yes no) (yes yes no yes) (no yes no yes) (no yes no yes))");
}

#[test]
fn tables_hold_false_values_like_any_other() {
    // A missing key reads as `#f`, or as the default it is given. A stored `#nil`, `#none` or `#f` is an entry.
    assert_eq!(eval("(define t (table 'a #nil 'b #none 'c #f)) (list t (table-length t) (table-ref t 'a 0) (table-ref t 'b 0) (table-ref t 'c 0) (table-ref t 'd) (table-ref t 'd #nil) (map (lambda (k) (table-has? t k)) '(a b c d)))"), "(#table((a . #nil) (b . #none) (c . #f)) 3 #nil #none #f #f #nil (#t #t #t #f))");
    assert_eq!(eval("(define t (table 'a 1)) (table-set! t 'a #nil) (table-set! t 'b #none) (list (table-has? t 'a) (table-ref t 'a 0) (table-keys t) (or (table-ref t 'limit) 50) (or (table-ref t 'b) 'none-is-false))"), "(#t #nil (a b) 50 none-is-false)");
    // They are keys by what they are, each its own.
    assert_eq!(eval("(define t (table #nil 1 #none 2 #f 3 '() 4)) (list (table-ref t #nil) (table-ref t #none) (table-ref t #f) (table-ref t '()) (table-length t))"), "(1 2 3 4 4)");
    assert_eq!(eval("(list (equal? (table 'a #none) (table 'a #none)) (equal? (table 'a #none) (table 'a #nil)) (equal? (table 'a #nil) (table)))"), "(#t #f #f)");
    assert_eq!(eval("(define t (table 'n 1)) (table-update! t 'n (lambda (n) (and n (+ n 1)))) (table-update! t 'm (lambda (m) (or m 'new))) (table-update! t 'k (lambda (k) k) #none) (table->list t)"), "((n . 2) (m . new) (k . #none))");
}

/// A read or a write with a constant key remembers where it found the key, and tries that place first. What it remembers is only a guess: the same code must give the right answer for any table, however its entries are laid out and however they change in between.
#[test]
fn table_reads_and_writes_with_constant_keys_follow_the_table() {
    let get = "(define (name t) (table-ref t 'name)) (define (id t) (table-ref t \"id\" 'none)) (define (seven t) (table-ref t 7 'none)) (define (rename! t v) (table-set! t 'name v))";
    // Tables with the key in different places, with other keys in its place, or without it, read one after the other by the same code.
    let layouts = "(define tables (list (table 'name 1 \"id\" 2 7 3) (table 7 30 \"id\" 20 'name 10) (table 'other 0 'name 100) (table 'name2 0 \"idx\" 0 8 0) (table) (table \"id\" 200 'pad 0 'pad2 0 'name 1000)))
                   (list (map name tables) (map id tables) (map seven tables) (map name (reverse tables)) (map name tables))";
    assert_eq!(eval(&format!("{get} {layouts}")), "((1 10 100 #f #f 1000) (2 20 none none none 200) (3 30 none none none none) (1000 #f #f 100 10 1) (1 10 100 #f #f 1000))");
    // One table whose entries move: keys before the one that is read are removed, the table grows and is made again, and the key itself is removed and set again.
    let moving = "(define t (table 'a 0 'b 0 'name 'first))
                  (define seen (list (name t)))
                  (define (note!) (set! seen (cons (name t) seen)))
                  (table-delete! t 'a) (note!)
                  (let fill ((i 0)) (if (< i 100) (begin (table-set! t i i) (fill (+ i 1))))) (note!)
                  (let empty ((i 0)) (if (< i 100) (begin (table-delete! t i) (empty (+ i 1))))) (note!)
                  (let fill ((i 100)) (if (< i 140) (begin (table-set! t i i) (fill (+ i 1))))) (note!)
                  (table-delete! t 'name) (note!)
                  (table-set! t 'name 'second) (note!)
                  (table-clear! t) (note!)
                  (rename! t 'third) (note!)
                  (reverse seen)";
    assert_eq!(eval(&format!("{get} {moving}")), "(first first first first first #f second #f third)");
    // Writes go to the entry of the key in whichever table they are given, and add it where it is missing.
    let writing = "(define tables (list (table 'name 1 'x 0) (table 'x 0 'name 2) (table 'x 0)))
                   (for-each (lambda (t) (rename! t (list 'new (table-length t)))) tables)
                   (for-each (lambda (t) (rename! t (list 'newer (table-ref t 'name)))) (reverse tables))
                   (map table->list tables)";
    assert_eq!(eval(&format!("{get} {writing}")), "(((name newer (new 2)) (x . 0)) ((x . 0) (name newer (new 2))) ((x . 0) (name newer (new 1))))");
    // The default is given only when the key is missing, and a false value that is stored is not the default.
    assert_eq!(eval("(define (limit t) (table-ref t 'limit 50)) (map limit (list (table) (table 'limit 5) (table 'limit #f) (table 'limit #nil) (table 'other 1)))"), "(50 5 #f #nil 50)");
    // What is not a table is refused by name, as without a constant key.
    assert_eq!(uncaught("(let () (define (name t) (table-ref t 'name)) (name (vector 1)))"), "#<error table-ref: wrong type of argument #(1) name #f>");
    assert_eq!(uncaught("(let () (define (rename! t) (table-set! t 'name 1)) (rename! 5))"), "#<error table-set!: wrong type of argument 5 name 1>");
}

/// A write with a constant key stores a new object in a table that has lived through collections. The collector must still see it.
#[test]
fn values_written_with_a_constant_key_survive_collections() {
    let mut arena = arena();
    let text = "(let ()
                  (define t (table 'held (list 0)))
                  (define (churn n acc) (if (eqv? n 0) acc (churn (- n 1) (list n n n))))
                  (define (hold! i) (table-set! t 'held (list i (number->string i))))
                  (let loop ((i 0) (bad 0))
                    (if (eqv? i 200)
                        bad
                        (begin
                          (hold! i)
                          (churn 2000 0)
                          (loop (+ i 1) (if (equal? (table-ref t 'held) (list i (number->string i))) bad (+ bad 1)))))))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(run_to_outcome(&mut arena, &mut machine, false), "done 0");
}

#[test]
fn vectors_are_walked_and_mapped_by_index() {
    assert_eq!(eval("(define seen '()) (vector-for-each (lambda (x) (set! seen (cons x seen))) (vector 1 2 3)) (list seen (vector-for-each car (vector)) (vector-for-each car #()))"), "((3 2 1) #<void> #<void>)");
    assert_eq!(eval("(list (vector-map (lambda (x) (* x x)) (vector 1 2 3)) (vector-map car #()) (vector-map (lambda (x) x) #(a \"b\" #\\c)))"), "(#(1 4 9) #() #(a \"b\" #\\c))");
    // With several vectors the procedure takes an element of each, up to the length of the shortest.
    assert_eq!(eval("(define seen '()) (vector-for-each (lambda (a b c) (set! seen (cons (list a b c) seen))) (vector 1 2 3) #(x y) (vector \"p\" \"q\" \"r\" \"s\")) (reverse seen)"), "((1 x \"p\") (2 y \"q\"))");
    assert_eq!(eval("(list (vector-map + #(1 2 3) #(10 20 30)) (vector-map list #(1 2 3) #(a b)) (vector-map + #(1 2) #() #(5)))"), "(#(11 22 33) #((1 a) (2 b)) #())");
    // The result of a map is a new vector that can be written to, and the calls are made from the first index on.
    assert_eq!(eval("(define v (vector 1 2 3)) (define order '()) (define m (vector-map (lambda (x) (set! order (cons x order)) (+ x 1)) v)) (vector-set! m 0 'changed) (list v m order (eq? v m))"), "(#(1 2 3) #(changed 3 4) (3 2 1) #f)");
    // What is not a vector is refused by the operation that reads it, and an error in the procedure passes through.
    assert_eq!(eval("(map (lambda (thunk) (guard (e (#t (list (error-object-kind e) (error-object-who e)))) (thunk))) (list (lambda () (vector-for-each car '(1 2))) (lambda () (vector-map car 5)) (lambda () (vector-map car #(1))) (lambda () (vector-for-each (lambda (a b) a) #(1) 'x))))"), "((wrong-type vector-length) (wrong-type vector-length) (wrong-type car) (wrong-type vector-length))");
    // A long vector is walked without deep recursion.
    assert_eq!(eval("(define v (make-vector 100000 1)) (define sum 0) (vector-for-each (lambda (x) (set! sum (+ sum x))) v) (list sum (vector-length (vector-map (lambda (x) (+ x 1)) v)) (vector-ref (vector-map (lambda (x) (+ x 1)) v) 99999))"), "(100000 100000 2)");
}

#[test]
fn large_groups_of_mutually_recursive_closures_compile() {
    // Each procedure calls the next and captures `n`, so the group is one cycle of closures that escape.
    for size in [2, 16, 17, 20, 30, 31, 40] {
        let defines: String = (0..size).map(|i| format!("(define (f{i} k) (if (= k 0) (+ n {i}) (f{} (- k 1))))", (i + 1) % size)).collect();
        let all: String = (0..size).map(|i| format!("f{i} ")).collect();
        let text = format!("(define (make n) {defines} (list {all})) ((car (make 100)) {})", size + 1);
        assert_eq!(eval(&text), "101", "{size}");
    }
}

#[test]
fn keyword_apply_and_procedure_keywords() {
    assert_eq!(eval("(keyword-apply (lambda (x #:b b #:a a) (list x a b)) '(#:a #:b) '(1 2) 0 '())"), "(0 1 2)");
    assert_eq!(eval("(keyword-apply list '() '() 1 '(2 3))"), "(1 2 3)");
    assert_eq!(eval("(call-with-values (lambda () (procedure-keywords (lambda (#:z z #:a [a 1]) z))) list)"), "((#:z) (#:a #:z))");
    assert_eq!(eval("(call-with-values (lambda () (procedure-keywords car)) list)"), "(() ())");
}

#[test]
fn match_takes_the_first_clause_that_matches() {
    assert_eq!(eval("(match 5 [1 'one] [5 'five] [_ 'other])"), "five");
    assert_eq!(eval("(match '(1 2) [(list a b c) 'three] [(list a b) (list b a)])"), "(2 1)");
    assert_eq!(eval("(match \"hi\" [\"no\" 1] [\"hi\" 2])"), "2");
    assert_eq!(eval("(list (match 'x ['x 1]) (match '() [() 2]) (match '#:k [#:k 3]) (match #(1 2) [#(1 2) 4]))"), "(1 2 3 4)");
    assert_eq!(eval("(match '(1 . 2) [(cons a b) (list a b)])"), "(1 2)");
    assert_eq!(eval("(match '(1 2 3 4) [(list-rest a b r) (list a b r)])"), "(1 2 (3 4))");
    assert_eq!(eval("(match (vector 1 2) [(vector a) 1] [(vector a b) (+ a b)])"), "3");
    assert_eq!(eval("(match '(1 (2 3)) [(list x (list y z)) (match x [1 (+ y z)])])"), "5");
    // A variable that occurs twice in a pattern matches, at its second occurrence, a value `equal?` to its first binding.
    assert_eq!(eval("(list (match '(1 1) [(list a a) 'same] [_ 'diff]) (match '(1 2) [(list a a) 'same] [_ 'diff]))"), "(same diff)");
    // Clauses are in tail position.
    assert_eq!(eval("(define (count n) (match n [0 'done] [n (count (- n 1))])) (count 100000)"), "done");
    assert_eq!(eval("(define (len l) (match l [() 0] [(cons _ r) (+ 1 (len r))])) (len '(1 2 3 4))"), "4");
}

#[test]
fn match_repeats_the_last_pattern_of_a_list() {
    assert_eq!(eval(r#"(match '("!ping" "a" "b") [(list "!ping" args ...) args])"#), r#"("a" "b")"#);
    assert_eq!(eval("(match '((1 2) (3 4)) [(list (list a b) ...) (list a b)])"), "((1 3) (2 4))");
    assert_eq!(eval("(match '(1 (2 3) (4 5)) [(list x (list ys zs) ...) (list x ys zs)])"), "(1 (2 4) (3 5))");
    assert_eq!(eval("(list (match '() [(list x ...) x]) (match '(1 . 2) [(list x ...) x] [_ 'improper]))"), "(() improper)");
    assert_eq!(eval("(match (vector 1 2) [(list x ...) x] [_ 'not-a-list])"), "not-a-list");
    assert_eq!(error("(match '(1 2) [(list x ... y) x])"), (Unsupported, "..."));
    assert_eq!(error("(match '(1 2) [(list ... x) x])"), (BadSyntax, "..."));
    assert_eq!(error("(match '(1 2) [(list a (list a ...)) a])"), (Duplicate, "a"));
}

#[test]
fn match_clauses_share_what_they_start_by_looking_at() {
    fn each(clauses: &str, values: &str) -> String {
        eval(&format!("(map (lambda (v) (match v {clauses})) '{values})"))
    }
    let lists = "[(list 1 a) (list 'one a)] [(list 2 a) (list 'two a)] [(cons x _) (list 'pair x)] [_ 'other]";
    assert_eq!(each(lists, "((1 5) (2 6) (3 7) (1 2 3) (2) 9)"), "((one 5) (two 6) (pair 3) (pair 1) (pair 2) other)");
    let vectors = "[(vector 1 b) (list 'one b)] [(vector a b) (list a b)] [(vector a) (list a)] [_ 'other]";
    assert_eq!(each(vectors, "(#(1 2) #(3 4) #(5) #(1 2 3) (1 2))"), "((one 2) (3 4) (5) other other)");
    let guarded = "[(list a b) #:when (> a b) 'more] [(list a b) (=> next) (if (eqv? a b) (next) 'less)] [(list _ _) 'same] [_ 'other]";
    assert_eq!(each(guarded, "((2 1) (1 2) (3 3) (1))"), "(more less same other)");
    // The variables of a pattern are bound in the body of the clause, not in the expressions inside the pattern. That includes the variables that an `or`
    // or a repeat binds.
    assert_eq!(eval("(let ([a 10]) (match '(1 2) [(list a (? (lambda (y) (> y a)))) 'more] [_ 'not]))"), "not");
    assert_eq!(eval("(let ([a 10]) (match '(1 2) [(list (or a a) (? (lambda (y) (> y a)))) 'more] [_ 'not]))"), "not");
    assert_eq!(eval("(let ([a 10]) (match '(((1)) 2) [(list (list (list a) ...) (? (lambda (y) (> y a)))) 'more] [_ 'not]))"), "not");
    assert_eq!(eval("(let ([a 10]) (match '(1 2) [(not (list a (? (lambda (y) (> y a))))) 'not-list] [_ 'list]))"), "not-list");
    assert_eq!(eval("(match '((1 2) (3)) [(list (or (list a _) (list a)) ...) a])"), "(1 3)");
    assert_eq!(eval("(match '(1 (2) (3)) [(or (list 0 (list a) ...) (list 1 (list a) ...)) a])"), "(2 3)");
    assert_eq!(eval("(map (lambda (v) (match v [(list (list (list a) ...) a) a] [_ 'no])) '((((1) (2)) (1 2)) (((1)) (2))))"), "((1 2) no)");
    assert_eq!(eval("(map (lambda (v) (match v [(list (or (list a _) a) a) a] [_ 'no])) '(((1 2) 1) (1 1) ((3 2) 1)))"), "(1 1 no)");
    assert_eq!(eval("(match '((1 2) (3 4)) [(list (list a b) ...) #:when (equal? a '(1 3)) b])"), "(2 4)");
}

#[test]
fn match_patterns_combine() {
    assert_eq!(eval("(list (match 4 [(? pair? n) 'pair] [n 'other]) (match '(1) [(? pair? (list n)) n]))"), "(other 1)");
    assert_eq!(eval("(match '(1 2) [(or (list a 1) (list a 2)) a])"), "1");
    assert_eq!(eval("(match 5 [(and n (not (? pair?) 3)) (list 'neither n)])"), "(neither 5)");
    assert_eq!(eval("(match 3 [(not 3) 'not-three] [_ 'three])"), "three");
    assert_eq!(eval("(match '(1 2) [(app length 2) 'two])"), "two");
    // As in Racket, `(== v same?)` matches `x` if `(same? v x)` is true.
    assert_eq!(eval("(list (match 7 [(== 7) 'seven]) (match 7 [(== 8 <) 'less] [_ 'not]) (match 7 [(== 8 >) 'more]))"), "(seven not more)");
    assert_eq!(error("(match '(1 2) [(or (list a) (list a b)) a])"), (BadSyntax, "(list a b)"));
    assert_eq!(error("(match 1 [`(a) 1])"), (Unsupported, "`(a)"));
    assert_eq!(error("(match 1 [(lister a) 1])"), (BadSyntax, "(lister a)"));
}

#[test]
fn match_guards_and_escapes_go_on_to_the_next_clause() {
    assert_eq!(eval("(map (lambda (n) (match n [n #:when (> n 10) 'big] [n 'small])) '(5 50))"), "(small big)");
    assert_eq!(eval("(match 5 [n (=> skip) (if (eqv? n 5) (skip) 'kept)] [_ 'skipped])"), "skipped");
    let caught = "(guard (e (#t (list (error-object-kind e) (error-object-message e) (error-object-irritants e)))) (match 9 [1 1]))";
    assert_eq!(eval(caught), r#"(error "match: no matching clause for" (9))"#);
    let none = "(guard (e (#t (error-object-irritants e))) (match 1))";
    assert_eq!(eval(none), "(1)");
    assert_eq!(error("(match 1 [x #:when])"), (BadSyntax, "[x #:when]"));
    assert_eq!(error("(match 1 [x])"), (BadSyntax, "[x]"));
}

#[test]
fn vm_faults_and_errors_are_error_objects() {
    fn caught(body: &str) -> String {
        eval(&format!(
            "(guard (e ((error-object? e) (list (error-object-kind e) (error-object-message e) (error-object-irritants e)))) {body})"
        ))
    }
    assert_eq!(caught("(car 1)"), r#"(wrong-type "wrong type of argument" (1))"#);
    assert_eq!(caught("(vector-ref (vector 1) 5)"), r#"(out-of-range "value out of range" (#(1) 5))"#);
    assert_eq!(caught("(/ 1 0)"), r#"(divide-by-zero "division by zero" (1 0))"#);
    assert_eq!(caught("(error \"bad thing\" 1 'two)"), r#"(error "bad thing" (1 two))"#);
    assert_eq!(caught("((lambda (x) x))"), r#"(arity "wrong number of arguments" (#<procedure> 0))"#);
    assert_eq!(eval("(list (error-object? 1) (guard (e (#t (error-object? e))) (car '())))"), "(#f #t)");
    assert_eq!(eval_in(&mut arena(), "(error \"no one\")"), Ok(Err(Fault::Error)));
    assert_eq!(caught("(utf8->string #u8(255))"), r#"(not-utf8 "invalid UTF-8" (#u8(255)))"#);
}

#[test]
fn marks_are_seen_inside_and_dropped_after() {
    let text = "(define (depth) (mark-value 'depth 0))
                (define (nest n) (if (eqv? n 0) (list (depth)) (call-with-mark 'depth (+ (depth) 1) (lambda () (cons (depth) (nest (- n 1)))))))
                (list (nest 3) (depth))";
    assert_eq!(eval(text), "((1 2 3 3) 0)");
    // A mark that is set in tail position replaces the mark of its frame, so a loop runs in
    // constant space.
    let tail = "(define (loop n) (if (eqv? n 0) (mark-value 'k #f) (call-with-mark 'k n (lambda () (loop (- n 1))))))
                (list (loop 100000) (call-with-mark 'k 'outer (lambda () (+ 0 (loop 3)))))";
    assert_eq!(eval(tail), "(1 1)");
    let syntax = "(define (loop n) (if (eqv? n 0) (mark-value 'k #f) (with-continuation-mark 'k n (loop (- n 1)))))
                  (list (loop 100000) (with-continuation-mark 'k 'a (list (mark-value 'k #f) (+ 0 (loop 2)))) (mark-value 'k 'none))";
    assert_eq!(eval(syntax), "(1 (a 1) none)");
    assert!(eval_in(&mut arena(), "(with-continuation-mark 'k 1)").is_err());
}

#[test]
fn handlers_set_for_a_call_are_put_back_when_it_returns() {
    // After the `with-exception-handler` call of a level returns, a raise in that level goes to the handler of the level outside it. The recursion is deep, so frames
    // overflow stack segments and are copied back. All of this happens again each time the continuation captured at the bottom is called.
    let text = "(define saved #f) (define count 0)
                (define (down n)
                  (if (eqv? n 0)
                      (+ (call/cc (lambda (k) (set! saved k) 0)) (raise-continuable 0))
                      (let ((r (with-exception-handler (lambda (e) n) (lambda () (down (- n 1))))))
                        (+ r (raise-continuable 0)))))
                (let ((r (with-exception-handler (lambda (e) 0) (lambda () (down 2000)))))
                  (set! count (+ count 1))
                  (if (eqv? count 3) (list r count) (saved 0)))";
    assert_eq!(eval(text), "(2001000 3)");
}

#[test]
fn guards_the_loop_cant_keep_in_a_frame_go_back_to_their_records() {
    // The inner loop installs a guard in the calling frame only when the request is a plain call
    // and the thunk is a closure that takes exactly no arguments. A thunk with a rest parameter, or
    // a guard installed through `apply`, is left to the outer loop, which keeps the guard in a
    // record on the continuation chain.
    let text = "(define log '()) (define (note x) (set! log (cons x log)))
                (define (f n) (if (eqv? n 0) (raise 'deep) (+ 1 (f (- n 1)))))
                (define (through-wind)
                  (%guard (lambda args (dynamic-wind (lambda () (note 'in)) (lambda () (f 3000)) (lambda () (note 'out))))
                          (lambda (e) (list 'caught e))))
                (list (through-wind)
                      (+ 1 (%guard (lambda args 5) (lambda (e) 'no)))
                      (apply %guard (list (lambda args (car 1)) (lambda (e) (error-object-kind e))))
                      (with-continuation-mark 'k 'v (list (%guard (lambda args (raise 1)) (lambda (e) (mark-value 'k e)))))
                      (let loop ((n 0)) (if (eqv? n 20000) n (loop (+ 1 (%guard (lambda args (car n)) (lambda (e) n))))))
                      (reverse log))";
    assert_eq!(eval(text), "((caught deep) 6 wrong-type (v) 20000 (in out))");
}

#[test]
fn guards_go_back_to_the_frames_they_were_set_in() {
    // Each level raises the value that its guard caught to the level outside it, and leaves a `dynamic-wind` extent on the way. The recursion is deep, so
    // frames overflow stack segments and are copied back. All of this happens again each time the continuation captured at the bottom
    // is called.
    let text = "(define saved #f) (define count 0) (define outs 0)
                (define (down n)
                  (if (eqv? n 0)
                      (raise (call/cc (lambda (k) (set! saved k) 0)))
                      (raise (guard (e (#t (+ e n)))
                               (dynamic-wind (lambda () #f) (lambda () (down (- n 1))) (lambda () (set! outs (+ outs 1))))))))
                (let ((r (guard (e (#t e)) (down 2000))))
                  (set! count (+ count 1))
                  (if (eqv? count 3) (list r count outs) (saved 0)))";
    assert_eq!(eval(text), "(2001000 3 6000)");
    let tail = "(define (safe x) (guard (e (#t 'caught)) (car x))) (list (safe 1) (safe '(a)))";
    assert_eq!(eval(tail), "(caught a)");
    let log = "(define log '()) (define (note x) (set! log (cons x log)))";
    let across = format!(
        "{log} (list (guard (e (#t (list 'g e)))
                       (call-with-continuation-prompt
                         (lambda () (dynamic-wind (lambda () (note 'in)) (lambda () (raise 'x)) (lambda () (note 'out))))))
                     (reverse log))"
    );
    assert_eq!(eval(&across), "((g x) (in out))");
    // A guard inside a composable continuation catches a value that is raised when the continuation is called.
    let mut arena = arena();
    let capture = "(define k #f)
                   (call-with-continuation-prompt
                     (lambda () (guard (e (#t (list 'caught (error-object-kind e))))
                                  (+ 1 (call-with-composable-continuation (lambda (c) (set! k c) 0))))))";
    assert_eq!(eval_in(&mut arena, capture), Ok(Ok("1".into())));
    assert_eq!(eval_in(&mut arena, "(list (k 1) (k 'a))"), Ok(Ok("(2 (caught wrong-type))".into())));
}

#[test]
fn winders_run_on_the_way_in_and_out() {
    let log = "(define log '()) (define (note x) (set! log (cons x log)))";
    fn wind(log: &str, body: &str) -> String {
        eval(&format!("{log} (let ((r {body})) (list r (reverse log)))"))
    }
    assert_eq!(wind(log, "(dynamic-wind (lambda () (note 'in)) (lambda () (note 'during) 'v) (lambda () (note 'out)))"), "(v (in during out))");
    let values = "(call-with-values (lambda () (dynamic-wind (lambda () 0) (lambda () (values 1 2)) (lambda () 3))) list)";
    assert_eq!(eval(values), "(1 2)");
    let escape = "(call/cc (lambda (k) (dynamic-wind (lambda () (note 'in)) (lambda () (k 'escaped) (note 'not)) (lambda () (note 'out)))))";
    assert_eq!(wind(log, escape), "(escaped (in out))");
    let inside = "(dynamic-wind (lambda () (note 'in)) (lambda () (call/cc (lambda (k) (note 'jump) (k 1)))) (lambda () (note 'out)))";
    assert_eq!(wind(log, inside), "(1 (in jump out))");
    let nested = "(call-with-continuation-prompt
                    (lambda ()
                      (dynamic-wind (lambda () (note 'a-in))
                                    (lambda () (dynamic-wind (lambda () (note 'b-in))
                                                             (lambda () (abort-current-continuation (default-continuation-prompt-tag) (lambda () 'aborted)))
                                                             (lambda () (note 'b-out))))
                                    (lambda () (note 'a-out)))))";
    assert_eq!(wind(log, nested), "(aborted (a-in b-in b-out a-out))");
    // The example from R7RS: a continuation that is captured inside the extent and called from outside re-enters the extent.
    let again = "(let ((path '()) (c #f))
                   (let ((add (lambda (s) (set! path (cons s path)))))
                     (dynamic-wind (lambda () (add 'connect))
                                   (lambda () (add (call/cc (lambda (c0) (set! c c0) 'talk1))))
                                   (lambda () (add 'disconnect)))
                     (if (eqv? (length path) 3) (c 'talk2) (reverse path))))";
    assert_eq!(eval(again), "(connect talk1 disconnect connect talk2 disconnect)");
    // Calling a composable continuation runs the `before` thunks of the winders that it holds.
    let mut arena = arena();
    let capture = format!(
        "{log} (define k #f)
         (call-with-continuation-prompt
           (lambda () (dynamic-wind (lambda () (note 'in))
                                    (lambda () (call-with-composable-continuation (lambda (c) (set! k c) 0)))
                                    (lambda () (note 'out)))))"
    );
    assert_eq!(eval_in(&mut arena, &capture), Ok(Ok("0".into())));
    assert_eq!(eval_in(&mut arena, "(list (+ 1 (k 5)) (reverse log))"), Ok(Ok("(6 (in out in out))".into())));
    // A guard that leaves the extent runs the `after` thunks before its clauses.
    let guarded = "(guard (e (#t (note (list 'caught e)) 'g))
                     (dynamic-wind (lambda () (note 'in)) (lambda () (raise 'x)) (lambda () (note 'out))))";
    assert_eq!(wind(log, guarded), "(g (in out (caught x)))");
}

#[test]
fn errors_no_handler_takes_run_the_afters_first() {
    let mut arena = arena();
    let log = "(define log '()) (define (note x) (set! log (cons x log)))";
    let failing = format!("{log} (dynamic-wind (lambda () (note 'in)) (lambda () (dynamic-wind (lambda () (note 'in2)) (lambda () (car 1)) (lambda () (note 'out2)))) (lambda () (note 'out)))");
    assert_eq!(eval_in(&mut arena, &failing), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena, "(reverse log)"), Ok(Ok("(in in2 out2 out)".into())));
    // In a coroutine, a yield runs no `after` thunk. A failure runs the `after` thunks before the value is raised again
    // where the coroutine was resumed.
    let co = format!(
        "{log} (define co (make-coroutine (lambda () (dynamic-wind (lambda () (note 'in)) (lambda () (co/yield 1) (car 1)) (lambda () (note 'out))))))
         (let* ((first (co/resume co)) (seen (reverse log))
                (second (guard (e (#t (list 'caught (error-object-kind e) (co/status co) (reverse log)))) (co/resume co))))
           (list first seen second))"
    );
    assert_eq!(eval(&co), "(1 (in) (caught wrong-type error (in out)))");
    let inside = "(co/resume (make-coroutine (lambda () (guard (e (#t (list 'inside e))) (raise 'x)))))";
    assert_eq!(eval(inside), "(inside x)");
    // `co/try-resume` returns the error of resuming a coroutine that is not pending, instead of raising it.
    let done = "(define co (make-coroutine (lambda () 1))) (co/resume co)
                (call-with-values (lambda () (co/try-resume co)) (lambda (ok e) (list ok (error-object-kind e))))";
    assert_eq!(eval(done), "(#f not-pending)");
    let values = "(call-with-values (lambda () (co/try-resume (make-coroutine (lambda () (values 1 2))))) list)";
    assert_eq!(eval(values), "(#t 1 2)");
}

#[test]
fn raising_in_a_loop_runs_in_constant_space() {
    fn text(rounds: u64) -> String {
        format!(
            "(let ((log 0))
                  (let loop ((i 0) (sum 0))
                    (if (eqv? i {rounds})
                        (list sum log)
                        (loop (+ i 1)
                              (+ sum (guard (e ((null? e) 0) ((pair? e) (car e)))
                                       (dynamic-wind (lambda () #f)
                                                     (lambda () (+ (with-exception-handler (lambda (e) 1) (lambda () (raise-continuable i)))
                                                                   (raise (list (vector-ref (vector 1) 0)))))
                                                     (lambda () (set! log (+ log 1))))))))))"
        )
    }
    assert_eq!(eval(&text(1000)), "(1000 1000)");
    // Run a loop that does not end, through enough pauses to see the amount of live memory settle.
    let mut arena = arena();
    let mut machine = machine(&mut arena, &text(u64::MAX >> 4));
    let mut live = Vec::new();
    for run in 1..=128 {
        if run % 8 == 0 {
            arena.collect();
            live.push(arena.used());
        }
        arena
            .step(|mc| match machine.run(mc).unwrap() {
                Outcome::Paused => {}
                Outcome::Raised(r) => panic!("{}", raised_text(mc, r)),
                other => panic!("{other:?}"),
            })
            .unwrap();
    }
    let (first, second) = live.split_at(live.len() / 2);
    assert!(second.iter().max() <= first.iter().max(), "live memory grows: {live:?}");
}

#[path = "macros.rs"]
mod macros;

#[path = "modules.rs"]
mod modules;

#[test]
fn faults_name_the_operation_and_what_it_was_given() {
    fn displayed(text: &str) -> String {
        arena().mutate(|mc| {
            let [thunk] = load_text(mc, text).unwrap()[..] else { panic!("one form") };
            let raised = run_raising(mc, thunk).expect_err("raised");
            ragwort_printer_scheme::to_string(mc, raised, ragwort_printer_scheme::Mode::Display, usize::MAX).unwrap()
        })
    }
    assert_eq!(displayed("(car 5)"), "car: wrong type of argument: 5");
    assert_eq!(displayed("(string-length \"abc\" 1)"), "wrong number of arguments: #<procedure string-length> 2");
    assert_eq!(displayed("(vector-ref (vector 1 2) 9)"), "vector-ref: value out of range: #(1 2) 9");
    assert_eq!(displayed("(+ \"two\" 1)"), "+: wrong type of argument: \"two\" 1");
    assert_eq!(displayed("(if (< 1 'x) 1 2)"), "<: wrong type of argument: 1 x");
    assert_eq!(displayed("(5 1 2)"), "not a procedure: 5");
    assert_eq!(displayed("((lambda (x) x) 1 2)"), "wrong number of arguments: #<procedure> 2");
    assert_eq!(displayed("(error \"bad thing\" \"a\" 'b)"), "bad thing: \"a\" b");
    assert_eq!(displayed("(error \"alone\")"), "alone");
    assert_eq!(uncaught("(error \"bad thing\" \"a\" 'b)"), "#<error \"bad thing\" \"a\" b>");
    // An operation in tail position, and one whose result a loop branches on, report the same way.
    assert_eq!(displayed("((lambda (x) (cdr x)) 7)"), "cdr: wrong type of argument: 7");
    assert_eq!(displayed("(let loop ([i 0]) (if (< i 'end) (loop (+ i 1)) i))"), "<: wrong type of argument: 0 end");
}

#[test]
fn procedures_are_named_for_what_they_are_bound_to() {
    assert_eq!(eval("(let () (define (greet x) x) greet)"), "#<procedure greet>");
    assert_eq!(eval("(let ([f (lambda (x) x)]) f)"), "#<procedure f>");
    assert_eq!(eval("(letrec ([even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))] [odd? (lambda (n) (if (= n 0) #f (even? (- n 1))))]) even?)"), "#<procedure even?>");
    assert_eq!(eval("(let loop ([i 0]) (if (< i 1) loop 0))"), "#<procedure loop>");
    assert_eq!(eval("(let () (define (opt a #:key [k 1]) a) opt)"), "#<procedure opt>");
    assert_eq!(eval("(lambda (x) x)"), "#<procedure>");
    assert_eq!(eval("(list car string-length)"), "(#<procedure car> #<procedure string-length>)");
    let top = "(define (greet a) a) (define (opt a #:key [k 1]) a) (struct point (x y)) (list greet opt point-x point (greet 1))";
    assert_eq!(eval_in(&mut arena(), top), Ok(Ok("(#<procedure greet> #<procedure opt> #<procedure point-x> #<procedure point> 1)".into())));
    // An arity error names the procedure that was called.
    assert_eq!(uncaught("(let () (define (greet a) a) (greet 1 2))"), "#<error wrong number of arguments #<procedure greet> 2>");
    assert_eq!(uncaught("((lambda (x) x))"), "#<error wrong number of arguments #<procedure> 0>");
}

#[test]
fn errors_record_the_calls_in_progress() {
    let names = "(guard (e (#t (map car (error-object-traceback e))))";
    fn traced(text: String) -> Result<Result<String, Fault>, Error> {
        eval_in(&mut arena(), &text)
    }
    let fault = "(define (inner x) (vector-ref x 9)) (define (middle x) (+ 1 (inner x))) (define (outer x) (+ 1 (middle x)))";
    assert_eq!(traced(format!("{fault} {names} (outer (vector 1)))")), Ok(Ok("(inner middle outer #f)".into())));
    let raised = "(define (inner x) (+ 1 (error \"bad\" x))) (define (outer x) (+ 1 (inner x)))";
    assert_eq!(traced(format!("{raised} {names} (outer 5))")), Ok(Ok("(inner outer #f)".into())));
    // Each entry is `(name file line)`: the line is that of the call or operation in progress in the procedure, and the file is `#f` for source without a name. A call in tail position leaves no entry.
    assert_eq!(traced("(error-object-traceback (guard (e (#t e)) (car 1)))".into()), Ok(Ok("((#f #f 1) (#f #f 1))".into())));
    let lines = "(define (inner x)\n  (car x))\n\n(define (outer x)\n  (+ 1 (inner x)))\n(guard (e (#t (error-object-traceback e)))\n  (outer 5))";
    assert_eq!(traced(lines.into()), Ok(Ok("((inner #f 2) (outer #f 5) (#f #f 6))".into())));
    assert_eq!(traced(format!("(define (inner x) (car x)) (define (outer x) (inner x)) {names} (outer 5))")), Ok(Ok("(inner #f)".into())));
    // A guard that matches no clause raises the condition again, which keeps the trace of where it was first raised.
    let again = "(define (inner x) (car x)) (define (outer x) (+ 1 (inner x)))";
    assert_eq!(traced(format!("{again} {names} (guard (e2 ((string? e2) 'no)) (outer 5)))")), Ok(Ok("(inner outer #f #f)".into())));
    // The trace continues through `dynamic-wind` and into the procedure that resumed a coroutine.
    let wound = "(define (work x) (+ 1 (car x))) (define (via) (+ 1 (dynamic-wind (lambda () 1) (lambda () (+ 1 (work 5))) (lambda () 2))))";
    assert_eq!(traced(format!("{wound} {names} (via))")), Ok(Ok("(work #f dynamic-wind via #f)".into())));
    let resumed = "(define (work x) (+ 1 (car x))) (define (step) (+ 1 (work 5))) (define (drive co) (+ 1 (co/resume co)))";
    assert_eq!(traced(format!("{resumed} {names} (drive (make-coroutine step)))")), Ok(Ok("(work step drive #f)".into())));
    assert_eq!(uncaught("(error-object-traceback 5)"), "#<error error-object-traceback: wrong type of argument 5>");
}

#[test]
fn a_host_reads_the_trace_of_a_raised_condition() {
    fn trace_of(text: &str) -> ragwort_vm::report::Trace {
        arena().mutate(|mc| {
            let mut raised = None;
            for &thunk in &load_text(mc, text).unwrap() {
                raised = run_raising(mc, thunk).err();
            }
            ragwort_vm::report::trace(mc, raised.expect("raised"))
        })
    }
    let trace = trace_of("(define (f x) (+ 1 (car x))) (+ 1 (f 1))");
    let seen: Vec<(Option<&str>, bool)> = trace.contexts.iter().map(|context| (context.procedure.as_deref(), context.top_level)).collect();
    assert_eq!(seen, [(Some("f"), false), (None, true)]);
    assert!(!trace.truncated);
    // A call stack deeper than the trace records keeps its innermost calls.
    let deep = trace_of("(define (deep n) (if (= n 0) (car n) (+ 1 (deep (- n 1))))) (deep 200)");
    assert!(deep.truncated);
    assert_eq!(deep.contexts.len(), 64);
    assert!(deep.contexts.iter().all(|context| context.procedure.as_deref() == Some("deep")));
    // A value that is not a condition has no trace.
    assert_eq!(trace_of("(raise 'plain)"), ragwort_vm::report::Trace::default());
}

#[test]
fn a_guard_can_opt_out_of_call_traces() {
    let inner = "(define (inner x) (+ 1 (car x)))";
    let quiet = format!("{inner} (guard (e #:no-traceback (#t (list (error-object-message e) (error-object-traceback e)))) (+ 1 (inner 5)))");
    assert_eq!(eval_in(&mut arena(), &quiet), Ok(Ok("(\"wrong type of argument\" ())".into())));
    let traced = format!("{inner} (guard (e (#t (map car (error-object-traceback e)))) (+ 1 (inner 5)))");
    assert_eq!(eval_in(&mut arena(), &traced), Ok(Ok("(inner #f #f)".into())));
    // A quiet guard that matches no clause raises the condition again from its own context, so the trace an outer guard sees starts there.
    let mid = "(define (mid) (+ 1 (guard (e2 #:no-traceback ((string? e2) 'no)) (+ 1 (inner 5)))))";
    let outer = format!("{inner} {mid} (guard (e (#t (map car (error-object-traceback e)))) (+ 1 (mid)))");
    assert_eq!(eval_in(&mut arena(), &outer), Ok(Ok("(mid #f #f)".into())));
    assert_eq!(eval_in(&mut arena(), "(guard (e #:no-traceback) (car 1))"), Ok(Err(Fault::WrongType)));
    assert_eq!(eval("(guard (e #:no-traceback ((symbol? e) (list 'caught e))) (raise 'boom))"), "(caught boom)");
    assert_eq!(eval("(let loop ([i 0] [acc 0]) (if (< i 1000) (loop (+ i 1) (+ acc (guard (e #:no-traceback (#t 1)) (car i)))) acc))"), "1000");
}

/// Runs the forms of `text` until one raises, and passes the report of what it raised to `check`.
fn reported(text: &str, check: impl for<'gc> FnOnce(&Mutation<'gc>, ragwort_vm::report::Report<'gc>)) {
    arena().mutate(|mc| {
        let mut raised = None;
        for &thunk in &load_text(mc, text).unwrap() {
            if let Err(value) = run_raising(mc, thunk) {
                raised = Some(value);
                break;
            }
        }
        check(mc, ragwort_vm::report::Report::of(mc, raised.expect("raised")));
    });
}

#[test]
fn a_host_matches_on_what_was_raised() {
    use ragwort_types::num::NumError;
    use ragwort_vm::report::{Raised, procedure_name};

    reported("(car 5)", |mc, report| {
        let Raised::WrongType { operation: Some(operation), operands } = report.error else { panic!("{:?}", report.error) };
        assert_eq!((operation.name(), show(mc, operands)), ("car", "(5)".to_string()));
    });
    reported("(vector-ref (vector 1) 9)", |mc, report| {
        let Raised::OutOfRange { operation: Some(operation), operands } = report.error else { panic!("{:?}", report.error) };
        assert_eq!((operation.name(), show(mc, operands)), ("vector-ref", "(#(1) 9)".to_string()));
    });
    reported("(/ 1 0)", |_, report| assert!(matches!(report.error, Raised::Number { error: NumError::DivideByZero, operation: Some(_), .. })));
    reported("(define (f a) a) (+ 1 (f 1 2))", |mc, report| {
        let Raised::Arity { operation: None, procedure: Some(procedure), given: 2 } = report.error else { panic!("{:?}", report.error) };
        assert_eq!(procedure_name(mc, procedure).map(|name| show(mc, name.value(mc))), Some("f".to_string()));
    });
    reported("(car)", |_, report| assert!(matches!(report.error, Raised::Arity { procedure: Some(_), given: 0, .. })));
    // A receiving call reports how many values it passed to its consumer.
    reported("(define three (car (list (lambda () (values 1 2 3))))) (define (f a b) a) (+ 1 (call-with-values three f))", |mc, report| {
        let Raised::Arity { operation: None, procedure: Some(procedure), given: 3 } = report.error else { panic!("{:?}", report.error) };
        assert_eq!(procedure_name(mc, procedure).map(|name| show(mc, name.value(mc))), Some("f".to_string()));
    });
    reported("(define one (car (list (lambda () 1)))) (define (f a b) a) (call-with-values one f)", |_, report| {
        assert!(matches!(report.error, Raised::Arity { procedure: Some(_), given: 1, .. }), "{:?}", report.error);
    });
    reported("(define two (car (list (lambda () (values 1 2))))) (+ 1 (two))", |mc, report| {
        assert_eq!(report.error, Raised::ValueCount { received: Some(2) });
        assert_eq!(ragwort_printer_scheme::render(mc, &report, usize::MAX), "error: wrong number of values: 2");
    });
    reported("(5 1)", |mc, report| {
        let Raised::NotProcedure { value: Some(value) } = report.error else { panic!("{:?}", report.error) };
        assert_eq!(show(mc, value), "5");
    });
    reported("(define (g) later) (g) (define later 1)", |mc, report| {
        let Raised::Unbound { name: Some(name) } = report.error else { panic!("{:?}", report.error) };
        assert_eq!(show(mc, name.value(mc)), "later");
    });
    reported("(error \"bad\" 1 2)", |mc, report| {
        let Raised::Error { message, irritants } = report.error else { panic!("{:?}", report.error) };
        assert_eq!((show(mc, message), show(mc, irritants)), ("\"bad\"".to_string(), "(1 2)".to_string()));
    });
    reported("(raise 'plain)", |mc, report| {
        let Raised::Value(value) = report.error else { panic!("{:?}", report.error) };
        assert_eq!(show(mc, value), "plain");
        assert!(report.trace.contexts.is_empty());
        assert_eq!(ragwort_printer_scheme::render(mc, &report, usize::MAX), "uncaught: plain");
    });
    reported("(define (f x) (+ 1 (car x))) (define (g x) (+ 1 (f x))) (+ 1 (g 5))", |mc, report| {
        assert_eq!(ragwort_printer_scheme::render(mc, &report, usize::MAX), "error: car: wrong type of argument: 5\n  in f\n  in g");
    });
}

#[test]
fn scripts_read_which_operation_failed() {
    assert_eq!(eval("(guard (e (#t (error-object-who e))) (car 5))"), "car");
    assert_eq!(eval("(guard (e (#t (error-object-who e))) (vector-ref (vector) 1))"), "vector-ref");
    assert_eq!(eval("(guard (e (#t (error-object-who e))) (error \"mine\"))"), "#f");
    assert_eq!(eval("(guard (e (#t (error-object-who e))) ((lambda (x) x)))"), "#f");
    assert_eq!(uncaught("(error-object-who 'x)"), "#<error error-object-who: wrong type of argument x>");
}

#[test]
fn inlined_procedures_keep_their_place_in_a_trace() {
    let names = "(guard (e (#t (error-object-traceback e)))";
    fn traced(text: String) -> Result<Result<String, Fault>, Error> {
        eval_in(&mut arena(), &text)
    }
    // A local procedure called once is inlined into its caller, and still gets an entry with the line of the failed operation.
    let once = "(define (outer x)\n  (define (helper y)\n    (car y))\n  (+ 1 (helper x)))";
    assert_eq!(traced(format!("{once}\n{names}\n  (+ 1 (outer 5)))")), Ok(Ok("((helper #f 3) (outer #f 4) (#f #f 6) (#f #f 5))".into())));
    // So does a small procedure copied into each of its calls, and a procedure inlined inside another inlined one.
    let small = "(define (outer x)\n  (define (first y) (car y))\n  (+ (first x)\n     (first x)))";
    assert_eq!(traced(format!("{small}\n{names}\n  (+ 1 (outer 5)))")), Ok(Ok("((first #f 2) (outer #f 3) (#f #f 6) (#f #f 5))".into())));
    let nested = "(define (outer x)\n  (define (a y)\n    (define (b z)\n      (car z))\n    (+ 1 (b y)))\n  (+ 1 (a x)))";
    assert_eq!(traced(format!("{nested}\n{names}\n  (+ 1 (outer 5)))")), Ok(Ok("((b #f 4) (a #f 5) (outer #f 6) (#f #f 8) (#f #f 7))".into())));
    // A loop runs in its procedure's frame and reports that procedure, at the line that failed.
    let looped = "(define (outer x)\n  (let loop ([i 0])\n    (if (< i 2)\n        (loop (+ i 1))\n        (car x))))";
    assert_eq!(traced(format!("{looped}\n{names}\n  (+ 1 (outer 5)))")), Ok(Ok("((outer #f 5) (#f #f 7) (#f #f 6))".into())));
    // A host sees which entries were inlined, and the rendered report marks them.
    reported(&format!("{once}\n(+ 1 (outer 5))"), |mc, report| {
        let seen: Vec<_> = report.trace.contexts.iter().map(|context| (context.procedure.as_deref(), context.inlined, context.top_level, context.line)).collect();
        assert_eq!(seen, [(Some("helper"), true, false, 3), (Some("outer"), false, false, 4), (None, false, true, 5)]);
        assert_eq!(ragwort_printer_scheme::render(mc, &report, usize::MAX), "error: car: wrong type of argument: 5\n  in helper [inlined]\n  in outer");
    });
}

/// One `table-ref` in a procedure reads tables of several shapes in turn. It remembers a few shapes and still reads every table right when there are more shapes than it remembers.
#[test]
fn one_read_serves_tables_of_many_shapes() {
    let turns = "(define (id-of t) (table-ref t 'id 'none))
                 (define (make kind n)
                   (case kind
                     ((0) (table 'id n 'a 1))
                     ((1) (table 'a 1 'id n))
                     ((2) (table 'a 1 'b 2 'id n))
                     ((3) (table 'a 1 'b 2 'c 3 'id n))
                     ((4) (table 'a 1 'b 2 'c 3 'd 4 'id n))
                     ((5) (table 'x n))
                     (else (let ((t (make-table))) (table-set! t 'z 0) (table-set! t 'id n) t))))
                 (let loop ((n 0) (seen '()))
                   (if (eqv? n 21) (reverse seen) (loop (+ n 1) (cons (id-of (make (modulo n 7) n)) seen))))";
    assert_eq!(eval(turns), "(0 1 2 3 4 none 6 7 8 9 10 11 none 13 14 15 16 17 18 none 20)");
    // A write through one instruction, to tables of two shapes and to one that grows past its shape.
    let writes = "(define (bump! t) (table-set! t 'count (+ 1 (table-ref t 'count 0))))
                  (define a (table 'count 0 'name \"a\")) (define b (table 'name \"b\" 'count 10)) (define c (table 'name \"c\"))
                  (for-each (lambda (t) (bump! t) (bump! t)) (list a b c a b c))
                  (map table->list (list a b c))";
    assert_eq!(eval(writes), "(((count . 4) (name . \"a\")) ((name . \"b\") (count . 14)) ((name . \"c\") (count . 4)))");
}

/// Tables that get the same field names in the same order have one shape, whichever way a program builds them. A table that is used as a map has none.
#[test]
fn tables_built_in_different_ways_share_a_shape() {
    use ragwort_types::pair::Pairs;
    use ragwort_types::table::Table;
    let text = "(define (literal n) (table 'id n 'name \"x\"))
                (define (stepwise n) (let ((t (make-table))) (table-set! t 'id n) (table-set! t 'name \"x\") t))
                (define keys (list 'id 'name))
                (define (put! t k v) (table-set! t k v))
                (define (through-a-helper n) (let ((t (make-table))) (for-each (lambda (k) (put! t k n)) keys) (table-set! t 'name \"x\") t))
                (define (from-a-list n) (list->table (list (cons 'id n) (cons 'name \"x\"))))
                (define (copied n) (table-copy (literal n)))
                (define (computed n) (table (car keys) n (cadr keys) \"x\"))
                (define (grown n) (let ((t (table 'id n))) (table-set! t 'name \"x\") t))
                (define (updated n) (let ((t (literal 0))) (table-update! t 'id (lambda (old) (+ old n))) (table-set! t 'name \"x\") t))
                (define (mapped n) (let ((t (make-table))) (table-set! t (string-append \"i\" \"d\") n) (table-set! t 'name \"x\") t))
                (define (numbered n) (let ((t (make-table))) (table-set! t n n) t))
                (define (reordered n) (let ((t (make-table))) (table-set! t 'name \"x\") (table-set! t 'id n) t))
                (list (literal 1) (stepwise 2) (through-a-helper 3) (from-a-list 4) (copied 5) (computed 6) (grown 7) (updated 8) (mapped 9) (numbered 10) (reordered 11))";
    let mut arena = arena();
    arena.mutate(|mc| {
        let mut last = Value::VOID;
        for thunk in load_text(mc, text).unwrap() {
            last = run(mc, thunk).unwrap();
        }
        let tables: Vec<Table> = Pairs::new(mc).elements(last).map(|value| Table::of(value).unwrap()).collect();
        let shape = tables[0].shape(mc).expect("a table literal has a shape");
        assert_eq!(shape.len(mc), 2);
        for (number, table) in tables[..8].iter().enumerate() {
            assert_eq!((table.shape(mc), table.len(mc)), (Some(shape), 2), "table {number}");
        }
        // A key that is a computed string or number makes the table a map. Fields in another order have another shape.
        assert_eq!((tables[8].shape(mc), tables[9].shape(mc), tables[8].len(mc)), (None, None, 2));
        assert!(tables[10].shape(mc).is_some_and(|other| other != shape && other.len(mc) == 2));
    });
    // The tables read the same whichever way they were built.
    let listed = format!("{text} (map table->list (list (literal 1) (stepwise 2) (through-a-helper 3) (from-a-list 4) (copied 5) (computed 6) (grown 7) (updated 8) (mapped 9) (numbered 10) (reordered 11)))");
    assert_eq!(
        eval(&listed),
        "(((id . 1) (name . \"x\")) ((id . 2) (name . \"x\")) ((id . 3) (name . \"x\")) ((id . 4) (name . \"x\")) ((id . 5) (name . \"x\")) ((id . 6) (name . \"x\")) ((id . 7) (name . \"x\")) ((id . 8) (name . \"x\")) ((\"id\" . 9) (name . \"x\")) ((10 . 10)) ((name . \"x\") (id . 11)))"
    );
}

/// A table that is filled field by field behaves as any table does when it outgrows its shape or loses and regains keys.
#[test]
fn a_table_filled_field_by_field_is_an_ordinary_table() {
    // More fields than a shape holds, added by one loop and read back.
    assert_eq!(eval("(define t (make-table)) (define names (let loop ((i 0) (acc '())) (if (eqv? i 100) (reverse acc) (loop (+ i 1) (cons (string->symbol (string-append \"f\" (number->string i))) acc))))) (for-each (lambda (name) (table-set! t name name)) names) (list (table-length t) (equal? (table-keys t) names) (table-ref t 'f0) (table-ref t 'f63) (table-ref t 'f64) (table-ref t 'f99) (table-ref t 'f100))"), "(100 #t f0 f63 f64 f99 #f)");
    // A removed field that is set again becomes the last entry. Fields and map keys mix in one table.
    assert_eq!(eval("(define t (make-table)) (table-set! t 'a 1) (table-set! t 'b 2) (table-set! t 'c 3) (table-delete! t 'a) (define before (table->list t)) (table-set! t 'a 4) (table-set! t \"s\" 5) (table-set! t 'd 6) (table-delete! t 'b) (list before (table->list t) (table-length t) (table-has? t 'b))"), "(((b . 2) (c . 3)) ((c . 3) (a . 4) (\"s\" . 5) (d . 6)) 4 #f)");
    // Two tables built by the same code are equal and separate, and one write site serves tables at every stage of being filled.
    assert_eq!(eval("(define (make n) (let ((t (make-table))) (table-set! t 'n n) (when (even? n) (table-set! t 'even #t)) (table-set! t 'last n) t)) (define made (map make '(1 2 3 4))) (table-set! (car made) 'n 100) (list (map table->list made) (equal? (make 6) (make 6)) (eq? (make 6) (make 6)))"), "((((n . 100) (last . 1)) ((n . 2) (even . #t) (last . 2)) ((n . 3) (last . 3)) ((n . 4) (even . #t) (last . 4))) #t #f)");
}

