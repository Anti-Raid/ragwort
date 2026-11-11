use ragwort_compiler::module::NoModules;
use ragwort_types::gc::{Arena, Value};
use ragwort_types::pair::Pairs;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use super::*;
use crate::ExpandErrorKind::*;

/// Root 0 holds the symbol table, root 1 a list of the modules loaded, newest first, root 2 the
/// prelude's module, which has run, and root 3 the modules other modules can require, as a list
/// of `(name . module)`.
fn arena() -> Arena {
    arena_of(1 << 24)
}

/// An arena as [`arena`] makes, of `bytes`.
fn arena_of(bytes: usize) -> Arena {
    let mut arena = Arena::new(bytes, 4);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        mc.set_root(1, Value::NIL);
        mc.set_root(3, Value::NIL);
        let session = SyntaxSession::named(mc, "prelude", PRELUDE).unwrap();
        let loaded = ragwort_native::load(mc, symbols, PRELUDE_NAME, &[], &[&session], &mut NoModules).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        mc.set_root(2, Value::object(mc, loaded.module));
    });
    arena
}

/// Loads `text` as a module, which implicitly requires the modules loaded before it, as a REPL's
/// input does, and exports what it defines for those loaded after.
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
    run_raising(mc, thunk).map_err(|raised| *raised.downcast::<Condition>(mc).expect("a condition").fault(mc).unwrap())
}

/// The thunk's value, or what it raised that nothing caught.
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
        Some(c) => format!("{:?} {}", c.fault(mc), show(mc, c.irritants(mc))),
        None => show(mc, raised),
    }
}

/// What the one form `text` raised that nothing caught, written out.
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

/// The kind of expansion error `text` has, and the text where it is.
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
    assert_eq!(eval_in(&mut arena(), "(apply + (values 1 2))"), Ok(Err(Fault::WrongType)));
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
    // What a macro introduces means the base binding, whatever the code binds the same names to.
    assert_eq!(eval("(let ((if list) (begin 'no)) (cond (#f 1) (else 2)))"), "2");
    assert_eq!(eval("(let ((loop 5)) (do ((i 0 (+ i 1))) ((eqv? i 3) loop)))"), "5");
    assert_eq!(eval("(let ((cons #f) (memv #f)) (list `(1 ,(+ 1 1)) (case 2 ((2) 'two))))"), "((1 2) two)");
    // The code's own top-level definitions shadow the prelude's for it, but not for macros.
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
    // Every argument's checked, though the answer's known before it.
    assert_eq!(uncaught("(< 2 1 'x)"), "#<error WrongType>");
    assert_eq!(uncaught("(< 1+2i 2)"), "#<error WrongType>");
    assert_eq!(uncaught("(<)"), "#<error Arity>");
}

#[test]
fn powers_stay_exact_when_they_can() {
    let text = "(list (expt 2 100) (expt 2/3 3) (expt 2 -2) (expt 1.5 2) (expt 4 1/2) (expt 0 0) (expt 0.0 0) (expt -1 (expt 10 30))
                      (expt 1 (expt 10 30)) (expt 0+1i 2) (expt -8 1/3))";
    assert_eq!(eval(text), "(1267650600228229401496703205376 8/27 1/4 2.25 2 1 1 1 1 -1 1.0+1.732050807568877i)");
    assert_eq!(uncaught("(expt 0 -1)"), "#<error Num(DivideByZero)>");
    // A result too big for the arena is turned down before it's computed, which ends the run.
    arena().mutate(|mc| {
        let [thunk] = load_text(mc, "(expt 3 (expt 10 15))").unwrap()[..] else { panic!("one form") };
        assert_eq!(Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap().run(mc), Err(Fault::OutOfMemory));
        // And one that fits is charged for the work before it's done.
        let [thunk] = load_text(mc, "(expt 3 1000000)").unwrap()[..] else { panic!("one form") };
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        machine.set_fuel(10_000);
        assert_eq!(machine.run(mc), Err(Fault::OutOfFuel));
    });
    assert_eq!(uncaught("(expt 'x 2)"), "#<error WrongType>");
}

#[test]
fn integer_division_keeps_the_sign_it_should() {
    let text = "(list (quotient 17 5) (quotient -17 5) (remainder 17 -5) (remainder -17 5) (modulo -17 5) (modulo 17 -5) (modulo -15 5)
                      (quotient 17.0 5) (modulo -17 5.0) (remainder -0.0 3) (modulo 100000000000000000000 7) (quotient -100000000000000000000 3)
                      (remainder 4611686018427387903 -1) (quotient -4611686018427387904 -1))";
    assert_eq!(eval(text), "(3 -3 2 -2 3 -3 0 3.0 3.0 -0.0 2 -33333333333333333333 0 4611686018427387904)");
    assert_eq!(uncaught("(modulo 1 0)"), "#<error Num(DivideByZero)>");
    assert_eq!(uncaught("(remainder 1/2 3)"), "#<error Num(NotInteger)>");
    assert_eq!(uncaught("(quotient 1.5 1)"), "#<error Num(NotInteger)>");
    assert_eq!(uncaught("(modulo \"1\" 2)"), "#<error WrongType>");
}

#[test]
fn a_continuation_reentered_in_a_loop_sees_its_own_spilled_values() {
    // 60 values live across a `call/cc` in the loop's first pass, more than a frame's registers
    // hold. Re-entered once the loop has gone round again, that pass must see its own.
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
    assert_eq!(uncaught("(bitwise-and 1.0 2)"), "#<error WrongType>");
    assert_eq!(uncaught("(bit-field 5 3 1)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(bit-set? -1 5)"), "#<error OutOfRange>");
}

#[test]
fn bit_fields_wider_than_their_numbers_cost_no_more() {
    // Each would take a mask of 125 MB, far more than the arena has, if it made one.
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
    assert_eq!(uncaught("(logical-shift-right 1 -1 32)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(logical-shift-left 1 -1 32)"), "#<error OutOfRange>");
    for text in ["(logical-shift-right 5 40.0 32)", "(logical-shift-left 5 81/2 32)", "(logical-shift-right 5 40 2.5)", "(logical-shift-left 'x 40 32)"] {
        assert_eq!(uncaught(text), "#<error WrongType>", "{text}");
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
    // Long strings join into ropes, which count and compare as their characters.
    let long = "(define (grow s n) (if (eqv? n 0) s (grow (string-append s s \"!\") (- n 1))))
                (define s (grow \"ab\" 12))
                (list (string-length s) (equal? (string-append s \"z\") (string-append s \"z\")) (string-length (string-append s s)))";
    assert_eq!(eval(long), "(12287 #t 24574)");
    assert_eq!(uncaught("(string-append \"a\" 'b)"), "#<error WrongType>");
    assert_eq!(uncaught("(string-length 'a)"), "#<error WrongType>");
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
    assert_eq!(uncaught("(substring \"abc\" 2 1)"), "#<error Str(OutOfRange)>");
    assert_eq!(uncaught("(substring \"abc\" 0 4)"), "#<error Str(OutOfRange)>");
    assert_eq!(uncaught("(string-ref \"abc\" 3)"), "#<error Str(OutOfRange)>");
    assert_eq!(uncaught("(string-ref \"abc\" -1)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(string->list \"abc\" 2 1)"), "#<error Str(OutOfRange)>");
    // Every argument's checked, though the answer's known before it.
    assert_eq!(uncaught("(string<? \"b\" \"a\" 'c)"), "#<error WrongType>");
}

#[test]
fn characters_are_code_points() {
    let text = "(list (char? #\\a) (char? \"a\") (char->integer #\\a) (char->integer #\\🦀) (integer->char 955) (integer->char 1114111)
                      (char=? #\\a #\\a #\\a) (char=? #\\a #\\b) (char<? #\\a #\\b #\\é) (char<? #\\b #\\a) (char>? #\\c #\\b #\\a)
                      (char<=? #\\a #\\a) (char>=? #\\a #\\b) (char=? #\\x) (eqv? (string-ref \"λ\" 0) (integer->char 955)))";
    assert_eq!(eval(text), "(#t #f 97 129408 #\\λ #\\x10ffff #t #f #t #f #t #t #f #t #t)");
    // What the printer writes for unseen characters reads back.
    assert_eq!(eval("(list (char->integer #\\x10ffff) (char->integer #\\x200b) (string->list \"a\\x200b;\\xfeff;\"))"), "(1114111 8203 (#\\a #\\x200b #\\xfeff))");
    assert_eq!(uncaught("(integer->char 55296)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(integer->char 1114112)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(integer->char -1)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(char->integer \"a\")"), "#<error WrongType>");
    assert_eq!(uncaught("(char<? #\\b #\\a 'c)"), "#<error WrongType>");
}

#[test]
fn strings_join_with_a_separator() {
    let text = "(list (string-join '(\"a\" \"b\" \"c\")) (string-join '(\"a\" \"b\" \"c\") \", \") (string-join '()) (string-join '(\"solo\") \"-\")
                      (string-join '(\"<@\" \">\") \"user\") (string-join '(\"é\" \"🦀\") \"\"))";
    assert_eq!(eval(text), "(\"a b c\" \"a, b, c\" \"\" \"solo\" \"<@user>\" \"é🦀\")");
    let long = "(define (words n acc) (if (eqv? n 0) acc (words (- n 1) (cons (number->string n) acc))))
                (string-length (string-join (words 1000 '()) \", \"))";
    assert_eq!(eval(long), "4891");
    assert_eq!(uncaught("(string-join '(\"a\" b))"), "#<error WrongType>");
    assert_eq!(uncaught("(string-join '(\"a\" . \"b\"))"), "#<error WrongType>");
    assert_eq!(uncaught("(string-join '(\"a\") 'x)"), "#<error WrongType>");
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
    // Fixnums are written in place, the ends of the range included.
    let ends = "(list (number->string 0) (number->string 0 2) (number->string -1 16) (number->string 1234567) (number->string 12345678)
                      (number->string 4611686018427387903) (number->string -4611686018427387904 16) (number->string -4611686018427387904 2)
                      (number->string 4611686018427387904))";
    assert_eq!(
        eval(ends),
        "(\"0\" \"0\" \"-1\" \"1234567\" \"12345678\" \"4611686018427387903\" \"-4000000000000000\" \"-100000000000000000000000000000000000000000000000000000000000000\" \"4611686018427387904\")"
    );
    assert_eq!(uncaught("(number->string 10 3)"), "#<error OutOfRange>");
    assert_eq!(uncaught("(number->string 'x)"), "#<error WrongType>");
}

#[test]
fn symbols_and_strings_name_each_other() {
    let text = "(list (symbol? 'a) (symbol? \"a\") (symbol? '#:a) (string? \"a\") (string? 'a) (symbol->string 'abc) (eq? 'abc (string->symbol \"abc\"))
                      (string->symbol \"two words\") (eq? (string->symbol (symbol->string 'x)) 'x))";
    assert_eq!(eval(text), "(#t #f #f #t #f \"abc\" #t |two words| #t)");
    assert_eq!(uncaught("(symbol->string \"a\")"), "#<error WrongType>");
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
    assert_eq!(error("(car '(a #`(b #,c)) #`d)"), (Unsupported, "#`d"));
    assert_eq!(error("(cond (else 1) (#t 2))"), (BadSyntax, "(else 1)"));
    assert_eq!(error("(let ((x)) x)"), (BadSyntax, "(x)"));
    assert_eq!(error("()"), (BadSyntax, "()"));
    assert_eq!(error("(f . x)"), (BadSyntax, "(f . x)"));
    assert_eq!(error("else"), (BadSyntax, "else"));
    let deep = |n| format!("{}1{}", "(car ".repeat(n), ")".repeat(n));
    assert_eq!(eval_in(&mut arena(), &deep(20_000)), Ok(Err(Fault::WrongType)));
}

/// Source nested however deeply reads, expands, compiles and runs on a small stack.
#[test]
fn deep_source_runs_on_a_small_stack() {
    let n = 20_000;
    let nest = |open: &str, inner: &str| format!("{}{inner}{}", open.repeat(n), ")".repeat(n));
    let cases = vec![
        (nest("(car ", "1"), Err(Fault::WrongType)),
        // Each `let` adds scopes to all inside it, so their sets grow as they nest, as do those of
        // the `let`s a `list` pattern matches with.
        (format!("{}x{}", "(let ((x 1)) ".repeat(1000), ")".repeat(1000)), Ok("1".to_string())),
        (format!("(match 1 [{}x{} 2] [_ 3])", "(list ".repeat(1000), ")".repeat(1000)), Ok("3".to_string())),
        (format!("(car '{})", nest("(", "x")), Ok(nest("(", "x")[1..n * 2].to_string())),
        (format!("`{}", nest("(", ",(+ 1 2)")), Ok(nest("(", "3"))),
        (format!("(match 1 [{} 2] [_ 3])", nest("(not ", "_")), Ok("2".to_string())),
        (format!("(match 1 [{} 2] [_ 3])", nest("(and ", "x")), Ok("2".to_string())),
    ];
    let small = std::thread::Builder::new().stack_size(1 << 20).spawn(move || {
        let mut arena = arena_of(1 << 28);
        cases.into_iter().map(|(text, want)| (eval_in(&mut arena, &text), want)).find(|(got, want)| got.as_ref() != Ok(want))
    });
    let wrong = small.unwrap().join().unwrap();
    assert!(wrong.is_none(), "{:?}", wrong.map(|(got, _)| got.map(|r| r.map(|s| s.len()))));
}

/// Syntax of data that holds itself stops rather than going on forever: out of fuel if the
/// task has a little, or else once what it's made fills the arena.
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

/// A call of the prelude's `list` with more arguments than it inlines is a call, rather than
/// `cons`es nested as deep as it's long.
#[test]
fn long_calls_of_inlined_functions_compile() {
    let nums = (0..1000).map(|i| i.to_string()).collect::<Vec<_>>().join(" ");
    assert_eq!(eval(&format!("(length (list {nums}))")), "1000");
    assert_eq!(eval("(list 1 2 3)"), "(1 2 3)");
}

/// The rest lists of calls to the prelude's `+` are the loop's only garbage, and binding them
/// pauses the run for the collector, so it doesn't run out of room.
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
    // Past the fixnums, onto bignums, and back.
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
    let transcendental = "(list (exp 0) (log 1) (sin 0.0) (cos 0.0) (atan 1 1) (atan 0 1) (exp 1) (log 100 10))";
    assert_eq!(eval(transcendental), "(1 0 0.0 1.0 0.7853981633974483 0 2.718281828459045 2.0)");
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
    // The procedures are values too, and a call that doesn't fit one goes to it.
    assert_eq!(eval(&format!("{point} (list (map point-x (list (point 1 2) (point 3 4))) (apply point '(5 6)) (procedure? point?))")), "((1 3) #(struct:point 5 6) #t)");
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point 1)")), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x 1 2)")), Ok(Err(Fault::Arity)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x 5)")), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena(), &format!("{point} (point-x (vector 1 2))")), Ok(Err(Fault::WrongType)));
    // Code before the form calls what it defines once the form has run, and not before, as it
    // can't refer to it before.
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
    assert_eq!(error("(if 1 (struct point (x)) 2)"), (ExpandErrorKind::Definition, "(struct point (x))"));
}

#[test]
fn structs_equal_only_to_themselves() {
    let session = "(struct session (token [uses #:mutable]) #:identity-eq?)";
    let made = format!("{session} (define s (session \"tok\" 0)) (set-session-uses! s 3)
                        (list s (session? s) (session-token s) (session-uses s) (equal? s s) (equal? s (session \"tok\" 3)) (eqv? s s)
                              (equal? (list s) (list s)) (equal? (list s) (list (session \"tok\" 3))))");
    assert_eq!(eval(&made), r#"(#(struct:session "tok" 3) #t "tok" 3 #t #f #t #t #f)"#);
    // A subtype of such a type is one too, and one of another type can be declared one.
    let sub = format!("{session} (struct admin session (level)) (struct point (x)) (struct pinned point (y) #:identity-eq?)
                       (list (equal? (admin 1 2 3) (admin 1 2 3)) (equal? (point 1) (point 1)) (equal? (pinned 1 2) (pinned 1 2))
                             (let ((p (pinned 1 2))) (equal? p p)) (member (point 1) (list (point 2) (point 1))) (member (session 1 2) (list (session 1 2))))");
    assert_eq!(eval(&sub), "(#f #t #f #t (#(struct:point 1)) #f)");
    assert_eq!(eval("(define (f) (struct cell (v) #:identity-eq?) (define c (cell 7)) (list c (cell-v c) (equal? c (cell 7)) (equal? c c))) (f)"), "(#(struct:cell 7) 7 #f #t)");
    // It's matched and copied as any other is.
    assert_eq!(eval(&format!("{session} (match (session 1 2) [(session t u) (list t u)])")), "(1 2)");
    assert_eq!(eval(&format!("{session} (define s (session 1 2)) (list (struct-copy session s [uses 9]) (equal? s (struct-copy session s)))")), "(#(struct:session 1 9) #f)");
}

#[test]
fn struct_fields_are_guarded() {
    let account = "(struct account (id [balance #:mutable #:guard (lambda (v) (and (number? v) (>= v 0)))] [owner #:guard string?]))";
    let caught = |body: &str| eval(&format!("{account} (guard (e (#t (list (error-object-kind e) (error-object-message e) (error-object-irritants e)))) {body})"));
    assert_eq!(eval(&format!("{account} (define a (account 1 10 \"al\")) (set-account-balance! a 25) (list a (account-balance a))")), "(#(struct:account 1 25 \"al\") 25)");
    // The constructor, the setter and a copy all call the guard.
    assert_eq!(caught("(account 1 -5 \"al\")"), r#"(error "struct account: the guard of field balance rejected" (-5))"#);
    assert_eq!(caught("(account 1 5 'al)"), r#"(error "struct account: the guard of field owner rejected" (al))"#);
    assert_eq!(caught("(set-account-balance! (account 1 5 \"al\") 'lots)"), r#"(error "struct account: the guard of field balance rejected" (lots))"#);
    assert_eq!(caught("(struct-copy account (account 1 5 \"al\") [balance -2])"), r#"(error "struct account: the guard of field balance rejected" (-2))"#);
    assert_eq!(caught("(apply account '(1 -5 \"al\"))"), r#"(error "struct account: the guard of field balance rejected" (-5))"#);
    let fine = format!("{account} (define a (account 1 2 \"al\")) (set-account-balance! a 30)
                        (list a (struct-copy account a [owner \"bo\"]) (map account-id (list a)))");
    assert_eq!(eval(&fine), r#"(#(struct:account 1 30 "al") #(struct:account 1 30 "bo") (1))"#);
    // A subtype's constructor calls the guards of the fields it inherits, and its own.
    let savings = format!("{account} (struct savings account ([rate #:guard real?]))");
    assert_eq!(eval(&format!("{savings} (savings 1 10 \"al\" 0.5)")), r#"#(struct:savings 1 10 "al" 0.5)"#);
    let caught_sub = |body: &str| eval(&format!("{savings} (guard (e (#t (error-object-message e))) {body})"));
    assert_eq!(caught_sub("(savings 1 -10 \"al\" 0.5)"), r#""struct savings: the guard of field balance rejected""#);
    assert_eq!(caught_sub("(savings 1 10 \"al\" 'high)"), r#""struct savings: the guard of field rate rejected""#);
    assert_eq!(caught_sub("(set-account-balance! (savings 1 10 \"al\" 0.5) -1)"), r#""struct account: the guard of field balance rejected""#);
    // The guard is evaluated once, when the form runs, and called with each value in order.
    let order = "(define log '()) (define (note x) (set! log (cons x log)) #t)
                 (struct pair2 ([a #:guard (begin (note 'made-a) note)] [b #:guard (begin (note 'made-b) note)]))
                 (pair2 1 2) (pair2 3 4) (reverse log)";
    assert_eq!(eval(order), "(made-a made-b 1 2 3 4)");
    // In a body, each run of the body makes the type and its guards again.
    let local = "(define (accepts? make v) (guard (e (#t #f)) (make v) #t))
                 (define (make limit) (struct capped ([n #:guard (lambda (v) (< v limit))])) capped)
                 (list (accepts? (make 10) 5) (accepts? (make 3) 5))";
    assert_eq!(eval(local), "(#t #f)");
    let cell = "(define (f) (struct cell ([v #:mutable #:guard number?])) (define c (cell 1)) (set-cell-v! c 2) (guard (e (#t (list c 'rejected))) (set-cell-v! c 'x))) (f)";
    assert_eq!(eval(cell), "(#(struct:cell 2) rejected)");
    // A macro can't name the read `match` and `struct-copy` are made of, even with the scopes
    // of syntax a built-in macro introduced, which do reach the prelude's `car`.
    let borrowed = |name: &str, args: &str| {
        format!("{account} (define a (account 1 2 \"al\"))
                 (define-syntax borrow (lambda (stx) (syntax-case stx () [(_ t) (with-syntax ([f (datum->syntax #'t '{name})]) #'(f {args}))])))
                 (cond [1 => borrow])")
    };
    assert_eq!(eval(&borrowed("car", "'(1 2)")), "1");
    assert_eq!(error(&borrowed("struct-ref", "a struct:account 0")).0, ExpandErrorKind::Unbound);
    // Only the form's own procedures reach a guard, so nothing makes a struct or sets a field
    // without one being called.
    for name in ["make-struct-type", "make-struct", "struct-ref", "struct-set!", "struct-guarded?", "struct-field-guard", "struct-set-field-guard!", "make-struct-guard-error"] {
        assert_eq!(error(&format!("{account} ({name} struct:account 1 2 3)")), (ExpandErrorKind::Unbound, name), "{name}");
    }
    // A guard that isn't a procedure is an error when the form runs.
    assert_eq!(eval_in(&mut arena(), "(struct bad ([x #:guard 5]))"), Ok(Err(Fault::WrongType)));
    for (bad, at) in [
        ("(struct p ([x #:guard]))", "[x #:guard]"),
        ("(struct p ([x #:guard a #:guard b]))", "[x #:guard a #:guard b]"),
        ("(struct p ([x #:nope]))", "[x #:nope]"),
    ] {
        assert_eq!(error(bad), (ExpandErrorKind::BadSyntax, at), "{bad}");
    }
    // A guarded procedure is still one of the form's, which can't be assigned.
    assert_eq!(error("(struct p ([x #:guard number?])) (set! p car)"), (ExpandErrorKind::Immutable, "p"));
    assert_eq!(error("(define (f) (struct p ([x #:guard number?])) (set! p car) 1)"), (ExpandErrorKind::Immutable, "p"));
}

#[test]
fn sealed_structs_have_no_subtypes() {
    let sealed = "(struct leaf (v) #:sealed) (struct node (l r)) (struct last node (x) #:sealed) (list (leaf 1) (last 1 2 3) (node? (last 1 2 3)))";
    assert_eq!(eval(sealed), "(#(struct:leaf 1) #(struct:last 1 2 3) #t)");
    assert_eq!(error("(struct leaf (v) #:sealed) (struct more leaf (w))"), (ExpandErrorKind::BadSyntax, "leaf"));
    assert_eq!(error("(define (f) (struct leaf (v) #:sealed) (struct more leaf (w)) 1)"), (ExpandErrorKind::BadSyntax, "leaf"));
    assert_eq!(error("(struct leaf (v) #:sealed #:what)"), (ExpandErrorKind::BadSyntax, "#:what"));
}

#[test]
fn structs_in_bodies() {
    // Each time the body runs makes a new type.
    let made = "(define (make) (struct cell (v)) (cons (cell 1) cell?))
                (let ((a (make)) (b (make))) (list (car a) ((cdr a) (car a)) ((cdr b) (car a)) (equal? (car a) (car b))))";
    assert_eq!(eval(made), "(#(struct:cell 1) #t #f #f)");
    let local = "(let () (struct p (x [y #:mutable])) (define q (p 1 2)) (set-p-y! q 5) (list (p? q) (p-x q) (p-y q) (map p-x (list q)) (equal? q (p 1 5))))";
    assert_eq!(eval(local), "(#t 1 5 (1) #t)");
    let sub = "(struct point (x y))
               (define (f) (struct point3 point (z)) (struct point4 point3 (w)) (define q (point4 1 2 3 4)) (list q (point-y q) (point3-z q) (point4-w q) (point? q) (point3? (point 1 2))))
               (f)";
    assert_eq!(eval(sub), "(#(struct:point4 1 2 3 4) 2 3 4 #t #f)");
    assert_eq!(error("(define (f) (struct p (x)) (set! p-x car) 1)"), (ExpandErrorKind::Immutable, "p-x"));
    assert_eq!(error("(define (f) (struct p (x)) (define p? 1) 1)").0, ExpandErrorKind::Duplicate);
    assert_eq!(error("(define (f) (struct p (x))) (f)").0, ExpandErrorKind::NoExpression);
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
    assert_eq!(eval("(define (f v) (struct cell (a)) (match (cell v) [(cell (list x y)) (+ x y)] [(cell x) x])) (list (f '(1 2)) (f 5))"), "(3 5)");
    assert_eq!(error(&format!("{shapes} (match 1 [(point x) x])")), (ExpandErrorKind::BadSyntax, "(point x)"));
    assert_eq!(error("(match 1 [(nope x) x])"), (ExpandErrorKind::BadSyntax, "(nope x)"));

    let copied = format!("{shapes} (define p (point3 1 2 3))
        (list (struct-copy point3 p [z 30]) (struct-copy point3 p [x 10] [z 30] [y 20]) (struct-copy point p [y 5]) (struct-copy point3 p) p
              (secret-v (struct-copy secret (secret 1) [v 2])))");
    assert_eq!(eval(&copied), "(#(struct:point3 1 2 30) #(struct:point3 10 20 30) #(struct:point 1 5) #(struct:point3 1 2 3) #(struct:point3 1 2 3) 2)");
    assert_eq!(eval("(define (f) (struct cell (a b)) (struct-copy cell (cell 1 2) [b 3])) (f)"), "#(struct:cell 1 3)");
    // The values are made in the order they're written, after the struct.
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
    let types = format!("{shapes} (list (struct-type? struct:point) (struct-type? struct:point3) (struct-type? (point 1 2)) (struct-type? point) (struct-type? 'point)
                                    (let () (struct cell (v)) (struct-type? struct:cell)))");
    assert_eq!(eval(&types), "(#t #t #f #f #f #t)");
    // An instance gives the type it was made as, and its fields' values in the order the type
    // names them.
    let whole = format!("{shapes} (define q (point3 1 2 3))
        (list (eq? (struct-type q) struct:point3) (eq? (struct-type q) struct:point) (struct-type (point 1 2)) (struct->list q) (struct->list (session 'tok 'al))
              (struct-fields (struct-type q)) (let () (struct unit ()) (struct->list (unit))) (map struct->list (list (point 1 2))))");
    assert_eq!(eval(&whole), "(#t #f #<struct-type:point> (1 2 3) (tok al) (x y z) () ((1 2)))");
    // The list is a new one each time, of the fields as they are then.
    let cells = "(struct cell (label [value #:mutable])) (struct cell3 cell (extra) #:mutable)";
    let listed = format!("{cells} (define c (cell 'a 1)) (define before (struct->list c)) (set-cell-value! c 2) (list before (struct->list c) (eq? (struct->list c) (struct->list c)))");
    assert_eq!(eval(&listed), "((a 1) (a 2) #f)");
    let mutable = format!("{cells} (list (struct-field-mutable? struct:cell 0) (struct-field-mutable? struct:cell 1) (struct-field-mutable? struct:cell3 0)
                                      (struct-field-mutable? struct:cell3 1) (struct-field-mutable? struct:cell3 2))");
    assert_eq!(eval(&mutable), "(#f #t #f #t #t)");
    // Code that knows nothing of a struct's type writes it out by its fields' names.
    let by_name = format!("{shapes}
        (define (struct->alist s) (map cons (struct-fields (struct-type s)) (struct->list s)))
        (list (struct->alist (point3 1 2 3)) (struct->alist (session 'tok 'al)))");
    assert_eq!(eval(&by_name), "(((x . 1) (y . 2) (z . 3)) ((token . tok) (user . al)))");
    assert_eq!(eval("(define (f) (struct cell (a b)) (list (struct-fields struct:cell) (struct->list (cell 1 2)) (eq? (struct-type (cell 1 2)) struct:cell))) (f)"), "((a b) (1 2) #t)");
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
    // A character whose case maps to several stays itself.
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
    assert_eq!(eval_in(&mut arena(), "(make-bytevector 2 256)"), Ok(Err(Fault::WrongType)));
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
    assert_eq!(eval(round_trip), "(pending 3 pending 20 (1 2 10 x) finished #t #f)");
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
    // Each top-level form runs in a machine of its own, which has finished by the next.
    assert_eq!(eval("(define top (co/running)) (co/status top)"), "finished");
}

#[test]
fn a_yield_goes_to_what_resumed_the_coroutine() {
    let nested = "(define inner (make-coroutine (lambda () (co/yield 'i1) 'i-done)))
                  (define outer (make-coroutine (lambda ()
                                  (let* ((a (co/resume inner)) (s (co/status outer)) (b (co/yield a)) (c (co/resume inner)))
                                    (list s b c (co/status inner))))))
                  (let* ((first (co/resume outer)) (rest (co/resume outer 'sent))) (list first rest (co/status outer)))";
    assert_eq!(eval(nested), "(i1 (running sent i-done finished) finished)");
    let walk = "(define (walk n) (if (eqv? n 0) 0 (begin (co/yield n) (+ 1 (walk (- n 1))))))
                (define co (make-coroutine (lambda () (walk 20000))))
                (let loop ((sum 0))
                  (let ((v (co/resume co)))
                    (if (eq? (co/status co) 'finished) (list sum v) (loop (+ sum v)))))";
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
    assert_eq!(eval(prompt), "(in 6 finished)");
    let escape = "(define co (make-coroutine (lambda () (call/cc (lambda (k) (co/yield 'a) (k 'escaped) 'not)))))
                  (list (co/resume co) (co/resume co))";
    assert_eq!(eval(escape), "(a escaped)");
}

#[test]
fn suspended_frames_survive_being_moved_and_shared() {
    // A continuation captured in the coroutine, called again after each yield, with other
    // coroutines run in between on whatever segments are free.
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
    // One generator resumed in turn from the top and from inside another coroutine, so the
    // segment it leaves goes to each.
    let turns = "(define gen (make-coroutine (lambda () (let loop ((i 0)) (co/yield i) (loop (+ i 1))))))
                 (define other (make-coroutine (lambda () (let loop () (co/yield (co/resume gen)) (loop)))))
                 (let loop ((n 0) (top #t) (acc '()))
                   (if (eqv? n 6) (reverse acc) (loop (+ n 1) (not top) (cons (if top (co/resume gen) (co/resume other)) acc))))";
    assert_eq!(eval(turns), "(0 1 2 3 4 5)");
    // Frames over a prompt, and under marks, yielded from at a few depths.
    let deep = "(define (down d) (if (eqv? d 0) (co/yield 'bottom) (list d (down (- d 1)))))
                (define co (make-coroutine (lambda ()
                             (list (down 3) (call-with-continuation-prompt (lambda () (down 2))) (down 30)))))
                (let* ((a (co/resume co)) (b (co/resume co 'x)) (c (co/resume co 'y)) (d (co/resume co 'z)))
                  (list a b c (car d) (cadr d) (co/status co)))";
    assert_eq!(eval(deep), "(bottom bottom bottom (3 (2 (1 x))) (2 (1 y)) finished)");
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
    // Its failure goes on through a coroutine that resumed it unprotected, which fails too.
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

/// The one thunk `text` loads as, in a machine.
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

/// How a run that `first` starts ends, past any pauses for the collector.
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
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "yielded (1 a)");
    // What the coroutines hold stays alive while they wait.
    arena.collect();
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.resume(mc, &[Value::fixnum(10).unwrap()]))), "yielded (1 b)");
    arena.collect();
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.resume(mc, &[Value::fixnum(20).unwrap()]))), "done (10 20 (done 1))");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[]))), "Err(Finished)");
    // Plain `run` goes on from a yield with no values.
    let mut machine = self::machine(&mut arena, "(call-with-values (lambda () (co/yield 'x)) list)");
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "yielded x");
    assert_eq!(arena.mutate(|mc| settled(mc, &mut machine, |m| m.run(mc))), "done ()");
}

#[test]
fn a_coroutine_two_machines_resume_in_turn_is_copied_where_it_waits() {
    let mut arena = arena();
    // Each machine resumes the generator, then a coroutine of its own that suspends, which
    // copies the generator's frames if it waits in between, as it may have since run elsewhere.
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
    assert_eq!(seen, (0..8).map(|i| format!("yielded {i}")).collect::<Vec<_>>());
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
    let kept = |body: &str| {
        let mut arena = arena();
        let text = format!("(define keep (let loop ((i 0) (acc '())) (if (eqv? i 200) acc (loop (+ i 1) (cons {body} acc)))))");
        eval_in(&mut arena, &text).unwrap().unwrap();
        arena.collect();
        arena.collect();
        arena.used()
    };
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
    // A handler of a `raise` that returns raises an error under the handlers outside it.
    let returned = "(guard (e ((error-object? e) (list (error-object-message e) (error-object-irritants e))))
                      (with-exception-handler (lambda (e) 'ignored) (lambda () (raise 'boom))))";
    assert_eq!(eval(returned), r#"("exception handler returned" (boom))"#);
    // One that isn't a procedure is a fault, raised under the handlers outside it.
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
    // No clause matches: raised again, continuably, from the guard.
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
    let kind = |call: &str| eval(&format!("(guard (e (#t (error-object-kind e))) (define (f a [b 1]) a) {call})"));
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
    let caught = |text: &str| eval(&format!("(guard (e (#t (list (error-object-kind e) (error-object-irritants e)))) {text})"));
    assert_eq!(caught("((lambda (#:a a) a) #:b 1)"), "(keyword (#:b))");
    assert_eq!(caught("(let ([f (lambda (#:a a) a)]) (f))"), "(keyword (#:a))");
    assert_eq!(caught("(define (f #:a a) a) (f #:a 1 2)"), "(arity ())");
    assert_eq!(caught("(car #:a 1)"), "(keyword (#:a))");
    assert_eq!(caught("(keyword-apply list '(#:b #:a) '(1 2) '())"), "(keyword (#:a))");
    assert_eq!(error("(define (f #:k k) k) (set! f 1)"), (Immutable, "f"));
    assert_eq!(error("(let () (define (f #:k k) k) (set! f 1) 2)"), (Immutable, "f"));
    assert_eq!(error("(define (f #:k k) k) (f #:k 1 #:k 2)"), (Duplicate, "#:k"));
    assert_eq!(error("(lambda (#:k a #:k b) 1)"), (Duplicate, "#:k"));
    assert_eq!(error("(lambda (#:k) 1)"), (BadSyntax, "#:k"));
    assert_eq!(error("(car #:k)"), (BadSyntax, "#:k"));
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
    // A variable bound twice matches what's equal? to what it's bound to first.
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
    let each = |clauses: &str, values: &str| eval(&format!("(map (lambda (v) (match v {clauses})) '{values})"));
    let lists = "[(list 1 a) (list 'one a)] [(list 2 a) (list 'two a)] [(cons x _) (list 'pair x)] [_ 'other]";
    assert_eq!(each(lists, "((1 5) (2 6) (3 7) (1 2 3) (2) 9)"), "((one 5) (two 6) (pair 3) (pair 1) (pair 2) other)");
    let vectors = "[(vector 1 b) (list 'one b)] [(vector a b) (list a b)] [(vector a) (list a)] [_ 'other]";
    assert_eq!(each(vectors, "(#(1 2) #(3 4) #(5) #(1 2 3) (1 2))"), "((one 2) (3 4) (5) other other)");
    let guarded = "[(list a b) #:when (> a b) 'more] [(list a b) (=> next) (if (eqv? a b) (next) 'less)] [(list _ _) 'same] [_ 'other]";
    assert_eq!(each(guarded, "((2 1) (1 2) (3 3) (1))"), "(more less same other)");
    // The pattern's variables are bound in the body, not in its expressions, even those an `or`
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
    // As in Racket, `(== v same?)` is true of `x` if `(same? v x)` is.
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
    let caught = |body: &str| {
        eval(&format!(
            "(guard (e ((error-object? e) (list (error-object-kind e) (error-object-message e) (error-object-irritants e)))) {body})"
        ))
    };
    assert_eq!(caught("(car 1)"), r#"(wrong-type "wrong type" ())"#);
    assert_eq!(caught("(vector-ref (vector 1) 5)"), r#"(out-of-range "out of range" ())"#);
    assert_eq!(caught("(/ 1 0)"), r#"(divide-by-zero "divide by zero" ())"#);
    assert_eq!(caught("(error \"bad thing\" 1 'two)"), r#"(error "bad thing" (1 two))"#);
    assert_eq!(caught("((lambda (x) x))"), r#"(arity "arity" ())"#);
    assert_eq!(eval("(list (error-object? 1) (guard (e (#t (error-object? e))) (car '())))"), "(#f #t)");
    assert_eq!(eval_in(&mut arena(), "(error \"no one\")"), Ok(Err(Fault::Error)));
    assert_eq!(caught("(utf8->string #u8(255))"), r#"(not-utf8 "not utf8" ())"#);
}

#[test]
fn marks_are_seen_inside_and_dropped_after() {
    let text = "(define (depth) (mark-value 'depth 0))
                (define (nest n) (if (eqv? n 0) (list (depth)) (call-with-mark 'depth (+ (depth) 1) (lambda () (cons (depth) (nest (- n 1)))))))
                (list (nest 3) (depth))";
    assert_eq!(eval(text), "((1 2 3 3) 0)");
    // One set in tail position replaces the mark of the frame it's in, so a loop runs in
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
    // After each level's handler call returns, a raise goes to the level outside it, as frames
    // overflow segments and are copied back, again each time the bottom's continuation is called.
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
    // A thunk that takes any number of arguments, or a guard set by `apply`, can't be called
    // in the loop, so the outer loop keeps its guard in a record on the chain.
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
    // Each level raises what its guard caught to the level outside it, leaving a winder, as
    // frames overflow segments and are copied back, again each time the bottom's continuation
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
    // A guard in a composable continuation catches what's raised where it's called.
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
    let wind = |body: &str| eval(&format!("{log} (let ((r {body})) (list r (reverse log)))"));
    assert_eq!(wind("(dynamic-wind (lambda () (note 'in)) (lambda () (note 'during) 'v) (lambda () (note 'out)))"), "(v (in during out))");
    let values = "(call-with-values (lambda () (dynamic-wind (lambda () 0) (lambda () (values 1 2)) (lambda () 3))) list)";
    assert_eq!(eval(values), "(1 2)");
    let escape = "(call/cc (lambda (k) (dynamic-wind (lambda () (note 'in)) (lambda () (k 'escaped) (note 'not)) (lambda () (note 'out)))))";
    assert_eq!(wind(escape), "(escaped (in out))");
    let inside = "(dynamic-wind (lambda () (note 'in)) (lambda () (call/cc (lambda (k) (note 'jump) (k 1)))) (lambda () (note 'out)))";
    assert_eq!(wind(inside), "(1 (in jump out))");
    let nested = "(call-with-continuation-prompt
                    (lambda ()
                      (dynamic-wind (lambda () (note 'a-in))
                                    (lambda () (dynamic-wind (lambda () (note 'b-in))
                                                             (lambda () (abort-current-continuation (default-continuation-prompt-tag) (lambda () 'aborted)))
                                                             (lambda () (note 'b-out))))
                                    (lambda () (note 'a-out)))))";
    assert_eq!(wind(nested), "(aborted (a-in b-in b-out a-out))");
    // R7RS's example: a continuation captured inside, called from outside, goes back in.
    let again = "(let ((path '()) (c #f))
                   (let ((add (lambda (s) (set! path (cons s path)))))
                     (dynamic-wind (lambda () (add 'connect))
                                   (lambda () (add (call/cc (lambda (c0) (set! c c0) 'talk1))))
                                   (lambda () (add 'disconnect)))
                     (if (eqv? (length path) 3) (c 'talk2) (reverse path))))";
    assert_eq!(eval(again), "(connect talk1 disconnect connect talk2 disconnect)");
    // A composable continuation runs the befores of the winders it holds.
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
    // A guard leaving the extent runs the afters, before its clauses.
    let guarded = "(guard (e (#t (note (list 'caught e)) 'g))
                     (dynamic-wind (lambda () (note 'in)) (lambda () (raise 'x)) (lambda () (note 'out))))";
    assert_eq!(wind(guarded), "(g (in out (caught x)))");
}

#[test]
fn errors_no_handler_takes_run_the_afters_first() {
    let mut arena = arena();
    let log = "(define log '()) (define (note x) (set! log (cons x log)))";
    let failing = format!("{log} (dynamic-wind (lambda () (note 'in)) (lambda () (dynamic-wind (lambda () (note 'in2)) (lambda () (car 1)) (lambda () (note 'out2)))) (lambda () (note 'out)))");
    assert_eq!(eval_in(&mut arena, &failing), Ok(Err(Fault::WrongType)));
    assert_eq!(eval_in(&mut arena, "(reverse log)"), Ok(Ok("(in in2 out2 out)".into())));
    // In a coroutine, a yield runs none, and a failure runs them before it's raised again
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
    // co/try-resume returns what a resume of a coroutine that isn't pending raises.
    let done = "(define co (make-coroutine (lambda () 1))) (co/resume co)
                (call-with-values (lambda () (co/try-resume co)) (lambda (ok e) (list ok (error-object-kind e))))";
    assert_eq!(eval(done), "(#f not-pending)");
    let values = "(call-with-values (lambda () (co/try-resume (make-coroutine (lambda () (values 1 2))))) list)";
    assert_eq!(eval(values), "(#t 1 2)");
}

#[test]
fn raising_in_a_loop_runs_in_constant_space() {
    let text = |n: u64| {
        format!(
            "(let ((log 0))
                  (let loop ((i 0) (sum 0))
                    (if (eqv? i {n})
                        (list sum log)
                        (loop (+ i 1)
                              (+ sum (guard (e ((null? e) 0) ((pair? e) (car e)))
                                       (dynamic-wind (lambda () #f)
                                                     (lambda () (+ (with-exception-handler (lambda (e) 1) (lambda () (raise-continuable i)))
                                                                   (raise (list (vector-ref (vector 1) 0)))))
                                                     (lambda () (set! log (+ log 1))))))))))"
        )
    };
    assert_eq!(eval(&text(1000)), "(1000 1000)");
    // Run one that doesn't end for as many pauses as it takes to see the live memory settle.
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
