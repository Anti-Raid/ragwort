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
    let mut arena = Arena::new(1 << 24, 4);
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
fn keywords_are_interned_values() {
    let text = "(list '#:when (keyword? '#:when) (keyword? 'when) (eq? '#:a '#:a) (eq? '#:a (string->keyword \"a\"))
                      (keyword->string '#:when) (equal? '(#:x 1) '(#:x 1)) (string->keyword \"two words\"))";
    assert_eq!(eval(text), "(#:when #t #f #t #t \"when\" #t #:|two words|)");
    // As in Racket, a keyword isn't an expression by itself.
    assert_eq!(error("(list #:when 1)"), (BadSyntax, "#:when"));
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
    assert_eq!(error(&deep(300)).0, TooDeep);
    assert_eq!(eval_in(&mut arena(), &deep(200)), Ok(Err(Fault::WrongType)));
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
    //    in `L4::Recur`).
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

#[test]
fn the_host_resumes_a_machine_that_yields() {
    let mut arena = arena();
    let text = "(let ((co (make-coroutine (lambda (x) (co/yield (list x 'a)) (co/yield (vector x 'b)) (list 'done x)))))
                  (let* ((a (co/yield (co/resume co 1))) (b (co/yield (vector->list (co/resume co)))) (c (co/resume co)))
                    (list a b c)))";
    let mut machine = machine(&mut arena, text);
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[]))), "Err(NotPending)");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.run(mc))), "yielded (1 a)");
    // What the coroutines hold stays alive while they wait.
    arena.collect();
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[Value::fixnum(10).unwrap()]))), "yielded (1 b)");
    arena.collect();
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[Value::fixnum(20).unwrap()]))), "done (10 20 (done 1))");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.resume(mc, &[]))), "Err(Finished)");
    // Plain `run` goes on from a yield with no values.
    let mut machine = self::machine(&mut arena, "(call-with-values (lambda () (co/yield 'x)) list)");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.run(mc))), "yielded x");
    assert_eq!(arena.mutate(|mc| show_outcome(mc, machine.run(mc))), "done ()");
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
    // The prelude names the kinds in the VM's order.
    let names = PRELUDE.split("#(malformed").nth(1).and_then(|rest| rest.split(')').next()).unwrap();
    let names: Vec<&str> = std::iter::once("malformed").chain(names.split_whitespace()).collect();
    assert_eq!(names, Fault::KINDS);
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
