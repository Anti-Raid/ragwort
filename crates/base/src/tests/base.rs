use ragwort_types::gc::Arena;
use ragwort_types::pair::Pair;
use ragwort_types::string::{Strings, display};
use ragwort_types::symbol::Symbol;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use super::*;
use crate::ExpandErrorKind::*;

/// Root 0 holds the symbol table, root 1 the code's globals and root 2 the prelude's, which it
/// has defined.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        let base = Globals::new(mc).unwrap();
        mc.set_root(0, symbols.value(mc));
        mc.set_root(1, Globals::new(mc).unwrap().value(mc));
        mc.set_root(2, base.value(mc));
        for thunk in prelude(mc, symbols, base).unwrap() {
            run(mc, thunk).unwrap();
        }
    });
    arena
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(*raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap()),
        }
    }
}

fn show<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    let strings = Strings::new(mc);
    if let Some(symbol) = Symbol::of(v) {
        return display(&strings, symbol.name(mc)).to_string();
    }
    if let Some(s) = strings.string(v) {
        return format!("{:?}", display(&strings, s).to_string());
    }
    if let Some(c) = v.as_char() {
        return format!("#\\{c}");
    }
    let Some(pair) = Pair::of(v) else {
        return match v {
            Value::NIL => "()",
            Value::TRUE => "#t",
            Value::FALSE => "#f",
            Value::VOID => "#<void>",
            _ => return v.as_fixnum().map_or("#<object>".into(), |n| n.to_string()),
        }
        .to_string();
    };
    let mut out = vec![show(mc, pair.head(mc))];
    let mut rest = pair.tail(mc);
    while let Some(pair) = Pair::of(rest) {
        out.push(show(mc, pair.head(mc)));
        rest = pair.tail(mc);
    }
    if rest != Value::NIL {
        out.push(format!(". {}", show(mc, rest)));
    }
    format!("({})", out.join(" "))
}

/// Loads `text` and runs its forms in order. Returns the last one's value, written out, or the
/// fault one raised.
fn eval_in(arena: &mut Arena, text: &str) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let (globals, base) = (Globals::of(mc, mc.root(1)).unwrap(), Globals::of(mc, mc.root(2)).unwrap());
        let session = SyntaxSession::new(mc, text).unwrap();
        let mut last = Value::VOID;
        for thunk in load(mc, symbols, globals, base, &session)? {
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
    // A definition of a macro's name shadows the macro across the whole body or load.
    assert_eq!(eval("(let ((f #f)) (set! f (lambda () (when))) (define (when) 99) (f))"), "99");
    assert_eq!(eval_in(&mut arena(), "(let () (when) (define (when) 99) (when))"), Ok(Err(Fault::NotProcedure)));
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
    assert_eq!(eval("`#(1 2)"), "#<object>");
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
fn globals_last_from_one_load_to_the_next() {
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(define counter 0) (define (bump!) (set! counter (+ counter 1)) counter)"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(bump!) (bump!)"), Ok(Ok("2".into())));
    assert_eq!(eval_in(&mut arena, "(define (car x) 'mine)"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(list (car '(1)) (cadr '(1 2)))"), Ok(Ok("(mine 2)".into())));
    assert_eq!(eval_in(&mut arena, "nowhere"), Ok(Err(Fault::Unbound)));
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
    assert_eq!(error("(define-syntax m 1)"), (Unsupported, "(define-syntax m 1)"));
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
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let (globals, base) = (Globals::of(mc, mc.root(1)).unwrap(), Globals::of(mc, mc.root(2)).unwrap());
        let session = SyntaxSession::new(mc, "(define (count n) (if (eqv? n 0) 'done (count (+ n -1)))) (count 400000)").unwrap();
        let mut thunks = load(mc, symbols, globals, base, &session).unwrap();
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
    assert_eq!(eval("(list (- 5) (- 10 1 2) (*) (* 2 3 4) (/ 12 3) (/ 2) (/ 1 2 3) (- 1/2 1/2))"), "(-5 7 1 24 4 #<object> #<object> 0)");
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
    // `call-with-composable-continuation` reifies a raw `Continuation` object, which is both
    // `continuation?` and `procedure?`; `call/cc` wraps it in an aborting lambda (`procedure?` only).
    assert_eq!(
        eval("(call-with-composable-continuation (lambda (k) (list (procedure? k) (continuation? k))))"),
        "(#t #t)"
    );
    assert_eq!(
        eval("(call/cc (lambda (k) (list (procedure? k) (continuation? k))))"),
        "(#t #f)"
    );
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
}
