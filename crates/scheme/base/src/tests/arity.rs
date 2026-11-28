use super::case_lambda::raised;
use super::*;

#[test]
fn apply_reports_the_procedure_and_the_number_of_arguments() {
    let g = "(define (g a) a)";
    assert_eq!(raised(&format!("{g} (apply g '(1 2))")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} (apply g '())")), "g: wrong number of arguments (expected 1, got 0)");
    // The arguments before the list are counted with its elements.
    assert_eq!(raised(&format!("{g} (apply g 1 2 '(3 4))")), "g: wrong number of arguments (expected 1, got 4)");
    assert_eq!(raised(&format!("{g} (apply g 1 2 3 4 5 6 7 8 9 '(10))")), "g: wrong number of arguments (expected 1, got 10)");
    assert_eq!(raised(&format!("{g} (apply g (vector->list (make-vector 40 0)))")), "g: wrong number of arguments (expected 1, got 40)");
    // A call whose result is used, and calls inside a procedure, report the same way.
    assert_eq!(raised(&format!("{g} (+ 1 (apply g '(1 2)))")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} (define (h) (apply g '(1 2))) (h)")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} (define (h) (+ 1 (apply g 1 '(2 3)))) (h)")), "g: wrong number of arguments (expected 1, got 3)");
    // `apply` as a value.
    assert_eq!(raised(&format!("{g} (define (call f . args) (apply f args)) (call g 1 2 3)")), "g: wrong number of arguments (expected 1, got 3)");
    assert_eq!(raised(&format!("{g} ((car (list apply)) g '(1 2))")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} ((car (list apply)) g 1 '(2 3))")), "g: wrong number of arguments (expected 1, got 3)");
    // Optional and rest parameters.
    assert_eq!(raised("(define (o a [b 2]) a) (apply o '(1 2 3))"), "o: wrong number of arguments (expected 1 to 2, got 3)");
    assert_eq!(raised("(define (o a [b 2]) a) (apply o '())"), "o: wrong number of arguments (expected 1 to 2, got 0)");
    assert_eq!(raised("(define (r a b . more) a) (apply r '(1))"), "r: wrong number of arguments (expected at least 2, got 1)");
    assert_eq!(raised("(apply (lambda (a) a) '(1 2))"), "wrong number of arguments (expected 1, got 2)");
}

#[test]
fn a_procedure_that_another_procedure_calls_reports_its_arguments() {
    let g = "(define (g a) a)";
    assert_eq!(raised(&format!("{g} (map g '(1 2) '(3 4))")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} (call-with-values (lambda () (values 1 2)) g)")), "g: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{g} (call-with-values (lambda () (values)) g)")), "g: wrong number of arguments (expected 1, got 0)");
    assert_eq!(raised(&format!("{g} (dynamic-wind g (lambda () 1) (lambda () 2))")), "g: wrong number of arguments (expected 1, got 0)");
    assert_eq!(raised("(with-exception-handler (lambda () 1) (lambda () (raise-continuable 5)))"), "wrong number of arguments (expected 0, got 1)");
}

#[test]
fn a_keyword_procedure_reports_its_positional_arguments() {
    let k = "(define (k a #:size [size 1]) a)";
    assert_eq!(raised(&format!("{k} (k 1 2)")), "k: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{k} (k)")), "k: wrong number of arguments (expected 1, got 0)");
    assert_eq!(raised(&format!("{k} (k 1 2 #:size 3)")), "k: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{k} (k #:size 3)")), "k: wrong number of arguments (expected 1, got 0)");
    assert_eq!(raised(&format!("{k} (+ 1 (k 1 2 #:size 3))")), "k: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{k} (apply k '(1 2 3))")), "k: wrong number of arguments (expected 1, got 3)");
    assert_eq!(raised(&format!("{k} (define (h f) (f 1 2)) (h k)")), "k: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{k} (keyword-apply k '(#:size) '(3) 1 '(2 3))")), "k: wrong number of arguments (expected 1, got 3)");
    // A procedure with a required keyword has no closure for a call without keywords.
    let q = "(define (q a #:size size #:tone [tone 0] #:zest [zest 0]) a)";
    assert_eq!(raised(&format!("{q} (q 1 2 #:size 3)")), "q: wrong number of arguments (expected 1, got 2)");
    assert_eq!(raised(&format!("{q} (q #:size 3 #:zest 4)")), "q: wrong number of arguments (expected 1, got 0)");
    assert_eq!(raised(&format!("{q} (keyword-apply q '(#:size) '(3) '(1 2 3))")), "q: wrong number of arguments (expected 1, got 3)");
    // A missing keyword is reported before the number of arguments.
    assert_eq!(raised(&format!("{q} (q 1 2)")), "missing required keyword: #:size");
    // Optional and rest parameters beside keywords.
    assert_eq!(raised("(define (o a [b 2] #:size [size 1]) a) (o 1 2 3)"), "o: wrong number of arguments (expected 1 to 2, got 3)");
    assert_eq!(raised("(define (o a [b 2] #:size [size 1]) a) (o #:size 5)"), "o: wrong number of arguments (expected 1 to 2, got 0)");
    assert_eq!(raised("(define (r a #:size [size 1] . more) a) (r #:size 5)"), "r: wrong number of arguments (expected at least 1, got 0)");
    assert_eq!(eval("(define (r a #:size [size 1] . more) (list a size more)) (list (r 1) (r 1 2 3 #:size 9) (apply r 1 '(2)))"), "((1 1 ()) (1 9 (2 3)) (1 1 (2)))");
}

#[test]
fn a_refused_call_at_any_stack_depth_reports_its_arguments() {
    // Some depth puts the refused call at the end of a stack segment, where the call starts on a new segment. The first segment holds fewer than 600 frames.
    let program = "
        (define g (car (list (lambda (a) a))))
        (define (direct n) (if (= n 0) (+ 1 (g 1 2)) (+ 1 (direct (- n 1)))))
        (define (applied n) (if (= n 0) (+ 1 (apply g 1 '(2 3))) (+ 1 (applied (- n 1)))))
        (define (given deep n) (guard (e (#t (cadr (error-object-irritants e)))) (deep n)))
        (let loop ([n 0] [wrong 0])
          (if (= n 600)
              wrong
              (loop (+ n 1) (if (and (= (given direct n) 2) (= (given applied n) 3)) wrong (+ wrong 1)))))";
    assert_eq!(eval_in(&mut arena_of(1 << 27), program).unwrap().unwrap(), "0");
}
