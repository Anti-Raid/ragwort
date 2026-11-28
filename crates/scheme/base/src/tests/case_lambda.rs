use super::*;

/// Runs the forms of `text` and returns the displayed form of the value that one of them raises.
pub(super) fn raised(text: &str) -> String {
    arena().mutate(|mc| {
        for thunk in load_text(mc, text).unwrap() {
            if let Err(raised) = run_raising(mc, thunk) {
                return ragwort_printer_scheme::to_string(mc, raised, ragwort_printer_scheme::Mode::Display, usize::MAX).unwrap();
            }
        }
        panic!("{text} raised nothing")
    })
}

#[test]
fn a_call_runs_the_first_clause_that_takes_its_arguments() {
    let f = "(define f (case-lambda [() 'none] [(a) (list 'one a)] [(a b c) (list 'three a b c)] [(a b . more) (list 'more a b more)]))";
    assert_eq!(eval(&format!("{f} (list (f) (f 1) (f 1 2) (f 1 2 3) (f 1 2 3 4) (f 1 2 3 4 5))")), "(none (one 1) (more 1 2 ()) (three 1 2 3) (more 1 2 (3 4)) (more 1 2 (3 4 5)))");
    // An earlier clause wins where two clauses take the same number.
    let first = "(define f (case-lambda [(a . more) (list 'rest a more)] [(a b) (list 'two a b)] [args 'any]))";
    assert_eq!(eval(&format!("{first} (list (f) (f 1) (f 1 2) (f 1 2 3))")), "(any (rest 1 ()) (rest 1 (2)) (rest 1 (2 3)))");
    // A procedure with one clause, and one that only has a rest parameter.
    assert_eq!(eval("(list ((case-lambda [(a b) (+ a b)]) 1 2) ((case-lambda [args args]) 1 2 3) ((case-lambda [args args])))"), "(3 (1 2 3) ())");
    // The arguments can come from a list, and a clause can call the procedure again.
    let sum = "(define sum (case-lambda [(xs) (sum xs 0)] [(xs acc) (if (null? xs) acc (sum (cdr xs) (+ acc (car xs))))]))";
    assert_eq!(eval(&format!("{f} {sum} (list (apply f '(1 2 3 4)) (apply f 1 '(2 3)) (apply f '()) (sum '(1 2 3 4)) (map f '(1 2) '(3 4)))")), "((more 1 2 (3 4)) (three 1 2 3) none 10 ((more 1 3 ()) (more 2 4 ())))");
}

#[test]
fn clauses_share_the_variables_around_them() {
    // Each call of `counter` makes one procedure. Its clauses read and set the same `n`.
    let counter = "(define (counter n) (case-lambda [() n] [(by) (set! n (+ n by)) n] [(by times) (set! n (+ n (* by times))) n]))
                   (define c (counter 10))
                   (define d (counter 0))";
    assert_eq!(eval(&format!("{counter} (list (c) (c 1) (c 2 3) (c) (d) (procedure? c))")), "(10 11 17 17 0 #t)");
    // A body has definitions of its own, and a deep loop through a clause does not grow the stack.
    let looping = "(define count (case-lambda [(n) (count n 0)] [(n acc) (define next (+ acc 1)) (if (= n 0) acc (count (- n 1) next))]))";
    assert_eq!(eval(&format!("{looping} (count 300000)")), "300000");
    // A coroutine's body and a handler can be such procedures.
    let coroutine = "(define co (make-coroutine (case-lambda [() 'none] [(a) (co/yield (list 'got a)) 'done])))
                     (list (co/resume co 5) (co/resume co) (with-exception-handler (case-lambda [(e) (list 'handled e)] [(e more) 'no]) (lambda () (raise-continuable 'oops))))";
    assert_eq!(eval(coroutine), "((got 5) done (handled oops))");
}

#[test]
fn a_call_that_no_clause_takes_is_an_arity_error() {
    let f = "(define f (case-lambda [(a) a] [(a b c) c]))";
    assert_eq!(raised(&format!("{f} (f 1 2)")), "f: wrong number of arguments (expected 1 or 3, got 2)");
    assert_eq!(raised(&format!("{f} (f)")), "f: wrong number of arguments (expected 1 or 3, got 0)");
    assert_eq!(raised(&format!("{f} (f 1 2 3 4)")), "f: wrong number of arguments (expected 1 or 3, got 4)");
    assert_eq!(raised(&format!("{f} (apply f '(1 2))")), "f: wrong number of arguments (expected 1 or 3, got 2)");
    assert_eq!(raised(&format!("{f} (apply f 1 2 '(3 4))")), "f: wrong number of arguments (expected 1 or 3, got 4)");
    let rest = "(define g (case-lambda [() 0] [(a b) b] [(a b c d . more) more]))";
    assert_eq!(raised(&format!("{rest} (g 1)")), "g: wrong number of arguments (expected 0, 2 or at least 4, got 1)");
    assert_eq!(raised(&format!("{rest} (g 1 2 3)")), "g: wrong number of arguments (expected 0, 2 or at least 4, got 3)");
    assert_eq!(eval(&format!("{rest} (list (g) (g 1 2) (g 1 2 3 4) (g 1 2 3 4 5))")), "(0 2 () (5))");
    // A call that the compiler could resolve itself is refused in the same way.
    assert_eq!(raised("((case-lambda [(a) a] [(a b c) c]) 1 2)"), "wrong number of arguments (expected 1 or 3, got 2)");
    assert_eq!(raised("(let ((h (case-lambda [(a) a] [(a b c) c]))) (h 1 2))"), "h: wrong number of arguments (expected 1 or 3, got 2)");
    // The clauses that reach the largest number in a row are reported as "at least".
    assert_eq!(raised("(define k (case-lambda [(a b) a] [(a b c . more) more])) (k 1)"), "k: wrong number of arguments (expected at least 2, got 1)");
}

#[test]
fn a_case_lambda_that_is_not_one_is_reported() {
    assert_eq!(error("(case-lambda)"), (ExpandErrorKind::BadSyntax, "(case-lambda)"));
    assert_eq!(error("(case-lambda [(a)])"), (ExpandErrorKind::BadSyntax, "[(a)]"));
    assert_eq!(error("(case-lambda [(a) a] 5)"), (ExpandErrorKind::BadSyntax, "5"));
    // A clause takes plain parameters and a rest parameter, and no default or keyword.
    assert_eq!(error("(case-lambda [(a [b 1]) a])"), (ExpandErrorKind::BadSyntax, "[(a [b 1]) a]"));
    assert_eq!(error("(case-lambda [(a #:k k) a])"), (ExpandErrorKind::BadSyntax, "[(a #:k k) a]"));
    assert_eq!(error("(case-lambda [(a a) a])"), (ExpandErrorKind::Duplicate, "a"));
}

/// Returns `count` parameter names, `p1` to `p{count}`, and the same number of arguments, `1` to `count`.
fn many(count: usize) -> (String, String) {
    let names: Vec<String> = (1..=count).map(|index| format!("p{index}")).collect();
    let numbers: Vec<String> = (1..=count).map(|index| index.to_string()).collect();
    (names.join(" "), numbers.join(" "))
}

#[test]
fn clauses_have_any_number_of_parameters() {
    // The widest clause that still gets a register for each parameter, next to a clause with none. Every number between them is refused.
    let (sixteen, numbers) = many(16);
    let spread = format!("(define f (case-lambda [() 'none] [({sixteen}) (list p1 p16)]))");
    assert_eq!(eval(&format!("{spread} (list (f) (f {numbers}))")), "(none (1 16))");
    for count in [1, 2, 8, 15, 17] {
        let message = format!("f: wrong number of arguments (expected 0 or 16, got {count})");
        assert_eq!(raised(&format!("{spread} (f {})", many(count).1)), message);
    }
    // A wider clause does not fit the registers. The procedure then counts its arguments itself.
    let (twenty, numbers) = many(20);
    let wide = format!("(define g (case-lambda [(a) (list 'one a)] [({twenty}) (list p1 p17 p20)] [(a b c . more) (list 'more c more)]))");
    assert_eq!(eval(&format!("{wide} (list (g 1) (g {numbers}) (g 1 2 3) (g 1 2 3 4 5) (apply g '(7)))")), "((one 1) (1 17 20) (more 3 ()) (more 3 (4 5)) (one 7))");
    assert_eq!(eval(&format!("{wide} (g {} 21 22)", numbers)), "(more 3 (4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22))");
    // Its arity error names it and the number that it got. It does not list the numbers that it takes.
    assert_eq!(raised(&format!("{wide} (g 1 2)")), "g: wrong number of arguments (got 2)");
    assert_eq!(raised(&format!("{wide} (g)")), "g: wrong number of arguments (got 0)");
    assert_eq!(eval(&format!("{wide} (guard (e (#t (list (error-object-kind e) (error-object-who e)))) (g 1 2))")), "(arity #f)");
    // A wide procedure with a rest clause and with captured variables.
    let (thirty, numbers) = many(30);
    let captured = format!("(define (make base) (case-lambda [({thirty} . more) (list base p30 more)] [() base]))
                            (define h (make 'kept))");
    assert_eq!(eval(&format!("{captured} (list (h) (h {numbers}) (h {numbers} 31))")), "(kept (kept 30 ()) (kept 30 (31)))");
    // The procedure was made by a call, so it has no name of its own.
    assert_eq!(raised(&format!("{captured} (h 1 2 3)")), "wrong number of arguments (got 3)");
}
