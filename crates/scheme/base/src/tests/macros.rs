use super::*;

#[test]
fn syntax_rules_macros_are_hygienic() {
    // What a macro binds doesn't capture what it's given, and what it refers to means what it
    // did where the macro was defined.
    let swap = "(define-syntax swap! (syntax-rules () ((_ a b) (let ((tmp a)) (set! a b) (set! b tmp)))))
                (define tmp 1) (define y 2) (swap! tmp y) (list tmp y)";
    assert_eq!(eval(swap), "(2 1)");
    let or = "(define-syntax my-or (syntax-rules () ((_) #f) ((_ e) e) ((_ e r ...) (let ((t e)) (if t t (my-or r ...))))))
              (list (let ((t 5) (if list)) (my-or #f t)) (my-or) (my-or #f #f 3))";
    assert_eq!(eval(or), "(5 #f 3)");
    // A definition a macro introduces at the top level is its own, apart from one of the name.
    let hidden = "(define-syntax def-hidden (syntax-rules () ((_ get) (begin (define secret 42) (define (get) secret)))))
                  (def-hidden get-it) (define secret 1) (list (get-it) secret)";
    assert_eq!(eval(hidden), "(42 1)");
}

#[test]
fn patterns_take_ellipses_tails_vectors_and_literals() {
    let text = "(define-syntax my-let* (syntax-rules ()
                  ((_ () body ...) (let () body ...))
                  ((_ ((x v) rest ...) body ...) (let ((x v)) (my-let* (rest ...) body ...)))))
                (define-syntax flat (syntax-rules () ((_ (a ...) ...) '(a ... ...))))
                (define-syntax table (syntax-rules () ((_ (k v ...) ...) '((k v ...) ...))))
                (define-syntax each (syntax-rules () ((_ x (y ...)) '((x y) ...))))
                (define-syntax ends (syntax-rules () ((_ a ... z) '(z a ...))))
                (define-syntax rest (syntax-rules () ((_ a . r) 'r)))
                (define-syntax vec (syntax-rules () ((_ #(a ...) b) (+ b a ...))))
                (define-syntax arrow (syntax-rules (=>) ((_ a => b) (list a b)) ((_ . _) 'other)))
                (list (my-let* ((a 1) (b (+ a 1))) (* a b))
                      (flat (1 2) (3) ())
                      (table (a 1 2) (b))
                      (each a (1 2))
                      (ends 1 2 3)
                      (rest 1 2 3)
                      (vec #(1 2 3) 10)
                      (arrow 1 => 2)
                      (let ((=> 0)) (arrow 1 => 2)))";
    assert_eq!(eval(text), "(2 (1 2 3) ((a 1 2) (b)) ((a 1) (a 2)) (3 1 2) (2 3) 16 (1 2) other)");
}

#[test]
fn macros_define_and_nest() {
    // A macro that defines macros, with `(... ...)` for an ellipsis of the one it defines.
    let text = "(define-syntax def-const (syntax-rules () ((_ name v) (define-syntax name (syntax-rules () ((_) v))))))
                (define-syntax def-lister (syntax-rules () ((_ name) (define-syntax name (syntax-rules () ((_ x (... ...)) (list x (... ...))))))))
                (define-syntax define-two (syntax-rules () ((_ a b v) (begin (define a v) (define b v)))))
                (def-const five 5) (def-lister lst) (define-two p q 7)
                (define (f) (define-two r s 1) (define-syntax twice (syntax-rules () ((_ e) (+ e e)))) (twice (+ r s)))
                (list (five) (lst 1 2 3) p q (f))";
    assert_eq!(eval(text), "(5 (1 2 3) 7 7 4)");
    let local = "(define-syntax m (syntax-rules () ((_) 'outer)))
                 (list (let-syntax ((m (syntax-rules () ((_) (list 'inner (m)))))) (m))
                       (letrec-syntax ((my-and (syntax-rules () ((_) #t) ((_ e) e) ((_ e r ...) (if e (my-and r ...) #f)))))
                         (my-and 1 2 3))
                       (let-syntax ((double (syntax-rules () ((_ x) (* x 2))))) (define y (double 4)) y))";
    assert_eq!(eval(local), "((inner outer) 3 8)");
}

#[test]
fn syntax_case_transformers_run_as_they_expand() {
    let text = "(define-syntax aif
                  (lambda (stx)
                    (syntax-case stx ()
                      ((k test then else)
                       (with-syntax ((it (datum->syntax #'k 'it)))
                         #'(let ((it test)) (if it then else)))))))
                (define-syntax kind (lambda (stx) (syntax-case stx () ((_ x) (identifier? #'x) #''id) ((_ x) #''other))))
                (define-syntax same? (lambda (stx) (syntax-case stx () ((_ a b) (if (free-identifier=? #'a #'b) #''yes #''no)))))
                (define-syntax count-args (lambda (stx) (syntax-case stx () ((_ x ...) (datum->syntax stx (length (syntax->list #'(x ...))))))))
                (define-syntax quoted (lambda (stx) (syntax-case stx () ((_ x) (datum->syntax #'x (list 'quote (syntax->datum #'x)))))))
                (define-syntax values-of (lambda (stx)
                  (syntax-case stx ()
                    ((_ e ...) (with-syntax (((t ...) (generate-temporaries #'(e ...)))) #'(let ((t e) ...) (list t ...)))))))
                (define-syntax answer (lambda (stx) #'42))
                (list (aif (memv 2 '(1 2 3)) (car it) 'none)
                      (kind a) (kind 1)
                      (same? car car) (same? car cdr) (let ((car 1)) (same? car car)) (same? else else)
                      (count-args a b c)
                      (quoted (a b))
                      (values-of 1 2 3)
                      (+ answer 1))";
    assert_eq!(eval(text), "(2 id other yes no yes yes 3 (a b) (1 2 3) 43)");
    let ids = "(define-syntax ids (lambda (stx)
                 (syntax-case stx ()
                   ((_ a b) (if (bound-identifier=? #'a #'b) #''same #''apart)))))
               (list (ids x x) (ids x y))";
    assert_eq!(eval(ids), "(same apart)");
}

#[test]
fn syntax_objects_are_values() {
    let text = "(list (syntax->datum #'(a (b . c) #(d e))) (identifier? #'x) (identifier? #'(x)) (syntax? 1)
                      (bound-identifier=? #'x #'x) (syntax-e #'5) (syntax->datum (datum->syntax #f '(p q))))";
    assert_eq!(eval(text), "((a (b . c) #(d e)) #t #f #f #t 5 (p q))");
    assert_eq!(eval("(list #'(a 1) (lambda () 1) (values))"), "(#<syntax (a 1)> #<procedure> #<values>)");
}

#[test]
fn syntax_procedures_run_outside_macros() {
    // Each temporary is in a scope of its own, named as its element is if that's an identifier.
    let temporaries = "(let ((ts (generate-temporaries #'(a 1))) (us (generate-temporaries '(a))))
                         (list (map syntax->datum ts) (syntax->datum (car us)) (map identifier? ts)
                               (bound-identifier=? (car ts) (car ts)) (bound-identifier=? (car ts) (car us))
                               (bound-identifier=? (car ts) #'a)))";
    assert_eq!(eval(temporaries), "((a t) t (#t #t) #t #f #f)");
    // A syntax violation is an error of kind `syntax`, its irritants the form and subform.
    let violation = "(guard (e (#t (list (error-object-kind e) (error-object-message e) (map syntax->datum (error-object-irritants e)))))
                       (syntax-violation 'who \"no good\" #'(x y) #'y))";
    assert_eq!(eval(violation), "(syntax \"no good\" ((x y) y))");
}

#[test]
fn syntax_case_runs_outside_macros() {
    let text = "(define (parts stx)
                  (syntax-case stx (to)
                    ((a to b) (list 'range (syntax->datum #'a) (syntax->datum #'b)))
                    ((x (y ...) ...) (syntax->datum #'((y ... x) ...)))
                    (#(v ...) (length (syntax->list #'(v ...))))
                    (_ 'other)))
                (list (parts #'(1 to 2)) (parts #'(k (1 2) (3))) (parts #'#(a b c)) (parts #'(1 2)) (parts 5))";
    assert_eq!(eval(text), "((range 1 2) ((1 2 k) (3 k)) 3 other other)");
    // With no clause that matches, it raises a syntax error, of what it was given.
    let none = "(guard (e (#t (list (error-object-kind e) (syntax->datum (car (error-object-irritants e))))))
                  (syntax-case #'(a b) () ((x) 'one)))";
    assert_eq!(eval(none), "(syntax (a b))");
    // As does a template whose ellipses repeat variables that matched different numbers of times.
    let uneven = "(define (zip stx) (syntax-case stx () (((a ...) (b ...)) #'((a b) ...))))
                  (list (syntax->datum (zip #'((1 2) (3 4)))) (guard (e (#t (error-object-kind e))) (zip #'((1 2) (3)))))";
    assert_eq!(eval(uneven), "(((1 3) (2 4)) syntax)");
}

#[test]
fn free_identifiers_are_the_same_if_they_refer_to_the_same_binding() {
    // `quote-syntax` is the syntax as it is, even of a pattern variable.
    let quoted = "(define-syntax q (lambda (stx) (syntax-case stx () ((_ x) (list (quote-syntax quote) (list #'x (quote-syntax x)))))))
                  (list (q a) (syntax->datum (quote-syntax (b #(c)))) (identifier? (quote-syntax d)))";
    assert_eq!(eval(quoted), "((a x) (b #(c)) #t)");
    let runtime = "(list (free-identifier=? #'car #'car) (free-identifier=? #'car #'cdr) (free-identifier=? (let ((car 1)) (quote-syntax car)) #'car)
                         (free-identifier=? (datum->syntax #'car 'car) #'car) (free-identifier=? #'nowhere #'nowhere))";
    assert_eq!(eval(runtime), "(#t #f #f #t #t)");
    // What a template names is what the module defines, even after the template's made.
    let later = "(define-syntax to? (lambda (stx) (syntax-case stx () ((_ x) (if (free-identifier=? #'x #'to) #''yes #''no)))))
                 (define-syntax range (lambda (stx) (syntax-case stx (to) ((_ a to b) #''(a b)) ((_ . _) #''bad))))
                 (define to 1)
                 (list (to? to) (let ((to 2)) (to? to)) (range 1 to 2) (let ((to 2)) (range 1 to 2)))";
    assert_eq!(eval(later), "(yes no (1 2) bad)");
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(define (a-car) #'car) (define (a-mine) #'mine) (define mine 1)"), Ok(Ok("#<void>".into())));
    let across = "(list (free-identifier=? (a-car) #'car) (let ((car 1)) (free-identifier=? (a-car) #'car)) (free-identifier=? (a-mine) #'mine))";
    assert_eq!(eval_in(&mut arena, across), Ok(Ok("(#t #f #t)".into())));
}

#[test]
fn transformers_can_catch_syntax_violations() {
    let text = "(define-syntax m (lambda (stx) (guard (e ((error-object? e) #''caught)) (syntax-violation 'm \"no\" stx))))
                (m)";
    assert_eq!(eval(text), "caught");
}

#[test]
fn syntax_from_an_earlier_load_keeps_its_scopes() {
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(define (an-x) #'x) (define (a-car) #'car)"), Ok(Ok("#<void>".into())));
    // Each load's top level is a scope of its own, as each module's is.
    assert_eq!(eval_in(&mut arena, "(list (bound-identifier=? (an-x) (an-x)) (bound-identifier=? (an-x) #'x))"), Ok(Ok("(#t #f)".into())));
    // What it refers to, a transformer can still put in what it makes.
    let using = "(define-syntax first (lambda (stx) (syntax-case stx () ((_ e) (list (a-car) #'e)))))
                 (let ((car cdr)) (first '(1 2)))";
    assert_eq!(eval_in(&mut arena, using), Ok(Ok("1".into())));
}

#[test]
fn macro_mistakes_point_at_themselves() {
    assert_eq!(error("(define-syntax two (syntax-rules () ((_ a b) a))) (two 1)"), (BadSyntax, "(two 1)"));
    let violation = "(define-syntax bad (lambda (stx) (syntax-case stx () ((_ x) (syntax-violation 'bad \"no\" stx #'x))))) (bad oops)";
    assert_eq!(error(violation), (BadSyntax, "oops"));
    assert_eq!(error("(define-syntax boom (lambda (stx) (car 1))) (boom)"), (Transformer, "(boom)"));
    assert_eq!(error("(define-syntax sym (lambda (stx) 'x)) (sym)"), (BadSyntax, "(sym)"));
    assert_eq!(error("(let ((x 1)) (define-syntax m (lambda (s) x)) (m))"), (Phase, "(lambda (s) x)"));
    assert_eq!(error("(define-syntax e (syntax-rules () ((_ a ...) a)))"), (BadSyntax, "a"));
    assert_eq!(error("(define-syntax e (syntax-rules () ((_ a) (a ...))))"), (BadSyntax, "a"));
    assert_eq!(error("(define-syntax d (syntax-rules () ((_ x x) x)))"), (Duplicate, "x"));
    assert_eq!(error("(define-syntax p (lambda (s) (syntax-case s () ((_ x) x))))"), (BadSyntax, "x"));
    assert_eq!(error("(define-syntax two-dots (syntax-rules () ((_ a ... b ...) 1)))"), (BadSyntax, "(_ a ... b ...)"));
    assert_eq!(error("(define-syntax zip (syntax-rules () ((_ (a ...) (b ...)) '((a b) ...)))) (zip (1 2) (3))"), (BadSyntax, "(zip (1 2) (3))"));
    // A macro that expands to itself stops when what it makes fills the arena, at the top level
    // and in an expression.
    assert_eq!(error("(define-syntax loop (syntax-rules () ((_) (loop)))) (loop)"), (OutOfMemory.into(), "(loop)"));
    // Which of its expansions fills it depends on how much room there was.
    let (kind, at) = error("(define-syntax loop (syntax-rules () ((_) (+ 1 (loop))))) (loop)");
    assert_eq!(kind, OutOfMemory.into());
    assert!(["(loop)", "(+ 1 (loop))"].contains(&at), "{at}");
    // One that runs forever runs out of fuel.
    assert_eq!(error("(define-syntax spin (lambda (s) (let f () (f)))) (spin)"), (Transformer, "(spin)"));
}
