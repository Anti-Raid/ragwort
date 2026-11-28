use super::*;

#[test]
fn syntax_rules_macros_expand_and_recur() {
    let list = "(%define-syntax build
                  (%syntax-rules ()
                    ((_) '())
                    ((_ first rest ...) (%intrinsic cons first (build rest ...)))))
                (build 'a 'b 'c)";
    assert_eq!(eval(list), "(a b c)");
    // A literal matches only the same identifier.
    let literal = "(%define-syntax pick
                     (%syntax-rules (left right)
                       ((_ left a b) a)
                       ((_ right a b) b)))
                   (%intrinsic cons (pick left 'a 'b) (pick right 'a 'b))";
    assert_eq!(eval(literal), "(a . b)");
    // A use that no rule matches is an error at the use.
    assert_eq!(error("(%define-syntax one (%syntax-rules () ((_ a) a))) (one 'a 'b)"), (BadShape, "(one 'a 'b)"));
}

#[test]
fn macros_are_hygienic() {
    // The macro's own `tmp` is apart from the `tmp` of the use.
    let swap = "(%define-syntax swap!
                  (%syntax-rules ()
                    ((_ a b) (%let ((tmp a)) (%set! a b) (%set! b tmp)))))
                (%let ((tmp 'one) (other 'two))
                  (swap! tmp other)
                  (%intrinsic cons tmp other))";
    assert_eq!(eval(swap), "(two . one)");
    // A name in a template refers to the module's binding, even where the use has a local variable of that name.
    let reference = "(%define-syntax call-helper (%syntax-rules () ((_) (%app helper))))
                     (%define helper (%lambda () 'module))
                     (%let ((helper (%lambda () 'local))) (call-helper))";
    assert_eq!(eval(reference), "module");
    // A loop that a macro makes has a name of its own. A `%break` in the use leaves the loop of the use.
    let labels = "(%define-syntax twice
                    (%syntax-rules ()
                      ((_ body) (%let ((n 0)) (%loop again (%if (%intrinsic eq? n 2) (%break again) #f) (%set! n (%intrinsic + n 1)) body)))))
                  (%let ((count 0))
                    (%loop again
                      (twice (%if (%intrinsic eq? count 3) (%break again) (%set! count (%intrinsic + count 1)))))
                    count)";
    assert_eq!(eval(labels), "3");
}

#[test]
fn macros_define_variables() {
    // A definition whose name comes from the use is a variable of the module. A definition whose name the macro introduces is private to that use.
    let counters = "(%define-syntax define-counter
                      (%syntax-rules ()
                        ((_ name) (%begin (%define count 0) (%define name (%lambda () (%set! count (%intrinsic + count 1)) count))))))
                    (define-counter one)
                    (define-counter two)
                    (%app one)
                    (%app one)
                    (%intrinsic cons (%app one) (%app two))";
    assert_eq!(eval(counters), "(3 . 1)");
    assert_eq!(error(&format!("{counters} count")), (Unbound, "count"));
    // The definitions of one use can refer to each other in any order.
    let mutual = "(%define-syntax define-parity
                    (%syntax-rules ()
                      ((_ name) (%begin
                                  (%define even (%lambda (n) (%if (%intrinsic eq? n 0) #t (%app odd (%intrinsic - n 1)))))
                                  (%define odd (%lambda (n) (%if (%intrinsic eq? n 0) #f (%app even (%intrinsic - n 1)))))
                                  (%define name even)))))
                  (define-parity even?)
                  (%app even? 10)";
    assert_eq!(eval(mutual), "#t");
    // `%begin` is also an expression. Its value is the value of its last expression.
    assert_eq!(eval("(%let ((x 'a)) (%begin (%set! x 'b) x))"), "b");
    assert_eq!(eval("(%begin (%define a 'one) (%define b a)) b"), "one");
}

#[test]
fn syntax_case_transformers_run_code() {
    // A fender chooses a clause by the kind of syntax that matched.
    let kind = "(%define-syntax kind
                  (%lambda (stx)
                    (%syntax-case stx ()
                      ((_ x) (%intrinsic identifier? #'x) #''name)
                      ((_ x) #''other))))
                (%intrinsic cons (kind a) (kind (a b)))";
    assert_eq!(eval(kind), "(name . other)");
    // A transformer can call what the module requires.
    let mut arena = arena();
    let lists = "(%define quoted-pair (%lambda (x) (%intrinsic cons 'quote (%intrinsic cons (%intrinsic cons x x) '()))))
                 (%provide quoted-pair)";
    module_in(&mut arena, "lists", lists).unwrap().unwrap();
    let imported = "(%require lists)
                    (%define-syntax doubled
                      (%lambda (stx)
                        (%syntax-case stx ()
                          ((_ x) (%intrinsic datum->syntax #'x (%app quoted-pair (%intrinsic syntax->datum #'x)))))))
                    (doubled a)";
    assert_eq!(eval_in(&mut arena, imported).unwrap().unwrap(), "(a . a)");
}

#[test]
fn bad_macros_are_reported() {
    assert_eq!(error("(%define-syntax five 5)"), (Transformer, "(%define-syntax five 5)"));
    assert_eq!(error("(%define later 'a) (%define-syntax m (%let ((x later)) (%lambda (stx) stx)))"), (Phase, "(%let ((x later)) (%lambda (stx) stx))"));
    assert_eq!(error("(%let ((x 'a)) (%define-syntax m (%syntax-rules () ((_) 'a))) x)"), (Definition, "(%define-syntax m (%syntax-rules () ((_) 'a)))"));
    assert_eq!(error("(%define-syntax m)"), (BadShape, "(%define-syntax m)"));
    // A macro's name is not a variable.
    assert_eq!(error("(%define-syntax m (%syntax-rules () ((_) 'a))) (%set! m 'b)"), (BadShape, "m"));
}

#[test]
fn case_lambda_picks_a_clause_by_the_number_of_arguments() {
    let pick = "(%define pick (%case-lambda (() 'none) ((a) a) ((a b . more) (%intrinsic cons b more))))
                (%intrinsic cons (%app pick) (%intrinsic cons (%app pick 'one) (%intrinsic cons (%app pick 'one 'two 'three) '())))";
    assert_eq!(eval(pick), "(none one (two three))");
    // A macro can make one, and a clause is a `%lambda` without defaults or keywords.
    let made = "(%define-syntax two-way (%syntax-rules () ((_ one two) (%case-lambda ((a) one) ((a b) two)))))
                (%let ((f (two-way 'single 'double))) (%intrinsic cons (%app f 1) (%app f 1 2)))";
    assert_eq!(eval(made), "(single . double)");
    assert_eq!(fault("(%define f (%case-lambda ((a) a) ((a b c) c))) (%app f 1 2)"), Fault::Arity);
    assert_eq!(error("(%case-lambda)"), (BadShape, "(%case-lambda)"));
    assert_eq!(error("(%case-lambda ((a (b 1)) a))"), (BadShape, "((a (b 1)) a)"));
    assert_eq!(error("(%case-lambda ((a)))"), (BadShape, "((a))"));
}
