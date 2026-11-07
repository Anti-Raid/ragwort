use ragwort_types::gc::{Arena, WINDOW};
use ragwort_types::pair::Pair;
use ragwort_types::string::display;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, Intrinsic, MIN_SEGMENT, Machine, Outcome, Read, Request};

use super::*;
use crate::LowerErrorKind::*;

/// Root 0 holds the symbol table and root 1 the globals, so they last from one load to the next.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 2);
    arena.mutate(|mc| {
        mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc));
        mc.set_root(1, Globals::new(mc).unwrap().value(mc));
    });
    arena
}

fn show<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    if let Some(symbol) = Symbol::of(v) {
        return display(&ragwort_types::string::Strings::new(mc), symbol.name(mc)).to_string();
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
        let (symbols, globals) = (Symbols::of(mc.root(0)).unwrap(), Globals::of(mc, mc.root(1)).unwrap());
        let session = SyntaxSession::new(mc, text).unwrap();
        let mut last = Value::VOID;
        for thunk in load(mc, symbols, globals, &session)? {
            let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
            last = loop {
                match machine.run(mc).unwrap() {
                    Outcome::Paused => {}
                    Outcome::Yielded(_) => panic!("yielded"),
                    Outcome::Done(value) => break value,
                    Outcome::Raised(raised) => return Ok(Err(*raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap())),
                }
            };
        }
        Ok(Ok(show(mc, last)))
    })
}

fn eval(text: &str) -> String {
    eval_in(&mut arena(), text).unwrap().unwrap()
}

fn fault(text: &str) -> Fault {
    eval_in(&mut arena(), text).unwrap().unwrap_err()
}

/// The kind of lowering error `text` has, and the text where it is.
fn error(text: &str) -> (LowerErrorKind, &str) {
    match eval_in(&mut arena(), text) {
        Err(Error::Lower(e)) => (e.kind, &text[e.start as usize..e.end as usize]),
        other => panic!("{text} lowered: {other:?}"),
    }
}

#[test]
fn quotes_ifs_and_intrinsics() {
    assert_eq!(eval("'a"), "a");
    assert_eq!(eval("(%quote (a (b . c) 'd))"), "(a (b . c) (quote d))");
    assert_eq!(eval("(%if (%intrinsic null? '()) 'yes 'no)"), "yes");
    assert_eq!(eval("(%if (%intrinsic pair? '()) 'yes 'no)"), "no");
    assert_eq!(eval("(%intrinsic cons 'a (%intrinsic cdr '(b c)))"), "(a c)");
}

#[test]
fn lets_scope_and_shadow() {
    assert_eq!(eval("(%let ((x 'a)) (%let ((x 'b)) x))"), "b");
    // A `%let`'s inits are in the scope around it, a `%letrec`'s in its own.
    assert_eq!(eval("(%let ((x 'a)) (%let ((y x) (x 'b)) (%intrinsic cons y x)))"), "(a . b)");
    assert_eq!(eval("(%let ((x 'outer)) (%letrec ((f (%lambda () x)) (x 'inner)) (%app f)))"), "inner");
    // A `%let*`'s inits see the names before them, which may repeat.
    assert_eq!(eval("(%let ((x 'a)) (%let* ((y x) (x 'b) (z (%intrinsic cons y x)) (x z)) x))"), "(a . b)");
    assert_eq!(eval("(%let* () 'a)"), "a");
    assert_eq!(eval("(%let ((x 'a)) (%intrinsic cons (%let* ((x 'b) (x 'c)) x) x))"), "(c . a)");
    // A body's expressions run in order.
    assert_eq!(eval("(%let ((x 'a)) (%set! x 'b) (%set! x (%intrinsic cons x x)) x)"), "(b . b)");
}

#[test]
fn closures_and_assignment() {
    let push = "(%let ((xs '()))
                  (%let ((push (%lambda (x) (%set! xs (%intrinsic cons x xs)) xs)))
                    (%app push 'a)
                    (%app push 'b)))";
    assert_eq!(eval(push), "(b a)");
    assert_eq!(eval("(%app (%lambda args args) 'a 'b)"), "(a b)");
    assert_eq!(eval("(%app (%app (%lambda (a . r) (%lambda () r)) 'a 'b 'c))"), "(b c)");
}

#[test]
fn letrec_and_globals() {
    let rev = "(%define-global reverse
                 (%lambda (xs)
                   (%letrec ((loop (%lambda (xs acc)
                                     (%if (%intrinsic null? xs)
                                          acc
                                          (%app loop (%intrinsic cdr xs) (%intrinsic cons (%intrinsic car xs) acc))))))
                     (%app loop xs '()))))
               (%app reverse '(a b c))";
    assert_eq!(eval(rev), "(c b a)");
    // Globals last from one load to the next, in the same `Globals`.
    let mut arena = arena();
    assert_eq!(eval_in(&mut arena, "(%define-global g 'a)"), Ok(Ok("#<void>".into())));
    assert_eq!(eval_in(&mut arena, "(%set! g (%intrinsic cons g g)) g"), Ok(Ok("(a . a)".into())));
    // A global can be named before it's defined, but not used.
    assert_eq!(eval("(%define-global f (%lambda () later)) (%define-global later 'yes) (%app f)"), "yes");
    assert_eq!(fault("nowhere"), Fault::Unbound);
    assert_eq!(fault("(%set! nowhere 'a)"), Fault::Unbound);
}

#[test]
fn requests_are_intrinsics_too() {
    let prompt = "(%let ((tag (%intrinsic make-continuation-prompt-tag)))
                    (%intrinsic call-with-prompt tag
                      (%lambda (v) (%intrinsic cons 'aborted v))
                      (%lambda () (%intrinsic cons 'not (%intrinsic abort tag 'x)))))";
    assert_eq!(eval(prompt), "(aborted . x)");
}

#[test]
fn requests_pass_on_their_arguments_from_where_they_are() {
    // At some depth, what with-mark calls doesn't fit on the segment its arguments are on.
    let deep = "(%define-global go
                  (%lambda (n)
                    (%if (%intrinsic eqv? n 0)
                         0
                         (%intrinsic + (%intrinsic with-mark 'k n (%lambda (a b c) (%intrinsic + a (%intrinsic + b c))) n 1 2)
                                       (%app go (%intrinsic + n -1))))))
                (%app go 2000)";
    assert_eq!(eval(deep), "2007000");
    assert_eq!(eval("(%apply-intrinsic apply (%lambda xs xs) 1 '(2 (3 4)))"), "(1 2 3 4)");
    assert_eq!(eval("(%intrinsic apply (%lambda (a b c) (%intrinsic cons a (%intrinsic cons b c))) '(1 2 3))"), "(1 2 . 3)");
    let long = "(%letrec ((up (%lambda (n xs) (%if (%intrinsic eqv? n 0) xs (%app up (%intrinsic + n -1) (%intrinsic cons n xs))))))
                  (%intrinsic length (%intrinsic apply (%lambda xs xs) (%app up 100 '()))))";
    assert_eq!(eval(long), "100");
    let co = "(%intrinsic co/resume (%intrinsic make-coroutine (%lambda (a b c) (%intrinsic cons a (%intrinsic cons b c)))) 1 2 3)";
    assert_eq!(eval(co), "(1 2 . 3)");
}

#[test]
fn reads_see_the_marks_where_they_run() {
    let k = "(%define-global k (%intrinsic make-continuation-prompt-tag))";
    // Read in a frame and used in a closure run under another mark: the frame's value.
    let outer = "(%intrinsic with-mark k 5
                   (%lambda () (%let ((h (%intrinsic mark-value k 0))) (%intrinsic with-mark k 1 (%lambda () h)))))";
    assert_eq!(eval(&format!("{k} {outer}")), "5");
    // Read in a closure run under another mark: that mark's value, inlined or not.
    let inner = "(%let ((f (%lambda () (%intrinsic mark-value k 0))))
                   (%intrinsic cons (%intrinsic with-mark k 1 f) (%intrinsic with-mark k 2 (%lambda () (%app f)))))";
    assert_eq!(eval(&format!("{k} {inner}")), "(1 . 2)");
    let all = "(%intrinsic with-mark k 'a
                 (%lambda () (%intrinsic cons (%intrinsic frame-mark k 0) (%intrinsic frame-marks k 0 #f))))";
    assert_eq!(eval(&format!("{k} {all}")), "(a a)");
    let spread = eval_in(&mut arena(), "(%apply-intrinsic mark-value 'k '(0))");
    assert!(format!("{spread:?}").contains("Arity(Read(MarkValue))"), "{spread:?}");
}

#[test]
fn intrinsics_reads_and_requests_have_different_names() {
    let mut names: Vec<&str> = Intrinsic::ALL.iter().map(|i| i.name()).collect();
    names.extend(Read::ALL.iter().map(|r| r.name()));
    names.extend(Request::ALL.iter().map(|r| r.name()));
    let count = names.len();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), count);
}

#[test]
fn bad_forms_point_at_themselves() {
    assert_eq!(error("(f x)"), (NotAForm, "(f x)"));
    assert_eq!(error("'a ()"), (NotAForm, "()"));
    assert_eq!(error("(%if a b)"), (BadShape, "(%if a b)"));
    assert_eq!(error("(%if a b . c)"), (BadShape, "(%if a b . c)"));
    assert_eq!(error("(%let (x) x)"), (BadShape, "x"));
    assert_eq!(error("(%let ((x)) x)"), (BadShape, "((x))"));
    assert_eq!(error("(%let ((x 'a)))"), (BadShape, "(%let ((x 'a)))"));
    assert_eq!(error("(%let ((x 'a) (x 'b)) x)"), (Duplicate, "x"));
    assert_eq!(error("(%let* ((x)) x)"), (BadShape, "((x))"));
    assert_eq!(error("(%let* ((x 'a)))"), (BadShape, "(%let* ((x 'a)))"));
    assert_eq!(error("(%lambda (a b . a) a)"), (Duplicate, "a"));
    assert_eq!(error("(%lambda ('a) a)"), (BadShape, "'a"));
    assert_eq!(error("(%set! (a) 'b)"), (BadShape, "(a)"));
    assert_eq!(error("(%intrinsic frob 'a)"), (UnknownIntrinsic, "frob"));
    assert_eq!(error("(%intrinsic car)"), (Arity, "(%intrinsic car)"));
    assert_eq!(error("(%intrinsic capture 'a)"), (Arity, "(%intrinsic capture 'a)"));
    let deep = |n| format!("{}'a{}", "(%intrinsic car ".repeat(n), ")".repeat(n));
    assert_eq!(error(&deep(300)).0, TooDeep);
    // Just under the limit, it lowers and compiles, and only fails as it runs.
    assert_eq!(fault(&deep(250)), Fault::WrongType);
    assert!(matches!(eval_in(&mut arena(), "(%if"), Err(Error::Read(_))));
}

#[test]
fn apply_takes_lists_longer_than_a_frame() {
    let list = |n| format!("'({})", vec!["a"; n].join(" "));
    let count = |text: &str| text.matches('a').count();
    for n in [WINDOW - 3, WINDOW - 2, WINDOW - 1, WINDOW, 1000] {
        assert_eq!(count(&eval(&format!("(%intrinsic apply (%lambda xs xs) {})", list(n)))), n);
        assert_eq!(count(&eval(&format!("(%intrinsic apply (%lambda (x y . r) r) {})", list(n)))), n - 2);
        assert_eq!(count(&eval(&format!("(%intrinsic apply (%lambda xs xs) 'a 'a {})", list(n)))), n + 2);
    }
    assert_eq!(fault(&format!("(%intrinsic apply (%lambda (x) x) {})", list(300))), Fault::Arity);
}

#[test]
fn calls_and_lambdas_of_any_size() {
    let symbols = |n| vec!["'a"; n].join(" ");
    let names = |n| (0..n).map(|i| format!("p{i}")).collect::<Vec<_>>().join(" ");
    assert_eq!(eval(&format!("(%intrinsic values-length (%intrinsic values {}))", symbols(300))), "300");
    assert_eq!(eval(&format!("(%app (%lambda xs xs) {})", symbols(300))).matches('a').count(), 300);
    let wide = format!("(%app (%lambda ({}) (%intrinsic cons p0 p299)) {})", names(300), (0..300).map(|i| format!("'s{i}")).collect::<Vec<_>>().join(" "));
    assert_eq!(eval(&wide), "(s0 . s299)");
}

#[test]
fn literals_and_vectors_are_self_quoting() {
    assert_eq!(eval("(%intrinsic cons 1 #t)"), "(1 . #t)");
    assert_eq!(eval("(%intrinsic + 1 2 3)"), "6");
    assert_eq!(eval("'(a `(b ,c ,@d))"), "(a (quasiquote (b (unquote c) (unquote-splicing d))))");
    assert_eq!(eval("(%intrinsic equal? '#(a #(b)) #(a #(b)))"), "#t");
    assert_eq!(error("`a"), (Unsupported, "`a"));
}

#[test]
fn apply_intrinsic_spreads_its_last_argument() {
    assert_eq!(eval("(%apply-intrinsic + '(1 2 3))"), "6");
    assert_eq!(eval("(%apply-intrinsic + 1 2 '(3 4))"), "10");
    assert_eq!(eval("(%apply-intrinsic cons 'a '(b))"), "(a . b)");
    assert_eq!(eval("(%intrinsic values-length (%apply-intrinsic values 'a '(b c)))"), "3");
    assert_eq!(fault("(%apply-intrinsic cons 'a '(b c))"), Fault::Arity);
    assert_eq!(fault("(%apply-intrinsic + 1 'x)"), Fault::WrongType);
    let tag = "(%let ((tag (%intrinsic make-continuation-prompt-tag)))
                 (%intrinsic call-with-prompt tag (%lambda (v) v) (%lambda () (%apply-intrinsic abort tag '(x)))))";
    assert_eq!(eval(tag), "x");
    let many = vec!["1"; 300].join(" ");
    assert_eq!(eval(&format!("(%apply-intrinsic + {many} '(1 1))")), "302");
    assert_eq!(error("(%apply-intrinsic +)"), (BadShape, "(%apply-intrinsic +)"));
}

#[test]
fn the_winders_take_only_winders() {
    let set = "(%let ((w (%intrinsic winders)))
                 (%intrinsic set-winders! (%intrinsic cons (%intrinsic make-winder 'in 'out) w))
                 (%let ((inside (%intrinsic winders)))
                   (%intrinsic set-winders! w)
                   (%intrinsic cons (%intrinsic length inside) (%intrinsic winders))))";
    assert_eq!(eval(set), "(1)");
    assert_eq!(fault("(%intrinsic set-winders! 1)"), Fault::WrongType);
    assert_eq!(fault("(%intrinsic set-winders! '(1))"), Fault::WrongType);
}

#[test]
fn a_mark_set_for_a_call_is_put_back_when_it_returns() {
    let simple = "(%let ((key (%intrinsic make-continuation-prompt-tag)))
                    (%let ((r (%intrinsic with-mark key 1 (%lambda (x) (%intrinsic cons x (%intrinsic mark-value key #f))) 'in)))
                      (%intrinsic cons r (%intrinsic mark-value key #f))))";
    assert_eq!(eval(simple), "((in . 1) . #f)");
    // Each level checks the marks it sees, inside and after its calls, as frames overflow
    // segments, are cut into records and copied back, again each time a continuation captured
    // at the bottom is called.
    let deep = "(%let* ((key (%intrinsic make-continuation-prompt-tag)) (saved #f) (count 0)
                        (check (%lambda (want) (%if (%intrinsic eqv? (%intrinsic mark-value key #f) want) 0 1))))
                  (%letrec ((down (%lambda (n outer)
                                    (%if (%intrinsic eqv? n 0)
                                         (%intrinsic call/cc (%lambda (k) (%set! saved k) 0))
                                         (%let ((r (%intrinsic with-mark key n
                                                     (%lambda ()
                                                       (%intrinsic with-mark key (%intrinsic + n 1000)
                                                         (%lambda ()
                                                           (%let ((inner (%app down (%intrinsic + n -1) (%intrinsic + n 1000))))
                                                             (%intrinsic + inner (%app check (%intrinsic + n 1000))))))))))
                                           (%intrinsic + r (%app check outer)))))))
                    (%let ((r (%app down 2000 #f)))
                      (%set! count (%intrinsic + count 1))
                      (%if (%intrinsic eqv? count 3) (%intrinsic cons r count) (%app saved 0)))))";
    assert_eq!(eval(deep), "(0 . 3)");
    // With no requests on the way down, the records are as big as segments, and copying them
    // back splits them between a frame and the call that set its mark.
    let calls = "(%let* ((key (%intrinsic make-continuation-prompt-tag)) (saved #f) (count 0)
                         (check (%lambda (want) (%if (%intrinsic eqv? (%intrinsic mark-value key #f) want) 0 1))))
                   (%letrec ((down (%lambda (n outer)
                                     (%if (%intrinsic eqv? n 0)
                                          (%intrinsic call/cc (%lambda (k) (%set! saved k) 0))
                                          (%let ((r (%intrinsic with-mark key n
                                                      (%lambda ()
                                                        (%let ((inner (%app down (%intrinsic + n -1) n)))
                                                          (%intrinsic + inner (%app check n)))))))
                                            (%intrinsic + r (%app check outer)))))))
                     (%let ((r (%app down 2000 #f)))
                       (%set! count (%intrinsic + count 1))
                       (%if (%intrinsic eqv? count 3) (%intrinsic cons r count) (%app saved 0)))))";
    assert_eq!(eval(calls), "(0 . 3)");
}
