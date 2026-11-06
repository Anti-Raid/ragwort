use ragwort_types::gc::{Arena, WINDOW};
use ragwort_types::pair::Pair;
use ragwort_types::string::display;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

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
fn bad_forms_point_at_themselves() {
    assert_eq!(error("(f x)"), (NotAForm, "(f x)"));
    assert_eq!(error("'a ()"), (NotAForm, "()"));
    assert_eq!(error("(%if a b)"), (BadShape, "(%if a b)"));
    assert_eq!(error("(%if a b . c)"), (BadShape, "(%if a b . c)"));
    assert_eq!(error("(%let (x) x)"), (BadShape, "x"));
    assert_eq!(error("(%let ((x)) x)"), (BadShape, "((x))"));
    assert_eq!(error("(%let ((x 'a)))"), (BadShape, "(%let ((x 'a)))"));
    assert_eq!(error("(%let ((x 'a) (x 'b)) x)"), (Duplicate, "x"));
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
