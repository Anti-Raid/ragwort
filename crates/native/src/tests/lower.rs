use ragwort_types::gc::{Arena, Gc, Value, WINDOW};
use ragwort_vm::objects::{Condition, ConditionFields, Module};
use ragwort_vm::{Fault, Intrinsic, MIN_SEGMENT, Machine, Outcome, Purity, Read, Request};

use ragwort_types::pair::Pair;
use ragwort_types::string::Strings;

use ragwort_types::pair::Pairs;

use super::*;
use crate::LowerErrorKind::*;

/// Root 0 holds the symbol table and root 1 the modules that have run, as a list of pairs of
/// a name and a module, so code loaded later can require them.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 2);
    arena.mutate(|mc| {
        mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc));
        mc.set_root(1, Value::NIL);
    });
    arena
}

/// The modules in root 1.
struct Registry;

impl<'gc> Resolver<'gc> for Registry {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        let name = Symbols::of(mc.root(0))?.intern_str(&Strings::new(mc), name).ok()?.value(mc);
        let mut entries = Pairs::new(mc).elements(mc.root(1)).filter_map(Pair::of);
        entries.find(|entry| entry.head(mc) == name)?.tail(mc).downcast::<Module>(mc)
    }
}

fn add_host<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    let sum = args.iter().map(|v| v.as_fixnum().ok_or(Fault::WrongType)).sum::<Result<i64, _>>()?;
    Ok(ragwort_vm::Reply::Value(Value::fixnum(sum).unwrap()))
}

fn list_host<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    Ok(ragwort_vm::Reply::Value(Pairs::new(cx.mc()).list(&args.iter().collect::<Vec<_>>())?))
}

/// `(wait n)`: defers with `n`, as a fixnum, for the test to reply to.
fn wait_host<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    Ok(ragwort_vm::Reply::Defer(Box::new(args.get(0).and_then(|n| n.as_fixnum()))))
}

/// The host functions every test's code is loaded with.
static HOSTS: [HostDef; 3] = [
    ragwort_vm::host!("add", 2, Purity::Pure, add_host),
    ragwort_vm::host!("wait", 1, Purity::Impure, wait_host),
    ragwort_vm::host!("list", -1, Purity::Discardable, list_host),
];

fn show<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    ragwort_printer_scheme::to_string(mc, v, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap()
}

/// Runs `thunk` to the end: its value, or the fault it raised.
fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Yielded(_) | Outcome::Deferred(_) => panic!("yielded"),
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(*raised.downcast::<Condition>(mc).unwrap().fault(mc).unwrap()),
        }
    }
}

/// Loads `text` as the module `name` and runs its forms in order. If they all do, other code can
/// require it. Returns the last one's value, written out, or the fault one raised.
fn module_in(arena: &mut Arena, name: &str, text: &str) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let loaded = load(mc, symbols, name, &HOSTS, &[&session], &mut Registry)?;
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            match run(mc, thunk) {
                Ok(value) => last = value,
                Err(fault) => return Ok(Err(fault)),
            }
        }
        let name = symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc);
        let entry = Pairs::new(mc).list_with_tail(vec![name], Value::object(mc, loaded.module)).unwrap();
        let modules = Pairs::new(mc).list_with_tail(vec![entry], mc.root(1)).unwrap();
        mc.set_root(1, modules);
        Ok(Ok(show(mc, last)))
    })
}

fn eval_in(arena: &mut Arena, text: &str) -> Result<Result<String, Fault>, Error> {
    module_in(arena, "main", text)
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
fn letrec_and_definitions() {
    let rev = "(%define reverse
                 (%lambda (xs)
                   (%letrec ((loop (%lambda (xs acc)
                                     (%if (%intrinsic null? xs)
                                          acc
                                          (%app loop (%intrinsic cdr xs) (%intrinsic cons (%intrinsic car xs) acc))))))
                     (%app loop xs '()))))
               (%app reverse '(a b c))";
    assert_eq!(eval(rev), "(c b a)");
    // A definition can be named before it's defined, but not used.
    assert_eq!(eval("(%define f (%lambda () later)) (%define later 'yes) (%app f)"), "yes");
    assert_eq!(fault("(%define f (%lambda () later)) (%app f) (%define later 'yes)"), Fault::Unbound);
    assert_eq!(fault("(%set! later 'no) (%define later 'yes)"), Fault::Unbound);
    assert_eq!(eval("(%define g 'a) (%set! g (%intrinsic cons g g)) g"), "(a . a)");
    assert_eq!(error("nowhere"), (Unbound, "nowhere"));
    assert_eq!(error("(%set! nowhere 'a)"), (Unbound, "nowhere"));
    assert_eq!(error("(%define x 1) (%define x 2)"), (Duplicate, "x"));
    assert_eq!(error("(%let ((x 1)) (%define y x))"), (Definition, "(%define y x)"));
    assert_eq!(error("(%app (%lambda () (%require lib)))"), (Definition, "(%require lib)"));
}

#[test]
fn modules_require_what_others_provide() {
    let mut arena = arena();
    let lib = "(%provide g (rename-out (bump bump!)) counter first)
               (%define g 'a)
               (%define counter 0)
               (%define bump (%lambda () (%set! counter (%intrinsic + counter 1)) counter))
               (%define first (%lambda (p) (%intrinsic car p)))
               (%define hidden 'h)";
    assert_eq!(module_in(&mut arena, "lib", lib), Ok(Ok("#<void>".into())));
    let mut eval = |text: &str| eval_in(&mut arena, text).unwrap().unwrap();
    assert_eq!(eval("(%require lib) g"), "a");
    // An export its module assigns is read as it is.
    assert_eq!(eval("(%require lib) (%app bump!) (%app bump!) counter"), "2");
    assert_eq!(eval("(%require \"lib\") (%app first '(x y))"), "x");
    assert_eq!(eval("(%require (only-in lib g first)) (%app first (%intrinsic cons g g))"), "a");
    assert_eq!(eval("(%require (prefix-in lib: lib)) lib:g"), "a");
    assert_eq!(eval("(%require (rename-in lib (g h))) h"), "a");
    assert_eq!(eval("(%require (except-in lib g)) (%define g 'mine) g"), "mine");
    // Requiring the same thing twice is fine.
    assert_eq!(eval("(%require lib (only-in lib g)) g"), "a");
    let mut error = |text: &str| match eval_in(&mut arena, text) {
        Err(Error::Lower(e)) => (e.kind, text[e.start as usize..e.end as usize].to_string()),
        other => panic!("{text} lowered: {other:?}"),
    };
    assert_eq!(error("(%require lib) hidden"), (Unbound, "hidden".into()));
    assert_eq!(error("(%require lib) bump"), (Unbound, "bump".into()));
    assert_eq!(error("(%require lib) (%set! g 'b)"), (Immutable, "g".into()));
    assert_eq!(error("(%require lib) (%define g 'b)"), (Conflict, "g".into()));
    assert_eq!(error("(%require lib (rename-in lib (first g)))"), (Conflict, "(rename-in lib (first g))".into()));
    assert_eq!(error("(%require (only-in lib nope))"), (NotProvided, "nope".into()));
    assert_eq!(error("(%require (rename-in lib (nope x)))"), (NotProvided, "(nope x)".into()));
    assert_eq!(error("(%require nowhere)"), (Resolve, "nowhere".into()));
    assert_eq!(error("(%require (sideways lib))"), (BadShape, "(sideways lib)".into()));
    assert_eq!(error("(%provide nope)"), (NotDefined, "nope".into()));
    assert_eq!(error("(%define a 1) (%provide a (rename-out (a a)))"), (Duplicate, "(a a)".into()));
    assert_eq!(error("(%provide (all-defined-out x))"), (BadShape, "(all-defined-out x)".into()));
}

#[test]
fn calls_of_imported_wrappers_inline() {
    let mut arena = arena();
    let lib = "(%provide (all-defined-out))
               (%define first (%lambda (p) (%intrinsic car p)))
               (%define sum (%lambda xs (%apply-intrinsic + xs)))
               (%define add1 (%lambda (z) (%intrinsic + z 1)))";
    module_in(&mut arena, "lib", lib).unwrap().unwrap();
    let main = "(%require lib) (%define f (%lambda (p) (%app add1 (%app sum (%app first p) 2 3))))";
    let ops = arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, main).unwrap();
        let loaded = load(mc, symbols, "main", &HOSTS, &[&session], &mut Registry).unwrap();
        for &thunk in &loaded.thunks {
            run(mc, thunk).unwrap();
        }
        let f = ragwort_vm::objects::ModuleFields::items(loaded.module, mc).get(0);
        let f = f.downcast::<ragwort_vm::objects::Closure>(mc).unwrap();
        let ops = ragwort_vm::objects::ClosureFields::code(f, mc).unwrap();
        ragwort_vm::objects::BytecodeFields::ops(ops, mc).unwrap().to_vec()
    });
    assert!(!ops.iter().any(|op| matches!(op, ragwort_vm::Op::Call { .. } | ragwort_vm::Op::TailCall { .. })), "{ops:?}");
    assert_eq!(eval_in(&mut arena, &format!("{main} (%app f '(1))")).unwrap().unwrap(), "7");
}

#[test]
fn a_module_reads_its_variables_unchecked_once_theyre_defined() {
    let ops = |text: &str| {
        let mut arena = arena();
        arena.mutate(|mc| {
            let symbols = Symbols::of(mc.root(0)).unwrap();
            let session = SyntaxSession::new(mc, text).unwrap();
            let loaded = load(mc, symbols, "main", &HOSTS, &[&session], &mut Registry).unwrap();
            let mut ops = Vec::new();
            for thunk in loaded.thunks {
                let thunk = thunk.downcast::<ragwort_vm::objects::Closure>(mc).unwrap();
                let code = ragwort_vm::objects::ClosureFields::code(thunk, mc).unwrap();
                ops.extend_from_slice(ragwort_vm::objects::BytecodeFields::ops(code, mc).unwrap());
                // And the code of the lambdas it makes.
                let constants = ragwort_types::constant::Constants::of(ragwort_vm::objects::BytecodeFields::constants(code, mc)).unwrap();
                for i in 0..constants.len(mc) as u32 {
                    let constant = constants.get(mc, i).unwrap();
                    let closure = constant.downcast::<ragwort_vm::objects::Closure>(mc).and_then(|c| ragwort_vm::objects::ClosureFields::code(c, mc));
                    if let Some(code) = constant.downcast::<ragwort_vm::objects::Bytecode>(mc).or(closure) {
                        ops.extend_from_slice(ragwort_vm::objects::BytecodeFields::ops(code, mc).unwrap());
                    }
                }
            }
            ops
        })
    };
    let checked = |ops: &[ragwort_vm::Op]| ops.iter().any(|op| matches!(op, ragwort_vm::Op::LoadSlotChecked { .. }));
    let unchecked = |ops: &[ragwort_vm::Op]| ops.iter().any(|op| matches!(op, ragwort_vm::Op::LoadSlot { .. }));
    let earlier = ops("(%define a 1) a");
    assert!(unchecked(&earlier) && !checked(&earlier), "{earlier:?}");
    let later = ops("(%define f (%lambda () b)) (%define b 1)");
    assert!(checked(&later), "{later:?}");
    let own = ops("(%define loop (%lambda (n) (%if (%intrinsic eqv? n 0) 0 (%app loop (%intrinsic + n -1)))))");
    assert!(unchecked(&own) && !checked(&own), "{own:?}");
    let not_lambda = ops("(%define x (%let ((y 1)) x))");
    assert!(checked(&not_lambda), "{not_lambda:?}");
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
    let deep = "(%define go
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
    let k = "(%define k (%intrinsic make-continuation-prompt-tag))";
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
    // A body of many forms is one `let`, however many there are.
    let long = format!("(%let ((n '())) {} (%intrinsic length n))", "(%set! n (%intrinsic cons 'a n)) ".repeat(10_000));
    assert_eq!(eval(&long), "10000");
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
    // Each level marks `n` for what it calls, which goes down a level and checks the marks it
    // sees after, as does the level, as frames overflow segments, are cut into records and copied
    // back, again each time a continuation captured at the bottom is called.
    let deep = |inside: &str| {
        format!(
            "(%let* ((key (%intrinsic make-continuation-prompt-tag)) (saved #f) (count 0)
                     (check (%lambda (want) (%if (%intrinsic eqv? (%intrinsic mark-value key #f) want) 0 1))))
               (%letrec ((down (%lambda (n outer)
                                 (%if (%intrinsic eqv? n 0)
                                      (%intrinsic call/cc (%lambda (k) (%set! saved k) 0))
                                      (%let ((r (%intrinsic with-mark key n (%lambda () {inside}))))
                                        (%intrinsic + r (%app check outer)))))))
                 (%let ((r (%app down 2000 #f)))
                   (%set! count (%intrinsic + count 1))
                   (%if (%intrinsic eqv? count 3) (%intrinsic cons r count) (%app saved 0)))))"
        )
    };
    // A mark in tail position replaces the level's, and the requests keep records small.
    let replaced = "(%intrinsic with-mark key (%intrinsic + n 1000)
                      (%lambda ()
                        (%let ((inner (%app down (%intrinsic + n -1) (%intrinsic + n 1000))))
                          (%intrinsic + inner (%app check (%intrinsic + n 1000))))))";
    assert_eq!(eval(&deep(replaced)), "(0 . 3)");
    // With no requests on the way down, the records are as big as segments, and copying them
    // back splits them between a frame and the call that set its mark.
    let calls = "(%let ((inner (%app down (%intrinsic + n -1) n))) (%intrinsic + inner (%app check n)))";
    assert_eq!(eval(&deep(calls)), "(0 . 3)");
}

#[test]
fn deferred_host_calls_go_to_what_runs_the_machine() {
    // A host call defers from the task and from a coroutine it resumes, and each reply is what
    // the call returns; a plain run replies void.
    let text = "(%let ((co (%intrinsic make-coroutine (%lambda () (%intrinsic cons (%call-host wait 3) 'done)))))
                  (%let* ((a (%call-host wait 1)) (b (%intrinsic co/resume co)) (c (%call-host wait 2)))
                    (%intrinsic cons a (%intrinsic cons b c))))";
    let mut arena = arena();
    let asked = arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let [thunk] = load(mc, symbols, "main", &HOSTS, &[&session], &mut Registry).unwrap().thunks[..] else { panic!("one form") };
        let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
        let mut asked = Vec::new();
        let mut outcome = machine.run(mc);
        loop {
            match outcome.unwrap() {
                Outcome::Deferred(waits) => {
                    asked.push(*waits.into_inner().downcast::<Option<i64>>().unwrap());
                    outcome = if asked.len() == 3 { machine.run(mc) } else { machine.reply(mc, Value::fixnum(asked.len() as i64).unwrap()) };
                }
                Outcome::Paused => outcome = machine.run(mc),
                Outcome::Done(v) => break (asked, show(mc, v), format!("{:?}", machine.reply(mc, Value::NIL).err())),
                other => panic!("{other:?}"),
            }
        }
    });
    assert_eq!(asked, (vec![Some(1), Some(3), Some(2)], "(1 (2 . done) . #<void>)".into(), "Some(Finished)".into()));
}

#[test]
fn a_finished_machine_restarts_on_its_stack() {
    // A continuation the first task left keeps its frames while the next runs.
    let text = "(%define k #f)
                (%define first (%lambda () (%intrinsic + 1 (%intrinsic call/cc (%lambda (c) (%set! k c) 1)))))
                (%define again (%lambda (n) (%intrinsic cons n (%intrinsic co/resume (%intrinsic make-coroutine (%lambda () n))))))
                (%define back (%lambda (n) (%app k n)))";
    let mut arena = arena();
    eval_in(&mut arena, text).unwrap().unwrap();
    let shown = arena.mutate(|mc| {
        let module = Registry.resolve(mc, "main", Value::FALSE).unwrap();
        let names = ragwort_types::vector::Vectors::new(mc).vector(ragwort_vm::objects::ModuleFields::names(module, mc)).unwrap();
        let variable = |name: &str| {
            let i = (0..names.len(mc)).find(|&i| show(mc, names.get(mc, i).unwrap()) == name).unwrap();
            ragwort_vm::objects::ModuleFields::items(module, mc).get(i)
        };
        let finish = |machine: &mut Machine| loop {
            match machine.run(mc).unwrap() {
                Outcome::Paused => {}
                Outcome::Done(v) => break show(mc, v),
                other => panic!("{other:?}"),
            }
        };
        let mut machine = Machine::new(mc, MIN_SEGMENT, variable("first"), &[]).unwrap();
        let busy = format!("{:?}", machine.restart(mc, variable("first"), &[]).err());
        let a = finish(&mut machine);
        machine.restart(mc, variable("again"), &[Value::fixnum(7).unwrap()]).unwrap();
        let b = finish(&mut machine);
        machine.restart(mc, variable("back"), &[Value::fixnum(41).unwrap()]).unwrap();
        (busy, a, b, finish(&mut machine))
    });
    assert_eq!(shown, ("Some(NotPending)".into(), "2".into(), "(7 . 7)".into(), "42".into()));
}

#[test]
fn native_code_calls_the_host_and_wraps_it_for_other_code() {
    assert_eq!(eval("(%call-host add 1 2)"), "3");
    assert_eq!(eval("(%call-host list 1 2 3)"), "(1 2 3)");
    // A wrapper is an ordinary procedure, which passes on what the host needs, such as a mark.
    let wrapped = "(%define add (%lambda (a) (%call-host add a (%intrinsic mark-value 'k 0))))
                   (%intrinsic with-mark 'k 5 (%lambda () (%app add 1)))";
    assert_eq!(eval(wrapped), "6");
    assert_eq!(fault("(%call-host add 1 'x)"), Fault::WrongType);
    assert_eq!(error("(%call-host nope 1)"), (UnknownHost, "nope"));
    assert_eq!(error("(%call-host add 1)"), (Arity, "(%call-host add 1)"));
    assert_eq!(error("(%call-host)"), (BadShape, "(%call-host)"));
    assert_eq!(error("(%call-host (add) 1)"), (BadShape, "(add)"));
}
