use ragwort_types::gc::{Arena, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::Strings;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use super::*;
use crate::Language::{Native, Scheme};

/// Root 0 holds the symbol table, root 1 the prelude's module, which has run, and root 2 the
/// modules other modules can require, as a list of `(name . module)`.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        let loaded = prelude(mc, symbols).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        mc.set_root(1, Value::object(mc, loaded.module));
        mc.set_root(2, Value::NIL);
    });
    arena
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(*raised.downcast::<Condition>(mc).expect("a condition").fault(mc).unwrap()),
            _ => panic!("yielded"),
        }
    }
}

/// The modules registered in root 2.
struct Registry;

impl<'gc> Resolver<'gc> for Registry {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        let name = Symbols::of(mc.root(0))?.intern_str(&Strings::new(mc), name).ok()?.value(mc);
        let mut entries = Pairs::new(mc).elements(mc.root(2)).filter_map(Pair::of);
        entries.find(|entry| entry.head(mc) == name)?.tail(mc).downcast::<Module>(mc)
    }
}

/// Loads the module `name` from `files`, runs it, and registers it for the modules loaded after
/// to require. Returns its last form's value, written out, or the fault one raised.
fn module_in(arena: &mut Arena, name: &str, files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    module_hosting(arena, name, &[], files)
}

/// [`module_in`], for a module whose native files call `hosts`.
fn module_hosting(arena: &mut Arena, name: &str, hosts: &'static [HostDef], files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    module_from(arena, name, hosts, false, files)
}

/// [`module_hosting`], for a module whose native files can name internal intrinsics if
/// `internals`.
fn module_from(arena: &mut Arena, name: &str, hosts: &'static [HostDef], internals: bool, files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let prelude = mc.root(1).downcast::<Module>(mc).unwrap();
        let sessions: Vec<SyntaxSession> = files.iter().map(|(_, text)| SyntaxSession::new(mc, text).unwrap()).collect();
        let files: Vec<File> = files.iter().zip(&sessions).map(|(&(language, _), session)| File { language, session }).collect();
        let loaded = load(mc, symbols, prelude, &Source { name, hosts, files: &files, implicit: &[], internals }, &mut Registry)?;
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            match run(mc, thunk) {
                Ok(value) => last = value,
                Err(fault) => return Ok(Err(fault)),
            }
        }
        let name = symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc);
        let entry = Pairs::new(mc).list_with_tail(vec![name], Value::object(mc, loaded.module)).unwrap();
        mc.set_root(2, Pairs::new(mc).list_with_tail(vec![entry], mc.root(2)).unwrap());
        Ok(Ok(ragwort_printer_scheme::to_string(mc, last, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap()))
    })
}

fn add_host<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
    let sum = args.iter().map(|v| v.as_fixnum().ok_or(Fault::WrongType)).sum::<Result<i64, _>>()?;
    Ok(ragwort_vm::Reply::Value(Value::fixnum(sum).ok_or(Fault::OutOfRange)?))
}

static HOSTS: [HostDef; 1] = [ragwort_vm::host!("add", 2, ragwort_vm::Purity::Impure, add_host)];

#[test]
fn host_wrappers_inline_into_the_modules_that_require_them() {
    let mut arena = arena();
    let bindings = "(%define add (%lambda (a b) (%call-host add a b))) (%provide (all-defined-out))";
    assert_eq!(module_hosting(&mut arena, "host", &HOSTS, &[(Native, bindings)]), Ok(Ok("#<void>".into())));
    // A module that requires it, with no host functions of its own, calls it, and one that
    // requires that calls what it wraps it in.
    let wrapper = "(require \"host\") (define (add10 n) (add n 10)) (provide add10) (add 1 2)";
    assert_eq!(module_in(&mut arena, "mid", &[(Scheme, wrapper)]), Ok(Ok("3".into())));
    assert_eq!(module_in(&mut arena, "bot", &[(Scheme, "(require \"mid\") (list (add10 5) (map add10 '(1 2)))")]), Ok(Ok("(15 (11 12))".into())));
}

#[test]
fn a_modules_files_are_one_body_across_languages() {
    let mut arena = arena();
    // Each file's code refers to what the other defines, by name, but for what a macro defines
    // hygienically.
    let scheme = "(define (inc x) (+ x 1))
                  (define-syntax def-hidden (syntax-rules () ((_ get) (begin (define secret 42) (define (get) secret)))))
                  (def-hidden get-secret)
                  (define (use) (list (twice-native 5) (inc 10) (get-secret)))";
    let native = "(%define twice-native (%lambda (x) (%intrinsic + x x)))
                  (%define result (%app use))
                  result";
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, scheme), (Native, native)]), Ok(Ok("(10 11 42)".into())));
    let defines = "(define-syntax def-hidden (syntax-rules () ((_ get) (begin (define secret 42) (define (get) secret))))) (def-hidden get-secret)";
    assert_eq!(module_in(&mut arena, "other", &[(Scheme, defines), (Native, "(%app get-secret)")]), Ok(Ok("42".into())));
    let hidden = module_in(&mut arena, "other", &[(Scheme, defines), (Native, "secret")]);
    assert!(matches!(hidden, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::Unbound), "{hidden:?}");
    // What a module provides is from any of its files.
    let provides = "(%provide twice-native) (%define twice-native (%lambda (x) (%intrinsic + x x)))";
    module_in(&mut arena, "mixed", &[(Scheme, "(provide inc) (define (inc x) (+ x 1))"), (Native, provides)]).unwrap().unwrap();
    let main = module_in(&mut arena, "user", &[(Scheme, "(require mixed) (inc (twice-native 2))")]);
    assert_eq!(main, Ok(Ok("5".into())));
}

#[test]
fn keyword_procedures_are_called_across_languages() {
    let mut arena = arena();
    let native = "(%provide greet) (%define greet (%lambda (name #:greeting [greeting \"hi\"]) (%intrinsic string-append greeting \" \" name)))";
    module_in(&mut arena, "lib", &[(Native, native)]).unwrap().unwrap();
    let user = module_in(&mut arena, "user", &[(Scheme, "(require lib) (list (greet \"al\") (greet \"al\" #:greeting \"yo\"))")]);
    assert_eq!(user, Ok(Ok("(\"hi al\" \"yo al\")".into())));
    // In one module, each language calls the cores of the keyword procedures the other defines.
    let scheme = "(define (f #:k [k 1]) k) (define (use) (g #:j 3))";
    let native = "(%define g (%lambda (#:j j) (%app f #:k j))) (%app use)";
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, scheme), (Native, native)]), Ok(Ok("3".into())));
    let ops = arena.mutate(|mc| {
        let (symbols, prelude) = (Symbols::of(mc.root(0)).unwrap(), mc.root(1).downcast::<Module>(mc).unwrap());
        let sessions = [SyntaxSession::new(mc, scheme).unwrap(), SyntaxSession::new(mc, native).unwrap()];
        let files = [File { language: Scheme, session: &sessions[0] }, File { language: Native, session: &sessions[1] }];
        let loaded = load(mc, symbols, prelude, &Source { name: "main", hosts: &[], files: &files, implicit: &[], internals: false }, &mut Registry).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        let items = ragwort_vm::objects::ModuleFields::items(loaded.module, mc);
        let closures = (0..items.len()).filter_map(|i| items.get(i).downcast::<ragwort_vm::objects::Closure>(mc));
        let code = closures.map(|f| ragwort_vm::objects::ClosureFields::code(f, mc).unwrap());
        code.map(|code| format!("{:?}", ragwort_vm::objects::BytecodeFields::ops(code, mc).unwrap())).collect::<Vec<_>>().join("\n")
    });
    assert!(ops.contains("Call") && !ops.contains("KeywordApply"), "{ops}");
}

/// The instructions of the procedures the Scheme module `text`, named `name`, defines, once it has
/// run.
fn closure_ops(arena: &mut Arena, name: &str, text: &str) -> String {
    arena.mutate(|mc| {
        let (symbols, prelude) = (Symbols::of(mc.root(0)).unwrap(), mc.root(1).downcast::<Module>(mc).unwrap());
        let session = SyntaxSession::new(mc, text).unwrap();
        let files = [File { language: Scheme, session: &session }];
        let loaded = load(mc, symbols, prelude, &Source { name, hosts: &[], files: &files, implicit: &[], internals: false }, &mut Registry).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        let items = ragwort_vm::objects::ModuleFields::items(loaded.module, mc);
        let closures = (0..items.len()).filter_map(|i| items.get(i).downcast::<ragwort_vm::objects::Closure>(mc));
        let code = closures.map(|f| ragwort_vm::objects::ClosureFields::code(f, mc).unwrap());
        code.map(|code| format!("{:?}", ragwort_vm::objects::BytecodeFields::ops(code, mc).unwrap())).collect::<Vec<_>>().join("\n")
    })
}

/// How many times `ops` has `name` as a whole word, as an instruction's or an intrinsic's is.
fn count(ops: &str, name: &str) -> usize {
    ops.split(|c: char| !c.is_alphanumeric()).filter(|&word| word == name).count()
}

/// How many procedure calls `ops` has, not counting calls of intrinsics.
fn calls(ops: &str) -> usize {
    count(ops, "Call") + count(ops, "TailCall")
}

#[test]
fn structs_are_used_across_modules() {
    let mut arena = arena();
    let shapes = "(provide (struct-out point) (struct-out session) origin)
                  (struct point (x [y #:mutable]))
                  (struct session (token) #:identity-eq?)
                  (define origin (point 0 0))";
    module_in(&mut arena, "shapes", &[(Scheme, shapes)]).unwrap().unwrap();
    let user = "(require shapes)
                (struct point3 point (z))
                (define p (point3 1 2 3))
                (set-point-y! p 20)
                (define (first-of p) (point-x p))
                (list p (first-of p) (point-y p) (point? origin) (point3? origin) (equal? origin (point 0 0)) (session-token (session 7)) (equal? (session 1) (session 1))
                      struct:point (map point-x (list origin)))";
    let expected = "(#(struct:point3 1 20 3) 1 20 #t #f #t 7 #f #<struct-type:point> (0))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    // A struct's name stands for its type whatever it's required as, and with everything else.
    let renamed = "(require (prefix-in s: shapes)) (struct p3 s:point (z)) (list (s:point-x (p3 1 2 3)) (s:point? (s:point 1 2)) (s:point? (p3 1 2 3)))";
    assert_eq!(module_in(&mut arena, "renamed", &[(Scheme, renamed)]), Ok(Ok("(1 #t #t)".into())));
    module_in(&mut arena, "all", &[(Scheme, "(provide (all-defined-out)) (struct pair2 (a b))")]).unwrap().unwrap();
    let all = "(require all) (struct triple pair2 (c)) (list (pair2-b (triple 1 2 3)) (pair2? (pair2 1 2)))";
    assert_eq!(module_in(&mut arena, "uses-all", &[(Scheme, all)]), Ok(Ok("(2 #t)".into())));
    // What's exported is what the form defines, and no more.
    let hidden = module_in(&mut arena, "hidden", &[(Scheme, "(require shapes) set-point-x!")]);
    assert!(matches!(hidden, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::Unbound), "{hidden:?}");
    let not_one = module_in(&mut arena, "not-one", &[(Scheme, "(provide (struct-out f)) (define (f) 1)")]);
    assert!(matches!(not_one, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::NotDefined), "{not_one:?}");
    // A call of another module's accessor reads the field itself, the type a constant.
    let ops = closure_ops(&mut arena, "reader", "(require shapes) (define (first-of p) (point-x p))");
    assert!(ops.contains("StructRef") && calls(&ops) == 0, "{ops}");
    // Either language defines structs the other uses, in one module or across them.
    module_in(&mut arena, "native-shapes", &[(Native, "(%provide (struct-out pair2)) (%struct pair2 (a (b #:mutable)))")]).unwrap().unwrap();
    let scheme = "(require native-shapes) (struct triple pair2 (c)) (define t (triple 1 2 3)) (set-pair2-b! t 20)
                  (list (match t [(triple a b c) (list a b c)]) (struct-copy pair2 t [a 10]) (match (pair2 5 6) [(pair2 a _) a]))";
    assert_eq!(module_in(&mut arena, "scheme-user", &[(Scheme, scheme)]), Ok(Ok("((1 20 3) #(struct:pair2 10 20) 5)".into())));
    let mixed = [(Native, "(%struct cell (v))"), (Scheme, "(struct labelled cell (name)) (define (unwrap c) (match c [(cell v) v])) (unwrap (labelled 4 'four))")];
    assert_eq!(module_in(&mut arena, "mixed", &mixed), Ok(Ok("4".into())));
    let native_user = "(%require shapes) (%struct tagged point (tag)) (%app point-y (%app tagged 1 2 'tag))";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native_user)]), Ok(Ok("2".into())));
    // Sealing goes with a struct to the modules that require it.
    let bank = "(provide (struct-out account) (struct-out receipt))
                (struct account (id [balance #:mutable]))
                (struct receipt (amount) #:sealed)";
    module_in(&mut arena, "bank", &[(Scheme, bank)]).unwrap().unwrap();
    let customer = "(require bank) (struct savings account (rate)) (define s (savings 1 5 2)) (set-account-balance! s 9) (list s (receipt-amount (receipt 3)))";
    assert_eq!(module_in(&mut arena, "customer", &[(Scheme, customer)]), Ok(Ok("(#(struct:savings 1 9 2) 3)".into())));
    let sealed = module_in(&mut arena, "sealed", &[(Scheme, "(require bank) (struct more receipt (x))")]);
    assert!(matches!(sealed, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::BadSyntax), "{sealed:?}");
    let sealed = module_in(&mut arena, "sealed", &[(Native, "(%require bank) (%struct more receipt (x))")]);
    assert!(matches!(sealed, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::BadShape), "{sealed:?}");
    // A match or a copy of another module's struct reads the fields itself too: a match
    // without checking the type again, once its test has.
    let ops = closure_ops(&mut arena, "matcher", "(require shapes) (define (f p) (match p [(point x y) (+ x y)]))");
    assert!(ops.contains("IsStructDerivedFrom") && ops.contains("StructField") && !ops.contains("StructRef") && calls(&ops) == 0, "{ops}");
    let ops = closure_ops(&mut arena, "copier", "(require shapes) (define (f p n) (struct-copy point p [y n]))");
    assert!(ops.contains("StructRef") && ops.contains("MakeStruct") && calls(&ops) == 0, "{ops}");
    // What the form is built from isn't written directly, in either language, unless the
    // embedder lets a module's native code.
    for name in ["make-struct-type", "make-struct", "struct-ref", "struct-field", "struct-set!"] {
        let scheme = module_in(&mut arena, "direct", &[(Scheme, &format!("(require bank) ({name} struct:account 1 2)"))]);
        assert!(matches!(scheme, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::Unbound), "{name}: {scheme:?}");
    }
    let direct = [
        ("make-struct-type", "(%intrinsic make-struct-type 'forged #f '() '() 0)"),
        ("make-struct", "(%intrinsic make-struct struct:account 1 -1)"),
        ("struct-ref", "(%intrinsic struct-ref (%app account 1 1) struct:account 0)"),
        ("struct-set!", "(%intrinsic struct-set! (%app account 1 1) struct:account 1 -1)"),
        ("struct-field", "(%intrinsic struct-field (%app account 1 1) 0)"),
        ("make-struct", "(%apply-intrinsic make-struct struct:account '(1 -1))"),
    ];
    for (name, body) in direct {
        let native = module_in(&mut arena, "direct", &[(Native, &format!("(%require bank) {body}"))]);
        assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::UnknownIntrinsic), "{name}: {native:?}");
    }
    let trusted = "(%require bank) (%define a (%intrinsic make-struct struct:account 1 -1)) (%intrinsic struct-set! a struct:account 1 -2) (%intrinsic struct-field a 1)";
    assert_eq!(module_from(&mut arena, "trusted", &[], true, &[(Native, trusted)]), Ok(Ok("-2".into())));
    // The procedures that look at a struct as a whole are any code's.
    let whole = "(%require bank) (%define a (%app account 1 5)) (%intrinsic cons (%intrinsic struct-fields (%intrinsic struct-type a)) (%intrinsic struct->list a))";
    assert_eq!(module_in(&mut arena, "whole", &[(Native, whole)]), Ok(Ok("((id balance) 1 5)".into())));
    // No language assigns what a struct form defines.
    let native = module_in(&mut arena, "main", &[(Scheme, "(struct point (x))"), (Native, "(%set! point-x 1)")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::Immutable), "{native:?}");
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, "(struct point (x))"), (Native, "(%app point-x (%app point 4))")]), Ok(Ok("4".into())));
}

#[test]
fn no_language_assigns_a_keyword_procedure() {
    // Scheme calls of it go to its core, so assigning it would leave them calling the old one.
    let mut arena = arena();
    let native = module_in(&mut arena, "main", &[(Scheme, "(define (f #:k k) k)"), (Native, "(%set! f 1)")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::Immutable), "{native:?}");
    let scheme = module_in(&mut arena, "main", &[(Scheme, "(define (f #:k k) k) (set! f 1)")]);
    assert!(matches!(scheme, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::Immutable), "{scheme:?}");
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, "(define (f k) k)"), (Native, "(%set! f 1) f")]), Ok(Ok("1".into())));
}

#[test]
fn errors_say_which_language_they_are_in() {
    let mut arena = arena();
    let scheme = module_in(&mut arena, "main", &[(Scheme, "(define x"), (Native, "1")]);
    assert!(matches!(scheme, Err(Error::Read(_))), "{scheme:?}");
    let native = module_in(&mut arena, "main", &[(Scheme, "1"), (Native, "(nope)")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::NotAForm), "{native:?}");
    let expand = module_in(&mut arena, "main", &[(Native, "1"), (Scheme, "(if)")]);
    assert!(matches!(expand, Err(Error::Expand(_))), "{expand:?}");
    // An empty require or provide spec is bad syntax, in either language.
    for text in ["(require ())", "(provide ())"] {
        let scheme = module_in(&mut arena, "main", &[(Scheme, text)]);
        assert!(matches!(scheme, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::BadSyntax), "{text}: {scheme:?}");
        let native = module_in(&mut arena, "main", &[(Native, &format!("(%{})", &text[1..text.len() - 1]))]);
        assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::BadShape), "{text}: {native:?}");
    }
}

/// What the compiler knows of a struct value it uses, and no more than that.
#[test]
fn struct_code_is_optimized() {
    let mut arena = arena();
    let kinds = "(provide (struct-out point) (struct-out point3) (struct-out circle) (struct-out cell))
                 (struct point (x y)) (struct point3 point (z)) (struct circle (r)) (struct cell ([v #:mutable]))";
    module_in(&mut arena, "kinds", &[(Scheme, kinds)]).unwrap().unwrap();
    let mut n = 0;
    let mut ops_of = |arena: &mut Arena, text: &str| {
        n += 1;
        closure_ops(arena, &format!("user{n}"), &format!("(require kinds) {text}"))
    };
    let made = |ops: &str| count(ops, "MakeStruct");
    let (checked, unchecked, tests) = (|ops: &str| count(ops, "StructRef"), |ops: &str| count(ops, "StructField"), |ops: &str| count(ops, "IsStructDerivedFrom"));

    // A struct made only to be read isn't made: its fields are what it was given, whether
    // they're variables or have to be evaluated first.
    let ops = ops_of(&mut arena, "(define (f a b) (let ((p (point a b))) (+ (point-x p) (point-y p))))");
    assert!(made(&ops) == 0 && checked(&ops) == 0 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, "(define (f g) (let ((p (point (g) (g)))) (point? p) (point-y p)))");
    assert!(made(&ops) == 0 && checked(&ops) == 0 && tests(&ops) == 0 && calls(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, "(define (f a b) (point-x (point a b)))");
    assert!(made(&ops) == 0 && checked(&ops) == 0, "{ops}");
    // One that's kept is made, and its fields that can't be set are still what it was given.
    let ops = ops_of(&mut arena, "(define (f a b g) (let ((p (point a b))) (g p) (point-x p)))");
    assert!(made(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 0, "{ops}");
    // A field that can be set is read, as what the struct is given to may set it: but its type
    // is known.
    let ops = ops_of(&mut arena, "(define (f n g) (let ((c (cell n))) (g c) (cell-v c)))");
    assert!(made(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");

    // The first read of a value by a type checks the type, and those after it don't.
    let ops = ops_of(&mut arena, "(define (f p) (+ (point-x p) (point-y p)))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, "(define (f p) (if (point? p) (+ (point-x p) (point-y p)) 0))");
    assert!(tests(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 2, "{ops}");
    // A read by a supertype is known of what's known to be of the subtype, and not the other
    // way.
    let ops = ops_of(&mut arena, "(define (f p) (if (point3? p) (point-x p) 0))");
    assert!(checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, "(define (f p) (if (point? p) (point3-z p) 0))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    // What one branch or one procedure learns, the code after it doesn't know.
    let ops = ops_of(&mut arena, "(define (f p c) (if c (point-x p) 0) (point-y p))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, "(define (f p h) (h (lambda () (point-x p))) (point-y p))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, "(define (f p) (if (point? p) 1 (point-x p)))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    // A variable that's assigned is known nothing of.
    let ops = ops_of(&mut arena, "(define (f p q) (let ((a (point-x p))) (set! p q) (+ a (point-y p))))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");

    // A value of one type is of its supertypes, of no type apart from them, and of no other
    // kind: a test of a subtype still has to be made.
    let ops = ops_of(&mut arena, "(define (f v) (if (point3? v) (list (point? v) (circle? v) (struct? v) (pair? v) (procedure? v)) 0))");
    assert!(tests(&ops) == 1 && count(&ops, "IsStruct") == 0 && count(&ops, "IsPair") == 0 && count(&ops, "IsProcedure") == 0, "{ops}");
    let ops = ops_of(&mut arena, "(define (f v) (if (point? v) (point3? v) 0))");
    assert!(tests(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, "(define (f a) (let ((p (point3 a a a))) (list (point? p) (point3? p) (circle? p) (struct? p) (vector? p))))");
    assert!(tests(&ops) == 0 && made(&ops) == 0, "{ops}");
    // A match reads the fields it binds, with the one test of the type.
    let ops = ops_of(&mut arena, "(define (f p) (match p [(point x _) x]))");
    assert!(tests(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, "(define (f p) (match p [(point3 _ _ z) z] [(point x y) (+ x y)] [(circle r) r]))");
    assert!(tests(&ops) == 3 && checked(&ops) == 0 && unchecked(&ops) == 4, "{ops}");

    // It all does what the code says.
    let run = "(require kinds)
        (define (sum a b) (let ((p (point a b))) (+ (point-x p) (point-y p))))
        (define (twice g) (let ((p (point (g) (g)))) (list (point? p) (point-y p) (point-x p))))
        (define (kept n g) (let ((c (cell n))) (g c) (cell-v c)))
        (define (both p) (+ (point-x p) (point-y p)))
        (define (after p c) (if c (point-x p) 0) (point-y p))
        (define (kind v) (if (point? v) (list (point3? v) (circle? v) (struct? v) (pair? v)) (if (circle? v) 'circle 'other)))
        (define (area v) (match v [(point3 _ _ z) z] [(point x y) (+ x y)] [(circle r) r] [_ 'none]))
        (define n 0) (define (next) (set! n (+ n 1)) n)
        (define (caught thunk) (guard (e (#t (error-object-kind e))) (thunk)))
        (list (sum 1 2) (twice next) (kept 1 (lambda (c) (set-cell-v! c 9))) (both (point3 1 2 3)) (after (point 1 2) #f)
              (kind (point 1 2)) (kind (point3 1 2 3)) (kind (circle 1)) (kind 5)
              (map area (list (point3 1 2 3) (point 1 2) (circle 4) 'x))
              (caught (lambda () (both 5))) (caught (lambda () (both (circle 1)))) (caught (lambda () (after (circle 1) #f))))";
    let expected = "(3 (#t 2 1) 9 3 2 (#f #f #t #f) (#t #f #t #f) circle other (3 3 4 none) wrong-type wrong-type wrong-type)";
    assert_eq!(module_in(&mut arena, "runs", &[(Scheme, run)]), Ok(Ok(expected.into())));
}
