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
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let prelude = mc.root(1).downcast::<Module>(mc).unwrap();
        let sessions: Vec<SyntaxSession> = files.iter().map(|(_, text)| SyntaxSession::new(mc, text).unwrap()).collect();
        let files: Vec<File> = files.iter().zip(&sessions).map(|(&(language, _), session)| File { language, session }).collect();
        let loaded = load(mc, symbols, prelude, &Source { name, hosts, files: &files, implicit: &[] }, &mut Registry)?;
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
        let loaded = load(mc, symbols, prelude, &Source { name: "main", hosts: &[], files: &files, implicit: &[] }, &mut Registry).unwrap();
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
