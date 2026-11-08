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
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let prelude = mc.root(1).downcast::<Module>(mc).unwrap();
        let sessions: Vec<SyntaxSession> = files.iter().map(|(_, text)| SyntaxSession::new(mc, text).unwrap()).collect();
        let files: Vec<File> = files.iter().zip(&sessions).map(|(&(language, _), session)| File { language, session }).collect();
        let loaded = load(mc, symbols, prelude, &Source { name, hosts: &[], files: &files, implicit: &[] }, &mut Registry)?;
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
fn errors_say_which_language_they_are_in() {
    let mut arena = arena();
    let scheme = module_in(&mut arena, "main", &[(Scheme, "(define x"), (Native, "1")]);
    assert!(matches!(scheme, Err(Error::Read(_))), "{scheme:?}");
    let native = module_in(&mut arena, "main", &[(Scheme, "1"), (Native, "(nope)")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::NotAForm), "{native:?}");
    let expand = module_in(&mut arena, "main", &[(Native, "1"), (Scheme, "(if)")]);
    assert!(matches!(expand, Err(Error::Expand(_))), "{expand:?}");
}
