use ragwort_types::gc::{Arena, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::Strings;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::{Fault, MIN_SEGMENT, Machine, Outcome};

use super::*;
use crate::Language::{Native, Scheme};

#[path = "macros.rs"]
mod macros;

/// Creates an arena for a test. Root 0 holds the symbol table. Root 1 holds the `scheme` module, which every test module requires implicitly. Root 2 holds the
/// modules that other modules can require, as a list of `(name . module)` pairs. It starts with Scheme's libraries, which have already run.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        let built = scheme(mc, symbols).unwrap();
        for &thunk in &built.thunks {
            run(mc, thunk).unwrap();
        }
        mc.set_root(1, Value::object(mc, built.all()));
        let mut modules = Value::NULL;
        for &(name, module) in &built.modules {
            let name = symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc);
            let entry = Pairs::new(mc).cons(name, Value::object(mc, module)).unwrap().value(mc);
            modules = Pairs::new(mc).cons(entry, modules).unwrap().value(mc);
        }
        mc.set_root(2, modules);
    });
    arena
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Result<Value<'gc>, Fault> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(raised.downcast::<Condition>(mc).expect("a condition").failure(mc).unwrap().fault),
            _ => panic!("yielded"),
        }
    }
}

/// A [`Resolver`] that finds the modules registered in root 2.
struct Registry;

impl<'gc> Resolver<'gc> for Registry {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        let name = Symbols::of(mc.root(0))?.intern_str(&Strings::new(mc), name).ok()?.value(mc);
        let mut entries = Pairs::new(mc).elements(mc.root(2)).filter_map(Pair::of);
        entries.find(|entry| entry.head(mc) == name)?.tail(mc).downcast::<Module>(mc)
    }
}

/// Loads the module `name` from `files`, runs it, and registers it so that modules loaded later
/// can require it. Returns the written form of the last form's value, or the fault that a form raised.
fn module_in(arena: &mut Arena, name: &str, files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    module_hosting(arena, name, &[], files)
}

/// Works like [`module_in`], for a module whose native files can call `hosts`.
fn module_hosting(arena: &mut Arena, name: &str, hosts: &'static [HostDef], files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    module_from(arena, name, hosts, false, files)
}

/// Works like [`module_hosting`]. The module's native files can name internal intrinsics if
/// `internals` is true.
fn module_from(arena: &mut Arena, name: &str, hosts: &'static [HostDef], internals: bool, files: &[(Language, &str)]) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let prelude = mc.root(1).downcast::<Module>(mc).unwrap();
        let sessions: Vec<SyntaxSession> = files.iter().map(|(_, text)| SyntaxSession::new(mc, text).unwrap()).collect();
        let files: Vec<File> = files.iter().zip(&sessions).map(|(&(language, _), session)| File { language, session }).collect();
        let loaded = load(mc, symbols, &Source { name, hosts, files: &files, implicit: &[prelude], internals }, &mut Registry)?;
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
    // A module with no host functions of its own requires `host` and calls the wrapper. A third module
    // requires the second and calls a procedure that wraps the wrapper.
    let wrapper = "(require \"host\") (define (add10 n) (add n 10)) (provide add10) (add 1 2)";
    assert_eq!(module_in(&mut arena, "mid", &[(Scheme, wrapper)]), Ok(Ok("3".into())));
    assert_eq!(module_in(&mut arena, "bot", &[(Scheme, "(require \"mid\") (list (add10 5) (map add10 '(1 2)))")]), Ok(Ok("(15 (11 12))".into())));
}

#[test]
fn a_modules_files_are_one_body_across_languages() {
    let mut arena = arena();
    // Code in each file refers by name to the definitions of the other file. The exception is a definition that a macro
    // introduces hygienically.
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
    // A module can provide definitions from any of its files.
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
    // Within one module, code in each language calls the core of a keyword procedure that the other language defines.
    let scheme = "(define (f #:k [k 1]) k) (define (use) (g #:j 3))";
    let native = "(%define g (%lambda (#:j j) (%app f #:k j))) (%app use)";
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, scheme), (Native, native)]), Ok(Ok("3".into())));
    let ops = arena.mutate(|mc| {
        let (symbols, prelude) = (Symbols::of(mc.root(0)).unwrap(), mc.root(1).downcast::<Module>(mc).unwrap());
        let sessions = [SyntaxSession::new(mc, scheme).unwrap(), SyntaxSession::new(mc, native).unwrap()];
        let files = [File { language: Scheme, session: &sessions[0] }, File { language: Native, session: &sessions[1] }];
        let loaded = load(mc, symbols, &Source { name: "main", hosts: &[], files: &files, implicit: &[prelude], internals: false }, &mut Registry).unwrap();
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

/// Loads and runs `text` as the Scheme module `name`. Returns the instructions of the procedures that the module defines, as
/// debug text.
fn closure_ops(arena: &mut Arena, name: &str, text: &str) -> String {
    arena.mutate(|mc| {
        let (symbols, prelude) = (Symbols::of(mc.root(0)).unwrap(), mc.root(1).downcast::<Module>(mc).unwrap());
        let session = SyntaxSession::new(mc, text).unwrap();
        let files = [File { language: Scheme, session: &session }];
        let loaded = load(mc, symbols, &Source { name, hosts: &[], files: &files, implicit: &[prelude], internals: false }, &mut Registry).unwrap();
        for thunk in loaded.thunks {
            run(mc, thunk).unwrap();
        }
        let items = ragwort_vm::objects::ModuleFields::items(loaded.module, mc);
        let closures = (0..items.len()).filter_map(|i| items.get(i).downcast::<ragwort_vm::objects::Closure>(mc));
        let code = closures.map(|f| ragwort_vm::objects::ClosureFields::code(f, mc).unwrap());
        code.map(|code| format!("{:?}", ragwort_vm::objects::BytecodeFields::ops(code, mc).unwrap())).collect::<Vec<_>>().join("\n")
    })
}

/// Returns how many times `name` occurs in `ops` as a whole word. The name of an instruction or of an intrinsic is a whole word.
fn count(ops: &str, name: &str) -> usize {
    ops.split(|c: char| !c.is_alphanumeric()).filter(|&word| word == name).count()
}

/// Returns the number of procedure calls in `ops`. Calls of intrinsics are not counted.
fn calls(ops: &str) -> usize {
    count(ops, "Call") + count(ops, "TailCall")
}

#[test]
fn an_image_holds_modules_for_another_arena() {
    let library = "(provide (struct-out point) (struct-out user #:omit-constructor) make-user greet next! table big area total)
                   (struct point (x [y #:mutable]))
                   (struct user (name age))
                   (define (make-user name age) (user name age))
                   (define (greet name #:greeting [greeting \"hello\"]) (string-append greeting \", \" name))
                   (define next! (let ((n 0)) (lambda () (set! n (+ n 1)) n)))
                   (next!)
                   (define table (list 'apple \"a string that is too long to fit in a word\" #(1 2 3) #\\x 1.5 (point 1 2)))
                   (define big (expt 2 100))
                   (define (area p) (match p [(point x y) (* x y)]))";
    let native = "(%define total (%lambda (a b) (%call-host add a b)))";
    let user = "(require library)
                (define p (point 3 4))
                (set-point-y! p 5)
                (list (area p) (match (make-user \"ann\" 3) [(user name _ ...) name]) (greet \"bo\") (greet \"cy\" #:greeting \"hi\") (next!) (next!)
                      (eq? (car table) 'apple) table (+ big 1) (total 20 22) (struct-copy point p [x 9]) (equal? (point 1 2) (list-ref table 5))
                      (string->symbol \"apple\") (eq? (string->symbol \"apple\") (car table)))";
    let expected = "(15 \"ann\" \"hello, bo\" \"hi, cy\" 2 3 #t (apple \"a string that is too long to fit in a word\" #(1 2 3) #\\x 1.5 #(struct:point 1 2)) 1267650600228229401496703205377 42 #(struct:point 9 5) #t apple #t)";
    let mut arena = arena();
    assert_eq!(module_hosting(&mut arena, "library", &HOSTS, &[(Scheme, library), (Native, native)]).map(|ran| ran.is_ok()), Ok(true));
    arena.collect();
    let bytes = arena.mutate(|mc| image::save(mc, &[mc.root(0), mc.root(1), mc.root(2)])).unwrap();
    // The arena that saved the image keeps working as before.
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));

    fn restored(bytes: &[u8]) -> Arena {
        let mut arena = Arena::new(1 << 24, 3);
        arena.mutate(|mc| {
            let roots = image::load(mc, bytes, HOSTS.iter()).unwrap();
            assert_eq!(roots.len(), 3);
            roots.iter().enumerate().for_each(|(i, &root)| mc.set_root(i, root));
        });
        arena
    }
    // A second arena that loads the image has the state that the first arena had when it saved the image. It has none of the first arena's later changes.
    let mut other = restored(&bytes);
    assert_eq!(module_in(&mut other, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    other.collect();
    assert_eq!(module_in(&mut other, "again", &[(Scheme, "(require library) (list (next!) (area (point 2 3)))")]), Ok(Ok("(4 6)".into())));
    let wrong = module_in(&mut other, "wrong", &[(Scheme, "(require library) (user \"ann\" 3)")]);
    assert!(matches!(wrong, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::NoConstructor), "{wrong:?}");
    // An arena that loaded an image can save an image in turn. The new image includes the modules that were loaded after the first image.
    other.collect();
    let more = other.mutate(|mc| image::save(mc, &[mc.root(0), mc.root(1), mc.root(2)])).unwrap();
    let mut third = restored(&more);
    assert_eq!(module_in(&mut third, "last", &[(Scheme, "(require library again) (next!)")]), Ok(Ok("5".into())));

    // An image identifies the host functions that its code calls. Loading fails if one of them is not supplied.
    let hostless = Arena::new(1 << 24, 3).mutate(|mc| image::load(mc, &bytes, []).map(|roots| roots.len()));
    assert_eq!(hostless, Err(image::ImageError::Host("add".into())));
    let mut cut = bytes.clone();
    cut.truncate(bytes.len() / 2);
    let cut = Arena::new(1 << 24, 3).mutate(|mc| image::load(mc, &cut, HOSTS.iter()).map(|roots| roots.len()));
    assert_eq!(cut, Err(image::ImageError::Load(ragwort_types::gc::image::LoadError::Malformed)));
}

/// A table saved in an image is complete in the arena that loads it. Its entries keep their order, and each key still finds its entry. A list used as a key is a key by identity, and a lookup still finds it although the list is at a different place in the new arena.
#[test]
fn an_image_keeps_tables_and_their_keys() {
    let library = "(provide scores point lookup ann half)
                   (define point (list 1 2))
                   (define scores (table 'ann 1 \"a key that is too long to fit in a word\" 2 3 'three 2.5 'half point 'here))
                   (table-set! scores (expt 2 100) 'big)
                   (table-delete! scores 3)
                   (define (lookup key) (table-ref scores key 'none))
                   (define (ann) (table-ref scores 'ann 'gone))
                   (define (half) (table-ref scores 2.5))
                   (ann) (half)";
    let user = "(require library)
                (list (ann) (half) (table->list scores) (lookup 'ann) (lookup \"a key that is too long to fit in a word\") (lookup 3) (lookup 2.5) (lookup (expt 2 100)) (lookup point) (lookup (list 1 2))
                      (begin (table-set! scores 'new 9) (table-delete! scores 'ann) (table-keys scores)) (ann))";
    let expected = "(1 half ((ann . 1) (\"a key that is too long to fit in a word\" . 2) (2.5 . half) ((1 2) . here) (1267650600228229401496703205376 . big)) 1 2 none half big here none \
                    (\"a key that is too long to fit in a word\" 2.5 (1 2) 1267650600228229401496703205376 new) gone)";
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "library", &[(Scheme, library)]).map(|ran| ran.is_ok()), Ok(true));
    arena.collect();
    let bytes = arena.mutate(|mc| image::save(mc, &[mc.root(0), mc.root(1), mc.root(2)])).unwrap();
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    for _ in 0..2 {
        let mut other = Arena::new(1 << 24, 3);
        other.mutate(|mc| {
            let roots = image::load(mc, &bytes, HOSTS.iter()).unwrap();
            roots.iter().enumerate().for_each(|(i, &root)| mc.set_root(i, root));
        });
        other.collect();
        assert_eq!(module_in(&mut other, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    }
}

/// In a branch where `nil?` or `none?` held for a variable, the variable is known to be that value. So a truth test of the variable in that branch is decided at compile time.
#[test]
fn a_test_of_a_variable_known_to_be_false_is_compiled_away() {
    let mut arena = arena();
    let known = "(provide a b)
                 (define (a x) (if (nil? x) (if x 'yes 'no) 'other))
                 (define (b x) (if (none? x) (if x 'yes 'no) 'other))";
    let ops = closure_ops(&mut arena, "known", known);
    assert_eq!((count(&ops, "JumpIfFalse"), count(&ops, "BranchIntrinsic1")), (0, 2), "{ops}");
    let unknown = "(provide a) (define (a x) (if (pair? x) (if x 'yes 'no) (if x 'true 'false)))";
    let ops = closure_ops(&mut arena, "unknown", unknown);
    assert_eq!((count(&ops, "JumpIfFalse"), count(&ops, "BranchIntrinsic1")), (1, 1), "{ops}");
}

/// A table read or write whose key is a constant is compiled to an instruction with a hint, whatever kind of value the key is. A key that is computed uses the plain operation.
#[test]
fn constant_keys_compile_to_hinted_table_instructions() {
    let mut arena = arena();
    let hinted = "(provide a b c d e)
                  (define (a t) (table-ref t 'name))
                  (define (b t) (list (table-ref t \"id\") (table-ref t 7 0) (table-ref t #\\x)))
                  (define (c t v) (table-set! t 'name v))
                  (define (d t v) (begin (table-set! t \"n\" v) (table-ref t 'name)))
                  (define (e t) (if (table-ref t 'on) (table-ref t 'a) (table-ref t 'b)))";
    let ops = closure_ops(&mut arena, "hinted", hinted);
    // The read with the default 0 keeps a register for its default. The others have the default `#f`.
    assert_eq!((count(&ops, "TableRefHinted"), count(&ops, "TableRefOrHinted"), count(&ops, "TableSetHinted"), count(&ops, "TableRef"), count(&ops, "TableSet")), (7, 1, 2, 0, 0), "{ops}");
    // A long string, a large float and a bignum are objects. As constant keys they are hinted too. Only the keys read from a variable are not.
    let plain = "(provide a b c)
                 (define (a t k) (table-ref t k))
                 (define (b t) (list (table-ref t \"a key that is too long to fit in a word\") (table-ref t 1.5e300) (table-ref t (expt 2 100))))
                 (define (c t k v) (table-set! t k v))";
    let ops = closure_ops(&mut arena, "plain", plain);
    assert_eq!((count(&ops, "TableRefHinted"), count(&ops, "TableRefOrHinted"), count(&ops, "TableSetHinted"), count(&ops, "TableRef"), count(&ops, "TableSet")), (3, 0, 0, 1, 1), "{ops}");
}

/// Host-owned data exposed as external tables: an event that the host received, which programs read, and a set of counters, which programs also modify.
mod events {
    use ragwort_types::Error;
    use ragwort_types::gc::Mutation;
    use ragwort_types::string::from_str;
    use ragwort_types::table::{ExternalTable, Key, Refused, Tables};
    use ragwort_types::vector::{ExternalVector, Vectors};

    use super::*;

    /// A message with the kinds of field that a JSON payload has: a number, text, a nested object, an array, `false` and `null`.
    struct Message;
    struct Author;

    #[derive(Default)]
    struct Counters(Vec<(String, i64)>);

    /// The names that a message mentions. This is an array of the payload, exposed as an external vector and read in place.
    struct Mentions;

    /// A vector of numbers that programs can modify.
    struct Numbers(Vec<i64>);

    impl ExternalVector for Mentions {
        fn len(&self) -> usize {
            2
        }

        fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
            Ok(from_str(&Strings::new(mc), ["ann", "bo"][index])?.value())
        }
    }

    impl ExternalVector for Numbers {
        const WRITABLE: bool = true;

        fn len(&self) -> usize {
            self.0.len()
        }

        fn get<'gc>(&self, _: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
            Ok(Value::fixnum(self.0[index]).expect("a small number"))
        }

        fn set<'gc>(&mut self, _: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Refused> {
            self.0[index] = value.as_fixnum().ok_or(Refused)?;
            Ok(())
        }
    }

    const FIELDS: [&str; 6] = ["id", "content", "author", "mentions", "pinned", "edited"];

    impl ExternalTable for Message {
        fn len(&self) -> usize {
            FIELDS.len()
        }

        fn has(&self, key: Key<'_>) -> bool {
            matches!(key, Key::Symbol(name) if FIELDS.contains(&name))
        }

        fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
            Ok(Some(match key {
                Key::Symbol("id") => Value::fixnum(7).expect("a small number"),
                Key::Symbol("content") => from_str(&Strings::new(mc), "hello from the host").map(|text| text.value())?,
                Key::Symbol("author") => Tables::new(mc).external(Author, 0)?.value(mc),
                Key::Symbol("mentions") => Vectors::new(mc).external(Mentions, 0)?.value(mc),
                Key::Symbol("pinned") => Value::FALSE,
                Key::Symbol("edited") => Value::NONE,
                _ => return Ok(None),
            }))
        }

        fn keys(&self) -> impl Iterator<Item = Key<'_>> {
            FIELDS.into_iter().map(Key::Symbol)
        }
    }

    impl ExternalTable for Author {
        fn len(&self) -> usize {
            1
        }

        fn has(&self, key: Key<'_>) -> bool {
            key == Key::Symbol("name")
        }

        fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
            let found = if self.has(key) {
                Some(from_str(&Strings::new(mc), "cy")?.value())
            } else {
                None
            };
            Ok(found)
        }

        fn keys(&self) -> impl Iterator<Item = Key<'_>> {
            std::iter::once(Key::Symbol("name"))
        }
    }

    impl ExternalTable for Counters {
        const WRITABLE: bool = true;

        fn len(&self) -> usize {
            self.0.len()
        }

        fn has(&self, key: Key<'_>) -> bool {
            matches!(key, Key::String(name) if self.0.iter().any(|(held, _)| held == name))
        }

        fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
            let Key::String(name) = key else { return Ok(None) };
            Ok(self.0.iter().find(|(held, _)| held == name).and_then(|&(_, count)| Value::fixnum(count)))
        }

        fn keys(&self) -> impl Iterator<Item = Key<'_>> {
            self.0.iter().map(|(name, _)| Key::String(name))
        }

        fn set<'gc>(&mut self, _: &Mutation<'gc>, key: Key<'_>, value: Value<'gc>) -> Result<(), Refused> {
            let (Key::String(name), Some(count)) = (key, value.as_fixnum()) else { return Err(Refused) };
            match self.0.iter_mut().find(|(held, _)| held == name) {
                Some(entry) => entry.1 = count,
                None => self.0.push((name.to_string(), count)),
            }
            Ok(())
        }

        fn delete(&mut self, key: Key<'_>) -> bool {
            let before = self.0.len();
            self.0.retain(|(held, _)| key != Key::String(held));
            self.0.len() < before
        }

        fn clear(&mut self) {
            self.0.clear();
        }
    }

    fn message<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, _: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        Ok(ragwort_vm::Reply::Value(Tables::new(cx.mc()).external(Message, 0)?.value(cx.mc())))
    }

    fn counters<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, _: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        Ok(ragwort_vm::Reply::Value(Tables::new(cx.mc()).external(Counters::default(), 0)?.value(cx.mc())))
    }

    fn numbers<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, _: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        Ok(ragwort_vm::Reply::Value(Vectors::new(cx.mc()).external(Numbers(vec![1, 2, 3]), 24)?.value(cx.mc())))
    }

    pub static HOSTS: [HostDef; 3] = [
        ragwort_vm::host!("message", 0, ragwort_vm::Purity::Impure, message),
        ragwort_vm::host!("counters", 0, ragwort_vm::Purity::Impure, counters),
        ragwort_vm::host!("numbers", 0, ragwort_vm::Purity::Impure, numbers),
    ];
}

/// A program uses a host-owned table as it uses a table of its own: it can read it, iterate over it, compare it and print it. It can modify the table only if the host's type is writable.
#[test]
fn programs_use_tables_the_host_holds() {
    let mut arena = arena();
    let bindings = "(%define message (%lambda () (%call-host message))) (%define counters (%lambda () (%call-host counters))) (%define numbers (%lambda () (%call-host numbers))) (%provide (all-defined-out))";
    assert_eq!(module_hosting(&mut arena, "events", &events::HOSTS, &[(Native, bindings)]), Ok(Ok("#<void>".into())));
    let reading = "(require \"events\")
                   (define msg (message))
                   (list (table? msg) (table-length msg) (table-ref msg 'id) (table-ref msg 'content) (table-ref (table-ref msg 'author) 'name) (vector-ref (table-ref msg 'mentions) 1)
                         (eq? (table-ref msg 'author) (table-ref msg 'author)) (eq? (table-ref msg 'content) (table-ref msg 'content))
                         (table-ref msg 'missing) (table-ref msg 'missing 'none) (table-ref msg \"id\") (table-has? msg 'missing) (table-ref msg (list 'id)))";
    assert_eq!(module_in(&mut arena, "reading", &[(Scheme, reading)]), Ok(Ok("(#t 6 7 \"hello from the host\" \"cy\" \"bo\" #t #t #f none #f #f #f)".into())));
    // `false`, `null` and a missing key are three distinct cases.
    let nothing = "(require \"events\")
                   (define msg (message))
                   (map (lambda (key) (list (table-has? msg key) (table-ref msg key 'absent) (if (table-ref msg key) 'true 'false))) '(pinned edited deleted))";
    assert_eq!(module_in(&mut arena, "nothing", &[(Scheme, nothing)]), Ok(Ok("((#t #f false) (#t #none false) (#f absent false))".into())));
    let walking = "(require \"events\")
                   (define msg (message))
                   (define seen '())
                   (table-for-each (lambda (key value) (set! seen (cons key seen))) msg)
                   (list (reverse seen) (table-keys msg) (length (table->list msg)) (table->list (table-copy (table-ref msg 'author)))
                         (equal? (table-ref msg 'author) (table 'name \"cy\")) (equal? (table 'name \"cy\") (table-ref msg 'author)) (equal? msg (message)) (equal? msg (table 'id 7))
                         msg)";
    let written = "((id content author mentions pinned edited) (id content author mentions pinned edited) 6 ((name . \"cy\")) #t #t #t #f \
                   #table((id . 7) (content . \"hello from the host\") (author . #table((name . \"cy\"))) (mentions . #(\"ann\" \"bo\")) (pinned . #f) (edited . #none)))";
    assert_eq!(module_in(&mut arena, "walking", &[(Scheme, walking)]), Ok(Ok(written.into())));
    let refused = "(require \"events\")
                   (define msg (message))
                   (define (kind thunk) (guard (e (#t (list (error-object-kind e) (error-object-who e)))) (thunk)))
                   (list (kind (lambda () (table-set! msg 'id 8))) (kind (lambda () (table-delete! msg 'id))) (kind (lambda () (table-clear! msg))) (kind (lambda () (table-update! msg 'id (lambda (id) (+ id 1)))))
                         (table-ref msg 'id) (table-length msg))";
    assert_eq!(module_in(&mut arena, "refused", &[(Scheme, refused)]), Ok(Ok("((immutable table-set!) (immutable table-delete!) (immutable table-clear!) (immutable table-set!) 7 6)".into())));
    // An array of the payload is a host-owned vector. A vector that the program can modify is host-owned too.
    let arrays = "(require \"events\")
                  (define msg (message))
                  (define names (table-ref msg 'mentions))
                  (define nums (numbers))
                  (define (kind thunk) (guard (e (#t (list (error-object-kind e) (error-object-who e)))) (thunk)))
                  (list (vector? names) (vector-length names) (vector-ref names 0) (vector->list names) (equal? names (vector \"ann\" \"bo\")) (equal? (vector \"ann\" \"bo\") names) (equal? names (vector \"ann\"))
                        (eq? names (table-ref msg 'mentions)) names
                        (kind (lambda () (vector-set! names 0 \"x\"))) (kind (lambda () (vector-ref names 2))) (kind (lambda () (vector-ref names -1)))
                        (begin (vector-set! nums 1 20) (vector->list nums)) (kind (lambda () (vector-set! nums 0 \"one\"))) (kind (lambda () (vector-set! nums 3 1))) (vector-ref nums 1) nums
                        (vector-map string-length names) (vector-map (lambda (name n) (list name n)) names nums) (let ((sum 0)) (vector-for-each (lambda (n) (set! sum (+ sum n))) nums) sum))";
    let read = "(#t 2 \"ann\" (\"ann\" \"bo\") #t #t #f #t #(\"ann\" \"bo\") (immutable vector-set!) (out-of-range vector-ref) (out-of-range vector-ref) \
                (1 20 3) (wrong-type vector-set!) (out-of-range vector-set!) 20 #(1 20 3) #(3 2) #((\"ann\" 1) (\"bo\" 20)) 24)";
    assert_eq!(module_in(&mut arena, "arrays", &[(Scheme, arrays)]), Ok(Ok(read.into())));
    let counting = "(require \"events\")
                    (define counts (counters))
                    (table-set! counts \"hits\" 1)
                    (table-update! counts \"hits\" (lambda (hits) (+ hits 1)))
                    (table-update! counts \"misses\" (lambda (misses) (+ misses 1)) 0)
                    (define (kind thunk) (guard (e (#t (error-object-kind e))) (thunk)))
                    (list (table->list counts) (table-length counts) (kind (lambda () (table-set! counts \"hits\" \"many\"))) (kind (lambda () (table-set! counts 'hits 1))) (table-ref counts \"hits\")
                          (table-delete! counts \"hits\") (table-delete! counts \"hits\") (table-keys counts) (table->list counts) (begin (table-clear! counts) (list (table-length counts) counts)))";
    assert_eq!(module_in(&mut arena, "counting", &[(Scheme, counting)]), Ok(Ok("(((\"hits\" . 2) (\"misses\" . 1)) 2 wrong-type wrong-type 2 #t #f (\"misses\") ((\"misses\" . 1)) (0 #table()))".into())));
}

/// `sums` and `products` each define a host function named `combine`. The two functions do different things, and each belongs to one module.
mod sums {
    use super::*;

    fn combine<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        let sum = args.iter().map(|v| v.as_fixnum().ok_or(Fault::WrongType)).sum::<Result<i64, _>>()?;
        Ok(ragwort_vm::Reply::Value(Value::fixnum(sum).ok_or(Fault::OutOfRange)?))
    }

    pub static HOSTS: [HostDef; 1] = [ragwort_vm::host!("combine", 2, ragwort_vm::Purity::Impure, combine)];
}

mod products {
    use super::*;

    fn combine<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        let product = args.iter().map(|v| v.as_fixnum().ok_or(Fault::WrongType)).product::<Result<i64, _>>()?;
        Ok(ragwort_vm::Reply::Value(Value::fixnum(product).ok_or(Fault::OutOfRange)?))
    }

    pub static HOSTS: [HostDef; 1] = [ragwort_vm::host!("combine", 2, ragwort_vm::Purity::Impure, combine)];
}

/// Two different host functions with the same name and the same module path. Their [`HostDef::path`]s are equal,
/// so the path cannot tell them apart.
static TWINS: [HostDef; 2] = [
    {
        fn twin<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, _: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
            Ok(ragwort_vm::Reply::Value(Value::TRUE))
        }
        ragwort_vm::host!("twin", 0, ragwort_vm::Purity::Impure, twin)
    },
    {
        fn twin<'s, 'gc>(_: &mut ragwort_vm::HostContext<'s, 'gc>, _: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
            Ok(ragwort_vm::Reply::Value(Value::FALSE))
        }
        ragwort_vm::host!("twin", 0, ragwort_vm::Purity::Impure, twin)
    },
];

#[test]
fn an_image_names_each_host_function_by_where_it_is() {
    assert_ne!(sums::HOSTS[0].path, products::HOSTS[0].path);
    assert!(sums::HOSTS[0].path.ends_with("tests::sums::combine"), "{}", sums::HOSTS[0].path);
    let wrapper = "(%provide combine) (%define combine (%lambda (a b) (%call-host combine a b)))";
    let user = "(require (prefix-in s: sums) (prefix-in p: products)) (list (s:combine 3 4) (p:combine 3 4) (map s:combine '(1 2) '(3 4)) (map p:combine '(1 2) '(3 4)))";
    let mut arena = arena();
    module_hosting(&mut arena, "sums", &sums::HOSTS, &[(Native, wrapper)]).unwrap().unwrap();
    module_hosting(&mut arena, "products", &products::HOSTS, &[(Native, wrapper)]).unwrap().unwrap();
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("(7 12 (4 6) (3 8))".into())));
    arena.collect();
    let bytes = arena.mutate(|mc| image::save(mc, &[mc.root(0), mc.root(1), mc.root(2)])).unwrap();
    // Each module calls its own host function, in whichever order the host functions are supplied.
    for hosts in [[&sums::HOSTS[0], &products::HOSTS[0]], [&products::HOSTS[0], &sums::HOSTS[0]]] {
        let mut other = Arena::new(1 << 24, 3);
        other.mutate(|mc| {
            let roots = image::load(mc, &bytes, hosts).unwrap();
            roots.iter().enumerate().for_each(|(i, &root)| mc.set_root(i, root));
        });
        assert_eq!(module_in(&mut other, "after", &[(Scheme, user)]), Ok(Ok("(7 12 (4 6) (3 8))".into())));
    }
    fn load(bytes: &[u8], hosts: Vec<&'static HostDef>) -> Result<usize, image::ImageError> {
        Arena::new(1 << 24, 3).mutate(|mc| image::load(mc, bytes, hosts).map(|roots| roots.len()))
    }
    // A host function that is supplied twice counts once. A host function that is not supplied is reported by its name.
    assert_eq!(load(&bytes, vec![&sums::HOSTS[0], &products::HOSTS[0], &sums::HOSTS[0]]), Ok(3));
    assert_eq!(load(&bytes, vec![&sums::HOSTS[0]]), Err(image::ImageError::Host("combine".into())));
    // Two host functions that an image could not tell apart are rejected.
    assert_eq!(TWINS[0].path, TWINS[1].path);
    assert_eq!(load(&bytes, vec![&sums::HOSTS[0], &products::HOSTS[0], &TWINS[0], &TWINS[1]]), Err(image::ImageError::SameHost(TWINS[0].path)));
}

#[test]
fn structs_provided_without_their_constructor_are_only_matched() {
    use ragwort_native::LowerErrorKind;
    use ragwort_scheme::ExpandErrorKind;
    let mut arena = arena();
    let users = "(provide (struct-out user #:omit-constructor) make-user)
                 (struct user (name [age #:mutable]) #:extra-constructor-name raw-user)
                 (define (make-user name age) (if (string? name) (user name age) (raw-user \"nobody\" 0)))
                 (struct-copy user (make-user 'x 1) [age 2])";
    assert_eq!(module_in(&mut arena, "users", &[(Scheme, users)]), Ok(Ok("#(struct:user \"nobody\" 2)".into())));
    // Every binding except the constructors is imported, and the struct's name works in a `match` pattern.
    let reader = "(require users) (define u (make-user \"ann\" 3)) (set-user-age! u 4)
                  (list (match u [(user name age) (list name age)]) (match u [(user name _ ...) name]) (match 5 [(user _ ...) 'user] [_ 'other])
                        (user? u) (user-name u) u struct:user)";
    let expected = "((\"ann\" 4) \"ann\" other #t \"ann\" #(struct:user \"ann\" 4) #<struct-type:user>)";
    assert_eq!(module_in(&mut arena, "reader", &[(Scheme, reader)]), Ok(Ok(expected.into())));
    let renamed = "(require (prefix-in u: users)) (match (u:make-user \"bo\" 1) [(u:user name _) name])";
    assert_eq!(module_in(&mut arena, "renamed", &[(Scheme, renamed)]), Ok(Ok("\"bo\"".into())));
    // A module that requires `users` cannot construct a `user`, except through the other procedures that `users` provides.
    let wrong = [
        ("(user \"ann\" 3)", ExpandErrorKind::NoConstructor),
        ("user", ExpandErrorKind::NoConstructor),
        ("(map user '(\"ann\") '(3))", ExpandErrorKind::NoConstructor),
        ("(struct-copy user (make-user \"ann\" 3) [age 5])", ExpandErrorKind::NoConstructor),
        ("(struct admin user (level))", ExpandErrorKind::BadSyntax),
        ("(raw-user \"ann\" 3)", ExpandErrorKind::Unbound),
        ("(set! user 1)", ExpandErrorKind::Immutable),
    ];
    for (text, kind) in wrong {
        let result = module_in(&mut arena, "wrong", &[(Scheme, &format!("(require users) {text}"))]);
        assert!(matches!(result, Err(Error::Expand(e)) if e.kind == kind), "{text}: {result:?}");
    }
    let native = "(%require users) (%app user-name (%app make-user \"cy\" 1))";
    assert_eq!(module_in(&mut arena, "native-reader", &[(Native, native)]), Ok(Ok("\"cy\"".into())));
    for (text, kind) in [("(%app user \"ann\" 3)", LowerErrorKind::NoConstructor), ("user", LowerErrorKind::NoConstructor), ("(%struct admin user (level))", LowerErrorKind::BadShape)] {
        let result = module_in(&mut arena, "wrong", &[(Native, &format!("(%require users) {text}"))]);
        assert!(matches!(result, Err(Error::Lower(e)) if e.kind == kind), "{text}: {result:?}");
    }
    // Native ragwort provides a struct without its constructor in the same way.
    let pairs = "(%provide (struct-out pair2 #:omit-constructor) twice) (%struct pair2 (a b)) (%define twice (%lambda (a) (%app pair2 a a)))";
    module_in(&mut arena, "pairs", &[(Native, pairs)]).unwrap().unwrap();
    assert_eq!(module_in(&mut arena, "pair-reader", &[(Scheme, "(require pairs) (match (twice 4) [(pair2 a b) (+ a b)])")]), Ok(Ok("8".into())));
    let made = module_in(&mut arena, "pair-maker", &[(Scheme, "(require pairs) (pair2 1 2)")]);
    assert!(matches!(made, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::NoConstructor), "{made:?}");
    for (text, kind) in [("(provide (struct-out p #:nope))", ExpandErrorKind::BadSyntax), ("(provide (struct-out p #:omit-constructor) p)", ExpandErrorKind::Duplicate)] {
        let result = module_in(&mut arena, "wrong", &[(Scheme, &format!("{text} (struct p (x))"))]);
        assert!(matches!(result, Err(Error::Expand(e)) if e.kind == kind), "{text}: {result:?}");
    }
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
    // A struct's name refers to its type under whatever name it is required. That also holds for a struct that `(all-defined-out)` exports with everything else.
    let renamed = "(require (prefix-in s: shapes)) (struct p3 s:point (z)) (list (s:point-x (p3 1 2 3)) (s:point? (s:point 1 2)) (s:point? (p3 1 2 3)))";
    assert_eq!(module_in(&mut arena, "renamed", &[(Scheme, renamed)]), Ok(Ok("(1 #t #t)".into())));
    module_in(&mut arena, "all", &[(Scheme, "(provide (all-defined-out)) (struct pair2 (a b))")]).unwrap().unwrap();
    let all = "(require all) (struct triple pair2 (c)) (list (pair2-b (triple 1 2 3)) (pair2? (pair2 1 2)))";
    assert_eq!(module_in(&mut arena, "uses-all", &[(Scheme, all)]), Ok(Ok("(2 #t)".into())));
    // `struct-out` exports exactly the bindings that the struct form defines.
    let hidden = module_in(&mut arena, "hidden", &[(Scheme, "(require shapes) set-point-x!")]);
    assert!(matches!(hidden, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::Unbound), "{hidden:?}");
    let not_one = module_in(&mut arena, "not-one", &[(Scheme, "(provide (struct-out f)) (define (f) 1)")]);
    assert!(matches!(not_one, Err(Error::Expand(e)) if e.kind == ragwort_scheme::ExpandErrorKind::NotDefined), "{not_one:?}");
    // A call of another module's accessor compiles to a direct field read, with the struct type as a constant.
    let ops = closure_ops(&mut arena, "reader", "(require shapes) (define (first-of p) (point-x p))");
    assert!(ops.contains("StructRef") && calls(&ops) == 0, "{ops}");
    // Each language can use the structs that the other language defines, within one module or across modules.
    module_in(&mut arena, "native-shapes", &[(Native, "(%provide (struct-out pair2)) (%struct pair2 (a (b #:mutable)))")]).unwrap().unwrap();
    let scheme = "(require native-shapes) (struct triple pair2 (c)) (define t (triple 1 2 3)) (set-pair2-b! t 20)
                  (list (match t [(triple a b c) (list a b c)]) (struct-copy pair2 t [a 10]) (match (pair2 5 6) [(pair2 a _) a]))";
    assert_eq!(module_in(&mut arena, "scheme-user", &[(Scheme, scheme)]), Ok(Ok("((1 20 3) #(struct:pair2 10 20) 5)".into())));
    let mixed = [(Native, "(%struct cell (v))"), (Scheme, "(struct labelled cell (name)) (define (unwrap c) (match c [(cell v) v])) (unwrap (labelled 4 'four))")];
    assert_eq!(module_in(&mut arena, "mixed", &mixed), Ok(Ok("4".into())));
    let native_user = "(%require shapes) (%struct tagged point (tag)) (%app point-y (%app tagged 1 2 'tag))";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native_user)]), Ok(Ok("2".into())));
    // A sealed struct stays sealed in the modules that require it.
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
    // A `match` or a `struct-copy` of another module's struct compiles to direct field reads too. The `match`
    // does not check the type again after its own type test.
    let ops = closure_ops(&mut arena, "matcher", "(require shapes) (define (f p) (match p [(point x y) (+ x y)]))");
    assert!(ops.contains("IsStructDerivedFrom") && ops.contains("StructField") && !ops.contains("StructRef") && calls(&ops) == 0, "{ops}");
    let ops = closure_ops(&mut arena, "copier", "(require shapes) (define (f p n) (struct-copy point p [y n]))");
    assert!(ops.contains("StructRef") && ops.contains("MakeStruct") && calls(&ops) == 0, "{ops}");
    // Code in either language cannot use the internal intrinsics that a struct form is built from. The exception is
    // the native code of a module that the embedder loads with `internals` set.
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
    // Any code can use the intrinsics that inspect a whole struct.
    let whole = "(%require bank) (%define a (%app account 1 5)) (%intrinsic cons (%intrinsic struct-fields (%intrinsic struct-type a)) (%intrinsic struct->list a))";
    assert_eq!(module_in(&mut arena, "whole", &[(Native, whole)]), Ok(Ok("((id balance) 1 5)".into())));
    // Neither language can assign a binding that a struct form defines.
    let native = module_in(&mut arena, "main", &[(Scheme, "(struct point (x))"), (Native, "(%set! point-x 1)")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == ragwort_native::LowerErrorKind::Immutable), "{native:?}");
    assert_eq!(module_in(&mut arena, "main", &[(Scheme, "(struct point (x))"), (Native, "(%app point-x (%app point 4))")]), Ok(Ok("4".into())));
}

#[test]
fn no_language_assigns_a_keyword_procedure() {
    // Scheme calls of a keyword procedure go directly to its core. Assigning the procedure would leave those calls with the old core.
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

/// Checks the facts that the compiler derives about struct values. The compiler must use each fact and must not assume more than it knows.
#[test]
fn struct_code_is_optimized() {
    let mut arena = arena();
    let kinds = "(provide (struct-out point) (struct-out point3) (struct-out circle) (struct-out cell))
                 (struct point (x y)) (struct point3 point (z)) (struct circle (r)) (struct cell ([v #:mutable]))";
    module_in(&mut arena, "kinds", &[(Scheme, kinds)]).unwrap().unwrap();
    let mut users = 0;
    fn ops_of(arena: &mut Arena, users: &mut usize, text: &str) -> String {
        *users += 1;
        closure_ops(arena, &format!("user{users}"), &format!("(require kinds) {text}"))
    }
    fn made(ops: &str) -> usize {
        count(ops, "MakeStruct")
    }
    fn checked(ops: &str) -> usize {
        count(ops, "StructRef")
    }
    fn unchecked(ops: &str) -> usize {
        count(ops, "StructField")
    }
    fn tests(ops: &str) -> usize {
        count(ops, "IsStructDerivedFrom")
    }

    // A struct that is created only to be read is never allocated. A read of a field becomes the constructor argument, whether
    // that argument is a variable or an expression that must be evaluated first.
    let ops = ops_of(&mut arena, &mut users, "(define (f a b) (let ((p (point a b))) (+ (point-x p) (point-y p))))");
    assert!(made(&ops) == 0 && checked(&ops) == 0 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f g) (let ((p (point (g) (g)))) (point? p) (point-y p)))");
    assert!(made(&ops) == 0 && checked(&ops) == 0 && tests(&ops) == 0 && calls(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f a b) (point-x (point a b)))");
    assert!(made(&ops) == 0 && checked(&ops) == 0, "{ops}");
    // A struct that escapes is allocated. Reads of its immutable fields still become the constructor arguments.
    let ops = ops_of(&mut arena, &mut users, "(define (f a b g) (let ((p (point a b))) (g p) (point-x p)))");
    assert!(made(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 0, "{ops}");
    // A mutable field is read from the struct, because the code that receives the struct may set the field. The struct's type
    // is still known, so the read is unchecked.
    let ops = ops_of(&mut arena, &mut users, "(define (f n g) (let ((c (cell n))) (g c) (cell-v c)))");
    assert!(made(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");

    // The first field read of a value checks the value's type. Later reads of the same value do not.
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (+ (point-x p) (point-y p)))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (if (point? p) (+ (point-x p) (point-y p)) 0))");
    assert!(tests(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 2, "{ops}");
    // A value that is known to be of a subtype needs no check for a read through the supertype. The reverse
    // does not hold.
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (if (point3? p) (point-x p) 0))");
    assert!(checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (if (point? p) (point3-z p) 0))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    // A fact that is learned in one branch or inside one procedure is not known to the code after it.
    let ops = ops_of(&mut arena, &mut users, "(define (f p c) (if c (point-x p) 0) (point-y p))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p h) (h (lambda () (point-x p))) (point-y p))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (if (point? p) 1 (point-x p)))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 0, "{ops}");
    // Nothing is known about a variable that is assigned.
    let ops = ops_of(&mut arena, &mut users, "(define (f p q) (let ((a (point-x p))) (set! p q) (+ a (point-y p))))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");

    // A value of one struct type is also of that type's supertypes. It is of no unrelated struct type and of no other
    // kind of value. A test for a subtype must still be made.
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (if (point3? v) (list (point? v) (circle? v) (struct? v) (pair? v) (procedure? v)) 0))");
    assert!(tests(&ops) == 1 && count(&ops, "IsStruct") == 0 && count(&ops, "IsPair") == 0 && count(&ops, "IsProcedure") == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (if (point? v) (point3? v) 0))");
    assert!(tests(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f a) (let ((p (point3 a a a))) (list (point? p) (point3? p) (circle? p) (struct? p) (vector? p))))");
    assert!(tests(&ops) == 0 && made(&ops) == 0, "{ops}");
    // A `match` reads only the fields that it binds, after a single type test.
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (match p [(point x _) x]))");
    assert!(tests(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (match p [(point3 _ _ z) z] [(point x y) (+ x y)] [(circle r) r]))");
    assert!(tests(&ops) == 3 && checked(&ops) == 0 && unchecked(&ops) == 4, "{ops}");

    // A struct that is only read, set and tested in the code that creates it is never allocated, even if its
    // fields are set. Each field becomes a variable. The same holds for a struct that is passed to procedures that are
    // inlined. A struct that escapes is allocated.
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n)) (get (lambda (x) (cell-v x)))) (set-cell-v! c (+ (get c) 1)) (get c)))");
    assert!(made(&ops) == 0 && count(&ops, "StructSet") == 0 && calls(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n)) (bump! (lambda (x) (set-cell-v! x 5)))) (bump! c) (cell-v c)))");
    assert!(made(&ops) == 0 && count(&ops, "StructSet") == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n))) (set-cell-v! c (+ (cell-v c) 1)) (if (cell? c) (cell-v c) 0)))");
    assert!(made(&ops) == 0 && checked(&ops) == 0 && unchecked(&ops) == 0 && count(&ops, "StructSet") == 0 && tests(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n))) (lambda () (set-cell-v! c (+ (cell-v c) 1)) (cell-v c))))");
    assert!(made(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n))) (set-cell-v! c (+ (cell-v c) 1)) c))");
    assert!(made(&ops) == 1 && count(&ops, "StructSet") == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n))) (set-cell-v! c c) (cell-v c)))");
    assert!(made(&ops) == 1 && count(&ops, "StructSet") == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f n) (let ((c (cell n))) (if c (cell-v c) 0)))");
    assert!(made(&ops) == 1, "{ops}");

    // A type test that fails shows that the value is not of that type, nor of any subtype.
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (if (point? v) 1 (if (point3? v) 2 (if (point? v) 3 4))))");
    assert!(tests(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (cond [(point3? v) 1] [(point? v) 2] [(point3? v) 3] [else 4]))");
    assert!(tests(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (if (point? v) 1 0) (point? v))");
    assert!(tests(&ops) == 2, "{ops}");

    // An immutable field is read once. Later reads reuse the first read that dominates them,
    // whatever code runs in between. A mutable field is read again.
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (let ((a (point-x p))) (+ a (point-x p))))");
    assert!(checked(&ops) + unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (* (point-x p) (point-x p)))");
    assert!(checked(&ops) + unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p g) (if (> (point-x p) 0) (begin (g) (point-x p)) (- (point-x p))))");
    assert!(checked(&ops) + unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p) (match p [(point x _) (+ x (point-x p) (point-y p))]))");
    assert!(checked(&ops) == 0 && unchecked(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p c) (if c (point-x p) 0) (point-x p))");
    assert!(checked(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f p q) (+ (point-x p) (point-x q)))");
    assert!(checked(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f c g) (let ((a (cell-v c))) (g) (+ a (cell-v c))))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 1, "{ops}");

    // A fact about a module variable holds until code runs that could assign the variable: a
    // call or an assignment.
    // The variable is loaded once for a group of reads with no such code between them, and an immutable field
    // of its value is read once for the group.
    fn loads(ops: &str) -> usize {
        count(ops, "LoadSlot") + count(ops, "LoadSlotChecked")
    }
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f) (+ (point-x origin) (point-y origin)))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 1 && loads(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f) (* (point-x origin) (point-x origin)))");
    assert!(checked(&ops) + unchecked(&ops) == 1 && loads(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f h) (let ((a (point-x origin))) (h) (+ a (point-x origin))))");
    assert!(checked(&ops) == 2 && loads(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f) (if (point? origin) (point-x origin) 0))");
    assert!(tests(&ops) == 1 && checked(&ops) == 0 && unchecked(&ops) == 1 && loads(&ops) == 1, "{ops}");
    // The same holds across branches. A read in a branch reuses the value that was loaded before the branch.
    // A read after the branches does not reuse a value that only one branch loaded.
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f c) (let ((a (point-x origin))) (+ a (if c (point-y origin) (point-x origin)))))");
    assert!(checked(&ops) == 1 && unchecked(&ops) == 1 && loads(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f h) (if (point? origin) (begin (h) (point-x origin)) 0))");
    assert!(loads(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f c) (if c (point-x origin) 0) (point-y origin))");
    assert!(loads(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f c h) (let ((a (point-x origin))) (if c (h) 0) (+ a (point-y origin))))");
    assert!(loads(&ops) == 2, "{ops}");

    // Two loads of a captured variable yield the same struct. So an immutable field of the struct
    // is read once, and a load that is left without a use is removed.
    fn captured(ops: &str) -> usize {
        count(ops, "LoadUpvalue")
    }
    let ops = ops_of(&mut arena, &mut users, "(define (make p) (lambda () (* (point-x p) (point-x p)))) (define g (make (point 1 2)))");
    assert!(captured(&ops) == 1 && checked(&ops) + unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (make p h) (lambda () (let ((a (point-x p))) (h) (+ a (point-x p))))) (define g (make (point 1 2) list))");
    assert!(captured(&ops) == 2 && checked(&ops) + unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (make c) (lambda () (+ (cell-v c) (cell-v c)))) (define g (make (cell 1)))");
    assert!(captured(&ops) == 2 && checked(&ops) == 1 && unchecked(&ops) == 1, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f h) (let ((a (point-x origin))) (h) (+ a (point-y origin))))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f v) (let ((a (point-x origin))) (set! origin v) (+ a (point-y origin))))");
    assert!(checked(&ops) == 2 && unchecked(&ops) == 0, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define origin (point 1 2)) (define (f h) (if (point? origin) (h (lambda () (point-x origin))) 0))");
    assert!(unchecked(&ops) == 0, "{ops}");

    // When a `match` clause fails, the clauses after it use the reason. A value that was not a `point` skips the later `point`
    // clauses. A value that was a `point` skips the clauses for other types. No type test is made twice on
    // any path.
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (match v [(point 0 y) y] [(circle r) r] [(point x y) (+ x y)] [_ 'none]))");
    assert!(tests(&ops) == 2, "{ops}");
    let ops = ops_of(&mut arena, &mut users, "(define (f v) (match v [(point3 0 _ z) z] [(circle 0) 'dot] [(point3 x _ _) x] [(circle r) r] [(point x y) (+ x y)]))");
    assert!(tests(&ops) <= 4, "{ops}");
    // The same holds for any number of clauses. Thirty clauses over three types test for each type once.
    let long: String = (0..30).map(|i| [format!("[(point {i} y) (+ y {i})]"), format!("[(circle {i}) {i}]"), format!("[(cell {i}) {i}]")][i % 3].clone()).collect();
    let ops = ops_of(&mut arena, &mut users, &format!("(define (f v) (match v {long} [_ 'none]))"));
    assert!(tests(&ops) == 3, "{ops}");

    // The optimized code still computes the right results.
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
        (define (bump n) (let ((c (cell n))) (set-cell-v! c (+ (cell-v c) 1)) (if (cell? c) (cell-v c) 0)))
        (define (counter n) (let ((c (cell n))) (lambda () (set-cell-v! c (+ (cell-v c) 1)) (cell-v c))))
        (define count (counter 10))
        (define (which v) (cond [(point3? v) 1] [(point? v) 2] [(point3? v) 3] [else 4]))
        (define (twice-x p) (let ((a (point-x p))) (+ a (point-x p))))
        (define (square-x p) (* (point-x p) (point-x p)))
        (define (helped n) (let ((c (cell n)) (get (lambda (x) (cell-v x)))) (set-cell-v! c (+ (get c) 1)) (get c)))
        (define (origin-sum) (+ (* (point-x origin) (point-x origin)) (point-y origin)))
        (define (stale c g) (let ((a (cell-v c))) (g c) (+ a (cell-v c))))
        (define (pick v) (match v [(point 0 y) y] [(circle r) r] [(point x y) (+ x y)] [_ 'none]))
        (define (deep v) (match v [(point3 0 _ z) z] [(circle 0) 'dot] [(point3 x _ _) x] [(circle r) r] [(point x y) (+ x y)] [(cell (? pair?)) 'pair] [(cell v) v] [_ 'other]))
        (define (long v) (match v LONG [_ 'none]))
        (define (through p) (lambda (h) (let ((a (point-x p))) (h) (+ a (point-x p) (point-y p)))))
        (define (branched c h) (let ((a (point-x origin))) (if c (h) 0) (+ a (if c (point-y origin) (point-x origin)))))
        (define picked (list (map pick (list (point 0 7) (point 1 2) (circle 3) (point3 0 1 2) 5))
                             (map deep (list (point3 0 1 2) (point3 4 5 6) (circle 0) (circle 9) (point 1 2) (cell '(1)) (cell 8) 'x))))
        (define origin (point 1 2))
        (define (moved v) (let ((a (point-x origin))) (set! origin v) (list a (caught (lambda () (point-y origin))))))
        (define (swapped) (let ((a (point-x origin))) (set! origin (point 5 6)) (+ a (point-y origin))))
        (define more
          (list (map long (list (point 27 1) (point 0 1) (circle 28) (cell 29) (cell 2) (point 5 5) (point3 9 1 1) 'x))
                ((through (point 3 4)) list) (branched #f list) (branched #t (lambda () (set! origin (point 5 60)))) (begin (set! origin (point 1 2)) 'reset)
                (bump 4) (count) (count) (map which (list (point3 1 2 3) (point 1 2) (circle 1))) (twice-x (point 4 5))
                (stale (cell 1) (lambda (c) (set-cell-v! c 10))) (square-x (point 3 0)) (helped 6) (origin-sum) (swapped) (moved 'gone)
                (caught (lambda () (twice-x 5))) (caught (lambda () (square-x 'x)))))
        (list (sum 1 2) (twice next) (kept 1 (lambda (c) (set-cell-v! c 9))) (both (point3 1 2 3)) (after (point 1 2) #f)
              (kind (point 1 2)) (kind (point3 1 2 3)) (kind (circle 1)) (kind 5)
              (map area (list (point3 1 2 3) (point 1 2) (circle 4) 'x))
              (caught (lambda () (both 5))) (caught (lambda () (both (circle 1)))) (caught (lambda () (after (circle 1) #f)))
              more picked)";
    let expected = "(3 (#t 2 1) 9 3 2 (#f #f #t #f) (#t #f #t #f) circle other (3 3 4 none) wrong-type wrong-type wrong-type \
                    ((28 1 28 29 2 none 10 none) 10 2 61 reset 5 11 12 (1 2 4) 8 11 9 7 3 7 (5 wrong-type) wrong-type wrong-type) \
                    ((7 3 3 1 none) (2 4 dot 9 3 pair 8 other)))";
    assert_eq!(module_in(&mut arena, "runs", &[(Scheme, &run.replace("LONG", &long))]), Ok(Ok(expected.into())));
}

/// A `table` call whose keys are all constants is compiled to a call that takes its keys from a shape. A call with any other key stays as it is.
#[test]
fn a_table_call_with_constant_keys_takes_its_keys_from_a_shape() {
    let mut arena = arena();
    let shaped = "(provide a b c)
                  (define (a x y) (table 'id x 'name y))
                  (define (b x) (list (table 1 x \"two\" x #\\c x) (table 'id x 'name x)))
                  (define (c) (table 'on #t))";
    let ops = closure_ops(&mut arena, "shaped", shaped);
    assert_eq!((count(&ops, "MakeShapedTable"), count(&ops, "MakeTableOf")), (4, 0), "{ops}");
    let plain = "(provide a b c d)
                 (define (a k x) (table k x))
                 (define (b x) (table 'id x 'id x))
                 (define (c x) (table '(1 2) x))
                 (define (d) (table))";
    let ops = closure_ops(&mut arena, "plain", plain);
    assert_eq!((count(&ops, "MakeShapedTable"), count(&ops, "MakeTableOf")), (0, 4), "{ops}");
}

/// A shape is a constant of the code that uses it. An image keeps it, and the code makes working tables from it in another arena.
#[test]
fn an_image_keeps_the_shapes_of_table_calls() {
    let library = "(provide fresh kept)
                   (define (fresh n) (table 'id n \"a key that is too long to fit in a word\" 'long 2.5 'half))
                   (define kept (fresh 1))";
    let user = "(require library)
                (list (table->list kept) (table->list (fresh 2)) (begin (table-set! kept 'more 3) (table-delete! kept 2.5) (table-keys kept))
                      (table-ref (fresh 4) \"a key that is too long to fit in a word\") (table-ref (fresh 5) 'id) (equal? (fresh 6) (fresh 6)))";
    let expected = "(((id . 1) (\"a key that is too long to fit in a word\" . long) (2.5 . half)) ((id . 2) (\"a key that is too long to fit in a word\" . long) (2.5 . half)) \
                    (id \"a key that is too long to fit in a word\" more) long 5 #t)";
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "library", &[(Scheme, library)]).map(|ran| ran.is_ok()), Ok(true));
    arena.collect();
    let bytes = arena.mutate(|mc| image::save(mc, &[mc.root(0), mc.root(1), mc.root(2)])).unwrap();
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    for _ in 0..2 {
        let mut other = Arena::new(1 << 24, 3);
        other.mutate(|mc| {
            let roots = image::load(mc, &bytes, HOSTS.iter()).unwrap();
            roots.iter().enumerate().for_each(|(i, &root)| mc.set_root(i, root));
        });
        other.collect();
        assert_eq!(module_in(&mut other, "user", &[(Scheme, user)]), Ok(Ok(expected.into())));
    }
}

mod shaped {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use ragwort_types::Error;
    use ragwort_types::gc::Mutation;
    use ragwort_types::table::{ExternalTable, Key, Shape, Tables};

    use super::*;

    const FIELDS: [&str; 3] = ["id", "channel", "pinned"];
    /// The fields of a reaction, a second kind of event. It has `id` at another position than [`FIELDS`] has it.
    const REACTION: [&str; 3] = ["emoji", "user", "id"];
    /// The number of reads that asked an [`Event`] by key, and the number that asked it by position.
    pub static BY_KEY: AtomicUsize = AtomicUsize::new(0);
    pub static BY_POSITION: AtomicUsize = AtomicUsize::new(0);

    /// An event whose fields are in the order of its shape. Field `position` of event `number` is `10 * number + position`. The second field is the list of its field names.
    struct Event(i64, &'static [&'static str; 3]);

    impl ExternalTable for Event {
        fn len(&self) -> usize {
            FIELDS.len()
        }

        fn has(&self, key: Key<'_>) -> bool {
            matches!(key, Key::Symbol(name) if self.1.contains(&name))
        }

        fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
            BY_KEY.fetch_add(1, Ordering::Relaxed);
            let Key::Symbol(name) = key else { return Ok(None) };
            Ok(self.1.iter().position(|&field| field == name).and_then(|position| Value::fixnum(10 * self.0 + position as i64)))
        }

        fn keys(&self) -> impl Iterator<Item = Key<'_>> {
            self.1.iter().copied().map(Key::Symbol)
        }

        fn get_at<'gc>(&self, _: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>> {
            BY_POSITION.fetch_add(1, Ordering::Relaxed);
            let field = if position < FIELDS.len() {
                Value::fixnum(10 * self.0 + position as i64)
            } else {
                None
            };
            Some(Ok(field))
        }
    }

    /// Returns the field names of an event of kind `kind`: 0 for a message and anything else for a reaction.
    fn fields(kind: Option<i64>) -> Result<&'static [&'static str; 3], Fault> {
        match kind {
            Some(0) => Ok(&FIELDS),
            Some(_) => Ok(&REACTION),
            None => Err(Fault::WrongType),
        }
    }

    /// Makes the shape of the events of the kind that the caller passes. The module that binds the host functions calls it once for each kind and keeps the shapes in variables.
    fn event_shape<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        let mc = cx.mc();
        let symbols = Symbols::of_arena(mc)?;
        let mut keys = Vec::new();
        for name in fields(args.iter().next().and_then(|kind| kind.as_fixnum()))? {
            keys.push(symbols.intern_str(&Strings::new(mc), name)?.value(mc));
        }
        Ok(ragwort_vm::Reply::Value(Tables::new(mc).shape(&keys).map_err(|_| Fault::OutOfMemory)?.value(mc)))
    }

    /// Makes event `number` of kind `kind` with the shape that the caller passes.
    fn event<'s, 'gc>(cx: &mut ragwort_vm::HostContext<'s, 'gc>, args: ragwort_vm::HostArgs<'s, 'gc>) -> Result<ragwort_vm::Reply<'gc>, Fault> {
        let mut args = args.iter();
        let shape = args.next().and_then(Shape::of).ok_or(Fault::WrongType)?;
        let names = fields(args.next().and_then(|kind| kind.as_fixnum()))?;
        let number = args.next().and_then(|number| number.as_fixnum()).ok_or(Fault::WrongType)?;
        Ok(ragwort_vm::Reply::Value(Tables::new(cx.mc()).external_shaped(shape, Event(number, names), 0)?.value(cx.mc())))
    }

    pub static HOSTS: [HostDef; 2] = [ragwort_vm::host!("event-shape", 1, ragwort_vm::Purity::Impure, event_shape), ragwort_vm::host!("event", 3, ragwort_vm::Purity::Impure, event)];
}

/// A program reads a new external table of a shape for each event. An instruction with a constant key remembers the position of its key from the first event, and from then on asks the host by position.
#[test]
fn programs_read_the_events_of_a_shape_by_position() {
    use std::sync::atomic::Ordering;
    let mut arena = arena();
    let bindings = "(%define message-shape (%call-host event-shape 0)) (%define reaction-shape (%call-host event-shape 1))
                    (%define event (%lambda (number) (%call-host event message-shape 0 number)))
                    (%define reaction (%lambda (number) (%call-host event reaction-shape 1 number)))
                    (%provide event reaction)";
    assert_eq!(module_hosting(&mut arena, "shaped", &shaped::HOSTS, &[(Native, bindings)]), Ok(Ok("#<void>".into())));
    let reading = "(require \"shaped\")
                   (define (sum number) (let ((e (event number))) (+ (table-ref e 'id) (table-ref e 'pinned) (table-ref e 'pinned) (table-ref e 'missing 1000))))
                   (define (by-name number key) (table-ref (event number) key))
                   (list (map sum '(1 2 3 4)) (by-name 5 'channel) (table->list (event 6)) (table-length (event 7)) (equal? (event 8) (event 8)) (table? (event 9)))";
    let (key_before, position_before) = (shaped::BY_KEY.load(Ordering::Relaxed), shaped::BY_POSITION.load(Ordering::Relaxed));
    assert_eq!(module_in(&mut arena, "reading", &[(Scheme, reading)]), Ok(Ok("((1034 1064 1094 1124) 51 ((id . 60) (channel . 61) (pinned . 62)) 3 #t #t)".into())));
    let (by_key, by_position) = (shaped::BY_KEY.load(Ordering::Relaxed) - key_before, shaped::BY_POSITION.load(Ordering::Relaxed) - position_before);
    // The key `missing` is asked for by key, once for each of the four events. The two reads of `id` and `pinned` in the first event may ask by key before their positions are known. Every later read of them asks by position.
    assert!(by_position >= 6, "{by_position} reads by position, {by_key} by key");
    assert!((4..=4 + 2 + 1 + 3 + 6).contains(&by_key), "{by_position} reads by position, {by_key} by key");
    // One procedure reads the `id` of messages and of reactions in turn. The two kinds have `id` at different positions. The read remembers both shapes, so only the first event of each kind can be asked by key.
    let turns = "(require \"shaped\")
                 (define (id-of e) (table-ref e 'id))
                 (let loop ((n 0) (ids '()))
                   (if (eqv? n 10) (reverse ids) (loop (+ n 1) (cons (id-of (if (even? n) (event n) (reaction n))) ids))))";
    let (key_before, position_before) = (shaped::BY_KEY.load(Ordering::Relaxed), shaped::BY_POSITION.load(Ordering::Relaxed));
    assert_eq!(module_in(&mut arena, "turns", &[(Scheme, turns)]), Ok(Ok("(0 12 20 32 40 52 60 72 80 92)".into())));
    let (by_key, by_position) = (shaped::BY_KEY.load(Ordering::Relaxed) - key_before, shaped::BY_POSITION.load(Ordering::Relaxed) - position_before);
    assert!(by_key <= 2 && by_position >= 8, "{by_position} reads by position, {by_key} by key");
}

