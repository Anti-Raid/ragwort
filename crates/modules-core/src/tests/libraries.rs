use ragwort_types::gc::Mutation;
use ragwort_vm::{HostArgs, HostContext, MIN_SEGMENT, Purity, Reply, host};

use super::*;
use crate::{Error, load};

fn twice<'s, 'gc>(_: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let number = args.get(0).and_then(Value::as_fixnum).ok_or(Fault::WrongType)?;
    Ok(Reply::Value(Value::fixnum(number * 2).ok_or(Fault::OutOfRange)?))
}

static HOSTS: [HostDef; 1] = [host!("twice", 1, Purity::Pure, twice)];

/// A library with state: each arena counts the counters that it made.
static COUNTER: Library = Library {
    name: "lib/counter",
    base: Some(&PRELUDE),
    files: &[LibraryFile::scheme(
        "counter.rg",
        "(provide make-counter counters-made)
         (define made (make-table))
         (table-set! made 'count 0)
         (define (make-counter start)
           (table-set! made 'count (+ 1 (table-ref made 'count 0)))
           (let ((n start)) (lambda () (set! n (+ n 1)) n)))
         (define (counters-made) (table-ref made 'count 0))",
    )],
    hosts: &[],
    requires: &[],
    internals: false,
};

/// A library in two languages that requires another library and calls a host function.
static TEXT: Library = Library {
    name: "lib/text",
    base: Some(&PRELUDE),
    files: &[
        LibraryFile::native("text.rgn", "(%define twice (%lambda (n) (%call-host twice n)))"),
        LibraryFile::scheme(
            "text.rg",
            "(require lib/counter)
             (provide shout doubled-counter label)
             (define label (string-append \"made by lib/text, \" \"in a string that is an object\"))
             (define (shout text) (string-append text \"!\"))
             (define (doubled-counter start) (let ((next (make-counter start))) (lambda () (twice (next)))))",
        ),
    ],
    hosts: &HOSTS,
    requires: &[&COUNTER],
    internals: false,
};

/// A library with a large value, which an arena should hold only if it requires the library.
static LARGE: Library = Library {
    name: "lib/large",
    base: Some(&PRELUDE),
    files: &[LibraryFile::scheme("large.rg", "(provide large) (define large (make-vector 5000 0))")],
    hosts: &[],
    requires: &[],
    internals: false,
};

/// Starts an arena from `libraries`. Root 0 holds the shelf.
fn started(libraries: &Libraries) -> Arena {
    let mut arena = Arena::new(1 << 24, 1);
    arena.mutate(|mc| mc.set_root(0, libraries.start(mc).unwrap().value(mc)));
    arena
}

fn finish<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) -> Value<'gc> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return value,
            _ => panic!("the program did not finish"),
        }
    }
}

/// Compiles `text` as a module in the arena and runs it. The code can require the libraries in `allowed`, or all of them for `None`.
/// Returns the written form of the last form's value.
fn program(arena: &mut Arena, libraries: &Libraries, allowed: Option<&[&str]>, text: &str) -> Result<String, Error> {
    arena.mutate(|mc| {
        let shelf = Shelf::of(mc, mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let files = [File { language: Language::Scheme, session: &session }];
        // Scheme code is compiled against the prelude, which the arena loads here if it does not hold it yet.
        let prelude = libraries.require(mc, shelf, PRELUDE.name).unwrap().unwrap();
        let mut resolver = libraries.resolver(shelf, allowed);
        let source = Source { name: "main", hosts: &[], files: &files, implicit: &[], internals: false };
        let loaded = load(mc, shelf.symbols(mc), prelude, &source, &mut resolver)?;
        assert!(resolver.failed().is_none());
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            last = finish(mc, thunk);
        }
        Ok(ragwort_printer_scheme::to_string(mc, last, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap())
    })
}

fn loaded(arena: &mut Arena) -> usize {
    arena.mutate(|mc| Shelf::of(mc, mc.root(0)).unwrap().loaded(mc))
}

/// An arena gets a library when its code first requires it, together with the libraries that the library needs. Each arena has its own
/// state of a library. An arena does not hold a library that it never requires.
#[test]
fn an_arena_loads_a_library_when_its_code_requires_it() {
    let libraries = Libraries::build(&[&TEXT, &LARGE], 64 << 20).unwrap();
    // A library is built after its base and the libraries that it requires, which join the set by themselves.
    assert_eq!(libraries.names().collect::<Vec<_>>(), [PRELUDE.name, "lib/counter", "lib/text", "lib/large"]);

    let mut first = started(&libraries);
    // A new arena holds no library, not even the prelude.
    assert_eq!(loaded(&mut first), 0);
    assert_eq!(program(&mut first, &libraries, None, "(+ 1 2)").unwrap(), "3");
    assert_eq!(loaded(&mut first), 1);
    first.collect();
    let bare = first.objects();
    // The program requires one library. The arena loads it, and the library that it requires.
    let text = "(require lib/text) (define next (doubled-counter 10)) (list (next) (next) (shout label))";
    assert_eq!(program(&mut first, &libraries, None, text).unwrap(), "(22 24 \"made by lib/text, in a string that is an object!\")");
    assert_eq!(loaded(&mut first), 3);
    // The library's code keeps working after a collection that moves its objects, and a second requirement finds the loaded library.
    first.set_evacuate_all(true);
    first.collect();
    let again = "(require lib/text) (require lib/counter) (list (shout \"again\") (counters-made))";
    assert_eq!(program(&mut first, &libraries, None, again).unwrap(), "(\"again!\" 1)");
    assert_eq!(loaded(&mut first), 3);

    // A second arena has its own state of the library, and loads only what it requires.
    let mut second = started(&libraries);
    let counting = "(require lib/counter) (define a (make-counter 0)) (define b (make-counter 5)) (list (a) (b) (counters-made))";
    assert_eq!(program(&mut second, &libraries, None, counting).unwrap(), "(1 6 2)");
    assert_eq!(loaded(&mut second), 2);
    assert_eq!(program(&mut first, &libraries, None, "(require lib/counter) (counters-made)").unwrap(), "1");

    // Neither arena holds the large library. A third arena that requires it holds its vector of 5000 slots.
    first.collect();
    second.collect();
    let mut third = started(&libraries);
    assert_eq!(program(&mut third, &libraries, None, "(require lib/large) (vector-length large)").unwrap(), "5000");
    third.collect();
    assert!(first.occupied_bytes() + 40_000 <= third.occupied_bytes(), "{} and {} bytes", first.occupied_bytes(), third.occupied_bytes());
    assert!(first.objects() > bare && second.objects() < first.objects());
}

/// The embedder chooses the libraries that an arena's code can require.
#[test]
fn code_requires_only_the_libraries_that_it_is_allowed() {
    let libraries = Libraries::build(&[&TEXT, &LARGE], 64 << 20).unwrap();
    let mut arena = started(&libraries);
    assert!(program(&mut arena, &libraries, Some(&["lib/counter"]), "(require lib/text) (shout \"no\")").is_err());
    // Only the prelude was loaded, for the compile.
    assert_eq!(loaded(&mut arena), 1);
    assert_eq!(program(&mut arena, &libraries, Some(&["lib/counter"]), "(require lib/counter) (counters-made)").unwrap(), "0");
    // A name that no library has is not found either.
    assert!(program(&mut arena, &libraries, None, "(require lib/missing) 1").is_err());
    // A set that was built without a library does not have it.
    let small = Libraries::build(&[&COUNTER], 64 << 20).unwrap();
    let mut other = started(&small);
    assert!(program(&mut other, &small, None, "(require lib/large) 1").is_err());
    assert_eq!(program(&mut other, &small, None, "(require lib/counter) (counters-made)").unwrap(), "0");
}

static FIRST_OF_TWO: Library = Library { name: "lib/first", base: Some(&PRELUDE), files: &[], hosts: &[], requires: &[&SECOND_OF_TWO], internals: false };
static SECOND_OF_TWO: Library = Library { name: "lib/second", base: Some(&PRELUDE), files: &[], hosts: &[], requires: &[&FIRST_OF_TWO], internals: false };
static FAILING: Library = Library { name: "lib/failing", base: Some(&PRELUDE), files: &[LibraryFile::scheme("failing.rg", "(car 5)")], hosts: &[], requires: &[], internals: false };
static UNBOUND: Library = Library { name: "lib/unbound", base: Some(&PRELUDE), files: &[LibraryFile::scheme("unbound.rg", "(define x 1)\n(no-such-procedure x)")], hosts: &[], requires: &[], internals: false };
static OTHER_COUNTER: Library = Library { name: "lib/counter", base: Some(&PRELUDE), files: &[LibraryFile::scheme("other.rg", "(provide one) (define one 1)")], hosts: &[], requires: &[], internals: false };
/// A library without a base must be native code.
static BASELESS: Library = Library { name: "lib/baseless", base: None, files: &[LibraryFile::scheme("baseless.rg", "(define x 1)")], hosts: &[], requires: &[], internals: false };

#[test]
fn a_set_that_cannot_be_built_says_which_library_is_wrong() {
    assert!(matches!(Libraries::build(&[&FIRST_OF_TWO], 64 << 20), Err(BuildError::Cycle(_))));
    assert!(matches!(Libraries::build(&[&COUNTER, &FAILING], 64 << 20), Err(BuildError::Raised { library: "lib/failing", fault: Some(Fault::WrongType) })));
    assert!(matches!(Libraries::build(&[&UNBOUND], 64 << 20), Err(BuildError::Load { library: "lib/unbound", error: Located { file: Some(0), .. } })));
    assert!(matches!(Libraries::build(&[&COUNTER, &OTHER_COUNTER], 64 << 20), Err(BuildError::SameName("lib/counter"))));
    assert!(matches!(Libraries::build(&[&BASELESS], 64 << 20), Err(BuildError::Base("lib/baseless"))));
    // The same library twice is one library. The prelude joins as the base.
    assert_eq!(Libraries::build(&[&COUNTER, &TEXT, &COUNTER], 64 << 20).unwrap().names().count(), 3);
}

/// The base library of another language: a few procedures in native code, with nothing beneath it.
static OTHER_BASE: Library = Library {
    name: "other/base",
    base: None,
    files: &[LibraryFile::native("base.rgn", "(%provide add twice) (%define add (%lambda (a b) (%intrinsic + a b))) (%define twice (%lambda (n) (%call-host twice n)))")],
    hosts: &HOSTS,
    requires: &[],
    internals: false,
};

/// A library of that language. This test has no front end for another language, so the library is native code that requires its base.
static OTHER_LIBRARY: Library = Library {
    name: "other/math",
    base: None,
    files: &[LibraryFile::native("math.rgn", "(%require other/base) (%provide add-twice) (%define add-twice (%lambda (a b) (%app twice (%app add a b))))")],
    hosts: &[],
    requires: &[&OTHER_BASE],
    internals: false,
};

/// A set holds the libraries of several languages, each on its own base. An arena that runs code of one language does not hold the
/// base of another.
#[test]
fn each_language_has_its_own_base_library() {
    let libraries = Libraries::build(&[&OTHER_LIBRARY, &TEXT], 64 << 20).unwrap();
    assert_eq!(libraries.names().collect::<Vec<_>>(), ["other/base", "other/math", PRELUDE.name, "lib/counter", "lib/text"]);
    let mut arena = started(&libraries);
    arena.collect();
    let bare = arena.occupied_bytes();
    // The arena loads the other language's library and its base, and calls the library.
    let result = arena.mutate(|mc| {
        let shelf = Shelf::of(mc, mc.root(0)).unwrap();
        libraries.require(mc, shelf, "other/math").unwrap().unwrap();
        assert!(libraries.require(mc, shelf, "other/none").unwrap().is_none());
        // Native code calls the library. It requires it through the same resolver.
        let session = SyntaxSession::new(mc, "(%require other/math) (%app add-twice 3 4)").unwrap();
        let mut resolver = libraries.resolver(shelf, None);
        let loaded = ragwort_native::load(mc, shelf.symbols(mc), "main", &[], &[&session], &mut resolver).unwrap();
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            last = finish(mc, thunk);
        }
        last.as_fixnum()
    });
    assert_eq!(result, Some(14));
    assert_eq!(loaded(&mut arena), 2);
    arena.collect();
    // The prelude is a hundred kilobytes of objects. This arena holds a page or two more than an empty one.
    assert!(arena.occupied_bytes() <= bare + 2 * 16384, "{} bytes, {bare} when empty", arena.occupied_bytes());
    // The same arena can run Scheme code later, and loads the prelude then.
    assert_eq!(program(&mut arena, &libraries, None, "(require lib/text) (shout \"both\")").unwrap(), "\"both!\"");
    assert_eq!(loaded(&mut arena), 5);
}
