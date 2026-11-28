use std::path::{Path, PathBuf};

use super::*;

/// Creates a new, empty folder for the test `name`.
fn scratch(name: &str) -> PathBuf {
    let folder = std::env::temp_dir().join(format!("ragwort-cli-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&folder);
    std::fs::create_dir_all(&folder).unwrap();
    folder
}

/// Writes the file `name` in `folder`. A module that is not a REPL input starts with no procedure. So a Scheme file gets a last line that
/// requires all of Scheme, which leaves the lines and columns of `text` as they are.
fn file(folder: &Path, name: &str, text: &str) -> PathBuf {
    let path = folder.join(name);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    let text = if name.ends_with(".rg") {
        format!("{text}\n(require scheme)")
    } else {
        text.to_string()
    };
    std::fs::write(&path, text).unwrap();
    path
}

fn dir(name: &str, folder: &Path) -> ModuleDir {
    ModuleDir { name: name.into(), folder: folder.into() }
}

/// Evaluates the REPL input `text` and returns the values that the REPL writes for it.
fn eval(program: &mut Program, text: &str) -> Result<Vec<String>, Vec<String>> {
    let mut written = Vec::new();
    program.eval(text, &mut |value| written.push(value.to_string()))?;
    Ok(written)
}

fn values(written: &[&str]) -> Result<Vec<String>, Vec<String>> {
    Ok(written.iter().map(|value| value.to_string()).collect())
}

/// Creates a library of two modules under `root`. `lib/foo` requires `lib/text`. The folder of `lib/text` has a file in each
/// language and a file that is not source code.
fn library(root: &Path) -> Vec<ModuleDir> {
    file(root, "text/a.rg", "(provide shout (struct-out user #:omit-constructor) make-user)\n(struct user (name age))\n(define (make-user name age) (user name age))\n(define (shout s) (string-append s \"!\"))");
    file(root, "text/b.rgn", "(%provide twice)\n(%define twice (%lambda (x) (%intrinsic + x x)))");
    file(root, "text/notes.txt", "(not code");
    file(root, "foo/foo.rg", "(require lib/text)\n(provide greet)\n(define (greet u) (match u [(user name _ ...) (shout name)]))");
    vec![dir("lib/foo", &root.join("foo")), dir("lib/text", &root.join("text"))]
}

#[test]
fn the_repl_keeps_what_each_input_defines() {
    let mut program = Program::new(HEAP, Vec::new()).unwrap();
    assert_eq!(eval(&mut program, "(define x 4) (* x x)"), values(&["16"]));
    assert_eq!(eval(&mut program, "(define (f a)\n  (+ a x))\n(f 1) \"s\" (if #f #f) 'done"), values(&["5", "\"s\"", "done"]));
    assert_eq!(eval(&mut program, "(define x 10) (list x (f 1))"), values(&["(10 5)"]));
    assert_eq!(eval(&mut program, "(struct point (x y))"), values(&[]));
    assert_eq!(eval(&mut program, "(match (point 1 2) [(point a _ ...) a])"), values(&["1"]));
    assert_eq!(eval(&mut program, "(list display write newline)").map(|written| written.len()), Ok(1));
    // An input that fails does not change the inputs before it.
    assert_eq!(eval(&mut program, "(car 5)"), Err(vec!["error: car: wrong type of argument: 5\n  at <input>:1".to_string()]));
    assert_eq!(eval(&mut program, "1 (car 5) 2"), Err(vec!["error: car: wrong type of argument: 5\n  at <input>:1".to_string()]));
    assert_eq!(eval(&mut program, "\n (nope)"), Err(vec!["<input>:2:3: undefined identifier".to_string()]));
    // An input that fails keeps the definitions that ran before the error, and none of the definitions after it. Neither a reference nor a call reaches a procedure whose definition never ran.
    assert_eq!(eval(&mut program, "(define (kept) 10) (car 7) (define (lost) 20)").map_err(|e| e.len()), Err(1));
    assert_eq!(eval(&mut program, "(kept)"), values(&["10"]));
    assert_eq!(eval(&mut program, "lost"), Err(vec!["<input>:1:1: undefined identifier".to_string()]));
    assert_eq!(eval(&mut program, "(lost)"), Err(vec!["<input>:1:2: undefined identifier".to_string()]));
    assert_eq!(eval(&mut program, "(define (lost) 21) (lost)"), values(&["21"]));
    assert_eq!(eval(&mut program, "(set! x 2)"), Err(vec!["<input>:1:7: cannot assign to imported binding".to_string()]));
    assert_eq!(eval(&mut program, "(f x)"), values(&["14"]));
}

#[test]
fn an_input_is_whole_once_what_it_opens_is_closed() {
    let mut program = Program::new(HEAP, Vec::new()).unwrap();
    for (text, unfinished) in [("(define (f a)\n", true), ("(f \"a", true), ("#| note", true), ("(f 1) (g", true), ("(f 1)\n", false), ("x", false), ("", false), ("(f 1))", false)] {
        assert_eq!(program.unfinished(text), unfinished, "{text}");
    }
}

#[test]
fn code_requires_the_modules_the_command_line_names() {
    let root = scratch("requires");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(eval(&mut program, "(require lib/foo lib/text) (list (greet (make-user \"ann\" 3)) (twice 21))"), values(&["(\"ann!\" 42)"]));
    assert_eq!(eval(&mut program, "(require lib/text) (user \"ann\" 3)"), Err(vec!["<input>:1:21: struct constructor not provided by module".to_string()]));
    // A module that an input requires by name stays visible to the inputs after it. A later definition
    // shadows the module's binding of the same name.
    assert_eq!(eval(&mut program, "(twice 4)"), values(&["8"]));
    assert_eq!(eval(&mut program, "(define (twice x) 'mine) (twice 4)"), values(&["mine"]));
    assert_eq!(eval(&mut program, "(list (twice 4) (shout \"a\"))"), values(&["(mine \"a!\")"]));
    let mut filtered = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(eval(&mut filtered, "(require (only-in lib/text twice)) (twice 4)"), values(&["8"]));
    assert_eq!(eval(&mut filtered, "(twice 4)"), Err(vec!["<input>:1:2: undefined identifier".to_string()]));
    let main = file(&root, "main.rg", "(require lib/foo lib/text)\n(define made (make-user \"bo\" 1))\n(greet made)\n(twice 2)");
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&main, true), Ok(()));
    let failing = file(&root, "failing.rg", "(require lib/text)\n(twice 'two)");
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&failing, true), Err(vec![format!("error: +: wrong type of argument: two two\n  at {}:2", failing.display())]));
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&failing, false), Ok(()));
    // A required module runs in steps, as an entry point does. The garbage that it creates while it runs is
    // collected along the way, however much there is.
    let churn = "(define (churn i last) (if (= i 0) (vector-length last) (churn (- i 1) (make-vector 200000 i))))";
    file(&root, "heavy/heavy.rg", &format!("(provide made)\n{churn}\n(define made (churn 400 #f))"));
    let mut heavy = Program::new(HEAP, vec![dir("heavy", &root.join("heavy"))]).unwrap();
    assert_eq!(eval(&mut heavy, "(require heavy) made"), values(&["200000"]));
    assert_eq!(eval(&mut heavy, &format!("{churn} (churn 400 #f)")), values(&["200000"]));
    // A long run is stepped, so its garbage is collected along the way.
    let long = file(&root, "long.rg", "(define (count i acc) (if (= i 0) (length acc) (count (- i 1) (cons i '()))))\n(count 3000000 '())");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&long, true), Ok(()));
}

#[test]
fn what_is_wrong_says_where() {
    fn run(dirs: Vec<ModuleDir>, path: &Path) -> Vec<String> {
        Program::new(HEAP, dirs).unwrap().run_file(path, true).unwrap_err()
    }
    fn at(path: &Path, rest: &str) -> String {
        format!("{}:{rest}", path.display())
    }
    let root = scratch("wrong");
    let unbound = file(&root, "unbound.rg", "(define (f) 1)\n\n(f 1 2\n   (g))\n");
    assert_eq!(run(Vec::new(), &unbound), [at(&unbound, "4:5: undefined identifier")]);
    let unclosed = file(&root, "unclosed.rgn", "(%define x 1)\n(%define y");
    assert_eq!(run(Vec::new(), &unclosed), [at(&unclosed, "2:1: unclosed list, string, or comment")]);
    let native = file(&root, "native.rgn", "(%define x 1)\n  (x)");
    assert_eq!(run(Vec::new(), &native), [at(&native, "2:3: list does not start with a form name")]);
    let missing = file(&root, "missing.rg", "(require nope)");
    assert_eq!(run(Vec::new(), &missing), [at(&missing, "1:10: module not found")]);
    assert!(run(Vec::new(), &root.join("absent.rg"))[0].starts_with(&at(&root.join("absent.rg"), " ")));

    // An error in a required module is reported first, followed by the location of the `require`.
    let broken = file(&root, "broken/one.rg", "(provide f)\n(define (f) 1)");
    let second = file(&root, "broken/two.rg", "(define (g)\n  (h))");
    let user = file(&root, "user.rg", "(require broken)\n(f)");
    assert_eq!(run(vec![dir("broken", broken.parent().unwrap())], &user), [at(&second, "2:4: undefined identifier"), at(&user, "1:10: module not found")]);
    let raising = file(&root, "raising/one.rg", "(car 1)");
    let raises = file(&root, "raises.rg", "(require raising)");
    assert_eq!(run(vec![dir("raising", raising.parent().unwrap())], &raises), [format!("module raising: error: car: wrong type of argument: 1\n  at {}:1", raising.display()), at(&raises, "1:10: module not found")]);
    let empty = scratch("wrong-empty");
    let needs = file(&root, "needs.rg", "(require empty)");
    assert_eq!(run(vec![dir("empty", &empty)], &needs), [format!("{}: no .rg or .rgn files", empty.display()), at(&needs, "1:10: module not found")]);

    // Modules that require each other can't be loaded.
    let a = file(&root, "a/a.rg", "(require b)");
    let b = file(&root, "b/b.rg", "(require a)");
    let dirs = vec![dir("a", a.parent().unwrap()), dir("b", b.parent().unwrap())];
    let cycle = file(&root, "cycle.rg", "(require a)");
    assert_eq!(run(dirs, &cycle), ["module a: circular dependency via a, b".to_string(), at(&b, "1:10: module not found"), at(&a, "1:10: module not found"), at(&cycle, "1:10: module not found")]);
}

#[test]
fn compiling_lists_the_bytecode_of_each_module() {
    let root = scratch("compiles");
    let main = file(&root, "main.rg", "(require lib/foo)\n(define (inc n) (+ n 1))\n(car 1)");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    program.list();
    assert_eq!(program.load_all(), Ok(()));
    assert_eq!(program.run_file(&main, false), Ok(()));
    let listing = program.take_listing();
    let modules: Vec<&str> = listing.lines().filter(|line| line.starts_with("module ")).collect();
    assert_eq!(modules, ["module lib/text", "module lib/foo", "module main"]);
    let main = &listing[listing.find("module main").unwrap()..];
    assert!(main.contains("  form 0\n    fn0: arity 0, 0 captured\n      0   LoadConst { dst: 2, value: closure(fn1) }"), "{main}");
    assert!(main.contains("    fn1: arity 1, 0 captured\n"), "{main}");
    assert!(main.contains("intrinsic: Car"), "{main}");
    assert_eq!(program.take_listing(), "");

    let wrong = file(&root, "wrong.rg", "(define (f) (g))");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    program.list();
    assert_eq!(program.run_file(&wrong, false), Err(vec![format!("{}:1:14: undefined identifier", wrong.display())]));
    assert_eq!(program.take_listing(), "");
}

#[test]
fn an_image_starts_a_program_from_the_modules_it_holds() {
    let root = scratch("images");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(program.load_all(), Ok(()));
    let bytes = program.save_image().unwrap();
    // Nothing is read from the folders again. The modules come from the image.
    std::fs::remove_dir_all(root.join("text")).unwrap();
    std::fs::remove_dir_all(root.join("foo")).unwrap();
    let mut loaded = Program::from_image(HEAP, Vec::new(), &bytes).unwrap();
    assert_eq!(eval(&mut loaded, "(require lib/foo lib/text) (list (greet (make-user \"ann\" 3)) (twice 21))"), values(&["(\"ann!\" 42)"]));
    assert_eq!(eval(&mut loaded, "(list display (twice 1))").map(|written| written.len()), Ok(1));
    let main = file(&root, "main.rg", "(require lib/foo lib/text)\n(greet (make-user \"bo\" 1))\n(twice 'two)");
    assert_eq!(Program::from_image(HEAP, Vec::new(), &bytes).unwrap().run_file(&main, true), Err(vec![format!("error: +: wrong type of argument: two two\n  at {}:3", main.display())]));

    // Modules from folders are loaded on top of the image, and the combination can be saved as another image.
    file(&root, "extra/e.rg", "(require lib/text)\n(provide thrice)\n(define (thrice x) (+ x (twice x)))");
    let mut more = Program::from_image(HEAP, vec![dir("extra", &root.join("extra"))], &bytes).unwrap();
    assert_eq!(more.load_all(), Ok(()));
    let both = more.save_image().unwrap();
    let mut last = Program::from_image(HEAP, Vec::new(), &both).unwrap();
    assert_eq!(eval(&mut last, "(require extra) (thrice 5)"), values(&["15"]));

    let clash = Program::from_image(HEAP, vec![dir("lib/text", &root)], &bytes).err();
    assert_eq!(clash, Some(vec!["module `lib/text` is already present in the image".to_string()]));
    assert_eq!(Program::from_image(HEAP, Vec::new(), b"not an image").err(), Some(vec!["invalid or corrupted ragwort image".to_string()]));
    let mut other = bytes.clone();
    other[8] ^= 1;
    assert_eq!(Program::from_image(HEAP, Vec::new(), &other).err(), Some(vec!["image was created by a different build of ragwort".to_string()]));
}

#[test]
fn a_program_stops_at_its_memory_limit() {
    let big = "(define kept (make-vector 1000000 0)) (vector-length kept)";
    let mut small = Program::new(4 << 20, Vec::new()).unwrap();
    assert_eq!(eval(&mut small, big), Err(vec!["error: out of memory".to_string()]));
    assert_eq!(eval(&mut small, "(+ 1 2)"), values(&["3"]));
    let mut roomy = Program::new(HEAP, Vec::new()).unwrap();
    assert_eq!(eval(&mut roomy, big), values(&["1000000"]));
}

#[test]
fn an_uncaught_error_lists_the_calls_in_progress() {
    let root = scratch("trace");
    let main = file(&root, "main.rg", "(define (inner x) (vector-ref x 9))\n(define (middle x) (+ 1 (inner x)))\n(define (main) (+ 1 (middle (vector 1))))\n(main)");
    let at = main.display();
    let report = format!("error: vector-ref: value out of range: #(1) 9\n  in inner ({at}:1)\n  in middle ({at}:2)\n  in main ({at}:3)");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&main, true), Err(vec![report]));
    let anonymous = file(&root, "anonymous.rg", "(define (apply-it f) (+ 1 (f 5)))\n(apply-it (lambda (x) (+ 1 (car x))))");
    let at = anonymous.display();
    let report = format!("error: car: wrong type of argument: 5\n  in (anonymous) ({at}:2)\n  in apply-it ({at}:1)");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&anonymous, true), Err(vec![report]));
}

#[test]
fn a_procedure_inlined_from_another_module_keeps_its_entry() {
    fn dirs(root: &Path) -> Vec<ModuleDir> {
        vec![dir("util", &root.join("util"))]
    }
    let root = scratch("inlined");
    let util = file(&root, "util/u.rg", "(provide second)\n(define (second xs)\n  (car\n    (cdr xs)))");
    let main = file(&root, "main.rg", "(require util)\n(define (use x)\n  (+ 1 (second x)))\n(+ 1 (use 5))");
    // The entry has the line of the operation that failed, not the line where the procedure's definition starts.
    let report = format!("error: cdr: wrong type of argument: 5\n  in second [inlined] ({}:4)\n  in use ({at}:3)\n  at {at}:4", util.display(), at = main.display());
    assert_eq!(Program::new(HEAP, dirs(&root)).unwrap().run_file(&main, true), Err(vec![report.clone()]));
    // The entry survives an image, which saves the inline template with the lines of its operations.
    let mut library = Program::new(HEAP, dirs(&root)).unwrap();
    assert_eq!(library.load_all(), Ok(()));
    let bytes = library.save_image().unwrap();
    assert_eq!(Program::from_image(HEAP, Vec::new(), &bytes).unwrap().run_file(&main, true), Err(vec![report]));
}

#[test]
fn native_code_and_keyword_calls_report_their_lines() {
    let root = scratch("positions");
    let native = file(&root, "main.rgn", "(%define inner (%lambda (x)\n  (%intrinsic car x)))\n(%define outer (%lambda (x)\n  (%intrinsic + 1 (%app inner x))))\n(%intrinsic + 1 (%app outer 5))");
    let at = native.display();
    let report = format!("error: car: wrong type of argument: 5\n  in inner ({at}:2)\n  in outer ({at}:4)\n  at {at}:5");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&native, true), Err(vec![report]));
    let keyword = file(&root, "keyword.rg", "(define (pick xs #:from [from 0])\n  (vector-ref xs from))\n(define (use xs)\n  (+ 1\n     (pick xs #:from 9)))\n(+ 1 (use (vector 1)))");
    let at = keyword.display();
    let report = format!("error: vector-ref: value out of range: #(1) 9\n  in pick ({at}:2)\n  in use ({at}:5)\n  at {at}:6");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&keyword, true), Err(vec![report]));
}

#[test]
fn a_module_starts_with_no_procedure() {
    let root = scratch("bare");
    // A file that is not a REPL input requires what it uses. The forms of the language need no library.
    let forms = root.join("forms.rg");
    std::fs::write(&forms, "(define (pick x) (match x [(list a b) a] [_ 'other]))\n(guard (e (#t 'caught)) (pick '(1 2)))").unwrap();
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&forms, true), Ok(()));
    // The report of a procedure that the module does not have names the library to require.
    let bare = root.join("bare.rg");
    std::fs::write(&bare, "(define (inc n)\n  (+ n 1))").unwrap();
    let report = format!("{}:2:4: undefined identifier: `+` is in `scheme/number`, which is not required", bare.display());
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&bare, true), Err(vec![report]));
    std::fs::write(&bare, "(require scheme/number)\n(define (inc n)\n  (+ n 1))\n(inc (car '(1)))").unwrap();
    let report = format!("{}:4:7: undefined identifier: `car` is in `scheme/list`, which is not required", bare.display());
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&bare, true), Err(vec![report]));
    std::fs::write(&bare, "(require scheme/number scheme/list)\n(define (inc n)\n  (+ n 1))\n(inc (car '(1)))").unwrap();
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&bare, true), Ok(()));
    // The report does not name a library that the module requires, also when a filter leaves the name out.
    for required in ["(require (prefix-in l: scheme/list))", "(require (only-in scheme/list cdr))", "(require [scheme/number (except-in scheme/list car)])", "(require (except-in scheme car))"] {
        std::fs::write(&bare, format!("{required}\n(car '(1))")).unwrap();
        let report = format!("{}:2:2: undefined identifier", bare.display());
        assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&bare, true), Err(vec![report]), "{required}");
    }
    // A REPL input has all of Scheme, and can still require one library by name.
    let mut program = Program::new(HEAP, Vec::new()).unwrap();
    assert_eq!(eval(&mut program, "(map (lambda (n) (* n n)) '(1 2 3))"), values(&["(1 4 9)"]));
    assert_eq!(eval(&mut program, "(require (prefix-in n: scheme/number)) (n:+ 1 2)"), values(&["3"]));
    // A folder cannot be the module of a name that a library of Scheme has.
    let clash = Program::new(HEAP, vec![dir("scheme/list", &root)]).err();
    assert_eq!(clash, Some(vec!["module `scheme/list` is already a library of Scheme".to_string()]));
}

#[test]
fn a_group_that_an_input_requires_stays_visible() {
    let root = scratch("groups");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    // The modules of a group are required by name alone, so the inputs after it see them, as with `(require lib/foo lib/text)`.
    assert_eq!(eval(&mut program, "(require [lib/foo [lib/text]]) (twice 21)"), values(&["42"]));
    assert_eq!(eval(&mut program, "(list (twice 4) (greet (make-user \"ann\" 3)))"), values(&["(8 \"ann!\")"]));
    // A module inside a filter is required for that input only, in a group too.
    let mut filtered = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(eval(&mut filtered, "(require [lib/foo (only-in lib/text twice)]) (twice 4)"), values(&["8"]));
    assert_eq!(eval(&mut filtered, "(twice 4)"), Err(vec!["<input>:1:2: undefined identifier".to_string()]));
    assert_eq!(eval(&mut filtered, "(require (only-in lib/text make-user)) (greet (make-user \"bo\" 1))"), values(&["\"bo!\""]));
}
