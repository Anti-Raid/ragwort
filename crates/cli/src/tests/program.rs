use std::path::{Path, PathBuf};

use super::*;

/// A new, empty folder for the test `name`.
fn scratch(name: &str) -> PathBuf {
    let folder = std::env::temp_dir().join(format!("ragwort-cli-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&folder);
    std::fs::create_dir_all(&folder).unwrap();
    folder
}

fn file(folder: &Path, name: &str, text: &str) -> PathBuf {
    let path = folder.join(name);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, text).unwrap();
    path
}

fn dir(name: &str, folder: &Path) -> ModuleDir {
    ModuleDir { name: name.into(), folder: folder.into() }
}

/// What the REPL writes for the input `text`.
fn eval(program: &mut Program, text: &str) -> Result<Vec<String>, Vec<String>> {
    let mut written = Vec::new();
    program.eval(text, &mut |value| written.push(value.to_string()))?;
    Ok(written)
}

fn values(written: &[&str]) -> Result<Vec<String>, Vec<String>> {
    Ok(written.iter().map(|value| value.to_string()).collect())
}

/// A library of two modules, the second requiring the first, whose folder has files in both
/// languages and one that's neither.
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
    // What's wrong with an input leaves the ones before it as they were.
    assert_eq!(eval(&mut program, "(car 5)"), Err(vec!["uncaught: #<error WrongType>".to_string()]));
    assert_eq!(eval(&mut program, "1 (car 5) 2"), Err(vec!["uncaught: #<error WrongType>".to_string()]));
    assert_eq!(eval(&mut program, "\n (nope)"), Err(vec!["<input>:2:3: a name nothing defines".to_string()]));
    assert_eq!(eval(&mut program, "(set! x 2)"), Err(vec!["<input>:1:7: an assignment of an import".to_string()]));
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
    assert_eq!(eval(&mut program, "(require lib/text) (user \"ann\" 3)"), Err(vec!["<input>:1:21: a struct whose constructor its module doesn't provide".to_string()]));
    // A module an input requires by name is there for the inputs after it, till they define
    // what it does.
    assert_eq!(eval(&mut program, "(twice 4)"), values(&["8"]));
    assert_eq!(eval(&mut program, "(define (twice x) 'mine) (twice 4)"), values(&["mine"]));
    assert_eq!(eval(&mut program, "(list (twice 4) (shout \"a\"))"), values(&["(mine \"a!\")"]));
    let mut filtered = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(eval(&mut filtered, "(require (only-in lib/text twice)) (twice 4)"), values(&["8"]));
    assert_eq!(eval(&mut filtered, "(twice 4)"), Err(vec!["<input>:1:2: a name nothing defines".to_string()]));
    let main = file(&root, "main.rg", "(require lib/foo lib/text)\n(define made (make-user \"bo\" 1))\n(greet made)\n(twice 2)");
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&main, true), Ok(()));
    let failing = file(&root, "failing.rg", "(require lib/text)\n(twice 'two)");
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&failing, true), Err(vec!["uncaught: #<error WrongType>".to_string()]));
    assert_eq!(Program::new(HEAP, library(&root)).unwrap().run_file(&failing, false), Ok(()));
    // A module that's required runs as an entry point does: what it drops as it starts is
    // collected as it goes, however much that is.
    let churn = "(define (churn i last) (if (= i 0) (vector-length last) (churn (- i 1) (make-vector 200000 i))))";
    file(&root, "heavy/heavy.rg", &format!("(provide made)\n{churn}\n(define made (churn 400 #f))"));
    let mut heavy = Program::new(HEAP, vec![dir("heavy", &root.join("heavy"))]).unwrap();
    assert_eq!(eval(&mut heavy, "(require heavy) made"), values(&["200000"]));
    assert_eq!(eval(&mut heavy, &format!("{churn} (churn 400 #f)")), values(&["200000"]));
    // A long run is stepped, so what it drops is collected as it goes.
    let long = file(&root, "long.rg", "(define (count i acc) (if (= i 0) (length acc) (count (- i 1) (cons i '()))))\n(count 3000000 '())");
    assert_eq!(Program::new(HEAP, Vec::new()).unwrap().run_file(&long, true), Ok(()));
}

#[test]
fn what_is_wrong_says_where() {
    let root = scratch("wrong");
    let run = |dirs: Vec<ModuleDir>, path: &Path| Program::new(HEAP, dirs).unwrap().run_file(path, true).unwrap_err();
    let at = |path: &Path, rest: &str| format!("{}:{rest}", path.display());
    let unbound = file(&root, "unbound.rg", "(define (f) 1)\n\n(f 1 2\n   (g))\n");
    assert_eq!(run(Vec::new(), &unbound), [at(&unbound, "4:5: a name nothing defines")]);
    let unclosed = file(&root, "unclosed.rgn", "(%define x 1)\n(%define y");
    assert_eq!(run(Vec::new(), &unclosed), [at(&unclosed, "2:1: a list, string or comment that's never closed")]);
    let native = file(&root, "native.rgn", "(%define x 1)\n  (x)");
    assert_eq!(run(Vec::new(), &native), [at(&native, "2:3: a list that doesn't start with a form's name")]);
    let missing = file(&root, "missing.rg", "(require nope)");
    assert_eq!(run(Vec::new(), &missing), [at(&missing, "1:10: a module that can't be found")]);
    assert!(run(Vec::new(), &root.join("absent.rg"))[0].starts_with(&at(&root.join("absent.rg"), " ")));

    // An error in a required module comes first, then where it was required.
    let broken = file(&root, "broken/one.rg", "(provide f)\n(define (f) 1)");
    let second = file(&root, "broken/two.rg", "(define (g)\n  (h))");
    let user = file(&root, "user.rg", "(require broken)\n(f)");
    assert_eq!(run(vec![dir("broken", broken.parent().unwrap())], &user), [at(&second, "2:4: a name nothing defines"), at(&user, "1:10: a module that can't be found")]);
    let raising = file(&root, "raising/one.rg", "(car 1)");
    let raises = file(&root, "raises.rg", "(require raising)");
    assert_eq!(run(vec![dir("raising", raising.parent().unwrap())], &raises), ["module raising: uncaught: #<error WrongType>".to_string(), at(&raises, "1:10: a module that can't be found")]);
    let empty = scratch("wrong-empty");
    let needs = file(&root, "needs.rg", "(require empty)");
    assert_eq!(run(vec![dir("empty", &empty)], &needs), [format!("{}: no .rg or .rgn files", empty.display()), at(&needs, "1:10: a module that can't be found")]);

    // Modules that require each other can't be loaded.
    let a = file(&root, "a/a.rg", "(require b)");
    let b = file(&root, "b/b.rg", "(require a)");
    let dirs = vec![dir("a", a.parent().unwrap()), dir("b", b.parent().unwrap())];
    let cycle = file(&root, "cycle.rg", "(require a)");
    assert_eq!(run(dirs, &cycle), ["module a: it requires itself, through a, b".to_string(), at(&b, "1:10: a module that can't be found"), at(&a, "1:10: a module that can't be found"), at(&cycle, "1:10: a module that can't be found")]);
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
    assert_eq!(program.run_file(&wrong, false), Err(vec![format!("{}:1:14: a name nothing defines", wrong.display())]));
    assert_eq!(program.take_listing(), "");
}

#[test]
fn an_image_starts_a_program_from_the_modules_it_holds() {
    let root = scratch("images");
    let mut program = Program::new(HEAP, library(&root)).unwrap();
    assert_eq!(program.load_all(), Ok(()));
    let bytes = program.save_image().unwrap();
    // Nothing is read from the folders again: the modules are the image's.
    std::fs::remove_dir_all(root.join("text")).unwrap();
    std::fs::remove_dir_all(root.join("foo")).unwrap();
    let mut loaded = Program::from_image(HEAP, Vec::new(), &bytes).unwrap();
    assert_eq!(eval(&mut loaded, "(require lib/foo lib/text) (list (greet (make-user \"ann\" 3)) (twice 21))"), values(&["(\"ann!\" 42)"]));
    assert_eq!(eval(&mut loaded, "(list display (twice 1))").map(|written| written.len()), Ok(1));
    let main = file(&root, "main.rg", "(require lib/foo lib/text)\n(greet (make-user \"bo\" 1))\n(twice 'two)");
    assert_eq!(Program::from_image(HEAP, Vec::new(), &bytes).unwrap().run_file(&main, true), Err(vec!["uncaught: #<error WrongType>".to_string()]));

    // Modules from folders go on top, and the two make another image.
    file(&root, "extra/e.rg", "(require lib/text)\n(provide thrice)\n(define (thrice x) (+ x (twice x)))");
    let mut more = Program::from_image(HEAP, vec![dir("extra", &root.join("extra"))], &bytes).unwrap();
    assert_eq!(more.load_all(), Ok(()));
    let both = more.save_image().unwrap();
    let mut last = Program::from_image(HEAP, Vec::new(), &both).unwrap();
    assert_eq!(eval(&mut last, "(require extra) (thrice 5)"), values(&["15"]));

    let clash = Program::from_image(HEAP, vec![dir("lib/text", &root)], &bytes).err();
    assert_eq!(clash, Some(vec!["the module `lib/text` is in the image already".to_string()]));
    assert_eq!(Program::from_image(HEAP, Vec::new(), b"not an image").err(), Some(vec!["not a ragwort image, or one that's damaged".to_string()]));
    let mut other = bytes.clone();
    other[8] ^= 1;
    assert_eq!(Program::from_image(HEAP, Vec::new(), &other).err(), Some(vec!["the image was made by another build of ragwort".to_string()]));
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
