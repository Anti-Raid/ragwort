use ragwort_native::LowerErrorKind;
use ragwort_scheme::ExpandErrorKind;
use ragwort_vm::objects::ModuleFields;

use super::*;

/// The native module `loops`, which exports macros and keeps a helper procedure and a helper macro to itself.
const LOOPS: &str = "(%define-syntax while
                       (%syntax-rules ()
                         ((_ test body ...) (%loop again (%if test (%begin body ...) (%break again))))))
                     (%define-syntax unless
                       (%syntax-rules ()
                         ((_ test body ...) (%if test #f (%begin body ...)))))
                     (%define-syntax counted
                       (%syntax-rules ()
                         ((_ body) (%begin (%app note) (twice body) (%app notes)))))
                     (%define-syntax twice
                       (%syntax-rules ()
                         ((_ body) (%begin body body))))
                     (%define count 0)
                     (%define note (%lambda () (%set! count (%intrinsic + count 1))))
                     (%define notes (%lambda () count))
                     (%provide while unless counted)";

#[test]
fn native_macros_are_used_from_native_and_scheme() {
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "loops", &[(Native, LOOPS)]), Ok(Ok("#<void>".into())));
    let native = "(%require loops)
                  (%let ((n 0) (seen '()))
                    (while (%intrinsic < n 3)
                      (%set! seen (%intrinsic cons n seen))
                      (%set! n (%intrinsic + n 1)))
                    seen)";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native)]), Ok(Ok("(2 1 0)".into())));
    // In a Scheme module, the parts of the macro's use are Scheme expressions.
    let scheme = "(require loops)
                  (define (collect limit)
                    (let ((n 0) (seen '()))
                      (while (< n limit)
                        (set! seen (cons (* n n) seen))
                        (set! n (+ n 1)))
                      (reverse seen)))
                  (list (collect 4) (unless (pair? '()) 'empty))";
    assert_eq!(module_in(&mut arena, "scheme-user", &[(Scheme, scheme)]), Ok(Ok("((0 1 4 9) empty)".into())));
    // A Scheme file still cannot name a core form itself.
    let direct = module_in(&mut arena, "direct", &[(Scheme, "(%intrinsic car '(a))")]);
    assert!(matches!(direct, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{direct:?}");
}

#[test]
fn a_macros_output_refers_to_its_own_module() {
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "loops", &[(Native, LOOPS)]), Ok(Ok("#<void>".into())));
    // `counted` uses a macro and two procedures that `loops` does not export. The user's own `note`, `notes` and `twice` are other bindings.
    let scheme = "(require loops)
                  (define (note) 'mine)
                  (define notes 'mine)
                  (define (twice x) (list x x))
                  (define hits 0)
                  (list (counted (set! hits (+ hits 1))) hits (note) (twice notes))";
    assert_eq!(module_in(&mut arena, "scheme-user", &[(Scheme, scheme)]), Ok(Ok("(1 2 mine (mine mine))".into())));
    let native = "(%require loops)
                  (%let ((note 'local) (hits 0))
                    (%intrinsic cons (counted (%set! hits (%intrinsic + hits 1))) hits))";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native)]), Ok(Ok("(2 . 2)".into())));
    // The names that the macro's output uses are not bindings of the module that uses the macro.
    let hidden = module_in(&mut arena, "hidden", &[(Scheme, "(require loops) (notes)")]);
    assert!(matches!(hidden, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{hidden:?}");
}

#[test]
fn scheme_macros_are_exported_to_scheme() {
    let mut arena = arena();
    let library = "(define (pair-up a b) (cons a b))
                   (define-syntax swap!
                     (syntax-rules ()
                       ((_ a b) (let ((tmp a)) (set! a b) (set! b tmp)))))
                   (define-syntax paired
                     (syntax-rules (with)
                       ((_ a with b) (pair-up a b))
                       ((_ a) (paired a with 'alone))))
                   (provide swap! paired)";
    assert_eq!(module_in(&mut arena, "tools", &[(Scheme, library)]), Ok(Ok("#<void>".into())));
    // The macro's `tmp`, `let`, `cons` and `pair-up` are the library's. The literal `with` matches the same name in the use.
    let user = "(require tools)
                (define (pair-up a b) 'mine)
                (let ((tmp 1) (other 2) (let 'shadowed) (cons 'shadowed))
                  (swap! tmp other)
                  (list tmp other (paired tmp with other) (paired tmp)))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("(2 1 (2 . 1) (2 . alone))".into())));
    // Filters rename a macro as they rename a variable.
    let renamed = "(require (prefix-in t: (only-in tools swap!)))
                   (let ((a 1) (b 2)) (t:swap! a b) (list a b))";
    assert_eq!(module_in(&mut arena, "renamed", &[(Scheme, renamed)]), Ok(Ok("(2 1)".into())));
    let missing = module_in(&mut arena, "missing", &[(Scheme, "(require (only-in tools swap!)) (paired 1)")]);
    assert!(matches!(missing, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{missing:?}");
    // A macro is not a value.
    let value = module_in(&mut arena, "value", &[(Scheme, "(require tools) (list swap!)")]);
    assert!(matches!(value, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::BadSyntax), "{value:?}");
    // Native ragwort cannot expand Scheme's forms, so it cannot use a Scheme macro.
    let native = module_in(&mut arena, "native-user", &[(Native, "(%require tools) (%let ((a 1) (b 2)) (swap! a b))")]);
    assert!(matches!(native, Err(Error::Lower(e)) if e.kind == LowerErrorKind::Language), "{native:?}");
}

#[test]
fn exported_macros_can_define_and_be_exported_again() {
    let mut arena = arena();
    let library = "(%define-syntax define-getter
                     (%syntax-rules ()
                       ((_ name value) (%begin (%define held value) (%define name (%lambda () held))))))
                   (%provide (all-defined-out))";
    assert_eq!(module_in(&mut arena, "getters", &[(Native, library)]), Ok(Ok("#<void>".into())));
    // Each use defines a variable of the using module, and a hidden variable that only that use refers to.
    let scheme = "(require getters)
                  (define-getter one 1)
                  (define-getter two 2)
                  (define held 'mine)
                  (list (one) (two) held)";
    assert_eq!(module_in(&mut arena, "scheme-user", &[(Scheme, scheme)]), Ok(Ok("(1 2 mine)".into())));
    let native = "(%require getters)
                  (define-getter one 'a)
                  (define-getter two 'b)
                  (%intrinsic cons (%app one) (%app two))";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native)]), Ok(Ok("(a . b)".into())));
    // A module's own macro can use an imported macro, and a third module can use that macro.
    let middle = "(require getters)
                  (define-syntax define-getters
                    (syntax-rules ()
                      ((_ (name value) ...) (begin (define-getter name value) ...))))
                  (provide define-getters)";
    assert_eq!(module_in(&mut arena, "middle", &[(Scheme, middle)]), Ok(Ok("#<void>".into())));
    let last = "(require middle) (define-getters (a 1) (b 2)) (list (a) (b))";
    assert_eq!(module_in(&mut arena, "last", &[(Scheme, last)]), Ok(Ok("(1 2)".into())));
}

#[test]
fn a_modules_files_share_macros_across_languages() {
    let mut arena = arena();
    // A macro of native ragwort is made of core forms, so the module's Scheme file can use it. The files are declared in order.
    let native = "(%define-syntax unless (%syntax-rules () ((_ test body ...) (%if test #f (%begin body ...)))))
                  (%define count 0)
                  (%define-syntax tally (%syntax-rules () ((_ body) (%begin (%set! count (%intrinsic + count 1)) body count))))";
    let scheme = "(define (check n) (unless (< n 0) 'not-negative))
                  (provide unless)
                  (list (check 1) (check -1) (tally 'one) (tally 'two))";
    assert_eq!(module_in(&mut arena, "mixed", &[(Native, native), (Scheme, scheme)]), Ok(Ok("(not-negative #f 1 2)".into())));
    // Either file can provide the macro, and another module can then require it.
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, "(require mixed) (unless #f 'ran)")]), Ok(Ok("ran".into())));
    // A Scheme macro is made of Scheme's forms, which the native file cannot use.
    let scheme = "(define-syntax twice (syntax-rules () ((_ body) (begin body body))))";
    let other = module_in(&mut arena, "other", &[(Scheme, scheme), (Native, "(twice 'a)")]);
    assert!(matches!(other, Err(Error::Lower(e)) if e.kind == LowerErrorKind::Language), "{other:?}");
}

#[test]
fn a_module_passes_on_what_it_requires() {
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "loops", &[(Native, LOOPS)]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "numbers", &[(Scheme, "(define (double n) (* 2 n)) (define limit 3) (provide double limit)")]), Ok(Ok("#<void>".into())));
    // `kit` provides two macros of `loops`, a procedure and a variable of `numbers` under new names, a prelude procedure, and a definition of its own.
    let kit = "(require loops numbers)
               (define (triple n) (* 3 n))
               (provide while counted triple car (rename-out (double twice) (limit top)))";
    assert_eq!(module_in(&mut arena, "kit", &[(Scheme, kit)]), Ok(Ok("#<void>".into())));
    // A module that requires only `kit` gets all of them. The macros' output still refers to `loops`.
    let user = "(require kit)
                (define n 0)
                (while (< n top) (set! n (+ n 1)))
                (list n (twice 4) (triple 4) (counted 'x) (car '(a b)))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("(3 8 12 1 a)".into())));
    // A native module passes on in the same way, and a module can pass on what was passed on to it.
    assert_eq!(module_in(&mut arena, "again", &[(Native, "(%require kit) (%provide while twice)")]), Ok(Ok("#<void>".into())));
    let last = "(require again) (define n 0) (while (< n 5) (set! n (twice (+ n 1)))) n";
    assert_eq!(module_in(&mut arena, "last", &[(Scheme, last)]), Ok(Ok("6".into())));
    // A binding that is passed on is the binding of the module that defines it.
    let same = "(require kit numbers (prefix-in again: again)) (list (eq? twice double) (eq? again:twice double))";
    assert_eq!(module_in(&mut arena, "same", &[(Scheme, same)]), Ok(Ok("(#t #t)".into())));
}

#[test]
fn exported_macros_refer_to_what_other_macros_defined() {
    let mut arena = arena();
    // `define-counter` defines a hidden variable, a hidden macro that reads it, and a macro and a procedure under the names of its use.
    let library = "(define-syntax define-counter
                     (syntax-rules ()
                       ((_ name next!)
                        (begin
                          (define count 0)
                          (define-syntax peek (syntax-rules () ((_) count)))
                          (define (next!) (set! count (+ count 1)))
                          (define-syntax name (syntax-rules () ((_) (list (peek) count))))))))
                   (define-counter hits hit!)
                   (define-counter misses miss!)
                   (provide hits hit! misses miss!)";
    assert_eq!(module_in(&mut arena, "counters", &[(Scheme, library)]), Ok(Ok("#<void>".into())));
    let user = "(require counters)
                (define count 'mine)
                (define (peek) 'mine)
                (hit!) (hit!) (miss!)
                (list (hits) (misses) count (peek))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("((2 2) (1 1) mine mine)".into())));
    // The same in native ragwort, used from Scheme.
    let native = "(%define-syntax define-cell
                    (%syntax-rules ()
                      ((_ read write!)
                       (%begin
                         (%define held 'empty)
                         (%define-syntax held-twice (%syntax-rules () ((_) (%intrinsic cons held held))))
                         (%define write! (%lambda (value) (%set! held value)))
                         (%define-syntax read (%syntax-rules () ((_) (held-twice))))))))
                  (define-cell cell-ref cell-set!)
                  (%provide cell-ref cell-set!)";
    assert_eq!(module_in(&mut arena, "cells", &[(Native, native)]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "cell-user", &[(Scheme, "(require cells) (define held 'mine) (cell-set! 7) (list (cell-ref) held)")]), Ok(Ok("((7 . 7) mine)".into())));
}

/// Returns the names of the variables of the module `name` that hold a value, out of `names`.
fn held(arena: &mut Arena, name: &str, names: &[&str]) -> Vec<String> {
    arena.mutate(|mc| {
        let module = Registry.resolve(mc, name, Value::FALSE).unwrap();
        let slots = ragwort_types::vector::AnyVector::of(module.names(mc)).unwrap();
        let mut found = Vec::new();
        for slot in 0..slots.len(mc) {
            let text = ragwort_printer_scheme::to_string(mc, slots.get(mc, slot).unwrap(), ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap();
            if names.contains(&text.as_str()) && module.items(mc).get(slot) != Value::UNDEFINED {
                found.push(text);
            }
        }
        found.sort();
        found
    })
}

#[test]
fn a_module_keeps_only_the_macros_that_another_module_can_reach() {
    let mut arena = arena();
    let macros = ["exported", "inner", "local-only", "unused-helper", "quoted", "by-quoted"];
    // `exported` is provided, and its output uses `inner`. The module uses `local-only` and `unused-helper` only itself.
    let library = "(define (wrap x) (list x))
                   (define-syntax inner (syntax-rules () ((_ x) (wrap x))))
                   (define-syntax exported (syntax-rules () ((_ x) (inner x))))
                   (define-syntax unused-helper (syntax-rules () ((_ x) (wrap x))))
                   (define-syntax local-only (syntax-rules () ((_ x) (unused-helper x))))
                   (define (uses-local) (local-only 1))
                   (provide exported uses-local)";
    assert_eq!(module_in(&mut arena, "kept", &[(Scheme, library)]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "kept", &macros), ["exported", "inner"]);
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, "(require kept) (list (exported 5) (uses-local))")]), Ok(Ok("((5) (1))".into())));
    // Syntax that the module's code quotes can reach another module, so the macros that it refers to are kept. A macro in a body is not.
    let quoting = "(define-syntax by-quoted (syntax-rules () ((_) 'reached)))
                   (define-syntax quoted (syntax-rules () ((_) (by-quoted))))
                   (define-syntax unused-helper (syntax-rules () ((_) 'unused)))
                   (define (in-body) (let-syntax ((local (syntax-rules () ((_) (unused-helper))))) (local)))
                   (define (use) (quote-syntax (quoted)))
                   (provide use in-body)";
    assert_eq!(module_in(&mut arena, "quoting", &[(Scheme, quoting)]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "quoting", &macros), ["by-quoted", "quoted"]);
    let user = "(require quoting)
                (define-syntax splice (lambda (stx) (use)))
                (list (splice) (in-body))";
    assert_eq!(module_in(&mut arena, "quote-user", &[(Scheme, user)]), Ok(Ok("(reached unused)".into())));
    // `all-defined-out` provides the macros too, so the module keeps them all. `all-var-defined-out` provides only the variables.
    let helpers = "(define-syntax inner (syntax-rules () ((_ x) (list x))))
                   (define (one) (inner 1))
                   (provide (FORM))";
    assert_eq!(module_in(&mut arena, "everything", &[(Scheme, &helpers.replace("FORM", "all-defined-out"))]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "everything", &macros), ["inner"]);
    assert_eq!(module_in(&mut arena, "variables", &[(Scheme, &helpers.replace("FORM", "all-var-defined-out"))]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "variables", &macros), [""; 0]);
    assert_eq!(module_in(&mut arena, "one-user", &[(Scheme, "(require variables) (one)")]), Ok(Ok("(1)".into())));
    let unprovided = module_in(&mut arena, "inner-user", &[(Scheme, "(require variables) (inner 1)")]);
    assert!(matches!(unprovided, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{unprovided:?}");
    assert_eq!(module_in(&mut arena, "native-variables", &[(Native, "(%define-syntax inner (%syntax-rules () ((_ x) x))) (%define two (inner 2)) (%provide (all-var-defined-out))")]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "native-variables", &macros), [""; 0]);
    assert_eq!(module_in(&mut arena, "two-user", &[(Scheme, "(require native-variables) two")]), Ok(Ok("2".into())));
    // The same holds for native ragwort.
    let native = "(%define-syntax inner (%syntax-rules () ((_ x) (%intrinsic cons x x))))
                  (%define-syntax exported (%syntax-rules () ((_ x) (inner x))))
                  (%define-syntax local-only (%syntax-rules () ((_ x) x)))
                  (%define five (local-only 5))
                  (%provide exported five)";
    assert_eq!(module_in(&mut arena, "native-kept", &[(Native, native)]), Ok(Ok("#<void>".into())));
    assert_eq!(held(&mut arena, "native-kept", &macros), ["exported", "inner"]);
    assert_eq!(module_in(&mut arena, "native-user", &[(Scheme, "(require native-kept) (list (exported 1) five)")]), Ok(Ok("((1 . 1) 5)".into())));
}

#[test]
fn a_module_passes_on_everything_from_a_module() {
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "loops", &[(Native, LOOPS)]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "numbers", &[(Scheme, "(define (double n) (* 2 n)) (define limit 3) (provide double limit)")]), Ok(Ok("#<void>".into())));
    // An umbrella module: it provides what it requires, under the names that it uses itself, next to a definition of its own.
    let kit = "(require loops (prefix-in n: numbers))
               (define (triple n) (* 3 n))
               (provide triple (all-from-out loops numbers))";
    assert_eq!(module_in(&mut arena, "kit", &[(Scheme, kit)]), Ok(Ok("#<void>".into())));
    let user = "(require kit)
                (define n 0)
                (while (< n n:limit) (set! n (+ n 1)))
                (list n (n:double 4) (triple 4) (unless #f 'ran))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("(3 8 12 ran)".into())));
    // A native module does the same, and the bindings stay those of the modules that define them.
    assert_eq!(module_in(&mut arena, "all", &[(Native, "(%require kit numbers) (%provide (all-from-out kit numbers))")]), Ok(Ok("#<void>".into())));
    let last = "(require all numbers) (list (eq? double n:double) (triple limit) (unless #f 'ran))";
    assert_eq!(module_in(&mut arena, "last", &[(Scheme, last)]), Ok(Ok("(#t 9 ran)".into())));
    // A module can pass on the module that it requires implicitly. Its own `car` shadows the prelude's, so it does not pass on a `car`.
    assert_eq!(module_in(&mut arena, "base", &[(Scheme, "(define (car x) 'mine) (provide (all-from-out scheme))")]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "base-user", &[(Scheme, "(require (prefix-in b: (only-in base cadr))) (b:cadr '(a b))")]), Ok(Ok("b".into())));
    let shadowed = module_in(&mut arena, "shadowed", &[(Scheme, "(require (only-in base car))")]);
    assert!(matches!(shadowed, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::NotProvided), "{shadowed:?}");
    let missing = module_in(&mut arena, "missing", &[(Scheme, "(provide (all-from-out loops))")]);
    assert!(matches!(missing, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::NotDefined), "{missing:?}");
}

#[test]
fn a_require_takes_a_group_of_specs() {
    let mut arena = arena();
    assert_eq!(module_in(&mut arena, "loops", &[(Native, LOOPS)]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "numbers", &[(Scheme, "(define (double n) (* 2 n)) (define limit 3) (provide double limit)")]), Ok(Ok("#<void>".into())));
    // A group requires every spec in it.
    assert_eq!(module_in(&mut arena, "plain", &[(Scheme, "(require [loops numbers]) (list (double limit) (unless #f 'ran))")]), Ok(Ok("(6 ran)".into())));
    // A filter around a group applies to all of it, and the names that it mentions come from any member. A member can be a filter or a group itself.
    let filtered = "(require (prefix-in k: [loops [(only-in numbers double)]]))
                    (require (only-in [numbers loops] limit unless))
                    (list (k:double limit) (k:unless #f 'ran) (unless #f 'too))";
    assert_eq!(module_in(&mut arena, "filtered", &[(Scheme, filtered)]), Ok(Ok("(6 ran too)".into())));
    let native = "(%require (rename-in [loops numbers] (double twice) (unless if-not)))
                  (%intrinsic cons (%app twice limit) (if-not #f 'ran))";
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, native)]), Ok(Ok("(6 . ran)".into())));
    // A name that no member provides is an error at the name. A module that a group passes on is found by the name that the group wrote.
    let missing = module_in(&mut arena, "missing", &[(Scheme, "(require (only-in [numbers loops] limit nope))")]);
    assert!(matches!(missing, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::NotProvided), "{missing:?}");
    assert_eq!(module_in(&mut arena, "passes", &[(Scheme, "(require [loops numbers]) (provide (all-from-out numbers))")]), Ok(Ok("#<void>".into())));
    // A filter around a group can keep nothing of a member. The member is still required, so the module can pass on all of it, which is nothing.
    let emptied = "(require (only-in [loops numbers] double)) (provide (all-from-out loops numbers))";
    assert_eq!(module_in(&mut arena, "emptied", &[(Scheme, emptied)]), Ok(Ok("#<void>".into())));
    assert_eq!(module_in(&mut arena, "emptied-user", &[(Scheme, "(require (prefix-in e: emptied)) (e:double 4)")]), Ok(Ok("8".into())));
    let gone = module_in(&mut arena, "gone-user", &[(Scheme, "(require (only-in emptied while))")]);
    assert!(matches!(gone, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::NotProvided), "{gone:?}");
    assert_eq!(module_in(&mut arena, "last", &[(Scheme, "(require (prefix-in p: passes)) (p:double p:limit)")]), Ok(Ok("6".into())));
    // The libraries of Scheme are required the same way.
    let bare = "(require [scheme/number scheme/list]) (car (list (+ 1 2)))";
    assert_eq!(module_in(&mut arena, "numbers-and-lists", &[(Scheme, bare)]), Ok(Ok("3".into())));
}

/// Loads `text` as a Scheme module that requires nothing implicitly, and returns the written form of its last form's value.
fn bare(arena: &mut Arena, name: &str, text: &str) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let files = [File { language: Scheme, session: &session }];
        let loaded = load(mc, symbols, &Source { name, hosts: &[], files: &files, implicit: &[], internals: false }, &mut Registry)?;
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            match run(mc, thunk) {
                Ok(value) => last = value,
                Err(fault) => return Ok(Err(fault)),
            }
        }
        Ok(Ok(ragwort_printer_scheme::to_string(mc, last, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap()))
    })
}

#[test]
fn a_scheme_module_starts_with_the_forms_and_no_procedure() {
    let mut arena = arena();
    // Every form works in a module that requires nothing, the ones that expand to calls of procedures included.
    let forms = "(struct point (x y))
                 (define-syntax swap! (syntax-rules () ((_ a b) (let ((tmp a)) (set! a b) (set! b tmp)))))
                 (define (kind v)
                   (match v
                     [(list a b) `(two ,a ,@(case b [(1 2) '(small)] [else '(big)]))]
                     [(point x _) (cond [x => (lambda (found) found)] [else 'none])]
                     [(vector a _) a]
                     [_ 'other]))
                 (define moved (struct-copy point (point 1 2) [x 5]))
                 (define caught (guard (e (#t 'caught)) (match 5 [(list) 'empty])))
                 (define marked (with-continuation-mark 'key 'value (let-values ([(a) (let ((x 1) (y 2)) (swap! x y) (when (if x #t #f) (quote-syntax here)) (unless #f 'done))]) a)))
                 (do ((i 0 (if i i i)) (acc '() acc)) (#t `(,(kind '(1 2)) ,(kind moved) ,(kind #(v w)) ,(kind 5) ,caught)))";
    assert_eq!(bare(&mut arena, "forms", forms), Ok(Ok("((two 1 small) 5 v other caught)".into())));
    // A procedure is in a library. The module has it once it requires the library, and has nothing else of the language.
    let unbound = bare(&mut arena, "unbound", "(car '(1))");
    assert!(matches!(unbound, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{unbound:?}");
    assert_eq!(bare(&mut arena, "lists", "(require scheme/list) (car '(1))"), Ok(Ok("1".into())));
    let other = bare(&mut arena, "other", "(require scheme/list) (+ (car '(1)) 1)");
    assert!(matches!(other, Err(Error::Expand(e)) if e.kind == ExpandErrorKind::Unbound), "{other:?}");
    assert_eq!(bare(&mut arena, "all", "(require scheme) (+ (car '(1)) (string-length \"ab\"))"), Ok(Ok("3".into())));
    // A procedure that a form calls is the language's own, whatever the module defines under that name.
    let shadowed = "(define (equal? a b) #f) (define (car x) 'mine) (define (list . xs) 'mine) (match '(1 2) [(list 1 b) b])";
    assert_eq!(bare(&mut arena, "shadowed", shadowed), Ok(Ok("2".into())));
}

#[test]
fn the_list_of_what_each_library_provides_matches_the_libraries() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let mut total = 0;
        for (library, _) in ragwort_scheme::LIBRARIES {
            let module = Registry.resolve(mc, library, Value::FALSE).unwrap();
            let mut exported: Vec<String> = ragwort_compiler::module::Imports::all(mc, module).unwrap().0.into_iter().map(|(name, _)| name).collect();
            exported.sort();
            let mut listed: Vec<String> = ragwort_scheme::PROVIDED.iter().filter(|&&(_, provider)| provider == library).map(|&(name, _)| name.to_string()).collect();
            listed.sort();
            assert_eq!(exported, listed, "{library}");
            assert!(exported.iter().all(|name| library_of(name) == Some(library)), "{library}");
            total += exported.len();
        }
        // No two libraries provide the same name, and `scheme` passes on every one.
        let all = Registry.resolve(mc, ragwort_scheme::SCHEME.0, Value::FALSE).unwrap();
        assert_eq!(ragwort_compiler::module::Imports::all(mc, all).unwrap().0.len(), total);
        assert_eq!(total, ragwort_scheme::PROVIDED.len());
        assert_eq!(library_of("no-such-procedure"), None);
    });
}

#[test]
fn a_case_lambda_is_a_procedure_like_any_other_across_modules() {
    let mut arena = arena();
    let library = "(define area (case-lambda [(side) (* side side)] [(width height) (* width height)]))
                   (define-syntax describe (syntax-rules () ((_ x ...) (case-lambda [() 'none] [(extra) (list extra x ...)]))))
                   (provide area describe)";
    assert_eq!(module_in(&mut arena, "shapes", &[(Scheme, library)]), Ok(Ok("#<void>".into())));
    // Another module calls it, passes it on, and gets one from a macro. A native module calls it too.
    let user = "(require shapes) (define d (describe 1 2)) (list (area 3) (area 2 5) (map area '(1 2)) (d) (d 0))";
    assert_eq!(module_in(&mut arena, "user", &[(Scheme, user)]), Ok(Ok("(9 10 (1 4) none (0 1 2))".into())));
    assert_eq!(module_in(&mut arena, "native-user", &[(Native, "(%require shapes) (%app area 4 5)")]), Ok(Ok("20".into())));
    assert_eq!(module_in(&mut arena, "wrong", &[(Scheme, "(require shapes) (area 1 2 3)")]), Ok(Err(Fault::Arity)));
}
