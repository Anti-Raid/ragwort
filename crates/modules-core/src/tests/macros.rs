use ragwort_native::LowerErrorKind;
use ragwort_scheme::ExpandErrorKind;

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
