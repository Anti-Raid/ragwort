use ragwort_compiler::module::Resolver;
use ragwort_types::pair::Pair;
use ragwort_types::string::Strings;

use super::*;

/// The modules registered in root 3.
struct Registry;

impl<'gc> Resolver<'gc> for Registry {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        let name = Symbols::of(mc.root(0))?.intern_str(&Strings::new(mc), name).ok()?.value(mc);
        let mut entries = Pairs::new(mc).elements(mc.root(3)).filter_map(Pair::of);
        entries.find(|entry| entry.head(mc) == name)?.tail(mc).downcast::<Module>(mc)
    }
}

/// Loads the module `name` from the Scheme `text`, runs it, and registers it for the modules
/// loaded after to require. Returns its last form's value, written out, or the fault one raised.
fn module_in(arena: &mut Arena, name: &str, text: &str) -> Result<Result<String, Fault>, Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let prelude = mc.root(2).downcast::<Module>(mc).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let loaded = load(mc, symbols, prelude, name, &[&session], &[], &mut Registry)?;
        Ok(run_and_register(mc, name, loaded))
    })
}

/// [`module_in`], of native ragwort.
fn native_in(arena: &mut Arena, name: &str, text: &str) -> Result<Result<String, Fault>, ragwort_native::Error> {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let session = SyntaxSession::new(mc, text).unwrap();
        let loaded = ragwort_native::load(mc, symbols, name, &[], &[&session], &mut Registry)?;
        Ok(run_and_register(mc, name, loaded))
    })
}

/// Runs what's `loaded`, and registers its module as `name`.
fn run_and_register<'gc>(mc: &Mutation<'gc>, name: &str, loaded: ragwort_compiler::module::Loaded<'gc>) -> Result<String, Fault> {
    let symbols = Symbols::of(mc.root(0)).unwrap();
    let mut last = Value::VOID;
    for thunk in loaded.thunks {
        last = run(mc, thunk)?;
    }
    let name = symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc);
    let entry = Pairs::new(mc).list_with_tail(vec![name], Value::object(mc, loaded.module)).unwrap();
    mc.set_root(3, Pairs::new(mc).list_with_tail(vec![entry], mc.root(3)).unwrap());
    Ok(show(mc, last))
}

/// An arena with a native module `lib` registered: `twice`, `bump!`, and `total`, the count of
/// bumps, which `bump!` assigns.
fn with_lib() -> Arena {
    let mut arena = arena();
    let lib = "(%provide twice bump! (rename-out (count total)))
               (%define count 0)
               (%define twice (%lambda (x) (%intrinsic + x x)))
               (%define bump! (%lambda () (%set! count (%intrinsic + count 1)) count))";
    native_in(&mut arena, "lib", lib).unwrap().unwrap();
    arena
}

#[test]
fn scheme_requires_what_native_modules_provide() {
    let mut arena = with_lib();
    let mut eval = |text: &str| module_in(&mut arena, "main", text).unwrap().unwrap();
    // An export its module assigns is read as it is when it's read.
    assert_eq!(eval("(require lib) (let* ((a (bump!)) (b (bump!))) (list (twice 4) a b total))"), "(8 1 2 2)");
    assert_eq!(eval("(require (prefix-in l: lib)) (l:twice 2)"), "4");
    assert_eq!(eval("(require (rename-in lib (twice double))) (double 3)"), "6");
    assert_eq!(eval("(require (only-in lib twice) (except-in lib twice bump!)) (list (twice 1) total)"), "(2 2)");
    // A module's own definition shadows the prelude's, but not what it requires.
    assert_eq!(eval("(require lib) (define (car x) (twice x)) (car 5)"), "10");
}

#[test]
fn modules_mistakes_point_at_themselves() {
    let mut arena = with_lib();
    let mut error = |text: &str| match module_in(&mut arena, "main", text) {
        Err(Error::Expand(e)) => (e.kind, text[e.start as usize..e.end as usize].to_string()),
        other => panic!("{text} expanded: {other:?}"),
    };
    assert_eq!(error("(require nowhere)"), (Resolve, "nowhere".into()));
    assert_eq!(error("(require (only-in lib nope))"), (NotProvided, "nope".into()));
    assert_eq!(error("(require (rename-in lib (nope x)))"), (NotProvided, "(nope x)".into()));
    assert_eq!(error("(require (sideways lib))"), (BadSyntax, "(sideways lib)".into()));
    assert_eq!(error("(require lib) (define twice 1)"), (Conflict, "twice".into()));
    assert_eq!(error("(require lib) (set! total 1)"), (Immutable, "total".into()));
    assert_eq!(error("(require (only-in lib twice)) bump!"), (Unbound, "bump!".into()));
    assert_eq!(error("(provide nope)"), (NotDefined, "nope".into()));
    assert_eq!(error("(define a 1) (provide a (rename-out (a a)))"), (Duplicate, "(a a)".into()));
    assert_eq!(error("(define a 1) (define a 2)"), (Duplicate, "a".into()));
    assert_eq!(error("(let () (require lib) 1)"), (Definition, "(require lib)".into()));
    assert_eq!(error("(if #t (provide x) 1)"), (Definition, "(provide x)".into()));
    // A name nothing defines is an error before anything runs, wherever it is.
    assert_eq!(error("(define (f) (g)) (define (g) 1) (define (h) nowhere)"), (Unbound, "nowhere".into()));
    // A transformer runs before the module's variables are defined.
    assert_eq!(error("(define helper 1) (define-syntax m (lambda (s) helper)) (m)"), (Phase, "(lambda (s) helper)".into()));
}

#[test]
fn a_variable_used_before_its_definition_runs_is_unbound() {
    let mut arena = arena();
    let mut eval = |text: &str| module_in(&mut arena, "main", text).unwrap();
    assert_eq!(eval("(define (f) y) (define r (f)) (define y 1)"), Err(Fault::Unbound));
    assert_eq!(eval("(define y 1) (define (f) y) (f)"), Ok("1".into()));
}

#[test]
fn native_modules_require_what_scheme_ones_provide() {
    let mut arena = arena();
    let shapes = "(provide area (rename-out (side edge))) (define side 3) (define (area) (* side side))";
    module_in(&mut arena, "shapes", shapes).unwrap().unwrap();
    let native = "(%require shapes) (%intrinsic cons (%app area) edge)";
    assert_eq!(native_in(&mut arena, "main", native), Ok(Ok("(9 . 3)".into())));
}
