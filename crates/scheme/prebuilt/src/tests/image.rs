use ragwort_compiler::module::Resolver;
use ragwort_modules_core::{File, Language, Source};
use ragwort_types::gc::{Arena, Gc, Value};
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::{MIN_SEGMENT, Machine, Outcome};

use super::*;

/// Finds a library among the modules that the image gave.
struct Loaded<'m, 'gc>(&'m [(&'static str, Gc<'gc, Module>)]);

impl<'gc> Resolver<'gc> for Loaded<'_, 'gc> {
    fn resolve(&mut self, _: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        self.0.iter().find(|(loaded, _)| *loaded == name).map(|&(_, module)| module)
    }
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

/// Loads the image into a new arena, then compiles `text` as a module that can require the libraries, and runs it. Returns the written
/// form of the last form's value.
fn program(text: &str) -> String {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let (symbols, libraries) = load(mc).unwrap();
        assert!(libraries.thunks.is_empty());
        let session = SyntaxSession::new(mc, text).unwrap();
        let files = [File { language: Language::Scheme, session: &session }];
        let source = Source { name: "main", hosts: &[], files: &files, implicit: &[], internals: false };
        let mut resolver = Loaded(&libraries.modules);
        let loaded = ragwort_modules_core::load(mc, symbols, &source, &mut resolver).unwrap();
        let mut last = Value::VOID;
        for thunk in loaded.thunks {
            last = finish(mc, thunk);
        }
        ragwort_printer_scheme::to_string(mc, last, ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap()
    })
}

/// The image of this build loads. A program that falls back to compiling the libraries when it does not load would hide a failure here.
#[test]
fn the_libraries_of_scheme_load_from_the_image() {
    // Each arena that loads the image has the libraries, and code requires one of them or all of them.
    assert_eq!(program("(require scheme/number scheme/list) (map (lambda (n) (* n n)) (list 1 2 3))"), "(1 4 9)");
    assert_eq!(program("(require scheme) (define t (table 'a 1)) (table-set! t 'b (string-append \"x\" (number->string 2))) (table->list t)"), "((a . 1) (b . \"x2\"))");
    assert_eq!(program("(require scheme) (define co (make-coroutine (lambda (a) (co/yield (+ a 1)) 'end))) (list (co/resume co 1) (co/resume co) (co/status co))"), "(2 end dead)");
    // The modules are in the order of the libraries, with the `scheme` module last.
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| {
        let (_, libraries) = load(mc).unwrap();
        let names: Vec<&str> = libraries.modules.iter().map(|&(name, _)| name).collect();
        assert_eq!(names.len(), ragwort_modules_core::libraries::scheme::LIBRARIES.len() + 1);
        assert_eq!(names.last(), Some(&"scheme"));
        assert!(names.contains(&"scheme/number"));
    });
}

#[test]
fn bytes_that_are_no_image_of_this_build_do_not_load() {
    assert!(Arena::new(1 << 24, 0).mutate(|mc| read(mc, &[]).is_err()));
    // A changed byte no longer matches the image's checksum.
    let mut bytes = IMAGE.to_vec();
    let last = bytes.len() - 1;
    bytes[last] ^= 1;
    assert!(Arena::new(1 << 24, 0).mutate(|mc| read(mc, &bytes).is_err()));
}
