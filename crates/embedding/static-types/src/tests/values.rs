use ragwort_compiler::module::NoModules;
use ragwort_scheme::LIBRARIES;
use ragwort_types::external::{ExternalKind, ExternalRefs};
use ragwort_types::gc::{self, Arena, Mutation};
use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::Module;
use ragwort_vm::{MIN_SEGMENT, Machine, Outcome};

use crate::{Error, Number, Pair, Table, Value};

/// Creates an arena whose root 0 holds the symbol table and whose root 1 holds a list of the modules of Scheme's libraries, which have run.
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 24, 2);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        let mut libraries = gc::Value::NULL;
        for (name, source) in LIBRARIES {
            let session = SyntaxSession::named(mc, name, source).unwrap();
            let loaded = ragwort_native::load(mc, symbols, name, &[], &[&session], &mut NoModules).unwrap();
            for thunk in loaded.thunks {
                run(mc, thunk);
            }
            libraries = ragwort_types::pair::Pairs::new(mc).cons(gc::Value::object(mc, loaded.module), libraries).unwrap().value(mc);
        }
        mc.set_root(1, libraries);
    });
    arena
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: gc::Value<'gc>) -> gc::Value<'gc> {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).unwrap();
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return value,
            _ => panic!("the program did not finish"),
        }
    }
}

/// Runs the forms of `text` and returns the value of the last one.
fn eval<'gc>(mc: &Mutation<'gc>, text: &str) -> gc::Value<'gc> {
    let symbols = Symbols::of(mc.root(0)).unwrap();
    let libraries: Vec<_> = ragwort_types::pair::Pairs::new(mc).elements(mc.root(1)).map(|module| module.downcast::<Module>(mc).unwrap()).collect();
    let session = SyntaxSession::new(mc, text).unwrap();
    let loaded = ragwort_scheme::load(mc, symbols, "main", &[&session], &libraries, &mut NoModules).unwrap();
    let mut last = gc::Value::VOID;
    for thunk in loaded.thunks {
        last = run(mc, thunk);
    }
    last
}

/// Runs `text` and returns its value as a static value.
fn kept(arena: &mut Arena, text: &str) -> Value {
    arena.mutate(|mc| Value::from_gc(mc, eval(mc, text)).unwrap())
}

fn show(arena: &mut Arena, value: &Value) -> std::string::String {
    arena.mutate(|mc| ragwort_printer_scheme::to_string(mc, value.to_gc(mc).unwrap(), ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap())
}

/// A value that is not an object becomes plain data. It takes no handle and gives the same value back.
#[test]
fn values_that_are_no_objects_are_plain_data() {
    let mut arena = arena();
    let cases = [
        ("#t", Value::Boolean(true)),
        ("#f", Value::Boolean(false)),
        ("'()", Value::Null),
        ("#nil", Value::Nil),
        ("#none", Value::None),
        ("(if #f #f)", Value::Void),
        ("-42", Value::Integer(-42)),
        ("4611686018427387903", Value::Integer(gc::Value::MAX_FIXNUM)),
        // Too large for a value word, but not for an `i64`.
        ("9223372036854775807", Value::Integer(i64::MAX)),
        ("-9223372036854775808", Value::Integer(i64::MIN)),
        ("1.5", Value::Float(1.5)),
        // A flonum that has no encoding in a value word.
        ("1e300", Value::Float(1e300)),
        ("#\\λ", Value::Char('λ')),
    ];
    for (text, expected) in cases {
        let value = kept(&mut arena, text);
        assert_eq!(value, expected, "{text}");
        assert_eq!(arena.handles(), 0, "{text} takes no handle");
        let back = arena.mutate(|mc| Value::from_gc(mc, value.to_gc(mc).unwrap()).unwrap());
        assert_eq!(back, expected, "{text} comes back");
    }
    assert_eq!((Value::from(true), Value::from(7i64), Value::from('x')), (Value::Boolean(true), Value::Integer(7), Value::Char('x')));
}

/// Each kind of object gets the handle type of its kind. The handle keeps the object while collections move it, and gives it back.
#[test]
fn each_kind_of_object_gets_its_handle_type() {
    let mut arena = arena();
    let cases = [
        ("\"a string that is longer than a value word\"", "string", "\"a string that is longer than a value word\""),
        ("(string-append \"one part and \" \"another part of a rope\")", "string", "\"one part and another part of a rope\""),
        ("'name", "symbol", "name"),
        ("'#:name", "keyword", "#:name"),
        ("(expt 2 100)", "number", "1267650600228229401496703205376"),
        ("(/ 1 3)", "number", "1/3"),
        ("(make-bytevector 3 1)", "bytevector", "#u8(1 1 1)"),
        ("(cons 1 2)", "pair", "(1 . 2)"),
        ("(vector 1 \"two\" 'three)", "vector", "#(1 \"two\" three)"),
    ];
    let mut values = Vec::new();
    for (text, name, _) in cases {
        let value = kept(&mut arena, text);
        assert_eq!(value.type_name(), name, "{text}");
        values.push(value);
    }
    assert_eq!(arena.handles(), cases.len());
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    for (value, (text, _, written)) in values.iter().zip(cases) {
        assert_eq!(show(&mut arena, value), written, "{text}");
    }
    drop(values);
    assert_eq!(arena.handles(), 0);
}

#[test]
fn tables_structs_procedures_and_coroutines_have_handle_types() {
    let mut arena = arena();
    let table = kept(&mut arena, "(let ([t (make-table)]) (table-set! t 'answer 42) t)");
    let instance = kept(&mut arena, "(struct point (x y)) (point 3 4)");
    let procedure = kept(&mut arena, "(lambda (x) (+ x 1))");
    let keyword_procedure = kept(&mut arena, "(lambda (x #:by [by 1]) (+ x by))");
    let coroutine = kept(&mut arena, "(make-coroutine (lambda () 1))");
    let condition = kept(&mut arena, "(guard (e [#t e]) (car 5))");
    let names = [&table, &instance, &procedure, &keyword_procedure, &coroutine, &condition].map(Value::type_name);
    assert_eq!(names, ["table", "struct", "procedure", "procedure", "coroutine", "value"]);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let Value::Table(table) = &table else { panic!("a table") };
        let key = Symbols::of(mc.root(0)).unwrap().intern_str(&Strings::new(mc), "answer").unwrap().value(mc);
        assert_eq!(table.get(mc).unwrap().get(mc, key).unwrap().and_then(gc::Value::as_fixnum), Some(42));
        let Value::Struct(instance) = &instance else { panic!("a struct") };
        let fields = ragwort_vm::structs::field(mc, instance.value(mc).unwrap(), 1).unwrap();
        assert_eq!(fields.as_fixnum(), Some(4));
        // A procedure that is kept can be called in a later step.
        let Value::Procedure(procedure) = &procedure else { panic!("a procedure") };
        let mut machine = Machine::new(mc, MIN_SEGMENT, procedure.get(mc).unwrap(), &[gc::Value::fixnum(41).unwrap()]).unwrap();
        let Outcome::Done(result) = machine.run(mc).unwrap() else { panic!("done") };
        assert_eq!(result.as_fixnum(), Some(42));
    });
}

static COUNTER: ExternalKind<u32> = ExternalKind::by_identity("counter");

#[test]
fn external_values_and_short_strings() {
    let mut arena = Arena::new(1 << 20, 0);
    let (external, short, long) = arena.mutate(|mc| {
        let external = ExternalRefs::new(mc).make(&COUNTER, 7u32, 0, gc::Value::NULL).unwrap();
        let strings = Strings::new(mc);
        let short = ragwort_types::string::from_str(&strings, "héllo").unwrap().value();
        let long = ragwort_types::string::from_str(&strings, "longer than seven bytes").unwrap().value();
        (Value::from_gc(mc, external.value(mc)).unwrap(), Value::from_gc(mc, short).unwrap(), Value::from_gc(mc, long).unwrap())
    });
    // The short string is in its handle. The external value and the long string each take a slot.
    assert_eq!(arena.handles(), 2);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let Value::External(external) = &external else { panic!("an external value") };
        assert_eq!(external.get(mc).unwrap().data::<u32>(mc), Some(&7));
        let (Value::String(short), Value::String(long)) = (&short, &long) else { panic!("strings") };
        let strings = Strings::new(mc);
        assert_eq!(ragwort_types::string::to_string(&strings, short.get(mc).unwrap()), "héllo");
        assert_eq!(ragwort_types::string::to_string(&strings, long.get(mc).unwrap()), "longer than seven bytes");
    });
    // A value that is no object is the same in every arena. A handle of an object is refused by another arena.
    let mut other = Arena::new(1 << 20, 0);
    other.mutate(|mc| {
        assert!(short.to_gc(mc).is_ok());
        assert_eq!((long.to_gc(mc).err(), external.to_gc(mc).err()), (Some(Error::Foreign), Some(Error::Foreign)));
    });
}

/// A typed handle is made only of a value of its kind. Handles compare by identity.
#[test]
fn typed_handles_check_the_kind_and_compare_by_identity() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let pairs = ragwort_types::pair::Pairs::new(mc);
        let pair = pairs.cons(gc::Value::fixnum(1).unwrap(), gc::Value::NULL).unwrap().value(mc);
        let twin = pairs.cons(gc::Value::fixnum(1).unwrap(), gc::Value::NULL).unwrap().value(mc);
        assert!(Table::of(mc, pair).unwrap().is_none() && Pair::of(mc, gc::Value::NULL).unwrap().is_none());
        let first = Pair::of(mc, pair).unwrap().unwrap();
        assert!(first == Pair::of(mc, pair).unwrap().unwrap() && first != Pair::of(mc, twin).unwrap().unwrap() && first == first.clone());
        assert_eq!(first.get(mc).unwrap().head(mc).as_fixnum(), Some(1));
        // A number handle takes any number. A small one costs no slot.
        let small = Number::of(mc, gc::Value::fixnum(5).unwrap()).unwrap().unwrap();
        assert!(!small.handle().is_object() && Number::of(mc, pair).unwrap().is_none());
        assert_eq!(Value::from(first.clone()), Value::from_gc(mc, pair).unwrap());
    });
    assert_eq!(arena.handles(), 0);
}

#[test]
fn a_weak_handle_gives_its_typed_handle_while_the_object_lives() {
    let mut arena = Arena::new(1 << 20, 0);
    let pair = arena.mutate(|mc| {
        let pair = ragwort_types::pair::Pairs::new(mc).cons(gc::Value::fixnum(9).unwrap(), gc::Value::NULL).unwrap();
        Pair::of(mc, pair.value(mc)).unwrap().unwrap()
    });
    let weak = pair.downgrade();
    let copy = weak.clone();
    arena.set_evacuate_all(true);
    arena.collect();
    let again: Pair = weak.upgrade().unwrap();
    assert!(again == pair);
    arena.mutate(|mc| assert_eq!(again.get(mc).unwrap().head(mc).as_fixnum(), Some(9)));
    drop((pair, again));
    arena.collect();
    assert!(weak.upgrade().is_none() && copy.upgrade().is_none());
    assert_eq!((arena.handles(), arena.objects()), (0, 0));
}
