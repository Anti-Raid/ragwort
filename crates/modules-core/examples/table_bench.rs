//! Times table reads and measures table sizes, for tables that a program makes and for tables that a host holds.
//!
//! A host that passes events to a program makes a new table for every event, and the program reads a few
//! fields of each table once. So the cost that matters is the first read of a field of a new table, and the
//! memory that each table takes. The lines printed:
//!
//! - `loop + host call`: the loop that every other line runs, with a host call that returns a number.
//! - `external ...`: a table whose entries the host holds, made by a host call.
//! - `external with shape ...`: the same table, made with a shape that the host built once. The host is still asked by key.
//! - `external by position ...`: the same, for a host that also looks its fields up by position.
//! - `record ...`: a table in the arena that a host call fills with the same six fields, key by key.
//! - `shaped record ...`: the same table, made by the host from a shape that it built once.
//! - `literal ...`: a table in the arena that the program makes with `(table 'id 1 ...)`.
//! - `... same table`: one table made before the loop and read in the loop.
//! - `... two kinds in turn`: one procedure reads tables of two shapes alternately. The two shapes have the same keys in opposite orders.
//! - `bytes per table`: the memory that one table takes while the program holds it.
//!
//! An argument limits the run to the lines whose name contains it: `table_bench "by position"`.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_compiler::module::Resolver;
use ragwort_modules_core::{File, Language, Source, load, prelude};
use ragwort_types::Error;
use ragwort_types::gc::{Arena, Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::Strings;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_types::table::{ExternalTable, Key, Shape, Tables};
use ragwort_vm::objects::Module;
use ragwort_vm::{Fault, HostArgs, HostContext, HostDef, MIN_SEGMENT, Machine, Outcome, Purity, Reply, host};

/// The number of loop iterations that each timed line runs.
const N: usize = 1_000_000;
/// The number of tables that a size measurement holds.
const HELD: usize = 10_000;

const FIELDS: [&str; 6] = ["id", "content", "author-id", "channel-id", "guild-id", "pinned"];

/// An event with six fields. Every field is a small number, so that the timings show the cost of the table and not the cost of making the values.
struct Message;

impl Message {
    fn field(name: &str) -> Option<i64> {
        FIELDS.iter().position(|&field| field == name).map(|position| position as i64 + 1)
    }
}

impl ExternalTable for Message {
    fn len(&self) -> usize {
        FIELDS.len()
    }

    fn has(&self, key: Key<'_>) -> bool {
        matches!(key, Key::Symbol(name) if Self::field(name).is_some())
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        let Key::Symbol(name) = key else { return Ok(None) };
        Ok(Self::field(name).and_then(Value::fixnum))
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        FIELDS.into_iter().map(Key::Symbol)
    }
}

/// A [`Message`] that also looks its fields up by their position in the shape. If `reversed`, its shape has the fields in the opposite order.
struct Positional {
    reversed: bool,
}

impl ExternalTable for Positional {
    fn len(&self) -> usize {
        FIELDS.len()
    }

    fn has(&self, key: Key<'_>) -> bool {
        Message.has(key)
    }

    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        Message.get(mc, key)
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        FIELDS.into_iter().map(Key::Symbol)
    }

    fn get_at<'gc>(&self, _: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>> {
        let field = if self.reversed { FIELDS.len().checked_sub(position + 1) } else { Some(position) };
        Some(Ok(field.filter(|&field| field < FIELDS.len()).and_then(|field| Value::fixnum(field as i64 + 1))))
    }
}

/// Returns the shape of a [`Message`], or the shape with the same fields in the opposite order if `reversed`. Each is made on the first call and kept in a root.
fn shape<'gc>(mc: &Mutation<'gc>, reversed: bool) -> Result<Shape<'gc>, Fault> {
    let root = if reversed { 4 } else { 3 };
    if let Some(shape) = Shape::of(mc.root(root)) {
        return Ok(shape);
    }
    let symbols = Symbols::of_arena(mc)?;
    let mut keys = Vec::with_capacity(FIELDS.len());
    for name in FIELDS {
        keys.push(symbols.intern_str(&Strings::new(mc), name)?.value(mc));
    }
    if reversed {
        keys.reverse();
    }
    let shape = Tables::new(mc).shape(&keys).map_err(|_| Fault::OutOfMemory)?;
    mc.set_root(root, shape.value(mc));
    Ok(shape)
}

fn zero<'s, 'gc>(_: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Value(Value::fixnum(0).expect("a small number")))
}

fn message<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Value(Tables::new(cx.mc()).external(Message, 0)?.value(cx.mc())))
}

/// Makes a table in the arena with the fields of a [`Message`].
fn record<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    let symbols = Symbols::of_arena(mc)?;
    let table = Tables::new(mc).with_room(FIELDS.len())?;
    for name in FIELDS {
        let key = symbols.intern_str(&Strings::new(mc), name)?.value(mc);
        let value = Message::field(name).and_then(Value::fixnum).expect("a field has a small number");
        table.set(mc, key, value).map_err(|_| Fault::OutOfMemory)?;
    }
    Ok(Reply::Value(table.value(mc)))
}

/// Makes the same table as [`record`] from the shape of a [`Message`].
fn shaped_record<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    Ok(Reply::Value(Tables::new(mc).shaped(shape(mc, false)?, (1..=FIELDS.len() as i64).map(Value::fixnum))?.value(mc)))
}

fn shaped_message<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    Ok(Reply::Value(Tables::new(mc).external_shaped(shape(mc, false)?, Message, 0)?.value(mc)))
}

fn positional_message<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    Ok(Reply::Value(Tables::new(mc).external_shaped(shape(mc, false)?, Positional { reversed: false }, 0)?.value(mc)))
}

fn reversed_message<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    let mc = cx.mc();
    Ok(Reply::Value(Tables::new(mc).external_shaped(shape(mc, true)?, Positional { reversed: true }, 0)?.value(mc)))
}

static HOSTS: [HostDef; 7] = [
    host!("zero", 0, Purity::Impure, zero),
    host!("message", 0, Purity::Impure, message),
    host!("record", 0, Purity::Impure, record),
    host!("shaped-record", 0, Purity::Impure, shaped_record),
    host!("shaped-message", 0, Purity::Impure, shaped_message),
    host!("positional-message", 0, Purity::Impure, positional_message),
    host!("reversed-message", 0, Purity::Impure, reversed_message),
];

const BINDINGS: &str = "(%define zero (%lambda () (%call-host zero))) (%define message (%lambda () (%call-host message))) (%define record (%lambda () (%call-host record))) \
                        (%define shaped-record (%lambda () (%call-host shaped-record))) (%define shaped-message (%lambda () (%call-host shaped-message))) \
                        (%define positional-message (%lambda () (%call-host positional-message))) (%define reversed-message (%lambda () (%call-host reversed-message))) \
                        (%provide (all-defined-out))";

/// A [`Resolver`] that finds the modules registered in root 2, a list of `(name . module)` pairs.
struct Registry;

impl<'gc> Resolver<'gc> for Registry {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        let name = Symbols::of(mc.root(0))?.intern_str(&Strings::new(mc), name).ok()?.value(mc);
        let mut entries = Pairs::new(mc).elements(mc.root(2)).filter_map(Pair::of);
        entries.find(|entry| entry.head(mc) == name)?.tail(mc).downcast::<Module>(mc)
    }
}

fn run<'gc>(mc: &Mutation<'gc>, thunk: Value<'gc>) {
    let mut machine = Machine::new(mc, MIN_SEGMENT, thunk, &[]).expect("machine");
    loop {
        match machine.run(mc).expect("run") {
            Outcome::Paused => {}
            Outcome::Done(_) => return,
            outcome => panic!("{outcome:?}"),
        }
    }
}

/// Loads module `name` from `text` into `arena` and registers it. Runs every form but the last, and returns a machine that runs the last form.
fn loaded(arena: &mut Arena, name: &str, language: Language, text: &str) -> Machine {
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).expect("the symbol table");
        let prelude = mc.root(1).downcast::<Module>(mc).expect("the prelude");
        let session = SyntaxSession::new(mc, text).expect("session");
        let files = [File { language, session: &session }];
        let loaded = load(mc, symbols, prelude, &Source { name, hosts: &HOSTS, files: &files, implicit: &[], internals: false }, &mut Registry).expect("load");
        let (last, first) = loaded.thunks.split_last().expect("a form");
        for &thunk in first {
            run(mc, thunk);
        }
        let name = symbols.intern_str(&Strings::new(mc), name).expect("name").value(mc);
        let entry = Pairs::new(mc).list_with_tail(vec![name], Value::object(mc, loaded.module)).expect("entry");
        mc.set_root(2, Pairs::new(mc).list_with_tail(vec![entry], mc.root(2)).expect("registry"));
        Machine::new(mc, MIN_SEGMENT, *last, &[]).expect("machine")
    })
}

/// Makes an arena that holds the prelude and the `events` module, whose procedures call the host functions.
fn arena() -> Arena {
    let mut arena = Arena::new(256 << 20, 5);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).expect("the symbol table");
        mc.set_root(0, symbols.value(mc));
        let loaded = prelude(mc, symbols).expect("the prelude");
        for thunk in loaded.thunks {
            run(mc, thunk);
        }
        mc.set_root(1, Value::object(mc, loaded.module));
        mc.set_root(2, Value::NULL);
    });
    let mut machine = loaded(&mut arena, "events", Language::Native, BINDINGS);
    finish(&mut arena, &mut machine);
    arena
}

/// Runs `machine` to its end, one collector step after another.
fn finish(arena: &mut Arena, machine: &mut Machine) {
    while !arena.step(|mc| matches!(black_box(machine.run(mc).expect("run")), Outcome::Done(_))).expect("room") {}
}

/// Returns the best time, over a few runs, of a loop of [`N`] iterations that adds up `body`. `setup` is a sequence of definitions that run before the loop.
fn time(setup: &str, body: &str) -> Duration {
    let text = format!("(require \"events\") {setup} (define (run n) (let loop ((i 0) (sum 0)) (if (< i n) (loop (+ i 1) (+ sum {body})) sum))) (run {N})");
    let mut best = Duration::MAX;
    for _ in 0..5 {
        let mut arena = arena();
        let mut machine = loaded(&mut arena, "main", Language::Scheme, &text);
        let start = Instant::now();
        finish(&mut arena, &mut machine);
        best = best.min(start.elapsed());
    }
    best
}

/// Returns the bytes of the pages that hold objects in an arena that holds `count` values, after a collection, and the number of live objects. `make` is an expression that makes a value, such as a table, and uses it as the program would. It can refer to `i`, the number of the value. `setup` is a sequence of definitions that run first.
fn held(setup: &str, make: &str, count: usize) -> (usize, usize) {
    let mut arena = arena();
    let text = format!("(require \"events\") {setup} (define keep (make-vector {count} #f)) (let loop ((i 0)) (if (< i {count}) (begin (vector-set! keep i {make}) (loop (+ i 1))) #t))");
    let mut machine = loaded(&mut arena, "keep", Language::Scheme, &text);
    finish(&mut arena, &mut machine);
    arena.collect();
    arena.collect();
    (arena.occupied_bytes(), arena.objects())
}

/// Returns the number of bytes that one table takes while a program holds it. The arena charges whole pages, so the size is the difference between holding four times [`HELD`] tables and holding eight times as many.
fn size(setup: &str, make: &str) -> (f64, f64) {
    let (more, less) = (held(setup, make, 8 * HELD), held(setup, make, 4 * HELD));
    ((more.0 - less.0) as f64 / (4 * HELD) as f64, (more.1 - less.1) as f64 / (4 * HELD) as f64)
}

fn main() {
    let read3 = "(+ (table-ref t 'id) (table-ref t 'author-id) (table-ref t 'channel-id))";
    let literal = "(table 'id 1 'content 2 'author-id 3 'channel-id 4 'guild-id 5 'pinned 6)";
    let stepwise = "(let ((t (make-table))) (table-set! t 'id 1) (table-set! t 'content 2) (table-set! t 'author-id 3) (table-set! t 'channel-id 4) (table-set! t 'guild-id 5) (table-set! t 'pinned 6) t)";
    let helped = "(let ((t (make-table))) (put! t 'id 1) (put! t 'content 2) (put! t 'author-id 3) (put! t 'channel-id 4) (put! t 'guild-id 5) (put! t 'pinned 6) t)";
    let mapped = "(let ((t (make-table))) (table-set! t i 1) (table-set! t (+ i 1) 2) (table-set! t (+ i 2) 3) (table-set! t (+ i 3) 4) (table-set! t (+ i 4) 5) (table-set! t (+ i 5) 6) t)";
    let roomy = "(let ((t (make-table 6))) (table-set! t i 1) (table-set! t (+ i 1) 2) (table-set! t (+ i 2) 3) (table-set! t (+ i 3) 4) (table-set! t (+ i 4) 5) (table-set! t (+ i 5) 6) t)";
    // The same tables with string keys. Two of the three keys that are read are too long to be held in a value word.
    let read3_worded = "(+ (table-ref t \"id\") (table-ref t \"author-identity\") (table-ref t \"channel-identity\"))";
    let worded = "(table \"id\" 1 \"content\" 2 \"author-identity\" 3 \"channel-identity\" 4 \"guild-identity\" 5 \"pinned\" 6)";
    let stepwise_worded = "(let ((t (make-table))) (table-set! t \"id\" 1) (table-set! t \"content\" 2) (table-set! t \"author-identity\" 3) (table-set! t \"channel-identity\" 4) (table-set! t \"guild-identity\" 5) (table-set! t \"pinned\" 6) t)";
    // A table with keys of its own: the keys are set with strings that are made at run time, so they are other objects than the constants of the reads.
    let fill_worded = "(table-set! t (string-append \"i\" \"d\") 1) (table-set! t (string-append \"author\" \"-identity\") 3) (table-set! t (string-append \"channel\" \"-identity\") 4)";
    let base = time("", "(zero)");
    let lines = [
        ("external, made", String::new(), "(begin (message) 0)".to_string()),
        ("external, made and 3 fields read once", String::new(), format!("(let ((t (message))) {read3})")),
        ("external, made and 3 fields read twice", String::new(), format!("(let ((t (message))) (+ {read3} {read3}))")),
        ("external, 3 fields of the same table", "(define t (message))".to_string(), read3.to_string()),
        ("external with shape, made", String::new(), "(begin (shaped-message) 0)".to_string()),
        ("external with shape, 3 fields read once", String::new(), format!("(let ((t (shaped-message))) {read3})")),
        ("external by position, 3 fields read once", String::new(), format!("(let ((t (positional-message))) {read3})")),
        ("external by position, 3 fields read twice", String::new(), format!("(let ((t (positional-message))) (+ {read3} {read3}))")),
        ("external by position, two kinds in turn", "(define (read t) (+ (table-ref t 'id) (table-ref t 'author-id) (table-ref t 'channel-id)))".to_string(), "(read (if (even? i) (positional-message) (reversed-message)))".to_string()),
        ("record, made", String::new(), "(begin (record) 0)".to_string()),
        ("record, made and 3 fields read once", String::new(), format!("(let ((t (record))) {read3})")),
        ("shaped record, made", String::new(), "(begin (shaped-record) 0)".to_string()),
        ("shaped record, made and 3 fields read once", String::new(), format!("(let ((t (shaped-record))) {read3})")),
        ("literal, made", String::new(), format!("(begin {literal} 0)")),
        ("literal, made and 3 fields read once", String::new(), format!("(let ((t {literal})) {read3})")),
        ("literal, 3 fields of the same table", format!("(define t {literal})"), read3.to_string()),
        ("field by field, made", String::new(), format!("(begin {stepwise} 0)")),
        ("field by field, made and 3 fields read once", String::new(), format!("(let ((t {stepwise})) {read3})")),
        ("field by field through a helper, made", "(define (put! t k v) (table-set! t k v))".to_string(), format!("(begin {helped} 0)")),
        ("copy of a literal, made", format!("(define t {literal})"), "(begin (table-copy t) 0)".to_string()),
        ("copy of a literal, 3 fields read once", format!("(define source {literal})"), format!("(let ((t (table-copy source))) {read3})")),
        ("string keys, literal, 3 fields of the same table", format!("(define t {worded})"), read3_worded.to_string()),
        ("string keys, literal, made and 3 fields read once", String::new(), format!("(let ((t {worded})) {read3_worded})")),
        ("string keys, field by field, made", String::new(), format!("(begin {stepwise_worded} 0)")),
        ("string keys, map, 3 fields of the same table", format!("(define t (let ((t (make-table 8))) {fill_worded} t))"), read3_worded.to_string()),
        ("string keys, map, key from a variable", format!("(define t {worded}) (define key (string-append \"author\" \"-identity\"))"), "(table-ref t key)".to_string()),
        (
            "string keys, long key from a variable",
            "(define t (table \"a field name that is a good deal longer than the usual ones are\" 1 \"id\" 2)) (define key (string-append \"a field name that is a good deal \" \"longer than the usual ones are\"))".to_string(),
            "(table-ref t key)".to_string(),
        ),
        ("map, 6 integer keys set", String::new(), format!("(begin {mapped} 0)")),
        ("map made with room, 6 integer keys set", String::new(), format!("(begin {roomy} 0)")),
        (
            "literal, two kinds in turn",
            "(define (read t) (+ (table-ref t 'id) (table-ref t 'author-id) (table-ref t 'channel-id)))".to_string(),
            format!("(read (if (even? i) {literal} (table 'pinned 6 'guild-id 5 'channel-id 4 'author-id 3 'content 2 'id 1)))"),
        ),
    ];
    let only = std::env::args().nth(1).unwrap_or_default();
    let nanos = base.as_secs_f64() * 1e9 / N as f64;
    println!("{:<42} {nanos:6.1} ns per iteration", "loop + host call");
    for (name, setup, body) in lines {
        if !name.contains(&only) {
            continue;
        }
        let took = time(&setup, &body).as_secs_f64() * 1e9 / N as f64;
        println!("{name:<42} {took:6.1} ns per iteration, {:6.1} over the loop", took - nanos);
    }
    println!();
    let sizes = [
        ("external, no field read", "(message)".to_string()),
        ("external, 1 field read", "(let ((t (message))) (table-ref t 'id) t)".to_string()),
        ("external, 3 fields read", format!("(let ((t (message))) {read3} t)")),
        ("external by position, 3 fields read", format!("(let ((t (positional-message))) {read3} t)")),
        ("record", "(record)".to_string()),
        ("shaped record", "(shaped-record)".to_string()),
        ("literal", literal.to_string()),
        ("field by field", stepwise.to_string()),
        ("copy of a literal", format!("(table-copy {literal})")),
    ];
    for (name, make) in sizes {
        if !name.contains(&only) {
            continue;
        }
        let (bytes, objects) = size("", &make);
        println!("{name:<42} {bytes:6.0} bytes per table, in {objects:.1} objects");
    }
    println!();
    // Strings that a program holds. Each text is about 36 characters, or about 606 for the long ones.
    let piece = "(define piece (make-string 600 #\\x)) (define other (string-append piece \"zzzzzz\"))";
    let strings = [
        ("string, a different text each", "", "(string-append \"a string that is kept, number \" (number->string (+ 100000 i)))"),
        ("string, the same text each time", "", "(string-append \"a string that is the same \" \"every time\")"),
        ("long string on a shared piece", piece, "(string-append piece (number->string (+ 100000 i)))"),
        ("long string on a shared piece, compared", piece, "(let ((s (string-append piece (number->string (+ 100000 i))))) (string=? s other) s)"),
        // Text with an emoji, as chat messages have: about 38 characters, and a message of about 100.
        ("string with an emoji, a different text each", "", "(string-append \"a string 😀 that is kept, number \" (number->string (+ 100000 i)))"),
        ("message of 100 characters with an emoji", "", "(string-append \"😀 \" (number->string (+ 100000 i)) \" \" (make-string 90 #\\a))"),
    ];
    for (name, setup, make) in strings {
        if !name.contains(&only) {
            continue;
        }
        let (bytes, objects) = size(setup, make);
        println!("{name:<42} {bytes:6.0} bytes per string, in {objects:.1} objects");
    }
}
