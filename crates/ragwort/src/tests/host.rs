use std::cell::Cell;
use std::rc::Rc;

use ragwort_compiler::module::NoModules;
use ragwort_types::gc::Arena;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::objects::{Condition, ConditionFields};
use ragwort_vm::report::procedure_name;
use ragwort_vm::{MIN_SEGMENT, Machine, Outcome};

use super::*;

/// Creates an arena whose root 0 holds the symbol table and whose root 1 holds the [`Hosting`].
fn arena() -> Arena {
    let mut arena = Arena::new(1 << 22, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        mc.set_root(0, symbols.value(mc));
        mc.set_root(1, Hosting::install(mc, symbols).unwrap().value(mc));
    });
    arena
}

fn hosting<'gc>(mc: &Mutation<'gc>) -> Hosting<'gc> {
    Hosting::of(mc, mc.root(1)).unwrap()
}

fn fixnum<'gc>(number: i64) -> Value<'gc> {
    Value::fixnum(number).unwrap()
}

fn number(value: Option<Value<'_>>) -> Result<i64, Fault> {
    value.and_then(Value::as_fixnum).ok_or(Fault::WrongType)
}

/// Calls `procedure` with `args`. Returns its value, or the fault of the condition that it raised.
fn call<'gc>(mc: &Mutation<'gc>, procedure: Value<'gc>, args: &[Value<'gc>]) -> Result<Value<'gc>, Fault> {
    // A call of the wrong arity fails before the machine starts.
    let mut machine = Machine::new(mc, MIN_SEGMENT, procedure, args)?;
    loop {
        match machine.run(mc).unwrap() {
            Outcome::Paused => {}
            Outcome::Done(value) => return Ok(value),
            Outcome::Raised(raised) => return Err(raised.downcast::<Condition>(mc).expect("a condition").failure(mc).unwrap().fault),
            _ => panic!("the call did not finish"),
        }
    }
}

/// Loads `text` as native code and returns the value of its one form.
fn native<'gc>(mc: &Mutation<'gc>, text: &str) -> Value<'gc> {
    let symbols = Symbols::of(mc.root(0)).unwrap();
    let session = SyntaxSession::new(mc, text).unwrap();
    let loaded = ragwort_native::load(mc, symbols, "main", &[], &[&session], &mut NoModules).unwrap();
    let [thunk] = loaded.thunks[..] else { panic!("one form") };
    call(mc, thunk, &[]).unwrap()
}

fn add<'s, 'gc>(_: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>, _: Captures<'gc>) -> Result<Reply<'gc>, Fault> {
    Ok(Reply::Value(fixnum(number(args.get(0))? + number(args.get(1))?)))
}

#[test]
fn a_closure_is_called_with_its_arguments_and_its_own_state() {
    let mut arena = arena();
    let calls = Rc::new(Cell::new(0));
    let counted = calls.clone();
    arena.mutate(|mc| {
        let scaled = hosting(mc)
            .procedure(mc, None, Arity::Exactly(2), &[], move |_, args, _| {
                counted.set(counted.get() + 1);
                Ok(Reply::Value(fixnum(number(args.get(0))? * 10 + number(args.get(1))?)))
            })
            .unwrap();
        assert!(ragwort_vm::is_procedure(mc, scaled));
        assert_eq!(call(mc, scaled, &[fixnum(4), fixnum(2)]), Ok(fixnum(42)));
        // Code of a program calls it as any procedure, in and out of tail position.
        let twice = native(mc, "(%lambda (f) (%intrinsic + (%app f 1 2) (%app f 3 4)))");
        assert_eq!(call(mc, twice, &[scaled]), Ok(fixnum(46)));
        let tail = native(mc, "(%lambda (f) (%app f 7 7))");
        assert_eq!(call(mc, tail, &[scaled]), Ok(fixnum(77)));
        // A fault of the closure is raised as a fault of an intrinsic is.
        assert_eq!(call(mc, scaled, &[fixnum(1), Value::NULL]), Err(Fault::WrongType));
    });
    assert_eq!(calls.get(), 5);
}

#[test]
fn the_arity_is_checked_before_the_closure_runs() {
    let mut arena = arena();
    arena.mutate(|mc| {
        for fixed in 0..=MAX_FIXED {
            let count = hosting(mc).procedure(mc, None, Arity::Exactly(fixed), &[], |_, args, _| Ok(Reply::Value(fixnum(args.len() as i64)))).unwrap();
            let args: Vec<Value> = (0..fixed as i64 + 1).map(fixnum).collect();
            assert_eq!(call(mc, count, &args[..fixed]), Ok(fixnum(fixed as i64)), "{fixed} arguments");
            assert_eq!(call(mc, count, &args), Err(Fault::Arity), "one too many for {fixed}");
            if fixed > 0 {
                assert_eq!(call(mc, count, &args[..fixed - 1]), Err(Fault::Arity), "one too few for {fixed}");
            }
        }
        let error = hosting(mc).procedure(mc, None, Arity::Exactly(MAX_FIXED + 1), &[], add).err();
        assert_eq!(error, Some(Error::TooManyParameters));
        assert_eq!(hosting(mc).procedure(mc, None, Arity::AtLeast(MAX_FIXED + 1), &[], add).err(), Some(Error::TooManyParameters));
    });
}

/// A procedure that takes any number of arguments past its fixed ones gets the further arguments as a list.
#[test]
fn further_arguments_arrive_as_a_list() {
    let mut arena = arena();
    arena.mutate(|mc| {
        for fixed in 0..=MAX_FIXED {
            let sum = hosting(mc)
                .procedure(mc, None, Arity::AtLeast(fixed), &[], move |cx, args, _| {
                    if args.len() != fixed + 1 {
                        return Err(Fault::Malformed);
                    }
                    let mut total = 0;
                    for index in 0..fixed {
                        total += number(args.get(index))?;
                    }
                    for further in Pairs::new(cx.mc()).elements(args.get(fixed).ok_or(Fault::Malformed)?) {
                        total += 100 * number(Some(further))?;
                    }
                    Ok(Reply::Value(fixnum(total)))
                })
                .unwrap();
            let args: Vec<Value> = (0..fixed as i64 + 2).map(|_| fixnum(1)).collect();
            assert_eq!(call(mc, sum, &args[..fixed]), Ok(fixnum(fixed as i64)), "no further arguments after {fixed}");
            assert_eq!(call(mc, sum, &args), Ok(fixnum(fixed as i64 + 200)), "two further arguments after {fixed}");
            if fixed > 0 {
                assert_eq!(call(mc, sum, &args[..fixed - 1]), Err(Fault::Arity));
            }
        }
    });
}

/// A closure reads and writes its captures, which are kept in the arena between calls and steps.
#[test]
fn captures_are_kept_in_the_arena() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let text = ragwort_types::string::from_str(&Strings::new(mc), "a text that is an object").unwrap().value();
        let next = hosting(mc)
            .procedure(mc, None, Arity::Exactly(0), &[fixnum(0), text], |cx, _, captures| {
                let mc = cx.mc();
                if captures.len(mc) != 2 || captures.get(mc, 2).is_some() || captures.set(mc, 2, Value::NULL) {
                    return Err(Fault::Malformed);
                }
                let count = number(captures.get(mc, 0))? + 1;
                captures.set(mc, 0, fixnum(count));
                let pair = Pairs::new(mc).cons(fixnum(count), captures.get(mc, 1).ok_or(Fault::Malformed)?)?;
                Ok(Reply::Value(pair.value(mc)))
            })
            .unwrap();
        mc.set_root(2, next);
    });
    for round in 1..=3 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let pair = Pair::of(call(mc, mc.root(2), &[]).unwrap()).unwrap();
            assert_eq!(pair.head(mc), fixnum(round));
            let text = Strings::new(mc).string(pair.tail(mc)).unwrap();
            assert_eq!(ragwort_types::string::to_string(&Strings::new(mc), text), "a text that is an object");
        });
    }
}

/// A procedure and a value that it captures can refer to each other. Both are collected once nothing else holds them, and the Rust closure is dropped.
#[test]
fn a_cycle_through_a_capture_is_collected() {
    let mut arena = arena();
    // The code of an arity is made at its first use and then kept. Use the arity once, so that the count below includes the code.
    arena.mutate(|mc| hosting(mc).procedure(mc, None, Arity::Exactly(0), &[], add).map(|_| ()).unwrap());
    arena.collect();
    arena.collect();
    let before = arena.objects();
    let owned = Rc::new(());
    let held = owned.clone();
    arena.mutate(|mc| {
        let holder = Vectors::new(mc).make(1, Value::FALSE).unwrap();
        let procedure = hosting(mc)
            .procedure(mc, None, Arity::Exactly(0), &[holder.value(mc)], move |cx, _, captures| {
                let _ = &held;
                Ok(Reply::Value(captures.get(cx.mc(), 0).ok_or(Fault::Malformed)?))
            })
            .unwrap();
        // The vector holds the procedure, and the procedure captures the vector.
        holder.items(mc).set(mc, 0, procedure);
        mc.set_root(2, procedure);
        assert_eq!(call(mc, procedure, &[]), Ok(holder.value(mc)));
    });
    arena.collect();
    assert_eq!((arena.objects() > before, Rc::strong_count(&owned)), (true, 2), "{} objects, {before} before", arena.objects());
    arena.mutate(|mc| mc.set_root(2, Value::NULL));
    arena.collect();
    arena.collect();
    assert_eq!((arena.objects(), Rc::strong_count(&owned)), (before, 1));
}

/// A closure can answer with a call to make in its place, or with a value to raise.
#[test]
fn a_closure_can_reply_with_a_call_or_a_raise() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let sum = hosting(mc).procedure(mc, None, Arity::Exactly(2), &[], add).unwrap();
        // Calls its capture with its own argument and 1.
        let forward = hosting(mc)
            .procedure(mc, None, Arity::Exactly(1), &[sum], |cx, args, captures| {
                let mc = cx.mc();
                let list = Pairs::new(mc).list(&[args.get(0).ok_or(Fault::Arity)?, fixnum(1)])?;
                Ok(Reply::Call(captures.get(mc, 0).ok_or(Fault::Malformed)?, list))
            })
            .unwrap();
        assert_eq!(call(mc, forward, &[fixnum(41)]), Ok(fixnum(42)));
        let nested = native(mc, "(%lambda (f) (%intrinsic + 1 (%app f 5)))");
        assert_eq!(call(mc, nested, &[forward]), Ok(fixnum(7)));
        let fail = hosting(mc).procedure(mc, None, Arity::Exactly(1), &[], |_, args, _| Ok(Reply::Raise(args.get(0).ok_or(Fault::Arity)?))).unwrap();
        let mut machine = Machine::new(mc, MIN_SEGMENT, fail, &[fixnum(9)]).unwrap();
        assert_eq!(machine.run(mc), Ok(Outcome::Raised(fixnum(9))));
    });
}

#[test]
fn a_procedure_has_the_name_it_was_made_with() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let name = symbols.intern_str(&Strings::new(mc), "add-two").unwrap();
        let named = hosting(mc).procedure(mc, Some(name), Arity::Exactly(2), &[], add).unwrap();
        let other = symbols.intern_str(&Strings::new(mc), "add-again").unwrap();
        let second = hosting(mc).procedure(mc, Some(other), Arity::Exactly(2), &[], add).unwrap();
        let plain = hosting(mc).procedure(mc, None, Arity::Exactly(2), &[], add).unwrap();
        assert_eq!((procedure_name(mc, named), procedure_name(mc, second), procedure_name(mc, plain)), (Some(name), Some(other), None));
        assert_eq!(call(mc, named, &[fixnum(1), fixnum(2)]), Ok(fixnum(3)));
        assert_eq!(call(mc, named, &[fixnum(1)]), Err(Fault::Arity));
        // A value that is not the support code is refused.
        assert!(Hosting::of(mc, mc.root(0)).is_none() && Hosting::of(mc, Value::NULL).is_none());
    });
}

/// A closure makes another procedure of a closure while it runs.
#[test]
fn a_closure_makes_procedures_while_it_runs() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let support = hosting(mc).value(mc);
        let adder = hosting(mc)
            .procedure(mc, None, Arity::Exactly(1), &[support], |cx, args, captures| {
                let mc = cx.mc();
                let hosting = captures.get(mc, 0).and_then(|value| Hosting::of(mc, value)).ok_or(Fault::Malformed)?;
                let made = hosting.procedure(mc, None, Arity::Exactly(1), &[args.get(0).ok_or(Fault::Arity)?], |cx, args, captures| {
                    Ok(Reply::Value(fixnum(number(captures.get(cx.mc(), 0))? + number(args.get(0))?)))
                });
                Ok(Reply::Value(made.map_err(|_| Fault::OutOfMemory)?))
            })
            .unwrap();
        let add_five = call(mc, adder, &[fixnum(5)]).unwrap();
        assert_eq!(call(mc, add_five, &[fixnum(37)]), Ok(fixnum(42)));
    });
}

/// Setting an arena up makes the module and nothing else. The code of an arity is made at its first use, and every procedure of the arity without a name shares it.
#[test]
fn the_code_of_an_arity_is_made_once() {
    let mut bare = Arena::new(1 << 22, 3);
    bare.mutate(|mc| mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc)));
    bare.collect();
    let mut arena = arena();
    arena.collect();
    // A handful of objects: the module with its name and its list of variable names, and the vector of the codes.
    assert!(arena.objects() <= bare.objects() + 10, "{} objects after the setup, {} without it", arena.objects(), bare.objects());
    arena.mutate(|mc| {
        let symbols = Symbols::of(mc.root(0)).unwrap();
        let name = symbols.intern_str(&Strings::new(mc), "named").unwrap();
        let first = code_of(mc, hosting(mc).procedure(mc, None, Arity::Exactly(2), &[], add).unwrap());
        let second = code_of(mc, hosting(mc).procedure(mc, None, Arity::Exactly(2), &[], add).unwrap());
        let other = code_of(mc, hosting(mc).procedure(mc, None, Arity::AtLeast(2), &[], add).unwrap());
        let named = code_of(mc, hosting(mc).procedure(mc, Some(name), Arity::Exactly(2), &[], add).unwrap());
        assert!(first == second && first != other && first != named);
    });
    // The copy for a name shares the instruction of the arity's code. So one more named procedure adds one frozen value: its Rust closure.
    arena.collect();
    arena.collect();
    let before = arena.frozen_values();
    arena.mutate(|mc| {
        let name = Symbols::of(mc.root(0)).unwrap().intern_str(&Strings::new(mc), "again").unwrap();
        mc.set_root(2, hosting(mc).procedure(mc, Some(name), Arity::Exactly(2), &[], add).unwrap());
    });
    assert_eq!(arena.frozen_values(), before + 1);
}

fn code_of<'gc>(mc: &Mutation<'gc>, procedure: Value<'gc>) -> Gc<'gc, Bytecode> {
    procedure.downcast::<Closure>(mc).unwrap().code(mc).unwrap()
}

