//! Builds the libraries of Scheme and saves them as the image `scheme.img` in the build's output folder. The crate includes the image.
//!
//! # What the script does
//!
//! - It compiles the libraries and the `scheme` module from their source, in an arena of its own.
//! - It runs them. A module must have run before code can require it.
//! - It collects, so the image holds no dead object.
//! - It saves the symbol table, then each module in the order of `ragwort_modules_core::Scheme::modules`. The crate's `load` reads them in
//!   that order.
//!
//! # The machine that runs the script
//!
//! The script runs on the machine that builds the program, which can be another kind of machine than the program is for. The image loads
//! all the same, unless the two differ in pointer width. See `ragwort_modules_core::image::stamp`.

use std::path::PathBuf;

use ragwort_modules_core::{image, scheme};
use ragwort_types::gc::{Arena, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::vector::{Vector, Vectors};
use ragwort_vm::{Machine, Outcome, SEGMENT};

/// The roots of the arena: the symbol table, a vector of the modules, and a vector of the thunks that have not run.
const SYMBOLS: usize = 0;
const MODULES: usize = 1;
const THUNKS: usize = 2;
const ROOTS: usize = 3;

/// The memory limit of the arena, in bytes.
const LIMIT: usize = 64 << 20;

/// Runs the thunks in the `THUNKS` root in order, one step of the arena at a time. One machine runs them all, because a machine has a stack of its own.
fn run(arena: &mut Arena, thunks: usize) {
    let mut machine: Option<Machine> = None;
    for index in 0..thunks {
        let earlier = machine.take();
        let mut running = arena.mutate(|mc| {
            let thunk = Vector::of(mc.root(THUNKS)).expect("the thunks").items(mc).get(index);
            match earlier {
                Some(mut earlier) => {
                    earlier.restart(mc, thunk, &[]).expect("a machine that finished restarts");
                    earlier
                }
                None => Machine::new(mc, SEGMENT, thunk, &[]).expect("room for a machine"),
            }
        });
        loop {
            let step = arena.step(|mc| match running.run(mc).expect("a library of Scheme runs") {
                Outcome::Paused => false,
                Outcome::Done(_) => true,
                _ => panic!("a library of Scheme did not run to its end"),
            });
            if step.expect("room to run the libraries of Scheme") {
                break;
            }
        }
        machine = Some(running);
    }
}

fn main() {
    let mut arena = Arena::new(LIMIT, ROOTS);
    let thunks = arena.mutate(|mc| {
        let symbols = Symbols::of_arena(mc).expect("room for the symbol table");
        let built = scheme(mc, symbols).expect("the libraries of Scheme compile");
        let mut modules = Vec::with_capacity(built.modules.len());
        for &(_, module) in &built.modules {
            modules.push(Value::object(mc, module));
        }
        let vectors = Vectors::new(mc);
        mc.set_root(SYMBOLS, symbols.value(mc));
        mc.set_root(MODULES, vectors.from_slice(&modules).expect("room for the modules").value(mc));
        mc.set_root(THUNKS, vectors.from_slice(&built.thunks).expect("room for the thunks").value(mc));
        built.thunks.len()
    });
    run(&mut arena, thunks);
    arena.mutate(|mc| mc.set_root(THUNKS, Value::NULL));
    arena.collect();
    let bytes = arena.mutate(|mc| {
        let modules = Vector::of(mc.root(MODULES)).expect("the modules").items(mc);
        let mut roots = Vec::with_capacity(modules.len() + 1);
        roots.push(mc.root(SYMBOLS));
        for index in 0..modules.len() {
            roots.push(modules.get(index));
        }
        image::save(mc, &roots).expect("an image holds the libraries of Scheme")
    });
    let out = PathBuf::from(std::env::var("OUT_DIR").expect("cargo says where the output goes"));
    std::fs::write(out.join("scheme.img"), bytes).expect("the image of the libraries");
    println!("cargo:rerun-if-changed=build.rs");
}
