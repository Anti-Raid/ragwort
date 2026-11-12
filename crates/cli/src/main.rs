//! The `ragwort` command: runs a file, opens a REPL, or compiles and prints bytecode. See
//! [`args`] for the command line.

mod args;
mod hosts;
mod listing;
mod program;
mod repl;

use std::process::ExitCode;

use crate::args::{Command, ModuleDir, USAGE};
use crate::hosts::{flush, put};
use crate::program::Program;

/// Writes each of `errors` to the standard error, after what's been written so far.
fn fail(errors: &[String]) -> ExitCode {
    flush();
    errors.iter().for_each(|error| eprintln!("{error}"));
    ExitCode::FAILURE
}

fn finish(result: Result<(), Vec<String>>) -> ExitCode {
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(errors) => fail(&errors),
    }
}

fn compile(modules: Vec<ModuleDir>, entry: Option<std::path::PathBuf>) -> ExitCode {
    let mut program = match Program::new(modules) {
        Ok(program) => program,
        Err(errors) => return fail(&errors),
    };
    program.list();
    let mut result = program.load_all();
    if result.is_ok()
        && let Some(entry) = entry
    {
        result = program.run_file(&entry, false);
    }
    put(&program.take_listing());
    finish(result)
}

fn main() -> ExitCode {
    let command = match args::parse(std::env::args().skip(1)) {
        Ok(command) => command,
        Err(message) => {
            eprintln!("ragwort: {message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            put(USAGE);
            ExitCode::SUCCESS
        }
        Command::Compile { modules, entry } => compile(modules, entry),
        Command::Run { modules, entry } => {
            let mut program = match Program::new(modules) {
                Ok(program) => program,
                Err(errors) => return fail(&errors),
            };
            match entry {
                Some(entry) => finish(program.run_file(&entry, true)),
                None => repl::run(&mut program),
            }
        }
    }
}
