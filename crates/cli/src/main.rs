//! The `ragwort` command: runs a file, opens a REPL, compiles and prints bytecode, or saves
//! compiled modules as an image. See [`args`] for the command line.

mod args;
mod hosts;
mod listing;
mod program;
mod repl;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::args::{Command, Source, USAGE};
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

/// The program `from` describes: one that starts from its image, if it has one.
fn program(from: Source) -> Result<Program, Vec<String>> {
    let Some(image) = from.image else { return Program::new(from.modules) };
    let bytes = std::fs::read(&image).map_err(|e| vec![format!("{}: {e}", image.display())])?;
    Program::from_image(from.modules, &bytes).map_err(|errors| errors.iter().map(|error| format!("{}: {error}", image.display())).collect())
}

/// Compiles the modules of `program` and `entry`, and writes their bytecode.
fn compile(mut program: Program, entry: Option<PathBuf>) -> ExitCode {
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

/// Compiles the modules of `program`, and saves it to the file at `to`.
fn save(mut program: Program, to: &Path) -> ExitCode {
    let saved = program.load_all().and_then(|()| program.save_image());
    finish(saved.and_then(|bytes| std::fs::write(to, bytes).map_err(|e| vec![format!("{}: {e}", to.display())])))
}

fn main() -> ExitCode {
    let command = match args::parse(std::env::args().skip(1)) {
        Ok(command) => command,
        Err(message) => {
            eprintln!("ragwort: {message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let (from, then): (Source, Box<dyn FnOnce(Program) -> ExitCode>) = match command {
        Command::Help => {
            put(USAGE);
            return ExitCode::SUCCESS;
        }
        Command::Compile { from, entry } => (from, Box::new(|program| compile(program, entry))),
        Command::Save { from, to } => (from, Box::new(move |program| save(program, &to))),
        Command::Run { from, entry: Some(entry) } => (from, Box::new(move |mut program| finish(program.run_file(&entry, true)))),
        Command::Run { from, entry: None } => (from, Box::new(|mut program| repl::run(&mut program))),
    };
    match program(from) {
        Ok(program) => then(program),
        Err(errors) => fail(&errors),
    }
}
