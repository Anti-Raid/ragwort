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

/// Flushes the standard output, then writes each of `errors` to the standard error. Returns the failure exit code.
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

/// Creates the program that `from` describes. The program starts from the image if `from` names one.
fn program(from: Source) -> Result<Program, Vec<String>> {
    let heap = from.heap.unwrap_or(program::HEAP);
    let Some(image) = from.image else { return Program::new(heap, from.modules) };
    let bytes = std::fs::read(&image).map_err(|error| vec![format!("{}: {error}", image.display())])?;
    Program::from_image(heap, from.modules, &bytes).map_err(|errors| errors.iter().map(|error| format!("{}: {error}", image.display())).collect())
}

/// Compiles the modules of `program` and the file `entry`, and writes their bytecode to the standard output.
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

/// Compiles and runs the modules of `program`, and saves them as an image in the file at `to`.
fn save(mut program: Program, to: &Path) -> ExitCode {
    let saved = program.load_all().and_then(|()| program.save_image());
    finish(saved.and_then(|bytes| std::fs::write(to, bytes).map_err(|error| vec![format!("{}: {error}", to.display())])))
}

/// The action that a command performs on its program, once the program is created.
enum Task {
    Compile(Option<PathBuf>),
    Save(PathBuf),
    Run(Option<PathBuf>),
}

fn main() -> ExitCode {
    let command = match args::parse(std::env::args().skip(1)) {
        Ok(command) => command,
        Err(message) => {
            eprintln!("ragwort: {message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let (from, task) = match command {
        Command::Help => {
            put(USAGE);
            return ExitCode::SUCCESS;
        }
        Command::Compile { from, entry } => (from, Task::Compile(entry)),
        Command::Save { from, to } => (from, Task::Save(to)),
        Command::Run { from, entry } => (from, Task::Run(entry)),
    };
    let mut program = match program(from) {
        Ok(program) => program,
        Err(errors) => return fail(&errors),
    };
    match task {
        Task::Compile(entry) => compile(program, entry),
        Task::Save(to) => save(program, &to),
        Task::Run(Some(entry)) => finish(program.run_file(&entry, true)),
        Task::Run(None) => repl::run(&mut program),
    }
}
