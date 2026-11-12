//! The REPL: reads what's typed until it's whole, runs it, and writes each form's value.

use std::io::{BufRead, IsTerminal};
use std::process::ExitCode;

use crate::hosts::{flush, put};
use crate::program::Program;

/// Runs what the standard input has, an input at a time, till it ends. It prompts if a person
/// is typing.
pub fn run(program: &mut Program) -> ExitCode {
    let stdin = std::io::stdin();
    let prompts = stdin.is_terminal();
    let mut pending = String::new();
    loop {
        if prompts {
            put(if pending.is_empty() { "> " } else { "  " });
            flush();
        }
        let mut line = String::new();
        let ended = match stdin.lock().read_line(&mut line) {
            Ok(read) => read == 0,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        pending.push_str(&line);
        if !ended && program.unfinished(&pending) {
            continue;
        }
        if !pending.trim().is_empty()
            && let Err(errors) = program.eval(&pending, &mut |text| put(&format!("{text}\n")))
        {
            flush();
            errors.iter().for_each(|error| eprintln!("{error}"));
        }
        pending.clear();
        if ended {
            break;
        }
    }
    if prompts {
        put("\n");
    }
    ExitCode::SUCCESS
}
