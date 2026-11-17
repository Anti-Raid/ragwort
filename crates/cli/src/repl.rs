//! The REPL. It reads input until the input is complete, runs it, and writes the value of each form.

use std::io::{BufRead, IsTerminal};
use std::process::ExitCode;

use crate::hosts::{flush, put};
use crate::program::Program;

/// Reads the standard input and runs it one input at a time, until the standard input ends. Prompts are shown if the standard input
/// is a terminal.
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
            Err(error) => {
                eprintln!("{error}");
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
