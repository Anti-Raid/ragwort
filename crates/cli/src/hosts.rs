//! The `repl` module: `display`, `write` and `newline`, which write to the standard output.
//!
//! It's written in native ragwort, over a host function for each: see `repl.rgn`. Any module
//! the command line loads gets them with `(require repl)`, and what's typed at the REPL has
//! them without.

use std::io::Write;

use ragwort_printer_scheme::{Mode, PrintError, to_string};
use ragwort_types::gc::Value;
use ragwort_vm::{Fault, HostArgs, HostContext, HostDef, Purity, Reply, host};

pub const NAME: &str = "repl";
pub const SOURCE: &str = include_str!("repl.rgn");

pub static HOSTS: [HostDef; 3] = [
    host!("display", 1, Purity::Impure, display),
    host!("write", 1, Purity::Impure, write),
    host!("newline", 0, Purity::Impure, newline),
];

/// The most characters one `display` or `write` writes.
const LIMIT: usize = 1 << 24;

/// Writes `text` to the standard output. What can't be written, as to a closed pipe, is dropped.
pub fn put(text: &str) {
    let _ = std::io::stdout().lock().write_all(text.as_bytes());
}

/// Writes out what [`put`] has kept back, as it does text with no newline after it.
pub fn flush() {
    let _ = std::io::stdout().lock().flush();
}

fn show<'gc>(cx: &mut HostContext<'_, 'gc>, args: HostArgs<'_, 'gc>, mode: Mode) -> Result<Reply<'gc>, Fault> {
    let value = args.get(0).ok_or(Fault::Arity)?;
    let text = to_string(cx.mc(), value, mode, LIMIT).map_err(|error| match error {
        PrintError::TooLong => Fault::OutOfRange,
        PrintError::Arena(_) => Fault::OutOfMemory,
    })?;
    cx.charge(text.len() as u64)?;
    put(&text);
    Ok(Reply::Value(Value::VOID))
}

fn display<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    show(cx, args, Mode::Display)
}

fn write<'s, 'gc>(cx: &mut HostContext<'s, 'gc>, args: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    show(cx, args, Mode::Write)
}

fn newline<'s, 'gc>(_: &mut HostContext<'s, 'gc>, _: HostArgs<'s, 'gc>) -> Result<Reply<'gc>, Fault> {
    put("\n");
    Ok(Reply::Value(Value::VOID))
}
