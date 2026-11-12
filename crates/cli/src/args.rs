//! The command line.
//!
//! ```text
//! ragwort [name=folder]... entry.rg            runs entry.rg
//! ragwort [name=folder]...                     opens a REPL
//! ragwort compile [name=folder]... [entry.rg]  compiles, and prints the bytecode
//! ```
//!
//! # Modules
//!
//! `name=folder` makes the files in `folder` the module `name`, which code requires by that
//! name. `ragwort lib/text=src/text main.rg` lets `main.rg` say `(require lib/text)`.
//!
//! - The name can be left out: `=lib/text` is `lib/text=lib/text`.
//! - A file ending in `.rg` is Scheme, one ending in `.rgn` is native ragwort, and other files
//!   are left alone. The files of a folder are one module, read in the order of their names.

#[cfg(test)]
#[path = "tests/args.rs"]
mod tests;

use std::path::{Path, PathBuf};

use ragwort_modules_core::Language;

pub const USAGE: &str = "\
usage:
  ragwort [name=folder]... entry.rg            run entry.rg
  ragwort [name=folder]...                     open a REPL
  ragwort compile [name=folder]... [entry.rg]  compile, and print the bytecode

  name=folder   the files in folder are the module `name`; `=folder` names it as the folder
  .rg files are Scheme, .rgn files are native ragwort
";

/// A module the command line names: its files are the ones in `folder`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleDir {
    pub name: String,
    pub folder: PathBuf,
}

/// What the command line asks for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    Help,
    /// Runs `entry`, or opens a REPL if there's none.
    Run { modules: Vec<ModuleDir>, entry: Option<PathBuf> },
    /// Compiles the modules and `entry`, and prints their bytecode.
    Compile { modules: Vec<ModuleDir>, entry: Option<PathBuf> },
}

/// The language of the file at `path`, by its extension, if it's a source file.
pub fn language(path: &Path) -> Option<Language> {
    match path.extension()?.to_str()? {
        "rg" => Some(Language::Scheme),
        "rgn" => Some(Language::Native),
        _ => None,
    }
}

/// What `args`, the arguments after the program's name, ask for, or what's wrong with them.
pub fn parse(args: impl IntoIterator<Item = String>) -> Result<Command, String> {
    let mut args = args.into_iter().peekable();
    let compile = args.next_if(|arg| arg == "compile").is_some();
    let mut modules: Vec<ModuleDir> = Vec::new();
    let mut entry = None;
    for arg in args {
        if arg == "-h" || arg == "--help" {
            return Ok(Command::Help);
        }
        if arg.starts_with('-') {
            return Err(format!("unknown option `{arg}`"));
        }
        if entry.is_some() {
            return Err(format!("`{arg}` comes after the entry point, which is last"));
        }
        let Some((name, folder)) = arg.split_once('=') else {
            if language(Path::new(&arg)).is_none() {
                return Err(format!("`{arg}` is neither `name=folder` nor a `.rg` or `.rgn` file"));
            }
            entry = Some(PathBuf::from(arg));
            continue;
        };
        if folder.is_empty() {
            return Err(format!("`{arg}` names no folder"));
        }
        let name = if name.is_empty() { folder.trim_end_matches('/') } else { name };
        if modules.iter().any(|module| module.name == name) {
            return Err(format!("the module `{name}` is given twice"));
        }
        modules.push(ModuleDir { name: name.to_string(), folder: PathBuf::from(folder) });
    }
    if !compile {
        return Ok(Command::Run { modules, entry });
    }
    if modules.is_empty() && entry.is_none() {
        return Err("`compile` needs a module or an entry point".to_string());
    }
    Ok(Command::Compile { modules, entry })
}
