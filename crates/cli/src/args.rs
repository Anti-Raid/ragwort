//! The command line.
//!
//! ```text
//! ragwort [name=folder]... entry.rg            runs entry.rg
//! ragwort [name=folder]...                     opens a REPL
//! ragwort compile [name=folder]... [entry.rg]  compiles, and prints the bytecode
//! ragwort compile -o file [name=folder]...     compiles, and saves an image
//! ```
//!
//! # Images
//!
//! `compile -o core.img core=lib/core` compiles and runs the modules it names and saves them
//! to `core.img`. `--image core.img`, with any of the commands, starts from what the image
//! holds, so `ragwort --image core.img bot.rg` runs `bot.rg` without compiling `core` again.
//!
//! - A module in an image has run already. It isn't run again when the image is loaded, so
//!   what it does as it runs, such as writing a line, happens once, when the image is made.
//! - `compile --image core.img -o more.img extra=lib/extra` makes an image of both.
//! - An image is for the build of `ragwort` that made it.
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
  ragwort compile -o file [name=folder]...     compile, and save the modules as an image

  name=folder   the files in folder are the module `name`; `=folder` names it as the folder
  --image file  start from the modules an image holds
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
    Run { from: Source, entry: Option<PathBuf> },
    /// Compiles the modules and `entry`, and prints their bytecode.
    Compile { from: Source, entry: Option<PathBuf> },
    /// Compiles the modules, and saves them to the file as an image.
    Save { from: Source, to: PathBuf },
}

/// Where a command's modules are from: an image, if it starts from one, and folders.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Source {
    pub image: Option<PathBuf>,
    pub modules: Vec<ModuleDir>,
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
    let (mut entry, mut image, mut output) = (None, None, None);
    while let Some(arg) = args.next() {
        if arg == "-h" || arg == "--help" {
            return Ok(Command::Help);
        }
        if arg == "--image" || arg == "-o" {
            let file = if arg == "-o" { &mut output } else { &mut image };
            if file.is_some() {
                return Err(format!("`{arg}` is given twice"));
            }
            *file = Some(PathBuf::from(args.next().ok_or_else(|| format!("`{arg}` needs a file"))?));
            continue;
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
    let from = Source { image, modules };
    match (compile, output) {
        (false, Some(_)) => Err("`-o` goes with `compile`".to_string()),
        (false, None) => Ok(Command::Run { from, entry }),
        (true, _) if from.modules.is_empty() && entry.is_none() => Err("`compile` needs a module or an entry point".to_string()),
        (true, Some(_)) if entry.is_some() => Err("an image holds modules, which have run: give the entry point when you run it".to_string()),
        (true, Some(to)) => Ok(Command::Save { from, to }),
        (true, None) => Ok(Command::Compile { from, entry }),
    }
}
