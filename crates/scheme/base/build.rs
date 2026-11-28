//! Finds the libraries of the Scheme language in the crate's `prelude` folder, and generates the code that lists them.
//!
//! # The folder
//!
//! Each `.rgn` file of the folder is one library, written in native ragwort. The library's name is `scheme/` followed by the file's
//! name: `number.rgn` is the library `scheme/number`. A file with another extension is ignored.
//!
//! To add a library, add a file. No other code names the libraries one by one. Cargo runs this script again when the folder changes.
//!
//! # What the script generates
//!
//! The script writes the file `prelude.rs` to the build's output folder, and `src/lib.rs` includes it. For a folder that holds
//! `list.rgn` and `number.rgn`, the file reads:
//!
//! ```text
//! pub const LIBRARIES: [(&str, &str); 2] = [
//!     ("scheme/list", include_str!("/path/to/prelude/list.rgn")),
//!     ("scheme/number", include_str!("/path/to/prelude/number.rgn")),
//! ];
//!
//! pub const SCHEME: (&str, &str) = ("scheme", "(%require scheme/list scheme/number)\n(%provide (all-from-out scheme/list scheme/number))\n");
//!
//! pub const PROVIDED: [(&str, &str); 3] = [
//!     ("+", "scheme/number"),
//!     ("car", "scheme/list"),
//!     ("cdr", "scheme/list"),
//! ];
//! ```
//!
//! - `LIBRARIES` is the name and the source of each library, ordered by name. `include_str!` reads the source when the crate is compiled.
//! - `SCHEME` is the name and the source of the `scheme` module. It requires every library and passes on all that they provide. So it
//!   always covers every file of the folder.
//! - `PROVIDED` is each name that a library provides, with the library's name. It is ordered by name, so a name can be found with a
//!   binary search. The crate uses it to say which library an unbound name is in.
//!
//! # What a library provides
//!
//! The script does not parse a library. It takes a line that starts with `(%define name` as a definition that the library provides.
//! That is right for a library that follows two rules:
//!
//! - It provides every variable that it defines, with `(%provide (all-var-defined-out))`.
//! - Each of its definitions starts at the beginning of a line.
//!
//! A test of the `ragwort-modules-core` crate checks `PROVIDED` against what the built libraries export.

use std::fmt::Write;
use std::path::PathBuf;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("cargo says where the crate is"));
    let folder = manifest.join("prelude");
    // A change to the folder, such as a new file, runs the script again.
    println!("cargo:rerun-if-changed={}", folder.display());
    let mut files: Vec<PathBuf> = Vec::new();
    for entry in std::fs::read_dir(&folder).expect("the prelude folder") {
        let path = entry.expect("an entry of the prelude folder").path();
        if path.extension().is_some_and(|extension| extension == "rgn") {
            files.push(path);
        }
    }
    // The order in which a folder lists its files differs between systems. Sorting gives every build the same order.
    files.sort();
    // The names of the libraries, in order.
    let mut names = Vec::with_capacity(files.len());
    // Each name that a library defines, with the library's name.
    let mut provided: Vec<(String, String)> = Vec::new();
    // The text of `prelude.rs`.
    let mut generated = String::new();
    writeln!(generated, "/// The libraries of the Scheme language: the name of each, and its source in native ragwort. They hold the procedures of the language, and they are").expect("a line");
    writeln!(generated, "/// the files of the crate's `prelude` folder. No library requires another, so they can be built in any order.").expect("a line");
    writeln!(generated, "pub const LIBRARIES: [(&str, &str); {}] = [", files.len()).expect("a line");
    for file in &files {
        let stem = file.file_stem().expect("a file name").to_str().expect("a file name in UTF-8");
        let name = format!("scheme/{stem}");
        // The path is absolute, because `include_str!` would read a relative path from the output folder.
        writeln!(generated, "    ({name:?}, include_str!({:?})),", file.to_str().expect("a path in UTF-8")).expect("a line");
        let text = std::fs::read_to_string(file).expect("a library's source");
        for line in text.lines() {
            // The name ends at the first space. The rest of the line is the start of the definition's value.
            if let Some(defined) = line.strip_prefix("(%define ").and_then(|rest| rest.split_whitespace().next()) {
                provided.push((defined.to_string(), name.clone()));
            }
        }
        names.push(name);
    }
    writeln!(generated, "];").expect("a line");
    // The `scheme` module names every library twice: once to require it, and once to pass on what it provides.
    let all = names.join(" ");
    let source = format!("; scheme: every library of the Scheme language. A module that requires it gets the bindings of them all.\n\n(%require {all})\n(%provide (all-from-out {all}))\n");
    writeln!(generated).expect("a line");
    writeln!(generated, "/// The module that passes on every library of [`LIBRARIES`]: its name, and its source in native ragwort. A module that requires it gets every procedure of the language.").expect("a line");
    writeln!(generated, "pub const SCHEME: (&str, &str) = (\"scheme\", {source:?});").expect("a line");
    // Sorted by name, then by library, for the binary search of `library_of`.
    provided.sort();
    writeln!(generated).expect("a line");
    writeln!(generated, "/// Each name that a library of [`LIBRARIES`] provides, with the library's name, ordered by name. See [`library_of`].").expect("a line");
    writeln!(generated, "pub const PROVIDED: [(&str, &str); {}] = [", provided.len()).expect("a line");
    for (defined, library) in &provided {
        writeln!(generated, "    ({defined:?}, {library:?}),").expect("a line");
    }
    writeln!(generated, "];").expect("a line");
    let out = PathBuf::from(std::env::var("OUT_DIR").expect("cargo says where the output goes"));
    std::fs::write(out.join("prelude.rs"), generated).expect("the generated list of libraries");
}
