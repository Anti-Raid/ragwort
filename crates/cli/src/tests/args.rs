use std::path::PathBuf;

use super::*;

fn parsed(args: &[&str]) -> Result<Command, String> {
    parse(args.iter().map(|arg| arg.to_string()))
}

fn dir(name: &str, folder: &str) -> ModuleDir {
    ModuleDir { name: name.into(), folder: folder.into() }
}

#[test]
fn the_command_line_names_modules_then_an_entry_point() {
    assert_eq!(parsed(&[]), Ok(Command::Run { modules: vec![], entry: None }));
    assert_eq!(parsed(&["main.rg"]), Ok(Command::Run { modules: vec![], entry: Some(PathBuf::from("main.rg")) }));
    let modules = vec![dir("lib/text", "src/text"), dir("lib/foo", "lib/foo"), dir("up", "../up")];
    let args = ["lib/text=src/text", "=lib/foo/", "up=../up", "bot/main.rgn"];
    assert_eq!(parsed(&args), Ok(Command::Run { modules: modules.clone(), entry: Some(PathBuf::from("bot/main.rgn")) }));
    assert_eq!(parsed(&args[..3]), Ok(Command::Run { modules: modules.clone(), entry: None }));
    assert_eq!(parsed(&["compile", "lib/text=src/text", "=lib/foo/", "up=../up"]), Ok(Command::Compile { modules, entry: None }));
    assert_eq!(parsed(&["compile", "main.rg"]), Ok(Command::Compile { modules: vec![], entry: Some(PathBuf::from("main.rg")) }));
    assert_eq!(parsed(&["--help"]), Ok(Command::Help));
    assert_eq!(parsed(&["a=b", "-h"]), Ok(Command::Help));
}

#[test]
fn a_command_line_that_is_wrong_says_how() {
    for (args, part) in [
        (&["compile"][..], "needs a module or an entry point"),
        (&["main.rg", "a=b"], "after the entry point"),
        (&["main.rg", "other.rg"], "after the entry point"),
        (&["main.txt"], "neither"),
        (&["main"], "neither"),
        (&["a="], "names no folder"),
        (&["a=b", "a=c"], "given twice"),
        (&["=b", "b=c"], "given twice"),
        (&["--fast"], "unknown option"),
    ] {
        let error = parsed(args).unwrap_err();
        assert!(error.contains(part), "{args:?}: {error}");
    }
}

#[test]
fn a_file_is_in_the_language_of_its_extension() {
    assert_eq!(language(Path::new("a/main.rg")), Some(Language::Scheme));
    assert_eq!(language(Path::new("main.rgn")), Some(Language::Native));
    assert_eq!(language(Path::new("notes.md")), None);
    assert_eq!(language(Path::new("rg")), None);
}
