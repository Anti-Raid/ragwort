use std::path::PathBuf;

use super::*;

fn parsed(args: &[&str]) -> Result<Command, String> {
    parse(args.iter().map(|arg| arg.to_string()))
}

fn dir(name: &str, folder: &str) -> ModuleDir {
    ModuleDir { name: name.into(), folder: folder.into() }
}

fn from(modules: Vec<ModuleDir>) -> Source {
    Source { heap: None, image: None, modules }
}

#[test]
fn the_command_line_names_modules_then_an_entry_point() {
    assert_eq!(parsed(&[]), Ok(Command::Run { from: from(vec![]), entry: None }));
    assert_eq!(parsed(&["main.rg"]), Ok(Command::Run { from: from(vec![]), entry: Some(PathBuf::from("main.rg")) }));
    let modules = vec![dir("lib/text", "src/text"), dir("lib/foo", "lib/foo"), dir("up", "../up")];
    let args = ["lib/text=src/text", "=lib/foo/", "up=../up", "bot/main.rgn"];
    assert_eq!(parsed(&args), Ok(Command::Run { from: from(modules.clone()), entry: Some(PathBuf::from("bot/main.rgn")) }));
    assert_eq!(parsed(&args[..3]), Ok(Command::Run { from: from(modules.clone()), entry: None }));
    assert_eq!(parsed(&["compile", "lib/text=src/text", "=lib/foo/", "up=../up"]), Ok(Command::Compile { from: from(modules), entry: None }));
    assert_eq!(parsed(&["compile", "main.rg"]), Ok(Command::Compile { from: from(vec![]), entry: Some(PathBuf::from("main.rg")) }));
    assert_eq!(parsed(&["--help"]), Ok(Command::Help));
    assert_eq!(parsed(&["a=b", "-h"]), Ok(Command::Help));
}

#[test]
fn the_command_line_names_images() {
    let core = Source { heap: None, image: Some(PathBuf::from("core.img")), modules: vec![] };
    assert_eq!(parsed(&["--image", "core.img", "bot.rg"]), Ok(Command::Run { from: core.clone(), entry: Some(PathBuf::from("bot.rg")) }));
    assert_eq!(parsed(&["--image", "core.img"]), Ok(Command::Run { from: core.clone(), entry: None }));
    assert_eq!(parsed(&["compile", "--image", "core.img", "bot.rg"]), Ok(Command::Compile { from: core, entry: Some(PathBuf::from("bot.rg")) }));
    let saved = Command::Save { from: from(vec![dir("core", "lib/core")]), to: PathBuf::from("core.img") };
    assert_eq!(parsed(&["compile", "-o", "core.img", "core=lib/core"]), Ok(saved.clone()));
    assert_eq!(parsed(&["compile", "core=lib/core", "-o", "core.img"]), Ok(saved));
    let more = Source { heap: None, image: Some(PathBuf::from("core.img")), modules: vec![dir("extra", "lib/extra")] };
    assert_eq!(parsed(&["compile", "--image", "core.img", "-o", "more.img", "extra=lib/extra"]), Ok(Command::Save { from: more, to: PathBuf::from("more.img") }));
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
        (&["--image"], "needs a file"),
        (&["compile", "a=b", "-o"], "needs a file"),
        (&["--image", "a.img", "--image", "b.img"], "given twice"),
        (&["-o", "a.img", "a=b"], "goes with `compile`"),
        (&["compile", "-o", "a.img"], "needs a module"),
        (&["compile", "-o", "a.img", "a=b", "main.rg"], "give the entry point when you run it"),
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

#[test]
fn the_command_line_sets_the_memory_limit() {
    let limited = |heap: usize| Source { heap: Some(heap), image: None, modules: vec![] };
    assert_eq!(parsed(&["--heap", "16m", "bot.rg"]), Ok(Command::Run { from: limited(16 << 20), entry: Some(PathBuf::from("bot.rg")) }));
    assert_eq!(parsed(&["--heap", "512K"]), Ok(Command::Run { from: limited(512 << 10), entry: None }));
    assert_eq!(parsed(&["compile", "--heap", "1g", "main.rg"]), Ok(Command::Compile { from: limited(1 << 30), entry: Some(PathBuf::from("main.rg")) }));
    assert_eq!(parsed(&["--heap", "4096"]), Ok(Command::Run { from: limited(4096), entry: None }));
    for wrong in ["", "m", "0", "0m", "-1", "1.5m", "16mb", "+3", "99999999999999999999", "18446744073709551615k"] {
        assert_eq!(parsed(&["--heap", wrong]), Err(format!("`{wrong}` is not a size such as `16m`")));
    }
    assert_eq!(parsed(&["--heap"]), Err("`--heap` needs a size".to_string()));
    assert_eq!(parsed(&["--heap", "1m", "--heap", "2m"]), Err("`--heap` is given twice".to_string()));
}
