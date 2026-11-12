//! Gives the crate `RAGWORT_BUILD`, which tells this build of ragwort from any other: a
//! number made of the source of every ragwort crate, and what the build is for.
//!
//! An image is only good for the build that made it, and what a change to the source does to
//! an image's meaning can't be seen in the shape of what's saved: an intrinsic that does
//! something else, or two fields of an object that change places. So any change to the source
//! makes another build.
//!
//! The crates are the ones in the workspace this crate is in. Built on its own, it's this
//! crate alone, with its version.

use std::path::{Path, PathBuf};

/// The folders that hold nothing a build is made of.
const SKIPPED: [&str; 4] = ["target", "tests", "examples", "benches"];

fn hash(sum: &mut u64, bytes: &[u8]) {
    for &byte in bytes {
        *sum = (*sum ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01B3);
    }
    // What ends here isn't the start of what's next.
    *sum = (*sum ^ 0xFF).wrapping_mul(0x0000_0100_0000_01B3);
}

/// The source files under `folder`, added to `files`.
fn sources(folder: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(folder) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if !SKIPPED.contains(&&*name) && !name.starts_with('.') {
                sources(&path, files);
            }
        } else if name == "Cargo.toml" || ["rs", "rg", "rgn"].iter().any(|ext| path.extension().is_some_and(|e| e == *ext)) {
            files.push(path);
        }
    }
}

/// The folder of the workspace `manifest` is in, if it's in one.
fn workspace(manifest: &Path) -> Option<&Path> {
    manifest.ancestors().skip(1).find(|folder| std::fs::read_to_string(folder.join("Cargo.toml")).is_ok_and(|text| text.contains("[workspace]")))
}

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("cargo says where the crate is"));
    let root = match workspace(&manifest) {
        Some(workspace) => workspace.join("crates"),
        None => manifest.clone(),
    };
    let mut files = Vec::new();
    sources(&root, &mut files);
    files.sort();
    let mut sum = 0xCBF2_9CE4_8422_2325u64;
    for name in ["CARGO_PKG_VERSION", "TARGET"] {
        hash(&mut sum, std::env::var(name).unwrap_or_default().as_bytes());
    }
    for file in &files {
        hash(&mut sum, file.strip_prefix(&root).unwrap_or(file).to_string_lossy().as_bytes());
        hash(&mut sum, &std::fs::read(file).unwrap_or_default());
    }
    println!("cargo:rustc-env=RAGWORT_BUILD={sum:016x}");
    println!("cargo:rerun-if-changed={}", root.display());
}
