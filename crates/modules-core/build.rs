//! Sets the `RAGWORT_BUILD` environment variable for the crate. It is a stamp that identifies this build of ragwort: a
//! hash of the source of every ragwort crate, the crate version and the target's pointer width.
//!
//! The stamp does not name the target. An image is written in a fixed format, with every number in little-endian order at a fixed width, so
//! builds of one source for two targets read each other's images. A program built for one machine can include an image that a build script made on another.
//! The pointer width is in the stamp because no 32-bit build has been tried.
//!
//! An image is valid only for the build that made it. A change to the source can alter what
//! an image means without altering the shape of the saved data. Examples are an intrinsic that changes its
//! behaviour, and two fields of an object that swap places. So any change to the source
//! produces a different stamp.
//!
//! The hashed crates are the ones under `crates` in the workspace that contains this crate. When this crate is built
//! outside a workspace, the hash covers only this crate's own source and its version.

use std::path::{Path, PathBuf};

/// Names of folders that are skipped, because they hold no source that goes into a build.
const SKIPPED: [&str; 4] = ["target", "tests", "examples", "benches"];

fn hash(sum: &mut u64, bytes: &[u8]) {
    for &byte in bytes {
        *sum = (*sum ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01B3);
    }
    // Mix in a terminator after each input. Then `ab` followed by `c` does not hash like `a` followed by `bc`.
    *sum = (*sum ^ 0xFF).wrapping_mul(0x0000_0100_0000_01B3);
}

/// Adds the source files under `folder` to `files`. A source file is a `Cargo.toml` or a file that ends in `.rs`, `.rg` or `.rgn`.
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
        } else if name == "Cargo.toml" || ["rs", "rg", "rgn"].iter().any(|ext| path.extension().is_some_and(|found| found == *ext)) {
            files.push(path);
        }
    }
}

/// Returns the root folder of the workspace that contains the crate folder `manifest`, or `None` if the crate is in no workspace.
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
    for name in ["CARGO_PKG_VERSION", "CARGO_CFG_TARGET_POINTER_WIDTH"] {
        hash(&mut sum, std::env::var(name).unwrap_or_default().as_bytes());
    }
    for file in &files {
        hash(&mut sum, file.strip_prefix(&root).unwrap_or(file).to_string_lossy().as_bytes());
        hash(&mut sum, &std::fs::read(file).unwrap_or_default());
    }
    println!("cargo:rustc-env=RAGWORT_BUILD={sum:016x}");
    println!("cargo:rerun-if-changed={}", root.display());
}
