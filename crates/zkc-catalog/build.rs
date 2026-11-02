#[path = "codegen/projection.rs"]
mod projection;

use std::{env, fs, path::PathBuf};

fn main() {
    // The native installation document is interpreted only together with the
    // declaration document it references; both are inputs of one build.
    let declarations = PathBuf::from("../../common/catalog/declarations.json");
    let installation = PathBuf::from("../../common/catalog/installation.json");
    for source in [&declarations, &installation] {
        println!("cargo::rerun-if-changed={}", source.display());
    }
    for generator in [
        "projection",
        "validation",
        "instances",
        "installation",
        "installed",
    ] {
        println!("cargo::rerun-if-changed=codegen/{generator}.rs");
    }
    let read = |source: &PathBuf| {
        fs::read(source).unwrap_or_else(|error| panic!("read {}: {error}", source.display()))
    };
    let code =
        projection::generate(&read(&declarations), &read(&installation)).unwrap_or_else(|error| {
            panic!(
                "{} with {}: {error}",
                declarations.display(),
                installation.display()
            );
        });
    fs::write(
        PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("catalog.rs"),
        code,
    )
    .expect("write Rust declaration projection");
}
