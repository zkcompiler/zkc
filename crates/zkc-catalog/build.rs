#[path = "codegen/projection.rs"]
mod projection;

use std::{env, fs, path::PathBuf};

fn main() {
    let source = PathBuf::from("../../common/catalog/declarations.json");
    println!("cargo::rerun-if-changed={}", source.display());
    println!("cargo::rerun-if-changed=codegen/projection.rs");
    println!("cargo::rerun-if-changed=codegen/validation.rs");
    let bytes = fs::read(&source).expect("read shared declaration source");
    let code = projection::generate(&bytes).unwrap_or_else(|error| {
        panic!("{}: {error}", source.display());
    });
    fs::write(
        PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("catalog.rs"),
        code,
    )
    .expect("write Rust declaration projection");
}
