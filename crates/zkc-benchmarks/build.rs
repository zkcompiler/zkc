use std::process::Command;
fn main() {
    for name in ["OPT_LEVEL", "PROFILE", "TARGET"] {
        println!(
            "cargo:rustc-env=BENCH_{name}={}",
            std::env::var(name).unwrap()
        );
    }
    let output = Command::new(std::env::var("RUSTC").unwrap())
        .arg("--version")
        .output()
        .unwrap();
    println!(
        "cargo:rustc-env=BENCH_RUSTC={}",
        String::from_utf8(output.stdout).unwrap().trim()
    );
}
