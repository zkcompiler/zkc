use std::process::Command;
fn main() {
    for name in [
        "OPT_LEVEL",
        "PROFILE",
        "TARGET",
        "CARGO_CFG_TARGET_FEATURE",
        "CARGO_ENCODED_RUSTFLAGS",
    ] {
        println!(
            "cargo:rustc-env=BENCH_{name}={}",
            std::env::var(name).unwrap_or_default()
        );
    }
    let mut features: Vec<_> = std::env::vars()
        .filter_map(|(name, _)| name.strip_prefix("CARGO_FEATURE_").map(str::to_owned))
        .collect();
    features.sort();
    println!("cargo:rustc-env=BENCH_FEATURES={}", features.join(","));
    let output = Command::new(std::env::var("RUSTC").unwrap())
        .arg("--version")
        .output()
        .unwrap();
    println!(
        "cargo:rustc-env=BENCH_RUSTC={}",
        String::from_utf8(output.stdout).unwrap().trim()
    );
}
