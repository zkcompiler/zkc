//! Keep the pool-creating ark-ec feature off in resolved graphs, while retaining
//! polynomial/field parallelism. This checks resolution only, without building.
use serde_json::Value;
use std::{path::Path, process::Command};

#[test]
fn workspace_and_normal_sdk_keep_curve_msm_serial_and_fft_parallel() {
    let evidence = zkc_test_support::evidence("cpu-features");
    let root = zkc_test_support::root();
    audit(
        &metadata(&root.join("Cargo.toml"), true, evidence.path()),
        "workspace/all-features",
    );

    // A separate normal SDK consumer must not inherit workspace all-feature
    // unification, nor accidentally lose FFT parallelism outside the checkout.
    let consumer = evidence.nested("sdk-consumer");
    std::fs::create_dir_all(consumer.path().join("src")).unwrap();
    let sdk_path = serde_json::to_string(&root.join("crates/zkc").to_str().unwrap()).unwrap();
    std::fs::write(consumer.path().join("Cargo.toml"), format!(
        "[package]\nname = \"cpu-feature-consumer\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[workspace]\n\n[dependencies]\nzkc = {{ path = {sdk_path} }}\n"
    )).unwrap();
    std::fs::write(consumer.path().join("src/main.rs"), "fn main() {}\n").unwrap();
    // Reuse exact available versions, then resolve the new consumer offline.
    std::fs::copy(root.join("Cargo.lock"), consumer.path().join("Cargo.lock")).unwrap();
    audit(
        &metadata(&consumer.path().join("Cargo.toml"), false, consumer.path()),
        "normal SDK consumer",
    );
}

fn metadata(manifest: &Path, workspace: bool, evidence: &Path) -> Value {
    let mut command = Command::new(env!("CARGO"));
    command
        .args([
            "metadata",
            "--offline",
            "--format-version=1",
            "--manifest-path",
        ])
        .arg(manifest);
    if workspace {
        command.args(["--locked", "--all-features"]);
    }
    let output = command.output().expect("run Cargo feature resolution");
    std::fs::write(evidence.join("metadata.stderr"), &output.stderr).unwrap();
    std::fs::write(evidence.join("metadata.json"), &output.stdout).unwrap();
    assert!(
        output.status.success(),
        "metadata failed; inspect {}",
        evidence.display()
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn audit(metadata: &Value, scope: &str) {
    let packages = metadata["packages"].as_array().unwrap();
    let nodes = metadata["resolve"]["nodes"].as_array().unwrap();
    for (name, parallel) in [
        ("ark-ec", false),
        ("ark-poly-commit", false),
        ("ark-ff", true),
        ("ark-poly", true),
    ] {
        let package = packages
            .iter()
            .find(|p| p["name"] == name && p["version"] == "0.6.0")
            .unwrap();
        let node = nodes.iter().find(|n| n["id"] == package["id"]).unwrap();
        let features = node["features"].as_array().unwrap();
        assert_eq!(
            features.iter().any(|f| f == "parallel"),
            parallel,
            "{scope}: unexpected {name} features: {features:?}"
        );
        assert!(
            features.iter().any(|f| f == "std"),
            "{scope}: {name} lost std"
        );
    }
}
