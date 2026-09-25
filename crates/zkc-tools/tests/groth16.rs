//! Explicit PIR execution and strict external proof codec controls.
#[cfg(feature = "test-utils")]
#[path = "common/circom.rs"]
mod circom;

use ark_bn254::{Fq, Fq2, Fr, G2Affine};
use ark_ff::{Field, PrimeField};
use serde_json::{Value as Json, json};
use zkc_arkworks::bn254::{G1, G2};
use zkc_tools::groth16::{Proof, Statement, VerifyingKey};

fn sample() -> Proof {
    Proof {
        a: G1::generator(),
        b: G2::generator(),
        c: G1::generator(),
    }
}
fn bytes(v: &Json) -> Vec<u8> {
    serde_json::to_vec(v).unwrap()
}
#[test]
fn proof_json_has_exact_fields_shapes_domains_and_canonical_coordinates() {
    let proof = sample();
    let encoded = proof.to_json().unwrap();
    assert_eq!(Proof::from_json(&encoded).unwrap(), proof);
    let valid: Json = serde_json::from_slice(&encoded).unwrap();
    assert_eq!(valid["pi_a"], json!(["1", "2", "1"]));
    for (path, value) in [
        (vec!["protocol"], json!("plonk")),
        (vec!["curve"], json!("bn254")),
        (vec!["pi_a"], json!(["1", "2"])),
        (vec!["pi_c"], json!(["1", "2", "1", "0"])),
        (
            vec!["pi_b"],
            json!([["1", "2"], ["3", "4"], ["1", "0"], ["0", "0"]]),
        ),
    ] {
        let mut bad = valid.clone();
        bad[path[0]] = value;
        assert!(Proof::from_json(&bytes(&bad)).is_err());
    }
    for value in [
        json!(1),
        json!("01"),
        json!("-1"),
        json!("+1"),
        json!(" 1"),
        json!("1e0"),
        json!(Fq::MODULUS.to_string()),
        json!("99999999999999999999999999999999999999999999999999999999999999999999999999999999"),
    ] {
        let mut bad = valid.clone();
        bad["pi_a"][0] = value;
        assert!(Proof::from_json(&bytes(&bad)).is_err());
    }
    for z in ["0", "2"] {
        let mut bad = valid.clone();
        bad["pi_a"][2] = json!(z);
        assert!(Proof::from_json(&bytes(&bad)).is_err());
    }
    let mut bad = valid.clone();
    bad["pi_a"][1] = json!("3");
    assert!(Proof::from_json(&bytes(&bad)).is_err());
    let mut extra = valid.clone();
    extra["extra"] = json!(0);
    assert!(Proof::from_json(&bytes(&extra)).is_err());
    for name in ["pi_a", "pi_b", "pi_c", "protocol", "curve"] {
        let mut missing = valid.clone();
        missing.as_object_mut().unwrap().remove(name);
        assert!(Proof::from_json(&bytes(&missing)).is_err());
        let duplicate = format!(
            "{{\"{name}\":{},{}",
            valid[name],
            String::from_utf8(encoded.clone())
                .unwrap()
                .trim_start_matches('{')
        );
        assert!(Proof::from_json(duplicate.as_bytes()).is_err());
    }
    for end in [0, 1, encoded.len() / 2, encoded.len() - 1] {
        assert!(Proof::from_json(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.extend(b" null");
    assert!(Proof::from_json(&trailing).is_err());
    let infinity = Proof {
        a: G1::identity(),
        b: G2::identity(),
        c: G1::identity(),
    };
    assert_eq!(
        Proof::from_json(&infinity.to_json().unwrap()).unwrap(),
        infinity
    );
    let mut bad: Json = serde_json::from_slice(&infinity.to_json().unwrap()).unwrap();
    bad["pi_b"][1][1] = json!("1");
    assert!(Proof::from_json(&bytes(&bad)).is_err());
}
#[test]
fn rejects_on_curve_g2_outside_the_prime_order_subgroup() {
    // Deterministically find a twist point; do not clear its cofactor.
    let mut bad = serde_json::from_slice::<Json>(&sample().to_json().unwrap()).unwrap();
    for i in 0..100u64 {
        let x = Fq2::new(Fq::from(i), Fq::from(1));
        let b = Fq2::new(Fq::from(3), Fq::from(0)) / Fq2::new(Fq::from(9), Fq::from(1));
        if let Some(y) = (x.square() * x + b).sqrt() {
            let point = G2Affine::new_unchecked(x, y);
            assert!(point.is_on_curve());
            if !point.is_in_correct_subgroup_assuming_on_curve() {
                bad["pi_b"] = json!([
                    [
                        x.c0.into_bigint().to_string(),
                        x.c1.into_bigint().to_string()
                    ],
                    [
                        y.c0.into_bigint().to_string(),
                        y.c1.into_bigint().to_string()
                    ],
                    ["1", "0"]
                ]);
                assert_eq!(
                    Proof::from_json(&bytes(&bad)).unwrap_err().code,
                    "groth16-invalid-g2"
                );
                return;
            }
        }
    }
    panic!("failed to construct subgroup control");
}
#[test]
fn public_scalars_and_effective_key_are_strict() {
    assert_eq!(
        Statement::from_json(br#"["0","1"]"#).unwrap().0.as_ref(),
        [Fr::from(0), Fr::from(1)]
    );
    for value in [
        json!([1]),
        json!(["01"]),
        json!([Fr::MODULUS.to_string()]),
        json!(["-1"]),
        json!({}),
    ] {
        assert!(Statement::from_json(&bytes(&value)).is_err());
    }
    let p: Json = serde_json::from_slice(&sample().to_json().unwrap()).unwrap();
    let key = json!({"protocol":"groth16","curve":"bn128","nPublic":1,"vk_alpha_1":p["pi_a"],
        "vk_beta_2":p["pi_b"],"vk_gamma_2":p["pi_b"],"vk_delta_2":p["pi_b"],"IC":[p["pi_a"],p["pi_a"]]});
    let vk = VerifyingKey::from_json(&bytes(&key)).unwrap();
    assert_eq!(VerifyingKey::from_json(&vk.to_json().unwrap()).unwrap(), vk);
    for count in [
        json!(0),
        json!(2),
        json!(32768),
        json!(-1),
        json!(1.0),
        json!("1"),
    ] {
        let mut bad = key.clone();
        bad["nPublic"] = count;
        assert!(VerifyingKey::from_json(&bytes(&bad)).is_err());
    }
    let mut bad = key.clone();
    bad["IC"][0][1] = json!("3");
    assert!(VerifyingKey::from_json(&bytes(&bad)).is_err());
    let mut bad = key;
    bad["vk_alphabeta_12"] = json!(["0"]);
    assert!(VerifyingKey::from_json(&bytes(&bad)).is_err());
}

#[test]
fn normalized_relation_retains_exact_field_layout_rows_and_canonical_entries() {
    use zkc_tools::groth16::PreparedRelation;
    let relation = json!([
        "zkc.relation.r1cs/1",
        "bn254.fr",
        "3",
        "0",
        "1",
        [[[["1", "1"]], [["2", "1"]], [["0", "6"]]]]
    ]);
    let prepared = PreparedRelation::from_normalized(&bytes(&relation)).unwrap();
    assert_eq!(
        prepared.identity(),
        "151447f98836792113aac88ff71e39a104aa68c22855cdadd7992bd65d55ba83"
    );
    assert_eq!(
        (prepared.columns(), prepared.n_public(), prepared.rows()),
        (3, 1, 1)
    );
    for (field, value) in [
        (0, json!("zkc.relation.r1cs/2")),
        (1, json!("bls12-381.fr")),
        (2, json!("03")),
        (2, json!("0")),
        (4, json!("3")),
        (5, json!({})),
    ] {
        let mut bad = relation.clone();
        bad[field] = value;
        assert!(PreparedRelation::from_normalized(&bytes(&bad)).is_err());
    }
    for terms in [
        json!([["3", "1"]]),
        json!([["1", "0"]]),
        json!([["1", "01"]]),
        json!([["1", "1"], ["1", "1"]]),
        json!([["2", "1"], ["1", "1"]]),
    ] {
        let mut bad = relation.clone();
        bad[5][0][0] = terms;
        assert!(PreparedRelation::from_normalized(&bytes(&bad)).is_err());
    }
}

#[cfg(feature = "test-utils")]
mod genuine {
    use super::*;
    use std::{
        path::{Path, PathBuf},
        process::Command,
    };
    use zkc_tools::{
        groth16::{PreparedProtocol, PreparedRelation, ProverKey, Randomness, policy},
        snarkjs::{self, Limits, Witness},
    };
    fn read(path: impl AsRef<Path>) -> Vec<u8> {
        std::fs::read(path).unwrap()
    }
    fn controlled() -> Randomness {
        Randomness::Test {
            r: Fr::from(1),
            s: Fr::from(2),
        }
    }
    fn snarkjs(root: &Path, args: &[&Path], verb: &str) -> std::process::Output {
        Command::new("node")
            .arg(root.join("node_modules/snarkjs/cli.js"))
            .args(["groth16", verb])
            .args(args)
            .env("NODE_OPTIONS", "--max-old-space-size=4096")
            .output()
            .expect("installed pinned snarkjs CLI")
    }
    fn accepted(output: std::process::Output) {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            !String::from_utf8_lossy(&output.stdout).contains("Invalid proof"),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
    #[test]
    // The compiler and the checker are resolved by name like anywhere else;
    // what this cannot have without being told is the snarkjs fixture tree.
    #[ignore = "requires ZKC_GROTH16_FIXTURE from unmodified snarkjs 0.7.5"]
    fn compiled_pir_matches_both_depths_and_cross_verifies_with_unmodified_snarkjs() {
        let root = PathBuf::from(
            std::env::var_os("ZKC_GROTH16_FIXTURE").expect("set ZKC_GROTH16_FIXTURE"),
        );
        let compiler = zkc_test_support::compiler();
        let lean = zkc_test_support::checker("interactive-protocol");
        let temp = zkc_test_support::evidence(module_path!());
        for depth in [2, 16] {
            let dir = root.join(format!("artifacts/depth{depth}"));
            let protocol = PreparedProtocol::compile(
                &compiler,
                &lean,
                &read(zkc_test_support::root().join("examples/protocols/groth16.pir")),
                &read(dir.join(format!("depth{depth}.r1cs"))),
            )
            .unwrap();
            let relation = protocol.relation().unwrap();
            let normalized = Command::new(&compiler)
                .arg("relation-read")
                .arg(dir.join(format!("depth{depth}.r1cs")))
                .output()
                .unwrap();
            assert!(normalized.status.success());
            let normalized: Json = serde_json::from_slice(&normalized.stdout).unwrap();
            assert_eq!(
                PreparedRelation::from_normalized(&bytes(&normalized))
                    .unwrap()
                    .identity(),
                relation.identity()
            );

            // Cached ordinary source still requires the installed checker.
            let cached = PreparedProtocol::prepare(
                protocol.source(),
                protocol.endpoints(),
                &lean,
                protocol.relation_identity(),
            )
            .unwrap();
            assert!(
                PreparedProtocol::prepare(
                    protocol.source(),
                    protocol.endpoints(),
                    &lean,
                    &"0".repeat(64)
                )
                .is_err()
            );
            let modified = String::from_utf8(protocol.endpoints().to_vec())
                .unwrap()
                .replacen("[\"1\"]", "[\"2\"]", 1);
            assert_ne!(modified.as_bytes(), protocol.endpoints());
            assert!(
                PreparedProtocol::prepare(
                    protocol.source(),
                    modified.as_bytes(),
                    &lean,
                    protocol.relation_identity()
                )
                .is_err()
            );

            let key =
                snarkjs::read_zkey(dir.join("final.zkey"), &Limits::default(), &policy()).unwrap();
            let witness =
                snarkjs::read_wtns(dir.join("witness.wtns"), &Limits::default(), &policy())
                    .unwrap();
            let vk = VerifyingKey::from_json(&read(dir.join("vk.json"))).unwrap();
            let statement = Statement::from_json(&read(dir.join("public.json"))).unwrap();
            let prover = ProverKey::new(&key, &vk, relation).unwrap();
            for matrix in [0, 1] {
                let mut altered = normalized.clone();
                altered[5][0][matrix][0][1] = json!("2");
                let altered = PreparedRelation::from_normalized(&bytes(&altered)).unwrap();
                assert_eq!(
                    ProverKey::new(&key, &vk, &altered).unwrap_err().code,
                    "groth16-relation-key-coefficients"
                );
            }
            let mut wrong_header = normalized.clone();
            wrong_header[4] = json!("2");
            let wrong_header = PreparedRelation::from_normalized(&bytes(&wrong_header)).unwrap();
            assert_eq!(
                ProverKey::new(&key, &vk, &wrong_header).unwrap_err().code,
                "groth16-relation-key-header"
            );
            let mut wrong_field = normalized.clone();
            wrong_field[1] = json!("bls12-381.fr");
            assert!(PreparedRelation::from_normalized(&bytes(&wrong_field)).is_err());
            let mut changed_c = normalized.clone();
            changed_c[5][0][2] = json!([["0", "1"]]);
            let changed_c = PreparedRelation::from_normalized(&bytes(&changed_c)).unwrap();
            // Zkey does not contain C: this intentionally remains an external
            // key derivation premise. Its different relation identity is caught
            // when code and data are joined below.
            let changed_c_key = ProverKey::new(&key, &vk, &changed_c).unwrap();

            let invocation = protocol
                .bind(vk.clone(), statement.clone(), b"configured-test-relation")
                .unwrap();
            assert!(
                invocation
                    .prove(&changed_c_key, &witness, controlled())
                    .is_err()
            );
            let proof = invocation.prove(&prover, &witness, controlled()).unwrap();
            // The native checked entry consumes retained material from the
            // same real codecs, with per-invocation premise authorization.
            let contract = zkc_tools::ingress::Groth16Contract::new(
                zkc_tools::ingress::RelationSubject::from_prepared(relation),
                vk.clone(),
                zkc_tools::ingress::GROTH16_PREMISES,
            )
            .unwrap();
            let checked_key = contract
                .check_key(
                    &bytes(&normalized),
                    &read(dir.join("final.zkey")),
                    &Limits::default(),
                )
                .unwrap();
            let checked_assignment = contract
                .check_assignment(
                    &statement,
                    &read(dir.join("witness.wtns")),
                    &Limits::default(),
                )
                .unwrap();
            for (context, kind) in [
                (Vec::new(), zkc_tools::ingress::FailureKind::Malformed),
                (vec![0; 4097], zkc_tools::ingress::FailureKind::Resource),
            ] {
                let error = protocol
                    .bind_checked(&contract, statement.clone(), &context)
                    .unwrap_err();
                assert_eq!(error.kind, kind);
                assert_eq!(error.code, "groth16-relation-context");
            }
            let checked_invocation = protocol
                .bind_checked(&contract, statement.clone(), b"configured-test-relation")
                .unwrap();
            assert_eq!(
                cached
                    .bind_checked(&contract, statement.clone(), b"context")
                    .unwrap_err()
                    .code,
                "ingress-compiled-descriptor-unavailable"
            );
            assert_eq!(
                checked_invocation
                    .prove(
                        &checked_key,
                        &checked_assignment,
                        &zkc_tools::ingress::AcceptedPremises::default(),
                        controlled()
                    )
                    .unwrap_err()
                    .code,
                "ingress-required-premise"
            );
            let accepted_premises =
                zkc_tools::ingress::AcceptedPremises::new(zkc_tools::ingress::GROTH16_PREMISES);
            // C is not present in the zkey. A second contract can therefore
            // validate the same bytes under a different C premise, but its
            // checked objects must never enter this compiled invocation.
            let other_contract = zkc_tools::ingress::Groth16Contract::new(
                zkc_tools::ingress::RelationSubject::from_prepared(&changed_c),
                vk.clone(),
                zkc_tools::ingress::GROTH16_PREMISES,
            )
            .unwrap();
            let other_key = other_contract
                .check_key(
                    changed_c.canonical_descriptor(),
                    &read(dir.join("final.zkey")),
                    &Limits::default(),
                )
                .unwrap();
            let other_assignment = other_contract
                .check_assignment(
                    &statement,
                    &read(dir.join("witness.wtns")),
                    &Limits::default(),
                )
                .unwrap();
            assert_eq!(
                protocol
                    .bind_checked(&other_contract, statement.clone(), b"context")
                    .unwrap_err()
                    .code,
                "ingress-compiled-relation-mismatch"
            );
            assert_eq!(
                checked_invocation
                    .prove(
                        &other_key,
                        &checked_assignment,
                        &accepted_premises,
                        controlled()
                    )
                    .unwrap_err()
                    .code,
                "ingress-key-subject"
            );
            assert_eq!(
                checked_invocation
                    .prove(
                        &checked_key,
                        &other_assignment,
                        &accepted_premises,
                        controlled()
                    )
                    .unwrap_err()
                    .code,
                "ingress-assignment-subject"
            );
            let checked_proof = checked_invocation
                .prove(
                    &checked_key,
                    &checked_assignment,
                    &accepted_premises,
                    controlled(),
                )
                .unwrap();
            assert_eq!(checked_proof.artifact, proof.artifact);
            checked_invocation
                .verify_artifact(&checked_proof.artifact, &accepted_premises)
                .unwrap();
            let reference = Proof::from_json(&read(dir.join("proof-r1-s2.json"))).unwrap();
            assert_eq!(
                proof.proof, reference,
                "controlled coordinates depth {depth}"
            );
            assert_eq!(
                proof.proof.to_json().unwrap(),
                reference.to_json().unwrap(),
                "same explicit serialization"
            );
            invocation.verify_artifact(&proof.artifact).unwrap();
            cached
                .bind(vk.clone(), statement.clone(), b"configured-test-relation")
                .unwrap()
                .verify_artifact(&proof.artifact)
                .unwrap();
            invocation.verify(&reference).unwrap();
            invocation
                .verify_json(&read(dir.join("proof.json")))
                .unwrap();
            let again = invocation.prove(&prover, &witness, controlled()).unwrap();
            assert_eq!(again.artifact, proof.artifact);
            let output = temp.path().join(format!("zkc-{depth}.json"));
            std::fs::write(&output, proof.proof.to_json().unwrap()).unwrap();
            accepted(snarkjs(
                &root,
                &[&dir.join("vk.json"), &dir.join("public.json"), &output],
                "verify",
            ));
            let fresh = invocation.prove(&prover, &witness, Randomness::Os).unwrap();
            let fresh2 = invocation.prove(&prover, &witness, Randomness::Os).unwrap();
            assert_ne!(fresh.proof, fresh2.proof);
            invocation.verify(&fresh.proof).unwrap();
            invocation.verify(&fresh2.proof).unwrap();
            std::fs::write(&output, fresh.proof.to_json().unwrap()).unwrap();
            accepted(snarkjs(
                &root,
                &[&dir.join("vk.json"), &dir.join("public.json"), &output],
                "verify",
            ));
            // The unchanged producer is invoked in this test, not only replayed.
            let external = temp.path().join(format!("external-{depth}.json"));
            let public = temp.path().join(format!("public-{depth}.json"));
            accepted(snarkjs(
                &root,
                &[
                    &dir.join("final.zkey"),
                    &dir.join("witness.wtns"),
                    &external,
                    &public,
                ],
                "prove",
            ));
            assert_eq!(Statement::from_json(&read(public)).unwrap(), statement);
            invocation.verify_json(&read(external)).unwrap();
            let mut bad = reference.clone();
            bad.a = bad.a.neg();
            assert!(invocation.verify(&bad).is_err());
            for n in [0, 8, 40, proof.artifact.len() - 1] {
                assert!(invocation.verify_artifact(&proof.artifact[..n]).is_err());
            }
            let mut trailing = proof.artifact.clone();
            trailing.push(0);
            assert!(invocation.verify_artifact(&trailing).is_err());
            let mut signals = statement.0.to_vec();
            signals[0] += Fr::from(1);
            let wrong_root = protocol
                .bind(
                    vk.clone(),
                    Statement(signals.into()),
                    b"configured-test-relation",
                )
                .unwrap();
            assert!(wrong_root.verify(&reference).is_err());
            assert!(wrong_root.verify_artifact(&proof.artifact).is_err());
            assert!(wrong_root.prove(&prover, &witness, controlled()).is_err());
            let other_context = protocol
                .bind(vk.clone(), statement.clone(), b"another-relation-domain")
                .unwrap();
            assert!(other_context.verify_artifact(&proof.artifact).is_err());
            // Bare snarkjs JSON has no domain marker; explicit rebinding is documented.
            other_context.verify(&reference).unwrap();
            let mut wrong_vk: Json = serde_json::from_slice(&vk.to_json().unwrap()).unwrap();
            wrong_vk["vk_delta_2"] = serde_json::from_slice::<Json>(&sample().to_json().unwrap())
                .unwrap()["pi_b"]
                .clone();
            let wrong_vk = VerifyingKey::from_json(&bytes(&wrong_vk)).unwrap();
            assert!(ProverKey::new(&key, &wrong_vk, relation).is_err());
            assert!(
                protocol
                    .bind(wrong_vk, statement.clone(), b"configured-test-relation")
                    .unwrap()
                    .verify(&reference)
                    .is_err()
            );
            let mut wrong_domain = key.clone();
            wrong_domain.coset_shift = -wrong_domain.coset_shift;
            assert_eq!(
                ProverKey::new(&wrong_domain, &vk, relation)
                    .unwrap_err()
                    .code,
                "groth16-domain"
            );
            // Change the leaf commitment witness cell, retaining the expected root.
            let index =
                circom::witness_index(&dir.join(format!("depth{depth}.sym")), "main.nodes[0]");
            let mut bad_witness = witness.0.to_vec();
            assert!(index > statement.0.len() && index < bad_witness.len());
            bad_witness[index] += Fr::from(1);
            let tampered = invocation.prove(&prover, &Witness(bad_witness.into()), controlled());
            assert!(
                tampered.is_err(),
                "PIR must stop on unsatisfied commitment witness"
            );
            assert!(
                invocation
                    .verify_json(&read(dir.join("controls/tampered-proof.json")))
                    .is_err()
            );
            if depth == 2 {
                let output = temp.path().join("cli-proof.json");
                let artifact = temp.path().join("cli.proof");
                let prefix = temp.path().join("cli-code");
                let status = Command::new(env!("CARGO_BIN_EXE_groth16-artifact"))
                    .arg("prove")
                    .arg("--compiler")
                    .arg(&compiler)
                    .arg("--lean")
                    .arg(&lean)
                    .arg("--r1cs")
                    .arg(dir.join("depth2.r1cs"))
                    .arg("--vk")
                    .arg(dir.join("vk.json"))
                    .arg("--public")
                    .arg(dir.join("public.json"))
                    .args(["--context", "cli-fixture", "--test-randomness", "1,2"])
                    .arg("--zkey")
                    .arg(dir.join("final.zkey"))
                    .arg("--witness")
                    .arg(dir.join("witness.wtns"))
                    .arg("--proof")
                    .arg(&output)
                    .arg("--artifact")
                    .arg(&artifact)
                    .arg("--save-code")
                    .arg(&prefix)
                    .output()
                    .unwrap();
                assert!(
                    status.status.success(),
                    "{}",
                    String::from_utf8_lossy(&status.stderr)
                );
                assert_eq!(Proof::from_json(&read(&output)).unwrap(), reference);
                let record: Json = serde_json::from_slice(&status.stdout).unwrap();
                assert_eq!(record["randomness"], "explicit-test-tape");
                assert_eq!(
                    record["key_binding"]["external_premises"]["C_IC_H_key_derivation"],
                    "unverified"
                );
                let check = |flag: &str, path: &Path, context: &str| {
                    Command::new(env!("CARGO_BIN_EXE_groth16-artifact"))
                        .arg("verify")
                        // Cached public verification has no compiler/R1CS/zkey/witness dependency.
                        .args(["--compiler", "/absent/compiler"])
                        .arg("--lean")
                        .arg(&lean)
                        .arg("--common")
                        .arg(temp.path().join("cli-code.common.json"))
                        .arg("--endpoints")
                        .arg(temp.path().join("cli-code.endpoints.json"))
                        .arg("--relation-id")
                        .arg(protocol.relation_identity())
                        .arg("--vk")
                        .arg(dir.join("vk.json"))
                        .arg("--public")
                        .arg(dir.join("public.json"))
                        .args(["--context", context, flag])
                        .arg(path)
                        .output()
                        .unwrap()
                };
                for (flag, path) in [
                    ("--proof", output.as_path()),
                    ("--artifact", artifact.as_path()),
                    ("--proof", dir.join("proof.json").as_path()),
                ] {
                    let result = check(flag, path, "cli-fixture");
                    assert!(
                        result.status.success(),
                        "{}",
                        String::from_utf8_lossy(&result.stderr)
                    );
                }
                assert!(
                    !check("--artifact", &artifact, "different-context")
                        .status
                        .success()
                );
            }
            let mut short = witness.0.to_vec();
            short.pop();
            assert!(
                invocation
                    .prove(&prover, &Witness(short.into()), controlled())
                    .is_err()
            );
        }
    }
}
