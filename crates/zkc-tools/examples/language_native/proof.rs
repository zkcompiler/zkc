//! Source-authored Schnorr runs through the same independent native proof host.
use super::*;
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_tools::artifact::native::ProofInputs;
use zkc_tools::artifact::{hex, native::NativeDeployment};
use zkc_tools::entry::SetupAuthority as ProofSetups;
use zkc_tools::entry::{
    BindingPolicy, BindingScope, NamedValues, Package, ProofEntry, ProofOptions, ProofRequest,
    RoleInputs as NamedRoleInputs, Value as LogicalValue,
};

pub(super) fn run(directory: &Path) {
    authored(directory);
    for suite in 0..2 {
        for simplified in 0..2 {
            for released in 0..2 {
                let bytes = std::fs::read(
                    directory.join(format!("source-proof-{suite}-{simplified}-{released}.json")),
                )
                .unwrap();
                let published = std::fs::read(directory.join(format!(
                    "source-proof-{suite}-{simplified}-{released}.entry"
                )))
                .unwrap();
                // This test's publication is produced by the preceding trusted
                // compiler invocation. Applications supply their own trusted pin.
                let package = Package::capture(
                    &published,
                    &Sha256::digest(&published).into(),
                    Package::MAX_BYTES,
                )
                .unwrap();
                assert_eq!(
                    package.artifact(),
                    std::str::from_utf8(&bytes)
                        .unwrap()
                        .strip_suffix('\n')
                        .unwrap()
                );
                assert_eq!(package.options().simplify, simplified == 1);
                assert_eq!(package.options().release_storage, released == 1);
                let checked = zkc_tools::entry::Interface::read(&package).unwrap();
                assert!(checked.is_proof());
                assert_eq!(checked.entry(), "sample::Demo");
                let interface: Json = serde_json::from_str(package.interface()).unwrap();
                assert_eq!(
                    interface["original"],
                    hex(&Sha256::digest(package.original().as_bytes()))
                );
                // Bind the exact packaged publication, without the standalone
                // language-bundle command's presentation newline.
                let bytes = package.artifact().as_bytes();
                let envelope: Json = serde_json::from_slice(bytes).unwrap();
                let deployment =
                    NativeDeployment::admit(bytes, &hex(&Sha256::digest(bytes))).unwrap();
                checked.check_proof(&deployment).unwrap();
                interface::controls(&package, |view| view.check_proof(&deployment));
                interface::changed_publication_cannot_reuse_pin(&package);
                for change in 0..3 {
                    let altered = interface::alter(&package, |frame, view| {
                        if change == 0 {
                            frame["options"]["simplify"] = json!(simplified == 0);
                        } else if change == 1 {
                            frame["original"] = json!(package.original().to_owned() + "\n");
                            view["original"] = json!(hex(&Sha256::digest(
                                frame["original"].as_str().unwrap().as_bytes()
                            )));
                        } else {
                            let symbol = view["protocol"].as_str().unwrap().to_owned();
                            let protocol = view["protocols"]
                                .as_array_mut()
                                .unwrap()
                                .iter_mut()
                                .find(|p| p["symbol"] == symbol)
                                .unwrap();
                            let service = protocol["services"]
                                .as_array_mut()
                                .unwrap()
                                .iter_mut()
                                .find(|s| s["owner"] == "P")
                                .unwrap();
                            service["contract"] = json!("random.bn254.fr/1");
                        }
                    });
                    assert_eq!(
                        zkc_tools::entry::Interface::read(&altered)
                            .unwrap()
                            .check_proof(&deployment),
                        Err(zkc_tools::entry::InterfaceError::NativeBinding)
                    );
                }

                let codec = backend(&json!({"entry":envelope[2][1][1]}), "P");
                let wire = |value: Value| hex(&codec.encode_native_value(&value).unwrap());
                let base = wire(Value::Curve(GroupPoint::generator()));
                let point = wire(Value::Curve(
                    GroupPoint::generator().scale(Scalar::from(3u64)),
                ));
                let input = |prover: bool, witness: u64| {
                    let data = if prover {
                        json!([
                            ["0", ["wire", base]],
                            ["1", ["wire", point]],
                            ["2", ["wire", wire(field(witness))]]
                        ])
                    } else {
                        json!([["0", ["wire", base]], ["1", ["wire", point]]])
                    };
                    let services = if prover {
                        json!([["3", "1"]])
                    } else {
                        json!([])
                    };
                    json!([
                        "zkc.native-proof-inputs/1",
                        [["V", "0", base], ["V", "1", point]],
                        data,
                        "",
                        services,
                        envelope[2][3].as_array().unwrap().len().to_string()
                    ])
                };
                let typed = |prover: bool, witness: u64| {
                    let common = || {
                        vec![
                            Value::Curve(GroupPoint::generator()).into(),
                            Value::Curve(GroupPoint::generator().scale(Scalar::from(3u64))).into(),
                        ]
                    };
                    let mut inputs = common();
                    if prover {
                        inputs.push(field(witness).into());
                    }
                    ProofInputs {
                        public: common(),
                        inputs,
                        context: Vec::new(),
                        services: if prover { vec![1] } else { vec![] },
                        transcript_budget: envelope[2][3].as_array().unwrap().len() as u64,
                    }
                };
                let tape = || BTreeMap::from([(3, vec![Scalar::from(7u64)])]);
                let encoded = deployment
                    .execute_test(&input(true, 3), None, tape())
                    .unwrap();
                let in_process = deployment
                    .execute_typed_test(&typed(true, 3), None, tape())
                    .unwrap();
                assert_eq!(encoded.binding, in_process.binding);
                assert_eq!(encoded.outcome, in_process.outcome);
                assert_eq!(encoded.resources, in_process.resources);
                let typed_proof = in_process.outcome.unwrap();
                assert!(
                    deployment
                        .execute_typed(&typed(false, 0), Some(&typed_proof))
                        .unwrap()
                        .outcome
                        .is_ok()
                );
                let mut mismatch = typed(true, 3);
                mismatch.inputs[1] = Value::Curve(GroupPoint::generator()).into();
                assert_eq!(
                    deployment
                        .execute_typed(&mismatch, None)
                        .err()
                        .unwrap()
                        .to_string(),
                    "native-proof-shared-public-input"
                );
                mismatch = typed(true, 3);
                mismatch.public[0] = InputValue::Resource { budget: 1 };
                assert_eq!(
                    deployment
                        .execute_typed(&mismatch, None)
                        .err()
                        .unwrap()
                        .to_string(),
                    "native-input-private"
                );
                mismatch = typed(true, 3);
                mismatch.inputs[2] = InputValue::Resource { budget: 1 };
                assert_eq!(
                    deployment
                        .execute_typed(&mismatch, None)
                        .err()
                        .unwrap()
                        .to_string(),
                    "native-input-private"
                );
                for (bad, expected) in [
                    (0, "native-proof-context-limit"),
                    (1, "native-proof-public-inputs"),
                    (2, "native-proof-role-inputs"),
                    (3, "native-proof-service-inputs"),
                    (4, "native-proof-budget"),
                    (5, "native-proof-budget"),
                ] {
                    let mut request = typed(true, 3);
                    match bad {
                        0 => request.context = vec![0; 4097],
                        1 => {
                            request.public.pop();
                        }
                        2 => {
                            request.inputs.pop();
                        }
                        3 => request.services.clear(),
                        4 => request.transcript_budget = 1_000_001,
                        _ => request.services[0] = 1_000_001,
                    }
                    assert_eq!(
                        deployment
                            .execute_typed(&request, None)
                            .err()
                            .unwrap()
                            .to_string(),
                        expected
                    );
                }
                let named = ProofEntry::admit(
                    package.clone(),
                    ProofOptions::default(),
                    ProofSetups::default(),
                )
                .unwrap();
                assert_eq!(named.binding_scope(), BindingScope::Transcript);
                let named_request = |prover: bool, witness: u64| {
                    let common = || {
                        NamedValues::from([
                            ("base".into(), Value::Curve(GroupPoint::generator()).into()),
                            (
                                "point".into(),
                                Value::Curve(GroupPoint::generator().scale(Scalar::from(3u64)))
                                    .into(),
                            ),
                        ])
                    };
                    let mut values = NamedValues::new();
                    if prover {
                        values.insert("scalar".into(), field(witness).into());
                    }
                    ProofRequest {
                        setups: BTreeMap::new(),
                        public: common(),
                        private: NamedRoleInputs {
                            inputs: values,
                            services: if prover {
                                BTreeMap::from([("nonces".into(), 1)])
                            } else {
                                BTreeMap::new()
                            },
                        },
                        context: Vec::new(),
                        transcript_budget: Some(typed(prover, witness).transcript_budget),
                    }
                };
                let native_named = named.prove(named_request(true, 3)).unwrap();
                assert!(native_named.outputs.unwrap().is_empty());
                let proof_bytes = native_named.native.outcome.unwrap();
                let checked_named = named.verify(named_request(false, 0), &proof_bytes).unwrap();
                assert!(checked_named.is_success());
                let checked_named = checked_named.into_result().ok().unwrap();
                assert!(checked_named.output_error.is_none());
                assert!(
                    matches!(&checked_named.outputs.unwrap()["accepted"], LogicalValue::Leaf(InputValue::Native(v)) if matches!(v.as_ref(), Value::Bool(true)))
                );
                let mut wrong_names = named_request(true, 3);
                wrong_names
                    .private
                    .inputs
                    .insert("extra".into(), LogicalValue::Unit);
                assert_eq!(
                    named.prove(wrong_names).err().unwrap().to_string(),
                    "entry-input-names"
                );
                wrong_names = named_request(false, 0);
                wrong_names.private.services.insert("challenges".into(), 1);
                assert_eq!(
                    named
                        .verify(wrong_names, &proof_bytes)
                        .err()
                        .unwrap()
                        .to_string(),
                    "entry-service-names"
                );
                let invalid_named = named
                    .prove(named_request(true, 5))
                    .unwrap()
                    .native
                    .outcome
                    .unwrap();
                let rejection = named
                    .verify(named_request(false, 0), &invalid_named)
                    .unwrap();
                assert!(!rejection.is_success());
                let rejection = rejection.into_result().err().unwrap();
                assert_eq!(
                    rejection.native.outcome.as_ref().unwrap_err(),
                    "artifact-rejected"
                );
                assert!(rejection.outputs.is_none());
                let produced = deployment.execute(&input(true, 3), None).unwrap();
                assert!(produced.cleanup_errors.is_empty());
                assert_eq!(produced.messages, 2);
                assert!(produced.outputs.as_ref().unwrap().is_empty());
                let proof = produced.outcome.unwrap();
                // Separately admitted handle and verifier inputs; no witness or
                // producer runtime state is available to this invocation.
                let verifier =
                    NativeDeployment::admit(bytes, &hex(&Sha256::digest(bytes))).unwrap();
                let validated = verifier.execute(&input(false, 0), Some(&proof)).unwrap();
                assert!(validated.cleanup_errors.is_empty());
                validated.outcome.unwrap();
                assert!(matches!(
                    validated.outputs.as_ref().unwrap().get(&0),
                    Some(Value::Bool(true))
                ));
                let invalid = deployment.execute(&input(true, 5), None).unwrap();
                assert!(invalid.cleanup_errors.is_empty());
                let rejected = verifier
                    .execute(&input(false, 0), Some(&invalid.outcome.unwrap()))
                    .unwrap();
                assert!(rejected.cleanup_errors.is_empty());
                assert_eq!(rejected.outcome.unwrap_err(), "artifact-rejected");
                assert!(rejected.outputs.is_none());
                let mut wrong_context = input(false, 0);
                wrong_context[3] = json!("01");
                assert!(
                    verifier
                        .execute(&wrong_context, Some(&proof))
                        .unwrap()
                        .outcome
                        .is_err()
                );
            }
        }
    }
}

fn authored(directory: &Path) {
    let bytes = std::fs::read(directory.join("host-proof.entry")).unwrap();
    let package =
        Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap();
    assert_eq!(
        ProofEntry::admit(
            package.clone(),
            ProofOptions::default(),
            ProofSetups::default()
        )
        .err()
        .unwrap()
        .to_string(),
        "entry-proof-binding-policy"
    );
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    let prover = ProofEntry::admit(package.clone(), options, ProofSetups::default()).unwrap();
    let verifier = ProofEntry::admit(package, options, ProofSetups::default()).unwrap();
    assert_eq!(prover.binding_scope(), BindingScope::HeaderOnly);
    for pair in [false, true] {
        let payload = |wire: bool| {
            let leaf = |n| {
                if wire {
                    LogicalValue::from(InputValue::Wire(
                        backend(&json!({"entry":"sample::Echo"}), "P")
                            .encode_native_value(&field(n))
                            .unwrap(),
                    ))
                } else {
                    field(n).into()
                }
            };
            LogicalValue::Record(NamedValues::from([
                (
                    "choice".into(),
                    LogicalValue::Variant {
                        alternative: if pair { "Pair" } else { "Empty" }.into(),
                        fields: if pair {
                            NamedValues::from([("0".into(), leaf(3)), ("1".into(), leaf(5))])
                        } else {
                            NamedValues::new()
                        },
                    },
                ),
                ("marker".into(), Value::Bool(true).into()),
            ]))
        };
        let request = || ProofRequest {
            setups: BTreeMap::new(),
            public: NamedValues::from([
                ("payload".into(), payload(false)),
                ("empty".into(), LogicalValue::Unit),
            ]),
            private: NamedRoleInputs::default(),
            context: vec![1, 2, 3],
            transcript_budget: Some(0),
        };
        let produced = prover.prove(request()).unwrap();
        assert!(produced.output_error.is_none());
        assert!(matches!(
            &produced.outputs.unwrap()["empty"],
            LogicalValue::Unit
        ));
        let proof = produced.native.outcome.unwrap();
        let checked = verifier.verify(request(), &proof).unwrap();
        assert!(
            checked.native.outcome.is_ok(),
            "{:?}",
            checked.native.outcome
        );
        assert!(checked.output_error.is_none());
        let outputs = checked.outputs.unwrap();
        assert!(matches!(&outputs["empty"], LogicalValue::Unit));
        assert_eq!(
            format!("{:?}", outputs["received"]),
            format!("{:?}", payload(false))
        );
        let mut bad = request();
        bad.public.remove("empty");
        let error = prover.prove(bad).err().unwrap();
        assert_eq!(error.phase, zkc_tools::entry::EntryPhase::Request);
        assert_eq!(error.code(), "entry-input-names");
        bad = request();
        bad.private
            .inputs
            .insert("empty".into(), LogicalValue::Unit);
        assert_eq!(
            verifier.verify(bad, &proof).err().unwrap().to_string(),
            "entry-input-names"
        );
        bad = request();
        bad.transcript_budget = Some(1);
        let error = prover.prove(bad).err().unwrap();
        assert_eq!(error.phase, zkc_tools::entry::EntryPhase::Preparation);
        assert_eq!(error.code(), "native-proof-unselected-transcript");
        bad = request();
        bad.context.push(4);
        let rejected = verifier.verify(bad, &proof).unwrap();
        assert!(rejected.native.outcome.is_err());
        assert!(rejected.outputs.is_none());
        bad = request();
        bad.private.inputs.insert("payload".into(), payload(true));
        let error = prover.prove(bad).err().unwrap();
        assert_eq!(error.phase, zkc_tools::entry::EntryPhase::Request);
        assert_eq!(error.code(), "entry-input-names");
        // The SDK accepts canonical wires as the single public supply as well.
        let mut wired = request();
        wired.public.insert("payload".into(), payload(true));
        assert!(prover.prove(wired).unwrap().is_success());
    }
}
