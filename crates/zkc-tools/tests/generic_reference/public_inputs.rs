//! Public PCS entry values pass the real per-port input adapter before execution.
//! Reference comparison is conditional on that host admission, not an equality
//! claim between the host's stricter per-port policy and role authorization.
use super::*;
use std::sync::Arc;
use zkc_arkworks::{Keys, Table};
use zkc_backends::{
    Domain, EntryPolicy, InputBindings, NativeBackend, PortConstraint, PublicInputs, SetupRegistry,
};

#[test]
fn public_pcs_inputs_use_pinned_setups_and_independent_reference_checks() {
    let fixture = Fixture::from_fixture("generic-verify-opening.pir");
    let policy = Policy::default();
    for rank in [1, 2] {
        let a = Keys::setup_for_development(rank, &policy.ark_bounds()).unwrap();
        let b = Keys::setup_for_development(rank, &policy.ark_bounds()).unwrap();
        let keys = [&a, &b];
        let identity = a.verifier_key().metadata();
        let table = Table::from_logical(
            &(0..1u64 << rank)
                .map(|i| Scalar::from(i * i))
                .collect::<Vec<_>>(),
            &policy.ark_bounds(),
        )
        .unwrap();
        let point: Vec<_> = (0..rank).map(|i| Scalar::from(i as u64 + 2)).collect();
        let state = a.prover_key().commit(&table).unwrap();
        let (value, proof) = state.open(&point).unwrap();
        let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
        let admitted =
            admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
        let entry = admitted.entry("main").unwrap().into_iter().next().unwrap();
        let host = |mode| {
            let mut ports = BTreeMap::new();
            for source in ["commitment", "proof"] {
                let target = admitted
                    .source_map()
                    .unwrap()
                    .port("concrete", "V", source)
                    .unwrap();
                let setup = if mode == 2 {
                    None
                } else if (mode == 1 && source == "commitment") || (mode == 3 && source == "proof")
                {
                    Some(b.verifier_key().metadata())
                } else {
                    Some(identity)
                };
                ports.insert(
                    target.into(),
                    PortConstraint {
                        arity: Some(rank),
                        setup,
                    },
                );
            }
            NativeBackend::with_setups(
                policy,
                EntryPolicy::new(
                    Domain::new("V", "test", "main", Some("concrete")),
                    None,
                    PublicInputs::LocalOnly,
                )
                .with_ports(ports),
                SetupRegistry::new(
                    keys.iter().map(|k| k.verifier_key().clone()).collect(),
                    &policy,
                )
                .unwrap(),
            )
            .unwrap()
        };
        for correct in [true, false] {
            let claim = if correct {
                value
            } else {
                value + Scalar::from(1)
            };
            let values = vec![
                Value::VerifierKey(Arc::new(a.verifier_key().clone())),
                Value::Commitment(Arc::new(state.commitment().clone())),
                Value::Point(point.clone().into()),
                Value::Field(claim),
                Value::Proof(Arc::new(proof.clone())),
            ];
            let backend = host(0);
            let mut bindings = InputBindings::new();
            bindings.insert("key", values[0].clone()).unwrap();
            let encoded: Vec<_> = entry
                .inputs
                .iter()
                .zip(&values)
                .enumerate()
                .map(|(i, ((name, _), value))| {
                    let data = if i == 0 {
                        json!(["host", "key"])
                    } else {
                        json!([
                            "wire",
                            zkc_test_support::hex(&backend.encode_value(value).unwrap())
                        ])
                    };
                    json!([name, data])
                })
                .collect();
            let encoded = serde_json::to_vec(&json!(["zkc.inputs/1", encoded])).unwrap();
            let decoded = backend
                .inputs_from_json(&entry, &encoded, &bindings)
                .unwrap();
            for (mode, code) in [
                (1, "key-mismatch"),
                (2, "input-setup-required"),
                (3, "key-mismatch"),
            ] {
                assert!(
                    host(mode)
                        .inputs_from_json(&entry, &encoded, &bindings)
                        .unwrap_err()
                        .code
                        .contains(code)
                );
            }
            let trace = Trace::new(&fixture.source);
            let observed = Observed {
                inner: backend,
                source_map: admitted.source_map().unwrap().clone(),
                events: trace.clone(),
                conversions: 0,
            };
            let mut runner = Runner::new(&admitted, "main", "V", "test", observed, decoded)
                .unwrap_or_else(|e| panic!("{}", e.error));
            let terminal = loop {
                match runner.poll() {
                    Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                    action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
                    action => panic!("unexpected {action:?}"),
                }
            };
            let Action::Returned(returned) = terminal else {
                panic!("native verification failed")
            };
            let names = ["key", "commitment", "point", "value", "proof"];
            let ports: Vec<_> = names
                .into_iter()
                .zip(&values)
                .map(|(name, value)| json!([name, value_json(value)]))
                .collect();
            let mut answers = Vec::new();
            for (name, index) in [("commitment", 1), ("proof", 4)] {
                let request = json!([
                    "zkc.reference-primitive/2",
                    [
                        "source-origin/2",
                        "test",
                        "main",
                        "concrete",
                        [],
                        name,
                        "V",
                        []
                    ],
                    "validate",
                    ["multilinear.kzg.bls12-381/1"],
                    [],
                    [value_json(&values[index])]
                ]);
                answers.push(json!([request, commitments::reply(&keys, &request)]));
            }
            for event in trace.snapshot() {
                if event[0] == "response" {
                    answers.push(json!([event[1], commitments::reply(&keys, &event[1])]));
                }
            }
            let input = json!([
                "zkc.reference-inputs/1",
                "main",
                "test",
                [["V", ports]],
                [],
                answers,
                [],
                [
                    "zkc.reference-setups/1",
                    [[
                        "V",
                        keys.iter()
                            .map(|k| commitment_identity(k.verifier_key().metadata()))
                            .collect::<Vec<_>>()
                    ]],
                    []
                ]
            ]);
            let result = fixture.reference(&input);
            assert_eq!(
                result[3],
                json!([
                    "returned",
                    returned.iter().map(value_json).collect::<Vec<_>>()
                ])
            );
            assert_eq!(result[3][1], json!([["bool", correct.to_string()]]));
            let events: Vec<_> = result[4]
                .as_array()
                .unwrap()
                .iter()
                .filter(|e| e[0] != "external")
                .cloned()
                .collect();
            assert_eq!(events, trace.snapshot());
            assert_eq!(runner.backend().inner.active_frames(), 0);
        }
    }
}
