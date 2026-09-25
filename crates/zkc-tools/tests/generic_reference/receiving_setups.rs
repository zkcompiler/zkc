//! Two PCS instances share compiled code and use independently selected codecs.
use super::*;
use std::sync::Arc;
use zkc_arkworks::{Keys, Metadata, Table};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, PublicInputs, SetupRegistry};
use zkc_runtime::interactive::{BackendError, Receive};
use zkc_tools::protocol::{MessageDecoder, drive_with_decoder};

struct Decoder {
    a: Metadata,
    b: Metadata,
    mode: u8,
}
impl Decoder {
    fn selected(&self, site: &str) -> Option<Metadata> {
        match site {
            "commit_a" if self.mode == 2 => None,
            "commit_a" if self.mode == 1 => Some(self.b),
            "commit_a" | "proof_a" => Some(self.a),
            "commit_b" | "proof_b" => Some(self.b),
            _ => None,
        }
    }
}
impl MessageDecoder<Observed> for Decoder {
    fn decode(
        &self,
        backend: &Observed,
        receive: &Receive,
        bytes: &[u8],
    ) -> Result<Value, BackendError> {
        match receive.ty.kind() {
            zkc_runtime::interactive::Type::Commitment | zkc_runtime::interactive::Type::Proof => {
                let key = self
                    .selected(&receive.envelope.site)
                    .ok_or_else(|| BackendError::new("refused:receiving-setup-missing"))?;
                backend
                    .inner
                    .decode_for_setup(receive.ty.clone(), key, bytes)
            }
            _ => backend.inner.decode_typed_value(receive.ty.clone(), bytes),
        }
    }
}

fn compare(rank: usize, mode: u8) {
    let fixture = Fixture::from_fixture("generic-openings.pir");
    let policy = Policy::default();
    let a = Keys::setup_for_development(2, &policy.ark_bounds()).unwrap();
    let b = Keys::setup_for_development(rank, &policy.ark_bounds()).unwrap();
    let keys = [&a, &b];
    let decoder = Decoder {
        a: a.verifier_key().metadata(),
        b: b.verifier_key().metadata(),
        mode,
    };
    let host = |role| {
        NativeBackend::with_setups(
            policy,
            EntryPolicy::new(
                Domain::new(role, "test", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            SetupRegistry::new(
                keys.iter().map(|k| k.verifier_key().clone()).collect(),
                &policy,
            )
            .unwrap(),
        )
        .unwrap()
    };
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &host("P"), &checker).unwrap();
    let table = |n| {
        Value::Table(Arc::new(
            Table::from_logical(
                &(0..1u64 << n)
                    .map(|i| Scalar::from(i * i))
                    .collect::<Vec<_>>(),
                &policy.ark_bounds(),
            )
            .unwrap(),
        ))
    };
    let p = vec![
        Value::ProverKey(Arc::new(a.prover_key().clone())),
        Value::ProverKey(Arc::new(b.prover_key().clone())),
        table(2),
        table(rank),
    ];
    let v = vec![
        Value::VerifierKey(Arc::new(a.verifier_key().clone())),
        Value::VerifierKey(Arc::new(b.verifier_key().clone())),
        Value::Point(vec![Scalar::from(2); 2].into()),
        Value::Point(vec![Scalar::from(3); rank].into()),
    ];
    let trace = Trace::new(&fixture.source);
    let mut supplied = Vec::new();
    let mut runners = BTreeMap::new();
    for (role, names, values) in [
        ("P", ["ka", "kb", "a", "b"], p),
        ("V", ["va", "vb", "ra", "rb"], v),
    ] {
        supplied.push(json!([
            role,
            names
                .into_iter()
                .zip(&values)
                .map(|(n, v)| json!([n, value_json(v)]))
                .collect::<Vec<_>>()
        ]));
        let observed = Observed {
            inner: host(role),
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        runners.insert(
            role.into(),
            Runner::new(&admitted, "main", role, "test", observed, values)
                .unwrap_or_else(|e| panic!("{}", e.error)),
        );
    }
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let report = drive_with_decoder(&mut schedule, &mut runners, &mut trace.clone(), &decoder);
    let native = trace.snapshot();
    let mut answers = Vec::new();
    let mut receiving = Vec::new();
    for event in &native {
        if event[0] == "response" && event[1][2].as_str().unwrap().starts_with("pcs.") {
            answers.push(json!([event[1], commitments::reply(&keys, &event[1])]));
        }
        if event[0] == "send"
            && matches!(
                event[4][0].as_str().unwrap().split(':').next(),
                Some("commitment" | "proof")
            )
        {
            let request = json!([
                "zkc.reference-primitive/2",
                event[1],
                "validate",
                ["multilinear.kzg.bls12-381/1"],
                [],
                [event[4]]
            ]);
            answers.push(json!([request, commitments::reply(&keys, &request)]));
            if let Some(identity) = decoder.selected(event[1][5].as_str().unwrap()) {
                let mut location = event[1].clone();
                location[6] = json!("V");
                receiving.push(json!([
                    ["receive", location, event[2], "P", event[4][0]],
                    commitment_identity(identity)
                ]));
            }
        }
    }
    let authorized: Vec<_> = keys
        .iter()
        .map(|k| commitment_identity(k.verifier_key().metadata()))
        .collect();
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        supplied,
        [],
        answers,
        [],
        [
            "zkc.reference-setups/1",
            [["P", authorized], ["V", authorized]],
            receiving
        ]
    ]);
    let result = fixture.reference(&inputs);
    let events: Vec<_> = result[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] != "external")
        .cloned()
        .collect();
    assert_eq!(events, native);
    if mode == 0 {
        let JointOutcome::Returned(values) = report.outcome else {
            panic!("{:?}", report.outcome)
        };
        assert_eq!(
            result[3],
            json!([
                "returned",
                values["V"].iter().map(value_json).collect::<Vec<_>>()
            ])
        );
        assert_eq!(report.wire.messages, 8);
        assert_eq!(result[3][1], json!([["bool", "true"], ["bool", "true"]]));
        // Run the independent open verifier against the actual native verifier's
        // trace. Its peer replies carry no prover key or private opening state.
        let verifier_events: Vec<_> = native
            .iter()
            .filter(|event| {
                let location = if event[0] == "request" || event[0] == "response" {
                    &event[1][1]
                } else {
                    &event[1]
                };
                location[6] == "V"
            })
            .cloned()
            .collect();
        let mut replies = Vec::new();
        let mut services = Vec::new();
        for event in &verifier_events {
            if event[0] == "receive" {
                replies.push(json!([
                    ["receive", event[1], event[2], event[3], event[4][0]],
                    event[4]
                ]));
                if matches!(
                    event[4][0].as_str().unwrap().split(':').next(),
                    Some("commitment" | "proof")
                ) {
                    let request = json!([
                        "zkc.reference-primitive/2",
                        event[1],
                        "validate",
                        ["multilinear.kzg.bls12-381/1"],
                        [],
                        [event[4]]
                    ]);
                    services.push(json!([request, commitments::reply(&keys, &request)]));
                }
            } else if event[0] == "response" && event[1][2] == "pcs.check" {
                services.push(json!([event[1], commitments::reply(&keys, &event[1])]));
            }
        }
        let mut verifier = inputs.clone();
        verifier[3] = json!([inputs[3][1]]);
        verifier[5] = json!(services);
        verifier[6] = json!(replies);
        verifier[7][1] = json!([inputs[7][1][1]]);
        let (success, open) = fixture.reference_as(&verifier, Some("V"));
        assert!(success, "{open}");
        assert_eq!(open[3], result[3]);
        let observed: Vec<_> = open[4]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e[0] != "external")
            .cloned()
            .collect();
        assert_eq!(observed, verifier_events);
        let mut wrong = verifier;
        wrong[6][0][0][2] = json!("wrong-schema");
        assert_eq!(
            fixture.reference_as(&wrong, Some("V")).1[3][1],
            "reply-origin"
        );
    } else {
        let JointOutcome::Failed(error) = report.outcome else {
            panic!("host decode failure")
        };
        let detail = if mode == 2 {
            "receiving-setup-missing"
        } else if rank == 2 {
            "key-mismatch"
        } else {
            "arity-mismatch"
        };
        assert_eq!(error, format!("refused:{detail}"));
        assert_eq!(result[3][0], "refused");
        assert_eq!(result[3][1], detail);
        assert_eq!(result[3][2][5], "commit_a");
        assert_eq!(result[3][2][6], "V");
        assert_eq!(report.wire.messages, 3);
    }
    for runner in runners.values() {
        assert_eq!(runner.backend().inner.active_frames(), 0);
    }
}

#[test]
fn receiving_selects_an_intended_authorized_setup() {
    for rank in [1, 2] {
        for mode in 0..3 {
            compare(rank, mode);
        }
    }
}
