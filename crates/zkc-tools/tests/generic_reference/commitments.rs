//! PCS services use pinned real keys and original mathematical operands. Lean
//! constructs custody and computes evaluations; the service returns proof bytes.
use super::*;
use std::sync::Arc;
use zkc_arkworks::{Keys, Table};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, PublicInputs, SetupRegistry};

fn unhex(value: &Json) -> Vec<u8> {
    zkc_test_support::unhex(value.as_str().unwrap())
}
fn fields(value: &Json) -> Vec<Scalar> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|v| zkc_arkworks::parse_decimal(v.as_str().unwrap()).unwrap())
        .collect()
}
fn payload(value: &Json, kind: u8) -> Vec<u8> {
    let bytes = unhex(value);
    assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 1, kind]);
    bytes[6..].to_vec()
}
fn key<'a>(keys: &'a [&Keys], identity: &Json) -> &'a Keys {
    keys.iter()
        .find(|k| commitment_identity(k.verifier_key().metadata()) == *identity)
        .unwrap()
}

/// This adapter deliberately discards native outputs. It interprets the exact
/// request with the authorized upstream keys, returning only the service result.
pub(super) fn reply(keys: &[&Keys], request: &Json) -> Json {
    let args = &request[5];
    let bounds = Policy::default().ark_bounds();
    let values = match request[2].as_str().unwrap() {
        "validate" => {
            let kind = args[0][0].as_str().unwrap().split(':').next().unwrap();
            let bytes = payload(&args[0][1], if kind == "commitment" { 6 } else { 7 });
            assert!(keys.iter().any(|key| {
                if kind == "commitment" {
                    key.verifier_key()
                        .decode_commitment(&bytes, &bounds)
                        .is_ok()
                } else {
                    key.verifier_key().decode_proof(&bytes, &bounds).is_ok()
                }
            }));
            vec![]
        }
        "pcs.commit" => {
            let k = key(keys, &args[0][1]);
            let table = Table::from_logical(&fields(&args[1][1][1]), &bounds).unwrap();
            let committed = k.prover_key().commit(&table).unwrap();
            vec![value_json(&Value::Commitment(Arc::new(
                committed.commitment().clone(),
            )))]
        }
        "pcs.open" => {
            let state = &args[0][1];
            let k = key(keys, &state[0]);
            let table = Table::from_logical(&fields(&state[1][1]), &bounds).unwrap();
            let original = k.prover_key().commit(&table).unwrap();
            assert_eq!(
                original.commitment().to_bytes(&bounds).unwrap(),
                payload(&state[2], 6)
            );
            let (_evaluation, proof) = original.open(&fields(&args[1][1])).unwrap();
            vec![value_json(&Value::Proof(Arc::new(proof)))]
        }
        "pcs.check" => {
            let k = key(keys, &args[0][1]).verifier_key();
            let commitment = k
                .decode_commitment(&payload(&args[1][1], 6), &bounds)
                .unwrap();
            let proof = k.decode_proof(&payload(&args[4][1], 7), &bounds).unwrap();
            let value = zkc_arkworks::parse_decimal(args[3][1].as_str().unwrap()).unwrap();
            let accepted = k
                .check(&commitment, &fields(&args[2][1]), value, &proof)
                .unwrap();
            vec![value_json(&Value::Bool(accepted))]
        }
        other => panic!("unexpected PCS service {other}"),
    };
    json!(["ok", values])
}

fn compare(
    fixture: &Fixture,
    keys: &[&Keys],
    verifier: usize,
    cells: &[u64],
    first: &[u64],
    second: &[u64],
) {
    let policy = Policy::default();
    let inner = NativeBackend::with_setups(
        policy,
        EntryPolicy::new(
            Domain::new("P", "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        SetupRegistry::new(
            keys.iter().map(|k| k.verifier_key().clone()).collect(),
            &policy,
        )
        .unwrap(),
    )
    .unwrap();
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted = admit_physical(&fixture.source, &fixture.candidate, &inner, &checker).unwrap();
    let values = vec![
        Value::ProverKey(Arc::new(keys[0].prover_key().clone())),
        Value::VerifierKey(Arc::new(keys[verifier].verifier_key().clone())),
        Value::Table(
            Table::from_logical(
                &cells.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
                &Policy::default().ark_bounds(),
            )
            .unwrap()
            .into(),
        ),
        Value::Point(
            first
                .iter()
                .copied()
                .map(Scalar::from)
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Point(
            second
                .iter()
                .copied()
                .map(Scalar::from)
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Field(Scalar::from(11)),
    ];
    let ports: Vec<_> = ["key", "verifier", "table", "first", "second", "r"]
        .into_iter()
        .zip(&values)
        .map(|(n, v)| json!([n, value_json(v)]))
        .collect();
    let trace = Trace::new(&fixture.source);
    let observed = Observed {
        inner,
        source_map: admitted.source_map().unwrap().clone(),
        events: trace.clone(),
        conversions: 0,
    };
    let mut runner = Runner::new(&admitted, "main", "P", "test", observed, values)
        .unwrap_or_else(|e| panic!("{}", e.error));
    let terminal = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
            action => panic!("unexpected {action:?}"),
        }
    };
    let native = trace.snapshot();
    // Only successful native operations reach their cryptographic service after
    // logical preconditions. The service recomputes each answer from its inputs.
    let answers: Vec<_> = native
        .iter()
        .filter(|e| {
            e[0] == "response"
                && e[1][2].as_str().unwrap().starts_with("pcs.")
                && e[1][2] != "pcs.equal"
        })
        .map(|e| json!([e[1], reply(keys, &e[1])]))
        .collect();
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [["P", ports]],
        [],
        answers,
        [],
        [
            "zkc.reference-setups/1",
            [[
                "P",
                keys.iter()
                    .map(|k| commitment_identity(k.verifier_key().metadata()))
                    .collect::<Vec<_>>()
            ]],
            []
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
    match terminal {
        Action::Returned(values) => {
            assert_eq!(
                result[3],
                json!([
                    "returned",
                    values.iter().map(value_json).collect::<Vec<_>>()
                ])
            );
            assert_eq!(runner.backend().conversions, 2);
        }
        Action::Stopped(stop) => {
            let StopKind::Backend(error) = &stop.kind else {
                panic!("backend stop")
            };
            let (reason, detail) = error.code.split_once(':').unwrap();
            assert_eq!(result[3][0], reason);
            assert_eq!(result[3][1], detail);
            assert_stop_location(&trace, &stop, &result[3][2], true);
            assert_eq!(runner.usage().live_value_bytes, 0);
        }
        _ => unreachable!(),
    }
    assert_eq!(result[5], json!([]));
    assert_eq!(runner.backend().inner.active_frames(), 0);

    if result[3][0] == "returned" {
        // A changed original must not reuse the cached response for commit.
        let mut changed = inputs.clone();
        changed[3][0][1][2][1][1][1][0] = json!("1234");
        let pending = fixture.reference(&changed);
        assert_eq!(pending[3][0], "pending-primitive");
        // Providers cannot install arbitrary custody by returning a second value.
        let mut forged = inputs.clone();
        forged[5][0][1][1]
            .as_array_mut()
            .unwrap()
            .push(json!(["opening_state:multilinear.kzg.bls12-381/1", []]));
        let refused = fixture.reference(&forged);
        assert_eq!(refused[3][1], "reference-value-not-supported");
    }
}

#[test]
fn commitments_retain_originals_and_check_key_identity() {
    let fixture = Fixture::from_fixture("generic-opening-reuse.pir");
    for rank in 1..=3 {
        for seed in [0, 7] {
            let a = Keys::setup_for_development(rank, &Policy::default().ark_bounds()).unwrap();
            let b = Keys::setup_for_development(rank, &Policy::default().ark_bounds()).unwrap();
            let cells: Vec<_> = (0..1u64 << rank).map(|i| i * i + seed).collect();
            let first: Vec<_> = (0..rank as u64).map(|i| 2 + i).collect();
            let second: Vec<_> = (0..rank as u64).map(|i| 5 + 2 * i).collect();
            compare(&fixture, &[&a, &b], 0, &cells, &first, &second);
            compare(&fixture, &[&b, &a], 0, &cells, &first, &second);
        }
    }
    let a = Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let b = Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let c = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    compare(&fixture, &[&a], 0, &[1, 2], &[2, 3], &[5, 7]);
    compare(&fixture, &[&a], 0, &[0, 1, 4, 9], &[2], &[5, 7]);
    compare(&fixture, &[&a], 0, &[0, 1, 4, 9], &[2, 3], &[5]);
    compare(&fixture, &[&a, &b], 1, &[0, 1, 4, 9], &[2, 3], &[5, 7]);
    compare(&fixture, &[&a, &c], 1, &[0, 1, 4, 9], &[2, 3], &[5, 7]);

    let mut false_claim = Fixture::from_fixture("generic-opening-reuse.pir");
    let mut source: Json = serde_json::from_slice(&false_claim.source).unwrap();
    source[3][3][0][7][4][4][3] = json!("r");
    false_claim.set_source(&source);
    compare(&false_claim, &[&a], 0, &[0, 1, 4, 9], &[2, 3], &[5, 7]);
}
