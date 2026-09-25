use std::collections::{BTreeMap, VecDeque};
use zkc_backends::{
    RistrettoScalar,
    choices::{Limits, Namespace, Sampler, Source, Usage},
};
use zkc_runtime::interactive::BackendError;

struct Tapes(BTreeMap<Namespace, VecDeque<[u8; 32]>>);
impl Source for Tapes {
    fn draw(&mut self, key: &Namespace) -> Result<[u8; 32], BackendError> {
        self.0
            .get_mut(key)
            .and_then(VecDeque::pop_front)
            .ok_or_else(|| BackendError::new("exhausted:tape"))
    }
}
fn key(role: &str, purpose: &str) -> Namespace {
    Namespace::new(role, purpose).unwrap()
}
fn scalar(n: u64) -> [u8; 32] {
    RistrettoScalar::from(n).to_bytes()
}

#[test]
fn separate_namespaces_and_raw_vs_logical_progress() {
    let prover = key("P", "blinding");
    let verifier = key("V", "batch");
    let tapes = Tapes(BTreeMap::from([
        (
            prover.clone(),
            VecDeque::from([[255; 32], [0; 32], scalar(7), scalar(9)]),
        ),
        (verifier.clone(), VecDeque::from([scalar(11)])),
    ]));
    let mut sampler = Sampler::new(
        tapes,
        [
            (prover.clone(), Limits { logical: 2, raw: 4 }),
            (verifier.clone(), Limits { logical: 1, raw: 1 }),
        ],
    )
    .unwrap();
    assert_eq!(
        sampler.monero_nonzero_scalar(&prover).unwrap(),
        RistrettoScalar::from(7u64)
    );
    assert_eq!(
        sampler.usage(&prover).unwrap(),
        Usage {
            logical_requests: 1,
            raw_requests: 3,
            raw_completed: 3,
            accepted: 1
        }
    );
    assert_eq!(sampler.usage(&verifier).unwrap(), Usage::default());
    assert_eq!(
        sampler.monero_nonzero_scalar(&verifier).unwrap(),
        RistrettoScalar::from(11u64)
    );
    assert_eq!(
        sampler.monero_nonzero_scalar(&prover).unwrap(),
        RistrettoScalar::from(9u64)
    );
    assert_eq!(
        sampler.monero_nonzero_scalar(&prover).unwrap_err().code,
        "exhausted:choice-logical-budget"
    );
    assert_eq!(sampler.usage(&prover).unwrap().raw_requests, 4);
    // A well-formed namespace that no stream was installed for.
    let missing = key("P", "batch");
    assert_eq!(
        sampler.monero_nonzero_scalar(&missing).unwrap_err().code,
        "refused:choice-namespace"
    );
    assert_eq!(
        sampler.usage(&missing).unwrap_err().code,
        "refused:choice-namespace"
    );
}

#[test]
fn raw_exhaustion_and_provider_failure_preserve_consumption() {
    let namespace = key("P", "blinding");
    // A zero draw is rejected and spends the one raw draw; an empty tape is
    // the provider's own failure, reported as it gave it.
    for (tape, first) in [
        (VecDeque::from([[0; 32]]), "exhausted:choice-raw-budget"),
        (VecDeque::new(), "exhausted:tape"),
    ] {
        let mut sampler = Sampler::new(
            Tapes(BTreeMap::from([(namespace.clone(), tape)])),
            [(namespace.clone(), Limits { logical: 2, raw: 1 })],
        )
        .unwrap();
        assert_eq!(
            sampler.monero_nonzero_scalar(&namespace).unwrap_err().code,
            first
        );
        let before = sampler.usage(&namespace).unwrap();
        assert_eq!(
            (
                before.logical_requests,
                before.raw_requests,
                before.accepted
            ),
            (1, 1, 0)
        );
        assert_eq!(
            sampler.monero_nonzero_scalar(&namespace).unwrap_err().code,
            "exhausted:choice-raw-budget"
        );
        assert_eq!(sampler.usage(&namespace).unwrap().raw_requests, 1);
    }
}

#[test]
fn stream_installation_rejects_collisions_and_malformed_names() {
    let k = key("P", "blinding");
    let limits = Limits { logical: 1, raw: 1 };
    let refusal = |streams: Vec<(Namespace, Limits)>| {
        Sampler::new(Tapes(BTreeMap::new()), streams)
            .err()
            .expect("stream table refused")
            .code
    };
    assert_eq!(
        refusal(vec![(k.clone(), limits), (k, limits)]),
        "refused:choice-streams"
    );
    let many = (0..1025)
        .map(|i| (key("P", &format!("s{i}")), limits))
        .collect::<Vec<_>>();
    assert_eq!(refusal(many), "refused:choice-streams");
    for s in ["", "a/b", "with space"] {
        assert_eq!(
            Namespace::new("P", s).unwrap_err().code,
            "refused:choice-namespace"
        );
        assert_eq!(
            Namespace::new(s, "blinding").unwrap_err().code,
            "refused:choice-namespace"
        );
    }
}

#[test]
fn logical_and_raw_budgets_are_refused_before_any_draw() {
    let namespace = key("P", "blinding");
    for (limits, expected) in [
        (
            Limits { logical: 0, raw: 1 },
            "exhausted:choice-logical-budget",
        ),
        (Limits { logical: 1, raw: 0 }, "exhausted:choice-raw-budget"),
    ] {
        let mut sampler = Sampler::new(
            Tapes(BTreeMap::from([(
                namespace.clone(),
                VecDeque::from([scalar(7)]),
            )])),
            [(namespace.clone(), limits)],
        )
        .unwrap();
        assert_eq!(
            sampler.monero_nonzero_scalar(&namespace).unwrap_err().code,
            expected
        );
        assert_eq!(sampler.usage(&namespace).unwrap().raw_requests, 0);
    }
}

#[test]
fn archived_upstream_raw_tapes_produce_the_exact_accepted_scalar_tapes() {
    let corpus: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/choices/monero.json")).unwrap();
    let decode = |v: &serde_json::Value| {
        let s = v.as_str().unwrap();
        assert_eq!(s.len(), 64);
        std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
    };
    for case in corpus["cases"].as_array().unwrap() {
        let raw = case["raw"].as_array().unwrap();
        let expected = case["accepted"].as_array().unwrap();
        let namespace = key("P", "blinding");
        let tapes = Tapes(BTreeMap::from([(
            namespace.clone(),
            raw.iter().map(decode).collect(),
        )]));
        let mut sampler = Sampler::new(
            tapes,
            [(
                namespace.clone(),
                Limits {
                    logical: expected.len() as u64,
                    raw: raw.len() as u64,
                },
            )],
        )
        .unwrap();
        for scalar in expected {
            assert_eq!(
                sampler
                    .monero_nonzero_scalar(&namespace)
                    .unwrap()
                    .to_bytes(),
                decode(scalar),
                "{}",
                case["case"]
            );
        }
        assert_eq!(
            sampler.usage(&namespace).unwrap(),
            Usage {
                logical_requests: expected.len() as u64,
                raw_requests: raw.len() as u64,
                raw_completed: raw.len() as u64,
                accepted: expected.len() as u64,
            }
        );
    }
}

#[test]
fn exact_order_and_rejection_threshold_boundaries() {
    // Independent little-endian subgroup order; construct 15*l using integer
    // carries rather than copying the implementation's rejection constant.
    let order = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
    ];
    let mut carry = 0u16;
    let threshold: [u8; 32] = order.map(|byte| {
        let n = u16::from(byte) * 15 + carry;
        carry = n >> 8;
        n as u8
    });
    assert_eq!(carry, 0);
    let mut below = threshold;
    below[0] -= 1;
    let mut above = threshold;
    above[0] += 1;
    let mut order_plus_one = order;
    order_plus_one[0] += 1;
    for (raw, expected, draws) in [
        ([0; 32], RistrettoScalar::from(7u64), 2),
        (order, RistrettoScalar::from(7u64), 2),
        (order_plus_one, RistrettoScalar::ONE, 1),
        (below, -RistrettoScalar::ONE, 1),
        (threshold, RistrettoScalar::from(7u64), 2),
        (above, RistrettoScalar::from(7u64), 2),
        ([255; 32], RistrettoScalar::from(7u64), 2),
    ] {
        let namespace = key("P", "blinding");
        let tapes = Tapes(BTreeMap::from([(
            namespace.clone(),
            VecDeque::from([raw, scalar(7)]),
        )]));
        let mut sampler =
            Sampler::new(tapes, [(namespace.clone(), Limits { logical: 1, raw: 2 })]).unwrap();
        assert_eq!(sampler.monero_nonzero_scalar(&namespace).unwrap(), expected);
        assert_eq!(
            sampler.usage(&namespace).unwrap(),
            Usage {
                logical_requests: 1,
                raw_requests: draws,
                raw_completed: draws,
                accepted: 1,
            }
        );
    }
}
