//! Installed block execution against independent raw Keccak equations.
#[path = "domains/support.rs"]
mod support;
use serde_json::json;
use sha3::{Digest, Keccak256};
use support::{Controlled, backend, domain, one, tree};
use zkc_cpu::{Capability, CapabilityObservation, CpuBackend, CpuOperation, Policy, Value};
use zkc_runtime::vm::{
    Backend, BackendError, CallContext, Frame, FrameExit, FrameKind, Identity, Invocation,
    OperationBinding,
};

const SUITES: [Identity; 2] = [
    Identity::HashChainKeccak256KoalaBearExt4,
    Identity::HashChainKeccak256KoalaBearExt8,
];
const BLOCK: &str = "transcript.native.indexed.indices";
const SEARCH: &str = "transcript.native.indexed.indices.search";
const CHECK: &str = "transcript.native.indexed.indices.gated";
fn binding(suite: Identity, contract: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: vec![suite.name().into()],
        implementation: format!("plonky3/{contract}"),
        physical_arguments: vec![],
    }
}
fn root() -> Vec<u8> {
    tree(&json!(["native-index-block-fixture"]))
}
fn origin(suite: Identity, template: bool, repeated: bool, coordinates: &[u64]) -> Vec<u8> {
    tree(&json!([
        if template {
            "zkc.native-origin-template/0"
        } else {
            "zkc.native-origin/0"
        },
        "main",
        if repeated {
            json!([["repeat", "loop", "body"]])
        } else {
            json!([])
        },
        coordinates.iter().map(u64::to_string).collect::<Vec<_>>(),
        [
            "query",
            "Source",
            "queries",
            "input_0",
            format!("random.{}/0", suite.scalar_field().unwrap().name()),
            "indices",
            "V"
        ]
    ]))
}
fn attrs(suite: Identity, n: u64, q: usize, b: Option<u8>, repeated: bool) -> Vec<String> {
    let mut result = vec![
        zkc_test_support::hex(&origin(suite, true, repeated, &[])),
        n.to_string(),
        q.to_string(),
    ];
    result.extend(b.map(|b| b.to_string()));
    result
}
fn token(value: &Value) -> &Capability {
    let Value::Transcript(token) = value else {
        panic!("transcript")
    };
    token
}
fn indices(value: &Value) -> &[u64] {
    let Value::Indices(indices) = value else {
        panic!("indices")
    };
    indices
}
fn witness(values: &[Value]) -> u64 {
    let Value::Index(w) = values[1] else {
        panic!("witness")
    };
    w
}
fn issue(backend: &mut CpuBackend, suite: Identity, budget: u64) -> Value {
    backend
        .issue_transcript_for(suite, domain(), budget, &root())
        .unwrap()
}
#[allow(clippy::too_many_arguments)]
fn run(
    suite: Identity,
    contract: &str,
    attributes: &[String],
    p: Policy,
    w: u64,
    coordinates: &[u64],
    budget: u64,
    output_limit: Option<usize>,
) -> (Result<Vec<Value>, String>, Controlled, Value) {
    let mut inner = backend(p);
    let old = issue(&mut inner, suite, budget);
    let mut args = vec![old.clone()];
    if contract == CHECK {
        args.push(Value::Index(w));
    }
    args.push(Value::Indices(coordinates.to_vec().into()));
    let mut controlled = Controlled::new(inner);
    controlled.output_limit = output_limit;
    let (result, controlled) = one(
        controlled,
        binding(suite, contract),
        &attributes.iter().map(String::as_str).collect::<Vec<_>>(),
        args,
    );
    (result, controlled, old)
}

// Deliberately no KeccakChain, transcript frame helper or search kernel in this
// reference. The installed provider and numerical search cannot supply answers.
fn hash(bytes: &[u8]) -> [u8; 32] {
    Keccak256::digest(bytes).into()
}
fn frame(tag: u8, label: &[u8], data: &[u8]) -> Vec<u8> {
    [
        vec![tag],
        (label.len() as u64).to_be_bytes().to_vec(),
        label.to_vec(),
        (data.len() as u64).to_be_bytes().to_vec(),
        data.to_vec(),
    ]
    .concat()
}
fn absorb(state: &[u8; 32], label: &[u8], data: &[u8]) -> [u8; 32] {
    hash(
        &[
            b"zkc.hash-chain.absorb/0\0".as_slice(),
            state,
            &frame(1, label, data),
        ]
        .concat(),
    )
}
fn initial(suite: Identity) -> [u8; 32] {
    hash(
        &[
            b"zkc.hash-chain.bind/0\0".to_vec(),
            frame(0, b"domain", b"zkc.artifact/0"),
            frame(0, b"suite", suite.name().as_bytes()),
            frame(1, b"binding", &root()),
        ]
        .concat(),
    )
}
fn prefix(start: &[u8; 32], occurrence: &[u8], n: u64, q: usize, b: u8) -> [u8; 32] {
    let mut s = absorb(start, b"origin", occurrence);
    s = absorb(&s, b"bound", &n.to_le_bytes());
    s = absorb(&s, b"count", &(q as u64).to_le_bytes());
    if b != 0 {
        s = absorb(&s, b"difficulty", &u64::from(b).to_le_bytes());
    }
    s
}
fn request(s: &[u8; 32], label: &[u8], length: usize) -> (Vec<u8>, [u8; 32]) {
    let length_bytes = (length as u64).to_be_bytes();
    let framed = frame(2, label, &length_bytes);
    let mut answer = Vec::new();
    for counter in 0..length.div_ceil(32) {
        answer.extend(hash(
            &[
                b"zkc.hash-chain.request/0\0".as_slice(),
                s,
                &framed,
                &(counter as u64).to_be_bytes(),
            ]
            .concat(),
        ));
    }
    answer.truncate(length);
    (
        answer,
        hash(&[b"zkc.hash-chain.absorb/0\0".as_slice(), s, &framed].concat()),
    )
}
fn answer(prefix: &[u8; 32], q: usize, b: u8, w: u64) -> (Vec<u8>, [u8; 32]) {
    if b == 0 {
        return request(prefix, b"indices", 8 * q);
    }
    let wire = [b"ZKCV\0\x1f".as_slice(), &w.to_le_bytes()].concat();
    request(
        &absorb(prefix, b"gate-witness", &wire),
        b"gated-indices",
        8 + 8 * q,
    )
}
fn accepts(bytes: &[u8], b: u8) -> bool {
    u64::from_le_bytes(bytes[..8].try_into().unwrap()).trailing_zeros() >= u32::from(b)
}
fn expected_indices(bytes: &[u8], n: u64, b: u8) -> Vec<u64> {
    bytes[if b == 0 { 0 } else { 8 }..]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|v| u64::from_le_bytes(*v) & (n - 1))
        .collect()
}

#[test]
fn installed_search_and_check_match_raw_equations_and_actual_occurrences() {
    for suite in SUITES {
        for (n, q, b, coordinates) in [
            (1, 9, 4, vec![]),
            (1 << 63, 7, 5, vec![11]),
            (16, 13, 3, vec![12]),
        ] {
            let repeated = !coordinates.is_empty();
            let a = attrs(suite, n, q, Some(b), repeated);
            let p = prefix(
                &initial(suite),
                &origin(suite, false, repeated, &coordinates),
                n,
                q,
                b,
            );
            let expected_w = (0..1 << 16)
                .find(|w| accepts(&answer(&p, q, b, *w).0, b))
                .unwrap();
            let (raw, successor) = answer(&p, q, b, expected_w);
            let (out, backend, old) = run(
                suite,
                SEARCH,
                &a,
                Policy::default(),
                0,
                &coordinates,
                2,
                Some(8 * q + 1280),
            );
            let out = out.unwrap();
            assert_eq!(witness(&out), expected_w);
            assert_eq!(indices(&out[0]), expected_indices(&raw, n, b));
            if n == 1 << 63 {
                assert!(
                    indices(&out[0])
                        .iter()
                        .any(|index| *index > u64::from(u32::MAX))
                );
            }
            if n == 1 {
                assert_eq!(indices(&out[0]), vec![0; q]);
            }
            let state = backend.inner.observe(token(&old)).unwrap();
            assert_eq!(
                (state.generation, state.draw_count, state.budget),
                (1, 1, 1)
            );
            assert_eq!(token(out.last().unwrap()).generation(), 1);
            // A second installed block exposes the exact committed successor.
            let next_attrs = attrs(suite, n, q, None, repeated);
            let (next, next_backend) = one(
                backend.inner,
                binding(suite, BLOCK),
                &next_attrs.iter().map(String::as_str).collect::<Vec<_>>(),
                vec![
                    out.last().unwrap().clone(),
                    Value::Indices(coordinates.clone().into()),
                ],
            );
            let next_prefix = prefix(
                &successor,
                &origin(suite, false, repeated, &coordinates),
                n,
                q,
                0,
            );
            assert_eq!(
                indices(&next.unwrap()[0]),
                expected_indices(&answer(&next_prefix, q, 0, 0).0, n, 0)
            );
            let state = next_backend.observe(token(&old)).unwrap();
            assert_eq!(
                (state.generation, state.draw_count, state.budget),
                (2, 2, 0)
            );
            let (checked, _, _) = run(
                suite,
                CHECK,
                &a,
                Policy::default(),
                expected_w,
                &coordinates,
                2,
                Some(8 * q + 768),
            );
            assert_eq!(indices(&checked.unwrap()[0]), indices(&out[0]));
            // Verification also accepts a later valid witness, independently of
            // honest earliest-witness policy or its zero attempt ceiling.
            let later = (expected_w + 1..1 << 16)
                .find(|w| accepts(&answer(&p, q, b, *w).0, b))
                .unwrap();
            let (checked, _, _) = run(
                suite,
                CHECK,
                &a,
                Policy {
                    max_search_attempts: 0,
                    ..Policy::default()
                },
                later,
                &coordinates,
                1,
                None,
            );
            assert_eq!(
                indices(&checked.unwrap()[0]),
                expected_indices(&answer(&p, q, b, later).0, n, b)
            );
        }
    }
}

#[test]
fn zero_difficulty_is_exact_ungated_equation_with_zero_witness_and_no_search() {
    for suite in SUITES {
        for (n, q) in [(1, 5), (1 << 63, 11)] {
            let p = Policy {
                max_search_attempts: 0,
                ..Policy::default()
            };
            let ordinary = attrs(suite, n, q, None, false);
            let gated = attrs(suite, n, q, Some(0), false);
            let (reference, successor) = answer(
                &prefix(&initial(suite), &origin(suite, false, false, &[]), n, q, 0),
                q,
                0,
                0,
            );
            let mut results = Vec::new();
            for (contract, attributes) in [(BLOCK, &ordinary), (SEARCH, &gated), (CHECK, &gated)] {
                let (out, checked, _) = run(suite, contract, attributes, p, 0, &[], 2, None);
                let out = out.unwrap();
                if contract == SEARCH {
                    assert_eq!(witness(&out), 0);
                }
                results.push(indices(&out[0]).to_vec());
                let (next, _) = one(
                    checked.inner,
                    binding(suite, BLOCK),
                    &ordinary.iter().map(String::as_str).collect::<Vec<_>>(),
                    vec![out.last().unwrap().clone(), Value::Indices(vec![].into())],
                );
                let next_prefix = prefix(&successor, &origin(suite, false, false, &[]), n, q, 0);
                assert_eq!(
                    indices(&next.unwrap()[0]),
                    expected_indices(&answer(&next_prefix, q, 0, 0).0, n, 0)
                );
            }
            assert!(
                results
                    .iter()
                    .all(|v| *v == expected_indices(&reference, n, 0))
            );
            let (out, backend, old) = run(suite, CHECK, &gated, p, 1, &[], 1, None);
            assert_eq!(out.unwrap_err(), "refused:gate-witness");
            assert_eq!(backend.inner.observe(token(&old)).unwrap().generation, 0);
        }
    }
}

#[test]
fn failures_before_commit_leave_authoritative_counters_unchanged() {
    let suite = SUITES[0];
    let q = 9;
    let attributes = attrs(suite, 16, q, Some(64), false);
    for (p, limit, budget, expected) in [
        (
            Policy {
                max_search_attempts: 0,
                max_numerical_work: 0,
                ..Policy::default()
            },
            None,
            1,
            "exhausted:search-attempts",
        ),
        (
            Policy {
                max_search_attempts: 1,
                ..Policy::default()
            },
            None,
            1,
            "exhausted:search-attempts",
        ),
        (
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
            None,
            1,
            "exhausted:numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: 8 * q + 1280 + 8 * q + (8 + 8 * q) - 1,
                ..Policy::default()
            },
            None,
            1,
            "exhausted:numerical-bytes",
        ),
        (
            Policy::default(),
            Some(8 * q + 1280 - 1),
            1,
            "exhausted:output-bytes",
        ),
        (Policy::default(), None, 0, "exhausted:resource-budget"),
    ] {
        let (out, backend, old) = run(suite, SEARCH, &attributes, p, 0, &[], budget, limit);
        assert_eq!(out.unwrap_err(), expected);
        let state = backend.inner.observe(token(&old)).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (0, 0, budget)
        );
        assert!(backend.outputs.is_empty());
    }
}

#[test]
fn full_replay_is_precharged_and_b64_check_commits_before_rejection() {
    for suite in SUITES {
        let a = attrs(suite, 1 << 63, 13, Some(64), false);
        let (out, backend, old) = run(suite, CHECK, &a, Policy::default(), 0, &[], 2, None);
        assert_eq!(out.unwrap_err(), "rejected:require");
        assert!(backend.outputs.is_empty());
        let state = backend.inner.observe(token(&old)).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (1, 1, 1)
        );
        // P + ceil((8+8Q)/32) + 5; independent framing lengths.
        let work = ((79 + origin(suite, false, false, &[]).len()) / 136 + 1) as u64
            + (8 + 8 * 13u64).div_ceil(32)
            + 5;
        let (out, backend, old) = run(
            suite,
            CHECK,
            &a,
            Policy {
                max_numerical_work: work - 1,
                ..Policy::default()
            },
            0,
            &[],
            1,
            None,
        );
        assert_eq!(out.unwrap_err(), "exhausted:numerical-work");
        assert_eq!(backend.inner.observe(token(&old)).unwrap().generation, 0);
        let (out, _, _) = run(
            suite,
            CHECK,
            &a,
            Policy {
                max_numerical_work: work,
                ..Policy::default()
            },
            0,
            &[],
            1,
            None,
        );
        assert_eq!(out.unwrap_err(), "rejected:require");
    }
}

#[test]
fn search_and_live_replay_share_one_work_ceiling() {
    for suite in SUITES {
        let q = 2048;
        let occurrence = origin(suite, false, false, &[]);
        let p = prefix(&initial(suite), &occurrence, 16, q, 1);
        let w = (0..1024)
            .find(|w| accepts(&answer(&p, q, 1, *w).0, 1))
            .unwrap();
        let replay =
            ((79 + occurrence.len()) / 136 + 1) as u64 + (8 + 8 * q as u64).div_ceil(32) + 5;
        let policy = Policy {
            max_numerical_work: replay,
            ..Policy::default()
        };
        let a = attrs(suite, 16, q, Some(1), false);
        let (verified, _, _) = run(suite, CHECK, &a, policy, w, &[], 1, None);
        assert!(verified.is_ok());
        let (searched, backend, old) = run(suite, SEARCH, &a, policy, 0, &[], 1, None);
        assert_eq!(searched.unwrap_err(), "exhausted:numerical-work");
        assert_eq!(backend.inner.observe(token(&old)).unwrap().generation, 0);
        assert!(backend.outputs.is_empty());
    }
}

#[test]
fn ungated_work_and_freeze_overlap_accept_exact_limits_and_refuse_one_short() {
    let suite = SUITES[0];
    let q = 7;
    let a = attrs(suite, 1, q, None, false);
    let work = ((79 + origin(suite, false, false, &[]).len()) / 136 + 1) as u64
        + (8 * q as u64).div_ceil(32)
        + 3;
    let retained = 8 * q + 768;
    let memory = retained + 8 * q + 8 * q;
    for (work_limit, memory_limit, output_limit, expected) in [
        (work, memory, retained, None),
        (work - 1, memory, retained, Some("exhausted:numerical-work")),
        (
            work,
            memory - 1,
            retained,
            Some("exhausted:numerical-bytes"),
        ),
        (work, memory, retained - 1, Some("exhausted:output-bytes")),
    ] {
        let (out, backend, old) = run(
            suite,
            BLOCK,
            &a,
            Policy {
                max_numerical_work: work_limit,
                max_numerical_bytes: memory_limit,
                ..Policy::default()
            },
            0,
            &[],
            1,
            Some(output_limit),
        );
        if let Some(expected) = expected {
            assert_eq!(out.unwrap_err(), expected);
            assert_eq!(backend.inner.observe(token(&old)).unwrap().generation, 0);
            assert!(backend.outputs.is_empty());
        } else {
            assert_eq!(indices(&out.unwrap()[0]), vec![0; q]);
        }
    }
}

#[test]
fn only_explicit_suites_and_checked_backend_attempt_policies_are_installed() {
    let cpu = backend(Policy::default());
    for suite in [
        Identity::HashChainKeccak256Fr64Be,
        Identity::Merlin3KoalaBearExt8,
        Identity::Merlin3Fr64Be,
    ] {
        for contract in [BLOCK, SEARCH, CHECK] {
            assert!(cpu.prepare_binding(&binding(suite, contract)).is_none());
        }
    }
    assert_eq!(Policy::default().max_search_attempts, 1 << 20);
    for attempts in [0, 1 << 24, (1 << 24) + 1, u64::MAX] {
        let policy = Policy {
            max_search_attempts: attempts,
            ..Policy::default()
        };
        let pool = zkc_cpu::CpuExecution::new(1).unwrap();
        for result in [
            CpuBackend::new(policy, support::entry(None), Default::default()),
            CpuBackend::new_with_cpu(
                policy,
                support::entry(None),
                Default::default(),
                pool.clone(),
            ),
            CpuBackend::new_with_installation(
                policy,
                support::entry(None),
                Default::default(),
                pool.clone(),
                Default::default(),
            ),
        ] {
            if attempts <= 1 << 24 {
                assert!(result.is_ok());
            } else {
                assert_eq!(result.err().unwrap().code, "refused:search-attempt-limit");
            }
        }
    }
}

#[test]
fn reached_static_parameter_and_coordinate_refusals_publish_nothing() {
    let suite = SUITES[0];
    let valid = attrs(suite, 16, 9, Some(1), false);
    for position in [1, 2, 3] {
        let mut inner = backend(Policy::default());
        let old = issue(&mut inner, suite, 1);
        let mut controlled = Controlled::new(inner);
        let mut invalid = valid.clone();
        invalid[position] = "01".into();
        controlled.attributes = Some(invalid);
        let (out, controlled) = one(
            controlled,
            binding(suite, SEARCH),
            &valid.iter().map(String::as_str).collect::<Vec<_>>(),
            vec![old.clone(), Value::Indices(vec![].into())],
        );
        assert_eq!(out.unwrap_err(), "refused:kernel-attributes");
        assert_eq!(controlled.inner.observe(token(&old)).unwrap().generation, 0);
        assert!(controlled.outputs.is_empty());
    }
    let (out, controlled, old) = run(suite, SEARCH, &valid, Policy::default(), 0, &[1], 1, None);
    assert_eq!(out.unwrap_err(), "refused:transcript-origin");
    assert_eq!(controlled.inner.observe(token(&old)).unwrap().generation, 0);
    assert!(controlled.outputs.is_empty());
}

// Capture authentic Runner frames for adversarial calls. No production mint or
// fake frame API is needed to test active-frame and resource-view boundaries.
struct AuthorityProbe {
    inner: CpuBackend,
    hidden: Value,
    foreign: Value,
    root_frame: Option<Frame>,
    after: Option<CapabilityObservation>,
}
impl Backend for AuthorityProbe {
    type Call = ();
    type Checkpoint = ();
    type Value = Value;
    type Operation = CpuOperation;
    fn prepare_binding(&self, b: &OperationBinding) -> Option<CpuOperation> {
        self.inner.prepare_binding(b)
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, a: &[Value]) -> Result<(), BackendError> {
        if matches!(f.kind(), FrameKind::Entry) {
            self.root_frame = Some(f.clone());
        }
        self.inner.enter_frame(f, a)
    }
    fn leave_frame(&mut self, f: &Frame, e: FrameExit, a: &[Value]) -> Result<(), BackendError> {
        self.inner.leave_frame(f, e, a)
    }
    fn apply(
        &mut self,
        op: &CpuOperation,
        i: &Invocation<'_>,
        a: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        let before = self.inner.observe(token(&a[0])).unwrap();
        for (replacement, expected) in [
            (&self.hidden, "refused:capability-out-of-view"),
            (&self.foreign, "refused:capability-authority"),
        ] {
            let mut args = a.to_vec();
            args[0] = replacement.clone();
            assert_eq!(self.inner.apply(op, i, &args).unwrap_err().code, expected);
        }
        let inactive = Invocation {
            context: CallContext {
                frame: self.root_frame.as_ref().unwrap(),
                ..i.context
            },
            ..*i
        };
        assert_eq!(
            self.inner.apply(op, &inactive, a).unwrap_err().code,
            "refused:inactive-frame"
        );
        assert_eq!(self.inner.observe(token(&a[0])).unwrap(), before);
        let out = self.inner.apply(op, i, a);
        self.after = Some(self.inner.observe(token(&a[0])).unwrap());
        assert_eq!(
            self.inner.apply(op, i, a).unwrap_err().code,
            "refused:capability-stale"
        );
        assert_eq!(
            self.inner.observe(token(&a[0])).unwrap(),
            *self.after.as_ref().unwrap()
        );
        out
    }
}
#[test]
fn authentic_frames_and_authority_are_required_and_failed_gate_stales_the_old_token() {
    for contract in [BLOCK, CHECK] {
        let suite = SUITES[0];
        let mut inner = backend(Policy::default());
        let old = issue(&mut inner, suite, 2);
        let hidden = issue(&mut inner, suite, 2);
        let foreign = issue(&mut backend(Policy::default()), suite, 2);
        let probe = AuthorityProbe {
            inner,
            hidden,
            foreign,
            root_frame: None,
            after: None,
        };
        let mut args = vec![old];
        if contract == CHECK {
            args.push(Value::Index(0));
        }
        args.push(Value::Indices(vec![].into()));
        let a = attrs(
            suite,
            16,
            7,
            if contract == CHECK { Some(64) } else { None },
            false,
        );
        let (out, probe) = one(
            probe,
            binding(suite, contract),
            &a.iter().map(String::as_str).collect::<Vec<_>>(),
            args,
        );
        if contract == CHECK {
            assert_eq!(out.unwrap_err(), "rejected:require");
        } else {
            assert!(out.is_ok());
        }
        let after = probe.after.unwrap();
        assert_eq!(
            (after.generation, after.draw_count, after.budget),
            (1, 1, 1)
        );
    }
}
