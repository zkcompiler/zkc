use super::support::*;
use serde_json::{Value as Json, json};
use zkc_backends::{Capability, Policy, RistrettoScalar, Value};
#[cfg(feature = "test-utils")]
use zkc_runtime::interactive::Backend;
use zkc_runtime::interactive::{Identity, Runner, Value as RuntimeValue, admit_supplied};
fn token(v: &Value) -> &Capability {
    match v {
        Value::Rng(t) | Value::Nonce(t) | Value::Transcript(t) => t,
        _ => panic!(),
    }
}
fn identity(d: bool) -> Identity {
    if d {
        Identity::Ristretto255Scalar
    } else {
        Identity::Bls12381Fr
    }
}
#[test]
fn canonical_transcript_observations_match_direct_merlin_and_suite_reduction() {
    for d in [false, true] {
        let f = identity(d);
        let suite = if f == Identity::Bls12381Fr {
            Identity::Merlin3Fr64Be
        } else {
            Identity::Merlin3Ristretto64Le
        };
        let root = tree(&json!(["native-contract-root", suite.name()]));
        for value in [
            field(d, 7),
            vector(d, &[2, 3]),
            call(
                d,
                "poly.from_coefficients",
                &[],
                vec![vector(d, &[2, 3, 0])],
            )
            .remove(0),
            groups(d, &[1, 2]),
            call(d, "curve.generator", &[], vec![]).remove(0),
            if d {
                Value::RistrettoRound([1u64, 2, 3].map(RistrettoScalar::from))
            } else {
                Value::Round([1u64, 2, 3].map(zkc_backends::Scalar::from))
            },
            Value::Bool(true),
        ] {
            let mut b = backend(Policy::default());
            let transcript = b.issue_transcript_for(suite, domain(), 2, &root).unwrap();
            let handle = token(&transcript).clone();
            let kind = value.ty().name();
            let mut observe = binding(d, &format!("transcript.observe.{kind}"));
            observe.arguments = vec![suite.name().into()];
            if value.ty() != zkc_runtime::interactive::Type::Bool {
                observe
                    .arguments
                    .push(value.physical_type().logical().identity().name().into());
            }
            observe
                .arguments
                .push(value.physical_type().logical().codec().unwrap());
            let challenge = binding(d, "transcript.challenge");
            let out = challenge.signature().unwrap().outputs;
            let attrs = ["Source", "message", "Schema", "P", "V"];
            let draw_attrs = ["Source", "call", "Draw", "draw", "V"];
            let bytes = program(
                &[observe, challenge],
                &[transcript.physical_type(), value.physical_type()],
                vec![
                    json!(["op", "observe", "b0", attrs, ["a0", "a1"], ["t1"]]),
                    json!(["op", "challenge", "b1", draw_attrs, ["t1"], ["c", "t2"]]),
                ],
                &out,
                &["c".into(), "t2".into()],
            );
            let encoded = b.encode_value(&value).unwrap();
            let mut direct = merlin::Transcript::new(b"zkc.artifact/1");
            direct.append_message(b"binding", &root);
            direct.append_message(
                b"origin",
                &tree(&json!([
                    "zkc.logical-origin/1",
                    "main",
                    "instance",
                    [],
                    ["message", "Source", "message", "Schema", "P", "V"]
                ])),
            );
            direct.append_message(b"value", &encoded);
            direct.append_message(
                b"origin",
                &tree(&json!([
                    "zkc.logical-origin/1",
                    "main",
                    "instance",
                    [],
                    ["challenge", "Source", "call", "Draw", "draw", "V"]
                ])),
            );
            let mut wide = [0; 64];
            direct.challenge_bytes(b"challenge", &mut wide);
            let expected = if d {
                Value::RistrettoField(RistrettoScalar::from_bytes_mod_order_wide(&wide))
            } else {
                Value::Field(zkc_arkworks::scalar_from_wide_be(&wide))
            };
            let (result, b) = run_program(b, &bytes, vec![transcript, value]);
            let result = result.unwrap();
            assert_value(&result[0], &expected);
            assert_eq!(token(&result[1]).identity(), suite);
            let observed = b.observe(&handle).unwrap();
            assert_eq!(
                (observed.generation, observed.draw_count, observed.budget),
                (2, 2, 0)
            );
            assert_eq!(b.active_frames(), 0);
        }
    }
}
#[test]
fn advancing_os_masks_do_not_issue_nonce_capabilities_and_capacity_preflight_consumes_nothing() {
    for d in [false, true] {
        let mut b = backend(Policy::default());
        let rng = b.issue_rng_for(identity(d), domain(), 20).unwrap();
        let h = token(&rng).clone();
        let (first, b) = one(b, binding(d, "random.vector"), &["4"], vec![rng]);
        let first = first.unwrap();
        assert!(matches!(
            first[0],
            Value::Vector(_) | Value::RistrettoVector(_)
        ));
        assert_eq!(token(&first[1]).identity(), identity(d));
        let (second, b) = one(
            b,
            binding(d, "random.vector"),
            &["4"],
            vec![first[1].clone()],
        );
        let second = second.unwrap();
        assert_ne!(
            b.encode_value(&first[0]).unwrap(),
            b.encode_value(&second[0]).unwrap()
        );
        let state = b.observe(&h).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (2, 8, 12)
        );
        let mut controlled = Controlled::new(b);
        controlled.output_limit = Some(0);
        let (fail, b) = one(
            controlled,
            binding(d, "random.vector"),
            &["4"],
            vec![second[1].clone()],
        );
        assert_eq!(fail.unwrap_err(), "exhausted:output-bytes");
        let state = b.inner.observe(&h).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (2, 8, 12)
        );
        let (empty, b) = one(
            b.inner,
            binding(d, "random.vector"),
            &["0"],
            vec![second[1].clone()],
        );
        let empty = empty.unwrap();
        assert_value(&empty[0], &vector(d, &[]));
        let state = b.observe(&h).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (3, 8, 12)
        );
    }
}
#[test]
fn capacities_and_unpassed_resources_fail_closed_in_both_domains() {
    for d in [false, true] {
        let mut b = backend(Policy::default());
        let rng = b.issue_rng_for(identity(d), domain(), 1).unwrap();
        let h = token(&rng).clone();
        let outside = b.issue_rng_for(identity(d), domain(), 7).unwrap();
        let out = token(&outside).clone();
        let mut controlled = Controlled::new(b);
        controlled.substitute = Some(outside);
        let (result, b) = one(
            controlled,
            binding(d, "random.draw"),
            &[],
            vec![rng.clone()],
        );
        assert_eq!(result.unwrap_err(), "refused:capability-out-of-view");
        assert_eq!(b.inner.observe(&h).unwrap().generation, 0);
        assert_eq!(b.inner.observe(&out).unwrap().generation, 0);
        let (result, b) = one(
            b.inner,
            binding(d, "random.vector"),
            &["3"],
            vec![rng.clone()],
        );
        assert_eq!(result.unwrap_err(), "exhausted:resource-budget");
        let state = b.observe(&h).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (0, 0, 1)
        );
        assert_eq!(b.observe(&out).unwrap().generation, 0);
        assert_eq!(b.active_frames(), 0);
        let sig = binding(d, "random.draw").signature().unwrap();
        let bytes = program(
            &[binding(d, "random.draw")],
            &sig.inputs,
            vec![json!(["op", "site", "b0", [], ["a0"], ["x", "t"]])],
            &sig.outputs,
            &["x".into(), "t".into()],
        );
        let admitted = admit_supplied(&bytes, &b).unwrap();
        assert!(Runner::new(&admitted, "main", "P", "session", b, vec![rng]).is_ok());
        // Every field of the domain, and the refusal named rather than only
        // counted: the same four the arkworks side checks in tests/resources.rs.
        for domain in [
            zkc_backends::Domain::new("V", "session", "main", None),
            zkc_backends::Domain::new("P", "other", "main", None),
            zkc_backends::Domain::new("P", "session", "other", None),
            zkc_backends::Domain::new("P", "session", "main", Some("other")),
        ] {
            let mut b = backend(Policy::default());
            let t = b.issue_rng_for(identity(d), domain, 1).unwrap();
            match Runner::new(&admitted, "main", "P", "session", b, vec![t]) {
                Err(e) => {
                    assert!(
                        e.error.to_string().contains("capability-domain"),
                        "{}",
                        e.error
                    );
                    assert_eq!(e.backend.active_frames(), 0);
                }
                Ok(_) => panic!("a capability from another domain was accepted"),
            }
        }
    }
}
#[cfg(feature = "test-utils")]
#[test]
fn vector_draw_schedule_matches_scalar_tapes_and_does_not_hide_zero() {
    for d in [false, true] {
        let mut b = backend(Policy::default());
        let rng = if d {
            b.issue_test_ristretto_tape(
                domain(),
                4,
                vec![
                    RistrettoScalar::ZERO,
                    RistrettoScalar::from(2u64),
                    RistrettoScalar::from(3u64),
                ],
            )
            .unwrap()
        } else {
            b.issue_test_tape(
                domain(),
                4,
                vec![
                    zkc_backends::Scalar::from(0),
                    zkc_backends::Scalar::from(2),
                    zkc_backends::Scalar::from(3),
                ],
            )
            .unwrap()
        };
        let h = token(&rng).clone();
        let (r, b) = one(b, binding(d, "random.vector"), &["2"], vec![rng]);
        let r = r.unwrap();
        assert_value(&r[0], &vector(d, &[0, 2]));
        let (r, b) = one(b, binding(d, "random.draw"), &[], vec![r[1].clone()]);
        let r = r.unwrap();
        assert_value(&r[0], &field(d, 3));
        let (r, b) = one(b, binding(d, "random.draw"), &[], vec![r[1].clone()]);
        assert_eq!(r.unwrap_err(), "exhausted:test-tape");
        let state = b.observe(&h).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (3, 4, 0)
        );
        assert_error(
            d,
            "field.inverse",
            &[],
            vec![field(d, 0)],
            "refused:zero-inverse",
        );
    }
}
#[cfg(feature = "test-utils")]
#[test]
fn ristretto_nonce_has_separate_issued_committed_spent_custody() {
    let mut b = backend(Policy::default());
    let nonce = b
        .issue_test_ristretto_nonce(domain(), 2, RistrettoScalar::from(7u64))
        .unwrap();
    let h = token(&nonce).clone();
    let (r, b) = one(
        b,
        binding(true, "curve.commit"),
        &[],
        vec![groups(true, &[2, 3]), nonce],
    );
    let r = r.unwrap();
    assert_value(&r[0], &groups(true, &[14, 21]));
    assert_eq!(b.observe(&h).unwrap().stage, "committed");
    let (r, b) = one(
        b,
        binding(true, "curve.response"),
        &[],
        vec![field(true, 5), field(true, 11), r[1].clone()],
    );
    assert_value(&r.unwrap()[0], &field(true, 62));
    assert_eq!(b.observe(&h).unwrap().stage, "spent");
    let mut b = backend(Policy::default());
    let nonce = b
        .issue_test_ristretto_nonce(domain(), 2, RistrettoScalar::from(7u64))
        .unwrap();
    let h = token(&nonce).clone();
    let (r, b) = one(
        b,
        binding(true, "curve.response"),
        &[],
        vec![field(true, 5), field(true, 11), nonce],
    );
    assert_eq!(r.unwrap_err(), "refused:nonce-stage");
    assert_eq!(b.observe(&h).unwrap().stage, "spent");
}

fn snapshot(b: &zkc_backends::NativeBackend, h: &Capability) -> Json {
    let s = b.observe(h).unwrap();
    json!([
        s.generation.to_string(),
        s.draw_count.to_string(),
        s.budget.to_string(),
        s.stage
    ])
}

#[test]
fn vector_atomic_resource_snapshots_zero_one_many_and_stale() {
    for d in [false, true] {
        for (n, budget, expected) in [(0, 0, [1, 0, 0]), (1, 1, [1, 1, 0]), (4, 7, [1, 4, 3])] {
            let mut b = backend(Policy::default());
            let rng = b.issue_rng_for(identity(d), domain(), budget).unwrap();
            let h = token(&rng).clone();
            let (result, b) = one(
                b,
                binding(d, "random.vector"),
                &[&n.to_string()],
                vec![rng.clone()],
            );
            let result = result.unwrap();
            assert_eq!(token(&result[1]).generation(), 1);
            let expected = json!([
                expected[0].to_string(),
                expected[1].to_string(),
                expected[2].to_string(),
                "rng"
            ]);
            assert_eq!(snapshot(&b, &h), expected);
            eprintln!(
                "resource-snapshot {} vector({n}) {}",
                identity(d).name(),
                expected
            );
            // Submit a stale token at the actual operation, including n=0.
            let mut controlled = Controlled::new(b);
            controlled.substitute = Some(rng);
            let (result, b) = one(
                controlled,
                binding(d, "random.vector"),
                &["0"],
                vec![result[1].clone()],
            );
            assert_eq!(result.unwrap_err(), "refused:capability-stale");
            assert_eq!(snapshot(&b.inner, &h), expected);
            assert_eq!(b.inner.active_frames(), 0);
        }
        for budget in [0, 2] {
            let mut b = backend(Policy::default());
            let rng = b.issue_rng_for(identity(d), domain(), budget).unwrap();
            let h = token(&rng).clone();
            let before = snapshot(&b, &h);
            let (result, b) = one(b, binding(d, "random.vector"), &["3"], vec![rng.clone()]);
            assert_eq!(result.unwrap_err(), "exhausted:resource-budget");
            assert_eq!(snapshot(&b, &h), before);
            let (result, b) = one(b, binding(d, "random.vector"), &["0"], vec![rng]);
            assert!(result.is_ok());
            assert_eq!(
                snapshot(&b, &h),
                json!(["1", "0", budget.to_string(), "rng"])
            );
        }
    }
}

#[test]
fn explicit_scalar_draw_consumes_before_output_failure_and_budget_refusal() {
    for d in [false, true] {
        for budget in [0, 1] {
            let mut b = backend(Policy::default());
            let rng = b.issue_rng_for(identity(d), domain(), budget).unwrap();
            let h = token(&rng).clone();
            let mut controlled = Controlled::new(b);
            controlled.output_limit = Some(0);
            let (result, b) = one(controlled, binding(d, "random.draw"), &[], vec![rng]);
            assert_eq!(
                result.unwrap_err(),
                if budget == 0 {
                    "exhausted:resource-budget"
                } else {
                    "exhausted:output-bytes"
                }
            );
            assert_eq!(snapshot(&b.inner, &h), json!(["1", "1", "0", "rng"]));
        }
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn vector_tape_exhaustion_keeps_full_transition_and_consumed_prefix() {
    for d in [false, true] {
        let mut b = backend(Policy::default());
        let rng = if d {
            b.issue_test_ristretto_tape(domain(), 5, vec![RistrettoScalar::ONE])
                .unwrap()
        } else {
            b.issue_test_tape(domain(), 5, vec![zkc_backends::Scalar::from(1)])
                .unwrap()
        };
        let h = token(&rng).clone();
        let (result, b) = one(b, binding(d, "random.vector"), &["3"], vec![rng.clone()]);
        assert_eq!(result.unwrap_err(), "exhausted:test-tape");
        assert_eq!(snapshot(&b, &h), json!(["1", "3", "2", "rng"]));
        assert_eq!(
            b.validate_value(&rng).unwrap_err().code,
            "refused:capability-stale"
        );
        assert_eq!(b.active_frames(), 0);
        eprintln!(
            "resource-snapshot {} tape-exhaustion {}",
            identity(d).name(),
            snapshot(&b, &h)
        );
    }
}
