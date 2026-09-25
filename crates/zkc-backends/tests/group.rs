mod common;
use common::*;
use zkc_backends::*;
use zkc_runtime::interactive::Backend;

fn prover_program() -> Vec<u8> {
    program(
        None,
        &[("x", "field"), ("c", "field"), ("nonce", "nonce")],
        vec![
            op("generator", "arkworks/curve.generator", &[], &["g"]),
            op("public", "arkworks/curve.scale", &["g", "x"], &["X"]),
            op("empty", "arkworks/curve.empty", &[], &["empty"]),
            op(
                "bases",
                "arkworks/curve.append",
                &["empty", "g"],
                &["bases"],
            ),
            op(
                "commit",
                "arkworks/curve.commit",
                &["bases", "nonce"],
                &["points", "next"],
            ),
            serde_json::json!(["op", "at", "arkworks/curve.at", ["0"], ["points"], ["R"]]),
            op(
                "response",
                "arkworks/curve.response",
                &["x", "c", "next"],
                &["s"],
            ),
        ],
        &["group", "group", "field"],
        &["X", "R", "s"],
    )
}
fn verifier_program() -> Vec<u8> {
    program(
        None,
        &[
            ("X", "group"),
            ("R", "group"),
            ("c", "field"),
            ("s", "field"),
        ],
        vec![
            op("generator", "arkworks/curve.generator", &[], &["g"]),
            op("left", "arkworks/curve.scale", &["g", "s"], &["left"]),
            op("scale", "arkworks/curve.scale", &["X", "c"], &["scaled"]),
            op("right", "arkworks/curve.add", &["R", "scaled"], &["right"]),
            op(
                "check",
                "arkworks/curve.equal",
                &["left", "right"],
                &["valid"],
            ),
            op("not", "arkworks/bool.not", &["valid"], &["invalid"]),
            op("restore", "arkworks/bool.not", &["invalid"], &["restored"]),
            op(
                "or",
                "arkworks/bool.or",
                &["valid", "restored"],
                &["either"],
            ),
            op("and", "arkworks/bool.and", &["valid", "either"], &["both"]),
            op("require", "arkworks/control.require", &["both"], &[]),
            op("suffix", "arkworks/curve.scale", &["g", "s"], &["suffix"]),
        ],
        &["group"],
        &["suffix"],
    )
}
#[test]
fn bls_nonce_stages_and_public_verifier_valid_and_invalid() {
    let mut p = backend().build();
    let nonce = p.issue_nonce(domain(), 2).unwrap();
    assert!(p.encode_value(&nonce).is_err());
    let (out, p) = run(&prover_program(), p, vec![f(7), f(11), nonce.clone()]);
    let out = out.unwrap();
    let state = p.observe(token(&nonce)).unwrap();
    assert_eq!(
        (
            state.generation,
            state.draw_count,
            state.budget,
            state.stage
        ),
        (2, 2, 0, "spent")
    );
    let Value::Curve(public) = out[0] else {
        panic!()
    };
    let Value::Curve(commitment) = out[1] else {
        panic!()
    };
    assert_eq!(public, GroupPoint::generator().scale(Scalar::from(7u64)));
    assert_eq!(
        GroupPoint::generator().scale(scalar(&out[2])),
        commitment.add(&public.scale(Scalar::from(11u64)))
    );
    assert!(p.validate_value(&nonce).is_err());
    assert_eq!(p.active_frames(), 0);
    let verifier = backend().build();
    let mut public = vec![
        verifier
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("group:bls12-381.g1").unwrap(),
                ),
                &p.encode_value(&out[0]).unwrap(),
            )
            .unwrap(),
        verifier
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("group:bls12-381.g1").unwrap(),
                ),
                &p.encode_value(&out[1]).unwrap(),
            )
            .unwrap(),
        f(11),
        verifier
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("field:bls12-381.fr").unwrap(),
                ),
                &p.encode_value(&out[2]).unwrap(),
            )
            .unwrap(),
    ];
    let (valid, v) = run(&verifier_program(), verifier, public.clone());
    assert!(valid.is_ok());
    assert_eq!(v.active_frames(), 0);
    public[3] = Value::Field(scalar(&out[2]) + Scalar::from(1u64));
    let (invalid, v) = run(&verifier_program(), backend().build(), public);
    assert_eq!(code(&invalid.unwrap_err()), "rejected:require");
    assert_eq!(v.active_frames(), 0);
    for (contract, implementation) in [
        ("random.draw", "reference/random.draw"),
        ("group.check", "arkworks/group.check"),
    ] {
        assert!(
            v.binding_signature(&zkc_runtime::interactive::OperationBinding {
                contract: contract.into(),
                arguments: vec!["bls12-381.fr".into()],
                implementation: implementation.into(),
            })
            .is_none()
        );
    }
}
#[test]
fn nonce_response_before_commit_fails_after_consuming_and_no_suffix() {
    let mut p = backend().build();
    let nonce = p.issue_nonce(domain(), 2).unwrap();
    let outside = p.issue_nonce(domain(), 2).unwrap();
    let before = p.observe(token(&outside)).unwrap();
    let bytes = program(
        None,
        &[("x", "field"), ("c", "field"), ("n", "nonce")],
        vec![op(
            "bad",
            "arkworks/curve.response",
            &["x", "c", "n"],
            &["s"],
        )],
        &["field"],
        &["s"],
    );
    let (out, p) = run(&bytes, p, vec![f(7), f(11), nonce.clone()]);
    assert_eq!(code(&out.unwrap_err()), "refused:nonce-stage");
    let state = p.observe(token(&nonce)).unwrap();
    assert_eq!(
        (
            state.generation,
            state.draw_count,
            state.budget,
            state.stage
        ),
        (1, 1, 1, "spent")
    );
    assert_eq!(p.observe(token(&outside)).unwrap(), before);
    assert_eq!(p.active_frames(), 0);
}
#[test]
fn nonce_cannot_commit_twice_even_using_valid_successor() {
    let mut p = backend().build();
    let nonce = p.issue_nonce(domain(), 3).unwrap();
    let bytes = program(
        None,
        &[("n", "nonce")],
        vec![
            op("generator", "arkworks/curve.generator", &[], &["g"]),
            op("empty", "arkworks/curve.empty", &[], &["empty"]),
            op(
                "bases",
                "arkworks/curve.append",
                &["empty", "g"],
                &["bases"],
            ),
            op(
                "first",
                "arkworks/curve.commit",
                &["bases", "n"],
                &["R", "n1"],
            ),
            op(
                "second",
                "arkworks/curve.commit",
                &["bases", "n1"],
                &["R2", "n2"],
            ),
        ],
        &["groups", "nonce"],
        &["R2", "n2"],
    );
    let (out, p) = run(&bytes, p, vec![nonce.clone()]);
    assert_eq!(code(&out.unwrap_err()), "refused:nonce-stage");
    let state = p.observe(token(&nonce)).unwrap();
    assert_eq!(
        (
            state.generation,
            state.draw_count,
            state.budget,
            state.stage
        ),
        (2, 2, 1, "spent")
    );
}
#[cfg(feature = "test-utils")]
#[test]
fn explicit_test_nonce_has_known_bls_response() {
    let mut p = backend().build();
    let nonce = p.issue_test_nonce(domain(), 2, Scalar::from(5u64)).unwrap();
    let (out, _) = run(&prover_program(), p, vec![f(7), f(11), nonce]);
    let out = out.unwrap();
    assert!(
        matches!(out[1], Value::Curve(p) if p == GroupPoint::generator().scale(Scalar::from(5u64)))
    );
    assert_eq!(scalar(&out[2]), Scalar::from(82u64));
}
