use zkc_runtime::interactive::Value as RuntimeValue;
mod common;
use common::*;
use serde_json::json;
use zkc_backends::*;
use zkc_runtime::interactive::{Backend, ErrorCode, admit_supplied};
fn real() -> NativeBackend {
    backend().build()
}
fn groups(n: &[u64]) -> Value {
    Value::groups(
        &n.iter()
            .map(|n| GroupPoint::generator().scale(Scalar::from(*n)))
            .collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
fn prog(
    ports: &[(&str, &str)],
    ops: Vec<serde_json::Value>,
    types: &[&str],
    ret: &[&str],
) -> Vec<u8> {
    program(None, ports, ops, types, ret)
}

#[test]
fn nominal_bindings_match_independent_provider_signatures() {
    use zkc_runtime::interactive::{LogicalType, OperationBinding, PhysicalType};
    let b = real();
    for (contract, arguments) in [
        ("curve.generator", vec!["bls12-381.g1"]),
        ("curve.scale", vec!["bls12-381.g1"]),
        ("pcs.commit", vec!["multilinear.kzg.bls12-381/1"]),
        ("poly.fold", vec!["bls12-381.fr"]),
        ("bool.and", vec![]),
        ("control.require", vec![]),
    ] {
        let declaration = OperationBinding {
            contract: contract.into(),
            arguments: arguments.into_iter().map(str::to_owned).collect(),
            implementation: format!("arkworks/{contract}"),
        };
        assert_eq!(
            b.binding_signature(&declaration),
            Some(declaration.signature().unwrap())
        );
    }
    for (contract, arguments, implementation) in [
        (
            "group.public",
            vec!["bls12-381.fr"],
            "reference/group.public",
        ),
        (
            "group.commit",
            vec!["bls12-381.fr"],
            "arkworks/group.commit",
        ),
        ("group.check", vec!["bls12-381.fr"], "arkworks/group.check"),
        (
            "curve.generator",
            vec!["bls12-381.g1"],
            "reference/curve.generator",
        ),
        (
            "transcript.observe.nonce",
            vec!["merlin3.bls12-381.fr64be/1"],
            "arkworks/transcript.observe.nonce",
        ),
        ("bool.and", vec![], "reference/bool.and"),
    ] {
        let declaration = OperationBinding {
            contract: contract.into(),
            arguments: arguments.into_iter().map(str::to_owned).collect(),
            implementation: implementation.into(),
        };
        assert!(declaration.signature().is_err(), "{implementation}");
        assert!(
            b.binding_signature(&declaration).is_none(),
            "{implementation}"
        );
    }
    assert!(LogicalType::parse("scalar:bls12-381.fr").is_err());
    assert!(LogicalType::parse("group:reference.additive.bls12-381.fr/1").is_err());
    assert!(PhysicalType::parse("group:bls12-381.g1@reference.additive-fr/1").is_err());
}
#[test]
fn public_curve_kernels_and_vector_bounds_run_through_runner() {
    let bytes = prog(
        &[("x", "field")],
        vec![
            op("g", "arkworks/curve.generator", &[], &["g"]),
            op("scale", "arkworks/curve.scale", &["g", "x"], &["scaled"]),
            op("add", "arkworks/curve.add", &["g", "scaled"], &["sum"]),
            op("empty", "arkworks/curve.empty", &[], &["empty"]),
            op(
                "append",
                "arkworks/curve.append",
                &["empty", "sum"],
                &["points"],
            ),
            json!(["op", "at", "arkworks/curve.at", ["0"], ["points"], ["got"]]),
            op("eq", "arkworks/curve.equal", &["got", "sum"], &["eq"]),
        ],
        &["group", "groups", "bool"],
        &["got", "points", "eq"],
    );
    let (out, _) = run(&bytes, real(), vec![f(7)]);
    let out = out.unwrap();
    let Value::Curve(p) = out[0] else { panic!() };
    assert_eq!(p, GroupPoint::generator().scale(Scalar::from(8)));
    assert!(matches!(out[2], Value::Bool(true)));
    let bad = prog(
        &[("points", "groups")],
        vec![json!([
            "op",
            "at",
            "arkworks/curve.at",
            ["1"],
            ["points"],
            ["got"]
        ])],
        &["group"],
        &["got"],
    );
    assert_eq!(
        code(&run(&bad, real(), vec![groups(&[1])]).0.unwrap_err()),
        "refused:group-index"
    );
    for index in ["01", "-1", "18446744073709551616", ""] {
        let b = prog(
            &[("points", "groups")],
            vec![json!([
                "op",
                "at",
                "arkworks/curve.at",
                [index],
                ["points"],
                ["got"]
            ])],
            &["group"],
            &["got"],
        );
        assert_eq!(
            admit_supplied(&b, &real()).unwrap_err().code,
            ErrorCode::Attributes
        );
    }
    let b = prog(
        &[("points", "groups"), ("g", "group")],
        vec![op(
            "append",
            "arkworks/curve.append",
            &["points", "g"],
            &["out"],
        )],
        &["groups"],
        &["out"],
    );
    let policy = Policy {
        max_groups: 1,
        ..Policy::default()
    };
    let backend = NativeBackend::new(policy, entry(None), None).unwrap();
    assert_eq!(
        code(
            &run(
                &b,
                backend,
                vec![groups(&[1]), Value::Curve(GroupPoint::identity())]
            )
            .0
            .unwrap_err()
        ),
        "exhausted:group-limit"
    );
}
#[test]
fn public_codecs_are_exact_and_nominally_typed() {
    let b = real();
    let g = Value::Curve(GroupPoint::generator());
    let wire = b.encode_value(&g).unwrap();
    assert_eq!(&wire[..6], b"ZKCV\x01\x09");
    assert_eq!(wire.len(), 54);
    // Historical additive-Fr bytes remain malformed G1 bytes; never map the
    // exposed discrete logarithm onto a curve generator.
    let mut old_group = b"ZKCV\x01\x09".to_vec();
    old_group.extend(zkc_arkworks::encode_scalar(&Scalar::from(1)).unwrap());
    assert!(b.decode_typed_value(g.physical_type(), &old_group).is_err());
    assert!(b.decode_typed_value(f(1).physical_type(), &wire).is_err());
    for value in [
        g,
        Value::Curve(GroupPoint::identity()),
        groups(&[]),
        groups(&[0, 1, 7]),
    ] {
        let bytes = b.encode_value(&value).unwrap();
        assert_eq!(
            b.encode_value(&b.decode_typed_value(value.physical_type(), &bytes).unwrap())
                .unwrap(),
            bytes
        );
        for n in 0..bytes.len() {
            assert!(
                b.decode_typed_value(value.physical_type(), &bytes[..n])
                    .is_err()
            );
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(b.decode_typed_value(value.physical_type(), &extra).is_err());
    }
    let mut enormous = b"ZKCV\x01\x0a".to_vec();
    enormous.extend(u32::MAX.to_le_bytes());
    assert_eq!(
        b.decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("groups:bls12-381.g1").unwrap()
            ),
            &enormous
        )
        .unwrap_err()
        .code,
        "exhausted:group-limit"
    );
    let mut invalid = b"ZKCV\x01\x0a".to_vec();
    invalid.extend(1u32.to_le_bytes());
    invalid.extend([0; 48]);
    invalid[10] = 0x80;
    assert!(
        b.decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("groups:bls12-381.g1").unwrap()
            ),
            &invalid
        )
        .is_err()
    );
    let mut nonexistent = b"ZKCV\x01\x0a".to_vec();
    nonexistent.extend(2u32.to_le_bytes());
    assert_eq!(
        b.decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("groups:bls12-381.g1").unwrap()
            ),
            &nonexistent
        )
        .unwrap_err()
        .code,
        "refused:wire-length"
    );
}
#[cfg(feature = "test-utils")]
#[test]
fn multibase_nonce_stages_zero_and_reuse() {
    let bytes = prog(
        &[
            ("bases", "groups"),
            ("n", "nonce"),
            ("x", "field"),
            ("c", "field"),
        ],
        vec![
            op(
                "commit",
                "arkworks/curve.commit",
                &["bases", "n"],
                &["rs", "ready"],
            ),
            op(
                "response",
                "arkworks/curve.response",
                &["x", "c", "ready"],
                &["z"],
            ),
        ],
        &["groups", "field"],
        &["rs", "z"],
    );
    for bases in [vec![], vec![0], vec![1, 3, 0]] {
        for k in [0, 11] {
            let mut backend = real();
            let nonce = backend
                .issue_test_nonce(domain(), 2, Scalar::from(k))
                .unwrap();
            let old = nonce.clone();
            let (out, backend) = run(&bytes, backend, vec![groups(&bases), nonce, f(7), f(13)]);
            let out = out.unwrap();
            let Value::Groups(rs) = &out[0] else { panic!() };
            assert_eq!(rs.len(), bases.len());
            for (r, base) in rs.iter().zip(&bases) {
                assert_eq!(*r, GroupPoint::generator().scale(Scalar::from(base * k)));
            }
            assert_eq!(scalar(&out[1]), Scalar::from(k + 13 * 7));
            let state = backend.observe(token(&old)).unwrap();
            assert_eq!(
                (state.generation, state.budget, state.stage),
                (2, 0, "spent")
            );
            assert_eq!(
                backend.validate_value(&old).unwrap_err().code,
                "refused:capability-stale"
            );
        }
    }
    for twice in [false, true] {
        let mut backend = real();
        let nonce = backend
            .issue_test_nonce(domain(), 3, Scalar::from(11))
            .unwrap();
        let (bytes, inputs) = if twice {
            (
                prog(
                    &[("b", "groups"), ("n", "nonce")],
                    vec![
                        op("c1", "arkworks/curve.commit", &["b", "n"], &["rs", "ready"]),
                        op(
                            "c2",
                            "arkworks/curve.commit",
                            &["b", "ready"],
                            &["rs2", "next"],
                        ),
                    ],
                    &["nonce"],
                    &["next"],
                ),
                vec![groups(&[1, 3]), nonce.clone()],
            )
        } else {
            (
                prog(
                    &[("n", "nonce"), ("x", "field")],
                    vec![op(
                        "bad",
                        "arkworks/curve.response",
                        &["x", "x", "n"],
                        &["z"],
                    )],
                    &["field"],
                    &["z"],
                ),
                vec![nonce.clone(), f(7)],
            )
        };
        let (out, backend) = run(&bytes, backend, inputs);
        assert_eq!(code(&out.unwrap_err()), "refused:nonce-stage");
        let state = backend.observe(token(&nonce)).unwrap();
        assert_eq!(state.stage, "spent");
        assert_eq!(state.generation, if twice { 2 } else { 1 });
        assert_eq!(backend.active_frames(), 0);
    }
}
#[cfg(feature = "test-utils")]
#[test]
fn pcs_equal_uses_pinned_public_commitments_and_preserves_keys() {
    let p = Policy::default();
    let keys = Keys::setup_for_development(1, &p.ark_bounds()).unwrap();
    let Value::Table(t) = table(&[1, 2]) else {
        panic!()
    };
    let c = keys.prover_key().commit(&t).unwrap();
    let Value::Table(t2) = table(&[2, 3]) else {
        panic!()
    };
    let c2 = keys.prover_key().commit(&t2).unwrap();
    let bytes = prog(
        &[("a", "commitment"), ("b", "commitment")],
        vec![op("eq", "arkworks/pcs.equal", &["a", "b"], &["same"])],
        &["bool"],
        &["same"],
    );
    for (other, expected) in [(c.commitment(), true), (c2.commitment(), false)] {
        let b = NativeBackend::new(p, entry(Some(1)), Some(keys.verifier_key().clone())).unwrap();
        let (out, _) = run(
            &bytes,
            b,
            vec![
                Value::Commitment(std::sync::Arc::new(c.commitment().clone())),
                Value::Commitment(std::sync::Arc::new(other.clone())),
            ],
        );
        assert!(matches!(out.unwrap()[0], Value::Bool(v) if v==expected));
    }
}

#[test]
fn real_os_nonce_custody_aliases_and_cancellation() {
    use zkc_runtime::interactive::{Action, Runner};
    let bytes = prog(
        &[("n", "nonce"), ("bases", "groups")],
        vec![op(
            "commit",
            "arkworks/curve.commit",
            &["bases", "n"],
            &["rs", "next"],
        )],
        &["groups", "nonce"],
        &["rs", "next"],
    );
    let mut backend = real();
    let nonce = backend.issue_nonce(domain(), 2).unwrap();
    let old = nonce.clone();
    let (out, backend) = run(&bytes, backend, vec![nonce, groups(&[1, 3])]);
    let out = out.unwrap();
    assert_eq!(backend.observe(token(&old)).unwrap().stage, "committed");
    assert_eq!(
        backend.encode_value(&out[1]).unwrap_err().code,
        "refused:nonserializable"
    );
    assert_eq!(
        backend
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("nonce:bls12-381.fr").unwrap()
                ),
                &[]
            )
            .unwrap_err()
            .code,
        "refused:nonserializable"
    );
    assert_eq!(
        real().validate_value(&out[1]).unwrap_err().code,
        "refused:capability-authority"
    );
    for wrong in [
        Domain::new("V", "session", "main", None),
        Domain::new("P", "session", "main", Some("different_instance")),
    ] {
        let mut backend = real();
        let nonce = backend.issue_nonce(wrong, 2).unwrap();
        let old = nonce.clone();
        let admitted = admit_supplied(&bytes, &backend).unwrap();
        let e = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![nonce, groups(&[1])],
        )
        .err()
        .unwrap();
        assert_eq!(e.backend.observe(token(&old)).unwrap().generation, 0);
        assert_eq!(e.backend.active_frames(), 0);
    }
    let aliases = prog(
        &[("a", "nonce"), ("b", "nonce")],
        vec![],
        &["nonce", "nonce"],
        &["a", "b"],
    );
    let mut backend = real();
    let nonce = backend.issue_nonce(domain(), 2).unwrap();
    let admitted = admit_supplied(&aliases, &backend).unwrap();
    let e = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        backend,
        vec![nonce.clone(), nonce.clone()],
    )
    .err()
    .unwrap();
    assert_eq!(e.backend.observe(token(&nonce)).unwrap().generation, 0);
    assert!(
        matches!(e.error,zkc_runtime::interactive::RuntimeError::Backend(e) if e.code=="refused:capability-alias")
    );
    // Cancel after commit but before participant return; preserve committed stage.
    let mut backend = real();
    let nonce = backend.issue_nonce(domain(), 2).unwrap();
    let old = nonce.clone();
    let mut runner = load(&bytes, backend, vec![nonce, groups(&[1])]);
    let Action::Local(local) = runner.poll() else {
        panic!()
    };
    runner.execute_local(&local.cut).unwrap();
    runner.cancel();
    let backend = runner.into_backend();
    assert_eq!(backend.observe(token(&old)).unwrap().generation, 1);
    assert_eq!(backend.observe(token(&old)).unwrap().stage, "committed");
    assert_eq!(backend.active_frames(), 0);
}
