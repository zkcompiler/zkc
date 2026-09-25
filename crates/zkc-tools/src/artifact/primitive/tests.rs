use super::respond;
use serde_json::json;

#[test]
fn bn254_public_service_preserves_distinct_groups_and_real_pairing_result() {
    use zkc_arkworks::bn254::{G1, G2, Scalar};
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
    use zkc_runtime::interactive::Value as RuntimeValue;
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "reference", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let wire = |v: &Value| {
        json!([
            v.physical_type().logical().spelling(),
            super::codec::hex(&backend.encode_value(v).unwrap())
        ])
    };
    let call = |name: &str, domain: &str, attrs: serde_json::Value, inputs: serde_json::Value| {
        respond(&json!([
            "zkc.public-primitive/1",
            [],
            name,
            [domain],
            attrs,
            inputs
        ]))
        .unwrap()
    };
    let p = G1::generator();
    let q = G2::generator();
    let left = Value::Bn254G1Vector(vec![p, p.neg()].into());
    let right = Value::Bn254G2Vector(vec![q, q].into());
    assert_eq!(
        call(
            "pairing.check",
            "bn254.fr",
            json!([]),
            json!([wire(&left), wire(&right)])
        ),
        json!(["ok", wire(&Value::Bool(true))])
    );
    let false_right = Value::Bn254G2Vector(vec![q, q.scale(Scalar::from(2))].into());
    assert_eq!(
        call(
            "pairing.check",
            "bn254.fr",
            json!([]),
            json!([wire(&left), wire(&false_right)])
        ),
        json!(["ok", wire(&Value::Bool(false))])
    );
    assert_eq!(
        call(
            "pairing.check",
            "bn254.fr",
            json!([]),
            json!([wire(&right), wire(&left)])
        ),
        json!(["error", "primitive-nominal-type"])
    );
    assert_eq!(
        call(
            "pairing.check",
            "bn254.fr",
            json!([]),
            json!([wire(&left), wire(&Value::Bn254G2Vector(vec![q].into()))])
        ),
        json!(["error", "primitive-length-mismatch"])
    );
    for (domain, point, vector, expected) in [
        (
            "bn254.g1",
            Value::Bn254G1(p),
            Value::Bn254G1Vector(vec![p, p].into()),
            Value::Bn254G1(p.scale(Scalar::from(5))),
        ),
        (
            "bn254.g2",
            Value::Bn254G2(q),
            Value::Bn254G2Vector(vec![q, q].into()),
            Value::Bn254G2(q.scale(Scalar::from(5))),
        ),
    ] {
        let scalars = Value::Bn254Vector(vec![Scalar::from(2), Scalar::from(3)].into());
        assert_eq!(
            call(
                "curve.msm",
                domain,
                json!([]),
                json!([wire(&scalars), wire(&vector)])
            ),
            json!(["ok", wire(&expected)])
        );
        assert_eq!(
            call(
                "curve.get",
                domain,
                json!([]),
                json!([wire(&vector), wire(&Value::Index(1))])
            ),
            json!(["ok", wire(&point)])
        );
        assert_eq!(
            call("curve.length", domain, json!([]), json!([wire(&vector)])),
            json!(["ok", wire(&Value::Index(2))])
        );
        assert_eq!(
            call("curve.at", domain, json!(["2"]), json!([wire(&vector)]))[0],
            "error"
        );
        assert_eq!(
            respond(&json!([
                "zkc.public-primitive/1",
                [],
                "validate",
                [],
                [],
                [wire(&point)]
            ]))
            .unwrap(),
            json!(["ok"])
        );
        let mut corrupted = wire(&point);
        corrupted[1] = json!(format!("{}00", corrupted[1].as_str().unwrap()));
        assert_eq!(
            respond(&json!([
                "zkc.public-primitive/1",
                [],
                "validate",
                [],
                [],
                [corrupted]
            ]))
            .unwrap()[0],
            "error"
        );
    }
}

#[test]
fn bn254_validation_rejects_noncanonical_scalars_and_matrix_order() {
    use super::codec;
    use ark_ff::{BigInteger, PrimeField};
    use zkc_arkworks::bn254::{Scalar, encode_scalar};
    let validate = |v| {
        respond(&json!([
            "zkc.public-primitive/1",
            [],
            "validate",
            [],
            [],
            [v]
        ]))
        .unwrap()
    };
    let one = encode_scalar(&Scalar::from(1)).unwrap();
    assert_eq!(
        validate(codec::value("field:bn254.fr", 40, &one)),
        json!(["ok"])
    );
    assert_eq!(
        validate(codec::value(
            "field:bn254.fr",
            40,
            &Scalar::MODULUS.to_bytes_le()
        )),
        json!(["error", "primitive-field"])
    );
    let mut body = [2u32, 2, 2]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect::<Vec<_>>();
    for (row, col) in [(0u32, 0u32), (1, 1)] {
        body.extend(row.to_le_bytes());
        body.extend(col.to_le_bytes());
        body.extend(one);
    }
    assert_eq!(
        validate(codec::value("matrix:bn254.fr", 45, &body)),
        json!(["ok"])
    );
    body[52..60].fill(0); // duplicate coordinate, not a canonical sparse matrix
    assert_eq!(
        validate(codec::value("matrix:bn254.fr", 45, &body)),
        json!(["error", "primitive-matrix-order"])
    );
    let mut polynomial = 1u32.to_le_bytes().to_vec();
    polynomial.extend([0; 32]);
    assert_eq!(
        validate(codec::value("polynomial:bn254.fr", 42, &polynomial)),
        json!(["error", "primitive-polynomial"])
    );
}

#[test]
fn explicit_configuration_is_independent_of_the_operation_curve() {
    let bounds = super::codec::bounds();
    let keys = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
    let wire = super::codec::hex(&keys.verifier_key().to_bytes(&bounds).unwrap());
    let key = json!(["vk", "verifier_key:multilinear.kzg.bls12-381/1", wire]);
    let mut points = Vec::new();
    for domain in ["bls12-381.g1", "ristretto255.group"] {
        let mut request = json!([
            "zkc.public-primitive/1",
            [],
            "curve.generator",
            [domain],
            [],
            []
        ]);
        let expected = respond(&request).unwrap();
        request[1] = json!([key]);
        assert_eq!(respond(&request).unwrap(), expected);
        points.push(expected[1].clone());
        let mut malformed = request.clone();
        malformed[1][0][2] = json!("00");
        assert_eq!(respond(&malformed).unwrap()[0], "error");
        malformed = request.clone();
        malformed[1][0][1] = json!("verifier_key:ristretto255.group");
        assert_eq!(
            respond(&malformed).unwrap(),
            json!(["error", "primitive-key-type"])
        );
        malformed = request;
        malformed[1] = json!([key, key]);
        assert_eq!(
            respond(&malformed).unwrap(),
            json!(["error", "primitive-key-record"])
        );
    }
    // Validation keeps its single-value contract. A key from another domain
    // does not change the value's nominal identity or permit a mixed batch.
    for point in &points {
        let request = json!(["zkc.public-primitive/1", [key], "validate", [], [], [point]]);
        assert_eq!(respond(&request).unwrap(), json!(["ok"]));
    }
    let batch = json!(["zkc.public-primitive/1", [key], "validate", [], [], points]);
    assert_eq!(
        respond(&batch).unwrap(),
        json!(["error", "primitive-operation"])
    );
    let mut wrong = json!([
        "zkc.public-primitive/1",
        [key],
        "validate",
        [],
        [],
        [points[1]]
    ]);
    wrong[5][0][0] = json!("group:bls12-381.g1");
    assert_eq!(respond(&wrong).unwrap()[0], "error");
}

#[test]
fn explicit_public_contracts_retain_nominal_identity_and_static_arguments() {
    let request = json!([
        "zkc.public-primitive/1",
        [],
        "curve.generator",
        ["bls12-381.g1"],
        [],
        []
    ]);
    let group = respond(&request).unwrap();
    assert_eq!(group[0], "ok");
    assert_eq!(group[1][0], "group:bls12-381.g1");
    let mut validate = json!(["zkc.public-primitive/1", [], "validate", [], [], [group[1]]]);
    assert_eq!(respond(&validate).unwrap(), json!(["ok"]));
    for ty in ["group:reference.additive.fr", "group", "scalar"] {
        validate[5][0][0] = json!(ty);
        assert_eq!(
            respond(&validate).unwrap(),
            json!(["error", "primitive-nominal-type"])
        );
    }
    let mut wrong = request;
    wrong[3][0] = json!("bls12-381.fr");
    assert_eq!(
        respond(&wrong).unwrap(),
        json!(["error", "primitive-static-arguments"])
    );
    // The other branch of the same comparison: validate is registered as
    // taking no static arguments, rather than taking one and being given the
    // wrong one. Which family the value belongs to cannot reach this, because
    // the arguments are compared before any value is parsed, so the koala-bear
    // and matrix suites check their own refusals and leave this one here.
    let arguments = json!([
        "zkc.public-primitive/1",
        [],
        "validate",
        ["bls12-381.g1"],
        [],
        [group[1]]
    ]);
    assert_eq!(
        respond(&arguments).unwrap(),
        json!(["error", "primitive-static-arguments"])
    );
}

#[test]
fn explicit_transcript_returns_bytes_from_the_requested_call_sequence() {
    let request = json!([
        "zkc.transcript-request/3",
        "merlin3.bls12-381.fr64be/1",
        "7a6b632e61727469666163742f31",
        [
            ["append", "62696e64696e67", "01"],
            ["append", "6f726967696e", "02"],
            ["challenge", "6368616c6c656e6765", "64"]
        ]
    ]);
    let mut transcript = merlin::Transcript::new(b"zkc.artifact/1");
    transcript.append_message(b"binding", &[1]);
    transcript.append_message(b"origin", &[2]);
    let mut bytes = [0; 64];
    transcript.challenge_bytes(b"challenge", &mut bytes);
    assert_eq!(
        respond(&request).unwrap(),
        json!(["ok", super::codec::hex(&bytes)])
    );
    let mut wrong = request.clone();
    wrong[3][2][2] = json!("32");
    assert_eq!(respond(&wrong), Err("primitive-transcript-step"));
    wrong = request.clone();
    wrong[2] = json!("ff");
    assert_eq!(respond(&wrong), Err("primitive-transcript-label"));
    wrong = request.clone();
    wrong[1] = json!("uninstalled-suite");
    assert_eq!(respond(&wrong), Err("primitive-suite"));
    wrong = request.clone();
    wrong[3][0][1] = json!("ff");
    assert_eq!(respond(&wrong), Err("primitive-transcript-label"));
    wrong = request.clone();
    wrong[3].as_array_mut().unwrap().reverse();
    assert_eq!(respond(&wrong), Err("primitive-history-last"));
    wrong = request.clone();
    wrong[3] = json!([]);
    assert_eq!(respond(&wrong), Err("primitive-history-length"));
    wrong = request;
    wrong[3][0][2] = json!("02");
    assert_ne!(
        respond(&wrong).unwrap(),
        json!(["ok", super::codec::hex(&bytes)])
    );
}

#[test]
fn public_domain_primitives_preserve_full_identity_and_match_native_contractions() {
    use zkc_backends::{
        Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, RistrettoScalar, Scalar, Value,
    };
    use zkc_runtime::interactive::Value as RuntimeValue;
    let b = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("P", "s", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let wire = |v: &Value| {
        json!([
            v.physical_type().logical().spelling(),
            super::codec::hex(&b.encode_value(v).unwrap())
        ])
    };
    for d in [false, true] {
        let domain = if d {
            "ristretto255.group"
        } else {
            "bls12-381.g1"
        };
        let vector = if d {
            Value::ristretto_vector(&[2u64, 3].map(RistrettoScalar::from), b.policy()).unwrap()
        } else {
            Value::vector(&[2u64, 3].map(Scalar::from), b.policy()).unwrap()
        };
        let groups = if d {
            Value::ristretto_groups(
                &[curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT; 2],
                b.policy(),
            )
            .unwrap()
        } else {
            Value::groups(&[zkc_backends::GroupPoint::generator(); 2], b.policy()).unwrap()
        };
        let request = json!([
            "zkc.public-primitive/1",
            [],
            "curve.msm",
            [domain],
            [],
            [wire(&vector), wire(&groups)]
        ]);
        let expected = if d {
            Value::RistrettoGroup(
                curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT
                    * RistrettoScalar::from(5u64),
            )
        } else {
            Value::Curve(zkc_backends::GroupPoint::generator().scale(Scalar::from(5)))
        };
        assert_eq!(respond(&request).unwrap(), json!(["ok", wire(&expected)]));
        let mut invalid = request.clone();
        invalid[5][0][0] = json!(if d {
            "vector:bls12-381.fr"
        } else {
            "vector:ristretto255.scalar"
        });
        assert_eq!(respond(&invalid).unwrap()[0], "error");
        invalid = request.clone();
        invalid[5][1] = wire(&if d {
            Value::ristretto_groups(&[], b.policy()).unwrap()
        } else {
            Value::groups(&[], b.policy()).unwrap()
        });
        assert_eq!(
            respond(&invalid).unwrap(),
            json!(["error", "primitive-length-mismatch"])
        );
        let validate = json!([
            "zkc.public-primitive/1",
            [],
            "validate",
            [],
            [],
            [wire(&vector)]
        ]);
        assert_eq!(respond(&validate).unwrap(), json!(["ok"]));
        let mut malformed = validate.clone();
        let mut bytes = b.encode_value(&vector).unwrap();
        bytes.push(0);
        malformed[5][0][1] = json!(super::codec::hex(&bytes));
        assert_eq!(respond(&malformed).unwrap()[0], "error");
        let invalid_poly = if d {
            Value::RistrettoPolynomial(vec![RistrettoScalar::ONE].into())
        } else {
            Value::Polynomial(vec![Scalar::from(1)].into())
        };
        let mut bytes = b.encode_value(&invalid_poly).unwrap();
        bytes[10..].fill(0);
        assert_eq!(
            respond(&json!([
                "zkc.public-primitive/1",
                [],
                "validate",
                [],
                [],
                [[
                    invalid_poly.physical_type().logical().spelling(),
                    super::codec::hex(&bytes)
                ]]
            ]))
            .unwrap(),
            json!(["error", "primitive-polynomial"])
        );
    }
}

#[test]
fn ristretto_transcript_byte_service_returns_challenge_bytes_without_reduction() {
    let request = json!([
        "zkc.transcript-request/3",
        "merlin3.ristretto255.scalar64le/1",
        "7a6b632e61727469666163742f31",
        [
            ["append", "62696e64696e67", "01"],
            ["challenge", "6368616c6c656e6765", "64"]
        ]
    ]);
    let mut t = merlin::Transcript::new(b"zkc.artifact/1");
    t.append_message(b"binding", &[1]);
    let mut bytes = [0; 64];
    t.challenge_bytes(b"challenge", &mut bytes);
    assert_eq!(
        respond(&request).unwrap(),
        json!(["ok", super::codec::hex(&bytes)])
    );
}

#[test]
fn profile_tagged_challenges_are_refused_and_nominal_reductions_stay_distinct() {
    for domain in [
        "ristretto255.scalar",
        "merlin3.ristretto255.scalar64le/1",
        "dalek.ristretto255/1",
    ] {
        assert_eq!(
            respond(&json!([
                "zkc.transcript-request/1",
                domain,
                "01",
                [["challenge", "02"]]
            ])),
            Err("primitive-request")
        );
    }
    let request = json!([
        "zkc.transcript-request/3",
        "merlin3.ristretto255.scalar64le/1",
        super::codec::hex(b"zkc.artifact/1"),
        [
            ["append", super::codec::hex(b"binding"), "01"],
            ["challenge", super::codec::hex(b"challenge"), "64"]
        ]
    ]);
    let reply = respond(&request).unwrap();
    let wide: [u8; 64] = super::codec::unhex(reply[1].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap();
    let ristretto = curve25519_dalek::scalar::Scalar::from_bytes_mod_order_wide(&wide);
    let bls = zkc_arkworks::scalar_from_wide_be(&wide);
    assert_ne!(
        ristretto.to_bytes().as_slice(),
        zkc_arkworks::encode_scalar(&bls).unwrap()
    );
    let mut unsupported = request;
    unsupported[1] = json!("merlin3.ristretto255.scalar64be/1");
    assert_eq!(respond(&unsupported), Err("primitive-suite"));
}

#[test]
fn spongefish_reference_bytes_are_frozen_and_requests_fail_closed() {
    let v: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/transcript-vectors.json"
        ))
        .expect("frozen transcript vector fixture must be present"),
    )
    .unwrap();
    for (request, output) in [("first_request", "first"), ("request", "second")] {
        assert_eq!(respond(&v[request]).unwrap(), json!(["ok", v[output]]));
    }
    let valid = &v["request"];
    let mut wrong = valid.clone();
    wrong[1] = json!("merlin3.bls12-381.fr64be/1");
    assert_eq!(respond(&wrong), Err("primitive-suite"));
    let mut wrong = valid.clone();
    wrong[2] = json!([]);
    assert_eq!(respond(&wrong), Err("primitive-history-length"));
    let mut wrong = valid.clone();
    wrong[2][0][1] = json!("0g");
    assert!(respond(&wrong).is_err());
    let mut wrong = valid.clone();
    wrong[2].as_array_mut().unwrap().pop();
    assert_eq!(respond(&wrong), Err("primitive-history-last"));
    for width in ["0", "63", "65", "064"] {
        let mut wrong = valid.clone();
        let steps = wrong[2].as_array_mut().unwrap();
        steps.last_mut().unwrap()[1] = json!(width);
        assert_eq!(respond(&wrong), Err("primitive-transcript-step"));
    }
    // Deliberate byte perturbations in domain, nominal suite, root, origin,
    // payload and request frame change the externally computed challenge.
    for index in [0, 1, 2, 3, 4, 5, 6] {
        let mut wrong = valid.clone();
        let mut bytes = wrong[2][index][1].as_str().unwrap().to_owned();
        let last = bytes.pop().unwrap();
        bytes.push(if last == '0' { '1' } else { '0' });
        wrong[2][index][1] = json!(bytes);
        assert_ne!(respond(&wrong).unwrap(), respond(valid).unwrap());
    }
}

#[test]
fn dynamic_group_primitive_all_domains_bounds_and_exact_operand_types() {
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
    use zkc_runtime::interactive::Value as RuntimeValue;
    let policy = Policy::default();
    let b = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("V", "reference", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let wire = |v: &Value| {
        json!([
            v.physical_type().logical().spelling(),
            super::codec::hex(&b.encode_value(v).unwrap())
        ])
    };
    let g = zkc_arkworks::GroupPoint::generator();
    let r = curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    let p = zkc_arkworks::bn254::G1::generator();
    let q = zkc_arkworks::bn254::G2::generator();
    for (domain, points, point) in [
        (
            "bls12-381.g1",
            Value::groups(&[g, g], &policy).unwrap(),
            Value::Curve(g),
        ),
        (
            "ristretto255.group",
            Value::RistrettoGroups(vec![r, r].into()),
            Value::RistrettoGroup(r),
        ),
        (
            "bn254.g1",
            Value::Bn254G1Vector(vec![p, p].into()),
            Value::Bn254G1(p),
        ),
        (
            "bn254.g2",
            Value::Bn254G2Vector(vec![q, q].into()),
            Value::Bn254G2(q),
        ),
    ] {
        let call = |op: &str, attrs, inputs| {
            respond(&json!([
                "zkc.public-primitive/1",
                [],
                op,
                [domain],
                attrs,
                inputs
            ]))
            .unwrap()
        };
        assert_eq!(
            call(
                "curve.get",
                json!([]),
                json!([wire(&points), wire(&Value::Index(1))])
            ),
            json!(["ok", wire(&point)])
        );
        assert_eq!(
            call("curve.length", json!([]), json!([wire(&points)])),
            json!(["ok", wire(&Value::Index(2))])
        );
        for i in [2, u64::MAX] {
            assert_eq!(
                call(
                    "curve.get",
                    json!([]),
                    json!([wire(&points), wire(&Value::Index(i))])
                ),
                json!(["error", "primitive-index"])
            );
        }
        assert_eq!(
            call(
                "curve.get",
                json!(["0"]),
                json!([wire(&points), wire(&Value::Index(0))])
            )[0],
            "error"
        );
        assert_eq!(
            call(
                "curve.get",
                json!([]),
                json!([wire(&points), wire(&Value::Bool(false))])
            )[0],
            "error"
        );
    }
}
