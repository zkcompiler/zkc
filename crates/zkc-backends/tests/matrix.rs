//! Matrix data is canonical, field-specific and independent of program size.
#[path = "domains/support.rs"]
mod support;
use rand::{Rng, SeedableRng, rngs::StdRng};
use serde_json::json;
use support::{Controlled, assert_value, backend, one, program};
use zkc_backends::{KoalaBear, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{
    Backend, ErrorCode, OperationBinding, Value as RuntimeValue, admit_supplied,
};

fn binding(d: usize, name: &str) -> OperationBinding {
    let (field, provider) = [
        ("bls12-381.fr", "arkworks"),
        ("ristretto255.scalar", "dalek"),
        ("koala-bear", "plonky3"),
    ][d];
    OperationBinding {
        contract: name.into(),
        arguments: vec![field.into()],
        implementation: format!("{provider}/{name}"),
    }
}
fn vector(d: usize, xs: &[u64]) -> Value {
    if d < 2 {
        support::vector(d == 1, xs)
    } else {
        Value::koala_bear_vector(
            &xs.iter()
                .map(|n| KoalaBear::new(*n as u32))
                .collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    }
}
fn scalar(d: usize, n: u64) -> Value {
    match d {
        0 => Value::Field(Scalar::from(n)),
        1 => Value::RistrettoField(RistrettoScalar::from(n)),
        _ => Value::KoalaBearField(KoalaBear::new(n as u32)),
    }
}
fn matrix(d: usize, rows: usize, columns: usize, entries: &[(u32, u32, u64)]) -> Value {
    let p = Policy::default();
    match d {
        0 => Value::matrix(
            rows,
            columns,
            &entries
                .iter()
                .map(|&(r, c, a)| (r, c, Scalar::from(a)))
                .collect::<Vec<_>>(),
            &p,
        ),
        1 => Value::ristretto_matrix(
            rows,
            columns,
            &entries
                .iter()
                .map(|&(r, c, a)| (r, c, RistrettoScalar::from(a)))
                .collect::<Vec<_>>(),
            &p,
        ),
        _ => Value::koala_bear_matrix(
            rows,
            columns,
            &entries
                .iter()
                .map(|&(r, c, a)| (r, c, KoalaBear::new(a as u32)))
                .collect::<Vec<_>>(),
            &p,
        ),
    }
    .unwrap()
}
fn call(d: usize, name: &str, attrs: &[&str], args: Vec<Value>) -> Value {
    one(backend(Policy::default()), binding(d, name), attrs, args)
        .0
        .unwrap()
        .remove(0)
}
fn wire(d: usize, rows: u32, columns: u32, entries: &[(u32, u32, u64)]) -> Vec<u8> {
    let mut b = b"ZKCV\x01".to_vec();
    b.push(23 + d as u8);
    for n in [rows, columns, entries.len() as u32] {
        b.extend(n.to_le_bytes());
    }
    for &(r, c, a) in entries {
        b.extend(r.to_le_bytes());
        b.extend(c.to_le_bytes());
        if d == 2 {
            b.extend((a as u32).to_le_bytes());
        } else {
            b.extend(a.to_le_bytes());
            b.extend([0; 24]);
        }
    }
    b
}
#[test]
fn random_sparse_products_and_bilinear_match_coordinate_oracle() {
    let mut rng = StdRng::seed_from_u64(83117);
    for d in 0..3 {
        for (rows, columns) in [(0, 0), (0, 7), (9, 0), (1, 1), (5, 7), (17, 31), (73, 19)] {
            let entries = (0..rows)
                .flat_map(|r| (0..columns).map(move |c| (r, c)))
                .filter_map(|(r, c)| {
                    if rng.gen_ratio(1, 5) {
                        Some((r, c, rng.gen_range(1..1000)))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let x = (0..columns)
                .map(|_| rng.gen_range(0..1000))
                .collect::<Vec<u64>>();
            let y = (0..rows)
                .map(|_| rng.gen_range(0..1000))
                .collect::<Vec<u64>>();
            let modulus = if d == 2 { 2_130_706_433u128 } else { u128::MAX };
            let expected = (0..rows)
                .map(|r| {
                    (entries
                        .iter()
                        .filter(|e| e.0 == r)
                        .map(|e| u128::from(e.2) * u128::from(x[e.1 as usize]))
                        .sum::<u128>()
                        % modulus) as u64
                })
                .collect::<Vec<_>>();
            let transpose = (0..columns)
                .map(|c| {
                    (entries
                        .iter()
                        .filter(|e| e.1 == c)
                        .map(|e| u128::from(e.2) * u128::from(y[e.0 as usize]))
                        .sum::<u128>()
                        % modulus) as u64
                })
                .collect::<Vec<_>>();
            let bilinear = (expected
                .iter()
                .zip(&y)
                .map(|(a, b)| u128::from(*a) * u128::from(*b))
                .sum::<u128>()
                % modulus) as u64;
            let m = matrix(d, rows as usize, columns as usize, &entries);
            assert_value(
                &call(d, "matrix.mul_vector", &[], vec![m.clone(), vector(d, &x)]),
                &vector(d, &expected),
            );
            assert_value(
                &call(
                    d,
                    "matrix.transpose_mul_vector",
                    &[],
                    vec![m.clone(), vector(d, &y)],
                ),
                &vector(d, &transpose),
            );
            assert_value(
                &call(
                    d,
                    "matrix.bilinear",
                    &[],
                    vec![m.clone(), vector(d, &y), vector(d, &x)],
                ),
                &scalar(d, bilinear),
            );
            assert_value(
                &call(
                    d,
                    "matrix.shape_check",
                    &[&rows.to_string(), &columns.to_string()],
                    vec![m.clone()],
                ),
                &Value::Bool(true),
            );
            assert_value(
                &call(
                    d,
                    "matrix.shape_check",
                    &[&(rows + 1).to_string(), &columns.to_string()],
                    vec![m.clone()],
                ),
                &Value::Bool(false),
            );
            let b = backend(Policy::default());
            let encoded = b.encode_value(&m).unwrap();
            assert_eq!(encoded, wire(d, rows, columns, &entries));
            assert_value(
                &b.decode_typed_value(m.physical_type(), &encoded).unwrap(),
                &m,
            );
            assert!(
                Value::typed_wire_retained_bytes_bound(
                    m.physical_type(),
                    encoded.len(),
                    b.policy()
                )
                .unwrap()
                    >= m.retained_bytes()
            );
            if let (Value::Matrix(a), Value::Matrix(b)) = (&m, &m.clone()) {
                assert_eq!(a.entries().as_ptr(), b.entries().as_ptr());
            }
        }
    }
}
#[test]
fn wire_refuses_every_noncanonical_structure_before_backing_allocation() {
    for d in 0..3 {
        let b = backend(Policy::default());
        let ty = matrix(d, 2, 3, &[]).physical_type();
        let valid = wire(d, 2, 3, &[(0, 1, 3), (1, 0, 4)]);
        let mut cases = vec![
            (
                wire(d, 2, 3, &[(1, 0, 3), (0, 1, 4)]),
                "refused:matrix-order",
            ),
            (
                wire(d, 2, 3, &[(0, 1, 3), (0, 1, 4)]),
                "refused:matrix-order",
            ),
            (wire(d, 2, 3, &[(0, 1, 0)]), "refused:matrix-zero"),
            (wire(d, 2, 3, &[(2, 0, 3)]), "refused:matrix-index"),
            (wire(d, 2, 3, &[(0, 3, 3)]), "refused:matrix-index"),
            (wire(d, 0, 3, &[(0, 0, 3)]), "refused:matrix-count"),
            (wire(d, 65537, 3, &[]), "exhausted:matrix-dimension-limit"),
            (
                wire(d, u32::MAX, u32::MAX, &[]),
                "exhausted:matrix-dimension-limit",
            ),
        ];
        for end in 0..valid.len() {
            cases.push((
                valid[..end].to_vec(),
                if end < 6 {
                    "refused:wire-header"
                } else {
                    "refused:wire-length"
                },
            ));
        }
        let mut trailing = valid.clone();
        trailing.push(0);
        cases.push((trailing, "refused:wire-length"));
        let mut count = wire(d, 65536, 65536, &[]);
        count[14..18].copy_from_slice(&u32::MAX.to_le_bytes());
        cases.push((count, "exhausted:matrix-nonzero-limit"));
        let mut count = valid.clone();
        count[14..18].copy_from_slice(&7u32.to_le_bytes());
        cases.push((count, "refused:matrix-count"));
        let mut count = wire(d, 65536, 65536, &[]);
        count[14..18].copy_from_slice(&1_048_576u32.to_le_bytes());
        cases.push((count, "refused:wire-length"));
        let mut wrong = valid.clone();
        wrong[5] = 23 + ((d + 1) % 3) as u8;
        cases.push((wrong, "refused:wire-header"));
        for (bad, code) in cases {
            assert_eq!(
                b.decode_typed_value(ty.clone(), &bad).unwrap_err().code,
                code
            );
        }
        let mut bad = valid.clone();
        let width = if d == 2 { 4 } else { 32 };
        bad[26..26 + width].fill(255);
        assert!(b.decode_typed_value(ty.clone(), &bad).is_err());
        let low_wire = backend(Policy {
            max_wire_bytes: valid.len() - 1,
            ..Policy::default()
        });
        assert_eq!(
            low_wire
                .decode_typed_value(ty.clone(), &valid)
                .unwrap_err()
                .code,
            "exhausted:wire-bytes"
        );
        let low_value = backend(Policy {
            max_value_bytes: 256,
            ..Policy::default()
        });
        assert_eq!(
            low_value
                .decode_typed_value(ty.clone(), &valid)
                .unwrap_err()
                .code,
            "exhausted:output-bytes"
        );
    }
    for (rows, columns) in [(usize::MAX, 1), (1, usize::MAX), (65537, 0)] {
        assert_eq!(
            Value::matrix(rows, columns, &[], &Policy::default())
                .unwrap_err()
                .code,
            "exhausted:matrix-dimension-limit"
        );
    }
    for es in [
        vec![(0, 0, Scalar::from(0))],
        vec![(0, 0, Scalar::from(1)), (0, 0, Scalar::from(2))],
        vec![(1, 0, Scalar::from(1)), (0, 0, Scalar::from(2))],
    ] {
        assert!(Value::matrix(2, 2, &es, &Policy::default()).is_err());
    }
}
#[test]
fn nominal_signatures_shapes_attributes_and_resource_failures_are_closed() {
    for d in 0..3 {
        let m = matrix(d, 2, 3, &[(0, 1, 7)]);
        for (name, args) in [
            ("matrix.mul_vector", vec![m.clone(), vector(d, &[1, 2])]),
            (
                "matrix.transpose_mul_vector",
                vec![m.clone(), vector(d, &[1, 2, 3])],
            ),
            (
                "matrix.bilinear",
                vec![m.clone(), vector(d, &[1]), vector(d, &[1, 2, 3])],
            ),
            (
                "matrix.bilinear",
                vec![m.clone(), vector(d, &[1, 2]), vector(d, &[1, 2])],
            ),
        ] {
            assert_eq!(
                one(backend(Policy::default()), binding(d, name), &[], args)
                    .0
                    .unwrap_err(),
                "refused:matrix-shape"
            );
        }
        let row = binding(d, "matrix.shape_check");
        let sig = row.signature().unwrap();
        assert_eq!(
            backend(Policy::default()).binding_signature(&row),
            Some(sig.clone())
        );
        for attrs in [
            vec![],
            vec!["1"],
            vec!["1", "2", "3"],
            vec!["01", "2"],
            vec!["65537", "0"],
            vec!["18446744073709551616", "0"],
        ] {
            let plan = program(
                std::slice::from_ref(&row),
                &sig.inputs,
                vec![json!(["op", "site", "b0", attrs, ["a0"], ["out"]])],
                &sig.outputs,
                &["out".into()],
            );
            assert_eq!(
                admit_supplied(&plan, &backend(Policy::default()))
                    .unwrap_err()
                    .code,
                ErrorCode::Attributes
            );
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.attributes = Some(attrs.iter().map(|s| s.to_string()).collect());
            assert_eq!(
                one(controlled, row.clone(), &["2", "3"], vec![m.clone()])
                    .0
                    .unwrap_err(),
                "refused:kernel-attributes"
            );
        }
        let mut wrong = Controlled::new(backend(Policy::default()));
        wrong.substitute = Some(matrix((d + 1) % 3, 2, 3, &[(0, 1, 7)]));
        assert_eq!(
            one(wrong, row.clone(), &["2", "3"], vec![m.clone()])
                .0
                .unwrap_err(),
            "refused:kernel-operands"
        );
        let mut low = Controlled::new(backend(Policy::default()));
        low.output_limit = Some(0);
        assert_eq!(
            one(
                low,
                binding(d, "matrix.mul_vector"),
                &[],
                vec![m.clone(), vector(d, &[1, 2, 3])]
            )
            .0
            .unwrap_err(),
            "exhausted:output-bytes"
        );
        let p = Policy {
            max_table_elements: 1,
            ..Policy::default()
        };
        assert_eq!(
            one(
                backend(p),
                binding(d, "matrix.mul_vector"),
                &[],
                vec![matrix(d, 2, 0, &[]), vector(d, &[])]
            )
            .0
            .unwrap_err(),
            "exhausted:element-limit"
        );
        let p = Policy {
            max_value_bytes: 512,
            ..Policy::default()
        };
        assert_eq!(
            one(
                backend(p),
                binding(d, "matrix.mul_vector"),
                &[],
                vec![matrix(d, 65536, 0, &[]), vector(d, &[])]
            )
            .0
            .unwrap_err(),
            "exhausted:output-bytes"
        );
    }
}
#[test]
fn nonzeros_use_separate_cap_and_large_inputs_keep_constant_size_programs() {
    for d in 0..3 {
        let entries = (0..65537)
            .map(|n| ((n / 257) as u32, (n % 257) as u32, 1))
            .collect::<Vec<_>>();
        let m = matrix(d, 257, 257, &entries);
        let b = backend(Policy::default());
        let wire = b.encode_value(&m).unwrap();
        let m = b.decode_typed_value(m.physical_type(), &wire).unwrap();
        // 65537 entries: more than the default dense vector cap, which is what
        // makes the constant-size program below the thing worth checking.
        let expected = (0..257)
            .map(|r| {
                if r < 255 {
                    257
                } else if r == 255 {
                    2
                } else {
                    0
                }
            })
            .collect::<Vec<_>>();
        assert_value(
            &call(d, "matrix.mul_vector", &[], vec![m, vector(d, &[1; 257])]),
            &vector(d, &expected),
        );
        let row = binding(d, "matrix.mul_vector");
        let sig = row.signature().unwrap();
        let p = program(
            &[row],
            &sig.inputs,
            vec![json!(["op", "site", "b0", [], ["a0", "a1"], ["out"]])],
            &sig.outputs,
            &["out".into()],
        );
        assert!(p.len() < 1500);
        assert!(wire.len() > 700000);
    }
}

#[test]
fn exact_nonzero_cap_and_dimension_cap_are_independent_of_dense_vector_policy() {
    let n = 1usize << 20;
    let mut bytes = Vec::with_capacity(18 + 12 * n);
    bytes.extend_from_slice(b"ZKCV\x01\x19");
    for v in [1024u32, 1024, n as u32] {
        bytes.extend(v.to_le_bytes());
    }
    for k in 0..n {
        bytes.extend(((k / 1024) as u32).to_le_bytes());
        bytes.extend(((k % 1024) as u32).to_le_bytes());
        bytes.extend(1u32.to_le_bytes());
    }
    let p = Policy {
        max_table_elements: 1,
        ..Policy::default()
    };
    let b = backend(p);
    let ty = matrix(2, 0, 0, &[]).physical_type();
    let m = b.decode_typed_value(ty.clone(), &bytes).unwrap();
    assert_eq!(b.encode_value(&m).unwrap(), bytes);
    assert_value(
        &call(2, "matrix.mul_vector", &[], vec![m, vector(2, &[1; 1024])]),
        &vector(2, &[1024; 1024]),
    );
    // A final bad coefficient cannot be hidden behind a valid prefix.
    let length = bytes.len();
    bytes[length - 4..].fill(0);
    assert_eq!(
        b.decode_typed_value(ty.clone(), &bytes).unwrap_err().code,
        "refused:matrix-zero"
    );
    bytes[14..18].copy_from_slice(&((n + 1) as u32).to_le_bytes());
    assert_eq!(
        b.decode_typed_value(ty.clone(), &bytes).unwrap_err().code,
        "exhausted:matrix-nonzero-limit"
    );
    for (r, c) in [(65536, 0), (0, 65536), (65536, 65536)] {
        let m = matrix(2, r, c, &[]);
        assert_value(
            &b.decode_typed_value(ty.clone(), &b.encode_value(&m).unwrap())
                .unwrap(),
            &m,
        );
    }
}

#[test]
fn matrix_transcript_codec_binds_canonical_bytes_and_refuses_cross_suite_payloads() {
    use zkc_runtime::interactive::Identity;
    for d in 0..2 {
        let field = if d == 0 {
            Identity::Bls12381Fr
        } else {
            Identity::Ristretto255Scalar
        };
        let suite = if field == Identity::Bls12381Fr {
            Identity::Merlin3Fr64Be
        } else {
            Identity::Merlin3Ristretto64Le
        };
        let mut challenges = Vec::new();
        for coefficient in [5, 6] {
            let m = matrix(d, 2, 3, &[(0, 0, coefficient), (1, 2, 7)]);
            let mut b = backend(Policy::default());
            let root = zkc_runtime::logical::encode_tree(&json!(["matrix-root"])).unwrap();
            let t = b
                .issue_transcript_for(suite, support::domain(), 2, &root)
                .unwrap();
            let observe = OperationBinding {
                contract: "transcript.observe.matrix".into(),
                arguments: vec![
                    suite.name().into(),
                    field.name().into(),
                    m.physical_type().logical().codec().unwrap(),
                ],
                implementation: format!(
                    "{}/transcript.observe.matrix",
                    if d == 0 { "arkworks" } else { "dalek" }
                ),
            };
            assert_eq!(
                b.binding_signature(&observe),
                Some(observe.signature().unwrap())
            );
            let challenge = support::binding(d == 1, "transcript.challenge");
            let outputs = challenge.signature().unwrap().outputs;
            let plan = program(
                &[observe.clone(), challenge],
                &[t.physical_type(), m.physical_type()],
                vec![
                    json!([
                        "op",
                        "observe",
                        "b0",
                        ["Source", "message", "Schema", "P", "V"],
                        ["a0", "a1"],
                        ["t1"]
                    ]),
                    json!([
                        "op",
                        "challenge",
                        "b1",
                        ["Source", "call", "Draw", "draw", "V"],
                        ["t1"],
                        ["c", "t2"]
                    ]),
                ],
                &outputs,
                &["c".into(), "t2".into()],
            );
            let mut direct = merlin::Transcript::new(b"zkc.artifact/1");
            direct.append_message(b"binding", &root);
            for (kind, body) in [
                (
                    "message",
                    json!(["message", "Source", "message", "Schema", "P", "V"]),
                ),
                (
                    "challenge",
                    json!(["challenge", "Source", "call", "Draw", "draw", "V"]),
                ),
            ] {
                let origin = zkc_runtime::logical::encode_tree(&json!([
                    "zkc.logical-origin/1",
                    "main",
                    "instance",
                    [],
                    body
                ]))
                .unwrap();
                direct.append_message(b"origin", &origin);
                if kind == "message" {
                    direct.append_message(b"value", &b.encode_value(&m).unwrap());
                }
            }
            let mut wide = [0; 64];
            direct.challenge_bytes(b"challenge", &mut wide);
            let expected = if d == 0 {
                Value::Field(zkc_arkworks::scalar_from_wide_be(&wide))
            } else {
                Value::RistrettoField(RistrettoScalar::from_bytes_mod_order_wide(&wide))
            };
            let (result, b) = support::run_program(b, &plan, vec![t, m]);
            let result = result.unwrap();
            assert_value(&result[0], &expected);
            challenges.push(b.encode_value(&result[0]).unwrap());
            let mut incompatible = observe;
            incompatible.arguments[1] = "koala-bear".into();
            incompatible.arguments[2] = "zkcv.matrix.koala-bear/1".into();
            assert!(incompatible.signature().is_err());
            assert!(b.binding_signature(&incompatible).is_none());
        }
        assert_ne!(challenges[0], challenges[1]);
    }
}
