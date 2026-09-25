//! Standalone local DLEQ equations through the ordinary generic Runner. Test
//! entry material is host supplied; this is not an artifact producer CLI.
#![cfg(feature = "test-utils")]
use zkc_runtime::interactive::Value as RuntimeValue;
mod common;
use common::{backend as new_backend, *};
use serde_json::{Value as Json, json};
use zkc_backends::*;
use zkc_runtime::interactive::{Runner, admit_supplied};

fn observed(site: &str, ty: &str, input: &str, value: &str, output: &str) -> Json {
    json!([
        "op",
        site,
        format!("arkworks/transcript.observe.{ty}"),
        [
            "DLEQ",
            site,
            format!("Schema_{ty}"),
            if site == "challenge_delivery" {
                "V"
            } else {
                "P"
            },
            if site == "challenge_delivery" {
                "P"
            } else {
                "V"
            }
        ],
        [input, value],
        [output]
    ])
}
fn draw() -> Json {
    json!([
        "op",
        "draw",
        "arkworks/transcript.challenge",
        ["DLEQ", "challenge_call", "DrawChallenge", "draw", "V"],
        ["t1"],
        ["c", "t2"]
    ])
}
fn producer() -> Vec<u8> {
    program(
        None,
        &[
            ("bases", "groups"),
            ("x", "field"),
            ("nonce", "nonce"),
            ("t", "transcript"),
        ],
        vec![
            op(
                "commit",
                "arkworks/curve.commit",
                &["bases", "nonce"],
                &["rs", "ready"],
            ),
            observed("commitments", "groups", "t", "rs", "t1"),
            draw(),
            observed("challenge_delivery", "field", "t2", "c", "t3"),
            op(
                "response",
                "arkworks/curve.response",
                &["x", "c", "ready"],
                &["z"],
            ),
            observed("response_delivery", "field", "t3", "z", "t4"),
        ],
        &["groups", "field", "transcript"],
        &["rs", "z", "t4"],
    )
}
fn validator() -> Vec<u8> {
    let mut ops = vec![
        observed("commitments", "groups", "t", "rs", "t1"),
        draw(),
        observed("challenge_delivery", "field", "t2", "c", "t3"),
        observed("response_delivery", "field", "t3", "z", "t4"),
    ];
    for i in 0..2 {
        for (value, prefix) in [("bases", "b"), ("publics", "y"), ("rs", "r")] {
            ops.push(json!([
                "op",
                format!("at_{prefix}{i}"),
                "arkworks/curve.at",
                [i.to_string()],
                [value],
                [format!("{prefix}{i}")]
            ]));
        }
        ops.extend([
            op(
                &format!("lhs{i}"),
                "arkworks/curve.scale",
                &[&format!("b{i}"), "z"],
                &[&format!("lhs{i}")],
            ),
            op(
                &format!("cy{i}"),
                "arkworks/curve.scale",
                &[&format!("y{i}"), "c"],
                &[&format!("cy{i}")],
            ),
            op(
                &format!("rhs{i}"),
                "arkworks/curve.add",
                &[&format!("r{i}"), &format!("cy{i}")],
                &[&format!("rhs{i}")],
            ),
            op(
                &format!("eq{i}"),
                "arkworks/curve.equal",
                &[&format!("lhs{i}"), &format!("rhs{i}")],
                &[&format!("ok{i}")],
            ),
        ]);
    }
    ops.push(op("both", "arkworks/bool.and", &["ok0", "ok1"], &["ok"]));
    ops.push(op("require", "arkworks/control.require", &["ok"], &[]));
    let mut j: Json = serde_json::from_slice(&program(
        None,
        &[
            ("bases", "groups"),
            ("publics", "groups"),
            ("rs", "groups"),
            ("z", "field"),
            ("t", "transcript"),
        ],
        ops,
        &["bool", "transcript"],
        &["ok", "t4"],
    ))
    .unwrap();
    j[4][0][3] = json!("V");
    j[5][0][2][0][0] = json!("V");
    serde_json::to_vec(&j).unwrap()
}
fn root(bases: &Value, publics: &Value, context: &str, backend: &NativeBackend) -> Vec<u8> {
    use zkc_test_support::hex;
    // A bounded TEST root with explicit statement and configuration bytes;
    // Main supplies the admitted-source/descriptor root in the actual driver.
    zkc_runtime::logical::encode_tree(&json!([
        "DLEQ-test-root",
        "source-fixture-v1",
        "descriptor-fixture-v1",
        context,
        hex(&backend.encode_value(bases).unwrap()),
        hex(&backend.encode_value(publics).unwrap()),
        "bls12-381.g1"
    ]))
    .unwrap()
}
fn run_validator(
    root: &[u8],
    bases: Value,
    publics: Value,
    rs: Value,
    z: Value,
) -> (
    Result<Vec<Value>, zkc_runtime::interactive::Stop>,
    NativeBackend,
) {
    let domain = Domain::new("V", "independent_verifier", "main", None);
    let pins = std::collections::BTreeMap::from([
        ("bases".into(), bases.clone()),
        ("publics".into(), publics.clone()),
    ]);
    let mut backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(domain.clone(), None, PublicInputs::Exact(pins)),
        None,
    )
    .unwrap();
    let transcript = backend.issue_transcript(domain, 4, root).unwrap();
    // Candidate values must cross ordinary canonical receiving-side codecs.
    let rs = backend
        .decode_typed_value(rs.physical_type(), &backend.encode_value(&rs).unwrap())
        .unwrap();
    let z = backend
        .decode_typed_value(z.physical_type(), &backend.encode_value(&z).unwrap())
        .unwrap();
    let admitted = admit_supplied(&validator(), &backend).unwrap();
    let runner = Runner::new(
        &admitted,
        "main",
        "V",
        "independent_verifier",
        backend,
        vec![bases, publics, rs, z, transcript],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    finish(runner)
}
#[test]
fn standalone_runner_dleq_honest_false_statement_proof_and_context() {
    let g = GroupPoint::generator();
    let bases = Value::groups(&[g, g.scale(Scalar::from(3))], &Policy::default()).unwrap();
    let publics = Value::groups(
        &[g.scale(Scalar::from(7)), g.scale(Scalar::from(21))],
        &Policy::default(),
    )
    .unwrap();
    let mut backend = backend().build();
    let binding = root(&bases, &publics, "application-A", &backend);
    let nonce = backend
        .issue_test_nonce(domain(), 2, Scalar::from(11))
        .unwrap();
    let old = nonce.clone();
    let transcript = backend.issue_transcript(domain(), 4, &binding).unwrap();
    let (out, backend) = run(
        &producer(),
        backend,
        vec![bases.clone(), f(7), nonce, transcript],
    );
    let out = out.unwrap();
    let Value::Groups(rs) = &out[0] else { panic!() };
    assert_eq!(
        rs.as_ref(),
        &[g.scale(Scalar::from(11)), g.scale(Scalar::from(33))]
    );
    // Prior research public nonce point fixture (k=11), independent frozen bytes.
    assert_eq!(
        zkc_test_support::hex(&rs[0].to_bytes().unwrap()),
        "80fd75ebcc0a21649e3177bcce15426da0e4f25d6828fbf4038d4d7ed3bd4421de3ef61d70f794687b12b2d571971a55"
    );
    assert_eq!(backend.observe(token(&old)).unwrap().stage, "spent");
    let (valid, validator_backend) = run_validator(
        &binding,
        bases.clone(),
        publics.clone(),
        out[0].clone(),
        out[1].clone(),
    );
    assert!(matches!(valid.unwrap()[0], Value::Bool(true)));
    assert_eq!(validator_backend.active_frames(), 0);
    for change in 0..4 {
        let (mut r, mut z, mut ys, mut root) = (
            out[0].clone(),
            out[1].clone(),
            publics.clone(),
            binding.clone(),
        );
        match change {
            0 => z = Value::Field(scalar(&z) + Scalar::from(1)),
            1 => r = Value::groups(&[rs[0].add(&g), rs[1]], &Policy::default()).unwrap(),
            2 => {
                ys = Value::groups(
                    &[g.scale(Scalar::from(7)), g.scale(Scalar::from(22))],
                    &Policy::default(),
                )
                .unwrap()
            }
            3 => root = self::root(&bases, &publics, "application-B", &backend),
            _ => unreachable!(),
        }
        let (bad, b) = run_validator(&root, bases.clone(), ys, r, z);
        assert_eq!(code(&bad.unwrap_err()), "rejected:require");
        assert_eq!(b.active_frames(), 0);
    }
    // Bind a false DLEQ statement consistently into BOTH roots. Producing a
    // response for x=7 does not make a mismatched second public key true.
    let false_publics = Value::groups(
        &[g.scale(Scalar::from(7)), g.scale(Scalar::from(22))],
        &Policy::default(),
    )
    .unwrap();
    let binding = root(&bases, &false_publics, "application-A", &backend);
    let mut b = new_backend().build();
    let nonce = b.issue_test_nonce(domain(), 2, Scalar::from(11)).unwrap();
    let transcript = b.issue_transcript(domain(), 4, &binding).unwrap();
    let (out, _) = run(&producer(), b, vec![bases.clone(), f(7), nonce, transcript]);
    let out = out.unwrap();
    let (bad, _) = run_validator(
        &binding,
        bases,
        false_publics,
        out[0].clone(),
        out[1].clone(),
    );
    assert_eq!(code(&bad.unwrap_err()), "rejected:require");
}
