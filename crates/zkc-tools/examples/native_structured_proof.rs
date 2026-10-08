//! Generic proof-host clients for a record containing a three-way dynamic sum.
#[path = "support/native_transcript.rs"]
mod reference;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, Scalar, Value, Variant,
};
use zkc_runtime::interactive::{LogicalType, Value as RuntimeValue, admit_supplied};
use zkc_test_support::variants::logical;
use zkc_tools::proof::{NativeDeployment, hex};
fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("Alice", "test", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn batch(tag: usize, count: usize) -> Value {
    let ty = LogicalType::parse(&logical(
        "Batch",
        json!([
            ["none", []],
            ["plain", ["vector:bls12-381.fr"]],
            ["scaled", ["vector:bls12-381.fr", "field:bls12-381.fr"]]
        ]),
    ))
    .unwrap();
    let vector = Value::Vector(
        (1..=count)
            .map(|x| Scalar::from(x as u64))
            .collect::<Vec<_>>()
            .into(),
    );
    Value::Variant(
        Variant::new(
            ty.variant_descriptor().unwrap().clone(),
            tag,
            match tag {
                0 => vec![],
                1 => vec![vector],
                2 => vec![vector, Value::Field(Scalar::from(3))],
                _ => unreachable!(),
            },
        )
        .unwrap(),
    )
}
fn inputs(envelope: &Json, producing: bool, tag: usize, count: usize) -> Json {
    let codec = backend();
    let value = |port: &Json| {
        let port: usize = port.as_str().unwrap().parse().unwrap();
        let value = match port {
            0 => Value::Curve(GroupPoint::generator()),
            1 => Value::Field(Scalar::from(3)),
            2 => Value::Curve(GroupPoint::generator().scale(Scalar::from(3))),
            5 => batch(tag, count),
            6 => Value::Index(count as u64),
            7 => Value::Field(Scalar::from(
                (count * (count + 1) / 2 * if tag == 2 { 3 } else { 1 }) as u64,
            )),
            8 => Value::Index(tag as u64),
            _ => panic!("port {port}"),
        };
        json!(hex(&codec.encode_native_value(&value).unwrap()))
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(&p[1])]))
        .collect();
    let role = if producing { "Alice" } else { "Bob" };
    let map = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let data: Vec<_> = map[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", value(&p[0])]]))
        .collect();
    let services: Vec<_> = map[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "1"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        services,
        envelope[2][3].as_array().unwrap().len().to_string()
    ])
}
fn clean(report: &zkc_tools::proof::NativeProofReport) {
    assert!(!report.outcome.as_ref().err().is_some_and(
        |e| e.starts_with("native-proof-cleanup") || e == "native-proof-active-frames"
    ));
    assert!(
        report
            .resources
            .iter()
            .all(|r| r["kind"] != "service" || r["leased"] == false)
    );
}
fn run(directory: &Path) {
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        if let Some(kind) = case["standalone"].as_str() {
            standalone(directory, name, kind, &envelope, &bytes);
            continue;
        }
        let deployment = NativeDeployment::admit(&bytes, &digest(&bytes), Default::default())
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        // Reverse challenge delivery is observed but absent from proof bytes.
        // Its descriptor origin and full payload type must still match the
        // actual helper; a row count or common observer name is insufficient.
        let reverse = envelope[2][3][2][1].clone();
        for missing in [true, false] {
            let mut changed = envelope.clone();
            let row = changed[2][5]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|r| r[0] == reverse)
                .unwrap();
            if missing {
                row[0] = json!("00");
            } else {
                row[1] = json!("bool");
                row[2] = json!("zkcv.bool/1");
            }
            changed[3] = json!(digest(&reference::tree(&changed[2])));
            let encoded = serde_json::to_vec(&changed).unwrap();
            let error = NativeDeployment::admit(&encoded, &digest(&encoded), Default::default())
                .expect_err("changed descriptor admitted");
            assert!(
                error.contains(if missing {
                    "native-proof-message-map"
                } else {
                    "native-proof-state-chain"
                }),
                "{error}"
            );
        }
        // Same wire layout, different nominal record identity. Recompute the
        // descriptor pin so semantic type comparison must reject this change.
        let mut renamed = envelope.clone();
        renamed[2][5][0][1] = json!(logical(
            "OtherAnnouncement",
            json!([[
                "record",
                [
                    "group:bls12-381.g1",
                    batch(0, 0).physical_type().logical().spelling()
                ]
            ]])
        ));
        renamed[3] = json!(digest(&reference::tree(&renamed[2])));
        let changed = serde_json::to_vec(&renamed).unwrap();
        assert_eq!(
            NativeDeployment::admit(&changed, &digest(&changed), Default::default()).unwrap_err(),
            "native-proof-wire-map"
        );
        let original: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
        assert_eq!(original[0], "zkc.program/1");
        for (tag, count) in [(0, 0), (1, 0), (1, 1), (1, 4), (2, 0), (2, 1), (2, 7)] {
            let p = inputs(&envelope, true, tag, count);
            let v = inputs(&envelope, false, tag, count);
            let produced = deployment
                .execute_test(&p, None, BTreeMap::from([(3, vec![Scalar::from(5)])]))
                .unwrap();
            clean(&produced);
            let proof = produced
                .outcome
                .unwrap_or_else(|e| panic!("{name}/{tag}/{count}: {e}"));
            verify_reference(&envelope, &p, &proof, tag, count);
            let validated = deployment.execute(&v, Some(&proof)).unwrap();
            clean(&validated);
            validated.outcome.unwrap();
            for length in [0, 7, 39, 47, proof.len() - 1] {
                let r = deployment.execute(&v, Some(&proof[..length])).unwrap();
                clean(&r);
                assert!(r.outcome.is_err());
            }
            let mut extra = proof.clone();
            extra.push(0);
            assert!(
                deployment
                    .execute(&v, Some(&extra))
                    .unwrap()
                    .outcome
                    .is_err()
            );
            // A dishonest producer recomputes the entire transcript with the
            // authorized public configuration but a different private batch.
            // Rejection must come from the authored guards, not a stale hash.
            for alternative in [
                batch((tag + 1) % 3, count),
                batch(1, count + 1),
                batch(2, count + 1),
            ] {
                let mut dishonest = p.clone();
                for row in dishonest[2].as_array_mut().unwrap() {
                    if row[0] == "5" {
                        row[1][1] =
                            json!(hex(&backend().encode_native_value(&alternative).unwrap()));
                    }
                }
                let wrong = deployment
                    .execute_test(
                        &dishonest,
                        None,
                        BTreeMap::from([(3, vec![Scalar::from(5)])]),
                    )
                    .unwrap();
                clean(&wrong);
                let wrong = wrong.outcome.unwrap();
                let rejected = deployment.execute(&v, Some(&wrong)).unwrap();
                clean(&rejected);
                assert!(rejected.outcome.is_err(), "unauthorized batch accepted");
            }
            let stem = format!("{name}_{tag}_{count}");
            for (suffix, data) in [
                ("producer.json", serde_json::to_vec(&p).unwrap()),
                ("validator.json", serde_json::to_vec(&v).unwrap()),
                ("proof", proof),
            ] {
                std::fs::write(directory.join(format!("{stem}.{suffix}")), data).unwrap();
            }
        }
        println!(
            "{name}: all alternatives, empty and dynamic batches, adaptive refusal and cleanup passed"
        );
    }
}
fn main() {
    run(Path::new(
        &std::env::args().nth(1).expect("generated corpus directory"),
    ));
}

// Upstream transcript primitives and direct frame parsing, independent of the
// native decoder, origin builder and proof-host transition code.
fn verify_reference(envelope: &Json, input: &Json, proof: &[u8], tag: usize, count: usize) {
    let root = reference::root(envelope, input);
    assert_eq!(&proof[..8], b"ZKCPRF01");
    assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
    let mut event = 0;
    let mut origin = |kind: &str, site: &str, sender: &str, receiver: &str| {
        let data = if kind == "query" {
            json!([
                "query",
                "main",
                site,
                "input_4",
                "random.bls12-381.fr/1",
                "draw",
                "Bob"
            ])
        } else {
            json!(["message", "main", site, site, sender, receiver])
        };
        let template = reference::tree(&json!([
            "zkc.native-origin-template/1",
            "main",
            [],
            [],
            data
        ]));
        assert_eq!(envelope[2][3][event], json!([kind, hex(&template)]));
        event += 1;
        reference::tree(&json!(["zkc.native-origin/2", "main", [], [], data]))
    };
    let mut position = 40;
    let mut frame = || {
        let n = u64::from_le_bytes(proof[position..position + 8].try_into().unwrap()) as usize;
        position += 8;
        let bytes = &proof[position..position + n];
        position += n;
        bytes
    };
    let record = frame();
    assert_eq!(&record[..10], b"ZKCV\x01\x41\0\0\0\0");
    let size = u32::from_le_bytes(record[10..14].try_into().unwrap()) as usize;
    assert_eq!(size, 54);
    let commitment = reference::group(&record[14..14 + size]);
    let mut batch = b"ZKCV\x01\x41".to_vec();
    batch.extend_from_slice(&(tag as u32).to_le_bytes());
    if tag != 0 {
        let mut vector = b"ZKCV\x01\x42".to_vec();
        vector.extend_from_slice(&(count as u32).to_le_bytes());
        for i in 1..=count {
            vector.extend_from_slice(&reference::scalar_wire(Scalar::from(i as u64))[6..]);
        }
        batch.extend_from_slice(&(vector.len() as u32).to_le_bytes());
        batch.extend_from_slice(&vector);
        if tag == 2 {
            let factor = reference::scalar_wire(Scalar::from(3));
            batch.extend_from_slice(&(factor.len() as u32).to_le_bytes());
            batch.extend_from_slice(&factor);
        }
    }
    assert_eq!(
        &record[14 + size..18 + size],
        &(batch.len() as u32).to_le_bytes()
    );
    assert_eq!(&record[18 + size..], &batch);
    let mut transcript = reference::Transcript::new(envelope[2][1][5].as_str().unwrap(), &root);
    transcript.absorb(b"origin", &origin("message", "commitment", "Alice", "Bob"));
    transcript.absorb(b"value", record);
    transcript.absorb(
        b"origin",
        &origin("query", "draw_challenge", "Bob", "Alice"),
    );
    let challenge = transcript.draw();
    transcript.absorb(b"origin", &origin("message", "challenge", "Bob", "Alice"));
    transcript.absorb(b"value", &reference::scalar_wire(challenge));
    let response = frame();
    let scalar = reference::scalar(response);
    transcript.absorb(b"origin", &origin("message", "response", "Alice", "Bob"));
    transcript.absorb(b"value", response);
    assert_eq!(scalar, Scalar::from(5) + challenge * Scalar::from(3));
    assert_eq!(
        GroupPoint::generator().scale(scalar),
        commitment.add(&GroupPoint::generator().scale(Scalar::from(3) * challenge))
    );
    assert_eq!(position, proof.len());
    assert_eq!(event, 4);
}

fn standalone(directory: &Path, name: &str, kind: &str, envelope: &Json, bytes: &[u8]) {
    let deployment = NativeDeployment::admit(bytes, &digest(bytes), Default::default()).unwrap();
    let (value, tag, body) = match kind {
        "vector" => (
            Value::Vector(vec![Scalar::from(7)].into()),
            66,
            reference::scalar_wire(Scalar::from(7))[6..].to_vec(),
        ),
        "groups" => (
            Value::Groups(vec![GroupPoint::generator()].into()),
            67,
            GroupPoint::generator().to_bytes().unwrap().to_vec(),
        ),
        "indices" => (
            Value::Indices(vec![u64::MAX].into()),
            68,
            u64::MAX.to_le_bytes().to_vec(),
        ),
        _ => unreachable!(),
    };
    let mut expected = b"ZKCV\x01".to_vec();
    expected.push(tag);
    expected.extend_from_slice(&1u32.to_le_bytes());
    expected.extend(body);
    assert_eq!(backend().encode_native_value(&value).unwrap(), expected);
    let yes = hex(b"ZKCV\x01\x05\x01");
    let input = |role| {
        let map = envelope[6]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r[0] == role)
            .unwrap();
        let public: Vec<_> = envelope[2][4]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| json!([p[0], p[1], yes]))
            .collect();
        let data: Vec<_> = map[2]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| {
                json!([
                    p[0],
                    [
                        "wire",
                        if p[0] == "0" {
                            hex(&expected)
                        } else {
                            yes.clone()
                        }
                    ]
                ])
            })
            .collect();
        json!(["zkc.native-proof-inputs/1", public, data, "", [], "0"])
    };
    let p = input("Alice");
    let v = input("Bob");
    let produced = deployment.execute(&p, None).unwrap();
    clean(&produced);
    let proof = produced.outcome.unwrap();
    let validated = deployment.execute(&v, Some(&proof)).unwrap();
    clean(&validated);
    validated.outcome.unwrap();
    assert_eq!(&proof[..8], b"ZKCPRF01");
    assert_eq!(
        &proof[8..40],
        &Sha256::digest(reference::root(envelope, &p))[..]
    );
    assert_eq!(&proof[40..48], &(expected.len() as u64).to_le_bytes());
    assert_eq!(&proof[48..], &expected);
    // The current program remains executable. Retired deployment tags refuse
    // before any message-type interpretation, even after recomputing pins.
    admit_supplied(envelope[4].as_str().unwrap().as_bytes(), &backend()).unwrap();
    let mut changed = envelope.clone();
    changed[0] = json!("zkc.native-proof/3");
    changed[2][0] = json!("zkc.native-proof-descriptor/3");
    changed[2][1][0] = json!("zkc.native-proof-policy/3");
    changed[3] = json!(digest(&reference::tree(&changed[2])));
    let changed = serde_json::to_vec(&changed).unwrap();
    assert_eq!(
        NativeDeployment::admit(&changed, &digest(&changed), Default::default()).unwrap_err(),
        "native-proof-format"
    );
    for (suffix, data) in [
        ("producer.json", serde_json::to_vec(&p).unwrap()),
        ("validator.json", serde_json::to_vec(&v).unwrap()),
        ("proof", proof),
    ] {
        std::fs::write(directory.join(format!("{name}.{suffix}")), data).unwrap();
    }
}
