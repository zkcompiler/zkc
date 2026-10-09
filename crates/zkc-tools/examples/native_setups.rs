//! Two independently authorized PCS setups through the same interpreter.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path, sync::Arc};
use zkc_arkworks::Keys;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};
use zkc_tools::proof::{NativeDeployment, SetupAuthority, hex};
fn inputs(
    envelope: &Json,
    keys: &[Keys],
    paths: &[std::path::PathBuf],
    producing: bool,
    second_point: u64,
) -> Json {
    let policy = Policy::default();
    let value = |port: usize| {
        let k = &keys[port / 6];
        let p = port % 6;
        if p == 2 {
            return hex(&k.verifier_key().to_bytes(&policy.ark_bounds()).unwrap());
        }
        let offset = port / 6 + 1;
        let point = if port / 6 == 0 { 7 } else { second_point };
        let table = Value::table(
            &(0..(1 << k.verifier_key().metadata().arity()))
                .map(|i| Scalar::from((offset + 3 * i) as u64))
                .collect::<Vec<_>>(),
            &policy,
        )
        .unwrap();
        let v = match p {
            0 => table,
            3 => {
                let Value::Table(t) = table else {
                    unreachable!()
                };
                Value::Commitment(Arc::new(
                    k.prover_key().commit(&t).unwrap().commitment().clone(),
                ))
            }
            4 => Value::Field(Scalar::from(point)),
            5 => Value::Field(Scalar::from(
                offset as u64 + 3 * point * ((1 << k.verifier_key().metadata().arity()) - 1),
            )),
            _ => panic!("port"),
        };
        let codec = NativeBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "test", "main", None), None),
            zkc_backends::SetupRegistry::new(
                vec![k.verifier_key().clone()],
                &zkc_backends::Policy::default(),
            )
            .unwrap(),
        )
        .unwrap();
        hex(&codec.encode_native_value(&v).unwrap())
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(p[1].as_str().unwrap().parse().unwrap())]))
        .collect();
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p[0] == if producing { "P" } else { "V" })
        .unwrap();
    let data: Vec<_> = role[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            let port: usize = p[0].as_str().unwrap().parse().unwrap();
            let spec = match port % 6 {
                1 => json!([
                    "prover_key_file",
                    [
                        paths[port / 6],
                        hex(&keys[port / 6].prover_key().material_fingerprint())
                    ]
                ]),
                2 => json!(["verifier_key", p[0]]),
                _ => json!(["wire", value(port)]),
            };
            json!([p[0], spec])
        })
        .collect();
    let transcript_budget = if envelope[2][1][5] == "" { "0" } else { "64" };
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        [],
        transcript_budget
    ])
}
fn run(d: &NativeDeployment, i: &Json, p: Option<&[u8]>) -> Result<Vec<u8>, String> {
    let r = d.execute(i, p)?;
    assert!(r.cleanup_errors.is_empty());
    r.outcome
}
fn main() {
    let dir = std::env::args().nth(1).unwrap();
    let dir = Path::new(&dir);
    let policy = Policy::default();
    let bounds = policy.ark_bounds();
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(dir.join("manifest.json")).unwrap()).unwrap();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let second_arity = if case["same_arity"].as_bool().unwrap_or(false) {
            1
        } else {
            2
        };
        let keys: Vec<_> = [1, second_arity, 1]
            .into_iter()
            .map(|n| Keys::setup_for_development(n, &bounds).unwrap())
            .collect();
        let paths: Vec<_> = (0..3)
            .map(|i| dir.join(format!("{name}.setup{i}.pk")))
            .collect();
        for (k, p) in keys.iter().zip(&paths) {
            std::fs::write(p, k.prover_key().to_bytes(&bounds).unwrap()).unwrap();
        }
        let authority = SetupAuthority {
            keys: BTreeMap::from([
                (2, keys[0].verifier_key().metadata().key_id()),
                (8, keys[1].verifier_key().metadata().key_id()),
            ]),
            inputs: BTreeMap::from([(1, 2), (3, 2), (7, 8), (9, 8)]),
        };
        let config = json!([
            "zkc.native-setup-authority/1",
            [
                ["2", hex(&authority.keys[&2])],
                ["8", hex(&authority.keys[&8])]
            ],
            [["1", "2"], ["3", "2"], ["7", "8"], ["9", "8"]]
        ]);
        std::fs::write(
            dir.join(format!("{name}.setups.json")),
            serde_json::to_vec(&config).unwrap(),
        )
        .unwrap();
        let bytes = std::fs::read(dir.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let pin: [u8; 32] = Sha256::digest(&bytes).into();
        assert!(NativeDeployment::admit(&bytes, &pin, Default::default()).is_err());
        assert!(
            NativeDeployment::admit(
                &bytes,
                &pin,
                SetupAuthority {
                    keys: BTreeMap::from([(2, authority.keys[&2])]),
                    inputs: authority.inputs.clone()
                }
            )
            .is_err()
        );
        for bad in [
            SetupAuthority::default(),
            SetupAuthority {
                keys: authority.keys.clone(),
                inputs: BTreeMap::new(),
            },
            SetupAuthority {
                keys: authority.keys.clone(),
                inputs: BTreeMap::from([(1, 2), (3, 2), (7, 99), (9, 8)]),
            },
        ] {
            assert_eq!(
                NativeDeployment::admit(&bytes, &pin, bad).unwrap_err(),
                "native-proof-key-authority"
            );
        }
        let d = NativeDeployment::admit(
            &bytes,
            &pin,
            SetupAuthority::parse(&serde_json::to_vec(&config).unwrap()).unwrap(),
        )
        .unwrap();
        let p = inputs(&envelope, &keys, &paths, true, 7);
        let v = inputs(&envelope, &keys, &paths, false, 7);
        let produced = d.execute(&p, None).unwrap();
        assert!(produced.cleanup_errors.is_empty());
        let proof = produced.outcome.unwrap();
        if case["early"] == true {
            // Only the first setup's two openings ran. The second setup still
            // participates in input authorization and the public binding root.
            assert_eq!(produced.messages, 4);
            let validated = d.execute(&v, Some(&proof)).unwrap();
            assert_eq!(
                validated.outcome,
                if case["refusal"].is_string() {
                    Err("artifact-rejected".into())
                } else {
                    Ok(Vec::new())
                }
            );
            assert_eq!(produced.return_at.as_ref().unwrap().1, "finish_P");
            assert_eq!(validated.return_at.as_ref().unwrap().1, "finish_V");
            let mut trailing = proof.clone();
            trailing.push(0);
            assert_eq!(run(&d, &v, Some(&trailing)).unwrap_err(), "proof-trailing");
            assert_eq!(validated.messages, 4);
            assert!(validated.cleanup_errors.is_empty());
            // A false finish condition keeps both transcript and setup paths
            // live. Recompute the second public evaluation at a distinct point.
            let continued_p = inputs(&envelope, &keys, &paths, true, 8);
            let continued_v = inputs(&envelope, &keys, &paths, false, 8);
            let continued = d.execute(&continued_p, None).unwrap();
            assert!(continued.return_at.is_none());
            assert_eq!(continued.messages, 8);
            assert!(continued.cleanup_errors.is_empty());
            let complete_proof = continued.outcome.unwrap();
            let checked = d.execute(&continued_v, Some(&complete_proof)).unwrap();
            assert_eq!(checked.outcome, Ok(Vec::new()));
            assert_eq!(checked.messages, 8);
            assert!(checked.return_at.is_none());
            assert!(checked.cleanup_errors.is_empty());
        }
        if let Some(refusal) = case["refusal"].as_str() {
            let error = run(&d, &v, Some(&proof)).unwrap_err();
            assert!(
                error.contains(refusal),
                "{name}: expected {refusal}, got {error}"
            );
        } else {
            run(&d, &v, Some(&proof)).unwrap();
        }
        for port in ["2", "8"] {
            let mut bad = v.clone();
            let row = bad[1]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|r| r[1] == port)
                .unwrap();
            row[2] = json!(hex(&keys[2].verifier_key().to_bytes(&bounds).unwrap()));
            assert!(run(&d, &bad, Some(&proof)).is_err());
        }
        for port in ["1", "7"] {
            let mut bad = p.clone();
            let row = bad[2]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|r| r[0] == port)
                .unwrap();
            let other = if port == "1" { 1 } else { 0 };
            row[1] = json!([
                "prover_key_file",
                [
                    paths[other],
                    hex(&keys[other].prover_key().material_fingerprint())
                ]
            ]);
            assert!(run(&d, &bad, None).is_err());
        }
        // A correctly authorized key remains wrong for another configured input.
        let mut swapped = authority.clone();
        swapped.inputs.insert(3, 8);
        let wrong = NativeDeployment::admit(&bytes, &pin, swapped).unwrap();
        assert_eq!(
            run(&wrong, &p, None).unwrap_err(),
            "native-proof-input-setup"
        );
        let mut badproof = proof.clone();
        *badproof.last_mut().unwrap() ^= 1;
        assert!(run(&d, &v, Some(&badproof)).is_err());
        std::fs::write(
            dir.join(format!("{name}.producer.json")),
            serde_json::to_vec(&p).unwrap(),
        )
        .unwrap();
        std::fs::write(
            dir.join(format!("{name}.validator.json")),
            serde_json::to_vec(&v).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join(format!("{name}.proof")), proof).unwrap();
    }
    println!("independent authorized setup composition and swap controls passed");
}
