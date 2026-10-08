//! General compositions, independent numerical checks and operational capacity.
mod reference;
use p3_field::PrimeCharacteristicRing;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{
    Bn254G1, Bn254G2, Bn254Scalar as F, Domain, EntryPolicy, KoalaBear as B, KoalaBearExt8 as E,
    NativeBackend, Policy, Sequence, Value,
};
use zkc_runtime::interactive::LogicalType;
use zkc_tools::proof::{NativeCapacity, NativeDeployment, hex};
fn codec() -> NativeBackend {
    NativeBackend::new(
        Policy {
            max_groups: 8192,
            ..Policy::default()
        },
        EntryPolicy::new(Domain::new("P", "composition", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn inputs(envelope: &Json, values: &[Value], producing: bool) -> Json {
    let codec = codec();
    let wire = |i: &Json| {
        hex(&codec
            .encode_native_value(&values[i.as_str().unwrap().parse::<usize>().unwrap()])
            .unwrap())
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(&p[1])]))
        .collect();
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == envelope[2][1][if producing { 2 } else { 3 }])
        .unwrap();
    let data: Vec<_> = role[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", wire(&p[0])]]))
        .collect();
    let services: Vec<_> = role[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "16"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        services,
        if envelope[2][1][5].as_str() == Some("") {
            "0"
        } else {
            "32"
        }
    ])
}
fn run(
    deployment: &NativeDeployment,
    inputs: &Json,
    proof: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let report = deployment.execute(inputs, proof)?;
    assert!(report.cleanup_errors.is_empty());
    if report.outcome.is_ok() {
        assert!(!report.cancelled);
    }
    report.outcome
}

fn qap(n: usize, change: &str) -> Vec<Value> {
    // Rectangular, distinct, non-symmetric A/B/C with two entries per row.
    // ONE is column zero. The extra witness columns make a transpose incorrect.
    // The non-unit ONE control keeps all rows true by dividing C's constant
    // coefficient by w[0]; only the explicit ONE predicate can reject it.
    let w: Vec<F> = (0..n + 2)
        .map(|i| {
            F::from(if i == 0 {
                if change == "one" { 2 } else { 1 }
            } else {
                (i % 17 + 1) as u64
            })
        })
        .collect();
    let matrices = (0..3)
        .map(|m| {
            let entries = (0..n)
                .flat_map(|i| {
                    let a = w[i + 1] + F::from(2) * w[i + 2];
                    let b = F::from(3) * w[0] + F::from(4) * w[i + 2];
                    let entries = match m {
                        0 => [(i + 1, F::from(1)), (i + 2, F::from(2))],
                        1 => [(0, F::from(3)), (i + 2, F::from(4))],
                        _ => [
                            (
                                0,
                                (a * b - w[1]) / w[0]
                                    + F::from(u64::from(change == "last_matrix" && i + 1 == n)),
                            ),
                            (1, F::from(1)),
                        ],
                    };
                    entries.map(|(col, value)| (i as u32, col as u32, value))
                })
                .collect::<Vec<_>>();
            Value::bn254_matrix(n, n + 2, &entries, &Policy::default()).unwrap()
        })
        .collect();
    let mut witness = w.clone();
    if change == "last_witness" {
        witness[n + 1] += F::from(1);
    }
    let count = n - usize::from(change == "query_length");
    vec![
        Value::Sequence(
            Sequence::new(
                LogicalType::parse("matrix:bn254.fr").unwrap(),
                matrices,
                &Policy::default(),
            )
            .unwrap(),
        ),
        Value::Bn254Vector(vec![w[1] + F::from(u64::from(change == "public"))].into()),
        Value::Bn254Vector(witness.into()),
        Value::Bn254G1Vector(
            (0..count)
                .map(|i| Bn254G1::generator().scale(F::from((i + 1) as u64)))
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Bn254G2(Bn254G2::generator()),
        Value::Bn254Field(F::from(match change {
            "zero_shift" => 0,
            "overlap" => 1,
            _ => 2,
        })),
        Value::Index((n + usize::from(change == "domain_size")) as u64),
    ]
}
fn air(n: usize, change: &str) -> Vec<Value> {
    let mut trace = (0..n)
        .map(|i| B::from_u64(3 + 2 * i as u64))
        .collect::<Vec<_>>();
    if change == "last_witness" {
        trace[n - 1] += B::ONE;
    }
    vec![
        Value::KoalaBearVector(trace.into()),
        Value::KoalaBearField(B::from_u64(if change == "start" { 4 } else { 3 })),
        Value::KoalaBearField(B::from_u64(2)),
        Value::KoalaBearExt8Field(E::from_u64(if change == "zero_shift" { 0 } else { 7 })),
        Value::Index((n + usize::from(change == "domain_size")) as u64),
        Value::Index(if change == "query" {
            n as u64
        } else {
            (n - 1) as u64
        }),
    ]
}
fn target(n: usize) -> Vec<Value> {
    vec![
        Value::Bn254G1(Bn254G1::generator()),
        Value::Bn254G2(Bn254G2::generator()),
        Value::Bn254Field(F::from(13)),
        Value::Index(n as u64),
    ]
}
fn admit(bytes: &[u8], groups: usize) -> NativeDeployment {
    NativeDeployment::admit(bytes, &hex(&Sha256::digest(bytes)), Default::default())
        .unwrap()
        .with_capacity(NativeCapacity {
            groups,
            ..NativeCapacity::default()
        })
        .unwrap()
}
fn packets(proof: &[u8]) -> Vec<(usize, &[u8])> {
    assert_eq!(&proof[..4], b"ZKCP");
    let mut at = 40;
    let mut frames = Vec::new();
    while at < proof.len() {
        let n = u64::from_le_bytes(proof[at..at + 8].try_into().unwrap()) as usize;
        frames.push((at, &proof[at + 8..at + 8 + n]));
        at += 8 + n;
    }
    assert_eq!(at, proof.len());
    frames
}
fn main() {
    reference::check_g2_ingress();
    let arg = std::env::args().nth(1).expect("generated directory");
    let dir = Path::new(&arg);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(dir.join("manifest.json")).unwrap()).unwrap();
    let mut measurements = Vec::new();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let bytes = std::fs::read(dir.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let sizes: &[usize] = match family {
            "qap-composition" => &[8, 64, 256, 1024, 4096, 8192],
            "air-composition" => &[16, 256, 4096, 8192],
            _ => &[0, 1, 7, 16],
        };
        for &n in sizes {
            // Every lowering mode reaches the largest required shape. Intermediate
            // probes use the default mode to avoid redundant expensive MSM executions.
            if name != family && n != sizes[0] && n != *sizes.last().unwrap() {
                continue;
            }
            let values = match family {
                "qap-composition" => qap(n, ""),
                "air-composition" => air(n, ""),
                _ => target(n),
            };
            let producer = inputs(&envelope, &values, true);
            let validator = inputs(&envelope, &values, false);
            let d = admit(&bytes, 8192);
            let start = std::time::Instant::now();
            let proof =
                run(&d, &producer, None).unwrap_or_else(|e| panic!("{name}/{n} produce: {e}"));
            run(&d, &validator, Some(&proof))
                .unwrap_or_else(|e| panic!("{name}/{n} validate: {e}"));
            reference::check(family, n, &values, &envelope, &producer, &proof);
            if family == "air-composition" && name == family && n == sizes[0] {
                let mut found = false;
                // Deterministic application contexts exercise a rejected candidate
                // in the actual native transcript, not just the sampler unit test.
                for context in 0u8..=255 {
                    let mut input = producer.clone();
                    input[3] = json!(format!("{context:02x}"));
                    let proof = run(&d, &input, None).unwrap();
                    let rejected = reference::check(family, n, &values, &envelope, &input, &proof);
                    if rejected > 0 {
                        let mut validation = validator.clone();
                        validation[3] = input[3].clone();
                        run(&d, &validation, Some(&proof)).unwrap();
                        println!(
                            "extension rejection context {context:02x}: {rejected} rejected words"
                        );
                        found = true;
                        break;
                    }
                }
                assert!(found, "context corpus did not exercise rejection sampling");
            }
            measurements.push(json!({"client":name,"size":n,"deployment_bytes":bytes.len(),"program_bytes":envelope[4].as_str().unwrap().len(),"proof_bytes":proof.len(),"elapsed_ms":start.elapsed().as_millis()}));
            println!(
                "{name}/{n}: accepted, independently checked ({} bytes)",
                proof.len()
            );
            if n == sizes[0] && name == family && family != "target-accumulation" {
                let boundaries = capacity_boundaries(&bytes, &producer, &validator, &proof);
                measurements.last_mut().unwrap()["capacity_boundaries"] = json!(boundaries);
            }
            if n == sizes[0] {
                // Sufficient operational ceilings cannot alter the semantic binding or proof.
                let default = admit(&bytes, 4096);
                assert_eq!(run(&default, &producer, None).unwrap(), proof);
                for (offset, frame) in packets(&proof) {
                    let mut wrong = proof.clone();
                    wrong[offset + 8 + frame.len() - 1] ^= 1;
                    assert!(
                        run(&d, &validator, Some(&wrong)).is_err(),
                        "{name}: accepted modified frame"
                    );
                }
                // Replace a terminal message with a different valid value. This
                // reaches the predicate, rather than failing point decoding.
                let replacements = match family {
                    "qap-composition" => vec![
                        (1, Value::Bn254G1(Bn254G1::generator())),
                        (2, Value::Bn254Gt(zkc_backends::Bn254Gt::generator())),
                    ],
                    "air-composition" => {
                        vec![(3, Value::KoalaBearExt8Vector(vec![E::ZERO].into()))]
                    }
                    _ => vec![(0, Value::Bn254Gt(zkc_backends::Bn254Gt::generator()))],
                };
                for (index, replacement) in replacements {
                    let encoded = codec().encode_native_value(&replacement).unwrap();
                    let (offset, previous) = packets(&proof)[index];
                    assert_eq!(encoded.len(), previous.len());
                    assert_ne!(encoded, previous);
                    let mut wrong = proof.clone();
                    wrong[offset + 8..offset + 8 + encoded.len()].copy_from_slice(&encoded);
                    assert_eq!(
                        run(&d, &validator, Some(&wrong)).unwrap_err(),
                        "artifact-rejected"
                    );
                }
                let mut trailing = proof.clone();
                trailing.push(0);
                assert!(run(&d, &validator, Some(&trailing)).is_err());
                assert!(run(&d, &validator, Some(&proof[..proof.len() - 1])).is_err());
                for change in match family {
                    "qap-composition" => vec!["last_witness", "last_matrix", "public", "one"],
                    "air-composition" => vec!["last_witness", "start"],
                    _ => vec![],
                } {
                    let changed = if family == "qap-composition" {
                        qap(n, change)
                    } else {
                        air(n, change)
                    };
                    if change == "one" {
                        reference::check_one_control(&changed);
                    }
                    let p = inputs(&envelope, &changed, true);
                    let v = inputs(&envelope, &changed, false);
                    let wrong = run(&d, &p, None).unwrap();
                    let error = run(&d, &v, Some(&wrong)).unwrap_err();
                    assert_eq!(error, "artifact-rejected", "{name}/{change}: {error}");
                }
                for change in match family {
                    "qap-composition" => {
                        vec!["zero_shift", "overlap", "domain_size", "query_length"]
                    }
                    "air-composition" => vec!["zero_shift", "domain_size", "query"],
                    _ => vec![],
                } {
                    let changed = if family == "qap-composition" {
                        qap(n, change)
                    } else {
                        air(n, change)
                    };
                    let error = run(&d, &inputs(&envelope, &changed, true), None).unwrap_err();
                    let expected = match change {
                        "zero_shift" => "refused:coset-zero-shift",
                        "query_length" => "refused:length-mismatch",
                        "query" => "refused:oracle-coordinate",
                        _ => "artifact-stopped:Explicit(\"reject\")",
                    };
                    assert_eq!(error, expected, "{name}/{change}");
                }
                for kind in [
                    "work", "live", "total", "wire", "value", "elements", "groups",
                ] {
                    let mut capacity = NativeCapacity {
                        groups: 8192,
                        ..NativeCapacity::default()
                    };
                    match kind {
                        "work" => capacity.work.instructions = 0,
                        "live" => capacity.values.live_bytes = 0,
                        "total" => capacity.values.total_bytes = 0,
                        "wire" => capacity.wire_bytes = 0,
                        "value" => capacity.value_bytes = 0,
                        "elements" => capacity.elements = 0,
                        _ => capacity.groups = 0,
                    }
                    if (kind == "groups" && family != "qap-composition")
                        || (kind == "elements" && family == "target-accumulation")
                    {
                        continue;
                    }
                    let limited = NativeDeployment::admit(
                        &bytes,
                        &hex(&Sha256::digest(&bytes)),
                        Default::default(),
                    )
                    .unwrap()
                    .with_capacity(capacity)
                    .unwrap();
                    let error = run(&limited, &producer, None)
                        .err()
                        .unwrap_or_else(|| panic!("{name}: capacity {kind} did not stop"));
                    let expected = match kind {
                        "work" => "artifact-stopped:Limit",
                        "live" => "artifact-input-bytes-limit",
                        // Loading work shares the cumulative byte ceiling; wire
                        // scanning is charged before reserving decoded values.
                        "total" => "artifact-input-work-limit",
                        "wire" => "native-capacity-wire",
                        _ => "native-wire-limit",
                    };
                    assert_eq!(error, expected, "{name}/{kind}");
                    assert_eq!(
                        run(&limited, &validator, Some(&proof)).unwrap_err(),
                        expected,
                        "{name}/{kind} validator"
                    );
                }
                for (suffix, value) in
                    [("producer.json", &producer), ("validator.json", &validator)]
                {
                    std::fs::write(
                        dir.join(format!("{name}.{suffix}")),
                        serde_json::to_vec(value).unwrap(),
                    )
                    .unwrap();
                }
                std::fs::write(dir.join(format!("{name}.proof")), &proof).unwrap();
            }
            if family == "target-accumulation" && n == 1 {
                let mut changed = target(n);
                changed[2] = Value::Bn254Field(F::from(14));
                let other_producer = inputs(&envelope, &changed, true);
                let other_validator = inputs(&envelope, &changed, false);
                let mut other_proof = run(&d, &other_producer, None).unwrap();
                run(&d, &other_validator, Some(&other_proof)).unwrap();
                assert_ne!(packets(&other_proof)[0].1, packets(&proof)[0].1);
                // Rebind only the unauthenticated header to the original public
                // inputs: the actual equation must still reject the changed x.
                other_proof[..40].copy_from_slice(&proof[..40]);
                assert_eq!(
                    run(&d, &validator, Some(&other_proof)).unwrap_err(),
                    "artifact-rejected"
                );
            }
            if family == "target-accumulation" && n == 16 {
                let limited = NativeDeployment::admit(
                    &bytes,
                    &hex(&Sha256::digest(&bytes)),
                    Default::default(),
                )
                .unwrap()
                .with_capacity(NativeCapacity {
                    work: zkc_runtime::interactive::WorkBudget {
                        iterations: 0,
                        ..Default::default()
                    },
                    ..Default::default()
                })
                .unwrap();
                assert_eq!(
                    run(&limited, &producer, None).unwrap_err(),
                    "artifact-stopped:Limit"
                );
            }
            if family == "qap-composition" && n == 8192 {
                assert_eq!(
                    run(&admit(&bytes, 4096), &producer, None).unwrap_err(),
                    "native-wire-limit"
                );
            }
        }
    }
    std::fs::write(
        dir.join("composition-measurements.json"),
        serde_json::to_vec_pretty(&measurements).unwrap(),
    )
    .unwrap();
}

// Fixed deterministic clients only: this is not a monotonicity claim for
// arbitrary providers or schedules. Every successful probe must preserve bytes.
fn capacity_boundaries(bytes: &[u8], producer: &Json, validator: &Json, proof: &[u8]) -> Vec<Json> {
    let mut boundaries = Vec::new();
    let digest = hex(&Sha256::digest(bytes));
    for kind in [
        "instructions",
        "iterations",
        "live",
        "total",
        "wire",
        "value",
        "elements",
        "groups",
    ] {
        let set = |n: usize| {
            let mut c = NativeCapacity::default();
            match kind {
                "instructions" => c.work.instructions = n as u64,
                "iterations" => c.work.iterations = n as u64,
                "live" => c.values.live_bytes = n,
                "total" => c.values.total_bytes = n,
                "wire" => c.wire_bytes = n,
                "value" => c.value_bytes = n,
                "elements" => c.elements = n,
                "groups" => c.groups = n,
                _ => unreachable!(),
            }
            c
        };
        let c = NativeCapacity::default();
        let ceiling = match kind {
            "instructions" => c.work.instructions as usize,
            "iterations" => c.work.iterations as usize,
            "live" => c.values.live_bytes,
            "total" => c.values.total_bytes,
            "wire" => c.wire_bytes,
            "value" => c.value_bytes,
            "elements" => c.elements,
            "groups" => c.groups,
            _ => unreachable!(),
        };
        for (input, incoming) in [(producer, None), (validator, Some(proof))] {
            let probe = |n| {
                let d = NativeDeployment::admit(bytes, &digest, Default::default())
                    .unwrap()
                    .with_capacity(set(n))
                    .unwrap();
                match d.execute(input, incoming) {
                    Err(error) => Err(format!("admission:{error}")),
                    Ok(report) => {
                        assert!(report.cleanup_errors.is_empty());
                        report
                            .outcome
                            .map(|out| {
                                assert_eq!(
                                    out.as_slice(),
                                    if incoming.is_some() { &[] } else { proof }
                                );
                            })
                            .map_err(|e| format!("execution:{e}"))
                    }
                }
            };
            probe(ceiling).unwrap();
            let (mut low, mut high) = (0, ceiling);
            while low < high {
                let middle = low + (high - low) / 2;
                if probe(middle).is_ok() {
                    high = middle;
                } else {
                    low = middle + 1;
                }
            }
            probe(low).unwrap();
            let below = if low > 0 {
                let error = probe(low - 1).unwrap_err();
                let expected: &[&str] = match kind {
                    "instructions" | "iterations" => &["execution:artifact-stopped:Limit"],
                    "live" | "total" => &[
                        "admission:artifact-input-bytes-limit",
                        "execution:artifact-stopped:Limit",
                        "execution:exhausted:output-bytes",
                    ],
                    "wire" => &[
                        "admission:native-capacity-wire",
                        "execution:native-capacity-wire",
                        "execution:exhausted:wire-bytes",
                    ],
                    "value" => &[
                        "admission:native-wire-limit",
                        "execution:native-wire-limit",
                        "execution:exhausted:output-bytes",
                    ],
                    "elements" => &[
                        "admission:native-wire-limit",
                        "execution:native-wire-limit",
                        "execution:exhausted:element-limit",
                        "execution:refused:coset-element-limit",
                        "execution:exhausted:oracle-element-limit",
                    ],
                    "groups" => &[
                        "admission:native-wire-limit",
                        "execution:native-wire-limit",
                        "execution:exhausted:group-limit",
                    ],
                    _ => unreachable!(),
                };
                assert!(expected.contains(&error.as_str()), "{kind}: {error}");
                assert_eq!(probe(low - 1).unwrap_err(), error);
                Some(error)
            } else {
                None
            };
            boundaries.push(json!({"dimension":kind,"role":if incoming.is_some(){"validator"}else{"producer"},"boundary":low,"below":below}));
            if low < ceiling {
                probe(low + 1).unwrap();
            }
            println!(
                "capacity {kind} {} boundary {low}",
                if incoming.is_some() {
                    "validator"
                } else {
                    "producer"
                }
            );
        }
    }
    boundaries
}
