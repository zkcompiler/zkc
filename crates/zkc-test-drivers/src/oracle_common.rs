//! Differential execution of whole common ideal realization, including actual
//! role delivery, dynamic stores and source-selected queries.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend(role: &str, entry: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_common", entry, None), None),
        Default::default(),
    )
    .unwrap()
}
fn input(role: &str, values: Vec<Value>) -> RoleInput<CpuBackend> {
    RoleInput {
        role: role.to_owned(),
        backend: backend(role, "main"),
        values,
    }
}
fn table(base: u64, length: u64) -> Value {
    Value::Indices((base..base + length).collect::<Vec<_>>().into())
}
#[derive(Default)]
struct Deliveries(Vec<String>);
impl Hooks<CpuBackend> for Deliveries {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        assert!(exchange.site.ends_with("_deliver"));
        self.0.push(exchange.site.to_owned());
        Ok(None)
    }
}
fn verify(report: &Report<CpuBackend>, expected: Option<u64>, label: &str) {
    match expected {
        Some(answer) => {
            assert!(
                matches!(report.outcome, Outcome::Completed),
                "{label}: {:?}",
                report.outcome
            );
            let receiver = report.roles.iter().find(|r| r.role == "V").unwrap();
            assert_eq!(receiver.outputs.len(), 1, "{label}");
            assert!(
                matches!(&receiver.outputs[0],Value::Index(x) if *x==answer),
                "{label}"
            );
        }
        None => {
            assert!(
                matches!(report.outcome, Outcome::ParticipantStopped { .. }),
                "{label}: {:?}",
                report.outcome
            );
            assert!(
                !format!("{:?}", report.outcome).contains("exhausted"),
                "{label}"
            );
        }
    }
    for (_, native) in &report.backends {
        assert_eq!(native.active_frames(), 0, "{label}");
    }
}
fn index(value: &Value) -> u64 {
    let Value::Index(value) = value else {
        panic!("expected index")
    };
    *value
}
fn record(value: &Value) -> &[Value] {
    let Value::Variant(value) = value else {
        panic!("expected record")
    };
    assert_eq!(value.alternative(), 0);
    value.payload()
}
fn reference(value: &Value) -> (usize, usize) {
    let fields = record(value);
    assert_eq!(fields.len(), 2);
    (index(&fields[0]) as usize, index(&fields[1]) as usize)
}
fn store(value: &Value) -> &zkc_cpu::Sequence {
    let Value::Sequence(value) = value else {
        panic!("expected store")
    };
    value
}
// Independent decoding of this source fixture's returned graph. It does not
// use generated controller code or a producer-supplied interpretation map.
fn returned_row(stores: &[Value], anchor: &Value, position: u64, remaining: usize) -> u64 {
    assert!(remaining > 0, "cyclic or overlong returned graph");
    let (constructor, instance) = reference(anchor);
    let fields = record(
        store(&stores[constructor])
            .get(instance)
            .expect("unbound returned anchor"),
    );
    if constructor < 2 {
        assert_eq!(fields.len(), 3);
        assert_eq!(index(&fields[0]), 4);
        assert_eq!(index(&fields[1]), 1);
        let Value::Indices(data) = &fields[2] else {
            panic!("base data")
        };
        data[position as usize]
    } else {
        assert_eq!(constructor, 2);
        assert_eq!(fields.len(), 4);
        assert_eq!(index(&fields[0]), instance as u64);
        assert_eq!(index(&fields[1]), 4);
        assert_eq!(index(&fields[2]), 1);
        let expected = if instance == 0 {
            (0, 0)
        } else {
            (2, instance - 1)
        };
        assert_eq!(reference(&fields[3]), expected);
        returned_row(stores, &fields[3], position, remaining - 1)
    }
}
fn main() {
    let directory = std::env::args().nth(1).expect("common fixture directory");
    let bytes = std::fs::read(Path::new(&directory).join("common-recurrence.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P", "main"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    let mut cases = 0;
    for lengths in [[4, 4], [0, 4], [4, 3]] {
        for trips in 0..=3 {
            for mapped in [0, 3, 4] {
                for position in [0, 2, 4] {
                    let mut deliveries = Deliveries::default();
                    let report = run(
                        &bundle,
                        "oracle_common",
                        vec![
                            input(
                                "P",
                                vec![
                                    table(10, lengths[0]),
                                    table(20, lengths[1]),
                                    Value::Index(mapped),
                                    Value::Index(trips),
                                ],
                            ),
                            input(
                                "V",
                                vec![
                                    Value::Index(mapped),
                                    Value::Index(position),
                                    Value::Index(trips),
                                ],
                            ),
                        ],
                        RunLimits::default(),
                        &mut deliveries,
                    )
                    .unwrap();
                    // Shape checks occur at both sends. Unused child queries in
                    // a reached virtual construction still check their domains.
                    let valid = lengths == [4, 4] && position < 4 && (trips == 0 || mapped < 4);
                    let label = format!("recurrence/{lengths:?}/{trips}/{mapped}/{position}");
                    verify(&report, valid.then_some(10 + position), &label);
                    assert_eq!(
                        deliveries.0.len(),
                        if lengths[0] != 4 {
                            0
                        } else if lengths[1] != 4 {
                            1
                        } else {
                            2
                        },
                        "{label}"
                    );
                    cases += 1;
                }
            }
        }
    }
    let bytes = std::fs::read(Path::new(&directory).join("common-holders.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("Alice", "main"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for which in 0..=2 {
        for position in 0..=4 {
            let mut deliveries = Deliveries::default();
            let report = run(
                &bundle,
                "oracle_common",
                vec![
                    input("Alice", vec![table(10, 4)]),
                    input("Bob", vec![table(20, 4)]),
                    input("V", vec![Value::Index(which), Value::Index(position)]),
                ],
                RunLimits::default(),
                &mut deliveries,
            )
            .unwrap();
            verify(
                &report,
                (which < 2 && position < 4).then_some(10 * (which + 1) + position),
                &format!("holders/{which}/{position}"),
            );
            assert_eq!(deliveries.0.len(), 2);
            cases += 1;
        }
    }

    let bytes = std::fs::read(Path::new(&directory).join("common-input.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P", "main"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for lengths in [[4, 4], [3, 4], [4, 3]] {
        for position in 0..=4 {
            let report = run(
                &bundle,
                "oracle_common",
                vec![
                    input("P", vec![table(10, lengths[0])]),
                    input("V", vec![table(40, lengths[1]), Value::Index(position)]),
                ],
                RunLimits::default(),
                &mut NoHooks,
            )
            .unwrap();
            // Different role components are not silently equated. The generated
            // honest-input relation remains a separate source obligation.
            verify(
                &report,
                (lengths == [4, 4] && position < 4).then_some(40 + position),
                &format!("input/{lengths:?}/{position}"),
            );
            cases += 1;
        }
    }
    let bytes = std::fs::read(Path::new(&directory).join("common-clauses.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P", "main"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for lengths in [[4, 4], [3, 4], [4, 3]] {
        for receiver_base in [0, 40] {
            for position in 0..=4 {
                let report = run(
                    &bundle,
                    "oracle_common",
                    vec![
                        input("P", vec![table(10, lengths[0])]),
                        input(
                            "V",
                            vec![table(receiver_base, lengths[1]), Value::Index(position)],
                        ),
                    ],
                    RunLimits::default(),
                    &mut NoHooks,
                )
                .unwrap();
                let label = format!("clauses/{lengths:?}/{receiver_base}/{position}");
                if lengths == [4, 4] && position < 4 {
                    assert!(matches!(report.outcome, Outcome::Completed), "{label}");
                    let holder = &report.roles.iter().find(|r| r.role == "P").unwrap().outputs;
                    let receiver = &report.roles.iter().find(|r| r.role == "V").unwrap().outputs;
                    assert_eq!(holder.len(), 1, "{label}");
                    assert!(
                        matches!(&holder[0], Value::Indices(xs) if xs.as_ref() == [10,11,12,13]),
                        "{label}"
                    );
                    assert_eq!(index(&receiver[1]), receiver_base + position, "{label}");
                    // The decision is an actual output, not execution of the
                    // external logical predicate or an inferred honesty guard.
                    assert!(
                        matches!(&receiver[2], Value::Bool(accepted) if *accepted == (receiver_base == 0)),
                        "{label}"
                    );
                    assert_eq!(
                        returned_row(&receiver[3..], &receiver[0], position, 64),
                        receiver_base + position,
                        "{label}"
                    );
                    for (_, native) in &report.backends {
                        assert_eq!(native.active_frames(), 0, "{label}");
                    }
                } else {
                    verify(&report, None, &label);
                }
                cases += 1;
            }
        }
    }
    let bytes = std::fs::read(Path::new(&directory).join("common-shape.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P", "main"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for length in [0, 4, 8, 9] {
        for shape in [0, 4, 8, 9] {
            for position in [0, 3, 8] {
                let mut deliveries = Deliveries::default();
                let report = run(
                    &bundle,
                    "oracle_common",
                    vec![
                        input("P", vec![table(10, length), Value::Index(shape)]),
                        input("V", vec![Value::Index(shape), Value::Index(position)]),
                    ],
                    RunLimits::default(),
                    &mut deliveries,
                )
                .unwrap();
                let valid = length == shape && shape <= 8 && position < shape;
                verify(
                    &report,
                    valid.then_some(10 + position),
                    &format!("shape/{length}/{shape}/{position}"),
                );
                assert_eq!(
                    deliveries.0.len(),
                    usize::from(length == shape && shape <= 8)
                );
                cases += 1;
            }
        }
    }
    for fixture in ["common-contents", "common-views"] {
        let bytes = std::fs::read(Path::new(&directory).join(format!("{fixture}.bundle"))).unwrap();
        let bundle = Bundle::admit(
            &bytes,
            &backend("P", "main"),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for trips in 0..=3 {
            for extent in [0, 2, 4, 5] {
                for mapped in [0, 3, 4] {
                    for position in [0, 4] {
                        let mut deliveries = Deliveries::default();
                        let report = run(
                            &bundle,
                            "oracle_common",
                            vec![
                                input(
                                    "P",
                                    vec![
                                        table(10, 4),
                                        table(20, 4),
                                        Value::Index(mapped),
                                        Value::Index(extent),
                                        Value::Index(trips),
                                    ],
                                ),
                                input("Q", vec![table(30, 4)]),
                                input(
                                    "V",
                                    vec![
                                        Value::Index(mapped),
                                        Value::Index(extent),
                                        Value::Index(position),
                                        Value::Index(trips),
                                    ],
                                ),
                            ],
                            RunLimits::default(),
                            &mut deliveries,
                        )
                        .unwrap();
                        let label = format!("{fixture}/{trips}/{extent}/{mapped}/{position}");
                        // Zero trips select the original base. Empty virtual tables
                        // evaluate no child queries, including an invalid unused map.
                        let rows = if trips == 0 { 4 } else { extent };
                        let valid = position < 4
                            && (trips == 0 || (extent <= 4 && (extent == 0 || mapped < 4)));
                        if valid {
                            assert!(
                                matches!(report.outcome, Outcome::Completed),
                                "{label}: {:?}",
                                report.outcome
                            );
                            let holder = report.roles.iter().find(|r| r.role == "P").unwrap();
                            let receiver = report.roles.iter().find(|r| r.role == "V").unwrap();
                            assert_eq!(holder.outputs.len(), 2, "{label}");
                            assert_eq!(receiver.outputs.len(), 2, "{label}");
                            let expected = (10..10 + rows).collect::<Vec<_>>();
                            assert!(
                                matches!(&holder.outputs[0], Value::Indices(values) if values.as_ref() == expected),
                                "{label}"
                            );
                            assert!(
                                matches!(holder.outputs[1], Value::Index(x) if x == rows),
                                "{label}"
                            );
                            assert!(
                                matches!(receiver.outputs[0], Value::Index(x) if x == 10 + position),
                                "{label}"
                            );
                            assert!(
                                matches!(receiver.outputs[1], Value::Index(x) if x == rows),
                                "{label}"
                            );
                        } else {
                            verify(&report, None, &label);
                        }
                        assert_eq!(deliveries.0.len(), 3, "{label}");
                        for (_, backend) in &report.backends {
                            assert_eq!(backend.active_frames(), 0, "{label}");
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    for (entry, suffix, base) in [
        ("main", "", 10),
        ("companion", "-companion", 40),
        ("ordinary", "-ordinary", 70),
    ] {
        let bytes =
            std::fs::read(Path::new(&directory).join(format!("common-entries{suffix}.bundle")))
                .unwrap();
        let bundle = Bundle::admit(
            &bytes,
            &backend("P", entry),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for length in [0, 3, 4] {
            for position in [0, 3, 4] {
                let mut deliveries = Deliveries::default();
                let role_input = |role: &str, values| RoleInput {
                    role: role.to_owned(),
                    backend: backend(role, entry),
                    values,
                };
                let inputs = if entry == "ordinary" {
                    vec![
                        role_input("P", vec![]),
                        role_input("V", vec![Value::Index(base), Value::Index(position)]),
                    ]
                } else {
                    vec![
                        role_input("P", vec![table(base, length)]),
                        role_input("V", vec![Value::Index(position)]),
                    ]
                };
                let report = run(
                    &bundle,
                    "oracle_common",
                    inputs,
                    RunLimits::default(),
                    &mut deliveries,
                )
                .unwrap();
                let expected = if entry == "ordinary" {
                    Some(base)
                } else {
                    (length == 4 && position < 4).then_some(base + position)
                };
                verify(
                    &report,
                    expected,
                    &format!("entries/{entry}/{length}/{position}"),
                );
                assert_eq!(
                    deliveries.0.len(),
                    usize::from(entry != "ordinary" && length == 4)
                );
                cases += 1;
            }
        }
    }
    for (entry, suffix) in [("main", ""), ("wrapper", "-wrapper")] {
        let bytes =
            std::fs::read(Path::new(&directory).join(format!("common-return{suffix}.bundle")))
                .unwrap();
        let bundle = Bundle::admit(
            &bytes,
            &backend("P", entry),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        let parameters = if entry == "main" {
            (0..=3).map(|trips| (trips, 4, 4)).collect::<Vec<_>>()
        } else {
            vec![(0, 4, 4), (0, 3, 4), (0, 4, 3)]
        };
        for (trips, holder_length, receiver_length) in parameters {
            for position in [0, 3, 4] {
                let role_input = |role: &str, values| RoleInput {
                    role: role.to_owned(),
                    backend: backend(role, entry),
                    values,
                };
                let inputs = if entry == "main" {
                    vec![
                        role_input("P", vec![table(10, 4), Value::Index(trips)]),
                        role_input("V", vec![Value::Index(trips), Value::Index(position)]),
                    ]
                } else {
                    vec![
                        role_input("P", vec![table(10, holder_length)]),
                        role_input(
                            "V",
                            vec![table(40, receiver_length), Value::Index(position)],
                        ),
                    ]
                };
                let mut deliveries = Deliveries::default();
                let report = run(
                    &bundle,
                    "oracle_common",
                    inputs,
                    RunLimits::default(),
                    &mut deliveries,
                )
                .unwrap();
                let label =
                    format!("returns/{entry}/{trips}/{holder_length}/{receiver_length}/{position}");
                if position < 4 && holder_length == 4 && receiver_length == 4 {
                    assert!(
                        matches!(report.outcome, Outcome::Completed),
                        "{label}: {:?}",
                        report.outcome
                    );
                    let holder = &report.roles.iter().find(|r| r.role == "P").unwrap().outputs;
                    let receiver = &report.roles.iter().find(|r| r.role == "V").unwrap().outputs;
                    assert_eq!(holder.len(), if entry == "main" { 3 } else { 1 }, "{label}");
                    for data in holder {
                        assert!(
                            matches!(data, Value::Indices(xs) if xs.as_ref() == [10, 11, 12, 13]),
                            "{label}"
                        );
                    }
                    if entry == "main" {
                        assert_eq!(receiver.len(), 7, "{label}");
                        let expected = if trips == 0 {
                            (0, 0)
                        } else {
                            (2, trips as usize - 1)
                        };
                        assert_eq!(reference(&receiver[0]), expected, "{label}");
                        assert_eq!(reference(&receiver[1]), expected, "{label}");
                        assert_eq!(reference(&receiver[2]), (1, 0), "{label}");
                        assert_eq!(index(&receiver[3]), 10 + position, "{label}");
                        assert_eq!(store(&receiver[4]).len(), 1, "{label}");
                        assert_eq!(store(&receiver[5]).len(), 1, "{label}");
                        assert_eq!(store(&receiver[6]).len(), trips as usize, "{label}");
                        for anchor in &receiver[..3] {
                            for row in 0..4 {
                                assert_eq!(
                                    returned_row(&receiver[4..], anchor, row, 8),
                                    10 + row,
                                    "{label}"
                                );
                            }
                        }
                    } else {
                        assert_eq!(receiver.len(), 3, "{label}");
                        assert_eq!(reference(&receiver[0]), (0, 0), "{label}");
                        assert_eq!(index(&receiver[1]), 40 + position, "{label}");
                        for row in 0..4 {
                            assert_eq!(
                                returned_row(&receiver[2..], &receiver[0], row, 8),
                                40 + row,
                                "{label}"
                            );
                        }
                    }
                } else {
                    verify(&report, None, &label);
                }
                assert_eq!(
                    deliveries.0.len(),
                    if entry == "main" { 2 } else { 0 },
                    "{label}"
                );
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0, "{label}");
                }
                cases += 1;
            }
        }
    }
    for suffix in ["", "-at"] {
        let entry = if suffix.is_empty() { "main" } else { "at" };
        let role_input = |role: &str, values| RoleInput {
            role: role.to_owned(),
            backend: backend(role, entry),
            values,
        };
        let bytes =
            std::fs::read(Path::new(&directory).join(format!("common-empty{suffix}.bundle")))
                .unwrap();
        let bundle = Bundle::admit(
            &bytes,
            &backend("P", entry),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for marker in [0, 1, 99] {
            for position in [0, 2, u64::MAX] {
                let mut deliveries = Deliveries::default();
                let values = if suffix.is_empty() {
                    vec![
                        role_input("P", vec![Value::Index(marker)]),
                        role_input("V", vec![Value::Index(marker)]),
                    ]
                } else {
                    vec![
                        role_input("P", vec![Value::Index(marker)]),
                        role_input("V", vec![Value::Index(position)]),
                    ]
                };
                let report = run(
                    &bundle,
                    "oracle_common",
                    values,
                    RunLimits::default(),
                    &mut deliveries,
                )
                .unwrap();
                verify(&report, suffix.is_empty().then_some(0), "empty sequence");
                assert_eq!(deliveries.0.len(), usize::from(!suffix.is_empty()));
                cases += 1;
            }
        }
    }
    println!("{cases} common ideal realization execution and delivery controls passed");
}
