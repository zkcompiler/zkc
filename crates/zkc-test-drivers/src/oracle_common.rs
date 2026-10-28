//! Differential execution of whole common ideal realization, including actual
//! role delivery, dynamic stores and source-selected queries.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_common", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn input(role: &str, values: Vec<Value>) -> RoleInput<CpuBackend> {
    RoleInput {
        role: role.to_owned(),
        backend: backend(role),
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
fn main() {
    let directory = std::env::args().nth(1).expect("common fixture directory");
    let bytes = std::fs::read(Path::new(&directory).join("common-recurrence.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P"),
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
        &backend("Alice"),
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
        &backend("P"),
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
    let bytes = std::fs::read(Path::new(&directory).join("common-shape.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("P"),
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
    println!("{cases} common ideal realization execution and delivery controls passed");
}
