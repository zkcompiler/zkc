//! Common oracle roots use the selected scheme and preserve receiver shape custody.
use std::path::Path;
use zkc_cpu::merkle::Scheme;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, KoalaBear, KoalaBearExt4, Policy, Value};
use zkc_kernels::plonky3::{
    merkle::{commit, poseidon2::Quartic},
    oracle::Shape,
};
use zkc_runtime::host::joint::*;

fn backend(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_roots", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn scalar(n: u64) -> KoalaBearExt4 {
    KoalaBearExt4::from([n as u32 + 11, 3, n as u32 + 17, 7].map(KoalaBear::new))
}
#[derive(Default)]
struct Messages {
    values: Vec<Vec<u8>>,
}
impl Hooks<CpuBackend> for Messages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        assert_eq!((exchange.sender, exchange.receiver), ("P", "V"));
        self.values.push(bytes.to_vec());
        Ok(None)
    }
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("common root fixtures directory");
    let directory = Path::new(&directory);
    let mut cases = 0;
    for input in [false, true] {
        for fixed in [false, true] {
            let name = format!(
                "root-{}-{}",
                if input { "input" } else { "send" },
                if fixed { "fixed" } else { "dynamic" }
            );
            let bundle = Bundle::admit(
                &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
                &backend("V"),
                zkc_cpu::cpu_contracts(),
                BundleLimits::default(),
            )
            .unwrap();
            let mut trial = |length: u64, holder_rows: u64, receiver_rows: u64, complete: bool| {
                let mut holder = vec![Value::KoalaBearExt4Vector(
                    (0..length).map(scalar).collect::<Vec<_>>().into(),
                )];
                let mut receiver = vec![];
                if input {
                    // Canonical but unrelated root: construction must not infer
                    // its height or impose equality with the holder's Data.
                    receiver.push(Value::MerkleDigest(
                        Scheme::Poseidon2KoalaBearExt4,
                        vec![0; 32].into(),
                    ));
                    if !fixed {
                        receiver.push(Value::Index(receiver_rows));
                    }
                } else {
                    holder.push(Value::Index(holder_rows));
                    receiver.push(Value::Index(receiver_rows));
                }
                let mut messages = Messages::default();
                let report = run(
                    &bundle,
                    "oracle_roots",
                    vec![
                        RoleInput {
                            role: "P".into(),
                            backend: backend("P"),
                            values: holder,
                        },
                        RoleInput {
                            role: "V".into(),
                            backend: backend("V"),
                            values: receiver,
                        },
                    ],
                    RunLimits::default(),
                    &mut messages,
                )
                .unwrap();
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name}/{length}/{holder_rows}/{receiver_rows}: {:?}",
                    report.outcome
                );
                let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
                if complete {
                    assert_eq!(verifier.outputs.len(), 1);
                    let expected_rows = if fixed { 8 } else { receiver_rows };
                    assert!(
                        matches!(verifier.outputs[0], Value::Index(rows) if rows == expected_rows)
                    );
                    assert_eq!(messages.values.len(), usize::from(!input));
                    if !input {
                        // Independently arrange antipodal pairs, then use the
                        // kernel API to check the compiler-generated delivery.
                        let arranged = (0..length / 2)
                            .flat_map(|i| [scalar(i), scalar(i + length / 2)])
                            .collect();
                        let (root, _) = commit::<Quartic>(
                            arranged,
                            Shape::new(2, length as usize / 2, 64).unwrap(),
                            1 << 20,
                        )
                        .unwrap();
                        let expected = backend("V")
                            .encode_native_value(&Value::MerkleDigest(
                                Scheme::Poseidon2KoalaBearExt4,
                                root.into(),
                            ))
                            .unwrap();
                        assert_eq!(messages.values[0], expected);
                    }
                } else {
                    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                    assert!(verifier.outputs.is_empty());
                }
                cases += 1;
            };
            for rows in [2, 4, 8, 16] {
                trial(rows, rows, rows, !fixed || rows == 8);
            }
            for rows in [0, 1, 3, 6, 32] {
                trial(rows, rows, rows, false);
            }
            for rows in [0, 1, 3, 6, 32] {
                if !input || !fixed {
                    trial(8, 8, rows, false);
                }
            }
            if !fixed {
                trial(8, 8, 4, true);
            }
            if !input {
                trial(8, 4, 8, false);
                trial(8, 16, 8, false);
            }
        }
    }
    cases += query_trials(directory);
    cases += virtual_trials(directory);
    println!("{cases} native selected-root, authenticated-query and refusal controls passed");
}

#[derive(Default)]
struct QueryMessages {
    sites: Vec<String>,
    fault: &'static str,
}
impl Hooks<CpuBackend> for QueryMessages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        self.sites.push(exchange.site.to_owned());
        let expected = if exchange.site.contains("opening_instance")
            || exchange.site.contains("opening_position")
        {
            ("V", "P")
        } else {
            ("P", "V")
        };
        assert_eq!((exchange.sender, exchange.receiver), expected);
        let replacement = match self.fault {
            "instance" if exchange.site.contains("opening_instance") => Some(Value::Index(1)),
            "position" if exchange.site.contains("opening_position") => Some(Value::Index(1)),
            "row" if exchange.site.contains("opening_row") => Some(Value::KoalaBearExt4Vector(
                vec![scalar(77), scalar(88)].into(),
            )),
            "root" if exchange.site.contains("deliver") => Some(Value::MerkleDigest(
                Scheme::Poseidon2KoalaBearExt4,
                vec![0; 32].into(),
            )),
            "proof" if exchange.site.contains("opening_proof") => {
                let mut changed = bytes.to_vec();
                *changed.last_mut().unwrap() ^= 1;
                return Ok(Some(changed));
            }
            _ => None,
        };
        Ok(replacement.map(|value| backend("V").encode_native_value(&value).unwrap()))
    }
}
fn query_trials(directory: &Path) -> usize {
    let mut cases = 0;
    for input in [false, true] {
        for fixed in [false, true] {
            let name = format!(
                "query-{}-{}",
                if input { "input" } else { "send" },
                if fixed { "fixed" } else { "dynamic" }
            );
            let bundle = Bundle::admit(
                &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
                &backend("V"),
                zkc_cpu::cpu_contracts(),
                BundleLimits::default(),
            )
            .unwrap();
            let mut trial = |rows: u64, position: u64, fault: &'static str| {
                let arranged = (0..rows / 2)
                    .flat_map(|i| [scalar(i), scalar(i + rows / 2)])
                    .collect();
                let (root, _) = commit::<Quartic>(
                    arranged,
                    Shape::new(2, rows as usize / 2, 64).unwrap(),
                    1 << 20,
                )
                .unwrap();
                let mut holder = vec![Value::KoalaBearExt4Vector(
                    (0..rows).map(scalar).collect::<Vec<_>>().into(),
                )];
                let mut receiver = vec![];
                if input {
                    receiver.push(Value::MerkleDigest(
                        Scheme::Poseidon2KoalaBearExt4,
                        if fault == "root" { vec![0; 32] } else { root }.into(),
                    ));
                } else {
                    holder.push(Value::Index(rows));
                    receiver.push(Value::Index(rows));
                }
                receiver.push(Value::Index(position));
                if input && !fixed {
                    receiver.push(Value::Index(rows));
                }
                let mut messages = QueryMessages {
                    fault,
                    ..Default::default()
                };
                let report = run(
                    &bundle,
                    "oracle_roots",
                    vec![
                        RoleInput {
                            role: "P".into(),
                            backend: backend("P"),
                            values: holder,
                        },
                        RoleInput {
                            role: "V".into(),
                            backend: backend("V"),
                            values: receiver,
                        },
                    ],
                    RunLimits::default(),
                    &mut messages,
                )
                .unwrap();
                let complete = position < rows && fault.is_empty();
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name}/{rows}/{position}/{fault}: {:?}",
                    report.outcome
                );
                let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
                if complete {
                    assert_eq!(verifier.outputs.len(), 1);
                    assert!(
                        matches!(verifier.outputs[0], Value::KoalaBearExt4Field(value) if value == scalar(position))
                    );
                    let reached: Vec<_> = messages
                        .sites
                        .iter()
                        .filter(|s| s.contains("opening_"))
                        .collect();
                    assert_eq!(reached.len(), 4);
                    for (site, purpose) in reached.iter().zip([
                        "opening_instance",
                        "opening_position",
                        "opening_row",
                        "opening_proof",
                    ]) {
                        assert!(
                            site.contains(purpose),
                            "wrong request/response order: {site}"
                        );
                    }
                } else {
                    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                    assert!(verifier.outputs.is_empty());
                    if position >= rows {
                        assert!(
                            !messages.sites.iter().any(|s| s.contains("opening_")),
                            "out-of-domain query communicated an opening request"
                        );
                    }
                }
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                cases += 1;
            };
            for rows in [2, 4, 8, 16] {
                if fixed && rows != 8 {
                    continue;
                }
                for position in 0..rows {
                    trial(rows, position, "");
                }
                trial(rows, rows, "");
                trial(rows, u64::MAX, "");
            }
            for fault in ["instance", "position", "row", "proof", "root"] {
                trial(8, 0, fault);
            }
        }
    }
    cases
}

fn virtual_trials(directory: &Path) -> usize {
    let mut cases = 0;
    for mode in 0..3 {
        let zero = mode != 0;
        let only = mode == 2;
        let name = match mode {
            0 => "query-recurrence",
            1 => "query-zero-trailing",
            _ => "query-zero-only",
        };
        let bundle = Bundle::admit(
            &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
            &backend("V"),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for trips in 0..=3 {
            for (position, mapped, fault) in [
                (0, 1, ""),
                (3, 3, ""),
                (7, 0, ""),
                (0, 8, ""),
                (8, 0, ""),
                (0, 1, "proof"),
                (0, 1, "row"),
            ] {
                let mut messages = QueryMessages {
                    fault,
                    ..Default::default()
                };
                let report = run(
                    &bundle,
                    "oracle_roots",
                    vec![
                        RoleInput {
                            role: "P".into(),
                            backend: backend("P"),
                            values: vec![
                                Value::KoalaBearExt4Vector(
                                    (0..8).map(scalar).collect::<Vec<_>>().into(),
                                ),
                                Value::KoalaBearExt4Field(scalar(99)),
                                Value::Index(mapped),
                                Value::Index(trips),
                            ],
                        },
                        RoleInput {
                            role: "V".into(),
                            backend: backend("V"),
                            values: vec![
                                Value::KoalaBearExt4Field(scalar(99)),
                                Value::Index(mapped),
                                Value::Index(position),
                                Value::Index(trips),
                            ],
                        },
                    ],
                    RunLimits::default(),
                    &mut messages,
                )
                .unwrap();
                let complete =
                    position < 8 && (only || ((trips == 0 || mapped < 8) && fault.is_empty()));
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name}/{trips}/{position}/{mapped}/{fault}: {:?}",
                    report.outcome
                );
                let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
                if complete {
                    assert_eq!(verifier.outputs.len(), 1);
                    assert!(
                        matches!(verifier.outputs[0], Value::KoalaBearExt4Field(value) if value == scalar(if only { 99 } else { position }))
                    );
                } else {
                    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                    assert!(verifier.outputs.is_empty());
                }
                // Duplicates and unused answers remain separate reached openings.
                // An invalid later mapped query (including a zero-query child)
                // retains the first opening; authentication failure stops there.
                let expected = if only || position >= 8 {
                    0
                } else if !complete || zero {
                    1
                } else {
                    trips as usize + 1
                };
                let openings = messages
                    .sites
                    .iter()
                    .filter(|s| s.contains("opening_proof"))
                    .count();
                assert_eq!(
                    openings, expected,
                    "{name}/{trips}/{position}/{mapped}/{fault}"
                );
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                cases += 1;
            }
        }
    }
    cases
}
