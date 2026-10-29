//! Common oracle roots use the selected scheme and preserve receiver shape custody.
use std::path::Path;
use zkc_cpu::merkle::Scheme;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, KoalaBear, KoalaBearExt4, Policy, Value, Variant};
use zkc_kernels::plonky3::{
    merkle::{commit, poseidon2::Quartic},
    oracle::Shape,
};
use zkc_runtime::host::joint::*;
use zkc_runtime::vm::Value as RuntimeValue;

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
    if std::env::args().nth(2).as_deref() == Some("batches") {
        let cases = batch_trials(directory);
        println!("{cases} native query-block, sharing and refusal controls passed");
        return;
    }
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
    cases += multiple_trials(directory);
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
        let request = exchange.site.contains("opening_request");
        let response = exchange.site.contains("opening_response");
        let expected = if request { ("V", "P") } else { ("P", "V") };
        assert_eq!((exchange.sender, exchange.receiver), expected);
        if self.fault == "proof" && response {
            let mut changed = bytes.to_vec();
            *changed.last_mut().unwrap() ^= 1;
            return Ok(Some(changed));
        }
        let replacement = if (request
            && matches!(
                self.fault,
                "instance" | "position" | "constructor" | "unknown_constructor"
            ))
            || (response && matches!(self.fault, "row" | "response_constructor"))
        {
            let decoded = backend("V")
                .decode_native_value(exchange.ty, bytes)
                .unwrap();
            let Value::Variant(value) = decoded else {
                panic!("non-variant opening")
            };
            let mut payload = value.payload().to_vec();
            let mut alternative = value.alternative();
            match self.fault {
                "instance" => payload[1] = Value::Index(1),
                "position" => payload[2] = Value::Index(1),
                "constructor" => payload[0] = Value::Index(1),
                "unknown_constructor" => payload[0] = Value::Index(99),
                "response_constructor" => alternative = 1 - alternative,
                "row" => {
                    payload[0] = match payload[0] {
                        Value::KoalaBearVector(_) => Value::KoalaBearVector(
                            vec![KoalaBear::new(77), KoalaBear::new(88)].into(),
                        ),
                        _ => Value::KoalaBearExt4Vector(vec![scalar(77), scalar(88)].into()),
                    };
                }
                _ => unreachable!(),
            }
            Some(Value::Variant(
                Variant::new(exchange.ty.clone(), alternative, payload).unwrap(),
            ))
        } else if self.fault == "root" && exchange.site.contains("deliver") {
            Some(Value::MerkleDigest(
                Scheme::Poseidon2KoalaBearExt4,
                vec![0; 32].into(),
            ))
        } else {
            None
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
                    assert_eq!(reached.len(), 2);
                    for (site, purpose) in
                        reached.iter().zip(["opening_request", "opening_response"])
                    {
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
                    .filter(|s| s.contains("opening_response"))
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

fn multiple_trials(directory: &Path) -> usize {
    let mut cases = 0;
    for mode in ["multiple", "mixed-kind", "mixed-scheme"] {
        let name = format!("query-{mode}");
        let bundle = Bundle::admit(
            &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
            &backend("V"),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for trips in 0..=3 {
            for (position, mapped, fault) in [
                (0, 0, ""),
                (1, 3, ""),
                (3, 1, ""),
                (4, 0, ""),
                (0, 4, ""),
                (0, 0, "instance"),
                (0, 0, "position"),
                (0, 0, "unknown_constructor"),
                (0, 0, "proof"),
                (0, 0, "row"),
                (0, 0, "constructor"),
                (0, 0, "response_constructor"),
            ] {
                // The equal-typed modes use identical tables and layouts. A
                // substituted constructor can return an otherwise valid proof,
                // so these cases depend on the suspended-constructor guard.
                if fault == "response_constructor" && mode != "multiple" {
                    continue;
                }
                let base = || {
                    Value::KoalaBearVector(
                        (0..4)
                            .map(|i| KoalaBear::new(i + 11))
                            .collect::<Vec<_>>()
                            .into(),
                    )
                };
                let extension =
                    || Value::KoalaBearExt4Vector((0..4).map(scalar).collect::<Vec<_>>().into());
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
                                if mode == "mixed-scheme" {
                                    base()
                                } else {
                                    extension()
                                },
                                if mode == "multiple" {
                                    extension()
                                } else {
                                    base()
                                },
                                Value::Index(mapped),
                                Value::Index(trips),
                            ],
                        },
                        RoleInput {
                            role: "V".into(),
                            backend: backend("V"),
                            values: vec![
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
                let complete = position < 4 && (trips == 0 || mapped < 4) && fault.is_empty();
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name}/{trips}/{position}/{mapped}/{fault}: {:?}",
                    report.outcome
                );
                let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
                if complete {
                    assert_eq!(verifier.outputs.len(), 1);
                    if mode == "mixed-scheme" {
                        assert!(
                            matches!(verifier.outputs[0], Value::KoalaBearField(value) if value == KoalaBear::new(position as u32 + 11))
                        );
                    } else {
                        assert!(
                            matches!(verifier.outputs[0], Value::KoalaBearExt4Field(value) if value == scalar(position))
                        );
                    }
                } else {
                    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                    assert!(verifier.outputs.is_empty());
                }
                let responses = messages
                    .sites
                    .iter()
                    .filter(|s| s.contains("opening_response"))
                    .count();
                let expected =
                    if position >= 4 || matches!(fault, "instance" | "unknown_constructor") {
                        0
                    } else if !complete {
                        1
                    } else {
                        trips as usize + 1
                    };
                assert_eq!(responses, expected, "{name}/{trips}/{fault}");
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                cases += 1;
            }
        }
    }
    cases
}

// Inspect the ordinary packet codec, so the controls observe the actual wire
// requests rather than trusting the compiler's query-block record.
#[derive(Default)]
struct BatchMessages {
    requests: Vec<Vec<(u64, u64, u64)>>,
    responses: Vec<usize>,
    fault: &'static str,
    injected: bool,
}
impl Hooks<CpuBackend> for BatchMessages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        let request = exchange.site.contains("opening_request");
        let response = exchange.site.contains("opening_response");
        if !request && !response {
            return Ok(None);
        }
        assert_eq!(
            (exchange.sender, exchange.receiver),
            if request { ("V", "P") } else { ("P", "V") }
        );
        let decoded = backend("V")
            .decode_native_value(exchange.ty, bytes)
            .unwrap();
        let Value::Variant(outer) = &decoded else {
            panic!("non-variant packet")
        };
        let packet = matches!(outer.payload().first(), Some(Value::Variant(_)));
        let mut components = if packet {
            outer.payload().to_vec()
        } else {
            vec![decoded.clone()]
        };
        if request {
            self.requests.push(
                components
                    .iter()
                    .map(|component| {
                        let Value::Variant(value) = component else {
                            panic!("non-variant request")
                        };
                        let [
                            Value::Index(constructor),
                            Value::Index(instance),
                            Value::Index(position),
                        ] = value.payload()
                        else {
                            panic!("bad request")
                        };
                        (*constructor, *instance, *position)
                    })
                    .collect(),
            );
        } else {
            self.responses.push(components.len());
        }
        let inject = !self.injected
            && match self.fault {
                "request-position" | "request-instance" | "unknown-constructor" => request,
                "row" | "proof" => response,
                "response-swap" => response && packet,
                "" => false,
                _ => panic!("unknown fault"),
            };
        if !inject {
            return Ok(None);
        }
        self.injected = true;
        if self.fault == "proof" {
            let mut changed = bytes.to_vec();
            *changed.last_mut().unwrap() ^= 1;
            return Ok(Some(changed));
        }
        if self.fault == "response-swap" {
            let last = components.len() - 1;
            components.swap(0, last);
        } else {
            let ty = components[0].physical_type();
            let Value::Variant(value) = &components[0] else {
                unreachable!()
            };
            let mut payload = value.payload().to_vec();
            match self.fault {
                "request-position" => payload[2] = Value::Index(1),
                "request-instance" => payload[1] = Value::Index(99),
                "unknown-constructor" => payload[0] = Value::Index(99),
                "row" => {
                    let Value::KoalaBearExt4Vector(row) = &payload[0] else {
                        panic!("bad row")
                    };
                    payload[0] = Value::KoalaBearExt4Vector(vec![scalar(77); row.len()].into());
                }
                _ => unreachable!(),
            }
            components[0] = Value::Variant(Variant::new(ty, value.alternative(), payload).unwrap());
        }
        let changed = if packet {
            Value::Variant(
                Variant::new(exchange.ty.clone(), outer.alternative(), components).unwrap(),
            )
        } else {
            components.pop().unwrap()
        };
        Ok(Some(backend("V").encode_native_value(&changed).unwrap()))
    }
}
fn batch_trials(directory: &Path) -> usize {
    let mut cases = 0;
    for mode in [
        "paired",
        "individual",
        "reversed",
        "invalid-first",
        "invalid-later",
        "guard",
    ] {
        let bundle = Bundle::admit(
            &std::fs::read(directory.join(format!("batch-{mode}.bundle"))).unwrap(),
            &backend("V"),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for (position, allow, fault) in [
            (0, true, ""),
            (7, true, ""),
            (8, true, ""),
            (u64::MAX, true, ""),
            (0, false, ""),
            (8, false, ""),
            (0, true, "row"),
            (0, true, "proof"),
            (0, true, "response-swap"),
            (0, true, "request-position"),
            (0, true, "request-instance"),
            (0, true, "unknown-constructor"),
        ] {
            // Identical data yields equal roots. It must still be impossible to
            // swap the two constructors' response alternatives.
            let data = || Value::KoalaBearExt4Vector((0..8).map(scalar).collect::<Vec<_>>().into());
            let mut messages = BatchMessages {
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
                        values: vec![data(), data()],
                    },
                    RoleInput {
                        role: "V".into(),
                        backend: backend("V"),
                        values: vec![Value::Index(position), Value::Bool(allow)],
                    },
                ],
                RunLimits::default(),
                &mut messages,
            )
            .unwrap();
            let valid = !matches!(mode, "invalid-first" | "invalid-later") || position < 8;
            let complete = allow && valid && fault.is_empty();
            assert_eq!(
                matches!(report.outcome, Outcome::Completed),
                complete,
                "{mode}/{position}/{allow}/{fault}: {:?}",
                report.outcome
            );
            let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
            if complete {
                let x = if mode == "invalid-first" { position } else { 0 };
                let y = if mode == "invalid-later" { position } else { 4 };
                assert_eq!(verifier.outputs.len(), 5);
                for (value, expected) in verifier.outputs.iter().zip([x, y, 0, 0, 1]) {
                    assert!(
                        matches!(value, Value::KoalaBearExt4Field(actual) if *actual==scalar(expected))
                    );
                }
            } else {
                assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                assert!(verifier.outputs.is_empty());
            }
            let a = |position| (0, 0, position);
            let b = (1, 0, 0);
            let mut expected = match mode {
                "paired" | "reversed" => vec![vec![a(0), b]],
                "individual" => vec![vec![a(0), a(4), b]],
                "invalid-first" if !valid => vec![],
                "invalid-first" => vec![vec![a(position)], vec![a(4), b]],
                "invalid-later" if !valid => vec![vec![a(0)]],
                "invalid-later" => vec![vec![a(0)], vec![a(position)], vec![a(0), b]],
                "guard" if !allow => vec![vec![a(0)]],
                "guard" => vec![vec![a(0)], vec![a(4), b]],
                _ => unreachable!(),
            };
            if fault.is_empty() {
                if complete {
                    expected.push(vec![a(1)]);
                }
            } else {
                assert!(messages.injected, "{mode}/{fault} was not injected");
                let reached = if fault == "response-swap" {
                    expected.iter().position(|batch| batch.len() > 1).unwrap() + 1
                } else {
                    1
                };
                expected.truncate(reached);
            }
            assert_eq!(
                messages.requests, expected,
                "{mode}/{position}/{allow}/{fault}"
            );
            let mut expected_responses: Vec<_> = expected.iter().map(Vec::len).collect();
            if matches!(fault, "request-instance" | "unknown-constructor") {
                expected_responses.clear();
            }
            assert_eq!(messages.responses, expected_responses, "{mode}/{fault}");
            for (_, native) in &report.backends {
                assert_eq!(native.active_frames(), 0);
            }
            cases += 1;
        }
    }
    cases
}
