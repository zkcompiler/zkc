//! Execute fresh compiler bundles with real arithmetic, codecs and managed roots.
//! This is an executable integration client: expectations come from each source
//! protocol and its arithmetic, independently of the generated dispatch plan.
use std::collections::BTreeMap;
use zkc_backends::services::{ServiceObservation, ServiceReference, ServiceRegistry};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};

use zkc_runtime::interactive::Value as RuntimeValue;
use zkc_tools::run::*;

fn backend(role: &str, session: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, session, entry, None), None),
        Default::default(),
    )
    .unwrap()
}
fn bundle(fixtures: &Fixtures, name: &str) -> Bundle {
    let suffix = fixtures.suffix;
    let bytes = std::fs::read(fixtures.directory.join(format!("{name}{suffix}.bundle"))).unwrap();
    Bundle::admit(
        &bytes,
        &backend("Alice", "admission", "main"),
        BundleLimits::default(),
    )
    .unwrap_or_else(|error| panic!("bundle {name}: {error}"))
}
fn field(n: u64) -> Value {
    Value::Field(Scalar::from(n))
}
fn tape(registry: &ServiceRegistry, owner: &str, budget: u64, values: &[u64]) -> ServiceReference {
    registry
        .issue_test_tape(
            owner,
            budget,
            values.iter().copied().map(Scalar::from).collect(),
        )
        .unwrap()
}
type References = BTreeMap<String, Vec<ServiceReference>>;
type Inputs = BTreeMap<String, Vec<Value>>;
struct Audit {
    registry: ServiceRegistry,
    references: References,
    before: BTreeMap<String, Vec<ServiceObservation>>,
    after: BTreeMap<String, Vec<ServiceObservation>>,
    messages: Vec<(String, Vec<u8>)>,
    replacement: Option<(String, Vec<u8>)>,
}
impl Audit {
    fn new(registry: &ServiceRegistry, references: References) -> Self {
        Self {
            registry: registry.clone(),
            references,
            before: BTreeMap::new(),
            after: BTreeMap::new(),
            messages: vec![],
            replacement: None,
        }
    }
}
impl Hooks<NativeBackend> for Audit {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        assert!(self.messages.len() < 64);
        self.messages.push((exchange.site.into(), bytes.to_vec()));
        if self
            .replacement
            .as_ref()
            .is_some_and(|(site, _)| site == exchange.site)
        {
            return Ok(Some(self.replacement.take().unwrap().1));
        }
        Ok(None)
    }
    fn observe(
        &mut self,
        role: &str,
        _: &NativeBackend,
        phase: Phase,
    ) -> Result<Option<String>, String> {
        let observations: Vec<_> = self
            .references
            .get(role)
            .into_iter()
            .flatten()
            .map(|r| self.registry.observe(r).unwrap())
            .collect();
        let text = format!("{observations:?}");
        assert!(text.len() <= 4096);
        match phase {
            Phase::BeforeCancellation => self.before.insert(role.into(), observations),
            Phase::AfterCancellation => self.after.insert(role.into(), observations),
        };
        Ok(Some(text))
    }
}
fn run_case(
    bundle: &Bundle,
    session: &str,
    mut values: Inputs,
    audit: &mut Audit,
) -> Report<NativeBackend> {
    let inputs = bundle
        .roles()
        .iter()
        .map(|role| {
            let name = &role.entry.role;
            let references = audit.references.get(name).cloned().unwrap_or_default();
            assert_eq!(references.len(), role.entry.services.len());
            let ports = role
                .entry
                .services
                .iter()
                .map(|p| p.name.clone())
                .zip(references)
                .collect();
            let backend = backend(name, session, bundle.entry())
                .with_services(audit.registry.clone(), ports)
                .unwrap();
            RoleInput {
                role: name.clone(),
                backend,
                values: values.remove(name).unwrap(),
            }
        })
        .collect();
    assert!(values.is_empty());
    let report = run(bundle, session, inputs, RunLimits::default(), audit).unwrap();
    assert!(audit.after.values().flatten().all(|o| !o.leased));
    report
}
fn role<'a>(report: &'a Report<NativeBackend>, name: &str) -> &'a RoleReport<Value> {
    report.roles.iter().find(|r| r.role == name).unwrap()
}
fn draws(observation: &ServiceObservation, count: u64, budget: u64, poisoned: bool, leased: bool) {
    let state = observation
        .state
        .as_ref()
        .expect("known test tape completion");
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (count, count, budget)
    );
    assert_eq!(
        (observation.poisoned, observation.leased),
        (poisoned, leased)
    );
}
fn nested(directory: &Fixtures) {
    let b = bundle(directory, "nested");
    for (count, replacement, expected, draws_count) in [
        (0, None, Outcome::Completed, 0),
        (1, None, Outcome::Completed, 0),
        (3, None, Outcome::Completed, 3),
        (3, Some(9), Outcome::ParticipantStopped { role: 1 }, 0),
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let coins = tape(&registry, "V", 8, &[2, 3, 5, 7, 11, 13, 17, 19]);
        let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
        if let Some(changed) = replacement {
            audit.replacement = Some((
                "count".into(),
                backend("P", "codec", "main")
                    .encode_native_value(&Value::Index(changed))
                    .unwrap(),
            ));
        }
        let report = run_case(
            &b,
            "nested",
            BTreeMap::from([
                ("P".into(), vec![Value::Index(count), field(10)]),
                ("V".into(), vec![Value::Bool(true)]),
            ]),
            &mut audit,
        );
        assert_eq!(report.outcome, expected, "nested {count} {replacement:?}");
        draws(
            &audit.after["V"][0],
            draws_count,
            8 - draws_count,
            false,
            false,
        );
        assert_eq!(audit.messages.len() as u64, 1 + draws_count);
        if expected == Outcome::Completed {
            let Value::Field(actual) = &role(&report, "P").outputs[0] else {
                panic!("field output")
            };
            assert_eq!(*actual, Scalar::from(if count == 3 { 20 } else { 10 }));
            let starts: Vec<_> = report
                .reached
                .iter()
                .filter(|r| r.step.role == 0 && r.loop_started)
                .map(|r| (r.iterations.clone(), r.loop_count.unwrap()))
                .collect();
            let mut expected = vec![(vec![], count)];
            expected.extend((0..count).map(|i| (vec![i], i)));
            assert_eq!(starts, expected);
        }
    }
}
fn data_values(directory: &Fixtures) {
    let b = bundle(directory, "data");
    let registry = ServiceRegistry::new(Policy::default());
    let mut audit = Audit::new(&registry, BTreeMap::new());
    let report = run_case(
        &b,
        "data",
        BTreeMap::from([("P".into(), vec![Value::Index(3), field(11)])]),
        &mut audit,
    );
    assert_eq!(report.outcome, Outcome::Completed);
    let output = &report.roles[0].outputs;
    let Value::Variant(record) = &output[0] else {
        panic!("record")
    };
    assert_eq!(record.alternative(), 0);
    assert!(matches!(record.payload()[0], Value::Index(3)));
    assert!(matches!(output[1], Value::Field(f) if f == Scalar::from(11)));
    assert!(matches!(output[2], Value::Bool(true)));
    let Value::FieldArray(empty) = &output[3] else {
        panic!("empty array")
    };
    assert!(empty.elements().is_empty());
}

fn traces(directory: &Fixtures) {
    let b = bundle(directory, "traces");
    let descriptor = b.roles()[0].entry.inputs[0]
        .1
        .logical()
        .variant_descriptor()
        .unwrap()
        .clone();
    for (a, bshape) in [
        (None, None),
        (Some((0, 3)), None),
        (None, Some((4, 2))),
        (Some((2, 7)), Some((8, 3))),
    ] {
        let make = |shape: Option<(usize, usize)>| {
            let values = shape
                .map(|(rows, cols)| {
                    vec![Value::matrix(rows, cols, &[], &Policy::default()).unwrap()]
                })
                .unwrap_or_default();
            Value::pack_variant(descriptor.clone(), usize::from(shape.is_some()), values).unwrap()
        };
        let registry = ServiceRegistry::new(Policy::default());
        let mut audit = Audit::new(&registry, BTreeMap::new());
        let report = run_case(
            &b,
            "traces",
            BTreeMap::from([("P".into(), vec![make(a), make(bshape)])]),
            &mut audit,
        );
        assert_eq!(report.outcome, Outcome::Completed);
        let out = &report.roles[0].outputs;
        assert!(matches!(out[0],Value::Bool(v) if v==a.is_some()));
        assert!(matches!(out[1],Value::Bool(v) if v==bshape.is_some()));
        let expected = [
            a.unwrap_or((0, 0)).0,
            a.unwrap_or((0, 0)).1,
            bshape.unwrap_or((0, 0)).0,
            bshape.unwrap_or((0, 0)).1,
        ];
        for (v, n) in out[2..].iter().zip(expected) {
            assert!(matches!(v,Value::Index(x) if *x==n as u64));
        }
    }
}
fn table(values: &[u64]) -> Value {
    Value::table(
        &values.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
// Independent tensor-product reference in logical MSB axis order.
fn evaluate(values: &[u64], point: &[u64]) -> Scalar {
    let mut values: Vec<_> = values.iter().copied().map(Scalar::from).collect();
    for r in point {
        let half = values.len() / 2;
        values = (0..half)
            .map(|i| values[i] + Scalar::from(*r) * (values[i + half] - values[i]))
            .collect();
    }
    assert_eq!(values.len(), 1);
    values[0]
}
fn sumcheck(directory: &Fixtures) {
    for (name, power) in [("sumcheck", 1_u32), ("cubic", 2_u32)] {
        let b = bundle(directory, name);
        let challenges = [2, 3, 5, 7, 11, 13, 17, 19];
        for (n, values, other) in [
            (0, vec![3], vec![5]),
            (1, vec![0, 1], vec![0, 1]),
            (2, vec![1, 2, 4, 8], vec![3, 5, 7, 11]),
            (
                3,
                vec![0, 1, 2, 3, 4, 5, 6, 7],
                vec![2, 3, 5, 7, 11, 13, 17, 19],
            ),
        ] {
            for fault in [
                "none",
                "coefficient",
                "linear",
                "terminal",
                "count",
                "short_count",
                "shape",
            ] {
                if n == 0 && ["coefficient", "linear"].contains(&fault) {
                    continue;
                }
                if fault == "short_count" && n == 0 {
                    continue;
                }
                if fault == "linear" && n != 1 {
                    continue;
                }
                let registry = ServiceRegistry::new(Policy::default());
                let coins = tape(&registry, "V", 8, &challenges);
                let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
                let encode = |v| {
                    backend("P", "codec", "main")
                        .encode_native_value(&v)
                        .unwrap()
                };
                if fault == "count" {
                    audit.replacement = Some(("arity".into(), encode(Value::Index(9))));
                }
                if fault == "short_count" {
                    audit.replacement = Some(("arity".into(), encode(Value::Index(n - 1))));
                }
                if fault == "coefficient" || fault == "linear" {
                    let mut coefficients = vec![0_u64; power as usize + 2];
                    if fault == "linear" {
                        coefficients[1] = 1;
                    } else {
                        coefficients[0] = 999;
                    }
                    let ty = zkc_runtime::interactive::LogicalType::field_array(
                        zkc_runtime::interactive::Identity::Bls12381Fr,
                        power as u64 + 2,
                    )
                    .unwrap();
                    let arr = Value::FieldArray(
                        zkc_backends::FieldArray::new(
                            ty,
                            coefficients
                                .into_iter()
                                .map(Scalar::from)
                                .collect::<Vec<_>>()
                                .into(),
                        )
                        .unwrap(),
                    );
                    audit.replacement = Some(("round_message".into(), encode(arr)));
                }
                let claim = values
                    .iter()
                    .zip(&other)
                    .map(|(a, b)| u64::pow(*a, power) * b)
                    .sum::<u64>();
                let changed = if fault == "terminal" {
                    values.iter().map(|x| x + 1).collect::<Vec<_>>()
                } else {
                    values.clone()
                };
                let initial = if fault == "shape" { n + 1 } else { n };
                let report = run_case(
                    &b,
                    "sumcheck",
                    BTreeMap::from([
                        (
                            "P".into(),
                            vec![Value::Index(initial), table(&values), table(&other)],
                        ),
                        (
                            "V".into(),
                            vec![table(&changed), table(&other), field(claim)],
                        ),
                    ]),
                    &mut audit,
                );
                let expected = match fault {
                    "coefficient" | "count" | "short_count" => {
                        Outcome::ParticipantStopped { role: 1 }
                    }
                    "shape" => Outcome::ParticipantStopped { role: 0 },
                    _ => Outcome::Completed,
                };
                assert_eq!(report.outcome, expected, "sumcheck n={n} {fault}");
                let used = if expected == Outcome::Completed { n } else { 0 };
                draws(&audit.after["V"][0], used, 8 - used, false, false);
                if expected == Outcome::Completed {
                    let accepted = fault == "none";
                    assert!(
                        matches!(role(&report,"V").outputs[0],Value::Bool(v) if v==accepted),
                        "sumcheck n={n} {fault}"
                    );
                    let output = &role(&report, "P").outputs;
                    let Value::Point(point) = &output[0] else {
                        panic!("point")
                    };
                    assert_eq!(
                        point.as_ref(),
                        challenges[..n as usize]
                            .iter()
                            .copied()
                            .map(Scalar::from)
                            .collect::<Vec<_>>()
                    );
                    let a = evaluate(&values, &challenges[..n as usize]);
                    let reference = (if power == 1 { a } else { a * a })
                        * evaluate(&other, &challenges[..n as usize]);
                    assert!(matches!(output[1],Value::Field(v) if v==reference));
                }
            }
        }
    }
}

fn layers(directory: &Fixtures) {
    let b = bundle(directory, "layers");
    for count in [0, 1, 3] {
        let registry = ServiceRegistry::new(Policy::default());
        let coins = tape(&registry, "V", 8, &[2, 3, 5, 7, 11, 13, 17, 19]);
        let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
        let report = run_case(
            &b,
            "layers",
            BTreeMap::from([
                ("P".into(), vec![Value::Index(count)]),
                ("V".into(), vec![Value::Index(count)]),
            ]),
            &mut audit,
        );
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(matches!(role(&report, "V").outputs[0], Value::Bool(true)));
        let used = count * (count.saturating_sub(1)) / 2;
        draws(&audit.after["V"][0], used, 8 - used, false, false);
        let nested: Vec<_> = report
            .reached
            .iter()
            .filter(|r| r.step.role == 0 && r.loop_started && r.iterations.len() == 1)
            .map(|r| r.loop_count.unwrap())
            .collect();
        assert_eq!(nested, (0..count).collect::<Vec<_>>());
    }
}

fn weighted(directory: &Fixtures) {
    use ark_ff::Field;
    let b = bundle(directory, "weighted");
    let challenges = [2, 3, 5, 7, 11, 13, 17, 19];
    for n in [0_u64, 1, 3] {
        for fault in [
            "none",
            "left",
            "terminal",
            "zero",
            "changed_challenge",
            "odd",
            "short",
        ] {
            if n == 0 && !["none", "terminal", "short"].contains(&fault) {
                continue;
            }
            let registry = ServiceRegistry::new(Policy::default());
            let mut tape_values = challenges;
            if fault == "zero" {
                tape_values[0] = 0;
            }
            let coins = tape(&registry, "V", 8, &tape_values);
            let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
            let changed = match fault {
                "left" => Some(("left", 999)),
                "terminal" => Some(("terminalA", 999)),
                "changed_challenge" => Some(("challenge", 0)),
                _ => None,
            };
            if let Some((site, value)) = changed {
                audit.replacement = Some((
                    site.into(),
                    backend("P", "codec", "main")
                        .encode_native_value(&field(value))
                        .unwrap(),
                ));
            }
            let length = if fault == "odd" { 3 } else { 1usize << n };
            let a: Vec<_> = (0..length).map(|i| Scalar::from(i as u64 + 1)).collect();
            let bv: Vec<_> = (0..length)
                .map(|i| Scalar::from(2 * i as u64 + 3))
                .collect();
            let claim = a.iter().zip(&bv).map(|(a, b)| *a * *b).sum::<Scalar>();
            let count = if fault == "short" {
                if n == 0 { 1 } else { n - 1 }
            } else {
                n
            };
            let report = run_case(
                &b,
                "weighted",
                BTreeMap::from([
                    (
                        "P".into(),
                        vec![
                            Value::Index(count),
                            Value::Vector(a.clone().into()),
                            Value::Vector(bv.clone().into()),
                        ],
                    ),
                    ("V".into(), vec![Value::Index(count), Value::Field(claim)]),
                ]),
                &mut audit,
            );
            let expected = match fault {
                "zero" => Outcome::ParticipantStopped { role: 1 },
                "changed_challenge" | "odd" | "short" => Outcome::ParticipantStopped { role: 0 },
                _ => Outcome::Completed,
            };
            assert_eq!(report.outcome, expected, "weighted {n} {fault}");
            let used = match fault {
                "odd" => 0,
                "short" => count.min(n),
                "zero" | "changed_challenge" => 1,
                _ => n,
            };
            draws(&audit.after["V"][0], used, 8 - used, false, false);
            if expected == Outcome::Completed {
                assert!(
                    matches!(role(&report,"V").outputs[0],Value::Bool(v) if v==(fault=="none")),
                    "weighted {n} {fault}"
                );
                let (mut a, mut bv) = (a, bv);
                for x in challenges.iter().take(n as usize) {
                    let x = Scalar::from(*x);
                    let ix = x.inverse().unwrap();
                    let half = a.len() / 2;
                    a = (0..half).map(|i| x * a[i] + ix * a[i + half]).collect();
                    bv = (0..half).map(|i| ix * bv[i] + x * bv[i + half]).collect();
                }
                let out = &role(&report, "P").outputs;
                assert!(matches!(out[0],Value::Field(v) if v==a[0]));
                assert!(matches!(out[1],Value::Field(v) if v==bv[0]));
            }
        }
    }
}

struct Fixtures {
    directory: std::path::PathBuf,
    suffix: &'static str,
}
fn main() {
    let directory = std::env::args().nth(1).expect("bundle directory");
    for suffix in ["", "_plain", "_release"] {
        execute(&Fixtures {
            directory: directory.clone().into(),
            suffix,
        });
    }
    println!(
        "native iteration: Sumcheck, nested layers, weighted folds, aggregates, failures and ownership passed in all three compiler modes"
    );
}
fn execute(directory: &Fixtures) {
    let evaluation = bundle(directory, "evaluate");
    for n in [0, 1, 2, 3] {
        let values = (1..=(1 << n)).collect::<Vec<u64>>();
        let other = values.iter().map(|x| x * x + 3).collect::<Vec<_>>();
        for delta in [-1_i32, 0, 1] {
            if n == 0 && delta < 0 {
                continue;
            }
            let coordinates = vec![2_u64; (n as i32 + delta) as usize];
            let registry = ServiceRegistry::new(Policy::default());
            let mut audit = Audit::new(&registry, BTreeMap::new());
            let report = run_case(
                &evaluation,
                "evaluate",
                BTreeMap::from([(
                    "P".into(),
                    vec![
                        Value::Point(
                            coordinates
                                .iter()
                                .copied()
                                .map(Scalar::from)
                                .collect::<Vec<_>>()
                                .into(),
                        ),
                        table(&values),
                        table(&other),
                    ],
                )]),
                &mut audit,
            );
            if delta == 0 {
                assert_eq!(report.outcome, Outcome::Completed);
                let expected = evaluate(&values, &coordinates) * evaluate(&other, &coordinates);
                assert!(matches!(role(&report,"P").outputs[0],Value::Field(x) if x==expected));
            } else {
                assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 0 });
            }
        }
        let constant = bundle(directory, "constant");
        let registry = ServiceRegistry::new(Policy::default());
        let coins = tape(&registry, "V", 8, &[2, 3, 5, 7, 11, 13, 17, 19]);
        let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
        let report = run_case(
            &constant,
            "constant",
            BTreeMap::from([
                (
                    "P".into(),
                    vec![Value::Index(n), table(&values), table(&other)],
                ),
                (
                    "V".into(),
                    vec![table(&values), table(&other), field(7 * (1 << n))],
                ),
            ]),
            &mut audit,
        );
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(matches!(role(&report, "V").outputs[0], Value::Bool(true)));
        assert!(matches!(role(&report,"P").outputs[1],Value::Field(x) if x==Scalar::from(7)));
    }

    let demand = bundle(directory, "demand");
    for n in [0, 1, 3] {
        let registry = ServiceRegistry::new(Policy::default());
        let mut audit = Audit::new(&registry, BTreeMap::new());
        let report = run_case(
            &demand,
            "demand",
            BTreeMap::from([("P".into(), vec![Value::Index(n), field(5)])]),
            &mut audit,
        );
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(matches!(role(&report,"P").outputs[0],Value::Field(x) if x==Scalar::from(5+10*n)));
        if n == 0 {
            assert_eq!(
                report.reached.len(),
                2,
                "body-only invariant math must not run on the zero path"
            );
        }
    }
    weighted(directory);
    layers(directory);
    sumcheck(directory);
    traces(directory);
    nested(directory);
    data_values(directory);
    let b = bundle(directory, "repeat");
    for (n, m, go, expected, draws_count) in [
        (0, 0, true, Outcome::Completed, 0),
        (1, 1, true, Outcome::Completed, 1),
        (3, 3, true, Outcome::Completed, 3),
        (3, 3, false, Outcome::ParticipantStopped { role: 1 }, 0),
        (2, 9, true, Outcome::ParticipantStopped { role: 1 }, 0),
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let coins = tape(&registry, "V", 8, &[2, 3, 5, 7, 11, 13, 17, 19]);
        let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
        let inputs = BTreeMap::from([
            ("P".into(), vec![Value::Index(n), field(10)]),
            ("V".into(), vec![Value::Index(m), Value::Bool(go)]),
        ]);
        let report = run_case(&b, "iteration", inputs, &mut audit);
        assert_eq!(report.outcome, expected, "n={n} m={m} go={go}");
        let observation = &audit.after["V"][0];
        draws(observation, draws_count, 8 - draws_count, false, false);
        assert_eq!(audit.messages.len(), draws_count as usize);
        if expected == Outcome::Completed {
            let Value::Field(actual) = &role(&report, "P").outputs[0] else {
                panic!("field result")
            };
            let expected = 10 + [2, 3, 5].iter().take(n as usize).sum::<u64>();
            assert_eq!(*actual, Scalar::from(expected));
            let occurrences: Vec<_> = report
                .reached
                .iter()
                .filter(|r| r.sent_bytes.is_some() && r.replacement_bytes.is_none())
                .map(|r| r.iterations.clone())
                .collect();
            assert_eq!(
                occurrences,
                (0..n).flat_map(|i| [vec![i], vec![i]]).collect::<Vec<_>>()
            );
        }
    }
    let registry = ServiceRegistry::new(Policy::default());
    let coins = tape(&registry, "V", 8, &[2]);
    let mut audit = Audit::new(&registry, BTreeMap::from([("V".into(), vec![coins])]));
    let report = run_case(
        &b,
        "disagreement",
        BTreeMap::from([
            ("P".into(), vec![Value::Index(1), field(10)]),
            ("V".into(), vec![Value::Index(2), Value::Bool(true)]),
        ]),
        &mut audit,
    );
    assert!(
        matches!(report.outcome, Outcome::DriverFailed(ref f) if f.kind == FailureKind::Contract)
    );
    draws(&audit.after["V"][0], 0, 8, false, false);
}
