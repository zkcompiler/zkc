//! Execute generated structured-mathematics bundles against independent arithmetic.
//! Checked reports here are trusted compiler output. The wrong-connector control
//! demonstrates that changed wiring can change the terminal decision; report
//! hashes alone do not authenticate an untrusted producer's connector.
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::services::ServiceRegistry;
use zkc_backends::{Domain, EntryPolicy, FieldArray, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::{DecodeReason, Identity, LogicalType, Value as RuntimeValue};
use zkc_tools::run::*;

fn backend(role: &str, session: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, session, entry, None), None),
        Default::default(),
    )
    .unwrap()
}
fn bundle(directory: &Path, name: &str) -> Bundle {
    Bundle::admit(
        &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
        &backend("Solo", "admission", "main"),
        BundleLimits::default(),
    )
    .unwrap()
}
fn array(values: &[Scalar]) -> Value {
    Value::FieldArray(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, values.len() as u64).unwrap(),
            values.into(),
        )
        .unwrap(),
    )
}
fn elements(value: &Value) -> &[Scalar] {
    let Value::FieldArray(array) = value else {
        panic!("expected field array");
    };
    array.elements()
}
fn scalar(value: &Value) -> Scalar {
    let Value::Field(value) = value else {
        panic!("expected scalar");
    };
    *value
}
fn execute(
    bundle: &Bundle,
    session: &str,
    mut values: BTreeMap<String, Vec<Value>>,
) -> Report<NativeBackend> {
    let inputs = bundle
        .roles()
        .iter()
        .map(|role| RoleInput {
            role: role.entry.role.clone(),
            backend: backend(&role.entry.role, session, bundle.entry()),
            values: values.remove(&role.entry.role).unwrap(),
        })
        .collect();
    assert!(values.is_empty());
    run(bundle, session, inputs, RunLimits::default(), &mut NoHooks).unwrap()
}
fn evaluate(coefficients: &[Scalar], point: Scalar) -> Scalar {
    coefficients
        .iter()
        .rev()
        .fold(Scalar::from(0), |acc, coefficient| {
            acc * point + coefficient
        })
}
fn univariate(directory: &Path) {
    let bundle = bundle(directory, "univariate");
    let omega =
        zkc_arkworks::parse_decimal("3465144826073652318776269530687742778270252468765361963008")
            .unwrap();
    assert_eq!(omega * omega, -Scalar::from(1));
    let offset = Scalar::from(3);
    let points = [offset, offset * omega, -offset, -offset * omega];
    for seed in 0..17u64 {
        let mut a: Vec<_> = (0..4)
            .map(|i| Scalar::from((seed + 1) * i * i * i + 7 * i * i + seed + 1))
            .collect();
        let mut b: Vec<_> = (0..4)
            .map(|i| Scalar::from((seed + 3) * i * i + 5 * i + 2 * seed + 7))
            .collect();
        if seed == 16 {
            a[2..].fill(Scalar::from(0));
            b[2..].fill(Scalar::from(0));
        }
        let mut product = vec![Scalar::from(0); 7];
        for i in 0..4 {
            for j in 0..4 {
                product[i + j] += a[i] * b[j];
            }
        }
        // The coset is {3,3w,-3,-3w}. Its vanishing polynomial is X^4-81.
        // The degree<4 interpolant is independently the remainder modulo it.
        let mut remainder = product[..4].to_vec();
        for i in 0..3 {
            remainder[i] += Scalar::from(81) * product[i + 4];
        }
        let outside = Scalar::from(7);
        let report = execute(
            &bundle,
            &format!("univariate-{seed}"),
            BTreeMap::from([(
                "Solo".into(),
                vec![array(&a), array(&b), Value::Field(outside)],
            )]),
        );
        assert_eq!(report.outcome, Outcome::Completed);
        let outputs = &report.roles[0].outputs;
        assert_eq!(elements(&outputs[0]), product);
        assert_eq!(elements(&outputs[1]), remainder);
        let evaluations: Vec<_> = points
            .iter()
            .map(|point| evaluate(&a, *point) * evaluate(&b, *point))
            .collect();
        assert_eq!(elements(&outputs[2]), evaluations);
        assert_eq!(scalar(&outputs[3]), evaluate(&product, outside));
        assert_eq!(scalar(&outputs[4]), evaluate(&remainder, outside));
        if seed == 16 {
            assert_eq!(scalar(&outputs[3]), scalar(&outputs[4]));
        } else {
            assert_ne!(scalar(&outputs[3]), scalar(&outputs[4]));
        }
        for point in points {
            assert_eq!(evaluate(&product, point), evaluate(&remainder, point));
        }
    }
}
fn array_exchange(directory: &Path) {
    let bundle = bundle(directory, "array");
    let report = execute(
        &bundle,
        "array-exchange",
        BTreeMap::from([
            ("P".into(), vec![Value::Field(Scalar::from(17))]),
            ("V".into(), vec![]),
        ]),
    );
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.wire.sends, 1);
    assert_eq!(report.wire.receives, 1);
    assert_eq!(
        scalar(&report.roles.iter().find(|r| r.role == "V").unwrap().outputs[0]),
        Scalar::from(17)
    );
}

fn mle(table: &[Scalar], point: &[Scalar]) -> Scalar {
    // Independent basis definition, deliberately different from compiler folding.
    table
        .iter()
        .enumerate()
        .map(|(index, value)| {
            point
                .iter()
                .enumerate()
                .fold(*value, |term, (axis, coordinate)| {
                    term * if (index >> (point.len() - axis - 1)) & 1 == 1 {
                        *coordinate
                    } else {
                        Scalar::from(1) - coordinate
                    }
                })
        })
        .sum()
}
fn expression(t: &[Scalar], u: &[Scalar], point: &[Scalar]) -> Scalar {
    let a = mle(t, point);
    a * a + a * mle(u, point)
}
#[derive(Default)]
struct Wire {
    replacement: Option<(&'static str, Vec<u8>)>,
    messages: Vec<(String, Vec<u8>)>,
}
impl Hooks<NativeBackend> for Wire {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(self.messages.len() < 4);
        self.messages
            .push((exchange.site.to_string(), bytes.to_vec()));
        if self
            .replacement
            .as_ref()
            .is_some_and(|(site, _)| *site == exchange.site)
        {
            return Ok(self.replacement.take().map(|(_, bytes)| bytes));
        }
        Ok(None)
    }
}
fn terminal_after(
    reduction: &Report<NativeBackend>,
    terminal: &Bundle,
    connector: &[(usize, usize)],
) -> Option<Report<NativeBackend>> {
    if reduction.outcome != Outcome::Completed {
        return None;
    }
    let residual = &reduction
        .roles
        .iter()
        .find(|r| r.role == "V")
        .unwrap()
        .outputs;
    let ports = &terminal.roles()[0].entry.inputs;
    assert_eq!(ports.len(), residual.len());
    let mut inputs = vec![None; ports.len()];
    assert_eq!(connector.len(), ports.len());
    for &(output, input) in connector {
        assert!(inputs[input].is_none());
        assert_eq!(ports[input].1, residual[output].physical_type());
        inputs[input] = Some(residual[output].clone());
    }
    let values = inputs.into_iter().map(Option::unwrap).collect();
    Some(execute(
        terminal,
        "actual-residual",
        BTreeMap::from([("V".into(), values)]),
    ))
}
fn accepted(report: &Report<NativeBackend>) -> bool {
    assert_eq!(report.outcome, Outcome::Completed);
    matches!(report.roles[0].outputs.as_slice(), [Value::Bool(true)])
}
fn reduction_case(
    bundle: &Bundle,
    t: &[Scalar],
    u: &[Scalar],
    claim: Scalar,
    wire: &mut Wire,
    budget: u64,
) -> (Report<NativeBackend>, u64) {
    let values = BTreeMap::from([
        ("P".into(), vec![array(t), array(u), Value::Field(claim)]),
        ("V".into(), vec![array(t), array(u), Value::Field(claim)]),
    ]);
    run_reduction(bundle, values, wire, budget)
}
fn run_reduction(
    bundle: &Bundle,
    mut values: BTreeMap<String, Vec<Value>>,
    wire: &mut Wire,
    budget: u64,
) -> (Report<NativeBackend>, u64) {
    let registry = ServiceRegistry::new(Policy::default());
    let random = registry
        .issue_test_tape("V", budget, vec![Scalar::from(5), Scalar::from(7)])
        .unwrap();
    let inputs = bundle
        .roles()
        .iter()
        .map(|role| {
            let mut b = backend(&role.entry.role, "sumcheck", bundle.entry());
            if role.entry.role == "V" {
                b = b
                    .with_services(
                        registry.clone(),
                        BTreeMap::from([(role.entry.services[0].name.clone(), random.clone())]),
                    )
                    .unwrap();
            }
            RoleInput {
                role: role.entry.role.clone(),
                backend: b,
                values: values.remove(&role.entry.role).unwrap(),
            }
        })
        .collect();
    let report = run(bundle, "sumcheck", inputs, RunLimits::default(), wire).unwrap();
    let observation = registry.observe(&random).unwrap();
    assert!(!observation.leased);
    let count = observation.state.as_ref().unwrap().draw_count;
    (report, count)
}
// This client consumes the exact compiler-owned pair and connector. Hashes bind
// bytes across the two results; they do not authenticate a forged report.
fn pair_metadata(a: &serde_json::Value, b: &serde_json::Value) -> Option<Vec<(usize, usize)>> {
    if a["format"] != "zkc.checked-run/0" || b["format"] != "zkc.checked-run/0" {
        return None;
    }
    let left = &a["correspondence"];
    let right = &b["correspondence"];
    for key in [
        "source_sha256",
        "requirements_sha256",
        "bundles_sha256",
        "requirements",
        "post_check_passes",
    ] {
        if left[key] != right[key] {
            return None;
        }
    }
    for artifact in [a, b] {
        let bytes = artifact["bundle"].as_str()?;
        let digest = format!("{:x}", Sha256::digest(bytes.as_bytes()));
        let report = &artifact["correspondence"];
        let entry = report["entry"].as_str()?;
        if report["bundle_sha256"].as_str()? != digest
            || left["bundles_sha256"][entry].as_str()? != digest
        {
            return None;
        }
    }
    if left["entry"] != "reduction" || right["entry"] != "terminal" {
        return None;
    }
    let records = left["requirements"].as_array()?;
    if records.len() != 1
        || records[0]["verifier_role"] != "V"
        || records[0]["terminal_role"] != "V"
    {
        return None;
    }
    records[0]["connector"]
        .as_array()?
        .iter()
        .map(|pair| {
            Some((
                usize::try_from(pair[0].as_u64()?).ok()?,
                usize::try_from(pair[1].as_u64()?).ok()?,
            ))
        })
        .collect()
}
fn sumcheck(directory: &Path, suffix: &str) {
    let read = |entry: &str| -> serde_json::Value {
        serde_json::from_slice(
            &std::fs::read(directory.join(format!("{entry}{suffix}.checked.json"))).unwrap(),
        )
        .unwrap()
    };
    let a = read("reduction");
    let b = read("terminal");
    let connector = pair_metadata(&a, &b).expect("matching checked reduction and terminal");
    let mut changed = b.clone();
    changed["bundle"] = serde_json::Value::String(format!("{} ", b["bundle"].as_str().unwrap()));
    assert!(pair_metadata(&a, &changed).is_none());
    let mut changed = b.clone();
    changed["correspondence"]["requirements"][0]["connector"][0] = serde_json::json!([1, 0]);
    assert!(pair_metadata(&a, &changed).is_none());
    let admit = |value: &serde_json::Value| {
        Bundle::admit(
            value["bundle"].as_str().unwrap().as_bytes(),
            &backend("Solo", "admission", "main"),
            BundleLimits::default(),
        )
        .unwrap()
    };
    let reduction = admit(&a);
    let terminal = admit(&b);
    for seed in 0..16u64 {
        let t: Vec<_> = (0..4)
            .map(|i| Scalar::from((seed + 1) * i * i * i + 7 * i * i + seed + 1))
            .collect();
        let u: Vec<_> = (0..4)
            .map(|i| Scalar::from((seed + 3) * i * i + 5 * i + 2 * seed + 7))
            .collect();
        let claim: Scalar = t.iter().zip(&u).map(|(a, b)| a * a + a * b).sum();
        let mut wire = Wire::default();
        let (report, draws) = reduction_case(&reduction, &t, &u, claim, &mut wire, 2);
        assert_eq!(draws, 2);
        assert_eq!(report.outcome, Outcome::Completed);
        let delivered = &report.roles.iter().find(|r| r.role == "P").unwrap().outputs;
        assert_eq!(
            delivered.iter().map(scalar).collect::<Vec<_>>(),
            vec![Scalar::from(5), Scalar::from(7)]
        );
        assert_eq!(
            wire.messages
                .iter()
                .map(|(site, _)| site.as_str())
                .collect::<Vec<_>>(),
            ["round0", "challenge0", "round1", "challenge1"]
        );
        let residual = &report.roles.iter().find(|r| r.role == "V").unwrap().outputs;
        assert_eq!(elements(&residual[0]), t);
        assert_eq!(elements(&residual[1]), u);
        assert_eq!(scalar(&residual[2]), Scalar::from(5));
        assert_eq!(scalar(&residual[3]), Scalar::from(7));
        assert_eq!(
            scalar(&residual[4]),
            expression(&t, &u, &[Scalar::from(5), Scalar::from(7)])
        );
        // Inspect both actual coefficient messages against the basis definition.
        let codec = backend("V", "inspect", "reduction");
        let ty = array(&[Scalar::from(0); 3]).physical_type();
        for (round, message) in [0usize, 2].into_iter().enumerate() {
            let q = codec
                .decode_native_value(&ty, &wire.messages[message].1)
                .unwrap();
            for x in [0, 1, 2, 11] {
                let expected = if round == 0 {
                    expression(&t, &u, &[Scalar::from(x), Scalar::from(0)])
                        + expression(&t, &u, &[Scalar::from(x), Scalar::from(1)])
                } else {
                    expression(&t, &u, &[Scalar::from(5), Scalar::from(x)])
                };
                assert_eq!(evaluate(elements(&q), Scalar::from(x)), expected);
            }
        }
        assert!(accepted(
            &terminal_after(&report, &terminal, &connector).unwrap()
        ));
    }
    let t: Vec<_> = [1, 2, 3, 4].into_iter().map(Scalar::from).collect();
    let u: Vec<_> = [5, 6, 7, 8].into_iter().map(Scalar::from).collect();
    // The final delivered challenge belongs to P's actual view. Replacing it
    // does not change V's independently sampled residual point.
    let changed = backend("V", "mutation", "reduction")
        .encode_native_value(&Value::Field(Scalar::from(9)))
        .unwrap();
    let mut different_view = Wire {
        replacement: Some(("challenge1", changed)),
        ..Wire::default()
    };
    let (views, draws) = reduction_case(
        &reduction,
        &t,
        &u,
        Scalar::from(100),
        &mut different_view,
        2,
    );
    assert_eq!(draws, 2);
    assert_eq!(views.outcome, Outcome::Completed);
    let delivered = &views.roles.iter().find(|r| r.role == "P").unwrap().outputs;
    assert_eq!(scalar(&delivered[1]), Scalar::from(9));
    assert!(accepted(
        &terminal_after(&views, &terminal, &connector).unwrap()
    ));
    let mut wire = Wire::default();
    let (false_claim, draws) = reduction_case(&reduction, &t, &u, Scalar::from(101), &mut wire, 2);
    assert_eq!(draws, 0);
    assert!(terminal_after(&false_claim, &terminal, &connector).is_none());
    assert_eq!(wire.messages.len(), 1);
    let codec = backend("V", "mutation", "reduction");
    // q1 + X(X-1) passes its sum guard but changes the actual final scalar.
    let bad_round = array(&[Scalar::from(286), Scalar::from(47), Scalar::from(3)]);
    let mut wire = Wire {
        replacement: Some(("round1", codec.encode_native_value(&bad_round).unwrap())),
        ..Wire::default()
    };
    let (report, draws) = reduction_case(&reduction, &t, &u, Scalar::from(100), &mut wire, 2);
    assert_eq!(draws, 2);
    assert!(!accepted(
        &terminal_after(&report, &terminal, &connector).unwrap()
    ));
    let mut wire = Wire {
        replacement: Some(("round0", vec![0])),
        ..Wire::default()
    };
    let (malformed, draws) = reduction_case(&reduction, &t, &u, Scalar::from(100), &mut wire, 2);
    assert_eq!(draws, 0);
    assert!(terminal_after(&malformed, &terminal, &connector).is_none());
    let State::Stopped(stop) = &malformed
        .roles
        .iter()
        .find(|r| r.role == "V")
        .unwrap()
        .before
    else {
        panic!("decode stop");
    };
    assert_eq!(stop.cause, StopCause::Decode(DecodeReason::Length));
    let mut wire = Wire::default();
    let (exhausted, draws) = reduction_case(&reduction, &t, &u, Scalar::from(100), &mut wire, 1);
    // The managed service counts the attempted exhausted draw as well.
    assert_eq!(draws, 2);
    assert!(terminal_after(&exhausted, &terminal, &connector).is_none());
}

// Original, participant and terminal port orders are deliberately different.
fn permuted_handoff(directory: &Path) {
    let read = |entry: &str| -> serde_json::Value {
        serde_json::from_slice(
            &std::fs::read(directory.join(format!("{entry}_permuted.checked.json"))).unwrap(),
        )
        .unwrap()
    };
    let a = read("reduction");
    let b = read("terminal");
    let connector = pair_metadata(&a, &b).unwrap();
    assert_eq!(connector, [(4, 3), (2, 1), (3, 4), (1, 0), (0, 2)]);
    let admit = |value: &serde_json::Value| {
        Bundle::admit(
            value["bundle"].as_str().unwrap().as_bytes(),
            &backend("Solo", "admission", "main"),
            BundleLimits::default(),
        )
        .unwrap()
    };
    let reduction = admit(&a);
    let terminal = admit(&b);
    for seed in 1..=4u64 {
        let t: Vec<_> = [1, 4, 10, 30].map(|x| Scalar::from(x + seed)).into();
        let u: Vec<_> = [5, 3, 17, 23].map(|x| Scalar::from(x * seed)).into();
        let claim: Scalar = t.iter().zip(&u).map(|(a, b)| a * a + a * b).sum();
        let values = BTreeMap::from([
            (
                "P".into(),
                vec![
                    Value::Field(claim),
                    array(&t),
                    Value::Field(Scalar::from(99)),
                    array(&u),
                ],
            ),
            ("V".into(), vec![Value::Field(claim), array(&t), array(&u)]),
        ]);
        let (report, draws) = run_reduction(&reduction, values, &mut Wire::default(), 2);
        assert_eq!(draws, 2);
        assert_eq!(report.outcome, Outcome::Completed);
        let residual = &report.roles.iter().find(|r| r.role == "V").unwrap().outputs;
        assert_eq!(elements(&residual[4]), t);
        assert_eq!(elements(&residual[2]), u);
        assert_eq!(scalar(&residual[3]), Scalar::from(5));
        assert_eq!(scalar(&residual[1]), Scalar::from(7));
        assert_eq!(
            scalar(&residual[0]),
            expression(&t, &u, &[Scalar::from(5), Scalar::from(7)])
        );
        assert!(accepted(
            &terminal_after(&report, &terminal, &connector).unwrap()
        ));
        // A complete, same-typed connector with the subjects swapped is false.
        let mut wrong = connector.clone();
        wrong[0].0 = 2;
        wrong[1].0 = 4;
        assert!(!accepted(
            &terminal_after(&report, &terminal, &wrong).unwrap()
        ));
    }
}

fn fixing(directory: &Path) {
    let bundles: Vec<_> = ["fixing", "fixing_plain", "fixing_competitor"]
        .iter()
        .map(|name| bundle(directory, name))
        .collect();
    for seed in 0..16u64 {
        let t: Vec<_> = (0..8)
            .map(|i| Scalar::from((seed + 1) * i * i * i + 7 * i * i + seed + 1))
            .collect();
        let u: Vec<_> = (0..8)
            .map(|i| Scalar::from((seed + 3) * i * i + 5 * i + 3 * seed + 7))
            .collect();
        let prefix = [Scalar::from(seed % 5), Scalar::from((seed + 1) % 7)];
        let points = [Scalar::from(seed + 7), Scalar::from(seed + 11)];
        for bundle in &bundles {
            let mut values = vec![array(&t), array(&u)];
            values.extend(prefix.into_iter().chain(points).map(Value::Field));
            let report = execute(
                bundle,
                "shared-prefix",
                BTreeMap::from([("Solo".into(), values)]),
            );
            assert_eq!(report.outcome, Outcome::Completed);
            let outputs = &report.roles[0].outputs;
            for (index, point) in points.into_iter().enumerate() {
                assert_eq!(
                    scalar(&outputs[index]),
                    expression(&t, &u, &[prefix[0], prefix[1], point])
                );
            }
            assert_eq!(elements(&outputs[2]).len(), 3);
            for point in [Scalar::from(0), Scalar::from(1), Scalar::from(17)] {
                assert_eq!(
                    evaluate(elements(&outputs[2]), point),
                    expression(&t, &u, &[prefix[0], prefix[1], point])
                );
            }
        }
    }
}

fn main() {
    let directory = std::env::args().nth(1).expect("generated bundle directory");
    let directory = Path::new(&directory);
    array_exchange(directory);
    univariate(directory);
    fixing(directory);
    permuted_handoff(directory);
    for suffix in ["", "_plain", "_release", "_factored"] {
        sumcheck(directory, suffix);
    }
    println!(
        "structured mathematics: array exchange, 17 univariate/coset cases, 68 checked Sumcheck handoffs (4 with permuted ports), 48 shared-prefix executions, and stopping/adversarial controls passed"
    );
}
