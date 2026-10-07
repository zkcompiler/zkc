//! Execute fresh compiler bundles with real arithmetic, codecs and managed roots.
//! This is an executable integration client: expectations come from each source
//! protocol and its arithmetic, independently of the generated dispatch plan.
use std::{collections::BTreeMap, path::Path};
use zkc_backends::services::{ServiceObservation, ServiceReference, ServiceRegistry};
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{CutKind, DecodeReason};
use zkc_tools::protocol::run::*;

fn backend(role: &str, session: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, session, entry, None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
fn bundle(directory: &Path, name: &str) -> Bundle {
    let bytes = std::fs::read(directory.join(format!("{name}.bundle"))).unwrap();
    Bundle::admit(
        &bytes,
        &backend("Alice", "admission", "main"),
        BundleLimits::default(),
    )
    .unwrap()
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
        assert!(self.messages.len() < 4);
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
    assert!(bundle.admitted().checked_source().is_none());
    assert!(audit.after.values().flatten().all(|o| !o.leased));
    report
}
fn role<'a>(report: &'a Report<NativeBackend>, name: &str) -> &'a RoleReport<Value> {
    report.roles.iter().find(|r| r.role == name).unwrap()
}
fn acceptance(report: &Report<NativeBackend>, name: &str, index: usize) -> bool {
    // This host-selected role/result coordinate is not inferred by the driver.
    let Value::Bool(value) = role(report, name).outputs[index] else {
        panic!("Boolean acceptance")
    };
    value
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
fn schnorr_inputs() -> Inputs {
    let g = GroupPoint::generator();
    let y = g.scale(Scalar::from(3));
    BTreeMap::from([
        (
            "Alice".into(),
            vec![Value::Curve(g), field(3), Value::Curve(y)],
        ),
        ("Bob".into(), vec![Value::Curve(g), Value::Curve(y)]),
    ])
}
fn schnorr(directory: &Path) {
    for variant in [
        "schnorr",
        "schnorr_plain",
        "schnorr_release",
        "schnorr_plain_release",
    ] {
        let b = bundle(directory, variant);
        let registry = ServiceRegistry::new(Policy::default());
        let nonce = tape(&registry, "Alice", 1, &[5]);
        let challenge = tape(&registry, "Bob", 1, &[11]);
        let mut audit = Audit::new(
            &registry,
            BTreeMap::from([
                ("Alice".into(), vec![nonce]),
                ("Bob".into(), vec![challenge]),
            ]),
        );
        let report = run_case(&b, variant, schnorr_inputs(), &mut audit);
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(acceptance(&report, "Bob", 0));
        assert_eq!(
            audit
                .messages
                .iter()
                .map(|(s, _)| s.as_str())
                .collect::<Vec<_>>(),
            ["commitment", "challenge", "response"]
        );
        let codec = backend("Alice", "codec", "main");
        // Independent group equation: z=5+11*3=38 and g*z = g*5 + (g*3)*11.
        let g = GroupPoint::generator();
        let z = Scalar::from(38);
        assert_eq!(
            g.scale(z),
            g.scale(Scalar::from(5))
                .add(&g.scale(Scalar::from(3)).scale(Scalar::from(11)))
        );
        for ((_, actual), expected) in audit.messages.iter().zip([
            Value::Curve(g.scale(Scalar::from(5))),
            field(11),
            field(38),
        ]) {
            assert_eq!(*actual, codec.encode_native_value(&expected).unwrap());
        }
        draws(&audit.before["Alice"][0], 1, 0, false, false);
        draws(&audit.before["Bob"][0], 1, 0, false, false);
    }
    let b = bundle(directory, "schnorr");
    let codec = backend("Alice", "codec", "main");
    for (site, value) in [
        (
            "commitment",
            Value::Curve(GroupPoint::generator().scale(Scalar::from(6))),
        ),
        ("challenge", field(12)),
        ("response", field(39)),
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let mut audit = Audit::new(
            &registry,
            BTreeMap::from([
                ("Alice".into(), vec![tape(&registry, "Alice", 1, &[5])]),
                ("Bob".into(), vec![tape(&registry, "Bob", 1, &[11])]),
            ]),
        );
        audit.replacement = Some((site.into(), codec.encode_native_value(&value).unwrap()));
        let report = run_case(&b, site, schnorr_inputs(), &mut audit);
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(!acceptance(&report, "Bob", 0));
        assert_eq!(report.wire.sends, 3);
        assert_eq!(report.wire.receives, 3);
    }
    let registry = ServiceRegistry::new(Policy::default());
    let mut audit = Audit::new(
        &registry,
        BTreeMap::from([
            ("Alice".into(), vec![tape(&registry, "Alice", 1, &[5])]),
            ("Bob".into(), vec![tape(&registry, "Bob", 1, &[11])]),
        ]),
    );
    audit.replacement = Some(("response".into(), vec![0]));
    let report = run_case(&b, "malformed", schnorr_inputs(), &mut audit);
    assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
    let State::Stopped(stop) = &role(&report, "Bob").before else {
        panic!("receive stop")
    };
    assert_eq!(stop.cause, StopCause::Decode(DecodeReason::Length));
    assert_eq!(stop.site.as_deref(), Some("response"));
    assert!(report.pending.is_none());
    assert_eq!(report.wire.sends, 3);
    // The production sampler is a smoke case, not a distribution/security claim.
    let registry = ServiceRegistry::new(Policy::default());
    let mut audit = Audit::new(
        &registry,
        BTreeMap::from([
            (
                "Alice".into(),
                vec![registry.issue_random("Alice", 1).unwrap()],
            ),
            ("Bob".into(), vec![registry.issue_random("Bob", 1).unwrap()]),
        ]),
    );
    let report = run_case(&b, "random", schnorr_inputs(), &mut audit);
    assert_eq!(report.outcome, Outcome::Completed);
    assert!(acceptance(&report, "Bob", 0));
    draws(&audit.after["Alice"][0], 1, 0, false, false);
    draws(&audit.after["Bob"][0], 1, 0, false, false);
    // A root owned by Alice cannot also bind Bob's entry. The first lease is
    // observed before host cancellation and released before custody returns.
    let registry = ServiceRegistry::new(Policy::default());
    let shared = tape(&registry, "Alice", 2, &[5, 11]);
    let mut audit = Audit::new(
        &registry,
        BTreeMap::from([
            ("Alice".into(), vec![shared.clone()]),
            ("Bob".into(), vec![shared]),
        ]),
    );
    let report = run_case(&b, "cross_role", schnorr_inputs(), &mut audit);
    assert!(matches!(
        report.outcome,
        Outcome::DriverFailed(Failure {
            kind: FailureKind::Setup,
            ..
        })
    ));
    assert_eq!(report.backends.len(), 2);
    assert!(report.reached.is_empty());
    draws(&audit.before["Alice"][0], 0, 2, false, true);
    draws(&audit.after["Alice"][0], 0, 2, false, false);
}
fn foreign_inputs(go: bool) -> Inputs {
    BTreeMap::from([
        ("Alice".into(), vec![field(3)]),
        ("Bob".into(), vec![Value::Bool(go), Value::Bool(false)]),
        ("Observer".into(), vec![Value::Bool(false)]),
    ])
}
fn service_inputs() -> Inputs {
    BTreeMap::from([
        ("Alice".into(), vec![field(3), Value::Bool(true)]),
        ("Bob".into(), vec![Value::Bool(false)]),
        ("Observer".into(), vec![Value::Bool(false)]),
    ])
}
fn services(directory: &Path) {
    for name in [
        "foreign",
        "foreign_plain",
        "foreign_release",
        "foreign_plain_release",
    ] {
        let b = bundle(directory, name);
        let registry = ServiceRegistry::new(Policy::default());
        let shared = tape(&registry, "Alice", 4, &[5, 11, 17, 23]);
        let mut audit = Audit::new(
            &registry,
            BTreeMap::from([("Alice".into(), vec![shared.clone(), shared])]),
        );
        let report = run_case(&b, name, foreign_inputs(false), &mut audit);
        assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
        assert!(audit.messages.is_empty());
        assert_eq!(report.reached.len(), 2);
        assert_eq!(report.reached[0].step.anchor, Some(0));
        assert_eq!(report.reached[1].step.anchor, Some(1));
        let State::Stopped(stop) = &role(&report, "Bob").before else {
            panic!("guard stop")
        };
        assert_eq!(stop.site.as_deref(), Some("foreign_guard"));
        assert!(matches!(&stop.cause,StopCause::Explicit(e) if e.text=="reject"));
        assert!(
            matches!(&role(&report,"Alice").before,State::Unpolled {kind:Some(CutKind::Query),site:Some(s)} if s=="second_draw")
        );
        assert_eq!(
            role(&report, "Observer").before,
            State::Unpolled {
                kind: None,
                site: None
            }
        );
        for o in &audit.before["Alice"] {
            draws(o, 1, 3, false, true);
        }
        for o in &audit.after["Alice"] {
            draws(o, 1, 3, false, false);
        }
    }
    // A coherent supplied reorder is deliberately admitted; it is the concrete
    // counterexample to treating candidate consistency as source correspondence.
    let mut raw: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory.join("foreign.bundle")).unwrap()).unwrap();
    raw["steps"].as_array_mut().unwrap().swap(1, 2);
    raw["steps"][1]["anchor"] = 1.into();
    raw["steps"][2]["anchor"] = 2.into();
    let b = Bundle::admit(
        raw.to_string().as_bytes(),
        &backend("Alice", "admission", "main"),
        BundleLimits::default(),
    )
    .unwrap();
    let registry = ServiceRegistry::new(Policy::default());
    let shared = tape(&registry, "Alice", 4, &[5, 11, 17, 23]);
    let mut audit = Audit::new(
        &registry,
        BTreeMap::from([("Alice".into(), vec![shared.clone(), shared])]),
    );
    let report = run_case(&b, "readiness_mutation", foreign_inputs(false), &mut audit);
    assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
    draws(&audit.before["Alice"][0], 2, 2, false, true);
    for (name, alias) in [("deferred", true), ("services", true), ("services", false)] {
        let b = bundle(directory, name);
        let registry = ServiceRegistry::new(Policy::default());
        let first = tape(&registry, "Alice", 4, &[5, 11, 17, 23]);
        let second = if alias {
            first.clone()
        } else {
            tape(&registry, "Alice", 2, &[11, 29])
        };
        let mut audit = Audit::new(
            &registry,
            BTreeMap::from([("Alice".into(), vec![first, second])]),
        );
        let values = if name == "deferred" {
            foreign_inputs(false)
        } else {
            service_inputs()
        };
        let report = run_case(&b, name, values, &mut audit);
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(!acceptance(&report, "Bob", 1));
        assert!(matches!(role(&report,"Bob").outputs[0],Value::Field(v) if v==Scalar::from(22)));
        let count = if name == "deferred" { 2 } else { 3 };
        if alias {
            for o in &audit.after["Alice"] {
                draws(o, count, 4 - count, false, false);
            }
        } else {
            draws(&audit.after["Alice"][0], 2, 2, false, false);
            draws(&audit.after["Alice"][1], 1, 1, false, false);
        }
        assert!(report.roles.iter().all(|r| !r.cancelled));
    }
    let b = bundle(directory, "deferred");
    let registry = ServiceRegistry::new(Policy::default());
    let shared = tape(&registry, "Alice", 1, &[5]);
    let mut audit = Audit::new(
        &registry,
        BTreeMap::from([("Alice".into(), vec![shared.clone(), shared])]),
    );
    let report = run_case(&b, "poison", foreign_inputs(false), &mut audit);
    assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 0 });
    let State::Stopped(stop) = &role(&report, "Alice").before else {
        panic!("query stop")
    };
    assert_eq!(stop.site.as_deref(), Some("second_draw"));
    assert!(audit.messages.is_empty());
    for o in &audit.before["Alice"] {
        draws(o, 2, 0, true, false);
    }
    assert_eq!(audit.before["Alice"], audit.after["Alice"]);
}
fn inverse_and_empty(directory: &Path) {
    for name in [
        "inverse",
        "inverse_plain",
        "inverse_release",
        "inverse_plain_release",
        "collision",
    ] {
        for reply in [0, 2] {
            let b = bundle(directory, name);
            let registry = ServiceRegistry::new(Policy::default());
            let mut audit = Audit::new(&registry, BTreeMap::new());
            let report = run_case(
                &b,
                "inverse",
                BTreeMap::from([
                    ("P".into(), vec![field(7), Value::Bool(true)]),
                    ("V".into(), vec![field(reply)]),
                ]),
                &mut audit,
            );
            assert_eq!(
                audit
                    .messages
                    .iter()
                    .map(|(s, _)| s.as_str())
                    .collect::<Vec<_>>(),
                ["send", "reply"]
            );
            assert_eq!(report.wire.sends, 2);
            assert_eq!(report.wire.receives, 2);
            if reply == 0 {
                assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 0 });
                let State::Stopped(stop) = &role(&report, "P").before else {
                    panic!("inverse stop")
                };
                assert_eq!(
                    stop.site.as_deref(),
                    Some(if name == "collision" {
                        "calculation_0"
                    } else {
                        "inverse"
                    })
                );
                assert_eq!(
                    role(&report, "V").before,
                    State::Unpolled {
                        kind: None,
                        site: None
                    }
                );
                assert!(role(&report, "V").cancelled);
            } else {
                assert_eq!(report.outcome, Outcome::Completed);
                assert!(
                    matches!(role(&report,"P").outputs[0],Value::Field(v) if v==Scalar::from(1))
                );
            }
        }
    }
    for name in ["single", "empty"] {
        let b = bundle(directory, name);
        let registry = ServiceRegistry::new(Policy::default());
        let mut audit = Audit::new(&registry, BTreeMap::new());
        let values = if name == "single" {
            vec![Value::Bool(false)]
        } else {
            vec![]
        };
        let report = run_case(
            &b,
            "no_messages",
            BTreeMap::from([("Solo".into(), values)]),
            &mut audit,
        );
        assert_eq!(report.outcome, Outcome::Completed);
        assert!(audit.messages.is_empty());
        if name == "single" {
            assert!(!acceptance(&report, "Solo", 0));
        } else {
            assert!(role(&report, "Solo").outputs.is_empty());
        }
    }
}
fn realized_mathematics(directory: &Path) {
    for name in ["realized", "realized_plain", "realized_release"] {
        let b = bundle(directory, name);
        for (a, coefficient, x) in [(2_u64, 3_u64, 5_u64), (7, 0, 11), (0, 4, 0)] {
            let registry = ServiceRegistry::new(Policy::default());
            let mut audit = Audit::new(&registry, BTreeMap::new());
            let report = run_case(
                &b,
                "realized_polynomial",
                BTreeMap::from([("P".into(), vec![field(a), field(coefficient), field(x)])]),
                &mut audit,
            );
            assert_eq!(report.outcome, Outcome::Completed);
            assert!(audit.messages.is_empty());
            let expected = Scalar::from((a + coefficient * x).pow(2));
            assert!(
                matches!(role(&report, "P").outputs[0], Value::Field(value) if value == expected)
            );
        }
    }
}
fn main() {
    let path = std::env::args_os()
        .nth(1)
        .expect("directory of freshly generated native bundles");
    let directory = Path::new(&path);
    schnorr(directory);
    services(directory);
    inverse_and_empty(directory);
    realized_mathematics(directory);
    println!(
        "native joint Schnorr, source order, message controls, managed aliases, cleanup and inverse checks passed"
    );
}
