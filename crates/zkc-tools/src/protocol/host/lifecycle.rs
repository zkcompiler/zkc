//! Failure injection around the real source host's preparation and cleanup.
use super::*;
use std::{cell::Cell, rc::Rc};
use zkc_runtime::interactive::{Backend, Frame, FrameExit, Invocation, PhysicalType};
#[derive(Default)]
struct Counters {
    issued: Cell<usize>,
    entered: Cell<usize>,
    retired: Cell<usize>,
}
struct Controlled {
    inner: NativeBackend,
    counts: Rc<Counters>,
    fail_issue: bool,
    fail_enter: bool,
    fail_observe: bool,
    fail_encode: bool,
}
impl Backend for Controlled {
    type Value = Value;
    fn validate_value(&self, v: &Value) -> std::result::Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, v: &[Value]) -> std::result::Result<(), BackendError> {
        self.counts.entered.set(self.counts.entered.get() + 1);
        if self.fail_enter {
            return Err(BackendError::new("injected-entry"));
        }
        self.inner.enter_frame(f, v)
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        e: FrameExit,
        v: &[Value],
    ) -> std::result::Result<(), BackendError> {
        self.inner.leave_frame(f, e, v)
    }
    fn apply(
        &mut self,
        i: &Invocation<'_>,
        v: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        self.inner.apply(i, v)
    }
}
impl WireBackend for Controlled {
    fn encode(&self, v: &Value) -> std::result::Result<Vec<u8>, BackendError> {
        if self.fail_encode {
            Err(BackendError::new("injected-output"))
        } else {
            self.inner.encode(v)
        }
    }
    fn decode(&self, t: PhysicalType, b: &[u8]) -> std::result::Result<Value, BackendError> {
        self.inner.decode(t, b)
    }
}
impl HostBackend for Controlled {
    fn external_work_spent(&self) -> u64 {
        self.inner.external_work_spent()
    }
    fn live_resource_units(&self) -> usize {
        self.inner.live_resource_units()
    }
    fn issue(&mut self, input: ResourceInput, d: Domain) -> Result<Value> {
        if self.fail_issue {
            return Err("injected-issue".into());
        }
        let value = HostBackend::issue(&mut self.inner, input, d)?;
        self.counts.issued.set(self.counts.issued.get() + 1);
        Ok(value)
    }
    fn prepare(
        &self,
        r: &EntryRole,
        b: &[u8],
        t: &BTreeMap<String, PhysicalType>,
    ) -> Result<zkc_backends::InputPlan> {
        HostBackend::prepare(&self.inner, r, b, t)
    }
    fn check_entry(
        &self,
        p: &zkc_backends::InputPlan,
        r: &EntryRole,
        b: &InputBindings,
    ) -> Result<()> {
        p.check_entry(&self.inner, r, b).map_err(|e| e.to_string())
    }
    fn retire(
        &mut self,
        c: &Capability,
    ) -> std::result::Result<CapabilityObservation, BackendError> {
        self.counts.retired.set(self.counts.retired.get() + 1);
        self.inner.retire(c)
    }
    fn observe(&self, c: &Capability) -> std::result::Result<CapabilityObservation, BackendError> {
        if self.fail_observe {
            Err(BackendError::new("injected-observation"))
        } else {
            self.inner.observe(c)
        }
    }
}
fn backend(role: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "host-tests", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
#[test]
fn source_host_prepares_all_roles_and_retains_partial_issuance_and_diagnostics() {
    use std::process::Command;
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("host.pir");
    std::fs::write(&path,r#"
use zkc::random::Rng;
use zkc::poly::Point;
protocol Host {
 roles (P,V);
 inputs (P r: Rng<"bls12-381.fr">, P x: Point<"bls12-381.fr">, V s: Rng<"bls12-381.fr">, V y: Point<"bls12-381.fr">);
 outputs (P Rng<"bls12-381.fr">, P Point<"bls12-381.fr">, V Rng<"bls12-381.fr">, V Point<"bls12-381.fr">);
 return (r,x,s,y);
}
instance root: Host { roles (P=P,V=V); }
entry main=root;
"#).unwrap();
    let compile = |mode| {
        let output = Command::new(zkc_test_support::compiler())
            .arg(mode)
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    };
    let source = compile("protocol-source");
    let candidate = compile("protocol-compile");
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let admitted = admit_physical(&source, &candidate, &backend("P"), &checker).unwrap();
    for mode in [
        "bad-input",
        "bad-entry",
        "issue",
        "load-P",
        "load-V",
        "diagnostics",
        "ok",
    ] {
        let mut input = json!([
            "zkc.run/2",
            "main",
            "host-tests",
            [],
            [
                [
                    "P",
                    [["rng", "entropy", "2", "entry"]],
                    [["r", ["host", "entropy"]], ["x", ["point", ["3"]]]],
                    []
                ],
                [
                    "V",
                    [["rng", "entropy", "2", "entry"]],
                    [["s", ["host", "entropy"]], ["y", ["point", ["4"]]]],
                    []
                ]
            ],
            []
        ]);
        if mode == "bad-input" {
            input[4][1][2][1][1][1] = json!(["bad"]);
        }
        let cfg = config(&input).unwrap();
        let declarations = inputs::declarations(&admitted, &cfg, &BTreeMap::new()).unwrap();
        let counts = Rc::new(Counters::default());
        let report = execute(
            &admitted,
            &cfg,
            &BTreeMap::new(),
            (0., 0.),
            declarations,
            |r| {
                Ok(Controlled {
                    inner: if mode == "bad-entry" && r.role == "V" {
                        NativeBackend::new(
                            Policy::default(),
                            EntryPolicy::new(
                                Domain::new(&r.role, "host-tests", "main", None),
                                None,
                                PublicInputs::LocalOnly,
                            )
                            .with_ports(BTreeMap::from([(
                                r.inputs[1].0.clone(),
                                zkc_backends::PortConstraint {
                                    arity: Some(2),
                                    setup: None,
                                },
                            )])),
                            None,
                        )
                        .unwrap()
                    } else {
                        backend(&r.role)
                    },
                    counts: counts.clone(),
                    fail_issue: mode == "issue" && r.role == "V",
                    fail_enter: mode.strip_prefix("load-") == Some(r.role.as_str()),
                    fail_observe: mode == "diagnostics",
                    fail_encode: mode == "diagnostics",
                })
            },
            &super::super::BackendDecoder,
        );
        if matches!(mode, "bad-input" | "bad-entry") {
            assert!(report.is_err());
            assert_eq!(counts.issued.get(), 0);
            assert_eq!(counts.entered.get(), 0);
            continue;
        }
        let report = report.unwrap();
        if mode == "issue" {
            assert_eq!(report["phase"], "issuance");
            assert_eq!(report["outcome"], json!(["failed", "injected-issue"]));
            assert_eq!(counts.entered.get(), 0);
            assert_eq!(counts.issued.get(), 1);
            assert_eq!(report["usage"].as_object().unwrap().len(), 2);
        } else if let Some(role) = mode.strip_prefix("load-") {
            assert_eq!(report["phase"], "construction");
            assert_eq!(report["status"], "setup-failed");
            assert_eq!(report["roles"][role]["started"], false);
            assert_eq!(report["usage"][role]["instructions"], 0);
            assert!(
                report["outcome"][1]
                    .as_str()
                    .unwrap()
                    .contains("injected-entry")
            );
            assert_eq!(counts.entered.get(), if role == "P" { 1 } else { 2 });
            assert_eq!(counts.issued.get(), 2);
            assert_eq!(
                report["cancelled_roles"],
                if role == "V" { json!(["P"]) } else { json!([]) }
            );
        } else {
            assert_eq!(report["outcome"][0], "returned");
            assert_eq!(counts.entered.get(), 2);
        }
        assert_eq!(counts.issued.get(), counts.retired.get());
        assert_eq!(
            report["retired_resources"].as_array().unwrap().len(),
            counts.issued.get()
        );
        if mode == "diagnostics" {
            assert!(
                report["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|r| r["kind"] == "observation")
            );
            assert!(
                report["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|r| r["kind"] == "output")
            );
        } else {
            assert!(report["diagnostics"].as_array().unwrap().is_empty());
        }
    }
}

#[test]
fn source_resource_declarations_preserve_kind_field_and_retirement() {
    use std::process::Command;
    use zkc_runtime::interactive::Value as RuntimeValue;
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("resources.pir");
    std::fs::write(
        &path,
        r#"
use zkc::random::{Rng, Nonce};
protocol Resources {
 roles(P);
 inputs(P a: Rng<"bls12-381.fr">, P b: Nonce<"bls12-381.fr">,
        P c: Rng<"ristretto255.scalar">, P d: Nonce<"ristretto255.scalar">);
 outputs(P Rng<"bls12-381.fr">, P Nonce<"bls12-381.fr">,
         P Rng<"ristretto255.scalar">, P Nonce<"ristretto255.scalar">);
 return(a,b,c,d);
}
instance root: Resources { roles(P=P); }
entry main=root;
"#,
    )
    .unwrap();
    let compile = |mode| {
        let output = Command::new(zkc_test_support::compiler())
            .arg(mode)
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    };
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let admitted = admit_physical(
        &compile("protocol-source"),
        &compile("protocol-compile"),
        &backend("P"),
        &checker,
    )
    .unwrap();
    let input = json!([
        "zkc.run/2",
        "main",
        "host-tests",
        [],
        [[
            "P",
            [
                ["rng", "a", "2", "entry"],
                ["nonce", "b", "2", "entry"],
                ["rng:ristretto255.scalar", "c", "2", "entry"],
                ["nonce:ristretto255.scalar", "d", "2", "entry"]
            ],
            [
                ["a", ["host", "a"]],
                ["b", ["host", "b"]],
                ["c", ["host", "c"]],
                ["d", ["host", "d"]]
            ],
            []
        ]],
        []
    ]);
    let cfg = config(&input).unwrap();
    let declarations = inputs::declarations(&admitted, &cfg, &BTreeMap::new()).unwrap();
    let mut prepared = inputs::prepare(declarations.roles, &BTreeMap::new(), |role| {
        Ok(backend(&role.role))
    })
    .unwrap();
    inputs::issue(&mut prepared).unwrap();
    let role = &mut prepared[0];
    let expected = [
        "rng:bls12-381.fr",
        "nonce:bls12-381.fr",
        "rng:ristretto255.scalar",
        "nonce:ristretto255.scalar",
    ];
    assert_eq!(
        role.values
            .iter()
            .map(|v| v.physical_type().logical().spelling())
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(role.handles.len(), 4);
    let backend = role.backend.as_mut().unwrap();
    for (_, root) in &role.handles {
        let observed = backend.retire(root).unwrap();
        assert_eq!(
            (observed.generation, observed.draw_count, observed.budget),
            (0, 0, 2)
        );
        assert!(backend.observe(root).is_err());
    }
}
