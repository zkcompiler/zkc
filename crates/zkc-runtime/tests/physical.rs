mod support;
use serde_json::{Value as Json, json};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use support::entry;
use zkc_runtime::{
    AdmittedJob, AdmittedProgram, Bindings, Budget, CheckFailure, CheckRequest, Checker, Error,
    Library, Outcome, PhaseEvidence, Realization, Resources, Stop,
    arena::Arena,
    buffer::{BufferStore, BufferUsage, PackedBuffers, SegmentedBuffers},
    table::{
        ChallengeProvider, Domain, ENDPOINT_PROFILE, FieldKernel, Phase, PhysicalOperation,
        PhysicalTableBindings, PhysicalTableLibrary, SmallPrimeKernel, State, TableBindings,
        TapeProvider, Type, Value,
    },
};

// Explicit fixture authorization for native unit tests only. This does not
// implement a preservation checker. Live Lean checking is exercised by the
// physical differential harness and the tools' optional installed-checker test.
struct FixtureChecker {
    source: Vec<u8>,
    candidate: Vec<u8>,
    phase: Option<PhaseEvidence>,
    calls: AtomicUsize,
}
impl Checker for FixtureChecker {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        assert_eq!(request.realization, Realization::TablePhysicalPlan);
        if request.phase != self.phase.as_ref() {
            return Err(CheckFailure::NotEstablished("phase-not-admitted".into()));
        }
        if request.source == self.source && request.candidate == self.candidate {
            Ok(())
        } else {
            Err(CheckFailure::NotEstablished(
                "physical-source-mismatch".into(),
            ))
        }
    }
}
impl FixtureChecker {
    fn with_policy(mut self, role: &str, phase: Option<PhaseEvidence>) -> Self {
        let mut source: Json = serde_json::from_slice(&self.source).unwrap();
        let mut candidate: Json = serde_json::from_slice(&self.candidate).unwrap();
        source[3][0] = json!(role);
        candidate[2][0] = json!(role);
        self.source = source.to_string().into_bytes();
        self.candidate = candidate.to_string().into_bytes();
        self.phase = phase;
        self
    }
}
fn fixture(
    source_body: Json,
    body: Json,
    declarations: Json,
    result: Json,
    grammar: &str,
) -> FixtureChecker {
    let context = json!(["trace", declarations, result, [["table-protocol", "1"]]]);
    FixtureChecker {
        source: json!(["zkc-request", 1, grammar, context, [], source_body])
            .to_string()
            .into_bytes(),
        candidate: json!(["zkc-table-physical-plan", 1, context, body])
            .to_string()
            .into_bytes(),
        phase: None,
        calls: AtomicUsize::new(0),
    }
}
fn admit(f: &FixtureChecker) -> Arc<AdmittedProgram<PhysicalOperation>> {
    AdmittedProgram::admit_physical(f.source.clone(), f.candidate.clone(), f.phase.clone(), f)
        .unwrap_or_else(|e| panic!("{}", e.reason))
}
fn decl(name: &str, ty: Json) -> Json {
    json!([name, ty, ["shared"], "capture"])
}
fn base<S: BufferStore<u8>>(storage: S) -> TableBindings<SmallPrimeKernel, TapeProvider, S> {
    TableBindings::with_storage(
        SmallPrimeKernel,
        TapeProvider::new(vec![3, 6]).unwrap(),
        State {
            two: 0,
            seven: 0,
            writes: 0u8.into(),
            sent: vec![],
        },
        storage,
    )
    .unwrap()
}
fn bindings<S: BufferStore<u8>>(
    storage: S,
) -> PhysicalTableBindings<SmallPrimeKernel, TapeProvider, S> {
    PhysicalTableBindings::new(base(storage)).unwrap()
}
fn run<S: BufferStore<u8>>(f: &FixtureChecker, inputs: Json, storage: S) -> Json {
    let job = AdmittedJob::bind(admit(f), inputs, bindings(storage))
        .unwrap_or_else(|e| panic!("{}", e.reason));
    let session = job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason));
    let (out, mut b) = session.execute().into_parts();
    let outcome = match out.unwrap() {
        Outcome::Returned(v) => json!(["returned", b.value_json(&v).unwrap()]),
        Outcome::Stopped(s) => json!(["stopped", s.name()]),
    };
    json!({"execution":{"status":"executed","outcome":outcome,"state":b.state_json(),"events":b.events()},
        "scalar-cells":b.scalar_cells(),"table-evaluations":b.table_evaluations()})
}
fn both(f: &FixtureChecker, inputs: Json) -> Json {
    let packed = run(f, inputs.clone(), PackedBuffers::new().unwrap());
    let segmented = run(f, inputs, SegmentedBuffers::new().unwrap());
    assert_eq!(packed, segmented);
    packed
}

#[test]
fn stopped_results_do_not_reserve_hypothetical_final_scalar_reads() {
    let ty = json!(["scalar", "f7"]);
    for body in [
        json!(["stop", "reject"]),
        json!(["bind", ty, ["stop", "reject"], ["return", 0]]),
    ] {
        let f = fixture(body.clone(), body, json!([]), ty.clone(), "region-source-1");
        let job = AdmittedJob::bind(
            admit(&f),
            json!([]),
            bindings(PackedBuffers::new().unwrap()),
        )
        .unwrap_or_else(|e| panic!("{}", e.reason));
        let session = job
            .reserve(Budget {
                steps: 8,
                ..Budget::default()
            })
            .unwrap_or_else(|e| panic!("{}", e.reason));
        let (outcome, b) = session.execute().into_parts();
        assert!(matches!(outcome, Ok(Outcome::Stopped(Stop::Reject))));
        assert_eq!(b.table_evaluations(), 0);
        assert_eq!(b.scalar_cells(), 0);
    }
}

fn simple(mode: &str, rank: usize, tail: Json) -> (FixtureChecker, Json) {
    let scalar = json!(["scalar", "f7"]);
    let residual = json!(["residual", "f7", rank]);
    let point = json!(["point", "f7"]);
    let f = fixture(
        json!(["apply", ["evaluate", "f7", rank], [0, 1], ["return", 0]]),
        json!([
            "apply",
            ["prepare", mode, "f7", rank],
            [0, 1],
            ["return", 0]
        ]),
        json!([decl("r", residual.clone()), decl("p", point.clone())]),
        scalar,
        "finite-source-1",
    );
    let cells = (0..(1usize << rank)).map(|i| i % 7).collect::<Vec<_>>();
    (
        f,
        json!([["r", residual, [9, cells, []]], ["p", point, tail]]),
    )
}
#[test]
fn returned_reference_decodes_with_reserved_completion_scratch_in_both_layouts() {
    for mode in ["lazy", "materialized"] {
        let (f, inputs) = simple(mode, 2, json!([1, 1]));
        let out = both(&f, inputs);
        assert_eq!(out["execution"]["outcome"], json!(["returned", 3]));
        assert_eq!(out["scalar-cells"], 1);
        assert_eq!(out["table-evaluations"], 1);
        assert_eq!(
            admit(&f).retained_bytes(),
            (f.source.as_slice(), f.candidate.as_slice())
        );
    }
}
#[test]
fn mixed_sites_preserve_old_scalars_and_count_every_demand() {
    let r = json!(["residual", "f7", 1]);
    let p = json!(["point", "f7"]);
    let declarations = json!([
        decl("r", r.clone()),
        decl("p0", p.clone()),
        decl("p1", p.clone())
    ]);
    for first in ["lazy", "materialized", "eager"] {
        for second in ["lazy", "materialized", "eager"] {
            let source = json!([
                "apply",
                ["evaluate", "f7", 1],
                [0, 1],
                [
                    "apply",
                    ["evaluate", "f7", 1],
                    [1, 3],
                    [
                        "apply",
                        ["add", "f7"],
                        [1, 0],
                        ["apply", ["add", "f7"], [2, 0], ["return", 0]]
                    ]
                ]
            ]);
            let choice = |m: &str| {
                if m == "eager" {
                    json!(["invoke", ["evaluate", "f7", 1]])
                } else {
                    json!(["prepare", m, "f7", 1])
                }
            };
            let body = json!([
                "apply",
                choice(first),
                [0, 1],
                [
                    "apply",
                    choice(second),
                    [1, 3],
                    [
                        "apply",
                        ["invoke", ["add", "f7"]],
                        [1, 0],
                        ["apply", ["invoke", ["add", "f7"]], [2, 0], ["return", 0]]
                    ]
                ]
            ]);
            let f = fixture(
                source,
                body,
                declarations.clone(),
                json!(["scalar", "f7"]),
                "finite-source-1",
            );
            let out = both(
                &f,
                json!([["r", r, [7, [2, 5], []]], ["p0", p, [0]], ["p1", p, [1]]]),
            );
            assert_eq!(out["execution"]["outcome"], json!(["returned", 2]));
            assert_eq!(
                out["table-evaluations"],
                if first == "lazy" { 3 } else { 2 }
            );
            assert_eq!(
                out["scalar-cells"],
                usize::from(first != "eager") + usize::from(second != "eager")
            );
        }
    }
}
#[test]
fn unused_preparation_keeps_its_guard_and_actual_failed_prefix() {
    let r = json!(["residual", "f7", 1]);
    let p = json!(["point", "f7"]);
    for mode in ["lazy", "materialized"] {
        for tail in [json!([]), json!([1])] {
            let source = json!([
                "apply",
                ["draw"],
                [],
                [
                    "apply",
                    ["record", "f7"],
                    [0],
                    ["apply", ["evaluate", "f7", 1], [2, 3], ["stop", "reject"]]
                ]
            ]);
            let body = json!([
                "apply",
                ["invoke", ["draw"]],
                [],
                [
                    "apply",
                    ["invoke", ["record", "f7"]],
                    [0],
                    [
                        "apply",
                        ["prepare", mode, "f7", 1],
                        [2, 3],
                        ["stop", "reject"]
                    ]
                ]
            ]);
            let f = fixture(
                source,
                body,
                json!([decl("r", r.clone()), decl("p", p.clone())]),
                json!(["bool"]),
                "finite-source-1",
            );
            let valid = tail == json!([1]);
            let out = both(&f, json!([["r", r, [9, [2, 5], []]], ["p", p, tail]]));
            assert_eq!(
                out["execution"]["outcome"],
                json!(["stopped", if valid { "reject" } else { "refused" }])
            );
            assert_eq!(
                out["execution"]["events"],
                json!([["drawn", 3], ["write", "f7", 3]])
            );
            assert_eq!(out["execution"]["state"], json!([0, 3, 1, [], [6]]));
            assert_eq!(out["scalar-cells"], usize::from(valid));
            assert_eq!(
                out["table-evaluations"],
                usize::from(valid && mode == "materialized")
            );
        }
    }
}
#[test]
fn stopped_invoke_counts_lazy_read_and_preserves_write_effect() {
    let (mut f, inputs) = simple("lazy", 1, json!([1]));
    let mut source: Json = serde_json::from_slice(&f.source).unwrap();
    let mut candidate: Json = serde_json::from_slice(&f.candidate).unwrap();
    source[3][2] = json!(["bool"]);
    candidate[2][2] = json!(["bool"]);
    source[5][3] = json!(["apply", ["abort_write", "f7"], [0], ["stop", "reject"]]);
    candidate[3][3] = json!([
        "apply",
        ["invoke", ["abort_write", "f7"]],
        [0],
        ["stop", "reject"]
    ]);
    f.source = source.to_string().into_bytes();
    f.candidate = candidate.to_string().into_bytes();
    let out = both(&f, inputs.clone());
    assert_eq!(out["execution"]["outcome"], json!(["stopped", "abort"]));
    assert_eq!(out["execution"]["events"], json!([["write", "f7", 1]]));
    assert_eq!(out["execution"]["state"], json!([0, 1, 1, [], [3, 6]]));
    assert_eq!(out["table-evaluations"], 1);
    let f = f.with_policy("prover", Some(endpoint_evidence(Phase::Sent)));
    let done = execute(
        &f,
        inputs,
        endpoint(PackedBuffers::new().unwrap(), Phase::Sent),
    );
    assert!(matches!(done.outcome(), Ok(Outcome::Stopped(Stop::Abort))));
    assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Sent)));
    assert_eq!(
        done.bindings().state_json(),
        json!(["prover", "sent", [0, 1, 1, [], [3, 6]]])
    );
    assert_eq!(done.bindings().events(), &[json!(["write", "f7", 1])]);
}
#[test]
fn structured_join_and_allocating_loop_preserve_captured_aliases() {
    let r = json!(["residual", "f7", 2]);
    let p = json!(["point", "f7"]);
    let s = json!(["scalar", "f7"]);
    let declarations = json!([
        decl("r", r.clone()),
        decl("p", p.clone()),
        decl("yes", json!(["bool"]))
    ]);
    // Bind captures a scalar from a branch; repeat allocates a fresh scalar on
    // each iteration; suffix still reads the captured original scalar twice.
    let branch = |physical: bool| {
        json!([
            "if",
            2,
            [
                "apply",
                if physical {
                    json!(["prepare", "lazy", "f7", 2])
                } else {
                    json!(["evaluate", "f7", 2])
                },
                [0, 1],
                ["return", 0]
            ],
            [
                "apply",
                if physical {
                    json!(["prepare", "materialized", "f7", 2])
                } else {
                    json!(["evaluate", "f7", 2])
                },
                [0, 1],
                ["return", 0]
            ]
        ])
    };
    let body = |physical: bool| {
        json!([
            "bind",
            s,
            branch(physical),
            [
                "repeat",
                3,
                s,
                0,
                [
                    "apply",
                    if physical {
                        json!(["prepare", "materialized", "f7", 2])
                    } else {
                        json!(["evaluate", "f7", 2])
                    },
                    [2, 3],
                    ["return", 0]
                ],
                [
                    "apply",
                    if physical {
                        json!(["invoke", ["add", "f7"]])
                    } else {
                        json!(["add", "f7"])
                    },
                    [0, 1],
                    [
                        "apply",
                        if physical {
                            json!(["invoke", ["add", "f7"]])
                        } else {
                            json!(["add", "f7"])
                        },
                        [0, 2],
                        ["return", 0]
                    ]
                ]
            ]
        ])
    };
    let f = fixture(body(false), body(true), declarations, s, "region-source-1");
    for yes in [true, false] {
        let out = both(
            &f,
            json!([
                ["r", r, [0, [1, 2, 3, 4], []]],
                ["p", p, [1, 1]],
                ["yes", ["bool"], yes]
            ]),
        );
        assert_eq!(out["execution"]["outcome"], json!(["returned", 5]));
        assert_eq!(out["scalar-cells"], 4);
        assert_eq!(out["table-evaluations"], if yes { 5 } else { 4 });
    }
}
#[test]
fn admission_independently_checks_both_interpretations_context_and_policy() {
    let (f, _) = simple("lazy", 1, json!([1]));
    let source: Json = serde_json::from_slice(&f.source).unwrap();
    let candidate: Json = serde_json::from_slice(&f.candidate).unwrap();
    let mut cases = vec![];
    let mut s = source.clone();
    s[5][1] = json!(["prepare", "lazy", "f7", 1]);
    cases.push((s, candidate.clone(), "unknown-operation"));
    let mut p = candidate.clone();
    p[3][1] = json!(["evaluate", "f7", 1]);
    cases.push((source.clone(), p, "unknown-physical-operation"));
    let mut p = candidate.clone();
    p[3][2] = json!([1, 0]);
    cases.push((source.clone(), p, "invalid-operand"));
    let mut p = candidate.clone();
    p[2][0] = json!("other");
    cases.push((source.clone(), p, "context-mismatch"));
    let mut p = candidate.clone();
    p[0] = json!("zkc-table-physical-reference");
    cases.push((source.clone(), p, "invalid-shape"));
    // Two inputs sharing a name: the contexts agree, and neither is valid.
    let mut s = source.clone();
    s[3][1][1][0] = json!("r");
    let mut p = candidate.clone();
    p[2] = s[3].clone();
    cases.push((s, p, "invalid-context"));
    let mut p = candidate.clone();
    p[3][1][1] = json!("cache");
    cases.push((source.clone(), p, "unsupported-preparation-mode"));
    let mut s = source.clone();
    let mut p = candidate.clone();
    s[3][3] = json!([["table-protocol", "2"]]);
    p[2][3] = s[3][3].clone();
    cases.push((s, p, "unresolved-dependency"));
    for (s, p, code) in cases {
        for phase in [None, Some(trace_evidence())] {
            let failure = AdmittedProgram::admit_physical(
                s.to_string().into_bytes(),
                p.to_string().into_bytes(),
                phase,
                &f,
            )
            .err()
            .unwrap();
            assert_eq!(failure.reason, Error(code));
        }
    }
    assert_eq!(f.calls.load(Ordering::Relaxed), 0);
    let mut p = candidate;
    p[3][3] = json!(["stop", "reject"]);
    let failure =
        AdmittedProgram::admit_physical(f.source.clone(), p.to_string().into_bytes(), None, &f)
            .err()
            .unwrap();
    assert_eq!(
        failure.checking,
        Some(CheckFailure::NotEstablished(
            "physical-source-mismatch".into()
        ))
    );
    assert_eq!(f.calls.load(Ordering::Relaxed), 1);
}
#[test]
fn input_values_are_bound_separately_and_cannot_inject_reference_handles() {
    let (f, inputs) = simple("lazy", 1, json!([1]));
    let program = admit(&f);
    for (actual, expected) in [
        (json!([]), "input-count"),
        (
            {
                let mut v = inputs.clone();
                v[0][0] = json!("substitute");
                v
            },
            "wrong-input-name",
        ),
        (
            {
                let mut v = inputs.clone();
                v[0][1] = json!(["residual", "f2", 1]);
                v
            },
            "wrong-input-type",
        ),
    ] {
        assert_eq!(
            AdmittedJob::bind(
                program.clone(),
                actual,
                bindings(PackedBuffers::new().unwrap())
            )
            .err()
            .unwrap()
            .reason,
            Error(expected)
        );
    }
    let f = fixture(
        json!(["return", 0]),
        json!(["return", 0]),
        json!([decl("s", json!(["scalar", "f7"]))]),
        json!(["scalar", "f7"]),
        "finite-source-1",
    );
    for value in [json!(["reference", 0]), json!({"handle":0}), json!(7)] {
        assert!(
            AdmittedJob::bind(
                admit(&f),
                json!([["s", ["scalar", "f7"], value]]),
                bindings(PackedBuffers::new().unwrap())
            )
            .is_err()
        );
    }
    assert_eq!(
        both(&f, json!([["s", ["scalar", "f7"], 2]]))["execution"]["outcome"],
        json!(["returned", 2])
    );
    assert_eq!(
        both(&f, json!([["s", ["scalar", "f7"], 5]]))["execution"]["outcome"],
        json!(["returned", 5])
    );
}

fn aliases<S: BufferStore<u8>>(store: S) {
    let mut b = bindings(store);
    let residual_ty = Type::Residual(Domain::Seven, 1u8.into()).sort();
    let point_ty = Type::Point(Domain::Seven).sort();
    let residual = b.input(&residual_ty, &json!([4, [2, 5], []])).unwrap();
    let zero = b.input(&point_ty, &json!([0])).unwrap();
    let one = b.input(&point_ty, &json!([1])).unwrap();
    b.reserve(
        Resources {
            steps: 1000,
            values: 20,
            bytes: 1000,
            scratch: 2,
            arguments: 3,
            ..Resources::default()
        },
        &Budget::default(),
    )
    .unwrap();
    b.begin_execution();
    let mut refs = vec![];
    for mode in ["lazy", "materialized"] {
        let op = PhysicalTableLibrary
            .operation(&json!(["prepare", mode, "f7", 1]))
            .unwrap();
        for point in [&zero, &one] {
            let Outcome::Returned(value) =
                b.invoke(&op, &[residual.clone(), point.clone()]).unwrap()
            else {
                panic!()
            };
            refs.push(value);
        }
    }
    for (i, value) in refs.iter().enumerate() {
        assert_eq!(b.value_json(value).unwrap(), if i % 2 == 0 { 2 } else { 5 });
        let Value::ScalarReference(_, handle) = value else {
            panic!()
        };
        for other in &refs[..i] {
            if let Value::ScalarReference(_, other) = other {
                assert_ne!(handle, other);
            }
        }
    }
    assert_eq!(b.value_json(&residual).unwrap(), json!([4, [2, 5], []]));
    let Value::ScalarReference(_, h) = refs[0] else {
        panic!()
    };
    assert_eq!(
        b.value_json(&Value::ScalarReference(Domain::Two, h)),
        Err(Error("scalar-domain-mismatch"))
    );
    let mut foreign = Arena::new().unwrap();
    foreign.reserve(1).unwrap();
    let foreign = foreign.publish(0).unwrap();
    assert_eq!(
        b.value_json(&Value::ScalarReference(Domain::Seven, foreign)),
        Err(Error("foreign-handle"))
    );
    let Value::Residual(h) = residual else {
        panic!()
    };
    assert_eq!(
        b.value_json(&Value::ScalarReference(Domain::Seven, h)),
        Err(Error("handle-kind-mismatch"))
    );
    let other = bindings(PackedBuffers::new().unwrap());
    assert_eq!(
        other.validate(&Type::Scalar(Domain::Seven).sort(), &refs[0]),
        Err(Error("foreign-handle"))
    );
    // Failed reads do not overwrite a represented alias.
    assert_eq!(b.value_json(&refs[0]).unwrap(), 2);
}
#[test]
fn fresh_aliases_validate_issuer_domain_and_object_kind() {
    aliases(PackedBuffers::new().unwrap());
    aliases(SegmentedBuffers::new().unwrap());
}
#[test]
fn returned_lazy_reads_and_loop_allocations_are_included_in_preflight() {
    let (f, inputs) = simple("lazy", 2, json!([1, 1]));
    let job = AdmittedJob::bind(admit(&f), inputs, bindings(PackedBuffers::new().unwrap()))
        .unwrap_or_else(|e| panic!("{}", e.reason));
    let state = job.bindings().state_json();
    let failure = job
        .reserve(Budget {
            steps: 12,
            ..Budget::default()
        })
        .err()
        .unwrap();
    assert_eq!(failure.reason, Error("capacity-limit"));
    assert_eq!(failure.job.bindings().state_json(), state);
    assert_eq!(failure.job.bindings().scalar_cells(), 0);
    assert!(failure.job.bindings().events().is_empty());
    let (f, inputs) = simple("materialized", 1, json!([1]));
    let job = AdmittedJob::bind(
        admit(&f),
        inputs,
        bindings(SegmentedBuffers::new().unwrap()),
    )
    .unwrap_or_else(|e| panic!("{}", e.reason));
    assert_eq!(
        job.reserve(Budget {
            bytes: 1,
            ..Budget::default()
        })
        .err()
        .unwrap()
        .reason,
        Error("capacity-limit")
    );
    let s = json!(["scalar", "f7"]);
    for count in [
        json!(100_001),
        Json::Number("184467440737095516160".parse().unwrap()),
    ] {
        let body = json!(["repeat", count, s, 0, ["return", 0], ["return", 0]]);
        let f = fixture(
            body.clone(),
            body,
            json!([decl("s", s.clone())]),
            s.clone(),
            "region-source-1",
        );
        let job = AdmittedJob::bind(
            admit(&f),
            json!([["s", s, 0]]),
            bindings(PackedBuffers::new().unwrap()),
        )
        .unwrap_or_else(|e| panic!("{}", e.reason));
        assert_eq!(
            job.reserve(Budget::default()).err().unwrap().reason,
            Error("capacity-limit")
        );
    }
}
#[test]
fn dormant_physical_bodies_still_validate_native_rank_limits() {
    let scalar = json!(["scalar", "f7"]);
    // The zero-iteration body cannot execute, but its unsupported native
    // intermediate rank must still be checked by preflight.
    let body = json!([
        "repeat",
        0,
        scalar,
        0,
        [
            "bind",
            ["residual", "f7", 13],
            ["stop", "reject"],
            ["return", 1]
        ],
        ["return", 0]
    ]);
    let f = fixture(
        body.clone(),
        body,
        json!([decl("s", scalar.clone())]),
        scalar.clone(),
        "region-source-1",
    );
    let job = AdmittedJob::bind(
        admit(&f),
        json!([["s", scalar, 2]]),
        bindings(PackedBuffers::new().unwrap()),
    )
    .unwrap_or_else(|e| panic!("{}", e.reason));
    assert_eq!(
        job.reserve(Budget::default()).err().unwrap().reason,
        Error("input-rank-limit")
    );
}

struct FailingReserve {
    inner: PackedBuffers<u8>,
    fail: Arc<std::sync::atomic::AtomicBool>,
    calls: Arc<AtomicUsize>,
}
impl BufferStore<u8> for FailingReserve {
    type Reference = <PackedBuffers<u8> as BufferStore<u8>>::Reference;
    fn required_bytes(&self, e: usize, b: usize) -> Result<usize, Error> {
        self.inner.required_bytes(e, b)
    }
    fn reserve(&mut self, e: usize, b: usize) -> Result<(), Error> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        if self.fail.load(Ordering::Relaxed) {
            return Err(Error("reservation-failed"));
        }
        self.inner.reserve(e, b)
    }
    fn publish(&mut self, v: &[u8]) -> Result<Self::Reference, Error> {
        self.inner.publish(v)
    }
    fn read(&self, r: &Self::Reference) -> Result<&[u8], Error> {
        self.inner.read(r)
    }
    fn usage(&self) -> BufferUsage {
        self.inner.usage()
    }
}
#[test]
fn allocation_failure_is_start_failure_and_execution_never_reserves_storage() {
    let (f, inputs) = simple("materialized", 1, json!([1]));
    let fail = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let store = FailingReserve {
        inner: PackedBuffers::new().unwrap(),
        fail: fail.clone(),
        calls: calls.clone(),
    };
    let job = AdmittedJob::bind(admit(&f), inputs, bindings(store))
        .unwrap_or_else(|e| panic!("{}", e.reason));
    fail.store(true, Ordering::Relaxed);
    let failure = job.reserve(Budget::default()).err().unwrap();
    assert_eq!(failure.reason, Error("reservation-failed"));
    assert_eq!(
        failure.job.bindings().state_json(),
        json!([0, 0, 0, [], [3, 6]])
    );
    assert_eq!(failure.job.bindings().scalar_cells(), 0);
    fail.store(false, Ordering::Relaxed);
    let session = failure
        .job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason));
    let reserved = calls.load(Ordering::Relaxed);
    fail.store(true, Ordering::Relaxed);
    let (out, mut b) = session.execute().into_parts();
    let Outcome::Returned(value) = out.unwrap() else {
        panic!()
    };
    assert_eq!(b.value_json(&value).unwrap(), 1);
    assert_eq!(calls.load(Ordering::Relaxed), reserved);
    assert_eq!(b.scalar_cells(), 1);
}
#[test]
fn reentry_keeps_provider_position_and_prior_stopped_state() {
    let source = json!([
        "apply",
        ["draw"],
        [],
        ["apply", ["abort_write", "f7"], [0], ["return", 0]]
    ]);
    let body = json!([
        "apply",
        ["invoke", ["draw"]],
        [],
        [
            "apply",
            ["invoke", ["abort_write", "f7"]],
            [0],
            ["return", 0]
        ]
    ]);
    let f = fixture(source, body, json!([]), json!(["bool"]), "finite-source-1");
    let program = admit(&f);
    let mut b = bindings(PackedBuffers::new().unwrap());
    for (expected, remaining) in [(3, json!([6])), (6, json!([]))] {
        let job = AdmittedJob::bind(program.clone(), json!([]), b)
            .unwrap_or_else(|e| panic!("{}", e.reason));
        let (out, next) = job
            .reserve(Budget::default())
            .unwrap_or_else(|e| panic!("{}", e.reason))
            .execute()
            .into_parts();
        assert!(matches!(out, Ok(Outcome::Stopped(Stop::Abort))));
        assert_eq!(next.state_json()[1], expected);
        assert_eq!(next.state_json()[4], remaining);
        assert_eq!(
            next.events(),
            &[json!(["drawn", expected]), json!(["write", "f7", expected])]
        );
        b = next;
    }
    let job = AdmittedJob::bind(program, json!([]), b).unwrap_or_else(|e| panic!("{}", e.reason));
    let done = job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert!(matches!(
        done.outcome(),
        Ok(Outcome::Stopped(Stop::Exhausted))
    ));
    assert_eq!(done.bindings().state_json(), json!([0, 6, 2, [], []]));
    assert!(done.bindings().events().is_empty());
}

#[test]
fn deferred_output_kernel_failure_is_an_explicit_host_error_with_live_owner() {
    struct Panics;
    impl zkc_runtime::table::FieldKernel for Panics {
        fn add(&self, _: Domain, _: u8, _: u8) -> u8 {
            panic!("test kernel")
        }
        fn sub(&self, _: Domain, _: u8, _: u8) -> u8 {
            panic!("test kernel")
        }
        fn mul(&self, _: Domain, _: u8, _: u8) -> u8 {
            panic!("test kernel")
        }
    }
    let (state, provider) = State::decode(&json!([0, 0, 0, [], [3, 6]])).unwrap();
    let b =
        PhysicalTableBindings::new(TableBindings::new(Panics, provider, state).unwrap()).unwrap();
    let (f, inputs) = simple("lazy", 1, json!([1]));
    let job = AdmittedJob::bind(admit(&f), inputs, b).unwrap_or_else(|e| panic!("{}", e.reason));
    let (out, mut b) = job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute()
        .into_parts();
    let Outcome::Returned(value) = out.unwrap() else {
        panic!()
    };
    assert_eq!(b.value_json(&value), Err(Error("backend-panic")));
    assert_eq!(b.state_json(), json!([0, 0, 0, [], [3, 6]]));
    assert_eq!(b.scalar_cells(), 1);
}

fn trace_evidence() -> PhaseEvidence {
    PhaseEvidence {
        profile: "table-round/1".into(),
        certificate: br#"["terminal"]"#.to_vec(),
        entry: None,
    }
}
fn endpoint_evidence(phase: Phase) -> PhaseEvidence {
    PhaseEvidence {
        profile: ENDPOINT_PROFILE.into(),
        entry: Some(entry(phase)),
        ..trace_evidence()
    }
}
fn endpoint<S: BufferStore<u8>>(
    storage: S,
    phase: Phase,
) -> PhysicalTableBindings<SmallPrimeKernel, TapeProvider, S> {
    PhysicalTableBindings::new(base(storage).with_endpoint("prover".into(), phase).unwrap())
        .unwrap()
}
fn execute<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>>(
    f: &FixtureChecker,
    inputs: Json,
    b: PhysicalTableBindings<K, P, S>,
) -> zkc_runtime::Completed<PhysicalTableBindings<K, P, S>> {
    AdmittedJob::bind(admit(f), inputs, b)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute()
}
fn round(mode: &str) -> (FixtureChecker, Json) {
    let (mut f, inputs) = simple(mode, 1, json!([1]));
    let mut source: Json = serde_json::from_slice(&f.source).unwrap();
    let mut candidate: Json = serde_json::from_slice(&f.candidate).unwrap();
    source[5][3] = json!([
        "apply",
        ["send"],
        [0, 0],
        ["apply", ["draw"], [], ["return", 2]]
    ]);
    candidate[3][3] = json!([
        "apply",
        ["invoke", ["send"]],
        [0, 0],
        ["apply", ["invoke", ["draw"]], [], ["return", 2]]
    ]);
    f.source = source.to_string().into_bytes();
    f.candidate = candidate.to_string().into_bytes();
    (f, inputs)
}
fn scalar_fixture(source: Json, body: Json, phase: Option<PhaseEvidence>) -> FixtureChecker {
    fixture(
        source,
        body,
        json!([]),
        json!(["scalar", "f7"]),
        "finite-source-1",
    )
    .with_policy("prover", phase)
}

fn phase_rounds<S: BufferStore<u8>>(storage: S, mode: &str) {
    let (f, inputs) = round(mode);
    let f = f.with_policy("prover", Some(endpoint_evidence(Phase::Ready)));
    let done = execute(&f, inputs.clone(), endpoint(storage, Phase::Ready));
    let (out, mut b) = done.into_parts();
    let Outcome::Returned(alias) = out.unwrap() else {
        panic!()
    };
    assert_eq!(b.endpoint_entry(), Some(entry(Phase::Ready)));
    assert_eq!(b.value_json(&alias).unwrap(), 1);
    assert_eq!(b.table_evaluations(), if mode == "lazy" { 3 } else { 1 });
    assert_eq!(b.events(), &[json!(["sent", 1, 1]), json!(["drawn", 3])]);
    // Same admission may be reused at the same actual entry. Previous cells and
    // their dependencies remain live across reservation and execution.
    let (out, mut b) = execute(&f, inputs, b).into_parts();
    assert!(matches!(out, Ok(Outcome::Returned(_))));
    assert_eq!(b.scalar_cells(), 2);
    assert_eq!(b.value_json(&alias).unwrap(), 1);
    assert_eq!(
        b.state_json(),
        json!(["prover", "ready", [0, 0, 0, [[1, 1], [1, 1]], []]])
    );
    assert_eq!(b.events(), &[json!(["sent", 1, 1]), json!(["drawn", 6])]);
}
#[test]
fn balanced_phase_trace_and_endpoint_preserve_owned_scalars_in_both_layouts() {
    for mode in ["lazy", "materialized"] {
        let (f, inputs) = round(mode);
        let f = f.with_policy("trace", Some(trace_evidence()));
        let report = both(&f, inputs);
        assert_eq!(report["execution"]["outcome"], json!(["returned", 1]));
        assert_eq!(
            report["execution"]["events"],
            json!([["sent", 1, 1], ["drawn", 3]])
        );
        phase_rounds(PackedBuffers::new().unwrap(), mode);
        phase_rounds(SegmentedBuffers::new().unwrap(), mode);
    }
}
#[test]
fn physical_admission_retains_exact_policy_and_rejects_missing_or_changed_evidence() {
    let (f, _) = round("lazy");
    let f = f.with_policy("trace", Some(trace_evidence()));
    let p = admit(&f);
    assert_eq!(
        p.retained_bytes(),
        (f.source.as_slice(), f.candidate.as_slice())
    );
    assert_eq!(p.phase_evidence(), f.phase.as_ref());
    let mut wrong_profile = trace_evidence();
    wrong_profile.profile = "another-policy/1".into();
    let mut wrong_certificate = trace_evidence();
    wrong_certificate.certificate = b"[]".to_vec();
    for evidence in [None, Some(wrong_profile), Some(wrong_certificate)] {
        let failure = AdmittedProgram::admit_physical(
            f.source.clone(),
            f.candidate.clone(),
            evidence.clone(),
            &f,
        )
        .err()
        .unwrap();
        assert_eq!(failure.reason, Error("phase-not-admitted"));
        assert_eq!(
            failure.checking,
            Some(CheckFailure::NotEstablished("phase-not-admitted".into()))
        );
        assert_eq!(failure.phase, evidence);
        assert_eq!(failure.source, f.source);
        assert_eq!(failure.candidate, f.candidate);
    }
    for (evidence, code) in [
        (
            PhaseEvidence {
                profile: String::new(),
                ..trace_evidence()
            },
            "invalid-phase-profile",
        ),
        (
            PhaseEvidence {
                certificate: b"[".to_vec(),
                ..trace_evidence()
            },
            "invalid-json",
        ),
        (endpoint_evidence(Phase::Ready), "endpoint-role-mismatch"),
    ] {
        let before = f.calls.load(Ordering::Relaxed);
        let failure = AdmittedProgram::admit_physical(
            f.source.clone(),
            f.candidate.clone(),
            Some(evidence),
            &f,
        )
        .err()
        .unwrap();
        assert_eq!(failure.reason, Error(code));
        assert_eq!(f.calls.load(Ordering::Relaxed), before);
    }
}
#[test]
fn physical_entry_checks_precede_inputs_and_preserve_policy_custody() {
    let p = scalar_fixture(
        json!(["stop", "abort"]),
        json!(["stop", "abort"]),
        Some(endpoint_evidence(Phase::Ready)),
    );
    for (phase, code) in [
        (Phase::Sent, "endpoint-entry-mismatch"),
        (Phase::Unknown, "unknown-endpoint-state"),
    ] {
        let b = endpoint(PackedBuffers::new().unwrap(), phase);
        let state = b.state_json();
        let failure = AdmittedJob::bind(admit(&p), json!("invalid inputs"), b)
            .err()
            .unwrap();
        assert_eq!(failure.reason, Error(code));
        assert_eq!(failure.bindings.state_json(), state);
        assert_eq!(failure.bindings.buffer_usage().elements, 0);
    }
    let failure = AdmittedJob::bind(
        admit(&p),
        json!([]),
        bindings(PackedBuffers::new().unwrap()),
    )
    .err()
    .unwrap();
    assert_eq!(failure.reason, Error("unsupported-endpoint-binding"));
    for (evidence, code) in [
        (None, "endpoint-evidence-required"),
        (Some(trace_evidence()), "endpoint-policy-mismatch"),
        (
            Some(PhaseEvidence {
                entry: None,
                ..endpoint_evidence(Phase::Ready)
            }),
            "endpoint-evidence-required",
        ),
    ] {
        let f = scalar_fixture(json!(["stop", "abort"]), json!(["stop", "abort"]), evidence);
        let failure = AdmittedJob::bind(
            admit(&f),
            json!([]),
            endpoint(PackedBuffers::new().unwrap(), Phase::Ready),
        )
        .err()
        .unwrap();
        assert_eq!(failure.reason, Error(code));
    }
    let foreign = PhysicalTableBindings::new(
        base(PackedBuffers::new().unwrap())
            .with_endpoint("verifier".into(), Phase::Ready)
            .unwrap(),
    )
    .unwrap();
    assert_eq!(
        foreign.validate_entry("prover", p.phase.as_ref()),
        Err(Error("endpoint-role-mismatch"))
    );
    assert_eq!(
        endpoint(PackedBuffers::new().unwrap(), Phase::Ready)
            .validate_entry("verifier", p.phase.as_ref()),
        Err(Error("endpoint-role-mismatch"))
    );
}
#[test]
/// `PhysicalTableBindings::validate_entry` delegates straight to the logical
/// bindings, whose state machine endpoint.rs checks assertion for assertion.
/// What this adds is that the physical wrapper preserves the delegation
/// through an admitted plan, and accounts its cells while doing so.
fn stopped_physical_endpoint_requires_readmission_from_retained_phase() {
    let (mut f, inputs) = round("lazy");
    let mut s: Json = serde_json::from_slice(&f.source).unwrap();
    let mut p: Json = serde_json::from_slice(&f.candidate).unwrap();
    s[5][3][3] = json!(["stop", "abort"]);
    p[3][3][3] = json!(["stop", "abort"]);
    f.source = s.to_string().into_bytes();
    f.candidate = p.to_string().into_bytes();
    let f = f.with_policy("prover", Some(endpoint_evidence(Phase::Ready)));
    let (out, b) = execute(
        &f,
        inputs.clone(),
        endpoint(PackedBuffers::new().unwrap(), Phase::Ready),
    )
    .into_parts();
    assert!(matches!(out, Ok(Outcome::Stopped(Stop::Abort))));
    assert_eq!(b.endpoint_entry(), Some(entry(Phase::Sent)));
    let state = b.state_json();
    let failure = AdmittedJob::bind(admit(&f), inputs, b).err().unwrap();
    assert_eq!(failure.reason, Error("endpoint-entry-mismatch"));
    assert_eq!(failure.bindings.state_json(), state);
    assert_eq!(failure.bindings.events(), &[json!(["sent", 1, 1])]);
    let no_policy = scalar_fixture(json!(["stop", "abort"]), json!(["stop", "abort"]), None);
    let failure = AdmittedJob::bind(admit(&no_policy), json!([]), failure.bindings)
        .err()
        .unwrap();
    assert_eq!(failure.reason, Error("endpoint-evidence-required"));
    let draw = scalar_fixture(
        json!(["apply", ["draw"], [], ["return", 0]]),
        json!(["apply", ["invoke", ["draw"]], [], ["return", 0]]),
        Some(endpoint_evidence(Phase::Sent)),
    );
    let (out, b) = execute(&draw, json!([]), failure.bindings).into_parts();
    assert!(matches!(out, Ok(Outcome::Returned(_))));
    assert_eq!(
        b.state_json(),
        json!(["prover", "ready", [0, 0, 0, [[1, 1]], [6]]])
    );
    assert_eq!(b.events(), &[json!(["drawn", 3])]);
    assert_eq!(b.scalar_cells(), 1);
}
#[test]
fn preparation_from_sent_entry_finishes_ready_or_retains_stopped_phase() {
    for mode in ["lazy", "materialized"] {
        let (mut f, inputs) = simple(mode, 1, json!([1]));
        let mut source: Json = serde_json::from_slice(&f.source).unwrap();
        let mut candidate: Json = serde_json::from_slice(&f.candidate).unwrap();
        // A real endpoint may prepare while sent, but cannot normally return
        // until its draw completes. The fixture must obey that same contract.
        source[5][3] = json!(["apply", ["draw"], [], ["return", 1]]);
        candidate[3][3] = json!(["apply", ["invoke", ["draw"]], [], ["return", 1]]);
        f.source = source.to_string().into_bytes();
        f.candidate = candidate.to_string().into_bytes();
        let evidence = PhaseEvidence {
            certificate: br#"["next",["next",["terminal"]]]"#.to_vec(),
            ..endpoint_evidence(Phase::Sent)
        };
        let f = f.with_policy("prover", Some(evidence));
        let (out, mut b) = execute(
            &f,
            inputs.clone(),
            endpoint(PackedBuffers::new().unwrap(), Phase::Sent),
        )
        .into_parts();
        let Outcome::Returned(alias) = out.unwrap() else {
            panic!()
        };
        assert_eq!(b.endpoint_entry(), Some(entry(Phase::Ready)));
        assert_eq!(b.value_json(&alias).unwrap(), 1);
        assert_eq!(b.endpoint_entry(), Some(entry(Phase::Ready)));
        assert_eq!(b.events(), &[json!(["drawn", 3])]);
        let (state, provider) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
        let empty = PhysicalTableBindings::new(
            TableBindings::new(SmallPrimeKernel, provider, state)
                .unwrap()
                .with_endpoint("prover".into(), Phase::Sent)
                .unwrap(),
        )
        .unwrap();
        let done = execute(&f, inputs, empty);
        assert!(matches!(
            done.outcome(),
            Ok(Outcome::Stopped(Stop::Exhausted))
        ));
        assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Sent)));
        assert_eq!(done.bindings().scalar_cells(), 1);
        let next = scalar_fixture(
            json!(["stop", "abort"]),
            json!(["stop", "abort"]),
            Some(endpoint_evidence(Phase::Ready)),
        );
        let (_, mut b) = execute(&next, json!([]), b).into_parts();
        assert_eq!(b.endpoint_entry(), Some(entry(Phase::Ready)));
        // Reentry with no scalar demand still retains the old output's scratch.
        assert_eq!(b.value_json(&alias).unwrap(), 1);
    }
}

struct FaultKernel(Arc<AtomicUsize>);
impl FieldKernel for FaultKernel {
    fn add(&self, d: Domain, a: u8, b: u8) -> u8 {
        match self.0.load(Ordering::Relaxed) {
            1 => 7,
            2 => panic!("deferred kernel fault"),
            _ => SmallPrimeKernel.add(d, a, b),
        }
    }
    fn sub(&self, d: Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.sub(d, a, b)
    }
    fn mul(&self, d: Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.mul(d, a, b)
    }
}
#[test]
fn failed_deferred_read_before_call_or_at_final_output_keeps_known_phase_and_owner() {
    for kind in [1, 2] {
        for final_read in [false, true] {
            let fault = Arc::new(AtomicUsize::new(if final_read { 0 } else { kind }));
            let (state, provider) = State::decode(&json!([0, 0, 0, [], [3, 6]])).unwrap();
            let b = PhysicalTableBindings::new(
                TableBindings::new(FaultKernel(fault.clone()), provider, state)
                    .unwrap()
                    .with_endpoint("prover".into(), Phase::Ready)
                    .unwrap(),
            )
            .unwrap();
            let (f, inputs) = round("lazy");
            let f = f.with_policy("prover", Some(endpoint_evidence(Phase::Ready)));
            let done = execute(&f, inputs, b);
            assert!(done.started());
            let (out, mut b) = done.into_parts();
            let error = Error(if kind == 1 {
                "field-contract-violation"
            } else {
                "backend-panic"
            });
            if final_read {
                let Outcome::Returned(alias) = out.unwrap() else {
                    panic!()
                };
                fault.store(kind, Ordering::Relaxed);
                assert_eq!(b.value_json(&alias), Err(error));
                fault.store(0, Ordering::Relaxed);
                assert_eq!(b.value_json(&alias).unwrap(), 1);
            } else {
                assert!(matches!(out, Err(e) if e == error));
            }
            let (sent, remaining, events) = if final_read {
                (
                    json!([[1, 1]]),
                    json!([6]),
                    vec![json!(["sent", 1, 1]), json!(["drawn", 3])],
                )
            } else {
                (json!([]), json!([3, 6]), vec![])
            };
            assert_eq!(
                b.state_json(),
                json!(["prover", "ready", [0, 0, 0, sent, remaining]])
            );
            assert_eq!(b.events(), events);
            assert_eq!(b.scalar_cells(), 1);
            let next = scalar_fixture(
                json!(["stop", "abort"]),
                json!(["stop", "abort"]),
                Some(endpoint_evidence(Phase::Ready)),
            );
            assert!(AdmittedJob::bind(admit(&next), json!([]), b).is_ok());
        }
    }
}
struct FaultProvider(u8, bool);
impl ChallengeProvider for FaultProvider {
    fn draw(&mut self) -> Result<Outcome<u8>, Error> {
        self.1 = true;
        match self.0 {
            0 => Err(Error("provider-io")),
            1 => Ok(Outcome::Returned(7)),
            _ => panic!("provider panic after effect"),
        }
    }
    fn remaining(&self) -> &[u8] {
        if self.1 { &[] } else { &[3] }
    }
}
#[test]
fn fault_during_physical_provider_call_leaves_unknown_with_prefix_and_no_reentry() {
    for kind in 0..3 {
        let (state, _) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
        let b = PhysicalTableBindings::new(
            TableBindings::new(SmallPrimeKernel, FaultProvider(kind, false), state)
                .unwrap()
                .with_endpoint("prover".into(), Phase::Ready)
                .unwrap(),
        )
        .unwrap();
        let (f, inputs) = round("lazy");
        let f = f.with_policy("prover", Some(endpoint_evidence(Phase::Ready)));
        let (out, b) = execute(&f, inputs.clone(), b).into_parts();
        assert!(matches!(
            out,
            Err(Error(
                "provider-io" | "field-contract-violation" | "backend-panic"
            ))
        ));
        assert_eq!(
            b.state_json(),
            json!(["prover", "unknown", [0, 0, 0, [[1, 1]], []]])
        );
        assert_eq!(b.events(), &[json!(["sent", 1, 1])]);
        assert_eq!(b.scalar_cells(), 1);
        let failure = AdmittedJob::bind(admit(&f), inputs, b).err().unwrap();
        assert_eq!(failure.reason, Error("unknown-endpoint-state"));
        assert_eq!(
            failure.bindings.endpoint_entry(),
            Some(entry(Phase::Unknown))
        );
    }
}
