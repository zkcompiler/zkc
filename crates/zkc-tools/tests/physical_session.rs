//! Live admission across successive invocations of one physical owner.
//! Lean executes each logical state transition with a fresh reference store;
//! native cells and aliases persist. This is differential evidence, not a proof
//! of a persistent native allocator or serialization of Lean store references.
use serde_json::{Value as Json, json};
use std::{fs, path::Path, process::Command, sync::Arc};
use zkc_runtime::{
    AdmittedJob, AdmittedProgram, Budget, EndpointEntry, Error, Outcome, PhaseEvidence, Stop,
    buffer::{BufferStore, PackedBuffers, SegmentedBuffers},
    table::{
        Phase, PhysicalOperation, PhysicalTableBindings, SmallPrimeKernel, State, TableBindings,
        TapeProvider, Value,
    },
};
use zkc_tools::LeanChecker;

struct Case {
    source: Json,
    candidate: Json,
    certificate: Json,
    inputs: Json,
    phase: Phase,
}
impl Case {
    fn prepare(mode: &str, stop: bool) -> Self {
        let r = json!(["residual", "f7", 1]);
        let p = json!(["point", "f7"]);
        let context = json!([
            "prover",
            [
                ["r", r, ["private", "prover"], "capture"],
                ["p", p, ["shared"], "argument"]
            ],
            ["scalar", "f7"],
            [["table-protocol", "1"]]
        ]);
        let tail = if stop {
            json!(["stop", "abort"])
        } else {
            json!(["apply", ["draw"], [], ["return", 2]])
        };
        let physical_tail = if stop {
            tail.clone()
        } else {
            json!(["apply", ["invoke", ["draw"]], [], ["return", 2]])
        };
        Self {
            source: json!([
                "zkc-request",
                1,
                "region-source-1",
                context,
                [],
                [
                    "apply",
                    ["evaluate", "f7", 1],
                    [0, 1],
                    ["apply", ["send"], [0, 0], tail]
                ]
            ]),
            candidate: json!([
                "zkc-table-physical-plan",
                1,
                context,
                [
                    "apply",
                    ["prepare", mode, "f7", 1],
                    [0, 1],
                    ["apply", ["invoke", ["send"]], [0, 0], physical_tail]
                ]
            ]),
            certificate: (0..if stop { 2 } else { 3 })
                .fold(json!(["terminal"]), |c, _| json!(["next", c])),
            inputs: json!([["r", r, [9, [2, 5], []]], ["p", p, [1]]]),
            phase: Phase::Ready,
        }
    }
    fn draw() -> Self {
        let context = json!(["prover", [], ["scalar", "f7"], [["table-protocol", "1"]]]);
        Self {
            source: json!([
                "zkc-request",
                1,
                "region-source-1",
                context,
                [],
                ["apply", ["draw"], [], ["return", 0]]
            ]),
            candidate: json!([
                "zkc-table-physical-plan",
                1,
                context,
                ["apply", ["invoke", ["draw"]], [], ["return", 0]]
            ]),
            certificate: json!(["next", ["terminal"]]),
            inputs: json!([]),
            phase: Phase::Sent,
        }
    }
    fn evidence(&self) -> PhaseEvidence {
        PhaseEvidence {
            profile: "table-endpoint/1".into(),
            certificate: self.certificate.to_string().into_bytes(),
            entry: Some(EndpointEntry {
                role: "prover".into(),
                phase: json!(self.phase.name()),
            }),
        }
    }
    fn admit(&self, checker: &LeanChecker) -> Arc<AdmittedProgram<PhysicalOperation>> {
        AdmittedProgram::admit_physical(
            self.source.to_string().into_bytes(),
            self.candidate.to_string().into_bytes(),
            Some(self.evidence()),
            checker,
        )
        .unwrap_or_else(|e| panic!("{}", e.reason))
    }
    fn reference(&self, checker: &Path, state: Json) -> Json {
        let dir = zkc_test_support::evidence(module_path!());
        let paths = ["source", "candidate", "inputs", "certificate", "entry"]
            .map(|name| dir.path().join(format!("{name}.json")));
        for (path, value) in paths.iter().zip([
            self.source.clone(),
            self.candidate.clone(),
            json!([self.inputs, state]),
            self.certificate.clone(),
            json!(["prover", self.phase.name()]),
        ]) {
            fs::write(path, value.to_string()).unwrap();
        }
        let out = Command::new(checker)
            .arg("run-entry")
            .args(&paths[..3])
            .arg("table-endpoint/1")
            .args(&paths[3..])
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
        serde_json::from_slice(&out.stdout).unwrap()
    }
}

type Bindings<S> = PhysicalTableBindings<SmallPrimeKernel, TapeProvider, S>;

fn step<S: BufferStore<u8>>(
    case: &Case,
    checker: &LeanChecker,
    path: &Path,
    bindings: Bindings<S>,
    total_cells: &mut u64,
    capture: &mut Option<Value>,
) -> Bindings<S> {
    let reference = case.reference(path, bindings.state_json());
    let program = case.admit(checker);
    let done = AdmittedJob::bind(program, case.inputs.clone(), bindings)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    let (out, mut bindings) = done.into_parts();
    let outcome = match out.unwrap() {
        Outcome::Returned(value) => {
            let decoded = bindings.value_json(&value).unwrap();
            if capture.is_none() {
                *capture = Some(value);
            }
            json!(["returned", decoded])
        }
        Outcome::Stopped(Stop::Abort) => json!(["stopped", "abort"]),
        other => panic!("unexpected outcome: {other:?}"),
    };
    assert_eq!(
        json!({"status":"executed", "outcome":outcome,
        "state":bindings.state_json(), "events":bindings.events()}),
        reference["execution"]
    );
    assert_eq!(
        json!(bindings.table_evaluations()),
        reference["table-evaluations"]
    );
    // This selected store is append-only. Sum the reference's per-invocation
    // publications; do not compare reference handle indices across invocations.
    *total_cells += reference["scalar-cells"].as_u64().unwrap();
    assert_eq!(json!(bindings.scalar_cells()), json!(*total_cells));
    assert_eq!(bindings.value_json(capture.as_ref().unwrap()).unwrap(), 5);
    bindings
}

fn session<S: BufferStore<u8>>(storage: S, mode: &str, path: &Path) {
    let checker = LeanChecker::new(path).unwrap();
    let (state, provider) = State::decode(&json!([0, 0, 0, [], [3, 6]])).unwrap();
    let logical = TableBindings::with_storage(SmallPrimeKernel, provider, state, storage)
        .unwrap()
        .with_endpoint("prover".into(), Phase::Ready)
        .unwrap();
    let bindings = PhysicalTableBindings::new(logical).unwrap();
    let (mut cells, mut alias) = (0, None);
    let bindings = step(
        &Case::prepare(mode, false),
        &checker,
        path,
        bindings,
        &mut cells,
        &mut alias,
    );
    assert_eq!(
        bindings.state_json(),
        json!(["prover", "ready", [0, 0, 0, [[5, 5]], [6]]])
    );
    let stopped = Case::prepare(mode, true);
    let bindings = step(&stopped, &checker, path, bindings, &mut cells, &mut alias);
    assert_eq!(
        bindings.state_json(),
        json!(["prover", "sent", [0, 0, 0, [[5, 5], [5, 5]], [6]]])
    );
    // The live checker accepts this ready-entry source, but that receipt cannot
    // bind the completed sent owner. Entry refusal precedes malformed inputs.
    let failure = AdmittedJob::bind(stopped.admit(&checker), Json::Null, bindings)
        .err()
        .unwrap();
    assert_eq!(failure.reason, Error("endpoint-entry-mismatch"));
    let bindings = step(
        &Case::draw(),
        &checker,
        path,
        failure.bindings,
        &mut cells,
        &mut alias,
    );
    assert_eq!(cells, 2);
    assert_eq!(
        bindings.state_json(),
        json!(["prover", "ready", [0, 0, 0, [[5, 5], [5, 5]], []]])
    );
}

#[test]
fn live_checker_readmits_the_same_owner_and_preserves_old_aliases() {
    let path = zkc_test_support::checker("table-physical-reference");
    let path = Path::new(&path);
    for mode in ["lazy", "materialized"] {
        session(PackedBuffers::new().unwrap(), mode, path);
        session(SegmentedBuffers::new().unwrap(), mode, path);
    }
}
