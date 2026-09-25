//! Project compilation's native preparation seam into separately compiled project source.
//! CheckedIndex stays in the host; only ordinary PCS values cross its codecs.
#[cfg(feature = "test-utils")]
#[path = "common/circom.rs"]
mod circom;

use serde_json::{Value as Json, json};
use std::{fs, path::Path, process::Command, sync::Arc};
use zkc_arkworks::{Bounds, Keys, Scalar};
use zkc_backends::{
    Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, SetupRegistry, Value,
};
use zkc_runtime::interactive::{Action, Runner, StopKind, Value as RuntimeValue, admit_physical};
use zkc_tools::{ingress::*, protocol::ParticipantChecker};

#[path = "common/observed.rs"]
mod observed;
use observed::PhysicalObserved;

fn compile(mode: &str, source: &Path, roots: &[&Path]) -> Vec<u8> {
    let output = Command::new(zkc_test_support::compiler())
        .arg(mode)
        .arg(source)
        .args(roots.iter().map(|p| format!("--library={}", p.display())))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}
fn relation(constant: u64, public_output: bool) -> RelationSubject {
    RelationSubject::from_normalized(
        &serde_json::to_vec(&json!([
            "zkc.relation.r1cs/1",
            "bn254.fr",
            "3",
            if public_output { "1" } else { "0" },
            if public_output { "0" } else { "1" },
            [[[["1", "1"]], [["2", "1"]], [["0", constant.to_string()]]]]
        ]))
        .unwrap(),
    )
    .unwrap()
}
fn backend(setup: &CheckedSetup) -> NativeBackend {
    let policy = Policy::default();
    NativeBackend::with_setups(
        policy,
        EntryPolicy::new(
            Domain::new("V", "index-opening", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        SetupRegistry::new(vec![setup.verifier().clone()], &policy).unwrap(),
    )
    .unwrap()
}

#[test]
fn two_native_checked_indexes_feed_imported_and_closed_compiled_kzg_checks() {
    let root = zkc_test_support::root();
    let evidence = zkc_test_support::evidence(module_path!());
    let lib = root.join("examples/libraries/pcs/lib.pir");
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let bounds = Bounds::new(4, 16, 1 << 20, 64);
    let keys = Keys::setup_for_development(2, &bounds).unwrap();
    let expected = ExpectedSetup::from_keys(&keys, &bounds).unwrap();
    let setup = expected
        .check(expected.verifier_bytes(), expected.prover_bytes(), &bounds)
        .unwrap();
    let premises = AcceptedPremises::new(PCS_PREMISES);
    let first = relation(6, false);
    let second = relation(7, false);
    let partition = relation(6, true); // Equal tables; different public-layout subject.
    let candidate = CoefficientIndex::encode(&first, 2, IndexLimits::default()).unwrap();
    let index = setup
        .check_index(&first, &candidate, IndexLimits::default())
        .unwrap();
    assert_eq!(index.subject().dimensions(), (1, 3));
    assert_eq!(index.subject().encoding(), INDEX_ENCODING);
    assert_eq!(
        setup
            .check_index(&second, &candidate, IndexLimits::default())
            .unwrap_err()
            .code,
        "ingress-index-mismatch"
    );
    for wrong in [&second, &partition] {
        assert_eq!(
            setup
                .commit_index(wrong, &index, &premises)
                .unwrap_err()
                .code,
            "ingress-index-subject"
        );
    }
    assert_eq!(
        setup
            .commit_index(&first, &index, &AcceptedPremises::default())
            .unwrap_err()
            .code,
        "ingress-required-premise"
    );
    assert_eq!(
        CoefficientIndex::encode(&first, 1, IndexLimits::default())
            .unwrap_err()
            .code,
        "ingress-setup-capacity"
    );
    assert_eq!(
        setup
            .check_index(
                &first,
                &candidate,
                IndexLimits {
                    max_coefficients: 11
                }
            )
            .unwrap_err()
            .code,
        "ingress-index-budget"
    );

    let mut programs = Vec::new();
    for name in ["main", "closed"] {
        let authored = root.join(format!("examples/projects/pcs/{name}.pir"));
        let roots: Vec<&Path> = if name == "main" { vec![&lib] } else { vec![] };
        let source = compile("protocol-source", &authored, &roots);
        let path = evidence.path().join(format!("{name}.json"));
        fs::write(&path, &source).unwrap();
        let physical = compile("protocol-compile", &path, &[]);
        fs::write(
            evidence.path().join(format!("{name}-physical.json")),
            &physical,
        )
        .unwrap();
        // Rust and the independently installed Lean checker admit actual endpoints.
        let admitted = admit_physical(&source, &physical, &backend(&setup), &checker).unwrap();
        programs.push(admitted);
    }
    let point = [Scalar::from(2), Scalar::from(3)];
    let mut records = Vec::new();
    for (subject, expected_values) in [
        (&first, [3, 2, 6]),
        (&second, [3, 2, 7]),
        (&partition, [3, 2, 6]),
    ] {
        let candidate = CoefficientIndex::encode(subject, 2, IndexLimits::default()).unwrap();
        let index = setup
            .check_index(subject, &candidate, IndexLimits::default())
            .unwrap();
        let committed = setup.commit_index(subject, &index, &premises).unwrap();
        // This is the explicit application-statement binding, before discarding
        // the host-only wrapper to send ordinary commitment/proof values.
        committed.check_applicability(&setup, subject).unwrap();
        if subject == &partition {
            assert_eq!(
                committed
                    .check_applicability(&setup, &first)
                    .unwrap_err()
                    .code,
                "ingress-commitment-subject"
            );
        }
        for (matrix, (table, expected_value)) in
            committed.tables().iter().zip(expected_values).enumerate()
        {
            let (value, proof) = table.open(&point).unwrap();
            assert_eq!(value, Scalar::from(expected_value)); // independent coefficient calculation
            assert!(
                setup
                    .verifier()
                    .check(table.commitment(), &point, value, &proof)
                    .unwrap()
            );
            for changed in [false, true] {
                let values = [
                    Value::VerifierKey(Arc::new(setup.verifier().clone())),
                    Value::Commitment(Arc::new(table.commitment().clone())),
                    Value::Point(point.to_vec().into()),
                    Value::Field(value + Scalar::from(u64::from(changed))),
                    Value::Proof(Arc::new(proof.clone())),
                ];
                let mut observations = Vec::new();
                for program in &programs {
                    let native = backend(&setup);
                    // Exercise the receiving setup registry and strict public codecs.
                    let received = values
                        .iter()
                        .map(|v| {
                            if matches!(v, Value::VerifierKey(_)) {
                                // Authenticated host setup, already decoded by ExpectedSetup.
                                return v.clone();
                            }
                            let wire = native.encode_value(v).unwrap();
                            if matches!(v, Value::Commitment(_) | Value::Proof(_)) {
                                native
                                    .decode_for_setup(
                                        v.physical_type(),
                                        setup.verifier().metadata(),
                                        &wire,
                                    )
                                    .unwrap()
                            } else {
                                native.decode_typed_value(v.physical_type(), &wire).unwrap()
                            }
                        })
                        .collect();
                    let observer = PhysicalObserved {
                        inner: native,
                        steps: vec![],
                        requests: vec![],
                    };
                    let mut runner =
                        Runner::new(program, "main", "V", "index-opening", observer, received)
                            .unwrap_or_else(|e| panic!("{}", e.error));
                    let status = loop {
                        match runner.poll() {
                            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                            Action::Returned(v) => {
                                assert!(!changed);
                                assert!(matches!(v.as_slice(), [Value::Bool(true)]));
                                break "returned";
                            }
                            Action::Stopped(stop) => {
                                assert!(changed);
                                assert!(
                                    matches!(stop.kind, StopKind::Backend(ref error) if error.code == "rejected:require")
                                );
                                break "stopped";
                            }
                            other => panic!("unexpected {other:?}"),
                        }
                    };
                    // Names differ by selected origin; contracts and order must agree.
                    let contracts: Vec<Json> = runner
                        .backend()
                        .requests
                        .iter()
                        .map(|r| r[2].clone())
                        .collect();
                    assert_eq!(
                        contracts,
                        vec![json!("pcs.check"), json!("control.require")]
                    );
                    observations.push((status, contracts));
                }
                assert_eq!(observations[0], observations[1]);
                records.push(json!({"matrix":matrix,"changed_value":changed,"outcome":observations[0].0,
                    "host_binding":"checked exact relation/setup/encoding/dimensions; not carried in PIR"}));
            }
        }
    }
    fs::write(
        evidence.path().join("coverage.json"),
        serde_json::to_vec_pretty(&records).unwrap(),
    )
    .unwrap();
}

// Independent R1CS-v1 container author, as in compiler/test/relation_import.py.
// Read the checked-in descriptor so default preparation tests need no snarkjs,
// setup, key or witness fixtures, but still exercise the binary R1CS reader.
fn groth16_r1cs(descriptor: &Json) -> Vec<u8> {
    use ark_ff::{BigInteger, PrimeField};
    let natural = |v: &Json| v.as_str().unwrap().parse::<u32>().unwrap();
    let columns = natural(&descriptor[2]);
    let outputs = natural(&descriptor[3]);
    let inputs = natural(&descriptor[4]);
    let rows = descriptor[5].as_array().unwrap();
    let mut header = 32u32.to_le_bytes().to_vec();
    header.extend(ark_bn254::Fr::MODULUS.to_bytes_le());
    for n in [columns, outputs, inputs, columns - outputs - inputs - 1] {
        header.extend(n.to_le_bytes());
    }
    header.extend(u64::from(columns).to_le_bytes());
    header.extend((rows.len() as u32).to_le_bytes());
    let mut constraints = Vec::new();
    for row in rows {
        for form in row.as_array().unwrap() {
            let terms = form.as_array().unwrap();
            constraints.extend((terms.len() as u32).to_le_bytes());
            for term in terms {
                constraints.extend(natural(&term[0]).to_le_bytes());
                let mut scalar = term[1]
                    .as_str()
                    .unwrap()
                    .parse::<num_bigint::BigUint>()
                    .unwrap()
                    .to_bytes_le();
                scalar.resize(32, 0);
                constraints.extend(scalar);
            }
        }
    }
    let wires = (0..u64::from(columns))
        .flat_map(u64::to_le_bytes)
        .collect::<Vec<_>>();
    let mut binary = b"r1cs".to_vec();
    binary.extend(1u32.to_le_bytes());
    binary.extend(3u32.to_le_bytes());
    for (id, bytes) in [(1u32, header), (2, constraints), (3, wires)] {
        binary.extend(id.to_le_bytes());
        binary.extend((bytes.len() as u64).to_le_bytes());
        binary.extend(bytes);
    }
    binary
}

struct Groth16Project {
    directory: tempfile::TempDir,
    app: std::path::PathBuf,
    library: std::path::PathBuf,
    r1cs: std::path::PathBuf,
    descriptor: Json,
    source: String,
}
impl Groth16Project {
    fn new() -> Self {
        let root = zkc_test_support::root();
        let directory = tempfile::tempdir().unwrap();
        let app = directory.path().join("main.pir");
        let library = directory.path().join("lib.pir");
        let r1cs = directory.path().join("expected.r1cs");
        let descriptor: Json = serde_json::from_slice(
            &fs::read(root.join("examples/libraries/groth16/circuit.json")).unwrap(),
        )
        .unwrap();
        fs::write(&r1cs, groth16_r1cs(&descriptor)).unwrap();
        fs::write(
            directory.path().join("circuit.json"),
            serde_json::to_vec(&descriptor).unwrap(),
        )
        .unwrap();
        let mut other = descriptor.clone();
        other[5][0][2] = json!([["0", "7"]]);
        fs::write(
            directory.path().join("other.json"),
            serde_json::to_vec(&other).unwrap(),
        )
        .unwrap();
        let source = fs::read_to_string(root.join("examples/libraries/groth16/lib.pir")).unwrap();
        fs::write(&library, &source).unwrap();
        fs::copy(root.join("examples/projects/groth16/main.pir"), &app).unwrap();
        Self {
            directory,
            app,
            library,
            r1cs,
            descriptor,
            source,
        }
    }
    fn prepare(&self) -> zkc_tools::groth16::Result<zkc_tools::groth16::PreparedProtocol> {
        zkc_tools::groth16::PreparedProtocol::compile_project(
            zkc_test_support::compiler(),
            zkc_test_support::checker("interactive-protocol"),
            &self.app,
            std::slice::from_ref(&self.library),
            &self.r1cs,
        )
    }
    fn with_other_view(&self) -> String {
        self.source.replace("derive Core =", "relation Other = r1cs(\"other.json\");\n  derive OtherCore = rank_one(Other, public_matrices);\n  derive Core =")
    }
}

#[test]
fn groth16_project_preparation_binds_checked_in_relation_without_external_fixtures() {
    use zkc_tools::groth16::PreparedProtocol;
    let fixture = Groth16Project::new();
    // An unrelated unused view is harmless. Selection also survives renaming
    // the selected source view; generated hash spellings are not hardcoded.
    let source = fixture
        .with_other_view()
        .replace("derive Core =", "derive Selected =")
        .replace("Core_Products(", "Selected_Products(")
        .replace("Core_Residuals(", "Selected_Residuals(");
    fs::write(&fixture.library, source).unwrap();
    let prepared = fixture.prepare().unwrap();
    let retained = prepared.relation().unwrap();
    assert_eq!(
        serde_json::from_slice::<Json>(retained.canonical_descriptor()).unwrap(),
        fixture.descriptor
    );
    assert_eq!(retained.identity(), prepared.relation_identity());

    // Preserve and exercise the public single-file wrapper's circuit.r1cs
    // convention, and the authenticated-cache path (which retains no R1CS).
    let closed = PreparedProtocol::compile(
        zkc_test_support::compiler(),
        zkc_test_support::checker("interactive-protocol"),
        &fs::read(zkc_test_support::root().join("examples/protocols/groth16.pir")).unwrap(),
        &fs::read(&fixture.r1cs).unwrap(),
    )
    .unwrap();
    assert_eq!(closed.relation_identity(), prepared.relation_identity());
    let cached = PreparedProtocol::prepare(
        closed.source(),
        closed.endpoints(),
        zkc_test_support::checker("interactive-protocol"),
        closed.relation_identity(),
    )
    .unwrap();
    assert!(cached.relation().is_none());
    let mut missing: Json = serde_json::from_slice(closed.source()).unwrap();
    missing[3][3][0][7][0][3] = json!("missing_function");
    assert_eq!(
        PreparedProtocol::prepare(
            &serde_json::to_vec(&missing).unwrap(),
            closed.endpoints(),
            zkc_test_support::checker("interactive-protocol"),
            closed.relation_identity()
        )
        .unwrap_err()
        .code,
        "groth16-relation-call-graph"
    );
    let mut endpoints: Json = serde_json::from_slice(closed.endpoints()).unwrap();
    endpoints[5][0][1] = json!("different_entry");
    assert_eq!(
        PreparedProtocol::prepare(
            closed.source(),
            &serde_json::to_vec(&endpoints).unwrap(),
            zkc_test_support::checker("interactive-protocol"),
            closed.relation_identity()
        )
        .unwrap_err()
        .code,
        "groth16-admission"
    );
}

#[test]
fn groth16_project_preparation_rejects_unused_selected_view() {
    let fixture = Groth16Project::new();
    let checked = "    let (az, bz, cz) = Core_Products(relation.a, relation.b, relation.c, bound.assignment);\n    let residuals = Core_Residuals(az, bz, cz);\n    Groth16Zero(residuals);\n";
    assert!(fixture.source.contains(checked));
    fs::write(&fixture.library, fixture.source.replace(checked, "")).unwrap();
    assert_eq!(
        fixture.prepare().unwrap_err().code,
        "groth16-relation-view-unused"
    );
}

#[test]
fn groth16_project_preparation_rejects_different_reachable_view() {
    let fixture = Groth16Project::new();
    let source = fixture
        .with_other_view()
        .replace("Core_Products(", "OtherCore_Products(")
        .replace("Core_Residuals(", "OtherCore_Residuals(");
    fs::write(&fixture.library, source).unwrap();
    assert_eq!(
        fixture.prepare().unwrap_err().code,
        "groth16-relation-view-mismatch"
    );
}

#[test]
fn groth16_project_preparation_rejects_additional_reachable_view() {
    let fixture = Groth16Project::new();
    let source = fixture.with_other_view().replace("    let (az, bz, cz) = Core_Products(",
        "    let (other_a, other_b, other_c) = OtherCore_Products(relation.a, relation.b, relation.c, bound.assignment);\n    let (az, bz, cz) = Core_Products(");
    fs::write(&fixture.library, source).unwrap();
    assert_eq!(
        fixture.prepare().unwrap_err().code,
        "groth16-relation-view-mismatch"
    );
}

#[test]
fn groth16_project_preparation_rejects_ambiguous_matching_views() {
    let fixture = Groth16Project::new();
    let source = fixture.source.replace(
        "derive Core =",
        "derive Another = rank_one(Circuit, public_matrices);\n  derive Core =",
    );
    fs::write(&fixture.library, source).unwrap();
    assert_eq!(
        fixture.prepare().unwrap_err().code,
        "groth16-relation-view-ambiguous"
    );
}

#[test]
fn groth16_project_preparation_follows_main_and_only_called_dependencies() {
    let fixture = Groth16Project::new();
    let mut snapshot: Json = serde_json::from_slice(&compile(
        "protocol-resolve",
        &fixture.app,
        &[&fixture.library],
    ))
    .unwrap();
    let common = &mut snapshot[2][3]; // frozen relation source -> library -> common
    let original = common[3][0].clone();
    let input_names = original[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p[0].clone())
        .collect::<Vec<_>>();
    let wrapper = json!([
        "protocol",
        "Wrapper",
        ["P", "V"],
        [],
        original[4],
        original[5],
        [["child", original[1], []]],
        [
            ["call", "run", "child", input_names, ["accepted"]],
            ["return", ["accepted"]]
        ]
    ]);
    common[3].as_array_mut().unwrap().push(wrapper);
    common[4].as_array_mut().unwrap().push(json!([
        "instance",
        "wrapper",
        "Wrapper",
        [],
        [["child", "proof"]],
        [["P", "P"], ["V", "V"]]
    ]));
    common[5][0][2] = json!("wrapper");
    let source = fixture.directory.path().join("wrapped.json");
    fs::write(&source, serde_json::to_vec(&snapshot).unwrap()).unwrap();
    let prepare = || {
        zkc_tools::groth16::PreparedProtocol::compile_project(
            zkc_test_support::compiler(),
            zkc_test_support::checker("interactive-protocol"),
            &source,
            &[],
            &fixture.r1cs,
        )
    };
    prepare().unwrap();
    // Keep the original proving protocol, function calls and dependency binding
    // in the admitted module, but route main through a body that never calls it.
    let common = &mut snapshot[2][3];
    let wrapper = common[3].as_array_mut().unwrap().last_mut().unwrap();
    wrapper[7] = json!([
        ["local", "accept", "V", "Always", [], ["accepted"]],
        ["return", ["accepted"]]
    ]);
    common[1].as_array_mut().unwrap().extend([
        json!(["zero_op", "index.constant", [], ""]),
        json!(["equal_op", "index.equal", [], ""]),
    ]);
    common[2].as_array_mut().unwrap().push(json!([
        "function",
        "Always",
        [],
        ["bool"],
        [
            ["op", "zero", "zero_op", ["0"], [], ["zero"]],
            [
                "op",
                "equal",
                "equal_op",
                [],
                ["zero", "zero"],
                ["accepted"]
            ],
            ["return", ["accepted"]]
        ],
        ["Always", []]
    ]));
    fs::write(&source, serde_json::to_vec(&snapshot).unwrap()).unwrap();
    // The candidate is independently compilable; host reachability must refuse.
    compile("protocol-compile", &source, &[]);
    assert_eq!(prepare().unwrap_err().code, "groth16-relation-view-unused");
}

#[cfg(feature = "test-utils")]
#[test]
#[ignore = "requires ZKC_GROTH16_FIXTURE produced by pinned snarkjs 0.7.5"]
fn imported_groth16_uses_real_checked_ingress_proving_and_verification() {
    use ark_bn254::Fr;
    use zkc_tools::{
        groth16::{PreparedProtocol, Proof, Randomness, Statement, VerifyingKey},
        snarkjs::Limits,
    };
    let fixture = std::path::PathBuf::from(
        std::env::var_os("ZKC_GROTH16_FIXTURE").expect("set ZKC_GROTH16_FIXTURE"),
    );
    let root = zkc_test_support::root();
    let evidence = zkc_test_support::evidence(module_path!());
    let compiler = zkc_test_support::compiler();
    let lean = zkc_test_support::checker("interactive-protocol");
    for depth in [2, 16] {
        let input = fixture.join(format!("artifacts/depth{depth}"));
        let dir = evidence.nested(&format!("depth{depth}"));
        let lib = dir.path().join("lib.pir");
        let app = dir.path().join("main.pir");
        let r1cs = dir.path().join("circuit.r1cs");
        fs::write(
            &lib,
            fs::read_to_string(root.join("examples/libraries/groth16/lib.pir"))
                .unwrap()
                .replace("circuit.json", "circuit.r1cs"),
        )
        .unwrap();
        fs::copy(root.join("examples/projects/groth16/main.pir"), &app).unwrap();
        fs::copy(input.join(format!("depth{depth}.r1cs")), &r1cs).unwrap();
        let protocol = PreparedProtocol::compile_project(
            &compiler,
            &lean,
            &app,
            std::slice::from_ref(&lib),
            &r1cs,
        )
        .unwrap();
        let relation = protocol.relation().unwrap();
        let vk = VerifyingKey::from_json(&fs::read(input.join("vk.json")).unwrap()).unwrap();
        let statement =
            Statement::from_json(&fs::read(input.join("public.json")).unwrap()).unwrap();
        let zkey = fs::read(input.join("final.zkey")).unwrap();
        let witness = fs::read(input.join("witness.wtns")).unwrap();
        let contract = Groth16Contract::new(
            RelationSubject::from_prepared(relation),
            vk.clone(),
            GROTH16_PREMISES,
        )
        .unwrap();
        let key = contract
            .check_key(relation.canonical_descriptor(), &zkey, &Limits::default())
            .unwrap();
        let assignment = contract
            .check_assignment(&statement, &witness, &Limits::default())
            .unwrap();
        let invocation = protocol
            .bind_checked(&contract, statement.clone(), b"frontend-project-groth16")
            .unwrap();
        let accepted = AcceptedPremises::new(GROTH16_PREMISES);
        let tape = || Randomness::Test {
            r: Fr::from(1),
            s: Fr::from(2),
        };
        assert_eq!(
            invocation
                .prove(&key, &assignment, &AcceptedPremises::default(), tape())
                .unwrap_err()
                .code,
            "ingress-required-premise"
        );
        let proof = invocation
            .prove(&key, &assignment, &accepted, tape())
            .unwrap();
        invocation
            .verify_artifact(&proof.artifact, &accepted)
            .unwrap();
        // Independently authored existing closed source executes the same real
        // arithmetic, and pinned external snarkjs supplies independent coordinates.
        let closed = PreparedProtocol::compile(
            &compiler,
            &lean,
            &fs::read(root.join("examples/protocols/groth16.pir")).unwrap(),
            &fs::read(&r1cs).unwrap(),
        )
        .unwrap();
        let closed = closed
            .bind_checked(&contract, statement.clone(), b"frontend-project-groth16")
            .unwrap();
        let closed_proof = closed.prove(&key, &assignment, &accepted, tape()).unwrap();
        assert_eq!(proof.proof, closed_proof.proof);
        assert_eq!(
            proof.proof,
            Proof::from_json(&fs::read(input.join("proof-r1-s2.json")).unwrap()).unwrap()
        );
        // Construction identities differ; artifact byte equality is not promised.
        fs::write(
            dir.path().join("proof.json"),
            proof.proof.to_json().unwrap(),
        )
        .unwrap();
        let external = Command::new("node")
            .arg(fixture.join("node_modules/snarkjs/cli.js"))
            .args(["groth16", "verify"])
            .arg(input.join("vk.json"))
            .arg(input.join("public.json"))
            .arg(dir.path().join("proof.json"))
            .output()
            .unwrap();
        assert!(
            external.status.success(),
            "{}",
            String::from_utf8_lossy(&external.stderr)
        );
        assert!(!String::from_utf8_lossy(&external.stdout).contains("Invalid proof"));
        fs::write(dir.path().join("proof.artifact"), &proof.artifact).unwrap();
        fs::write(dir.path().join("source.json"), protocol.source()).unwrap();
        fs::write(dir.path().join("endpoints.json"), protocol.endpoints()).unwrap();

        let mut changed: Json = serde_json::from_slice(relation.canonical_descriptor()).unwrap();
        changed[5][0][2] = json!([["0", "1"]]);
        let changed =
            RelationSubject::from_normalized(&serde_json::to_vec(&changed).unwrap()).unwrap();
        assert_ne!(changed, *contract.relation());
        assert_eq!(
            contract
                .check_key(changed.descriptor(), &zkey, &Limits::default())
                .unwrap_err()
                .code,
            "ingress-relation-mismatch"
        );
        let wrong_relation = dir.path().join("wrong-relation.json");
        fs::write(&wrong_relation, changed.descriptor()).unwrap();
        assert_eq!(
            PreparedProtocol::compile_project(
                &compiler,
                &lean,
                &app,
                std::slice::from_ref(&lib),
                &wrong_relation
            )
            .unwrap_err()
            .code,
            "groth16-relation-identity"
        );
        let other = Groth16Contract::new(changed, vk.clone(), GROTH16_PREMISES).unwrap();
        assert_eq!(
            protocol
                .bind_checked(&other, statement.clone(), b"frontend-project-groth16")
                .unwrap_err()
                .code,
            "ingress-compiled-relation-mismatch"
        );
        let wrong_assignment = other
            .check_assignment(&statement, &witness, &Limits::default())
            .unwrap();
        assert_eq!(
            invocation
                .prove(&key, &wrong_assignment, &accepted, tape())
                .unwrap_err()
                .code,
            "ingress-assignment-subject"
        );
        let other_key = other
            .check_key(other.relation().descriptor(), &zkey, &Limits::default())
            .unwrap();
        assert_eq!(
            invocation
                .prove(&other_key, &assignment, &accepted, tape())
                .unwrap_err()
                .code,
            "ingress-key-subject"
        );
        let mut wrong_statement = statement.0.to_vec();
        wrong_statement[0] += Fr::from(1);
        assert_eq!(
            contract
                .check_assignment(
                    &Statement(wrong_statement.into()),
                    &witness,
                    &Limits::default()
                )
                .unwrap_err()
                .code,
            "ingress-statement-mismatch"
        );
        // The host binds layout, not satisfaction: corrupt a private cell and
        // require actual compiled proving to stop rather than minting evidence.
        let mut bad_witness = assignment.witness().0.to_vec();
        let private_cell =
            circom::witness_index(&input.join(format!("depth{depth}.sym")), "main.nodes[0]");
        assert!(private_cell > statement.0.len() && private_cell < bad_witness.len());
        bad_witness[private_cell] += Fr::from(1);
        let bad = contract
            .bind_assignment(&statement, zkc_tools::snarkjs::Witness(bad_witness.into()))
            .unwrap();
        assert!(invocation.prove(&key, &bad, &accepted, tape()).is_err());
        let mut bad_artifact = proof.artifact.clone();
        let last = bad_artifact.len() - 1;
        bad_artifact[last] ^= 1;
        assert!(
            invocation
                .verify_artifact(&bad_artifact, &accepted)
                .is_err()
        );
        // Retaining/importing source is not a ceremony or C/IC/H derivation proof.
        for premise in GROTH16_PREMISES {
            assert!(
                key.evidence()
                    .contains(&EvidenceStatus::MissingProof(premise))
            );
        }
    }
}
