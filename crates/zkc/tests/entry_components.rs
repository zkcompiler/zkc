//! Fresh compiler/SDK pairing; run explicitly with the native owner's built tool.
#![cfg(all(feature = "cpu", feature = "files"))]
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    path::{Path, PathBuf},
    process::Command,
};
use zkc::entry::{
    self, BindingPolicy, EntryError, EntryPhase, FunctionEntry, FunctionInterface, FunctionOptions,
    FunctionRequest, InvocationBinding, InvocationContext, Package, ProofContext, ProofEntry,
    ProofOperation, ProofOptions, ProofRequest, RoleInputs, RunContext, RunEntry, RunRequest,
};

/// The explicit pairing gate uses the compiler build selected by
/// `ZKC_COMPILER_BIN`; a relative path is resolved from the checkout root.
fn compiler() -> PathBuf {
    let directory = std::env::var_os("ZKC_COMPILER_BIN")
        .expect("set ZKC_COMPILER_BIN to the freshly built compiler directory");
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(directory)
        .join("zkc-compile")
}
fn capture(bytes: &[u8]) -> Package {
    Package::capture(bytes, &Sha256::digest(bytes).into(), Package::MAX_BYTES).unwrap()
}
fn compile(compiler: &Path, source: &Path, name: &str) -> Package {
    let output = Command::new(compiler)
        .arg("language-package")
        .arg("--source-format=zkc-layout")
        .arg(format!("--module=m={}", source.display()))
        .arg(format!("--entry=m::{name}"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    capture(&output.stdout)
}
fn proof_request(host: &ProofEntry, proving: bool) -> ProofRequest {
    let groups = host.interface().input_groups();
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    ProofRequest {
        public: decoder
            .decode(
                &groups[0],
                br#"{"state_statement":true,"state_empty":null}"#,
                None,
            )
            .unwrap(),
        private: RoleInputs {
            inputs: if proving {
                decoder
                    .decode(&groups[1], br#"{"state_witness":false}"#, None)
                    .unwrap()
            } else {
                Default::default()
            },
            ..Default::default()
        },
        ..Default::default()
    }
}

#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_cpp_packages_execute_complete_component_run_proof_and_host_families() {
    let compiler = compiler();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/entry_components.zkc");
    let proof_package = compile(&compiler, &source, "Demo");
    let host = ProofEntry::admit(
        proof_package,
        ProofOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        Default::default(),
    )
    .unwrap();
    assert_eq!(host.interface().public_selections()[1].path, [2]);
    let produced = host.prove(proof_request(&host, true)).unwrap();
    assert!(produced.is_success());
    let checked = host
        .verify(
            proof_request(&host, false),
            &produced.native.outcome.unwrap(),
        )
        .unwrap();
    assert_eq!(checked.verification_result(), Some(true));

    // The default protocol Entry is a Host wrapper; pair its independently
    // authenticated joint child directly with the named Run API as well.
    let wrapper = compile(&compiler, &source, "Round");
    let artifact: Json = serde_json::from_str(wrapper.artifact()).unwrap();
    let child = artifact["deployments"][0]["package"].as_str().unwrap();
    let run = RunEntry::admit(
        capture(child.as_bytes()),
        Default::default(),
        Default::default(),
    )
    .unwrap();
    let groups = run.interface().input_groups();
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    let supplied = [
        br#"{"state_statement":true,"state_witness":false}"#.as_slice(),
        br#"{"state_statement":false,"state_empty":null}"#.as_slice(),
    ];
    let roles = groups
        .iter()
        .zip(supplied)
        .map(|(g, bytes)| {
            (
                g.name().to_owned(),
                RoleInputs {
                    inputs: decoder.decode(g, bytes, None).unwrap(),
                    ..Default::default()
                },
            )
        })
        .collect();
    assert!(
        run.prepare(RunRequest {
            session: "fresh-components".into(),
            roles,
            setups: Default::default()
        })
        .unwrap()
        .execute()
        .is_success()
    );

    let package = compile(&compiler, &source, "Produce");
    let children = FunctionInterface::deployment_interfaces(&package).unwrap();
    let authority = children
        .iter()
        .map(|d| (d.id().to_owned(), Default::default()))
        .collect();
    let deployments = children
        .iter()
        .map(|d| {
            (
                d.id().to_owned(),
                InvocationBinding::Proof(ProofContext::default()),
            )
        })
        .collect();
    let entry = FunctionEntry::admit(
        package,
        FunctionOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        authority,
    )
    .unwrap();
    let group = entry.interface().input_group();
    let args = json!({"public":{"state_statement":true,"state_empty":null},"witness":{"state_witness":false}});
    let arguments = decoder
        .decode(&group, args.to_string().as_bytes(), None)
        .unwrap();
    let result = entry
        .prepare(FunctionRequest {
            arguments,
            context: InvocationContext { deployments },
        })
        .unwrap()
        .execute();
    assert!(result.is_success(), "{}", result.diagnostics());
    assert!(result.value.is_some());
}

#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_cpp_host_transports_home_constructed_sealed_witness() {
    let compiler = compiler();
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/entry_components_opaque.zkc");

    // Selecting the proof names no external operation, so it compiles. Fresh
    // proving cannot reconstruct the private sealed witness; verifying never
    // consumes it. A typed Function signature can accept a retained value.
    let demo = compile(&compiler, &source, "Demo");
    for operation in [None, Some(ProofOperation::Prove)] {
        assert_refused(
            admit_proof(demo.clone(), operation),
            EntryPhase::Interface,
            "entry-input-constructor",
        );
    }
    admit_proof(demo, Some(ProofOperation::Verify)).unwrap();

    let import = admit_function(compile(&compiler, &source, "Import"));
    let forged = entry::Value::Record([("value".into(), false.into())].into());
    // A Function parameter admits retained values, so a fresh one is refused
    // only when preparation decodes it.
    assert_refused(
        import.prepare(FunctionRequest {
            arguments: [("secret".into(), forged)].into(),
            ..Default::default()
        }),
        EntryPhase::Preparation,
        "entry-input-constructor",
    );

    let produce = admit_function(compile(&compiler, &source, "Produce"));
    let check = admit_function(compile(&compiler, &source, "Check"));
    let run = admit_function(compile(&compiler, &source, "Run"));

    // A verifier consumes no prover witness, even at the external SDK boundary.
    let artifact: Json = serde_json::from_str(check.package().artifact()).unwrap();
    let bytes = artifact["deployments"][0]["package"].as_str().unwrap();
    ProofEntry::admit_operation(
        capture(bytes.as_bytes()),
        ProofOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        Default::default(),
        ProofOperation::Verify,
    )
    .unwrap();

    // Extracting a retained child does not turn it into an external constructor.
    for (host, proof) in [(&produce, true), (&run, false)] {
        let artifact: Json = serde_json::from_str(host.package().artifact()).unwrap();
        let bytes = artifact["deployments"][0]["package"].as_str().unwrap();
        let package = capture(bytes.as_bytes());
        let error = if proof {
            ProofEntry::admit(
                package,
                ProofOptions {
                    binding: BindingPolicy::AllowAuthored,
                    ..Default::default()
                },
                Default::default(),
            )
            .err()
            .expect("external proof constructor was granted")
        } else {
            RunEntry::admit(package, Default::default(), Default::default())
                .err()
                .expect("external Run constructor was granted")
        };
        assert_eq!(
            (error.phase, error.code()),
            (EntryPhase::Interface, "entry-input-constructor"),
            "{error}"
        );
    }

    for statement in [false, true] {
        let public = json!({"state_statement": statement, "state_empty": null});
        for value in [false, true] {
            let accepted = statement == value;
            // A producer can emit a well-framed proof for a false claim. Keep
            // the same bound public statement when checking semantic rejection.
            let produced = invoke_function(&produce, json!({"public": public, "value": value}));
            assert_completed_call(&produced, "prove");
            let candidate = produced.value.unwrap();
            // Candidate is a typed compiler result, carried as a whole value.
            let arguments = std::collections::BTreeMap::from([
                (
                    "public".into(),
                    entry::Value::Record(std::collections::BTreeMap::from([
                        ("state_statement".into(), statement.into()),
                        ("state_empty".into(), entry::Value::Unit),
                    ])),
                ),
                ("candidate".into(), candidate.into_value()),
            ]);
            let checked = execute_function(&check, arguments);
            assert_completed_call(&checked, "verify");
            let verified = checked.value.unwrap().into_value();
            // VerifyResult has no external constructor. Its admitted owner
            // exposes the public alternative without exposing construction.
            assert!(matches!(&verified, entry::Value::Opaque(_)));
            assert_eq!(
                verified.alternative().unwrap(),
                if accepted { "Accepted" } else { "Rejected" }
            );

            let completed = invoke_function(&run, json!({"statement": statement, "value": value}));
            assert_completed_call(&completed, "run");
            assert_eq!(
                bool::try_from(completed.value.unwrap().into_value()).unwrap(),
                accepted
            );
        }
    }
}

/// This was a closure-time refusal. Closing a selection names no external
/// operation, so it now compiles, and the SDK's Entry admission judges supply
/// for the operation that consumes each input.
#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_cpp_supply_is_judged_per_operation_at_admission() {
    let compiler = compiler();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/entry_supply.zkc");

    // A setup-context value keeps its recursive constructor demand. The
    // prover consumes the unconstructible opening state; the verifier only
    // its setup-initialized key, so it reaches setup authority instead.
    let opened = compile(&compiler, &source, "OpenedJob");
    for operation in [None, Some(ProofOperation::Prove)] {
        assert_refused(
            admit_proof(opened.clone(), operation),
            EntryPhase::Interface,
            "entry-input-constructor",
        );
    }
    assert_refused(
        admit_proof(opened, Some(ProofOperation::Verify)),
        EntryPhase::Authority,
        "entry-setup-authority",
    );
}

fn admit_proof(
    package: Package,
    operation: Option<ProofOperation>,
) -> Result<ProofEntry, EntryError> {
    let options = ProofOptions {
        binding: BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    match operation {
        Some(operation) => {
            ProofEntry::admit_operation(package, options, Default::default(), operation)
        }
        None => ProofEntry::admit(package, options, Default::default()),
    }
}

fn assert_refused<T>(result: Result<T, EntryError>, phase: EntryPhase, code: &str) {
    let Err(error) = result else {
        panic!("{code} was not refused");
    };
    assert_eq!((error.phase, error.code()), (phase, code), "{error}");
}

fn assert_completed_call(report: &entry::FunctionReport, operation: &str) {
    assert_eq!(
        report
            .calls
            .iter()
            .filter(|call| call.operation == operation && call.completed)
            .count(),
        1,
        "{}",
        report.diagnostics()
    );
}

fn admit_function(package: Package) -> FunctionEntry {
    let children = FunctionInterface::deployment_interfaces(&package).unwrap();
    let authority = children
        .iter()
        .map(|child| (child.id().to_owned(), Default::default()))
        .collect();
    FunctionEntry::admit(
        package,
        FunctionOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        authority,
    )
    .unwrap()
}

fn invoke_function(host: &FunctionEntry, arguments: Json) -> entry::FunctionReport {
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    let arguments = decoder
        .decode(
            &host.interface().input_group(),
            arguments.to_string().as_bytes(),
            None,
        )
        .unwrap();
    execute_function(host, arguments)
}

fn execute_function(host: &FunctionEntry, arguments: entry::NamedValues) -> entry::FunctionReport {
    let deployments = FunctionInterface::deployment_interfaces(host.package())
        .unwrap()
        .iter()
        .map(|child| {
            let binding = match child.operation() {
                "run" => InvocationBinding::Run(RunContext::default()),
                "prove" | "verify" => InvocationBinding::Proof(ProofContext::default()),
                operation => panic!("unexpected child operation: {operation}"),
            };
            (child.id().to_owned(), binding)
        })
        .collect();
    let result = host
        .prepare(FunctionRequest {
            arguments,
            context: InvocationContext { deployments },
        })
        .unwrap()
        .execute();
    assert!(result.is_success(), "{}", result.diagnostics());
    result
}

#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_function_proof_child_completes_on_a_later_attempt() {
    let compiler = compiler();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/function_attempts.zkc");
    let output = Command::new(&compiler)
        .arg("language-package")
        .arg("--source-format=zkc")
        .arg(format!("--module=m={}", source.display()))
        .arg("--entry=m::Produce")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let package = capture(&output.stdout);
    let children = FunctionInterface::deployment_interfaces(&package).unwrap();
    assert_eq!(children.len(), 1);
    let id = children[0].id().to_owned();
    let execute = |attempts: Option<entry::AttemptOptions>| {
        let entry = FunctionEntry::admit(
            package.clone(),
            FunctionOptions {
                binding: BindingPolicy::AllowAuthored,
                attempts: attempts
                    .map(|a| std::collections::BTreeMap::from([(id.clone(), a)]))
                    .unwrap_or_default(),
                ..Default::default()
            },
            std::collections::BTreeMap::from([(id.clone(), Default::default())]),
        )
        .unwrap();
        let group = entry.interface().input_group();
        let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
        let arguments = decoder
            .decode(&group, br#"{"public":{},"witness":{}}"#, None)
            .unwrap();
        entry
            .prepare(FunctionRequest {
                arguments,
                context: InvocationContext {
                    deployments: [(
                        id.clone(),
                        InvocationBinding::Proof(ProofContext::default()),
                    )]
                    .into(),
                },
            })
            .unwrap()
            .execute()
    };
    // Each attempt completes with probability one half. Under an explicit
    // policy a child whose first attempt requests a retry still produces its
    // proof; without one, that child fails at the one-attempt limit. Both are
    // observed within 64 independent calls except with probability 2^-63.
    let (mut retried, mut limited) = (false, false);
    for _ in 0..64 {
        let report = execute(Some(entry::AttemptOptions {
            count: 64,
            ..Default::default()
        }));
        assert!(report.is_success(), "{}", report.diagnostics());
        let attempts = report.calls[0].native["attempt_count"].as_u64().unwrap();
        if attempts >= 2 {
            assert_eq!(
                report.calls[0].native["attempts"][0]["decision"],
                json!({"Ok": false})
            );
            retried = true;
        }
        let single = execute(None);
        if !single.is_success() {
            assert_eq!(single.failure.unwrap().code, "native-attempt-limit");
            limited = true;
        }
        if retried && limited {
            break;
        }
    }
    assert!(retried && limited);
}
