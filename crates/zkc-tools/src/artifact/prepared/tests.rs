//! Real source-relative admission; no forged CheckedBundle or cloned backend.
use super::*;
use crate::artifact::{
    ArtifactFailure, FormatError, hex,
    inputs::{
        admission::{DECODE_COUNT, IMPORT_COUNT},
        tests::Case,
    },
    material::VERIFIER_IMPORTS,
};
use serde_json::json;
use zkc_arkworks::Keys;
use zkc_backends::Policy;
use zkc_runtime::interactive::{Backend, Value as RuntimeValue};

fn installation() -> CheckerInstallation {
    CheckerInstallation::new(
        zkc_test_support::compiler().display().to_string(),
        zkc_test_support::checker("interactive-protocol")
            .display()
            .to_string(),
    )
}
fn inputs(json: &Json) -> InvocationInputs {
    InvocationInputs::from_slice(&serde_json::to_vec(json).unwrap()).unwrap()
}
fn counters() {
    IMPORT_COUNT.set(0);
    VERIFIER_IMPORTS.set(0);
    DECODE_COUNT.set(0);
}
fn binding_error<T>(r: Result<T, InvocationError>) -> String {
    match r.err().expect("must fail") {
        InvocationError::Binding(s) => s,
        error => panic!("wrong error: {error}"),
    }
}

#[test]
fn bounded_input_boundary_rejects_before_binding() {
    assert_eq!(
        InvocationInputs::from_slice(&[b'['; 66]).err().unwrap(),
        "artifact-json-depth"
    );
    assert_eq!(
        InvocationInputs::from_slice(b"{}").err().unwrap(),
        "artifact-json-kind"
    );
    assert_eq!(
        InvocationInputs::from_slice(&vec![b' '; io::INPUT_LIMIT + 1])
            .err()
            .unwrap(),
        "artifact-byte-limit"
    );
    assert!(InvocationInputs::read("/nonexistent/prepared-inputs.json").is_err());
}

#[test]
fn repeated_success_failure_recovery_and_actual_binding() {
    let case = Case::new(1, 1, 0);
    let installation = installation();
    let options = InvocationOptions::new(0);
    let producer = inputs(&case.input);
    let mut val = case.input.clone();
    val[3] = json!([]);
    let validator = inputs(&val);
    let mut prepared = installation.prepare_checked(case.bundle, CacheLimits::default());
    counters();
    let first = prepared.produce(&installation, &producer, options).unwrap();
    let proof = first.execution.outcome.unwrap();
    let retained = prepared.cache_usage();
    assert_eq!(retained.entries, 2); // one VK and one PK, never the table witness
    assert_eq!((IMPORT_COUNT.get(), VERIFIER_IMPORTS.get()), (1, 1));
    let decodes = DECODE_COUNT.get();
    for _ in 0..3 {
        let p = prepared
            .produce(&installation.clone(), &producer, options)
            .unwrap();
        assert!(p.execution.outcome.is_ok());
        assert_eq!(p.binding, first.binding);
        assert_eq!(p.usage, first.usage); // complete fresh accounting every time
        let v = prepared
            .validate(&installation, &validator, &proof, options)
            .unwrap();
        assert!(v.execution.outcome.is_ok());
        assert_eq!(prepared.cache_usage(), retained);
    }
    assert_eq!((IMPORT_COUNT.get(), VERIFIER_IMPORTS.get()), (1, 1));
    assert!(DECODE_COUNT.get() > decodes); // private wire data is decoded every call
    let malformed = prepared
        .validate(&installation, &validator, b"bad", options)
        .unwrap();
    assert!(matches!(
        malformed.execution.outcome,
        Err(ArtifactFailure::Format(_))
    ));

    // Context and statement mutations rebind; neither can validate an old proof.
    for index in [1, 2] {
        let mut changed = val.clone();
        if index == 1 {
            changed[1] = json!("01");
        } else {
            let wire = changed[2][0][2].as_str().unwrap();
            changed[2][0][2] = json!(format!("{}00", &wire[..wire.len() - 2]));
        }
        let changed = inputs(&changed);
        let r = prepared
            .validate(&installation, &changed, &proof, options)
            .unwrap();
        assert_ne!(r.binding, first.binding);
        assert!(matches!(
            r.execution.outcome,
            Err(ArtifactFailure::Format(FormatError::Header))
        ));
    }
    let mut bad = case.input.clone();
    bad[3][1][2] = json!("00"); // malformed private table
    assert!(
        prepared
            .produce(&installation, &inputs(&bad), options)
            .is_err()
    );
    let mut changed = case.input.clone();
    let wire = changed[2][0][2].as_str().unwrap();
    changed[2][0][2] = json!(format!("{}00", &wire[..wire.len() - 2]));
    let rejected_proof = prepared
        .produce(&installation, &inputs(&changed), options)
        .unwrap()
        .execution
        .outcome
        .unwrap();
    changed[3] = json!([]);
    let rejected = prepared
        .validate(&installation, &inputs(&changed), &rejected_proof, options)
        .unwrap();
    assert!(matches!(
        rejected.execution.outcome,
        Err(ArtifactFailure::Rejected)
    ));
    assert!(
        prepared
            .validate(&installation, &validator, &proof, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
    assert_eq!(prepared.cache_usage(), retained);
}

#[test]
fn captured_key_bytes_pin_vk_and_configuration_never_alias() {
    let case = Case::new(1, 0, 0);
    let installation = installation();
    let mut prepared = installation.prepare_checked(case.bundle, CacheLimits::default());
    let options = InvocationOptions::new(0);
    let input = inputs(&case.input);
    counters();
    prepared.bind(&installation, &input, options, true).unwrap();
    let retained = prepared.cache_usage();
    let path = case.input[3][0][2].as_str().unwrap();
    let original = std::fs::read(path).unwrap();
    let mut bad = original.clone();
    bad.push(0);
    std::fs::write(path, &bad).unwrap();
    assert_eq!(
        binding_error(prepared.bind(&installation, &input, options, true)),
        "invalid-encoding"
    );
    assert_eq!(prepared.cache_usage(), retained); // no partially validated entry
    std::fs::remove_file(path).unwrap();
    assert_eq!(
        binding_error(prepared.bind(&installation, &input, options, true)),
        "artifact-io"
    );
    std::fs::write(path, &original).unwrap();
    let alias = case.dir.path().join("alias.pk");
    std::fs::write(&alias, &original).unwrap();
    let mut changed = case.input.clone();
    changed[3][0][2] = json!(alias);
    prepared
        .bind(&installation, &inputs(&changed), options, true)
        .unwrap();
    assert_eq!(IMPORT_COUNT.get(), 2); // initial import and rejected trailing byte
    changed[3][0][3] = json!("00".repeat(32));
    assert_eq!(
        binding_error(prepared.bind(&installation, &inputs(&changed), options, true)),
        "key-mismatch"
    );
    let keys = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    changed = case.input.clone();
    changed[4][1][0][2] = json!(hex(&keys
        .verifier_key()
        .to_bytes(&Policy::default().ark_bounds())
        .unwrap()));
    assert_eq!(
        binding_error(prepared.bind(&installation, &inputs(&changed), options, true)),
        "key-mismatch"
    );
    let old_binding = prepared
        .bind(&installation, &input, options, true)
        .unwrap()
        .binding;
    changed[3] = json!([]);
    let new_binding = prepared
        .bind(&installation, &inputs(&changed), options, false)
        .unwrap()
        .binding;
    assert_ne!(old_binding, new_binding);
    changed[4][1][0][2] = json!("00");
    assert_eq!(
        binding_error(prepared.bind(&installation, &inputs(&changed), options, false)),
        "artifact-verifier-key"
    );
    changed = case.input.clone();
    changed[4][1][0][0] = json!("wrong-port");
    assert_eq!(
        binding_error(prepared.bind(&installation, &inputs(&changed), options, true)),
        "artifact-configuration-order"
    );
    assert!(
        prepared
            .produce(&installation, &input, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
}

#[test]
fn fresh_capability_authority_and_installation_epoch() {
    let case = Case::new(0, 0, 0);
    let installation = installation();
    let input = inputs(&case.input);
    let mut prepared = installation.prepare_checked(case.bundle, CacheLimits::default());
    let options = InvocationOptions::new(17);
    let first = prepared.bind(&installation, &input, options, true).unwrap();
    let second = prepared
        .bind(&installation, &input, InvocationOptions::new(3), true)
        .unwrap();
    assert_eq!(first.binding, second.binding);
    for (_, token) in &first.resources {
        assert_eq!(first.backend.observe(token).unwrap().budget, 17);
        assert_eq!(
            second.backend.observe(token).unwrap_err().code,
            "refused:capability-authority"
        );
        assert_eq!(
            second
                .backend
                .validate_value(&Value::Transcript(token.clone()))
                .unwrap_err()
                .code,
            "refused:capability-authority"
        );
    }
    for (_, token) in &second.resources {
        let observation = second.backend.observe(token).unwrap();
        assert_eq!((observation.budget, observation.draw_count), (3, 0));
    }
    let different = CheckerInstallation::new(&installation.0.compiler, &installation.0.lean);
    assert!(matches!(
        prepared.produce(&different, &input, options),
        Err(InvocationError::InstallationMismatch)
    ));
    assert!(
        prepared
            .produce(&installation, &input, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
}

#[test]
fn cache_hits_preserve_exact_input_budgets_and_runtime_charges() {
    let case = Case::new(2, 0, 0);
    let installation = installation();
    let pk_len = std::fs::metadata(case.input[3][0][2].as_str().unwrap())
        .unwrap()
        .len() as usize;
    let vk_len = case.input[4][1][0][2].as_str().unwrap().len() / 2;
    let pool = 2 * case.key_charge + 1024;
    let options = InvocationOptions {
        value_budget: ValueBudget::default(),
        transcript_budget: 0,
        trace: TraceMode::None,
        input_limits: InputLimits {
            bytes: pool,
            values: 4,
            work: vk_len + pool + 7 + 2 * pk_len,
        },
    };
    let input = inputs(&case.input);
    let mut prepared = installation.prepare_checked(case.bundle, CacheLimits::default());
    counters();
    let first = prepared.produce(&installation, &input, options).unwrap();
    let warm = prepared.produce(&installation, &input, options).unwrap();
    assert!(first.execution.outcome.is_ok() && warm.execution.outcome.is_ok());
    assert_eq!(first.usage, warm.usage);
    assert!(warm.usage.total_value_bytes >= 2 * case.key_charge);
    assert!(warm.events.is_none());
    assert_eq!(IMPORT_COUNT.get(), 1);
    let tiny = InvocationOptions {
        value_budget: ValueBudget {
            live_bytes: 0,
            total_bytes: 0,
        },
        ..options
    };
    // Zero budget is exhausted while installing the initial frame, before
    // an executable run/report exists.
    assert!(matches!(prepared.produce(&installation, &input, tiny),
        Err(InvocationError::Runtime(code)) if code == "Limit"));
    let recovered = prepared.produce(&installation, &input, options).unwrap();
    assert!(recovered.execution.outcome.is_ok());
    assert_eq!(recovered.usage, first.usage);
    for (limits, code) in [
        (
            InputLimits {
                bytes: pool - 1,
                ..options.input_limits
            },
            "artifact-input-bytes-limit",
        ),
        (
            InputLimits {
                values: 3,
                ..options.input_limits
            },
            "artifact-input-count-limit",
        ),
        (
            InputLimits {
                work: options.input_limits.work - 1,
                ..options.input_limits
            },
            "artifact-input-work-limit",
        ),
    ] {
        assert_eq!(
            binding_error(prepared.produce(
                &installation,
                &input,
                InvocationOptions {
                    input_limits: limits,
                    ..options
                }
            )),
            code
        );
        assert_eq!(IMPORT_COUNT.get(), 1);
    }
    assert!(
        prepared
            .produce(&installation, &input, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
}

#[test]
fn cache_capacity_skip_clear_and_disabled_reuse_are_bounded() {
    let case = Case::new(1, 0, 0);
    let installation = installation();
    let input = inputs(&case.input);
    let mut prepared = installation.prepare_checked(case.bundle, CacheLimits::default());
    let options = InvocationOptions::new(0);
    prepared.bind(&installation, &input, options, true).unwrap();
    let exact = prepared.cache_usage();
    for (limits, entries) in [
        (
            CacheLimits {
                entries: 2,
                bytes: exact.bytes,
            },
            2,
        ),
        (
            CacheLimits {
                entries: 2,
                bytes: exact.bytes - 1,
            },
            1,
        ),
        (
            CacheLimits {
                entries: 1,
                bytes: usize::MAX,
            },
            1,
        ),
        (
            CacheLimits {
                entries: usize::MAX,
                bytes: 0,
            },
            0,
        ),
    ] {
        prepared.cache = MaterialCache::new(limits);
        counters();
        for _ in 0..4 {
            let bound = prepared.bind(&installation, &input, options, true).unwrap();
            assert_eq!(prepared.cache_usage().entries, entries);
            assert!(prepared.cache_usage().bytes <= limits.bytes);
            assert!(
                bound
                    .values
                    .iter()
                    .map(RuntimeValue::retained_bytes)
                    .sum::<usize>()
                    >= case.key_charge
            );
        }
        assert_eq!(IMPORT_COUNT.get(), if entries == 2 { 1 } else { 4 });
        prepared.clear_cache();
        assert_eq!(prepared.cache_usage(), CacheUsage::default());
    }
}

#[test]
fn real_nonce_rng_transcript_isolation_exhaustion_and_frozen_custody() {
    use crate::artifact::inputs::tests::{compile, write};
    use zkc_backends::{Domain, EntryPolicy, GroupPoint, PublicInputs, Scalar};
    let installation = installation();
    // A temporary directory rather than the run's evidence, because this case
    // removes it: what it checks is that the checked program does not change
    // when the files it was loaded from go away.
    let dir = tempfile::tempdir().unwrap();
    let source: Json =
        serde_json::from_str(include_str!("../../../tests/fixtures/artifact/dleq.json")).unwrap();
    let descriptor: Json = serde_json::from_str(include_str!(
        "../../../tests/fixtures/artifact/dleq.construction.json"
    ))
    .unwrap();
    let source = write(dir.path(), "source.json", &source);
    let descriptor = write(dir.path(), "descriptor.json", &descriptor);
    let construction = compile(
        &installation.0.compiler,
        &["protocol-construct", &source, &descriptor],
    );
    let common = write(dir.path(), "common.json", &construction[2]);
    let physical = compile(&installation.0.compiler, &["protocol-compile", &common]);
    let construction = write(dir.path(), "construction.json", &construction);
    let physical = write(dir.path(), "physical.json", &physical);
    let paths = || ArtifactPaths {
        source: &source,
        descriptor: &descriptor,
        construction: &construction,
        participants: &physical,
    };
    let mut prepared = installation
        .prepare(paths(), CacheLimits::default())
        .unwrap();
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("fixture", "fixture", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let wire = |v: Value| hex(&backend.encode_value(&v).unwrap());
    let g = GroupPoint::generator();
    let h = g.scale(Scalar::from(7));
    let x = Scalar::from(11);
    let mut input = json!([
        "zkc.artifact-inputs/1",
        "00",
        [
            ["base_0", "group:bls12-381.g1", wire(Value::Curve(g))],
            ["base_1", "group:bls12-381.g1", wire(Value::Curve(h))],
            [
                "image_0",
                "group:bls12-381.g1",
                wire(Value::Curve(g.scale(x)))
            ],
            [
                "image_1",
                "group:bls12-381.g1",
                wire(Value::Curve(h.scale(x)))
            ],
        ],
        [
            ["x", "field:bls12-381.fr", wire(Value::Field(x))],
            ["nonce_first", "nonce", "2"],
            ["nonce_second", "nonce", "2"]
        ],
        ["zkc.public-configuration/1", [], [], []]
    ]);
    let producer = inputs(&input);
    let mut val = input.clone();
    val[3] = json!([]);
    let validator = inputs(&val);
    let options = InvocationOptions::new(10);
    let mut kinds = std::collections::BTreeSet::new();
    for (input, role) in [(&producer, true), (&validator, false)] {
        let a = prepared.bind(&installation, input, options, role).unwrap();
        let b = prepared.bind(&installation, input, options, role).unwrap();
        for value in &a.values {
            if let Value::Nonce(t) | Value::Rng(t) | Value::Transcript(t) = value {
                kinds.insert(value.ty());
                let observation = a.backend.observe(t).unwrap();
                assert_eq!(observation.draw_count, 0);
                assert_eq!(
                    b.backend.validate_value(value).unwrap_err().code,
                    "refused:capability-authority"
                );
            }
        }
    }
    assert_eq!(kinds.len(), 3); // nonce, RNG and transcript all tested
    let first = prepared
        .produce(&installation, &producer, options)
        .unwrap()
        .execution
        .outcome
        .unwrap();
    let second = prepared
        .produce(&installation, &producer, options)
        .unwrap()
        .execution
        .outcome
        .unwrap();
    assert_ne!(first, second); // independent production OS randomness
    for proof in [&first, &second] {
        assert!(
            prepared
                .validate(&installation, &validator, proof, options)
                .unwrap()
                .execution
                .outcome
                .is_ok()
        );
    }
    // Fail after some genuine transitions; the next invocation remains fresh.
    let short = InvocationOptions::new(9);
    for failure in [
        prepared
            .produce(&installation, &producer, short)
            .unwrap()
            .execution
            .outcome
            .map(|_| ()),
        prepared
            .validate(&installation, &validator, &first, short)
            .unwrap()
            .execution
            .outcome,
    ] {
        match failure {
            Err(ArtifactFailure::Stopped(stop)) => assert!(matches!(stop.kind,
                zkc_runtime::interactive::StopKind::Backend(ref e) if e.code == "exhausted:resource-budget")),
            _ => panic!("expected transcript budget exhaustion"),
        }
    }
    input[3][1][2] = json!("0");
    assert!(
        prepared
            .produce(&installation, &inputs(&input), options)
            .unwrap()
            .execution
            .outcome
            .is_err()
    );
    let mut bad = first.clone();
    bad[54..102].fill(0xff); // malformed first G1 message
    assert!(matches!(
        prepared
            .validate(&installation, &validator, &bad, options)
            .unwrap()
            .execution
            .outcome,
        Err(ArtifactFailure::Backend(_))
    ));
    // Replacing custody paths cannot change the immutable checked program.
    std::fs::write(&source, b"[]").unwrap();
    assert!(
        installation
            .prepare(paths(), CacheLimits::default())
            .is_err()
    );
    dir.close().unwrap();
    assert!(
        prepared
            .produce(&installation, &producer, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
    assert!(
        prepared
            .validate(&installation, &validator, &first, options)
            .unwrap()
            .execution
            .outcome
            .is_ok()
    );
    assert_eq!(prepared.cache_usage(), CacheUsage::default());
}
