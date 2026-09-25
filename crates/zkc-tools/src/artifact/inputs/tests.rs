//! Actual CheckedBundle admission and binding with small budgets and load counters.
//! The compiler and the Lean checker are resolved by name; no synthetic or
//! mutated CheckedBundle and no mock backend is used.
use super::*;
use admission::{DECODE_COUNT, IMPORT_COUNT};
use std::{path::Path, process::Command, sync::Arc};
use zkc_arkworks::{Keys, Scalar};
use zkc_runtime::interactive::{Runner, Value as RuntimeValue};

pub(in crate::artifact) struct Case {
    pub(in crate::artifact) bundle: CheckedBundle,
    pub(in crate::artifact) input: Json,
    pub(in crate::artifact) dir: zkc_test_support::Evidence,
    pub(in crate::artifact) key_charge: usize,
}
pub(in crate::artifact) fn write(dir: &Path, name: &str, value: &Json) -> String {
    let path = dir.join(name);
    std::fs::write(&path, serde_json::to_vec(value).unwrap()).unwrap();
    path.to_str().unwrap().to_owned()
}
pub(in crate::artifact) fn compile(compiler: &str, args: &[&str]) -> Json {
    let output = Command::new(compiler).args(args).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}
impl Case {
    pub(in crate::artifact) fn new(key_count: usize, tables: usize, public_targets: usize) -> Self {
        let compiler = zkc_test_support::compiler().display().to_string();
        let lean = zkc_test_support::checker("interactive-protocol")
            .display()
            .to_string();
        let dir = zkc_test_support::evidence(module_path!());
        let policy = Policy::default();
        let keys = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(
                Domain::new("fixture", "s", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .unwrap();
        let table = Value::table(&[Scalar::from(1), Scalar::from(2)], &policy).unwrap();
        let table_hex = hex(&backend.encode_value(&table).unwrap());
        let mut ports = vec![
            json!(["ok", "V", "bool"]),
            json!(["coins", "V", "rng:bls12-381.fr"]),
        ];
        let mut config = vec![];
        let mut fixed = vec![];
        if key_count > 0 {
            ports.push(json!([
                "vk",
                "V",
                "verifier_key:multilinear.kzg.bls12-381/1"
            ]));
            config.push(json!([
                "vk",
                "verifier_key:multilinear.kzg.bls12-381/1",
                hex(&keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap())
            ]));
            let path = dir.path().join("material.pk");
            std::fs::write(
                &path,
                keys.prover_key().to_bytes(&policy.ark_bounds()).unwrap(),
            )
            .unwrap();
            for i in 0..key_count {
                ports.push(json!([
                    format!("pk{i}"),
                    "P",
                    "prover_key:multilinear.kzg.bls12-381/1"
                ]));
                fixed.push(json!([
                    format!("pk{i}"),
                    "prover_key_file",
                    path,
                    hex(&keys.prover_key().material_fingerprint()),
                    "vk"
                ]));
            }
        }
        for i in 0..tables {
            ports.push(json!([format!("t{i}"), "P", "table:bls12-381.fr"]));
            fixed.push(json!([format!("t{i}"), "table:bls12-381.fr", table_hex]));
        }
        let mut targets = vec![];
        for i in 0..public_targets {
            ports.push(json!([format!("public{i}"), "P", "table:bls12-381.fr"]));
            targets.push(json!(["P", format!("public{i}")]));
        }
        let mut declarations = vec![json!(["ok", [["V", "ok"]]])];
        let mut public = vec![json!([
            "ok",
            "bool",
            hex(&backend.encode_value(&Value::Bool(true)).unwrap())
        ])];
        if !targets.is_empty() {
            declarations.push(json!(["data", targets]));
            public.push(json!(["data", "table:bls12-381.fr", table_hex]));
        }
        let source = json!([
            "zkc.protocol/1",
            [],
            [[
                "function",
                "Accept",
                [["ok", "bool"]],
                ["bool"],
                [["return", ["ok"]]],
                ["Accept", []]
            ]],
            [[
                "protocol",
                "NoDraw",
                ["P", "V"],
                [],
                ports,
                [["V", "bool"], ["V", "rng:bls12-381.fr"]],
                [],
                [
                    ["local", "accept", "V", "Accept", ["ok"], ["accepted"]],
                    ["return", ["accepted", "coins"]]
                ]
            ]],
            [[
                "instance",
                "root",
                "NoDraw",
                [],
                [],
                [["P", "P"], ["V", "V"]]
            ]],
            [["entry", "main", "root"]]
        ]);
        let descriptor = json!([
            "zkc.construction/1",
            "main",
            "P",
            "V",
            declarations,
            ["coins", []],
            "0",
            "merlin3.bls12-381.fr64be/1",
            "exact"
        ]);
        let source = write(dir.path(), "source.json", &source);
        let descriptor = write(dir.path(), "descriptor.json", &descriptor);
        let construction = compile(&compiler, &["protocol-construct", &source, &descriptor]);
        let common = write(dir.path(), "common.json", &construction[2]);
        let physical = compile(&compiler, &["protocol-compile", &common]);
        let construction = write(dir.path(), "construction.json", &construction);
        let physical = write(dir.path(), "physical.json", &physical);
        let bundle = CheckedBundle::load(
            &source,
            &descriptor,
            &construction,
            &physical,
            &compiler,
            &lean,
        )
        .unwrap();
        let input = json!([
            "zkc.artifact-inputs/1",
            "00",
            public,
            fixed,
            ["zkc.public-configuration/1", config, [], []]
        ]);
        Self {
            bundle,
            input,
            dir,
            key_charge: Value::key_retained_bytes(Type::ProverKey, keys.verifier_key()).unwrap(),
        }
    }
    fn bind(&self, limits: LoadLimits) -> Result<BoundInputs> {
        IMPORT_COUNT.with(|n| n.set(0));
        DECODE_COUNT.with(|n| n.set(0));
        self.bundle
            .bind_with_limits(&self.input, &self.bundle.role(true).unwrap(), 0, limits)
    }
    fn error(&self, limits: LoadLimits) -> String {
        self.bind(limits).err().expect("must refuse")
    }
}

#[test]
fn host_preflight_refuses_aggregate_before_nonexistent_pk_file() {
    let mut case = Case::new(3, 0, 0);
    for r in case.input[3].as_array_mut().unwrap() {
        r[2] = json!(case.dir.path().join("does-not-exist.pk"));
    }
    assert_eq!(
        case.error(LoadLimits {
            bytes: case.key_charge * 2 + 1024,
            ..LoadLimits::default()
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!(IMPORT_COUNT.get(), 0);
    assert_eq!(DECODE_COUNT.get(), 0);
    // A sufficient budget reaches the named path and fails the I/O contract.
    assert_eq!(case.error(LoadLimits::default()), "artifact-io");
}

#[test]
fn host_reuses_matching_imports_and_runner_charges_every_operand() {
    let mut case = Case::new(3, 0, 0);
    let second = case.dir.path().join("same-bytes-different-path.pk");
    std::fs::copy(case.input[3][0][2].as_str().unwrap(), &second).unwrap();
    case.input[3][1][2] = json!(second);
    let bound = case.bind(LoadLimits::default()).unwrap();
    assert_eq!(IMPORT_COUNT.get(), 1);
    let keys: Vec<_> = bound
        .values
        .iter()
        .filter_map(|v| {
            if let Value::ProverKey(k) = v {
                Some(k)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(keys.len(), 3);
    assert!(Arc::ptr_eq(keys[0], keys[1]) && Arc::ptr_eq(keys[1], keys[2]));
    let charged: usize = bound.values.iter().map(RuntimeValue::retained_bytes).sum();
    assert!(charged >= 3 * case.key_charge);
    let runner = Runner::new(
        &case.bundle.admitted,
        &case.bundle.entry,
        &case.bundle.producer,
        "artifact",
        bound.backend,
        bound.values,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    assert_eq!(runner.usage().live_value_bytes, charged);
    assert_eq!(
        case.error(LoadLimits {
            bytes: 2 * case.key_charge + 1024,
            ..LoadLimits::default()
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!(IMPORT_COUNT.get(), 0);
}

#[test]
fn host_different_path_same_claimed_pin_still_authenticates_bytes() {
    let mut case = Case::new(2, 0, 0);
    let wrong = case.dir.path().join("wrong.pk");
    let mut bytes = std::fs::read(case.input[3][0][2].as_str().unwrap()).unwrap();
    bytes.push(0); // valid material plus forbidden trailing byte
    std::fs::write(&wrong, bytes).unwrap();
    case.input[3][1][2] = json!(wrong);
    assert_eq!(case.error(LoadLimits::default()), "invalid-encoding");
    assert_eq!(IMPORT_COUNT.get(), 2);
    std::fs::remove_file(&wrong).unwrap();
    assert_eq!(case.error(LoadLimits::default()), "artifact-io");
    assert_eq!(IMPORT_COUNT.get(), 1);
    // Same path and bytes but a different claimed pin cannot hit the cache.
    case.input[3][1][2] = case.input[3][0][2].clone();
    case.input[3][1][3] = json!("00".repeat(32));
    assert_eq!(case.error(LoadLimits::default()), "key-mismatch");
    assert_eq!(IMPORT_COUNT.get(), 2);
}

#[test]
fn host_bounds_fixed_decoded_tables_and_reuses_canonical_wire() {
    let case = Case::new(0, 4, 0);
    assert_eq!(
        case.error(LoadLimits {
            bytes: 1024,
            ..LoadLimits::default()
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!(DECODE_COUNT.get(), 0);
    let bound = case.bind(LoadLimits::default()).unwrap();
    assert_eq!(DECODE_COUNT.get(), 2); // one bool and one table, not four tables
    let tables: Vec<_> = bound
        .values
        .iter()
        .filter_map(|v| {
            if let Value::Table(t) = v {
                Some(t)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(tables.len(), 4);
    assert!(tables.windows(2).all(|t| Arc::ptr_eq(t[0], t[1])));
}

#[test]
fn host_bounds_public_target_amplification_before_decode() {
    let mut case = Case::new(0, 0, 8);
    // Pool is only bool+table+transcript (1,344 bytes). Repeated source
    // operands must independently exceed the 2 KiB entry budget.
    assert_eq!(
        case.error(LoadLimits {
            bytes: 2048,
            ..LoadLimits::default()
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!(DECODE_COUNT.get(), 0);
    case.input[3] = json!([["public0", "table:bls12-381.fr", case.input[2][1][2]]]);
    assert!(case.bind(LoadLimits::default()).is_ok());
    assert_eq!(DECODE_COUNT.get(), 2); // fixed public equality needs no second decode
    case.input[3][0][2] = json!("00");
    assert_eq!(
        case.error(LoadLimits::default()),
        "artifact-public-equality"
    );
}

#[test]
fn host_bounds_cumulative_loading_work_and_count() {
    let case = Case::new(2, 0, 0);
    assert_eq!(
        case.error(LoadLimits {
            work: 1,
            ..LoadLimits::default()
        }),
        "artifact-input-work-limit"
    );
    assert_eq!(IMPORT_COUNT.get(), 0);
    assert_eq!(
        case.error(LoadLimits {
            values: 1,
            ..LoadLimits::default()
        }),
        "artifact-input-count-limit"
    );
    let pk_len = std::fs::metadata(case.input[3][0][2].as_str().unwrap())
        .unwrap()
        .len() as usize;
    let vk_len = case.input[4][1][0][2].as_str().unwrap().len() / 2;
    // All known work plus one complete PK read: the second read is refused
    // even though its immutable parsed material would be a cache hit.
    let work = vk_len + 2 * case.key_charge + 1024 + 7 + pk_len;
    assert_eq!(
        case.error(LoadLimits {
            work,
            ..LoadLimits::default()
        }),
        "artifact-input-work-limit"
    );
    assert_eq!(IMPORT_COUNT.get(), 1);
}

#[test]
fn exact_pool_entry_work_and_value_boundaries_use_real_binding() {
    let case = Case::new(2, 0, 0);
    let pk_len = std::fs::metadata(case.input[3][0][2].as_str().unwrap())
        .unwrap()
        .len() as usize;
    let vk_len = case.input[4][1][0][2].as_str().unwrap().len() / 2;
    let pool = 2 * case.key_charge + 1024;
    let work = vk_len + pool + 7 + 2 * pk_len;
    let limits = LoadLimits {
        bytes: pool,
        work,
        values: 4,
    };
    let bound = case.bind(limits).unwrap();
    assert_eq!(bound.values.len(), 4);
    assert_eq!(IMPORT_COUNT.get(), 1);
    assert_eq!(DECODE_COUNT.get(), 1);
    assert_eq!(
        case.error(LoadLimits {
            bytes: pool - 1,
            ..limits
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!((IMPORT_COUNT.get(), DECODE_COUNT.get()), (0, 0));
    assert_eq!(
        case.error(LoadLimits {
            work: work - 1,
            ..limits
        }),
        "artifact-input-work-limit"
    );
    assert_eq!(IMPORT_COUNT.get(), 1);
    assert_eq!(
        case.error(LoadLimits {
            values: 3,
            ..limits
        }),
        "artifact-input-count-limit"
    );
    assert_eq!((IMPORT_COUNT.get(), DECODE_COUNT.get()), (0, 0));
    let public = Case::new(0, 0, 8);
    let entry = 8 * (256 + 64) + 1024;
    assert!(
        public
            .bind(LoadLimits {
                bytes: entry,
                ..LoadLimits::default()
            })
            .is_ok()
    );
    assert_eq!(
        public.error(LoadLimits {
            bytes: entry - 1,
            ..LoadLimits::default()
        }),
        "artifact-input-bytes-limit"
    );
    assert_eq!((IMPORT_COUNT.get(), DECODE_COUNT.get()), (0, 0));
}

#[test]
fn binding_cache_is_scoped_to_each_call_and_does_not_confuse_types() {
    let mut case = Case::new(1, 0, 0);
    assert!(case.bind(LoadLimits::default()).is_ok());
    assert_eq!(IMPORT_COUNT.get(), 1);
    let path = case.input[3][0][2].as_str().unwrap();
    let mut material = std::fs::read(path).unwrap();
    material.push(0);
    std::fs::write(path, &material).unwrap();
    assert_eq!(case.error(LoadLimits::default()), "invalid-encoding");
    assert_eq!(IMPORT_COUNT.get(), 1);
    case.input[3][0][3] = json!("00".repeat(32));
    assert!(case.bind(LoadLimits::default()).is_err());
}
