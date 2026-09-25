//! Explicit development fixture export; neither real artifact command calls it.
use serde_json::{Value as Json, json};
use std::{path::Path, sync::Arc};
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, Keys, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_tools::artifact::hex;
fn write(dir: &Path, name: &str, value: &Json) {
    std::fs::write(dir.join(name), serde_json::to_vec_pretty(value).unwrap()).unwrap();
}
fn main() {
    let dir = std::env::args()
        .nth(1)
        .expect("usage: artifact_fixture OUTPUT_DIRECTORY");
    let dir = Path::new(&dir);
    std::fs::create_dir_all(dir).unwrap();
    let policy = Policy::default();
    let b = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("fixture", "fixture", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let wire = |v: &Value| hex(&b.encode_value(v).unwrap());
    let g = GroupPoint::generator();
    let h = g.scale(Scalar::from(7));
    let x = Scalar::from(11);
    let publics = json!([
        ["base_0", "group:bls12-381.g1", wire(&Value::Curve(g))],
        ["base_1", "group:bls12-381.g1", wire(&Value::Curve(h))],
        [
            "image_0",
            "group:bls12-381.g1",
            wire(&Value::Curve(g.scale(x)))
        ],
        [
            "image_1",
            "group:bls12-381.g1",
            wire(&Value::Curve(h.scale(x)))
        ]
    ]);
    write(
        dir,
        "dleq.producer.json",
        &json!([
            "zkc.artifact-inputs/1",
            "61727469666163742d74657374",
            publics,
            [
                ["x", "field:bls12-381.fr", wire(&Value::Field(x))],
                ["nonce_first", "nonce", "2"],
                ["nonce_second", "nonce", "2"]
            ],
            ["zkc.public-configuration/1", [], [], []]
        ]),
    );
    write(
        dir,
        "dleq.validator.json",
        &json!([
            "zkc.artifact-inputs/1",
            "61727469666163742d74657374",
            publics,
            [],
            ["zkc.public-configuration/1", [], [], []]
        ]),
    );
    let keys = Keys::setup_for_development(3, &policy.ark_bounds()).unwrap();
    let f = Value::table(&(1..=8).map(Scalar::from).collect::<Vec<_>>(), &policy).unwrap();
    let g = Value::table(&(9..=16).map(Scalar::from).collect::<Vec<_>>(), &policy).unwrap();
    let (Value::Table(ft), Value::Table(gt)) = (&f, &g) else {
        unreachable!()
    };
    let fc = keys.prover_key().commit(ft).unwrap();
    let gc = keys.prover_key().commit(gt).unwrap();
    let public = json!([
        [
            "claim",
            "field:bls12-381.fr",
            wire(&Value::Field(ft.product_boolean_sum(gt).unwrap()))
        ],
        [
            "expected_f",
            "commitment:multilinear.kzg.bls12-381/1",
            wire(&Value::Commitment(Arc::new(fc.commitment().clone())))
        ],
        [
            "expected_g",
            "commitment:multilinear.kzg.bls12-381/1",
            wire(&Value::Commitment(Arc::new(gc.commitment().clone())))
        ]
    ]);
    let config = json!([
        "zkc.public-configuration/1",
        [[
            "vk",
            "verifier_key:multilinear.kzg.bls12-381/1",
            hex(&keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap())
        ]],
        [["V", "expected_f", "vk"], ["V", "expected_g", "vk"]],
        // Which setup each received commitment or opening proof is read under.
        // A site can be read under any key the configuration carries, so the
        // configuration says which, the way it already does for the expected
        // roots above; nothing infers it from the artifact.
        [
            ["interactive", "V", "root_f", "vk"],
            ["interactive", "V", "root_g", "vk"],
            ["opening", "V", "proof_message", "vk"]
        ]
    ]);
    let pk = dir.join("development.pk");
    std::fs::write(
        &pk,
        keys.prover_key().to_bytes(&policy.ark_bounds()).unwrap(),
    )
    .unwrap();
    let pk = pk.canonicalize().unwrap();
    write(
        dir,
        "committed-two-factor.producer.json",
        &json!([
            "zkc.artifact-inputs/1",
            "61727469666163742d74657374",
            public,
            [
                [
                    "pk",
                    "prover_key_file",
                    pk,
                    hex(&keys.prover_key().material_fingerprint()),
                    "vk"
                ],
                ["f", "table:bls12-381.fr", wire(&f)],
                ["g", "table:bls12-381.fr", wire(&g)]
            ],
            config
        ]),
    );
    write(
        dir,
        "committed-two-factor.validator.json",
        &json!([
            "zkc.artifact-inputs/1",
            "61727469666163742d74657374",
            public,
            [],
            config
        ]),
    );
    println!(
        "{}",
        json!({"status":"development-fixtures-written","directory":dir})
    );
}
