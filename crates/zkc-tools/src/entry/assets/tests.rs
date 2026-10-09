//! Packaged assets through the named run and proof Hosts. Native programs here
//! are hand-built carriers; the compiler's own packaging is checked elsewhere.
use crate::entry::{
    BindingPolicy, EntryError, EntryPhase, Package, ProofEntry, ProofOptions, ProofRequest,
    RoleInputs, RunEntry, RunRequest, SetupAuthority, Value,
};
use crate::execution::InputValue;
use crate::host::inputs::hash;
use crate::run::HostLimits;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc_backends::{KoalaBear, KoalaBearExt8, Value as Native};
use zkc_runtime::{
    interactive::{Identity, LogicalType, PhysicalType},
    logical,
    ring::{Expression, Node},
};

const BASE: &str = "koala-bear";
const EXTENSION: &str = "koala-bear.ext8-binomial3";
const ORIGINAL: &str = "module\n{}";

fn sha(text: &str) -> String {
    format!("{:x}", Sha256::digest(text.as_bytes()))
}
fn physical(logical: &str) -> String {
    PhysicalType::default_for(LogicalType::parse(logical).unwrap())
        .unwrap()
        .spelling()
}
/// Canonical arena text over two inputs with the selected combinations of
/// their product and sum as ordered outputs. Every node must be reachable.
fn arena(field: Identity, product: bool, sum: bool) -> String {
    let mut nodes = vec![Node::Input(0), Node::Input(1)];
    let mut outputs = Vec::new();
    if product {
        nodes.push(Node::Mul(0, 1));
        outputs.push(nodes.len() - 1);
    }
    if sum {
        nodes.push(Node::Add(0, 1));
        outputs.push(nodes.len() - 1);
    }
    Expression::new(vec![field; 2], nodes, outputs)
        .unwrap()
        .canonical()
}
/// Three distinct arenas: one on the executed path, one in a branch no
/// execution chooses, and one in a loop body that zero trips never enter.
struct Arenas {
    executed: String,
    branch: String,
    looped: String,
}
fn arenas(field: Identity) -> Arenas {
    Arenas {
        executed: arena(field, true, true),
        branch: arena(field, false, true),
        looped: arena(field, true, false),
    }
}
impl Arenas {
    fn pairs(&self) -> Vec<(String, String)> {
        [&self.executed, &self.branch, &self.looped]
            .into_iter()
            .map(|body| (sha(body), body.clone()))
            .collect()
    }
}
fn binding(name: &str, field: &str) -> Json {
    json!([name, "ring.point", [field], "plonky3/ring.point"])
}
/// `evaluate` substitutes the executed arena after a branch that is never
/// taken; `inner` runs only inside the participant's loop.
fn functions(field: &str, arenas: &Arenas) -> Json {
    let vector = physical(&format!("vector:{field}"));
    json!([
        [
            "function",
            "evaluate",
            [["x", vector]],
            [vector],
            [
                ["bool_constant", "choose", "never", false],
                [
                    "if",
                    "branch",
                    "never",
                    ["x"],
                    [
                        [
                            "op",
                            "hidden",
                            "branch_ring",
                            [sha(&arenas.branch)],
                            ["x"],
                            ["t"]
                        ],
                        ["yield", ["t"]]
                    ],
                    [["yield", ["x"]]],
                    ["chosen"]
                ],
                [
                    "op",
                    "evaluate",
                    "executed_ring",
                    [sha(&arenas.executed)],
                    ["chosen"],
                    ["r"]
                ],
                ["return", ["r"]]
            ],
            ["evaluate", []]
        ],
        [
            "function",
            "inner",
            [["x", vector]],
            [vector],
            [
                [
                    "op",
                    "inner",
                    "loop_ring",
                    [sha(&arenas.looped)],
                    ["x"],
                    ["r"]
                ],
                ["return", ["r"]]
            ],
            ["inner", []]
        ]
    ])
}
fn bindings(field: &str) -> Json {
    json!([
        binding("executed_ring", field),
        binding("branch_ring", field),
        binding("loop_ring", field)
    ])
}
fn run_program(field: &str, arenas: &Arenas) -> Json {
    let vector = physical(&format!("vector:{field}"));
    let index = physical("index");
    json!([
        "zkc.program/0",
        bindings(field),
        functions(field, arenas),
        [[
            "participant",
            "p",
            "root",
            "P",
            [["x", vector], ["rounds", index]],
            [vector],
            [
                ["local", "evaluate", "evaluate", ["x"], ["r"]],
                [
                    "loop",
                    "rounds",
                    ["value", "rounds", "8", "i"],
                    [],
                    ["x"],
                    [["local", "inner", "inner", ["x"], ["r2"]], ["yield", []]],
                    []
                ],
                ["return", ["r"]]
            ],
            []
        ]],
        [["entry", "Assets", [["P", "p"]]]]
    ])
}
fn run_bundle(program: &Json) -> String {
    json!({"format":"zkc.run/0","candidate":program.to_string(),"entry":"Assets","roles":["P"],
        "steps":[
            {"loop":[{"role":0,"instruction":0,"anchor":0},{"role":0,"instruction":1,"anchor":0}],
             "body":[{"role":0,"instruction":2,"anchor":1}],
             "yield":[{"role":0,"instruction":3,"anchor":null}]},
            {"role":0,"instruction":4,"anchor":null}]})
    .to_string()
}
fn schema(kind: &str, ty: &str, leaves: &[&str]) -> Json {
    json!({"kind":kind,"identity":sha(ty),"type":ty,"custody":false,
        "permissions":["Copy","Drop","Share","Wire"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn port(name: &str, index: u32, native: &[u32], roles: &[&str], schema: Json) -> Json {
    json!({"name":name,"index":index,"native":native,"roles":roles,"type":schema["type"],"schema":schema})
}
fn interface(protocol: Json, job: Json) -> Json {
    json!({"format":"zkc.language-interface/0","setups":[],"capture":sha("capture"),
        "original":sha(ORIGINAL),"toolchain":"test-toolchain","entry":"sample::Assets",
        "protocol":"Assets","protocols":[protocol],"relations":[],"job":job})
}
fn run_interface(field: &str) -> Json {
    let leaf = format!("vector:{field}");
    let vector = schema("builtin", &leaf, &[&leaf]);
    let index = schema("index", "index", &["index"]);
    interface(
        json!({"symbol":"Assets","roles":["P"],
            "inputs":[port("x",0,&[0],&["P"],vector.clone()), port("rounds",1,&[1],&["P"],index)],
            "outputs":[port("result",0,&[0],&["P"],vector)],"services":[],"clauses":[]}),
        json!({"kind":"run"}),
    )
}
/// Deliberately authorize a hand-built publication with its own digest. A
/// real client obtains the expected package identity independently.
fn package(interface: &Json, artifact: &str, assets: &[(String, String)]) -> Package {
    let mut assets = assets.to_vec();
    assets.sort();
    let frame =
        json!({"format":"zkc.entry/0","original":ORIGINAL,"interface":interface.to_string(),
        "artifact":artifact,"options":{"simplify":true,"release_storage":false},"assets":assets})
        .to_string();
    Package::capture(
        frame.as_bytes(),
        &Sha256::digest(frame.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
fn run_package(field: &str, arenas: &Arenas, assets: &[(String, String)]) -> Package {
    package(
        &run_interface(field),
        &run_bundle(&run_program(field, arenas)),
        assets,
    )
}
fn run_entry(package: Package) -> Result<RunEntry, EntryError> {
    RunEntry::admit(package, HostLimits::default(), SetupAuthority::default())
}
fn base_vector(values: &[u32]) -> Value {
    Native::KoalaBearVector(
        values
            .iter()
            .map(|v| KoalaBear::new(*v))
            .collect::<Vec<_>>()
            .into(),
    )
    .into()
}
fn extension_vector(values: &[u32]) -> Value {
    Native::KoalaBearExt8Vector(
        values
            .iter()
            .map(|v| KoalaBearExt8::from(KoalaBear::new(*v)))
            .collect::<Vec<_>>()
            .into(),
    )
    .into()
}
fn run_request(x: Value, rounds: u64) -> RunRequest {
    RunRequest {
        session: "assets".into(),
        roles: BTreeMap::from([(
            "P".into(),
            RoleInputs {
                inputs: BTreeMap::from([("x".into(), x), ("rounds".into(), rounds.into())]),
                services: BTreeMap::new(),
            },
        )]),
        setups: BTreeMap::new(),
    }
}
fn refused(result: Result<impl Sized, EntryError>, code: &str) {
    let error = result.err().expect("refusal");
    assert_eq!(error.phase, EntryPhase::Assets, "{error}");
    assert_eq!(error.code(), code);
}

#[test]
fn packaged_arenas_run_and_every_reachable_reference_is_checked_before_preparation() {
    let arenas = arenas(Identity::KoalaBear);
    let pairs = arenas.pairs();
    let entry = run_entry(run_package(BASE, &arenas, &pairs)).unwrap();
    let mut expected: Vec<_> = pairs.iter().map(|(d, _)| d.as_str()).collect();
    expected.sort_unstable();
    assert_eq!(entry.assets().identities().collect::<Vec<_>>(), expected);
    assert_eq!(
        entry
            .assets()
            .expression(&sha(&arenas.executed))
            .unwrap()
            .canonical(),
        arenas.executed
    );
    assert!(entry.assets().expression(&"0".repeat(64)).is_none());
    assert_eq!(
        entry
            .assets()
            .references()
            .iter()
            .map(|r| (r.function.as_str(), r.site.as_str(), r.identity.as_str()))
            .collect::<Vec<_>>(),
        [
            ("evaluate", "hidden", sha(&arenas.branch).as_str()),
            ("evaluate", "evaluate", sha(&arenas.executed).as_str()),
            ("inner", "inner", sha(&arenas.looped).as_str()),
        ]
    );
    assert!(
        entry
            .assets()
            .references()
            .iter()
            .all(|r| r.binding.declaration().contract == "ring.point")
    );
    assert_eq!(
        entry.assets().registry().identities().len(),
        entry.assets().identities().len()
    );
    // Zero loop trips: only the executed arena runs, and it runs on packaged
    // assets without any registry supplied by the caller.
    let report = entry
        .prepare(run_request(base_vector(&[3, 4]), 0))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{:?}", report.native.failure);
    let Value::Leaf(InputValue::Native(result)) = &report.outputs.as_ref().unwrap()["P"]["result"]
    else {
        panic!("vector result");
    };
    let Native::KoalaBearVector(values) = result.as_ref() else {
        panic!("KoalaBear vector result");
    };
    assert_eq!(values.as_ref(), [KoalaBear::new(12), KoalaBear::new(7)]);
    let work = |report: &crate::entry::RunReport| {
        report.native.execution.as_ref().unwrap().backends[0]
            .1
            .ring_work_spent()
    };
    let once = work(&report);
    assert!(once > 0);
    let looped = entry
        .prepare(run_request(base_vector(&[3, 4]), 2))
        .unwrap()
        .execute();
    assert!(looped.is_success());
    assert!(work(&looped) > once, "loop trips substitute the loop arena");
    // Omitting any arena refuses at admission, before any request exists,
    // including the arena behind the untaken branch and the zero-trip loop.
    for omitted in 0..pairs.len() {
        let remaining: Vec<_> = pairs
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != omitted)
            .map(|(_, p)| p.clone())
            .collect();
        refused(
            run_entry(run_package(BASE, &arenas, &remaining)),
            "entry-asset-missing",
        );
    }
}

#[test]
fn asset_bodies_are_admitted_by_identity_and_canonical_text() {
    let arenas = arenas(Identity::KoalaBear);
    let pairs = arenas.pairs();
    // The branch body under the executed arena's digest: content identity fails.
    let mut substituted = pairs.clone();
    substituted[0].1 = arenas.branch.clone();
    refused(
        run_entry(run_package(BASE, &arenas, &substituted)),
        "refused:ring-asset-identity",
    );
    // Equivalent but noncanonical text parses, hashes to the same canonical
    // identity, and still refuses: the package carries canonical bodies only.
    let mut spaced = pairs.clone();
    spaced[0].1 = arenas.executed.replace(',', ", ");
    assert_ne!(spaced[0].1, arenas.executed);
    refused(
        run_entry(run_package(BASE, &arenas, &spaced)),
        "entry-asset-canonical",
    );
    let mut malformed = pairs.clone();
    malformed[0].1 = "[\"zkc.ring/0\",[],[],[0]]".into();
    refused(
        run_entry(run_package(BASE, &arenas, &malformed)),
        "refused:ring-output",
    );
    // An admitted asset that no reachable operation references is retained
    // but reported through the API as unreferenced.
    let extra = arena(Identity::KoalaBearExt8, true, true);
    let mut extended = pairs.clone();
    extended.push((sha(&extra), extra.clone()));
    let entry = run_entry(run_package(BASE, &arenas, &extended)).unwrap();
    assert_eq!(entry.assets().identities().len(), 4);
    assert_eq!(entry.assets().references().len(), 3);
    assert!(
        entry
            .assets()
            .references()
            .iter()
            .all(|r| r.identity != sha(&extra))
    );
}

#[test]
fn carrier_compatibility_is_checked_statically_in_both_directions() {
    // KoalaBear arenas under an Ext8 carrier: inputs promote, and execution
    // substitutes extension values.
    let base = arenas(Identity::KoalaBear);
    let entry = run_entry(run_package(EXTENSION, &base, &base.pairs())).unwrap();
    let report = entry
        .prepare(run_request(extension_vector(&[3, 4]), 1))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{:?}", report.native.failure);
    let Value::Leaf(InputValue::Native(result)) = &report.outputs.unwrap()["P"]["result"] else {
        panic!("vector result");
    };
    let Native::KoalaBearExt8Vector(values) = result.as_ref() else {
        panic!("Ext8 vector result");
    };
    assert_eq!(
        values.as_ref(),
        [
            KoalaBearExt8::from(KoalaBear::new(12)),
            KoalaBearExt8::from(KoalaBear::new(7))
        ]
    );
    // Ext8 arenas under a KoalaBear carrier refuse at admission, even for the
    // arena behind the untaken branch.
    let extension = arenas(Identity::KoalaBearExt8);
    refused(
        run_entry(run_package(BASE, &extension, &extension.pairs())),
        "entry-asset-carrier",
    );
    let mut mixed = base.pairs();
    mixed[1] = (sha(&extension.branch), extension.branch.clone());
    let mut mixed_arenas = arenas(Identity::KoalaBear);
    mixed_arenas.branch = extension.branch.clone();
    refused(
        run_entry(run_package(BASE, &mixed_arenas, &mixed)),
        "entry-asset-carrier",
    );
}

fn proof_program(field: &str, arenas: &Arenas) -> Json {
    let vector = physical(&format!("vector:{field}"));
    let boolean = physical("bool");
    let mut functions = functions(field, arenas);
    functions.as_array_mut().unwrap().push(json!([
        "function",
        "accept",
        [],
        [boolean],
        [
            ["bool_constant", "accept", "yes", true],
            ["return", ["yes"]]
        ],
        ["accept", []]
    ]));
    json!([
        "zkc.program/0",
        bindings(field),
        functions,
        [
            [
                "participant",
                "prover",
                "root",
                "P",
                [["x", vector]],
                [],
                [
                    ["local", "evaluate", "evaluate", ["x"], ["r"]],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "verifier",
                "root",
                "V",
                [["x", vector]],
                [boolean],
                [
                    ["local", "evaluate", "evaluate", ["x"], ["r"]],
                    ["local", "accept", "accept", [], ["yes"]],
                    ["return", ["yes"]]
                ],
                []
            ]
        ],
        [["entry", "Assets", [["P", "prover"], ["V", "verifier"]]]]
    ])
}
fn deployment(field: &str, arenas: &Arenas) -> String {
    let leaf = format!("vector:{field}");
    let candidate = proof_program(field, arenas).to_string();
    // Vectors travel in the common native data frame.
    let descriptor = json!([
        "zkc.native-proof-descriptor/0",
        [
            "zkc.native-proof-policy/0",
            "Assets",
            "P",
            "V",
            "0",
            "",
            "",
            ["0"],
            []
        ],
        "zkc.native-origin/0",
        [],
        [["V", "0", leaf, "zkc.native-data/0"]],
        []
    ]);
    json!([
        "zkc.native-proof/0",
        sha(ORIGINAL),
        descriptor,
        hash(&logical::encode_tree(&descriptor).unwrap()),
        candidate,
        hash(candidate.as_bytes()),
        [
            ["P", "prover", [["0", leaf]], [], [], ""],
            ["V", "verifier", [["0", leaf]], [["0", "bool"]], [], "0"]
        ],
        ["true", "false"],
        []
    ])
    .to_string()
}
fn proof_interface(field: &str) -> Json {
    let leaf = format!("vector:{field}");
    let vector = schema("builtin", &leaf, &[&leaf]);
    let boolean = schema("boolean", "bool", &["bool"]);
    interface(
        json!({"symbol":"Assets","roles":["P","V"],
            "inputs":[port("x",0,&[0],&["P","V"],vector)],
            "outputs":[port("accepted",0,&[0],&["V"],boolean)],"services":[],"clauses":[]}),
        json!({"kind":"proof","prover":"P","verifier":"V","public":[0],
            "acceptance":{"direction":"output","port":0,"role":"V","path":[]},
            "completion":null,"target":null,"construction":{"kind":"authored"}}),
    )
}
fn proof_entry(
    field: &str,
    arenas: &Arenas,
    assets: &[(String, String)],
) -> Result<ProofEntry, EntryError> {
    let package = package(&proof_interface(field), &deployment(field, arenas), assets);
    ProofEntry::admit(
        package,
        ProofOptions {
            binding: BindingPolicy::AllowHeaderOnly,
            ..Default::default()
        },
        SetupAuthority::default(),
    )
}
fn proof_request() -> ProofRequest {
    ProofRequest {
        public: BTreeMap::from([("x".into(), base_vector(&[3, 4]))]),
        ..Default::default()
    }
}

#[test]
fn packaged_arenas_serve_both_independent_proof_participants() {
    let base = arenas(Identity::KoalaBear);
    let pairs = base.pairs();
    let prover = proof_entry(BASE, &base, &pairs).unwrap();
    let verifier = proof_entry(BASE, &base, &pairs).unwrap();
    for entry in [&prover, &verifier] {
        assert_eq!(
            entry
                .assets()
                .references()
                .iter()
                .map(|r| r.site.as_str())
                .collect::<Vec<_>>(),
            ["hidden", "evaluate"],
            "one shared function is reported once"
        );
    }
    let produced = prover.prove(proof_request()).unwrap();
    assert!(produced.is_success(), "{:?}", produced.native.outcome);
    assert!(produced.native.ring_work > 0);
    let proof = produced.native.outcome.unwrap();
    let checked = verifier.verify(proof_request(), &proof).unwrap();
    assert!(checked.is_success(), "{:?}", checked.native.outcome);
    assert!(checked.native.ring_work > 0);
    assert_eq!(
        bool::try_from(checked.outputs.unwrap().remove("accepted").unwrap()),
        Ok(true)
    );
    // Both participants need the arena behind the untaken branch at admission.
    refused(proof_entry(BASE, &base, &pairs[..1]), "entry-asset-missing");
    let extension = arenas(Identity::KoalaBearExt8);
    refused(
        proof_entry(BASE, &extension, &extension.pairs()),
        "entry-asset-carrier",
    );
}
