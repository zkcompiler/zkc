//! Pinned Entry packages for tests of the SDK and of applications built over
//! it, such as the browser adapter. No production command or file format
//! selects this feature-gated module.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use zkc_runtime::vm::{LogicalType, PhysicalType};

fn digest(text: &str) -> String {
    crate::io::bytes::hex(&Sha256::digest(text.as_bytes()))
}

/// Publish an interface document and native artifact as an Entry package.
/// Returns the package bytes and the pin an application holds independently
/// of them.
pub fn package(interface: &Json, artifact: &str) -> (Vec<u8>, [u8; 32]) {
    let bytes = json!({"format":"zkc.entry/0","original":"original",
        "interface":interface.to_string(),"artifact":artifact,"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
            "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,
            "oracle_realization":crate::entry::OracleSelection::default()}})
    .to_string()
    .into_bytes();
    let pin = Sha256::digest(&bytes).into();
    (bytes, pin)
}

/// An authored proof over Unicode source names: the prover `証明者` returns
/// its private boolean `秘密` as `結果`, and the verifier `検証者` accepts with
/// its public boolean `公開` as `受理`. Returns the interface document, which a
/// test may edit before [`package`] publishes it, and the native artifact.
/// Admission needs `BindingPolicy::AllowAuthored`.
pub fn authored_proof() -> (Json, String) {
    let boolean = PhysicalType::default_for(LogicalType::parse("bool").unwrap())
        .unwrap()
        .spelling();
    let candidate = json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "v",
                "root",
                "role00000000",
                [["x", boolean]],
                [boolean],
                [["return", ["x"]]],
                []
            ],
            [
                "participant",
                "p",
                "root",
                "role00000001",
                [["x", boolean], ["w", boolean]],
                [boolean],
                [["return", ["w"]]],
                []
            ]
        ],
        [[
            "entry",
            "main",
            [["role00000000", "v"], ["role00000001", "p"]]
        ]]
    ])
    .to_string();
    let descriptor = json!([
        "zkc.native-proof-descriptor/0",
        [
            "zkc.native-proof-policy/0",
            "main",
            "role00000001",
            "role00000000",
            "0",
            "",
            [],
            ["0"],
            [],
            "zkc.framed/0",
            "",
            []
        ],
        "zkc.native-origin/0",
        [],
        [["role00000000", "0", "bool", "zkcv.bool/0"]],
        [],
        [],
        [],
        r#"{"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[],"kind":"exact"}}"#
    ]);
    let artifact = json!([
        "zkc.native-proof/0",
        digest("original"),
        descriptor,
        crate::io::bytes::hash(&zkc_format::logical::encode_tree(&descriptor).unwrap()),
        candidate,
        digest(&candidate),
        [
            [
                "role00000000",
                "v",
                [["0", "bool"]],
                [["0", "bool"]],
                [],
                "0"
            ],
            [
                "role00000001",
                "p",
                [["0", "bool"], ["1", "bool"]],
                [["1", "bool"]],
                [],
                ""
            ]
        ],
        [
            "true",
            "false",
            "false",
            "true",
            "false",
            "true",
            crate::entry::OracleSelection::default()
                .canonical_json()
                .unwrap()
        ],
        []
    ])
    .to_string();
    let boolean = json!({"kind":"boolean","identity":digest("bool"),"type":"bool","generated":null,
        "custody":0,"sealed":false,"roles":[],"element":null,"constructible":true,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":["bool"]});
    // One boolean data port, placed at each of `roles` from native `native`.
    let port = |name: &str, index: u32, native: u32, roles: &[u32]| {
        let components = roles
            .iter()
            .map(|role| json!({"path":[],"leaf":0,"role":role,"facet":"data","native":native}))
            .collect::<Vec<_>>();
        json!({"name":name,"index":index,"native":[native],"placement":{"kind":"data","roles":roles},
            "components":components,"type":boolean["type"],"schema":boolean})
    };
    let doc = json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("original"),
        "toolchain":"test-toolchain","entry":"数学::証明₂","protocol":"main","relations":[],
        "protocols":[{"symbol":"main","roles":["検証者","証明者"],"services":[],"common_input_requirements":[],"clauses":[],
            "inputs":[port("公開",0,0,&[0,1]),port("秘密",1,1,&[1])],
            "outputs":[port("受理",0,0,&[0]),port("結果",1,1,&[1])]}],
        "job":{"kind":"proof","prover":"証明者","verifier":"検証者","public":[{"port":0,"path":[],"role":"検証者"}],
            "acceptance":{"direction":"output","port":0,"role":"検証者","path":[]},"completion":null,
            "target":null,"gates":[],"construction":{"kind":"authored", "format": "zkc.framed/0"}}});
    (doc, artifact)
}
