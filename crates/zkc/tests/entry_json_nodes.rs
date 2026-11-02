//! The shared Entry JSON node-ceiling corpus, read by the SDK's interface and
//! Host carrier readers through packaged inputs. The compiler's readers consume
//! the same cases (`compiler/test/host_entry.cpp`).
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use zkc::entry::{BoundInterface, FunctionInterface, InterfaceLimits, Package};

fn digest(bytes: &[u8]) -> String {
    zkc_test_support::hex(&Sha256::digest(bytes))
}

/// One input: a string, or ordered segments, each a string or a repeated item.
fn wire(value: &Json) -> String {
    if let Some(text) = value.as_str() {
        return text.to_owned();
    }
    let mut result = String::new();
    for segment in value.as_array().unwrap() {
        if let Some(text) = segment.as_str() {
            result.push_str(text);
            continue;
        }
        let item = segment["repeat"].as_str().unwrap();
        let separator = segment["separator"].as_str().unwrap();
        for i in 0..segment["count"].as_u64().unwrap() {
            if i > 0 {
                result.push_str(separator);
            }
            result.push_str(&item.replace("{i}", &i.to_string()));
        }
    }
    result
}

/// A Function interface whose Host carrier is the case input, so the carrier
/// reader runs after an admitted interface.
fn function_interface() -> String {
    let unit = json!({"kind":"unit","type":"()","identity":digest(b"()"),"generated":null,"custody":0,
        "sealed":false,"roles":[],"element":null,"constructible":true,"permissions":["Copy","Drop"],
        "fields":[],"alternatives":[],"leaves":[]});
    json!({"format":"zkc.language-interface/0","capture":digest(b"source capture"),
        "original":digest(b"original source"),"toolchain":"test","entry":"example::Main",
        "selection":{"kind":"function","function":"example::Main"},
        "functions":[{"symbol":"example::Main","parameters":[],"result":unit}],
        "protocols":[],"relations":[],"setups":[]})
    .to_string()
}

fn package(interface: &str, artifact: &str) -> Package {
    let bytes = json!({"format":"zkc.entry/0","original":"original source",
        "interface":interface,"artifact":artifact,"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
            "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,
            "oracle_realization":zkc::entry::OracleSelection::default()}})
    .to_string();
    let pin = Sha256::digest(bytes.as_bytes()).into();
    Package::capture(bytes.as_bytes(), &pin, Package::MAX_BYTES).unwrap()
}

#[test]
fn entry_readers_enforce_the_shared_node_ceilings_exactly() {
    let corpus: Json = serde_json::from_str(include_str!(
        "../../../common/tests/fixtures/entry-json/nodes.json"
    ))
    .unwrap();
    assert_eq!(corpus["format"], "zkc.entry-json-node-fixtures/0");
    let limits = InterfaceLimits::DEFAULT;
    // The interface reader admits the Function interface the Host cases use.
    FunctionInterface::read(&package(&function_interface(), "[]"), limits).unwrap();
    let cases = corpus["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 8);
    for case in cases {
        let name = case["name"].as_str().unwrap();
        let bytes = wire(&case["wire"]);
        let code = match case["reader"].as_str().unwrap() {
            "interface" => BoundInterface::read(&package(&bytes, "[]"), limits)
                .err()
                .map(|error| error.to_string()),
            "host" => FunctionInterface::deployment_interfaces(
                &package(&function_interface(), &bytes),
                limits,
            )
            .err()
            .map(|error| error.code().to_owned()),
            other => panic!("{name}: unknown reader {other}"),
        };
        let limited = code.as_deref() == Some("entry-interface-limit");
        assert_eq!(
            limited,
            case["expected"] == "node-limit",
            "{name}: unexpected result {code:?}"
        );
    }
}
