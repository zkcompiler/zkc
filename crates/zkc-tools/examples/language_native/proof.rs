//! Source-authored Schnorr runs through the same independent native proof host.
use super::*;
use serde_json::Value as Json;
use zkc_tools::artifact::{hex, native::NativeDeployment};
use zkc_tools::entry::Package;

pub(super) fn run(directory: &Path) {
    for suite in 0..2 {
        for simplified in 0..2 {
            for released in 0..2 {
                let bytes = std::fs::read(
                    directory.join(format!("source-proof-{suite}-{simplified}-{released}.json")),
                )
                .unwrap();
                let published = std::fs::read(directory.join(format!(
                    "source-proof-{suite}-{simplified}-{released}.entry"
                )))
                .unwrap();
                // This test's publication is produced by the preceding trusted
                // compiler invocation. Applications supply their own trusted pin.
                let package = Package::capture(
                    &published,
                    &Sha256::digest(&published).into(),
                    Package::MAX_BYTES,
                )
                .unwrap();
                assert_eq!(
                    package.artifact(),
                    std::str::from_utf8(&bytes)
                        .unwrap()
                        .strip_suffix('\n')
                        .unwrap()
                );
                assert_eq!(package.options().simplify, simplified == 1);
                assert_eq!(package.options().release_storage, released == 1);
                let checked = zkc_tools::entry::Interface::read(&package).unwrap();
                assert!(checked.is_proof());
                assert_eq!(checked.entry(), "sample::Demo");
                let interface: Json = serde_json::from_str(package.interface()).unwrap();
                assert_eq!(
                    interface["original"],
                    hex(&Sha256::digest(package.original().as_bytes()))
                );
                // Bind the exact packaged publication, without the standalone
                // language-bundle command's presentation newline.
                let bytes = package.artifact().as_bytes();
                let envelope: Json = serde_json::from_slice(bytes).unwrap();
                let deployment =
                    NativeDeployment::admit(bytes, &hex(&Sha256::digest(bytes))).unwrap();
                checked.check_proof(&deployment).unwrap();
                interface::controls(&package, |view| view.check_proof(&deployment));
                interface::changed_publication_cannot_reuse_pin(&package);
                for change in 0..3 {
                    let altered = interface::alter(&package, |frame, view| {
                        if change == 0 {
                            frame["options"]["simplify"] = json!(simplified == 0);
                        } else if change == 1 {
                            frame["original"] = json!(package.original().to_owned() + "\n");
                            view["original"] = json!(hex(&Sha256::digest(
                                frame["original"].as_str().unwrap().as_bytes()
                            )));
                        } else {
                            let symbol = view["protocol"].as_str().unwrap().to_owned();
                            let protocol = view["protocols"]
                                .as_array_mut()
                                .unwrap()
                                .iter_mut()
                                .find(|p| p["symbol"] == symbol)
                                .unwrap();
                            let service = protocol["services"]
                                .as_array_mut()
                                .unwrap()
                                .iter_mut()
                                .find(|s| s["owner"] == "P")
                                .unwrap();
                            service["contract"] = json!("random.bn254.fr/1");
                        }
                    });
                    assert_eq!(
                        zkc_tools::entry::Interface::read(&altered)
                            .unwrap()
                            .check_proof(&deployment),
                        Err(zkc_tools::entry::InterfaceError::NativeBinding)
                    );
                }

                let codec = backend(&json!({"entry":envelope[2][1][1]}), "P");
                let wire = |value: Value| hex(&codec.encode_native_value(&value).unwrap());
                let base = wire(Value::Curve(GroupPoint::generator()));
                let point = wire(Value::Curve(
                    GroupPoint::generator().scale(Scalar::from(3u64)),
                ));
                let input = |prover: bool, witness: u64| {
                    let data = if prover {
                        json!([
                            ["0", ["wire", base]],
                            ["1", ["wire", point]],
                            ["2", ["wire", wire(field(witness))]]
                        ])
                    } else {
                        json!([["0", ["wire", base]], ["1", ["wire", point]]])
                    };
                    let services = if prover {
                        json!([["3", "1"]])
                    } else {
                        json!([])
                    };
                    json!([
                        "zkc.native-proof-inputs/1",
                        [["V", "0", base], ["V", "1", point]],
                        data,
                        "",
                        services,
                        envelope[2][3].as_array().unwrap().len().to_string()
                    ])
                };
                let produced = deployment.execute(&input(true, 3), None).unwrap();
                assert!(produced.cleanup_errors.is_empty());
                assert_eq!(produced.messages, 2);
                assert!(produced.outputs.as_ref().unwrap().is_empty());
                let proof = produced.outcome.unwrap();
                // Separately admitted handle and verifier inputs; no witness or
                // producer runtime state is available to this invocation.
                let verifier =
                    NativeDeployment::admit(bytes, &hex(&Sha256::digest(bytes))).unwrap();
                let validated = verifier.execute(&input(false, 0), Some(&proof)).unwrap();
                assert!(validated.cleanup_errors.is_empty());
                validated.outcome.unwrap();
                assert!(matches!(
                    validated.outputs.as_ref().unwrap().get(&0),
                    Some(Value::Bool(true))
                ));
                let invalid = deployment.execute(&input(true, 5), None).unwrap();
                assert!(invalid.cleanup_errors.is_empty());
                let rejected = verifier
                    .execute(&input(false, 0), Some(&invalid.outcome.unwrap()))
                    .unwrap();
                assert!(rejected.cleanup_errors.is_empty());
                assert_eq!(rejected.outcome.unwrap_err(), "artifact-rejected");
                assert!(rejected.outputs.is_none());
                let mut wrong_context = input(false, 0);
                wrong_context[3] = json!("01");
                assert!(
                    verifier
                        .execute(&wrong_context, Some(&proof))
                        .unwrap()
                        .outcome
                        .is_err()
                );
            }
        }
    }
}
