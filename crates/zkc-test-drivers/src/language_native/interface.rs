//! Cross-language admission controls for the authenticated source/native link.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use zkc_tools::entry::{Interface, InterfaceError, Package, PackageError};

pub(super) fn alter(package: &Package, change: impl FnOnce(&mut Json, &mut Json)) -> Package {
    let mut frame: Json = serde_json::from_slice(package.bytes()).unwrap();
    let mut interface: Json = serde_json::from_str(package.interface()).unwrap();
    change(&mut frame, &mut interface);
    frame["interface"] = json!(interface.to_string());
    let bytes = frame.to_string().into_bytes();
    // Deliberately authorize a changed publication to test consistency checks
    // below authentication. A real client does not trust a self-supplied digest.
    Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap()
}
pub(super) fn changed_publication_cannot_reuse_pin(package: &Package) {
    let changed = alter(package, |_, interface| {
        let symbol = interface["protocol"].as_str().unwrap().to_owned();
        let protocol = interface["protocols"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|p| p["symbol"] == symbol)
            .unwrap();
        let inputs = protocol["inputs"].as_array_mut().unwrap();
        let first = inputs[0]["name"].clone();
        inputs[0]["name"] = inputs[1]["name"].clone();
        inputs[1]["name"] = first;
    });
    assert!(matches!(
        Package::capture(changed.bytes(), package.identity(), Package::MAX_BYTES),
        Err(PackageError::Identity)
    ));
}
pub(super) fn controls(
    package: &Package,
    check: impl Fn(&Interface) -> Result<(), InterfaceError>,
) {
    for change in 0..2 {
        let changed = alter(package, |frame, interface| {
            if change == 0 {
                frame["artifact"] = json!(package.artifact().to_owned() + "\n");
            } else {
                let symbol = interface["protocol"].as_str().unwrap().to_owned();
                for p in interface["protocols"].as_array_mut().unwrap() {
                    if p["symbol"] == symbol {
                        p["symbol"] = json!("other_protocol");
                    }
                }
                interface["protocol"] = json!("other_protocol");
            }
        });
        let view = Interface::read(&changed).unwrap();
        assert_eq!(check(&view), Err(InterfaceError::NativeBinding));
    }
}
