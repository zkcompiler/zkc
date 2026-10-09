//! File I/O for the same authenticated bundle host exposed to Rust callers.
use super::host::*;
use crate::host::inputs::*;
use serde_json::{Value as Json, json};
pub fn run(args: &[String]) -> Json {
    let mut report = json!({"format":"zkc.bundle-result/0","status":"refused","phase":"arguments","resources":[]});
    let result = (|| -> Result<()> {
        let [bundle, expected, inputs, options @ ..] = args else {
            return Err("usage: run-bundle BUNDLE EXPECTED_SHA256 INPUTS [--setups=AUTHORITY] [--capacity=LIMITS] [--limits=LIMITS]".into());
        };
        let pin = digest(expected)?;
        let mut limits = HostLimits::default();
        let mut setups = SetupAuthority::default();
        let mut seen = std::collections::BTreeSet::new();
        for option in options {
            let (name, path) = option.split_once('=').ok_or("bundle-option")?;
            if !seen.insert(name) {
                return Err("bundle-option".into());
            }
            match name {
                "--setups" => setups = SetupAuthority::parse(&read_regular(path, 64 * 1024)?)?,
                "--capacity" => {
                    limits.capacity = NativeCapacity::parse(&read_regular(path, 4096)?)?
                }
                "--limits" => {
                    let value = parse(&read_regular(path, 4096)?, 4096)?;
                    let row = array(&value, 5)?;
                    if text(&row[0])? != "zkc.bundle-limits/0" {
                        return Err("bundle-limits-format".into());
                    }
                    let size =
                        |v| usize::try_from(natural(v)?).map_err(|_| "bundle-limits".to_owned());
                    limits.steps = size(&row[1])?;
                    limits.message_bytes = size(&row[2])?;
                    limits.total_wire_bytes = size(&row[3])?;
                    limits.external_work = natural(&row[4])?;
                    limits.validate()?;
                }
                _ => return Err("bundle-option".into()),
            }
        }
        report["limits"] = limits.record();
        report["phase"] = json!("admission");
        let host = RunHost::admit(
            &read_regular(bundle, limits.bundle.bytes)?,
            &pin,
            limits,
            setups,
        )?;
        report["bundle_sha256"] = json!(host.identity());
        report["layout"] = host.layout();
        report["phase"] = json!("inputs");
        let prepared = host.prepare(&read_regular(inputs, INPUT_LIMIT)?)?;
        report = prepared.execute().json();
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}
