//! File I/O for the same authenticated bundle host exposed to Rust callers.
use super::host::*;
use crate::host::inputs::*;
use serde_json::{Value as Json, json};
pub fn run(args: &[String]) -> Json {
    let mut report = json!({"format":"zkc.bundle-result/1","status":"refused","phase":"arguments","resources":[]});
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
                "--setups" => setups = SetupAuthority::parse(&read(path, 64 * 1024)?)?,
                "--capacity" => limits.capacity = NativeCapacity::parse(&read(path, 4096)?)?,
                "--limits" => {
                    let value = parse(&read(path, 4096)?, 4096)?;
                    let row = array(&value, 5)?;
                    if text(&row[0])? != "zkc.bundle-limits/1" {
                        return Err("bundle-limits-format".into());
                    }
                    let size =
                        |v| usize::try_from(natural(v)?).map_err(|_| "bundle-limits".to_owned());
                    limits.steps = size(&row[1])?;
                    limits.message_bytes = size(&row[2])?;
                    limits.total_wire_bytes = size(&row[3])?;
                    limits.external_work = natural(&row[4])?;
                    let hard = HostLimits::default();
                    if limits.steps > hard.steps
                        || limits.message_bytes > hard.message_bytes
                        || limits.total_wire_bytes > hard.total_wire_bytes
                        || limits.external_work > hard.external_work
                    {
                        return Err("bundle-limits".into());
                    }
                }
                _ => return Err("bundle-option".into()),
            }
        }
        report["limits"] = limits.record();
        report["phase"] = json!("admission");
        let host = RunHost::admit(&read(bundle, limits.bundle.bytes)?, &pin, limits, setups)?;
        report["bundle_sha256"] = json!(host.identity());
        report["layout"] = host.layout();
        report["phase"] = json!("inputs");
        let prepared = host.prepare(&read(inputs, INPUT_LIMIT)?)?;
        report = prepared.execute().json();
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}
