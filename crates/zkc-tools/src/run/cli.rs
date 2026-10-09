//! File I/O for the same authenticated bundle host exposed to Rust callers.
use super::host::*;
use crate::execution::Capacity;
use crate::host::inputs::*;
use serde_json::{Value as Json, json};
pub(crate) fn run(args: &crate::cli::Arguments<'_>) -> Json {
    let mut report = json!({"format":"zkc.bundle-result/0","status":"refused","phase":"arguments","resources":[]});
    let result = (|| -> Result<()> {
        let bundle = args.positional[0];
        let pin = digest(args.positional[1])?;
        let inputs = args.positional[2];
        let mut limits = HostLimits::default();
        let mut setups = SetupAuthority::default();
        for &(name, value) in &args.options {
            let path = value.expect("validated value option");
            match name {
                "--setups" => setups = SetupAuthority::parse(&read_regular(path, 64 * 1024)?)?,
                "--capacity" => limits.capacity = Capacity::parse(&read_regular(path, 4096)?)?,
                "--limits" => limits = limits.with_work_limits(&read_regular(path, 4096)?)?,
                _ => unreachable!("validated run-bundle option"),
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
