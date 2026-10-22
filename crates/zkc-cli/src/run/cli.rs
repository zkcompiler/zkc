//! File I/O for the same authenticated bundle host exposed to Rust callers.
use super::*;
use crate::execution::Capacity;
use crate::files::*;
use serde_json::{Value as Json, json};
type Result<T> = std::result::Result<T, String>;
const INPUT_LIMIT: usize = 16 * 1024 * 1024;
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
                _ => unreachable!("validated bundle run option"),
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
        report = render(&prepared.execute());
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}

fn render(report: &HostReport) -> Json {
    let mut result = report.diagnostics();
    result["format"] = json!("zkc.bundle-result/0");
    result["status"] = json!(if report.phase == "execution" {
        "executed"
    } else {
        "setup-failed"
    });
    result["acceptance"] = Json::Null;
    result["assurance"] = json!([
        "authenticated-supplied-schedule",
        "session-freshness-host-obligation",
        "local-only-public-inputs",
        "registry-selected-receive-keys"
    ]);
    for encoded in report.encode_outputs() {
        let values = encoded
            .values
            .into_iter()
            .enumerate()
            .map(|(index, value)| match value {
                EncodedOutput::Wire {
                    physical_type,
                    bytes,
                } => json!(["wire", physical_type, hex(&bytes)]),
                EncodedOutput::Private { physical_type } => json!(["private", physical_type]),
                EncodedOutput::Unavailable { code } => {
                    result["diagnostics"].as_array_mut().unwrap().push(
                        json!({"role":encoded.role,"output":index,"kind":"output","code":code}),
                    );
                    json!(["unavailable", code])
                }
            })
            .collect::<Vec<_>>();
        if let Some(role) = result["roles"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|r| r["role"] == encoded.role)
        {
            role["outputs"] = json!(values);
        }
    }
    if result["diagnostics"]
        .as_array()
        .is_some_and(|d| !d.is_empty())
    {
        result["status"] = json!("diagnostic-failed");
    }
    result
}
