use std::{
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};
use zkc_runtime::interactive::{
    AdmissionError, ArtifactFormat, CallMapping, Correspondence, ErrorCode, PortMapping, SourceMap,
};

/// Installed independent Lean checker for the portable source/participant format.
/// The result establishes executable structural correspondence. It does not
/// assert the separate typed projection theorem applies to this raw decoder.
pub struct ParticipantChecker {
    executable: PathBuf,
    timeout: Duration,
}
impl ParticipantChecker {
    pub fn new(executable: impl AsRef<Path>) -> std::io::Result<Self> {
        Ok(Self {
            executable: executable.as_ref().canonicalize()?,
            timeout: Duration::from_secs(120),
        })
    }
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}
fn error(detail: impl Into<String>) -> AdmissionError {
    AdmissionError::new(ErrorCode::Correspondence, detail)
}
impl ParticipantChecker {
    fn invoke(
        &self,
        source: &[u8],
        candidate: &[u8],
        _format: ArtifactFormat,
    ) -> Result<Option<SourceMap>, AdmissionError> {
        let response_limit = 4_194_304;
        let io = |_: std::io::Error| error("checker-io");
        let dir = tempfile::tempdir().map_err(io)?;
        let source_path = dir.path().join("source.json");
        let candidate_path = dir.path().join("participants.json");
        std::fs::write(&source_path, source).map_err(io)?;
        std::fs::write(&candidate_path, candidate).map_err(io)?;
        let mut command = Command::new(&self.executable);
        command
            .arg("--check-generic")
            .arg(source_path)
            .arg(candidate_path);
        let output = crate::host::process::capture(
            &mut command,
            dir.path(),
            |elapsed| elapsed >= self.timeout,
            response_limit,
            false,
        )
        .map_err(|failure| match failure {
            crate::host::process::Error::Process(_) | crate::host::process::Error::Io(_) => {
                error("checker-io")
            }
            crate::host::process::Error::Timeout => error("checker-timeout"),
            crate::host::process::Error::OutputLimit => error("checker-response-limit"),
        })?;
        let status = output.status;
        let bytes = crate::host::io::read_bounded(output.stdout.path(), response_limit).map_err(
            |failure| match failure {
                crate::host::io::ReadError::Io(_) => error("checker-io"),
                crate::host::io::ReadError::Limit => error("checker-response-limit"),
            },
        )?;
        let value: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|_| error("checker-response"))?;
        if status.success() {
            return decode_mapping(&value).map(Some);
        }
        if status.code() == Some(1)
            && let Some(items) = value.as_array()
            && items.len() == 2
            && items[0] == "refused"
            && let Some(code) = items[1].as_str()
        {
            return Err(error(format!("checker-refused:{code}")));
        }
        Err(error("checker-response"))
    }
}

impl Correspondence for ParticipantChecker {
    fn check(
        &self,
        source: &[u8],
        candidate: &[u8],
        format: ArtifactFormat,
    ) -> Result<(), AdmissionError> {
        self.invoke(source, candidate, format).map(|_| ())
    }
    fn check_with_mapping(
        &self,
        source: &[u8],
        candidate: &[u8],
        _format: ArtifactFormat,
    ) -> Result<Option<SourceMap>, AdmissionError> {
        self.invoke(source, candidate, _format)
    }
}

fn decode_mapping(value: &serde_json::Value) -> Result<SourceMap, AdmissionError> {
    use serde_json::Value;
    fn array(value: &Value, size: Option<usize>) -> Result<&[Value], AdmissionError> {
        let items = value.as_array().ok_or_else(|| error("checker-mapping"))?;
        if size.is_some_and(|size| items.len() != size) || items.len() > 32768 {
            return Err(error("checker-mapping"));
        }
        Ok(items)
    }
    fn name(value: &Value, limit: usize) -> Result<String, AdmissionError> {
        let name = value.as_str().ok_or_else(|| error("checker-mapping"))?;
        if name.is_empty() || name.len() > limit {
            return Err(error("checker-mapping"));
        }
        Ok(name.to_owned())
    }
    let record = array(value, Some(5))?;
    if record[0] != "checked"
        || record[1] != "generic-structural-correspondence"
        || record[4] != "no-elaboration-adequacy-proof"
    {
        return Err(error("checker-response"));
    }
    let mut result = SourceMap::default();
    for value in array(&record[2], None)? {
        let record = array(value, Some(4))?;
        let mut arguments = Vec::new();
        for pair in array(&record[3], None)? {
            let pair = array(pair, Some(2))?;
            arguments.push((name(&pair[0], 128)?, name(&pair[1], 128)?));
        }
        result.ports.push(PortMapping {
            instance: name(&record[0], 128)?,
            role: name(&record[1], 128)?,
            participant: name(&record[2], 512)?,
            arguments,
        });
    }
    for value in array(&record[3], None)? {
        let record = array(value, Some(5))?;
        result.calls.push(CallMapping {
            instance: name(&record[0], 128)?,
            role: name(&record[1], 128)?,
            site: name(&record[2], 128)?,
            source_function: name(&record[3], 128)?,
            function: name(&record[4], 128)?,
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn mapping_decoder_requires_the_exact_claim_and_bounded_coordinates() {
        let valid = json!([
            "checked",
            "generic-structural-correspondence",
            [["root", "P", "root.P", [["source", "v0"]]]],
            [["root", "P", "site", "Configured", "generated"]],
            "no-elaboration-adequacy-proof"
        ]);
        let map = decode_mapping(&valid).unwrap();
        assert_eq!(map.port("root", "P", "source"), Some("v0"));
        assert_eq!(map.call("root", "P", "site").unwrap().function, "generated");
        let mut wrong_claim = valid.clone();
        wrong_claim[1] = json!("generic-local-correspondence");
        let mut stale_scope = valid.clone();
        stale_scope[4] = json!("no-typed-elaboration");
        let mut unbounded = valid.clone();
        unbounded[2][0][3][0][0] = json!("x".repeat(129));
        let mut short = valid.clone();
        short[3][0].as_array_mut().unwrap().pop();
        let mut empty = valid.clone();
        empty[3][0][3] = json!("");
        let mut invalid_kind = valid.clone();
        invalid_kind[2][0][3][0][1] = json!(0);
        let mut extra = valid.clone();
        extra.as_array_mut().unwrap().push(json!([]));
        for malformed in [
            wrong_claim,
            stale_scope,
            unbounded,
            short,
            empty,
            invalid_kind,
            extra,
        ] {
            assert!(decode_mapping(&malformed).is_err());
        }
    }
}
