use std::{
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};
use zkc_runtime::interactive::{
    AdmissionError, ArtifactFormat, CallMapping, Correspondence, ErrorCode, PhysicalType,
    PortMapping, RootMapping, SourceMap,
};

/// Installed independent Lean checker for the portable source/participant format.
/// The result establishes executable structural correspondence. It does not
/// assert the separate typed projection theorem applies to this raw decoder.
pub struct ParticipantChecker {
    executable: PathBuf,
    timeout: Duration,
    mathematical_capture: Option<(Vec<u8>, String)>,
}
impl ParticipantChecker {
    pub fn new(executable: impl AsRef<Path>) -> std::io::Result<Self> {
        Ok(Self {
            executable: executable.as_ref().canonicalize()?,
            timeout: Duration::from_secs(120),
            mathematical_capture: None,
        })
    }
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    /// Retain the original capture through the runtime correspondence call.
    /// Lean checks its target against the exact source given to admission, and
    /// the host binds its independently encoded subject to the caller's pin.
    pub fn with_mathematical_capture(mut self, capture: Vec<u8>, subject_pin: String) -> Self {
        self.mathematical_capture = Some((capture, subject_pin));
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
        if let Some((capture, _)) = &self.mathematical_capture {
            let capture_path = dir.path().join("mathematical.json");
            std::fs::write(&capture_path, capture).map_err(io)?;
            command.arg("--check-mathematical").arg(capture_path);
        } else {
            command.arg("--check-generic");
        }
        command.arg(source_path).arg(candidate_path);
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
            if let Some((_, subject_pin)) = &self.mathematical_capture {
                return decode_mathematical_mapping(&value, subject_pin).map(Some);
            }
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

/// Explicit host hash boundary: Lean determines all bytes and expected pins;
/// SHA256 only supplies their identity, never operation or provider semantics.
fn decode_mathematical_mapping(
    value: &serde_json::Value,
    subject_pin: &str,
) -> Result<SourceMap, AdmissionError> {
    use sha2::{Digest, Sha256};
    let fields = value
        .as_array()
        .ok_or_else(|| error("checker-mathematical-response"))?;
    if fields.len() != 4
        || fields[0] != "pending-hashes"
        || fields[1] != "mathematical-structural-correspondence"
    {
        return Err(error("checker-mathematical-response"));
    }
    let obligations = fields[3]
        .as_array()
        .ok_or_else(|| error("checker-hash-obligations"))?;
    if obligations.len() != 17 {
        return Err(error("checker-hash-obligations"));
    }
    for (index, obligation) in obligations.iter().enumerate() {
        let pair = obligation
            .as_array()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| error("checker-hash-obligation"))?;
        let request = pair[0]
            .as_array()
            .filter(|r| r.len() == 3)
            .ok_or_else(|| error("checker-hash-obligation"))?;
        if request[0] != "zkc.hash/1" || request[1] != "sha256" {
            return Err(error("checker-hash-obligation"));
        }
        let expected = pair[1]
            .as_str()
            .ok_or_else(|| error("checker-hash-obligation"))?;
        if expected.len() != 64
            || !expected
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(error("checker-hash-obligation"));
        }
        let bytes =
            crate::artifact::unhex(&request[2]).map_err(|_| error("checker-hash-obligation"))?;
        let prefix: &[u8] = match index {
            0 => b"zkc.math.subject.v1\0",
            1 => b"zkc.math.placement.target.v1\0",
            _ => b"zkc.math.installation.v1\0",
        };
        if !bytes.starts_with(prefix) {
            return Err(error("checker-hash-obligation"));
        }
        if crate::artifact::hex(&Sha256::digest(&bytes)) != expected {
            return Err(error("checker-mathematical-digest"));
        }
        if index == 0 && expected != subject_pin {
            return Err(error("checker-mathematical-source-pin"));
        }
    }
    decode_mapping(&fields[2])
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
    let record = array(value, None)?;
    if !matches!(record.len(), 5 | 6)
        || record[0] != "checked"
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
            // A checked inline-region key adds '@' to its bounded 128-byte
            // origin. It is correspondence metadata, not an authored symbol.
            source_function: name(&record[3], 129)?,
            function: name(&record[4], 128)?,
        });
    }
    if record.len() == 6 {
        let roots = array(&record[5], None)?;
        if roots.is_empty() || roots.len() > 4096 {
            return Err(error("checker-root-mapping"));
        }
        for value in roots {
            let r = array(value, Some(7))?;
            let ordinal = name(&r[6], 20)?;
            let output = ordinal
                .parse::<usize>()
                .map_err(|_| error("checker-root-mapping"))?;
            if output.to_string() != ordinal {
                return Err(error("checker-root-mapping"));
            }
            result.roots.push(RootMapping {
                instance: name(&r[0], 128)?,
                role: name(&r[1], 128)?,
                root: name(&r[2], 128)?,
                service: name(&r[3], 128)?,
                state_type: PhysicalType::parse(&name(&r[4], 1024)?)
                    .map_err(|_| error("checker-root-type"))?,
                input: name(&r[5], 128)?,
                output,
            });
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn mathematical_mapping_requires_every_trusted_hash_before_acceptance() {
        use sha2::{Digest, Sha256};
        let obligations: Vec<_> = (0..17)
            .map(|index| {
                let bytes = match index {
                    0 => b"zkc.math.subject.v1\0retained subject".as_slice(),
                    1 => b"zkc.math.placement.target.v1\0retained target".as_slice(),
                    _ => b"zkc.math.installation.v1\0descriptor".as_slice(),
                };
                json!([
                    ["zkc.hash/1", "sha256", crate::artifact::hex(bytes)],
                    crate::artifact::hex(&Sha256::digest(bytes))
                ])
            })
            .collect();
        let subject_pin = obligations[0][1].as_str().unwrap().to_owned();
        let record = json!([
            "pending-hashes",
            "mathematical-structural-correspondence",
            [
                "checked",
                "generic-structural-correspondence",
                [],
                [],
                "no-elaboration-adequacy-proof"
            ],
            obligations
        ]);
        assert!(decode_mathematical_mapping(&record, &subject_pin).is_ok());
        assert!(decode_mathematical_mapping(&record, &"0".repeat(64)).is_err());
        let mut bytes = record.clone();
        bytes[3][0][0][2] = json!("00");
        let mut pin = record.clone();
        pin[3][1][1] = json!("0".repeat(64));
        let mut algorithm = record.clone();
        algorithm[3][2][0][1] = json!("other");
        let mut malformed = record.clone();
        malformed[3][3][0][2] = json!("0");
        let mut missing = record.clone();
        missing[3].as_array_mut().unwrap().pop();
        let mut reordered = record.clone();
        reordered[3].as_array_mut().unwrap().swap(0, 1);
        let mut duplicate_subject = record.clone();
        duplicate_subject[3][2] = record[3][0].clone();
        let mut claim = record;
        claim[0] = json!("checked");
        for altered in [
            bytes,
            pin,
            algorithm,
            malformed,
            missing,
            reordered,
            duplicate_subject,
            claim,
        ] {
            assert!(decode_mathematical_mapping(&altered, &subject_pin).is_err());
        }
    }

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

    #[test]
    fn root_mapping_decoder_requires_typed_bounded_records() {
        let record = json!([
            "checked",
            "generic-structural-correspondence",
            [],
            [],
            "no-elaboration-adequacy-proof",
            [[
                "root",
                "P",
                "entropy",
                "random.draw",
                "rng:bls12-381.fr@host.resource/1",
                "v0",
                "0"
            ]]
        ]);
        assert_eq!(decode_mapping(&record).unwrap().roots[0].output, 0);
        for invalid in [
            json!("01"),
            json!("-1"),
            json!("18446744073709551616"),
            json!(0),
        ] {
            let mut bad = record.clone();
            bad[5][0][6] = invalid;
            assert!(decode_mapping(&bad).is_err());
        }
        let mut empty = record.clone();
        empty[5] = json!([]);
        assert!(decode_mapping(&empty).is_err());
        let mut ty = record.clone();
        ty[5][0][4] = json!("rng:unknown@host.resource/1");
        assert!(decode_mapping(&ty).is_err());
        let mut extra = record;
        extra[5][0].as_array_mut().unwrap().push(json!("extra"));
        assert!(decode_mapping(&extra).is_err());
    }
}
