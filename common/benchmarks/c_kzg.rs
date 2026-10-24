//! Standalone adapter for the pinned c-kzg EIP-4844 API, outside the native workspace.
#![forbid(unsafe_code)]

#[path = "../../crates/zkc-benchmarks/src/evidence.rs"]
mod evidence;
#[path = "../../crates/zkc-benchmarks/src/measure.rs"]
mod measure;

use c_kzg::{Blob, Bytes32, Bytes48, KzgSettings};
use measure::Plan;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    time::Instant,
};

const MAX_BLOBS: usize = 64;
const PROOF_BYTES: usize = 48;
type Result<T> = std::result::Result<T, Failure>;
type Upstream<T> = std::result::Result<T, c_kzg::Error>;

#[derive(Debug)]
enum Failure {
    Failed(String),
    Rejected(String),
    IncorrectResult(String),
}

impl From<String> for Failure {
    fn from(message: String) -> Self {
        Self::Failed(message)
    }
}

impl From<&str> for Failure {
    fn from(message: &str) -> Self {
        Self::Failed(message.into())
    }
}

impl Failure {
    fn report(&self) -> Value {
        let (status, error) = match self {
            Self::Failed(error) => ("failed", error),
            Self::Rejected(error) => ("rejected", error),
            Self::IncorrectResult(error) => ("incorrect-result", error),
        };
        json!({"format":"zkc.benchmark-worker/0", "status":status, "error":error})
    }
}

fn failed(error: impl std::fmt::Display) -> Failure {
    Failure::Failed(error.to_string())
}

fn read(path: &Path) -> Result<Vec<u8>> {
    std::fs::read(path).map_err(|error| failed(format!("{}: {error}", path.display())))
}

fn read_json<T: DeserializeOwned>(path: &Path) -> Result<T> {
    serde_json::from_slice(&read(path)?).map_err(failed)
}

fn absolute(path: &Path) -> Result<()> {
    if !path.is_absolute() {
        return Err(failed(format!("path must be absolute: {}", path.display())));
    }
    Ok(())
}

fn decode_hex<const N: usize>(text: &str) -> Result<[u8; N]> {
    fn digit(byte: u8) -> Result<u8> {
        match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            b'A'..=b'F' => Ok(byte - b'A' + 10),
            _ => Err("invalid hexadecimal digit".into()),
        }
    }
    if text.len() != 2 * N {
        return Err(failed(format!("expected {N} hexadecimal bytes")));
    }
    let mut bytes = [0; N];
    for (out, pair) in bytes.iter_mut().zip(text.as_bytes().as_chunks::<2>().0) {
        *out = digit(pair[0])? * 16 + digit(pair[1])?;
    }
    Ok(bytes)
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

// Serde unit enums also accept tagged objects; these wire fields require strings.
fn string_enum<'de, D, T>(deserializer: D) -> std::result::Result<T, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    let text = String::deserialize(deserializer)?;
    T::deserialize(serde::de::value::StringDeserializer::new(text))
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Api {
    Commitment,
    Opening,
    Point,
    Blob,
    Batch,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum Operation {
    Run,
    Prove,
    Verify,
}

#[derive(Deserialize)]
enum Kind {
    #[serde(rename = "c_kzg")]
    CKzg,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Backend {
    #[serde(deserialize_with = "string_enum")]
    kind: Kind,
    #[serde(deserialize_with = "string_enum")]
    api: Api,
    setup: PathBuf,
    inputs: PathBuf,
    expected: Option<PathBuf>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    format: String,
    backend: Backend,
    #[serde(deserialize_with = "string_enum")]
    operation: Operation,
    plan: Plan,
    proof: PathBuf,
}

impl Request {
    fn validate(&self) -> Result<()> {
        if self.format != "zkc.benchmark-job/0" {
            return Err("unknown benchmark job format".into());
        }
        let Kind::CKzg = self.backend.kind;
        self.plan.validate()?;
        let valid = match self.backend.api {
            Api::Commitment | Api::Opening => self.operation == Operation::Run,
            Api::Point => self.operation == Operation::Verify,
            Api::Blob | Api::Batch => {
                matches!(self.operation, Operation::Prove | Operation::Verify)
            }
        };
        if !valid {
            return Err("unsupported c-kzg API/operation pair".into());
        }
        for path in [&self.backend.setup, &self.backend.inputs] {
            absolute(path)?;
        }
        if let Some(expected) = &self.backend.expected {
            absolute(expected)?;
        } else if self.operation != Operation::Verify {
            return Err("run and prove jobs require expected outputs".into());
        }
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Inputs {
    blobs: Vec<PathBuf>,
    #[serde(default)]
    commitments: Vec<String>,
    z: Option<String>,
    y: Option<String>,
}

impl Inputs {
    fn validate(&self, job: Option<(Api, Operation)>) -> Result<()> {
        if !(1..=MAX_BLOBS).contains(&self.blobs.len()) {
            return Err("inputs require 1..64 blobs".into());
        }
        for path in &self.blobs {
            absolute(path)?;
        }
        if !self.commitments.is_empty() && self.commitments.len() != self.blobs.len() {
            return Err("commitments must match the blob count".into());
        }
        if let Some((api, operation)) = job {
            if api != Api::Batch && self.blobs.len() != 1 {
                return Err("non-batch calls require exactly one blob".into());
            }
            if (operation == Operation::Verify || operation == Operation::Prove)
                && self.commitments.len() != self.blobs.len()
            {
                return Err("verification and blob proving require one commitment per blob".into());
            }
            if matches!(api, Api::Opening | Api::Point) && self.z.is_none() {
                return Err("opening and point calls require z".into());
            }
            if api == Api::Point && self.y.is_none() {
                return Err("point verification requires y".into());
            }
        }
        Ok(())
    }

    fn decode(self) -> Result<Decoded> {
        // Keep large upstream Blob values out of nested iterator/result frames.
        let mut blobs = Vec::with_capacity(self.blobs.len());
        for path in &self.blobs {
            match Blob::from_bytes(&read(path)?) {
                Ok(blob) => blobs.push(blob),
                Err(error) => return Err(failed(error)),
            }
        }
        Ok(Decoded {
            blobs,
            commitments: self
                .commitments
                .iter()
                .map(|text| Ok(Bytes48::new(decode_hex(text)?)))
                .collect::<Result<_>>()?,
            z: self
                .z
                .as_deref()
                .map(|text| decode_hex(text).map(Bytes32::new))
                .transpose()?,
            y: self
                .y
                .as_deref()
                .map(|text| decode_hex(text).map(Bytes32::new))
                .transpose()?,
        })
    }
}

struct Decoded {
    blobs: Vec<Blob>,
    commitments: Vec<Bytes48>,
    z: Option<Bytes32>,
    y: Option<Bytes32>,
}

fn decode_proofs(bytes: &[u8], count: usize) -> Result<Vec<Bytes48>> {
    if bytes.len() != PROOF_BYTES * count {
        return Err(Failure::Rejected(format!(
            "expected {} proof bytes, got {}",
            PROOF_BYTES * count,
            bytes.len()
        )));
    }
    bytes
        .as_chunks::<PROOF_BYTES>()
        .0
        .iter()
        .map(|bytes| Bytes48::from_bytes(bytes).map_err(failed))
        .collect()
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Prepared {
    commitments: Vec<String>,
    proofs: Vec<String>,
    point_proof: Option<String>,
    y: Option<String>,
}

fn load_setup(path: &Path) -> Result<(KzgSettings, u128)> {
    let start = Instant::now();
    let settings = KzgSettings::load_trusted_setup_file(path, 0);
    let elapsed_ns = start.elapsed().as_nanos();
    Ok((settings.map_err(failed)?, elapsed_ns))
}

fn prepare(inputs: &Path, setup: &Path) -> Result<Value> {
    let inputs: Inputs = read_json(inputs)?;
    inputs.validate(None)?;
    let decoded = inputs.decode()?;
    let (settings, _) = load_setup(setup)?;
    let mut commitments = Vec::new();
    let mut proofs = Vec::new();
    for blob in &decoded.blobs {
        let commitment = settings.blob_to_kzg_commitment(blob).map_err(failed)?;
        let proof = settings
            .compute_blob_kzg_proof(blob, &commitment.to_bytes())
            .map_err(failed)?;
        commitments.push(encode_hex(commitment.to_bytes().as_slice()));
        proofs.push(encode_hex(proof.to_bytes().as_slice()));
    }
    let (point_proof, y) = if let Some(z) = &decoded.z {
        let (proof, y) = settings
            .compute_kzg_proof(&decoded.blobs[0], z)
            .map_err(failed)?;
        (
            Some(encode_hex(proof.to_bytes().as_slice())),
            Some(encode_hex(y.as_slice())),
        )
    } else {
        (None, None)
    };
    serde_json::to_value(Prepared {
        commitments,
        proofs,
        point_proof,
        y,
    })
    .map_err(failed)
}

enum Expected {
    Entry(Value),
    Proof(Vec<u8>),
    Acceptance,
}

fn expected(request: &Request, count: usize) -> Result<Expected> {
    if request.operation == Operation::Verify {
        return Ok(Expected::Acceptance);
    }
    let path = request.backend.expected.as_ref().unwrap();
    if request.operation == Operation::Run {
        return Ok(Expected::Entry(read_json(path)?));
    }
    let bytes = read(path)?;
    if bytes.len() != count * PROOF_BYTES {
        return Err("expected proof has the wrong byte length".into());
    }
    Ok(Expected::Proof(bytes))
}

enum Output {
    Commitment(Upstream<Vec<u8>>),
    Opening(Upstream<(Vec<u8>, Vec<u8>)>),
    Proof(Upstream<Vec<u8>>),
    Verified(Upstream<bool>),
}

/// Only upstream calls and construction of their returned bytes belong here.
fn execute(
    settings: &KzgSettings,
    request: &Request,
    inputs: &Decoded,
    proofs: &[Bytes48],
) -> Output {
    match (request.backend.api, request.operation) {
        (Api::Commitment, Operation::Run) => Output::Commitment(
            settings
                .blob_to_kzg_commitment(&inputs.blobs[0])
                .map(|commitment| commitment.to_bytes().as_slice().to_vec()),
        ),
        (Api::Opening, Operation::Run) => Output::Opening(
            settings
                .compute_kzg_proof(&inputs.blobs[0], inputs.z.as_ref().unwrap())
                .map(|(proof, y)| (proof.to_bytes().as_slice().to_vec(), y.as_slice().to_vec())),
        ),
        (Api::Point, Operation::Verify) => Output::Verified(settings.verify_kzg_proof(
            &inputs.commitments[0],
            inputs.z.as_ref().unwrap(),
            inputs.y.as_ref().unwrap(),
            &proofs[0],
        )),
        (Api::Blob | Api::Batch, Operation::Prove) => Output::Proof((|| {
            let mut bytes = Vec::with_capacity(inputs.blobs.len() * PROOF_BYTES);
            for (blob, commitment) in inputs.blobs.iter().zip(&inputs.commitments) {
                bytes.extend_from_slice(
                    settings
                        .compute_blob_kzg_proof(blob, commitment)?
                        .to_bytes()
                        .as_slice(),
                );
            }
            Ok(bytes)
        })()),
        (Api::Blob, Operation::Verify) => Output::Verified(settings.verify_blob_kzg_proof(
            &inputs.blobs[0],
            &inputs.commitments[0],
            &proofs[0],
        )),
        (Api::Batch, Operation::Verify) => Output::Verified(settings.verify_blob_kzg_proof_batch(
            &inputs.blobs,
            &inputs.commitments,
            proofs,
        )),
        _ => unreachable!("validated API/operation pair"),
    }
}

fn check_equal<T: PartialEq + ?Sized>(actual: &T, expected: &T) -> Result<()> {
    if actual != expected {
        return Err(Failure::IncorrectResult(
            "output differs from expected result".into(),
        ));
    }
    Ok(())
}

fn accepted(result: Upstream<bool>) -> Result<()> {
    match result {
        Ok(true) => Ok(()),
        Ok(false) => Err(Failure::Rejected(
            "upstream verification returned false".into(),
        )),
        Err(error) => Err(Failure::Rejected(error.to_string())),
    }
}

fn retain_proof(path: &Path, bytes: &[u8], proofs: &mut Vec<Value>) -> Result<()> {
    let retained = path.with_extension(format!("{}.proof", proofs.len()));
    std::fs::write(&retained, bytes).map_err(failed)?;
    proofs.push(json!({
        "path":retained, "bytes":bytes.len(), "sha256":encode_hex(&Sha256::digest(bytes))
    }));
    // Preserve the final produced proof as well as every individual invocation.
    std::fs::write(path, bytes).map_err(failed)
}

fn observe(
    output: Output,
    expected: &Expected,
    request: &Request,
    retained: &mut Vec<Value>,
) -> Result<()> {
    match (output, expected) {
        (Output::Commitment(result), Expected::Entry(expected)) => {
            let commitment = result.map_err(failed)?;
            check_equal(
                &json!({"format":"zkc.entry-outputs/0", "value":{"P":{"commitment":commitment}}}),
                expected,
            )
        }
        (Output::Opening(result), Expected::Entry(expected)) => {
            let (proof, y) = result.map_err(failed)?;
            check_equal(
                &json!({"format":"zkc.entry-outputs/0", "value":{"P":{"proof":proof,"y":y}}}),
                expected,
            )
        }
        (Output::Proof(result), Expected::Proof(expected)) => {
            let bytes = result.map_err(failed)?;
            retain_proof(&request.proof, &bytes, retained)?;
            // The common harness cross-verifies every retained proof after the
            // measurement schedule, keeping verification out of prover caches.
            check_equal(&bytes, expected)
        }
        (Output::Verified(result), Expected::Acceptance) => accepted(result),
        _ => unreachable!("validated operation and expected output"),
    }
}

fn worker(request_path: &Path) -> Result<Value> {
    let decode_start = Instant::now();
    let mut request: Request = read_json(request_path)?;
    request.validate()?;
    // Preserve the standard worker's current-directory resolution for proof paths.
    request.proof = std::path::absolute(&request.proof).map_err(failed)?;
    let inputs: Inputs = read_json(&request.backend.inputs)?;
    inputs.validate(Some((request.backend.api, request.operation)))?;
    let inputs = inputs.decode()?;
    let count = inputs.blobs.len();
    let proof_count = if request.backend.api == Api::Point {
        1
    } else {
        count
    };
    let proofs = if request.operation == Operation::Verify {
        decode_proofs(&read(&request.proof)?, proof_count)?
    } else {
        Vec::new()
    };
    let expected = expected(&request, count)?;
    let input_decode_ns = decode_start.elapsed().as_nanos();
    let (settings, setup_load_ns) = load_setup(&request.backend.setup)?;
    let mut retained = Vec::new();
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| Ok(execute(&settings, &request, &inputs, &proofs)),
        |output| observe(output, &expected, &request, &mut retained),
    )?;
    Ok(json!({
        "format":"zkc.benchmark-worker/0", "status":"passed",
        "boundary":"reference_kzg_call", "samples":samples,
        "proof_bytes":if request.operation == Operation::Run {0} else {PROOF_BYTES * proof_count},
        "admission_ns":setup_load_ns, "process_peak_rss_bytes":evidence::peak_rss(),
        "proofs":retained, "build":evidence::build(), "process":evidence::process(),
        "timer_floor_ns":evidence::timer_floor_ns(),
        "diagnostics":{
            "api":request.backend.api, "blob_count":count, "setup_load_ns":setup_load_ns,
            "input_decode_ns":input_decode_ns, "precompute":0,
            "input_decode_scope":"request, input and expected-result reads and decoding",
            "threading":"upstream single-threaded EIP-4844 API"
        }, "lifecycle":null
    }))
}

fn run(args: &[OsString]) -> Result<Value> {
    match args {
        [flag, inputs, setup] if flag == "--prepare" => {
            prepare(Path::new(inputs), Path::new(setup))
        }
        [request] if request != "--prepare" => worker(Path::new(request)),
        _ => Err(
            "usage: zkc-c-kzg-benchmarks [--prepare INPUTS.json SETUP.txt | REQUEST.json]".into(),
        ),
    }
}

fn main() {
    let (value, code) = match run(&std::env::args_os().skip(1).collect::<Vec<_>>()) {
        Ok(report) => (report, 0),
        Err(error) => (error.report(), 1),
    };
    println!("{value}");
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Scratch(PathBuf);

    impl Scratch {
        fn new() -> Self {
            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path =
                std::env::temp_dir().join(format!("zkc-c-kzg-{}-{nonce}", std::process::id()));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn job(api: &str, operation: &str) -> Value {
        json!({
            "format":"zkc.benchmark-job/0", "operation":operation,
            "backend":{"kind":"c_kzg", "api":api, "setup":"/setup.txt",
                "inputs":"/inputs.json", "expected":"/expected.json"},
            "plan":{"warmups":1,"samples":2,"iterations":3}, "proof":"/out.proof"
        })
    }

    fn inputs(count: usize, commitments: usize) -> Inputs {
        Inputs {
            blobs: vec![PathBuf::from("/blob.bin"); count],
            commitments: vec!["00".repeat(48); commitments],
            z: Some("00".repeat(32)),
            y: Some("00".repeat(32)),
        }
    }

    #[test]
    fn strict_job_fields_and_enums() {
        for (field, tagged) in [
            ("kind", json!({"c_kzg":null})),
            ("api", json!({"blob":null})),
        ] {
            let mut value = job("blob", "verify");
            value["backend"][field] = tagged;
            assert!(serde_json::from_value::<Request>(value).is_err());
        }
        let mut tagged = job("blob", "verify");
        tagged["operation"] = json!({"verify":null});
        assert!(serde_json::from_value::<Request>(tagged).is_err());
        for bad in [
            {
                let mut value = job("blob", "verify");
                value["extra"] = json!(true);
                value
            },
            {
                let mut value = job("blob", "verify");
                value["backend"]["extra"] = json!(true);
                value
            },
            {
                let mut value = job("blob", "verify");
                value["plan"]["extra"] = json!(true);
                value
            },
            {
                let mut value = job("blob", "verify");
                value["backend"]["kind"] = json!("host");
                value
            },
            job("unknown", "verify"),
            job("blob", "unknown"),
        ] {
            assert!(serde_json::from_value::<Request>(bad).is_err());
        }
        let duplicate = serde_json::to_string(&job("blob", "verify"))
            .unwrap()
            .replacen(
                "\"operation\":\"verify\"",
                "\"operation\":\"verify\",\"operation\":\"verify\"",
                1,
            );
        assert!(serde_json::from_str::<Request>(&duplicate).is_err());
        for key in ["format", "backend", "operation", "plan", "proof"] {
            let mut value = job("blob", "verify");
            value.as_object_mut().unwrap().remove(key);
            assert!(serde_json::from_value::<Request>(value).is_err(), "{key}");
        }
    }

    #[test]
    fn operation_matrix_is_exact() {
        for api in ["commitment", "opening", "point", "blob", "batch"] {
            for operation in ["run", "prove", "verify"] {
                let valid = matches!(
                    (api, operation),
                    ("commitment" | "opening", "run")
                        | ("point", "verify")
                        | ("blob" | "batch", "prove" | "verify")
                );
                let request: Request = serde_json::from_value(job(api, operation)).unwrap();
                assert_eq!(request.validate().is_ok(), valid, "{api}/{operation}");
            }
        }
    }

    #[test]
    fn invalid_format_plan_paths_and_missing_expectations_fail() {
        for bad in [
            {
                let mut value = job("blob", "prove");
                value["format"] = json!("zkc.benchmark-job/1");
                value
            },
            {
                let mut value = job("blob", "prove");
                value["plan"]["samples"] = json!(0);
                value
            },
            {
                let mut value = job("blob", "prove");
                value["plan"]["iterations"] = json!(0);
                value
            },
            {
                let mut value = job("blob", "prove");
                value["plan"]["iterations"] = json!(1_000_001);
                value
            },
            {
                let mut value = job("blob", "prove");
                value["backend"]["setup"] = json!("relative.txt");
                value
            },
            {
                let mut value = job("blob", "prove");
                value["backend"]["inputs"] = json!("relative.json");
                value
            },
            {
                let mut value = job("blob", "prove");
                value["backend"]["expected"] = json!("relative.json");
                value
            },
        ] {
            let request: Request = serde_json::from_value(bad).unwrap();
            assert!(matches!(request.validate(), Err(Failure::Failed(_))));
        }
        let mut relative_proof = job("blob", "verify");
        relative_proof["proof"] = json!("relative.proof");
        let request: Request = serde_json::from_value(relative_proof).unwrap();
        assert!(request.validate().is_ok());
        for (api, operation) in [
            ("commitment", "run"),
            ("blob", "prove"),
            ("point", "verify"),
        ] {
            let mut value = job(api, operation);
            value["backend"].as_object_mut().unwrap().remove("expected");
            let request: Request = serde_json::from_value(value).unwrap();
            assert_eq!(request.validate().is_ok(), operation == "verify");
        }
    }

    #[test]
    fn inputs_are_strict_and_commitments_default_to_empty() {
        let input: Inputs = serde_json::from_value(json!({"blobs":["/blob.bin"]})).unwrap();
        assert!(input.commitments.is_empty());
        assert!(input.z.is_none());
        assert!(input.y.is_none());
        assert!(serde_json::from_value::<Inputs>(json!({"blobs":[],"other":1})).is_err());
        assert!(serde_json::from_str::<Inputs>(r#"{"blobs":[],"blobs":[]}"#).is_err());
        assert!(serde_json::from_value::<Inputs>(json!({"commitments":[]})).is_err());
        let mut input = inputs(1, 0);
        input.blobs[0] = "relative.bin".into();
        assert!(input.validate(None).is_err());
    }

    #[test]
    fn blob_and_commitment_counts_are_bounded() {
        for count in [0, 1, 4, 16, 64, 65] {
            assert_eq!(
                inputs(count, 0).validate(None).is_ok(),
                (1..=64).contains(&count)
            );
            for commitments in [0, count, count + 1] {
                let input = inputs(count, commitments);
                for operation in [Operation::Prove, Operation::Verify] {
                    let valid = (1..=64).contains(&count) && commitments == count;
                    assert_eq!(input.validate(Some((Api::Batch, operation))).is_ok(), valid);
                    assert_eq!(
                        input.validate(Some((Api::Blob, operation))).is_ok(),
                        valid && count == 1
                    );
                }
            }
        }
        for api in [Api::Commitment, Api::Opening] {
            assert!(inputs(1, 0).validate(Some((api, Operation::Run))).is_ok());
            assert!(inputs(2, 0).validate(Some((api, Operation::Run))).is_err());
        }
    }

    #[test]
    fn opening_and_point_arguments_are_required() {
        let mut input = inputs(1, 1);
        assert!(
            input
                .validate(Some((Api::Point, Operation::Verify)))
                .is_ok()
        );
        input.y = None;
        assert!(
            input
                .validate(Some((Api::Point, Operation::Verify)))
                .is_err()
        );
        assert!(input.validate(Some((Api::Opening, Operation::Run))).is_ok());
        input.z = None;
        assert!(
            input
                .validate(Some((Api::Opening, Operation::Run)))
                .is_err()
        );
        assert!(
            input
                .validate(Some((Api::Point, Operation::Verify)))
                .is_err()
        );
    }

    #[test]
    fn hexadecimal_decode_refuses_bad_width_and_unicode_without_panicking() {
        assert_eq!(decode_hex::<2>("01Af").unwrap(), [1, 175]);
        for bad in ["", "0", "001", "00000", "0x00", "gggg", "éé"] {
            assert!(decode_hex::<2>(bad).is_err(), "{bad}");
        }
        assert!(decode_hex::<32>(&"00".repeat(32)).is_ok());
        assert!(decode_hex::<48>(&"00".repeat(48)).is_ok());
    }

    #[test]
    fn proof_shapes_refuse_truncation_and_trailing_bytes() {
        for count in [1, 4, 16, 64] {
            let bytes = vec![0; count * PROOF_BYTES];
            assert_eq!(decode_proofs(&bytes, count).unwrap().len(), count);
            assert!(matches!(
                decode_proofs(&bytes[..bytes.len() - 1], count),
                Err(Failure::Rejected(_))
            ));
            assert!(matches!(
                decode_proofs(&[bytes.as_slice(), &[0]].concat(), count),
                Err(Failure::Rejected(_))
            ));
        }
        assert!(matches!(decode_proofs(&[], 1), Err(Failure::Rejected(_))));
    }

    #[test]
    fn typed_blob_decode_requires_exact_raw_size() {
        let scratch = Scratch::new();
        let path = scratch.0.join("blob.bin");
        for size in [131071, 131072, 131073] {
            std::fs::write(&path, vec![0; size]).unwrap();
            let mut input = inputs(1, 0);
            input.blobs[0] = path.clone();
            assert_eq!(input.decode().is_ok(), size == 131072);
        }
        let mut input = inputs(1, 0);
        input.blobs[0] = path;
        std::fs::write(&input.blobs[0], vec![0; 131072]).unwrap();
        input.z = Some("00".repeat(31));
        assert!(input.decode().is_err());
    }

    #[test]
    fn malformed_proof_is_rejected_before_loading_setup() {
        let scratch = Scratch::new();
        let blob = scratch.0.join("blob.bin");
        let input = scratch.0.join("inputs.json");
        let proof = scratch.0.join("short.proof");
        let request = scratch.0.join("job.json");
        std::fs::write(&blob, vec![0; 131072]).unwrap();
        std::fs::write(
            &input,
            json!({"blobs":[blob], "commitments":["00".repeat(48)]}).to_string(),
        )
        .unwrap();
        let mut value = job("blob", "verify");
        value["backend"]["inputs"] = json!(input);
        value["backend"]["setup"] = json!(scratch.0.join("missing-setup.txt"));
        value["proof"] = json!(proof);
        std::fs::write(&request, value.to_string()).unwrap();
        for size in [0, 47, 49] {
            std::fs::write(&proof, vec![0; size]).unwrap();
            assert!(matches!(worker(&request), Err(Failure::Rejected(_))));
        }
    }

    #[test]
    fn expected_proofs_require_exact_raw_bytes_independent_of_extension() {
        let scratch = Scratch::new();
        let raw = scratch.0.join("expected.proof");
        let other = scratch.0.join("expected.data");
        let mut request: Request = serde_json::from_value(job("batch", "prove")).unwrap();
        let bytes = vec![7; 2 * PROOF_BYTES];
        std::fs::write(&raw, &bytes).unwrap();
        std::fs::write(&other, &bytes).unwrap();
        for path in [raw.clone(), other] {
            request.backend.expected = Some(path);
            let Expected::Proof(actual) = expected(&request, 2).unwrap() else {
                panic!("proof bytes")
            };
            assert_eq!(actual, bytes);
            assert!(matches!(expected(&request, 1), Err(Failure::Failed(_))));
        }
        request.backend.expected = Some(raw.clone());
        std::fs::write(raw, &bytes[..bytes.len() - 1]).unwrap();
        assert!(matches!(expected(&request, 2), Err(Failure::Failed(_))));
    }

    #[test]
    fn refusal_and_result_statuses_are_distinct() {
        assert!(accepted(Ok(true)).is_ok());
        assert_eq!(
            accepted(Ok(false)).unwrap_err().report()["status"],
            "rejected"
        );
        let error = Bytes48::from_bytes(&[]).unwrap_err();
        assert_eq!(
            accepted(Err(error)).unwrap_err().report()["status"],
            "rejected"
        );
        assert_eq!(
            check_equal(&[1], &[2]).unwrap_err().report()["status"],
            "incorrect-result"
        );
        let report = failed("invalid job").report();
        assert_eq!(
            report,
            json!({"format":"zkc.benchmark-worker/0", "status":"failed", "error":"invalid job"})
        );
    }

    #[test]
    fn proof_retention_includes_every_warmup_and_iteration() {
        let scratch = Scratch::new();
        let path = scratch.0.join("final.proof");
        let mut proofs = Vec::new();
        let mut invocation = 0;
        let samples = measure::measure(
            Plan {
                warmups: 1,
                samples: 2,
                iterations: 2,
            },
            || Ok(()),
            |_| Ok(vec![7; PROOF_BYTES]),
            |bytes| {
                invocation += 1;
                retain_proof(&path, &bytes, &mut proofs)
            },
        )
        .unwrap();
        assert_eq!(samples.len(), 3);
        assert_eq!(samples[0].phase, "warmup");
        assert_eq!(invocation, 6);
        assert_eq!(proofs.len(), 6);
        let bytes = vec![7; PROOF_BYTES];
        assert_eq!(read(&path).unwrap(), bytes);
        for proof in proofs {
            let retained = Path::new(proof["path"].as_str().unwrap());
            assert_eq!(retained.parent(), path.parent());
            assert_eq!(read(retained).unwrap(), bytes);
            assert_eq!(proof["bytes"], PROOF_BYTES);
            assert_eq!(proof["sha256"], encode_hex(&Sha256::digest(&bytes)));
        }
    }
}
