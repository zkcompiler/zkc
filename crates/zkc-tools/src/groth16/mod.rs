//! Groth16 through admitted, compiled PIR. The host binds typed prepared data,
//! role policy and statement context, and adapts proof formats. Polynomial,
//! MSM, blinding and pairing algorithms are all authored in `groth16.pir`.
//!
//! The application must authenticate its complete expected verification key
//! and relation context. Parsing a zkey neither identifies an intended relation
//! nor validates a ceremony. The interoperability fixtures have public trapdoors.
mod codec;
mod project;
mod relation;
use crate::{
    artifact::{ArtifactFailure, ProofReader, ProofWriter},
    noninteractive::{NoninteractiveArtifact, ProofInvocation},
    protocol::{ParticipantChecker, WireBackend},
    snarkjs::{PreparedKey, Witness},
};
use ark_ff::{FftField, Field};
pub use codec::{MAX_JSON_BYTES, Proof, Statement, VerifyingKey};
pub use relation::PreparedRelation;
use std::{collections::BTreeMap, path::Path, process::Command, time::Duration};
use zkc_backends::{
    Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, PublicRolePolicy, Value,
};
use zkc_runtime::interactive::{EntryRole, Identity, LogicalType, PhysicalType};

#[derive(Debug)]
pub struct Error {
    pub code: &'static str,
    pub detail: String,
}
impl Error {
    fn new(code: &'static str) -> Self {
        Self {
            code,
            detail: String::new(),
        }
    }
    fn detail(code: &'static str, detail: impl std::fmt::Display) -> Self {
        Self {
            code,
            detail: detail.to_string(),
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.code,
            if self.detail.is_empty() { "" } else { ": " },
            self.detail
        )
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
fn backend_error(e: impl std::fmt::Display) -> Error {
    Error::detail("groth16-backend", e)
}
fn artifact_error(e: ArtifactFailure) -> Error {
    if matches!(e, ArtifactFailure::Rejected) {
        Error::new("groth16-rejected")
    } else {
        Error::detail("groth16-execution", format!("{e:?}"))
    }
}

/// Explicit fixture workload policy; the backend's ordinary 4096 group default
/// is unchanged. Domain 8192 and variable count 4147 require this larger cap.
pub fn policy() -> Policy {
    Policy {
        max_groups: 32768,
        ..Policy::default()
    }
}

/// Bounded file reader for source, endpoint and public JSON adapters.
pub fn read_bounded(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>> {
    crate::host::io::read_bounded(path, limit).map_err(|error| match error {
        crate::host::io::ReadError::Io(e) => Error::detail("groth16-io", e),
        crate::host::io::ReadError::Limit => Error::new("groth16-file-limit"),
    })
}
fn compiler_output(compiler: &Path, command: &str, source: &Path) -> Result<Vec<u8>> {
    compiler_output_with_libraries(compiler, command, source, &[])
}
fn compiler_output_with_libraries(
    compiler: &Path,
    command: &str,
    source: &Path,
    libraries: &[std::path::PathBuf],
) -> Result<Vec<u8>> {
    let dir = tempfile::tempdir().map_err(|e| Error::detail("groth16-io", e))?;
    let mut invocation = Command::new(compiler);
    invocation
        .arg(command)
        .arg(source)
        .args(libraries.iter().map(|path| {
            let mut argument = std::ffi::OsString::from("--library=");
            argument.push(path);
            argument
        }));
    let output = crate::host::process::capture(
        &mut invocation,
        dir.path(),
        |elapsed| elapsed > Duration::from_secs(120),
        MAX_JSON_BYTES,
        true,
    )
    .map_err(|failure| match failure {
        crate::host::process::Error::Process(e) => Error::detail("groth16-compiler", e),
        crate::host::process::Error::Io(e) => Error::detail("groth16-io", e),
        crate::host::process::Error::Timeout => Error::new("groth16-compiler-timeout"),
        crate::host::process::Error::OutputLimit => Error::new("groth16-compiler-output-limit"),
    })?;
    if !output.status.success() {
        return Err(Error::detail(
            "groth16-compiler",
            String::from_utf8_lossy(&read_bounded(
                output
                    .stderr
                    .as_ref()
                    .expect("stderr capture requested")
                    .path(),
                MAX_JSON_BYTES,
            )?),
        ));
    }
    read_bounded(output.stdout.path(), MAX_JSON_BYTES)
}

#[cfg(all(test, unix))]
mod host_tests {
    use super::*;

    #[test]
    fn compiler_capture_preserves_library_arguments_and_failure_diagnostics() {
        // Use the shell as an argument-reporting fixture: each library remains
        // one OS argument, including spaces, and stderr is diagnostic only.
        let libraries = ["library root/one".into(), "second library".into()];
        let bytes = compiler_output_with_libraries(
            Path::new("/bin/sh"),
            "-c",
            Path::new("printf '%s\\n' \"$0\" \"$1\"; printf warning >&2"),
            &libraries,
        )
        .unwrap();
        assert_eq!(
            bytes,
            b"--library=library root/one\n--library=second library\n"
        );

        let failure = compiler_output(
            Path::new("/bin/sh"),
            "-c",
            Path::new("printf candidate; printf refused >&2; exit 7"),
        )
        .unwrap_err();
        assert_eq!(failure.code, "groth16-compiler");
        assert_eq!(failure.detail, "refused");
    }
}

/// Cached source-relative admitted code. Both depths use this same program.
#[derive(Clone, Debug)]
pub struct PreparedProtocol {
    artifact: NoninteractiveArtifact,
    relation_identity: String,
    relation: Option<std::sync::Arc<PreparedRelation>>,
}
impl PreparedProtocol {
    /// Compile an immutable snapshot, then require the installed independent
    /// Lean source/actual-endpoint correspondence checker. Never bypass it.
    /// This single-file convenience wrapper stages `source` as `protocol.pir`
    /// and the binary R1CS as `circuit.r1cs`; source must import that relative
    /// asset name. Other assets and library roots require `compile_project`.
    pub fn compile(
        compiler: impl AsRef<Path>,
        lean: impl AsRef<Path>,
        source: &[u8],
        r1cs: &[u8],
    ) -> Result<Self> {
        if source.len() > 1_048_576 || r1cs.len() > 64 * 1024 * 1024 {
            return Err(Error::new("groth16-source-limit"));
        }
        let dir = tempfile::tempdir().map_err(|e| Error::detail("groth16-io", e))?;
        let path = dir.path().join("protocol.pir");
        let asset = dir.path().join("circuit.r1cs");
        std::fs::write(&path, source).map_err(|e| Error::detail("groth16-io", e))?;
        std::fs::write(&asset, r1cs).map_err(|e| Error::detail("groth16-io", e))?;
        Self::compile_project(compiler, lean, &path, &[], &asset)
    }
    /// Reuse application-authenticated cached source and recheck its actual
    /// endpoints. The identity is a declared context matched to source origins;
    /// this path does not reconstruct a relation or prove key correspondence.
    /// The dedicated Groth16 host requires the `Core` rank-one view and the
    /// source/port contract of the maintained example, with Products and
    /// Residuals structurally reachable from `main`. Unlike `compile_project`,
    /// cached source has no retained view inventory or checked descriptor and
    /// cannot be used with `bind_checked`. General protocols use
    /// `NoninteractiveArtifact` directly.
    pub fn prepare(
        source: &[u8],
        endpoints: &[u8],
        lean: impl AsRef<Path>,
        relation_identity: &str,
    ) -> Result<Self> {
        Self::prepare_view(
            source,
            endpoints,
            lean.as_ref(),
            relation_identity,
            "Core",
            &[],
        )
    }
    fn prepare_view(
        source: &[u8],
        endpoints: &[u8],
        lean: &Path,
        relation_identity: &str,
        view: &str,
        rank_one_views: &[String],
    ) -> Result<Self> {
        if source.len() > MAX_JSON_BYTES || endpoints.len() > MAX_JSON_BYTES {
            return Err(Error::new("groth16-code-limit"));
        }
        if !relation::valid_identity(relation_identity) {
            return Err(Error::new("groth16-relation-identity"));
        }
        let source_json: serde_json::Value =
            serde_json::from_slice(source).map_err(|e| Error::detail("groth16-source", e))?;
        project::check_view_use(&source_json, relation_identity, view, rank_one_views)?;
        let domain = Domain::new("P", "admission", "main", None);
        let backend = NativeBackend::new(
            policy(),
            EntryPolicy::new(domain, None, PublicInputs::LocalOnly),
            None,
        )
        .map_err(backend_error)?;
        let checker =
            ParticipantChecker::new(lean).map_err(|e| Error::detail("groth16-checker", e))?;
        let artifact = NoninteractiveArtifact::prepare(
            source,
            endpoints,
            &backend,
            &checker,
            ("main", "P", "V", 0),
        )
        .map_err(|e| Error::detail("groth16-admission", e))?;
        Ok(Self {
            artifact,
            relation_identity: relation_identity.into(),
            relation: None,
        })
    }
    pub fn source(&self) -> &[u8] {
        self.artifact
            .entry()
            .admitted()
            .checked_source()
            .expect("source-relative admission")
    }
    pub fn endpoints(&self) -> &[u8] {
        self.artifact.entry().admitted().bytes()
    }
    pub fn relation_identity(&self) -> &str {
        &self.relation_identity
    }
    pub fn relation(&self) -> Option<&PreparedRelation> {
        self.relation.as_deref()
    }
    /// Bind the actual retained compiled relation to an independently selected
    /// ingress contract. Cached code without an exact descriptor refuses.
    pub fn bind_checked(
        &self,
        contract: &crate::ingress::Groth16Contract,
        statement: Statement,
        context: &[u8],
    ) -> crate::ingress::Result<crate::ingress::CheckedInvocation> {
        contract.bind(self, statement, context)
    }
    /// Bind application-selected public context before any proving or checking.
    /// The relation context is opaque application configuration, not a claim
    /// that a candidate key has been checked against a circuit or ceremony.
    pub fn bind(
        &self,
        key: VerifyingKey,
        statement: Statement,
        relation_context: &[u8],
    ) -> Result<Invocation> {
        if relation_context.is_empty() || relation_context.len() > 4096 {
            return Err(Error::new("groth16-relation-context"));
        }
        if statement.0.len() != key.n_public() {
            return Err(Error::new("groth16-public-count"));
        }
        let mut context = b"zkc.groth16.context/1".to_vec();
        for part in [
            self.relation_identity.as_bytes().to_vec(),
            relation_context.to_vec(),
            key.to_json()?,
            statement.to_json()?,
        ] {
            context.extend((part.len() as u64).to_le_bytes());
            context.extend(part);
        }
        Ok(Invocation {
            protocol: self.clone(),
            key,
            statement,
            context,
        })
    }
}

/// Prepared producer data, independent of code and witness; no hidden prover.
#[derive(Clone, Debug)]
pub struct ProverKey {
    key: VerifyingKey,
    values: BTreeMap<String, Value>,
    n_vars: usize,
    relation: std::sync::Arc<PreparedRelation>,
}
impl ProverKey {
    /// The entire effective public key must match application configuration.
    /// Check shape/root/coset conventions even for programmatically built keys.
    pub fn new(
        key: &PreparedKey,
        expected: &VerifyingKey,
        relation: &PreparedRelation,
    ) -> Result<Self> {
        relation.match_key(key)?;
        let public = VerifyingKey::from_prepared(key)?;
        if &public != expected {
            return Err(Error::new("groth16-key-mismatch"));
        }
        let n = key.domain_size;
        if !(2..=32768).contains(&n)
            || !n.is_power_of_two()
            || key.n_vars > 32768
            || key.n_vars <= key.n_public
            || key.a_query.len() != key.n_vars
            || key.b1_query.len() != key.n_vars
            || key.b2_query.len() != key.n_vars
            || key.h_query.len() != n
            || key.l_query.len() != key.n_vars - key.n_public - 1
            || key.qap_a.rows() != n
            || key.qap_b.rows() != n
            || key.qap_a.columns() != key.n_vars
            || key.qap_b.columns() != key.n_vars
        {
            return Err(Error::new("groth16-key-shape"));
        }
        let root = ark_bn254::Fr::get_root_of_unity(n as u64)
            .ok_or_else(|| Error::new("groth16-domain"))?;
        let shift = ark_bn254::Fr::get_root_of_unity(2 * n as u64)
            .ok_or_else(|| Error::new("groth16-domain"))?;
        if key.domain_root != root || key.coset_shift != shift || shift.square() != root {
            return Err(Error::new("groth16-domain"));
        }
        Ok(Self {
            key: public,
            values: key.values(),
            n_vars: key.n_vars,
            relation: std::sync::Arc::new(relation.clone()),
        })
    }
}

impl ProverKey {
    pub fn binding_record(&self) -> serde_json::Value {
        self.relation.record()
    }
}

/// Production defaults to OS-seeded resource issuance; fixed tapes are compiled
/// only with `test-utils` and must be selected explicitly for each invocation.
#[derive(Clone, Debug, Default)]
pub enum Randomness {
    #[default]
    Os,
    #[cfg(feature = "test-utils")]
    Test { r: ark_bn254::Fr, s: ark_bn254::Fr },
}

/// Prepared expected statement/key invocation. Verification has no prover key
/// or witness dependency. Internal framing binds this exact context and code.
#[derive(Clone, Debug)]
pub struct Invocation {
    protocol: PreparedProtocol,
    key: VerifyingKey,
    statement: Statement,
    context: Vec<u8>,
}
#[derive(Debug)]
pub struct ProducedProof {
    pub proof: Proof,
    pub artifact: Vec<u8>,
}
impl Invocation {
    fn bound(&self) -> ProofInvocation<'_> {
        self.protocol.artifact.bind(&self.context)
    }
    pub fn binding(&self) -> [u8; 32] {
        *self.bound().binding()
    }
    fn backend(&self, role: &EntryRole) -> Result<(NativeBackend, Domain)> {
        let domain = Domain::new(
            &role.role,
            &self.bound().session(),
            "main",
            Some(&role.instance),
        );
        let mut backend = NativeBackend::new(
            policy(),
            EntryPolicy::new(domain.clone(), None, PublicInputs::LocalOnly)
                .with_parameters(role.parameters.clone()),
            None,
        )
        .map_err(backend_error)?;
        if role.role == "V" {
            backend = backend.with_public_role_policy(
                PublicRolePolicy::new(["V".to_owned()]).map_err(backend_error)?,
            );
        }
        Ok((backend, domain))
    }
    fn inputs(&self, role: &EntryRole, mut values: BTreeMap<String, Value>) -> Result<Vec<Value>> {
        let map = self
            .protocol
            .artifact
            .entry()
            .admitted()
            .source_map()
            .ok_or_else(|| Error::new("groth16-source-map"))?;
        let mut ports = BTreeMap::new();
        for (name, value) in std::mem::take(&mut values) {
            if let Some(port) = map.port(&role.instance, &role.role, &name) {
                ports.insert(port.to_owned(), value);
            }
        }
        role.inputs
            .iter()
            .map(|(name, _)| {
                ports
                    .remove(name)
                    .ok_or_else(|| Error::detail("groth16-input-port", name))
            })
            .collect()
    }
    pub fn prove(
        &self,
        key: &ProverKey,
        witness: &Witness,
        randomness: Randomness,
    ) -> Result<ProducedProof> {
        if key.key != self.key || key.relation.identity() != self.protocol.relation_identity {
            return Err(Error::new("groth16-key-mismatch"));
        }
        if witness.0.len() != key.n_vars || witness.0.first() != Some(&ark_bn254::Fr::from(1)) {
            return Err(Error::new("groth16-assignment"));
        }
        if witness.0[1..self.key.n_public() + 1] != *self.statement.0 {
            return Err(Error::new("groth16-statement-mismatch"));
        }
        let role = self.protocol.artifact.entry().producer();
        let (mut backend, domain) = self.backend(role)?;
        let coins = match randomness {
            Randomness::Os => backend.issue_rng_for(Identity::Bn254Fr, domain, 2),
            #[cfg(feature = "test-utils")]
            Randomness::Test { r, s } => backend.issue_test_bn254_tape(domain, 2, vec![r, s]),
        }
        .map_err(backend_error)?;
        let mut values = key.values.clone();
        // The source groups its inputs into structs; each field is the port
        // `input.field`.
        for (port, prepared) in [
            ("qap.matrix_a", "qap_a"),
            ("qap.matrix_b", "qap_b"),
            ("qap.coset", "coset_shift"),
            ("qap.domain_size", "domain_size"),
            ("key.alpha", "alpha1"),
            ("key.beta_g1", "beta1"),
            ("key.beta_g2", "beta2"),
            ("key.delta_g1", "delta1"),
            ("key.delta_g2", "delta2"),
            ("key.a_query", "a_query"),
            ("key.b_g1_query", "b1_query"),
            ("key.b_g2_query", "b2_query"),
            ("key.private_query", "l_query"),
            ("key.h_query", "h_query"),
        ] {
            values.insert(port.into(), key.values[prepared].clone());
        }
        values.insert("assignment".into(), Value::Bn254Vector(witness.0.clone()));
        values.insert(
            "expected_statement".into(),
            Value::Bn254Vector(self.statement.0.clone()),
        );
        for (name, matrix) in ["relation.a", "relation.b", "relation.c"]
            .into_iter()
            .zip(key.relation.values())
        {
            values.insert(name.into(), matrix);
        }
        values.insert("coins".into(), coins);
        let inputs = self.inputs(role, values)?;
        let bound = self.bound();
        let mut producer = bound
            .producer(backend, inputs)
            .map_err(|e| Error::detail("groth16-load", format!("{:?}", e.error)))?;
        let produced = producer.produce().outcome.map_err(artifact_error)?;
        let proof = self.decode_artifact(&produced.proof)?;
        Ok(ProducedProof {
            proof,
            artifact: produced.proof,
        })
    }
    /// Parse internal framing only under the independently expected binding.
    pub fn decode_artifact(&self, bytes: &[u8]) -> Result<Proof> {
        let (backend, _) = self.backend(self.protocol.artifact.entry().verifier())?;
        let mut reader = ProofReader::new(bytes, &self.binding())
            .map_err(|e| Error::detail("groth16-framing", e))?;
        let mut values = Vec::new();
        for name in ["group:bn254.g1", "group:bn254.g2", "group:bn254.g1"] {
            let ty =
                LogicalType::parse(name).map_err(|e| Error::detail("groth16-point-type", e))?;
            let payload = reader
                .message()
                .map_err(|e| Error::detail("groth16-framing", e))?;
            values.push(
                backend
                    .decode(PhysicalType::default_for(ty), payload)
                    .map_err(backend_error)?,
            );
        }
        reader
            .finish()
            .map_err(|e| Error::detail("groth16-framing", e))?;
        match values.as_slice() {
            [Value::Bn254G1(a), Value::Bn254G2(b), Value::Bn254G1(c)] => Ok(Proof {
                a: *a,
                b: *b,
                c: *c,
            }),
            _ => Err(Error::new("groth16-proof-shape")),
        }
    }
    /// Explicitly adapt a bare snarkjs proof to this expected statement/key
    /// context. Bare JSON does not itself carry a source or relation binding.
    pub fn encode_artifact(&self, proof: &Proof) -> Result<Vec<u8>> {
        let (backend, _) = self.backend(self.protocol.artifact.entry().verifier())?;
        let mut writer = ProofWriter::new(&self.binding());
        for value in proof.values() {
            writer
                .message(&backend.encode(&value).map_err(backend_error)?)
                .map_err(|e| Error::detail("groth16-framing", e))?;
        }
        Ok(writer.finish())
    }
    pub fn verify(&self, proof: &Proof) -> Result<()> {
        self.verify_artifact(&self.encode_artifact(proof)?)
    }
    pub fn verify_json(&self, proof: &[u8]) -> Result<()> {
        self.verify(&Proof::from_json(proof)?)
    }
    pub fn verify_artifact(&self, proof: &[u8]) -> Result<()> {
        let role = self.protocol.artifact.entry().verifier();
        let (backend, _) = self.backend(role)?;
        let mut values = self.key.values();
        for (port, prepared) in [
            ("vk.input_query", "ic"),
            ("vk.alpha", "alpha1"),
            ("vk.beta", "beta2"),
            ("vk.gamma", "gamma2"),
            ("vk.delta", "delta2"),
        ] {
            values.insert(port.into(), values[prepared].clone());
        }
        values.insert(
            "statement".into(),
            Value::Bn254Vector(self.statement.0.clone()),
        );
        let inputs = self.inputs(role, values)?;
        let bound = self.bound();
        let mut verifier = bound
            .verifier(backend, inputs)
            .map_err(|e| Error::detail("groth16-load", format!("{:?}", e.error)))?;
        verifier
            .verify(proof, |v| {
                if let Value::Bool(b) = v {
                    Some(*b)
                } else {
                    None
                }
            })
            .outcome
            .map_err(artifact_error)?;
        Ok(())
    }
}
