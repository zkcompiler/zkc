//! Retained caller requirements checked against an immutable physical candidate.
use super::{CheckedBundle, construction::compiler_run, io};
use serde_json::Value as Json;

/// Caller-owned authority and its proposed closure certificate. Constructing
/// this value only checks bounded JSON ingress. It does not prove the laws in
/// the contract or admit a candidate. The caller authenticates the contract and
/// authorizes each actual invocation's application context independently.
pub struct ClaimRequirements {
    contract: Vec<u8>,
    certificate: Vec<u8>,
}
impl ClaimRequirements {
    pub fn from_slices(contract: &[u8], certificate: &[u8]) -> Result<Self, String> {
        for bytes in [contract, certificate] {
            io::parse(bytes, 1 << 20)?;
        }
        Ok(Self {
            contract: contract.into(),
            certificate: certificate.into(),
        })
    }
    pub fn contract(&self) -> &[u8] {
        &self.contract
    }
    pub fn certificate(&self) -> &[u8] {
        &self.certificate
    }
}

/// Installed physical pipeline inputs, not a transformation proof. Explicit
/// implementation selection uses the compiler's existing bounded JSON format;
/// any snapshot pin names the constructed source entering physical planning.
#[derive(Default)]
pub struct PhysicalChoices {
    pub linear_contractions: bool,
    pub release_storage: bool,
    implementations: Option<Vec<u8>>,
}
impl PhysicalChoices {
    pub fn with_implementations(mut self, bytes: &[u8]) -> Result<Self, String> {
        io::parse(bytes, 1 << 20)?;
        self.implementations = Some(bytes.into());
        Ok(self)
    }
}

pub(super) struct CheckedRequirements {
    pub requirements: ClaimRequirements,
    // Keep the recipe that the checker used beside its actual retained subject.
    pub choices: PhysicalChoices,
}

pub(super) fn check(
    bundle: &CheckedBundle,
    compiler: &str,
    requirements: ClaimRequirements,
    choices: PhysicalChoices,
) -> Result<CheckedRequirements, String> {
    let encode = |j: &Json| serde_json::to_vec(j).map_err(|_| "artifact-json".to_owned());
    // These are the captured, admitted subjects, never newly reopened paths.
    let source = encode(&bundle.source)?;
    let descriptor = encode(&bundle.descriptor)?;
    let construction = encode(&bundle.manifest)?;
    let mut options = Vec::new();
    if choices.linear_contractions {
        options.push(("--linear-contractions", None));
    }
    if choices.release_storage {
        options.push(("--release-storage", None));
    }
    if let Some(selection) = &choices.implementations {
        options.push(("--implementations", Some(selection.as_slice())));
    }
    let response = compiler_run(
        compiler,
        "claim-check-lowering",
        &[
            ("source", &source),
            ("contract", &requirements.contract),
            ("certificate", &requirements.certificate),
            ("descriptor", &descriptor),
            ("construction", &construction),
            ("physical", bundle.admitted.bytes()),
        ],
        &options,
        4096,
    )?;
    let contract = io::parse(&requirements.contract, 1 << 20)?;
    let laws = contract
        .get(8)
        .and_then(Json::as_array)
        .ok_or("artifact-claim-response")?
        .len();
    let expected = format!(
        "checked conditional claim closure; {laws} caller trust premises; no cryptographic security theorem\n"
    );
    if response != expected.as_bytes() {
        return Err("artifact-claim-response".into());
    }
    Ok(CheckedRequirements {
        requirements,
        choices,
    })
}

#[cfg(test)]
mod tests;
