//! Bounded document calls over the common schema decoder and admitted proof Host.
//! References name caller-owned bytes; they confer no filesystem capability.
use super::{
    AttemptOptions, EntryError, EntryPhase, NamedValues, ProofCall, ProofEntry, ProofOperation,
    ProofRequest, RoleInputs,
    inputs::{Decoder, InputError, InputGroup, Resolver},
};
use crate::execution::{Capacity, InputSource};
use std::{collections::BTreeMap, sync::Arc};

/// Non-value invocation configuration, independent of document transport.
#[derive(Default)]
pub struct ProofCallOptions {
    pub context: Vec<u8>,
    pub transcript_budget: Option<u64>,
    pub setups: BTreeMap<String, Vec<u8>>,
    pub services: BTreeMap<String, BTreeMap<String, u64>>,
}

/// One decoder and one aggregate budget for the complete memory request.
pub struct Documents<'a> {
    decoder: Decoder,
    bindings: &'a BTreeMap<String, Arc<Vec<u8>>>,
}
impl<'a> Documents<'a> {
    pub fn new(
        capacity: Capacity,
        installation: zkc_cpu::CpuInstallation,
        bindings: &'a BTreeMap<String, Arc<Vec<u8>>>,
    ) -> Result<Self, String> {
        capacity.validate()?;
        if bindings.len() > 1024 {
            return Err("entry-input-reference-limit".into());
        }
        let mut total = 0usize;
        for bytes in bindings.values() {
            capacity.check_wire(bytes.len())?;
            total = total
                .checked_add(bytes.len())
                .filter(|n| *n <= capacity.values.total_bytes)
                .ok_or("entry-request-limit")?;
        }
        Ok(Self {
            decoder: Decoder::with_installation(capacity, installation)?,
            bindings,
        })
    }
    pub fn load(
        &mut self,
        group: &InputGroup<'_>,
        bytes: Option<&[u8]>,
    ) -> Result<NamedValues, InputError> {
        self.decoder
            .decode_optional(group, bytes, Some(&mut Bindings(self.bindings)))
    }
}
struct Bindings<'a>(&'a BTreeMap<String, Arc<Vec<u8>>>);
impl Resolver for Bindings<'_> {
    fn resolve(&mut self, name: &str) -> Result<InputSource, String> {
        self.0
            .get(name)
            .cloned()
            .map(InputSource::from_bytes)
            .ok_or("entry-input-reference".into())
    }
}

impl ProofEntry {
    /// Check output codec feasibility before any source is loaded. Public data
    /// precedes the witness; setup import and candidate proof handling retain
    /// their existing preflight/execute phases. File and memory adapters share it.
    pub fn preflight_document_call(
        &self,
        operation: ProofOperation,
        options: ProofCallOptions,
        attempts: Option<AttemptOptions>,
        encode_results: bool,
        mut load: impl FnMut(&InputGroup<'_>) -> Result<NamedValues, InputError>,
    ) -> Result<ProofCall<'_>, EntryError> {
        self.observe_setups(&options.setups);
        if encode_results {
            self.check_result_encoding(operation)
                .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
        }
        let groups = self.interface().input_groups();
        let public = load(&groups[0]).map_err(EntryError::input)?;
        let private = if operation == ProofOperation::Prove {
            load(&groups[1]).map_err(EntryError::input)?
        } else {
            NamedValues::new()
        };
        let role = self
            .interface()
            .proof_role(operation)
            .ok_or_else(|| EntryError::new(EntryPhase::Request, "entry-job-kind"))?;
        let mut services = options.services;
        let selected = services.remove(role).unwrap_or_default();
        if !services.is_empty() {
            return Err(EntryError::new(EntryPhase::Request, "entry-service-names"));
        }
        self.preflight_call(
            operation,
            ProofRequest {
                public,
                private: RoleInputs {
                    inputs: private,
                    services: selected,
                },
                context: options.context,
                transcript_budget: options.transcript_budget,
                setups: options.setups,
            },
            attempts,
            encode_results,
        )
    }
    /// Bounded resident documents, with the same input/setup/proof precedence as
    /// file calls. Proof bytes are supplied later to ProofCall::execute.
    #[allow(clippy::too_many_arguments)]
    pub fn preflight_memory_call(
        &self,
        operation: ProofOperation,
        public: Option<&[u8]>,
        witness: Option<&[u8]>,
        bindings: &BTreeMap<String, Arc<Vec<u8>>>,
        options: ProofCallOptions,
        attempts: Option<AttemptOptions>,
        encode_results: bool,
    ) -> Result<ProofCall<'_>, EntryError> {
        // Construct and bound the source only inside the common codec preflight.
        let mut documents = None;
        self.preflight_document_call(operation, options, attempts, encode_results, |group| {
            if documents.is_none() {
                documents = Some(
                    Documents::new(self.capacity(), self.installation().clone(), bindings)
                        .map_err(|code| InputError {
                            code,
                            path: group.name().into(),
                        })?,
                );
            }
            documents.as_mut().expect("initialized documents").load(
                group,
                if group.name() == "public" {
                    public
                } else {
                    witness
                },
            )
        })
    }
}
