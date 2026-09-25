//! Persistent phase at actual table-provider calls, separate from trace admission.
use super::{ChallengeProvider, FieldKernel, TableBindings};
use crate::buffer::BufferStore;
use crate::{EndpointEntry, Error, PhaseEvidence};
use serde_json::{Value, json};

pub const ENDPOINT_PROFILE: &str = "table-endpoint/1";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Ready,
    Sent,
    /// A host failure may have interrupted a call after effects. No reply or
    /// stopped-call completion is known; re-admission must not guess a phase.
    Unknown,
}
impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Ready => "ready",
            Self::Sent => "sent",
            Self::Unknown => "unknown",
        }
    }
    pub fn decode(value: &Value) -> Result<Self, Error> {
        match value.as_str() {
            Some("ready") => Ok(Self::Ready),
            Some("sent") => Ok(Self::Sent),
            Some("unknown") => Ok(Self::Unknown),
            _ => Err(Error("invalid-endpoint-phase")),
        }
    }
}
pub(super) struct Endpoint {
    pub role: String,
    pub phase: Phase,
}
#[derive(Clone, Copy)]
pub(super) enum Call {
    Write,
    Send,
    Draw,
}

/// A single call's completion authority. Dropping it leaves the endpoint
/// unknown. It cannot be copied or reused to restore an earlier phase.
pub(super) struct PendingCall {
    call: Call,
    before: Phase,
}

impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> TableBindings<K, P, S> {
    /// The host supplies initial state under its deployment contract. Neither
    /// a certificate nor a serialized plan constructs or resets a live endpoint.
    pub fn with_endpoint(mut self, role: String, phase: Phase) -> Result<Self, Error> {
        if self.endpoint.is_some() {
            return Err(Error("endpoint-already-bound"));
        }
        self.endpoint = Some(Endpoint { role, phase });
        Ok(self)
    }
    pub fn endpoint_entry(&self) -> Option<EndpointEntry> {
        self.endpoint.as_ref().map(|e| EndpointEntry {
            role: e.role.clone(),
            phase: json!(e.phase.name()),
        })
    }
    pub(super) fn check_entry(
        &self,
        role: &str,
        evidence: Option<&PhaseEvidence>,
    ) -> Result<(), Error> {
        let Some(endpoint) = &self.endpoint else {
            return if evidence.and_then(|e| e.entry.as_ref()).is_some() {
                Err(Error("unsupported-endpoint-binding"))
            } else {
                Ok(())
            };
        };
        if endpoint.phase == Phase::Unknown {
            return Err(Error("unknown-endpoint-state"));
        }
        if endpoint.role != "prover" || role != endpoint.role {
            return Err(Error("endpoint-role-mismatch"));
        }
        let evidence = evidence.ok_or(Error("endpoint-evidence-required"))?;
        if evidence.profile != ENDPOINT_PROFILE {
            return Err(Error("endpoint-policy-mismatch"));
        }
        let entry = evidence
            .entry
            .as_ref()
            .ok_or(Error("endpoint-evidence-required"))?;
        if Some(entry) != self.endpoint_entry().as_ref() {
            return Err(Error("endpoint-entry-mismatch"));
        }
        Ok(())
    }
    pub(super) fn begin_call(&mut self, call: Call) -> Result<Option<PendingCall>, Error> {
        let Some(endpoint) = &mut self.endpoint else {
            return Ok(None);
        };
        if endpoint.role != "prover" {
            return Err(Error("primitive-owner-mismatch"));
        }
        let before = endpoint.phase;
        if before == Phase::Unknown {
            return Err(Error("unknown-endpoint-state"));
        }
        if matches!(
            (call, before),
            (Call::Send, Phase::Sent) | (Call::Draw, Phase::Ready)
        ) {
            return Err(Error("endpoint-call-not-enabled"));
        }
        // Leave unknown on any error or panic before a legitimate completion.
        endpoint.phase = Phase::Unknown;
        Ok(Some(PendingCall { call, before }))
    }
    pub(super) fn complete_call(&mut self, pending: Option<PendingCall>, returned: bool) {
        if let (Some(endpoint), Some(PendingCall { call, before })) = (&mut self.endpoint, pending)
        {
            endpoint.phase = if !returned {
                before
            } else {
                match call {
                    Call::Write => before,
                    Call::Send => Phase::Sent,
                    Call::Draw => Phase::Ready,
                }
            };
        }
    }
}
