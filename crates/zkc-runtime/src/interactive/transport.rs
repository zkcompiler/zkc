//! Public role actions, exact message coordinates and execution budgets.
use super::{ArtifactFormat, PhysicalType, backend::BackendError, model::*};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    Entry,
    Role,
    Session,
    Inputs,
    WrongAction,
    WrongCut,
    Envelope,
    Payload,
    Limit,
    Backend(BackendError),
    ExplicitStop(String),
    Admission(AdmissionError),
}
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for RuntimeError {}
impl From<BackendError> for RuntimeError {
    fn from(e: BackendError) -> Self {
        Self::Backend(e)
    }
}

/// Loading errors return backend custody, including any admission-side state.
#[derive(Debug)]
pub struct LoadError<B> {
    pub error: RuntimeError,
    pub backend: B,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathElement {
    Match { site: String, alternative: String },
    Conditional { site: String, taken: bool },
    For { site: String, index: u64 },
    Call { site: String, instance: String },
    Loop { site: String, iteration: u64 },
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Origin {
    pub format: ArtifactFormat,
    /// Host-agreed unique execution ID. Reusing it defeats cross-session replay separation.
    pub session: String,
    pub entry: String,
    pub instance: String,
    /// Ordered nesting, preserving interleaving of calls and loop iterations.
    pub path: Vec<PathElement>,
}
impl Origin {
    /// Canonical structured origin, also used by `domain_bytes`. Exposing it
    /// preserves complete call/iteration identity in host diagnostic records.
    pub fn json(&self) -> serde_json::Value {
        serde_json::json!([
            "zkc.origin/2",
            self.session,
            self.entry,
            self.instance,
            self.path
                .iter()
                .map(|p| match p {
                    PathElement::Match { site, alternative } =>
                        serde_json::json!(["match", site, alternative]),
                    PathElement::Conditional { site, taken } =>
                        serde_json::json!(["if", site, if *taken { "then" } else { "else" }]),
                    PathElement::For { site, index } =>
                        serde_json::json!(["for", site, index.to_string()]),
                    PathElement::Call { site, instance } =>
                        serde_json::json!(["call", site, instance]),
                    PathElement::Loop { site, iteration } =>
                        serde_json::json!(["loop", site, iteration.to_string()]),
                })
                .collect::<Vec<_>>()
        ])
    }
    pub fn domain_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(&self.json()).expect("array/string serialization")
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CutKind {
    Local,
    Send,
    Receive,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cut {
    pub origin: Origin,
    pub role: String,
    pub site: String,
    pub kind: CutKind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Envelope {
    pub origin: Origin,
    pub site: String,
    pub schema: String,
    pub sender: String,
    pub receiver: String,
}
impl Envelope {
    pub fn domain_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!([
            "zkc.message-domain/2",
            self.origin.json(),
            self.site,
            self.schema,
            self.sender,
            self.receiver
        ]))
        .expect("array/string serialization")
    }
    pub(super) fn cut(&self, kind: CutKind) -> Cut {
        Cut {
            origin: self.origin.clone(),
            role: if kind == CutKind::Send {
                self.sender.clone()
            } else {
                self.receiver.clone()
            },
            site: self.site.clone(),
            kind,
        }
    }
}
/// Untrusted construction is intentional: `deliver` checks every field and value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Packet<V> {
    pub envelope: Envelope,
    pub ty: PhysicalType,
    pub payload: V,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receive {
    pub envelope: Envelope,
    pub ty: PhysicalType,
}
impl Receive {
    pub fn cut(&self) -> Cut {
        self.envelope.cut(CutKind::Receive)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAction {
    pub cut: Cut,
    pub function: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StopKind {
    Incomplete,
    Explicit(String),
    Backend(BackendError),
    Limit,
    Cancelled,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stop {
    pub origin: Origin,
    pub role: String,
    pub site: Option<String>,
    pub kind: StopKind,
    /// Cleanup errors are local; completed resource transitions remain installed.
    pub cleanup_errors: Vec<BackendError>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action<V> {
    Local(LocalAction),
    Send(Packet<V>),
    Receive(Receive),
    Returned(Vec<V>),
    Stopped(Stop),
}
impl<V> Action<V> {
    pub fn cut(&self) -> Option<Cut> {
        match self {
            Self::Local(local) => Some(local.cut.clone()),
            Self::Send(packet) => Some(packet.envelope.cut(CutKind::Send)),
            Self::Receive(request) => Some(request.cut()),
            Self::Returned(_) | Self::Stopped(_) => None,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    pub instructions: u64,
    pub calls: u64,
    pub iterations: u64,
    pub live_values: usize,
    pub live_value_bytes: usize,
    pub total_value_bytes: usize,
}

/// Host policy for conservative retained-payload accounting. These charges
/// count every binding, including aliases; they are not allocator/RSS metrics.
/// Individual values, native kernels, wire decoding and structural execution
/// retain their independent hard limits. A protocol cannot change this policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueBudget {
    pub live_bytes: usize,
    pub total_bytes: usize,
}
impl Default for ValueBudget {
    fn default() -> Self {
        Self {
            live_bytes: Limits::VALUE_BYTES,
            total_bytes: Limits::TOTAL_VALUE_BYTES,
        }
    }
}
