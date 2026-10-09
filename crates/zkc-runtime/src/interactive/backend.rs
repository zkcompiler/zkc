use super::model::LogicalOrigin;
use super::{BoundSignature, OperationBinding, Origin, PhysicalType, ResolvedBinding};
use std::{fmt, sync::Arc};

/// Trusted adapter value, preferably an enum of typed immutable/Arc-backed values.
/// Cloning a capability copies its handle, never its issuance authority or state.
/// Implementations must have stable type/size and cheap, nonpanicking clones.
/// Locally discardable values, including immutable private custody, must have
/// inert, nonpanicking destruction:
/// dropping storage cannot affect backend state or semantic observations.
/// Untrusted ingress must not select its own implementation of this trait.
pub trait Value: Clone {
    /// Pack only the selected payload. Clones copy handles, never authority.
    fn pack_variant(
        _descriptor: Arc<super::VariantDescriptor>,
        _alternative: usize,
        _payload: Vec<Self>,
    ) -> Result<Self, BackendError> {
        Err(BackendError::new("variant-unsupported"))
    }
    /// Trusted checked decomposition; active payload only, in declaration order.
    fn unpack_variant(
        &self,
    ) -> Result<(Arc<super::VariantDescriptor>, usize, Vec<Self>), BackendError> {
        Err(BackendError::new("variant-unsupported"))
    }
    /// Trusted scalar access for backend-independent local control.
    fn control_bool(&self) -> Result<bool, BackendError> {
        Err(BackendError::new("local-control-bool"))
    }
    /// Pure, stable inspection of a logical natural; repeated reads have no effects.
    fn control_index(&self) -> Result<u64, BackendError> {
        Err(BackendError::new("local-control-index"))
    }
    /// Construct the native Boolean literal; the runner checks its full type
    /// and charges the ordinary instruction and retained-value budgets.
    fn from_control_bool(_value: bool) -> Result<Self, BackendError> {
        Err(BackendError::new("native-boolean-unsupported"))
    }
    /// Construct a native index. The runner validates its declared index type
    /// before binding an induction variable or entering its body.
    fn from_control_index(_index: u64) -> Result<Self, BackendError> {
        Err(BackendError::new("local-control-index"))
    }
    /// Intrinsic full type, derived from the admitted payload representation.
    fn physical_type(&self) -> PhysicalType;
    /// Validate the complete public representation, including nested contents.
    /// A private key/capability disguised as a public value must fail here.
    fn validate_serializable(&self) -> Result<(), BackendError>;
    /// Conservative retained payload bytes; count shared backing in full.
    fn retained_bytes(&self) -> usize;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackendError {
    pub code: String,
}
impl BackendError {
    /// Codes are local observations. They are never implicitly sent to a peer.
    pub fn new(code: impl Into<String>) -> Self {
        Self { code: code.into() }
    }
}
impl fmt::Display for BackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for BackendError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FrameId(pub(crate) u64);
impl FrameId {
    pub fn get(self) -> u64 {
        self.0
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrameKind {
    Entry,
    Loop { site: String, iteration: u64 },
    Local { site: String, function: String },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameExit {
    Returned,
    Stopped,
    Cancelled,
}

/// Runtime-minted boundary. Only the actual argument view crosses into a child.
#[derive(Clone, Debug)]
pub struct Frame {
    pub(crate) id: FrameId,
    pub(crate) parent: Option<FrameId>,
    pub(crate) role: String,
    pub(crate) origin: Origin,
    pub(crate) kind: FrameKind,
    pub(crate) inputs: Vec<(String, PhysicalType)>,
    pub(crate) services: Vec<super::ServicePort>,
}
impl Frame {
    /// Entry declarations, inherited read-only by structured loop frames.
    /// Their input_index refers to the entry interface, never child inputs.
    /// Only Entry may acquire leases; a loop borrows its active entry authority.
    pub fn services(&self) -> &[super::ServicePort] {
        &self.services
    }
    pub fn id(&self) -> FrameId {
        self.id
    }
    pub fn parent(&self) -> Option<FrameId> {
        self.parent
    }
    pub fn role(&self) -> &str {
        &self.role
    }
    pub fn origin(&self) -> &Origin {
        &self.origin
    }
    pub fn kind(&self) -> &FrameKind {
        &self.kind
    }
    pub fn inputs(&self) -> &[(String, PhysicalType)] {
        &self.inputs
    }
}

/// One allowlisted mathematical operation, never a whole-protocol callback.
pub struct Invocation<'a> {
    pub frame: &'a Frame,
    pub site: &'a str,
    pub kernel: &'a str,
    pub binding: &'a ResolvedBinding,
    pub logical_origin: &'a LogicalOrigin,
    pub attributes: &'a [String],
    /// Backend must check allocation/shape bounds before allocating its result.
    /// This is an output payload ceiling, not a reservation of external PCS scratch.
    pub max_output_bytes: usize,
}
impl Invocation<'_> {
    /// Unambiguous bytes for local service domain separation. No hash or crypto.
    pub fn domain_bytes(&self) -> Vec<u8> {
        let binding = self.binding.declaration();
        serde_json::to_vec(&serde_json::json!([
            "zkc.local-domain",
            self.frame.origin.json(),
            self.frame.role,
            match &self.frame.kind {
                FrameKind::Local { site, .. } => Some(site),
                _ => None,
            },
            [
                self.logical_origin.definition,
                serde_json::json!(self.logical_origin.arguments)
            ],
            self.site,
            [binding.contract, serde_json::json!(binding.arguments)],
            self.attributes
        ]))
        .expect("string/array domain serialization cannot fail")
    }
}

/// One synchronous service transition at an exposed participant cut.
pub struct ServiceInvocation<'a> {
    pub frame: &'a Frame,
    pub site: &'a str,
    pub port: &'a super::ServicePort,
    pub method: &'a str,
    pub max_output_bytes: usize,
}

/// Installed, trusted implementation. Artifact text never supplies these methods.
///
/// `enter_frame` atomically validates issuance, current generations, actual aliases,
/// ownership/instance binding and the parent's permitted view. On error it must
/// leave no active child frame. `leave_frame` refuses out-of-order exits without
/// changing any views. It always removes the top frame, including on output
/// validation error, and preserves all completed resource transitions. Both hooks must
/// preserve resources outside the actual argument view. A Returned exit may
/// transfer the entry result tuple through an enclosing loop frame. It does not
/// imply that the loop body reached its yield or completed its iteration. A kernel may access only
/// resources authorized by its explicit operands AND the active frame, even if
/// the backend's authoritative store contains other handles.
///
/// Every consume advances authoritative state before a possible failure. Returning
/// `Err` does not roll back state. Outputs cannot issue capabilities on the caller's
/// assertion alone. Entry hooks also validate public parameters, shapes, key/setup
/// identities and the host's admitted input policy for this exact role/entry.
pub trait Backend {
    type Value: Value;
    /// Read-only installation fact. True promises both Boolean constructors
    /// return native.bool/1 values. Runtime validation still checks each value.
    /// Admission checks this before any frame, message or backend transition.
    fn supports_boolean_literals(&self) -> bool {
        false
    }
    /// Independently installed method shape and aggregate retained reply bound.
    /// Author these from the implementation's actual supported values; echoing
    /// ServiceContract::signature does not provide independent installation facts.
    /// Keep them stable throughout admission and execution. Runtime checks both
    /// the declaration and actual replies; service-root authority is separate.
    /// The default refuses native service admission.
    fn service_support(
        &self,
        _contract: super::ServiceContract,
        _method: &str,
    ) -> Option<super::ServiceSupport> {
        None
    }
    fn query(
        &mut self,
        _invocation: &ServiceInvocation<'_>,
        _arguments: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError> {
        Err(BackendError::new("service-unsupported"))
    }
    /// Poison an already consumed service after reply validation/binding fails.
    /// Implementations supporting queries must override this hook.
    fn reject_service_reply(&mut self, _invocation: &ServiceInvocation<'_>) {}

    /// Independently installed full signature. Unsupported bindings fail closed.
    fn binding_signature(&self, _binding: &OperationBinding) -> Option<BoundSignature> {
        None
    }
    /// Canonical representation, variant/type consistency and per-value bounds.
    /// This is read-only and must not consume randomness/capabilities.
    fn validate_value(&self, value: &Self::Value) -> Result<(), BackendError>;
    fn enter_frame(&mut self, frame: &Frame, arguments: &[Self::Value])
    -> Result<(), BackendError>;
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Self::Value],
    ) -> Result<(), BackendError>;
    fn apply(
        &mut self,
        invocation: &Invocation<'_>,
        arguments: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError>;
}

#[cfg(test)]
mod domain_tests {
    use super::*;
    use crate::interactive::{LogicalOrigin, OperationBinding};

    fn frame(function: &str) -> Frame {
        Frame {
            id: FrameId(3),
            parent: Some(FrameId(1)),
            role: "P".into(),
            origin: Origin {
                session: "s".into(),
                entry: "main".into(),
                instance: "root".into(),
                path: vec![],
            },
            kind: FrameKind::Local {
                site: "round".into(),
                function: function.into(),
            },
            inputs: vec![],
            services: vec![],
        }
    }

    #[test]
    fn explicit_domains_preserve_semantic_origins_across_physical_selection() {
        let origin = LogicalOrigin {
            definition: "Fold".into(),
            arguments: vec![("F".into(), "bls12-381.fr".into())],
        };
        let binding = |implementation: &str| {
            ResolvedBinding::explicit(OperationBinding {
                contract: "poly.fold".into(),
                arguments: vec!["bls12-381.fr".into()],
                implementation: implementation.into(),
            })
            .unwrap()
        };
        let lsb = binding("arkworks/poly.fold");
        let msb = binding("arkworks-msb/poly.fold");
        let a = frame("generated_lsb");
        let mut b = frame("generated_msb");
        let domain =
            |frame: &Frame, binding: &ResolvedBinding, origin: &LogicalOrigin, site: &str| {
                Invocation {
                    frame,
                    site,
                    kernel: binding.implementation(),
                    binding,
                    logical_origin: origin,
                    attributes: &[],
                    max_output_bytes: 4096,
                }
                .domain_bytes()
            };
        let expected = domain(&a, &lsb, &origin, "fold");
        assert_eq!(expected, domain(&b, &msb, &origin, "fold"));
        assert_ne!(expected, domain(&b, &msb, &origin, "another"));
        let mut other = origin.clone();
        other.definition = "DifferentAlgorithm".into();
        assert_ne!(expected, domain(&b, &msb, &other, "fold"));
        b.origin.session = "other-session".into();
        assert_ne!(expected, domain(&b, &msb, &origin, "fold"));
    }

    #[test]
    fn explicit_local_domain_bytes_bind_semantic_operation_and_origin() {
        let binding = ResolvedBinding::explicit(OperationBinding {
            contract: "field.add".into(),
            arguments: vec!["bls12-381.fr".into()],
            implementation: "arkworks/field.add".into(),
        })
        .unwrap();
        let origin = LogicalOrigin {
            definition: "Add".into(),
            arguments: vec![("F".into(), "bls12-381.fr".into())],
        };
        let frame = frame("add");
        let bytes = Invocation {
            frame: &frame,
            site: "op",
            kernel: "arkworks/field.add",
            binding: &binding,
            logical_origin: &origin,
            attributes: &[],
            max_output_bytes: 1,
        }
        .domain_bytes();
        let expected = br#"["zkc.local-domain",["zkc.origin","s","main","root",[]],"P","round",["Add",[["F","bls12-381.fr"]]],"op",["field.add",["bls12-381.fr"]],[]]"#;
        assert_eq!(bytes, expected);
    }
}
