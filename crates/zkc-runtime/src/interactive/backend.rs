use super::model::LogicalOrigin;
use super::{
    Backing, BoundSignature, OperationBinding, Origin, PhysicalType, ResolvedBinding, Retained,
};
use std::{fmt, sync::Arc};

/// Trusted adapter value, preferably an enum of typed immutable/Arc-backed values.
/// Cloning a capability copies its handle, never its issuance authority or state.
/// Implementations must have stable type/size and cheap, nonpanicking clones.
/// Locally discardable values, including immutable private custody, must have
/// inert, nonpanicking destruction:
/// dropping storage cannot affect backend state or semantic observations.
/// Untrusted ingress must not select its own implementation of this trait.
pub trait Value: Clone {
    /// Canonical key for a small inline parameter, independent of allocation,
    /// frame and session. Returning Some promises no retained backing or hidden
    /// authority. Only the Runner's public provenance permits using this key.
    fn preparation_parameter(&self) -> Option<Vec<u8>> {
        None
    }

    /// Self-contained immutable data whose clones may outlive this runner and
    /// be shared by other backend instances. No arena/session references,
    /// authority, interior mutation or reference-count-dependent accounting.
    /// The backend separately certifies the computation and policy context.
    fn preparation_output(&self) -> bool {
        false
    }

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
    /// Exact equality with `physical_type()`, without requiring a new descriptor.
    /// Implementations may inspect native payloads or borrow stored descriptors.
    /// This stable classification never establishes current resource authority,
    /// payload validity, normalization, or policy acceptance.
    fn has_type(&self, expected: &PhysicalType) -> bool {
        self.physical_type() == *expected
    }
    /// Validate the complete public representation, including nested contents.
    /// A private key/capability disguised as a public value must fail here.
    fn validate_serializable(&self) -> Result<(), BackendError>;
    /// Conservative retained payload bytes; count shared backing in full.
    /// This full charge bounds one value and measures logical operand work.
    fn retained_bytes(&self) -> usize;
    /// Partition `retained_bytes` into storage owned by this binding alone
    /// (returned) and immutable allocations it shares, reported to `shared`
    /// with [`Backing::of`]. When `shared` returns true, also report the
    /// allocations that allocation itself retains, recursively; inline storage
    /// inside a shared allocation belongs to that allocation's charge. With all
    /// allocations distinct, the reported bytes sum to `retained_bytes`.
    /// The default reports no sharing, so every binding is charged in full.
    fn retained_parts(&self, _shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        self.retained_bytes()
    }
    /// An allocation whose immutable contents, together with the physical type,
    /// alone determine backend validation of this value. Return it only for
    /// values carrying no capability or other changeable authority. The Runner
    /// then reuses one successful validation for aliases bound at the same time.
    fn validation_backing(&self) -> Option<Backing> {
        None
    }
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

/// Immutable ordered input layout. Alternative regions share their capture
/// suffix, so retained metadata grows with source ports rather than arms times
/// captures. Iteration and equality expose the same flat port order to backends.
#[derive(Clone, Debug, Default)]
pub struct FrameInputs {
    explicit: Arc<[(String, PhysicalType)]>,
    captures: Arc<[(String, PhysicalType)]>,
}
impl FrameInputs {
    pub(crate) fn with_captures(
        explicit: Vec<(String, PhysicalType)>,
        captures: Arc<[(String, PhysicalType)]>,
    ) -> Self {
        Self {
            explicit: explicit.into(),
            captures,
        }
    }
    pub fn len(&self) -> usize {
        self.explicit.len() + self.captures.len()
    }
    pub fn is_empty(&self) -> bool {
        self.explicit.is_empty() && self.captures.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &(String, PhysicalType)> + Clone {
        self.explicit.iter().chain(self.captures.iter())
    }
}
impl From<Vec<(String, PhysicalType)>> for FrameInputs {
    fn from(explicit: Vec<(String, PhysicalType)>) -> Self {
        Self {
            explicit: explicit.into(),
            captures: Arc::from([]),
        }
    }
}
impl PartialEq for FrameInputs {
    fn eq(&self, other: &Self) -> bool {
        (Arc::ptr_eq(&self.explicit, &other.explicit)
            && Arc::ptr_eq(&self.captures, &other.captures))
            || self.iter().eq(other.iter())
    }
}
impl Eq for FrameInputs {}

/// Runtime-minted boundary. Only the actual argument view crosses into a child.
#[derive(Clone)]
pub struct Frame(Arc<FrameData>);

/// Constructed completely before publishing an immutable runtime boundary.
pub(crate) struct FrameData {
    pub(crate) id: FrameId,
    pub(crate) parent: Option<FrameId>,
    pub(crate) role: String,
    pub(crate) origin: Origin,
    pub(crate) kind: Arc<FrameKind>,
    pub(crate) inputs: FrameInputs,
    pub(crate) services: Vec<super::ServicePort>,
}
impl From<FrameData> for Frame {
    fn from(data: FrameData) -> Self {
        Self(Arc::new(data))
    }
}
impl std::fmt::Debug for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let FrameData {
            id,
            parent,
            role,
            origin,
            kind,
            inputs,
            services,
        } = self.0.as_ref();
        f.debug_struct("Frame")
            .field("id", id)
            .field("parent", parent)
            .field("role", role)
            .field("origin", origin)
            .field("kind", kind)
            .field("inputs", inputs)
            .field("services", services)
            .finish()
    }
}
impl Frame {
    /// Compare the boundary used for active-frame custody. Sharing immutable
    /// metadata proves equality; independently allocated equal frames still
    /// match. This compares id, parent, role, origin, kind and flat inputs.
    /// It does not authorize entry or service use: service declarations are
    /// excluded here and require their separate entry authority checks.
    #[inline]
    pub fn same_boundary(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        // Exhaustive destructuring requires an explicit custody decision when
        // adding metadata. Service authority is not part of this predicate.
        let FrameData {
            id,
            parent,
            role,
            origin,
            kind,
            inputs,
            services: _,
        } = self.0.as_ref();
        *id == other.id()
            && *parent == other.parent()
            && role.as_str() == other.role()
            && origin == other.origin()
            && kind.as_ref() == other.kind()
            && inputs == other.inputs()
    }

    /// Entry declarations, inherited read-only by structured loop frames.
    /// Their input_index refers to the entry interface, never child inputs.
    /// Only Entry may acquire leases; a loop borrows its active entry authority.
    pub fn services(&self) -> &[super::ServicePort] {
        &self.0.services
    }
    pub fn id(&self) -> FrameId {
        self.0.id
    }
    pub fn parent(&self) -> Option<FrameId> {
        self.0.parent
    }
    pub fn role(&self) -> &str {
        &self.0.role
    }
    pub fn origin(&self) -> &Origin {
        &self.0.origin
    }
    pub fn kind(&self) -> &FrameKind {
        &self.0.kind
    }
    pub fn inputs(&self) -> &FrameInputs {
        &self.0.inputs
    }
    pub(crate) fn shared_kind(&self) -> Arc<FrameKind> {
        self.0.kind.clone()
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
    /// This bounds newly allocated result storage; storage a result shares with
    /// its operands is already retained. It is not a reservation of external
    /// PCS scratch. The Runner still checks the full charge of each result.
    pub max_output_bytes: usize,
    /// Evidence about still-live immutable allocations, bound to this backend's
    /// Runner. Replacing an operand never gives the replacement this evidence.
    pub retained: Retained<'a>,
}
impl Invocation<'_> {
    /// Unambiguous bytes for local service domain separation. No hash or crypto.
    pub fn domain_bytes(&self) -> Vec<u8> {
        let binding = self.binding.declaration();
        serde_json::to_vec(&serde_json::json!([
            "zkc.local-domain/0",
            self.frame.origin().json(),
            self.frame.role(),
            match self.frame.kind() {
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

/// Independent installation evidence for one exact operation binding.
/// The Runner prepares handles again on the backend it takes into custody;
/// admission does not transfer handles from another backend. A handle carries
/// no input, frame, resource or setup authority.
pub trait InstalledKernel {
    fn signature(&self) -> &BoundSignature;
    /// Read-only installation fact, stable for the Runner's lifetime.
    /// Fixed inputs, attributes and backend policy determine this operation's
    /// outputs or refusal. It cannot observe frame identity, resources, time,
    /// entropy or mutable dependencies. Values, refusal and logical charges must
    /// not depend on cache warmth or reference counts. The backend checkpoint contract must
    /// account for all work counters. This is not a promise of totality.
    fn deterministic(&self) -> bool {
        false
    }
}
impl InstalledKernel for BoundSignature {
    fn signature(&self) -> &BoundSignature {
        self
    }
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
    type Kernel: InstalledKernel;
    /// Private backend data for one reached call site. Use `()` when no static
    /// invocation work needs preparation. It carries no resource authority.
    type Call;
    /// Fixed-size immutable evidence for replaying deterministic computation
    /// work. It owns no heap allocation, capabilities or mutable dependencies.
    type Checkpoint: Copy;
    fn computation_checkpoint(&self) -> Option<Self::Checkpoint> {
        None
    }
    /// Atomically replay only cumulative work, when the current policy and
    /// remaining backend capacities dominate the recorded initial state.
    /// False changes nothing. Pure local frame enter/leave remain mandatory;
    /// nested pure frames have no effects beyond validation under this policy.
    fn replay_computation(&mut self, _before: Self::Checkpoint, _after: Self::Checkpoint) -> bool {
        false
    }
    /// Read-only installation fact. True promises both Boolean constructors
    /// return native.bool/0 values. Runtime validation still checks each value.
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

    /// Resolve code and its independently installed signature for this exact
    /// contract, static arguments and implementation. Unsupported bindings refuse.
    /// This read-only operation must not draw randomness or consume resources.
    /// Code selection and signature stay valid for this backend's Runner lifetime;
    /// invocation-dependent policy, setup and resource checks remain in `apply`.
    /// The Runner calls this once per distinct binding before entering any frame.
    fn prepare_binding(&self, _binding: &OperationBinding) -> Option<Self::Kernel> {
        None
    }
    /// Inspect an installed signature without retaining a prepared handle.
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        self.prepare_binding(binding)
            .map(|kernel| kernel.signature().clone())
    }
    /// Canonical representation, variant/type consistency and per-value bounds.
    /// This is read-only and must not consume randomness/capabilities.
    fn validate_value(&self, value: &Self::Value) -> Result<(), BackendError>;
    /// Validate a value while reusing admitted immutable subtrees. The default
    /// performs the complete check. Capabilities always require fresh checks.
    fn validate_value_retained(
        &self,
        value: &Self::Value,
        _retained: Retained<'_>,
    ) -> Result<(), BackendError> {
        self.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, arguments: &[Self::Value])
    -> Result<(), BackendError>;
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Self::Value],
    ) -> Result<(), BackendError>;
    /// Enter with the same custody checks as `enter_frame`, optionally reusing
    /// validation of immutable argument subtrees retained by this Runner.
    fn enter_frame_retained(
        &mut self,
        frame: &Frame,
        arguments: &[Self::Value],
        _retained: Retained<'_>,
    ) -> Result<(), BackendError> {
        self.enter_frame(frame, arguments)
    }
    /// Leave with the same cleanup as `leave_frame`. A retained view can only
    /// discharge immutable value validation, never resource cleanup.
    fn leave_frame_retained(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Self::Value],
        _retained: Retained<'_>,
    ) -> Result<(), BackendError> {
        self.leave_frame(frame, exit, outputs)
    }
    /// Upper bound on operand bytes read by this installed kernel body,
    /// for kernels that access only part of their operands, such as one opening
    /// of a committed table. The Runner charges it as logical work before
    /// `apply`. `None` charges the full retained bytes of every operand.
    /// A backend that additionally walks nested operands for admission must
    /// bound those walks separately.
    fn operand_work(
        &self,
        _kernel: &Self::Kernel,
        _invocation: &Invocation<'_>,
        _arguments: &[Self::Value],
    ) -> Option<u64> {
        None
    }
    /// Execute with storage for this Runner's call-site preparation. Prepare only
    /// at the original validation point inside execution: unused branches must
    /// not fail early. The default needs no preparation and uses the same checked
    /// path as direct calls. Implementations must check any reused facts against
    /// the current binding/attributes and keep dynamic checks at every use.
    fn apply_prepared(
        &mut self,
        kernel: &Self::Kernel,
        _call: &mut Option<Self::Call>,
        invocation: &Invocation<'_>,
        arguments: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError> {
        self.apply(kernel, invocation, arguments)
    }
    /// Execute with a handle prepared for the invocation's exact binding. Check
    /// dynamic operands, attributes, policy, work and resource custody at use.
    /// Backends with public direct-call support must refuse a mismatched handle.
    fn apply(
        &mut self,
        kernel: &Self::Kernel,
        invocation: &Invocation<'_>,
        arguments: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError>;
}

#[cfg(test)]
mod domain_tests {
    use super::*;
    use crate::interactive::{
        LogicalOrigin, OperationBinding, PathElement, ServiceContract, ServicePort,
    };

    #[test]
    fn frame_inputs_share_capture_storage_and_compare_flat_order() {
        let ty = PhysicalType::parse("index@native.index/0").unwrap();
        let captures: Arc<[_]> = vec![("captured".into(), ty.clone())].into();
        let first = FrameInputs::with_captures(vec![("a".into(), ty.clone())], captures.clone());
        let second = FrameInputs::with_captures(vec![("b".into(), ty.clone())], captures);
        assert!(std::ptr::eq(
            first.iter().nth(1).unwrap(),
            second.iter().nth(1).unwrap()
        ));
        let flat: FrameInputs = vec![("a".into(), ty.clone()), ("captured".into(), ty)].into();
        assert_eq!(first, flat);
        assert_ne!(first, second);
        assert_eq!(first.len(), 2);
        assert!(!first.is_empty());
    }

    fn frame_data(function: &str) -> FrameData {
        FrameData {
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
            }
            .into(),
            inputs: vec![].into(),
            services: vec![],
        }
    }

    fn frame(function: &str) -> Frame {
        frame_data(function).into()
    }

    #[test]
    fn frame_sharing_preserves_boundary_equality() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<Frame>();
        // The former backend predicate is the value-based oracle, independent
        // of the new fast path and of where metadata is allocated.
        let old = |a: &Frame, b: &Frame| {
            a.id() == b.id()
                && a.parent() == b.parent()
                && a.role() == b.role()
                && a.origin() == b.origin()
                && a.kind() == b.kind()
                && a.inputs() == b.inputs()
        };
        let first = frame("local");
        let clone = first.clone();
        assert!(Arc::ptr_eq(&first.0, &clone.0));
        let equal = frame("local");
        assert!(!Arc::ptr_eq(&first.0, &equal.0));
        assert!(first.same_boundary(&clone));
        assert!(first.same_boundary(&equal));
        assert_eq!(
            format!("{first:?}"),
            concat!(
                "Frame { id: FrameId(3), parent: Some(FrameId(1)), role: \"P\", ",
                "origin: Origin { session: \"s\", entry: \"main\", instance: \"root\", path: [] }, ",
                "kind: Local { site: \"round\", function: \"local\" }, ",
                "inputs: FrameInputs { explicit: [], captures: [] }, services: [] }"
            )
        );

        let mutations: &[fn(&mut FrameData)] = &[
            |v| v.id = FrameId(4),
            |v| v.parent = None,
            |v| v.parent = Some(FrameId(2)),
            |v| v.role = "V".into(),
            |v| v.origin.session = "other".into(),
            |v| v.origin.entry = "other".into(),
            |v| v.origin.instance = "other".into(),
            |v| v.kind = FrameKind::Entry.into(),
            |v| {
                v.kind = FrameKind::Loop {
                    site: "loop".into(),
                    iteration: 2,
                }
                .into()
            },
            |v| {
                v.kind = FrameKind::Local {
                    site: "other".into(),
                    function: "local".into(),
                }
                .into()
            },
            |v| {
                v.kind = FrameKind::Local {
                    site: "round".into(),
                    function: "other".into(),
                }
                .into()
            },
            |v| {
                v.origin.path.push(PathElement::Match {
                    site: "m".into(),
                    alternative: "a".into(),
                })
            },
            |v| {
                v.origin.path.push(PathElement::Conditional {
                    site: "c".into(),
                    taken: true,
                })
            },
            |v| {
                v.origin.path.push(PathElement::For {
                    site: "f".into(),
                    index: 7,
                })
            },
            |v| {
                v.origin.path.push(PathElement::Loop {
                    site: "l".into(),
                    iteration: 3,
                })
            },
            |v| {
                v.inputs = vec![(
                    "x".into(),
                    PhysicalType::parse("index@native.index/0").unwrap(),
                )]
                .into()
            },
        ];
        let mut frames = vec![first, clone, equal];
        for change in mutations {
            let mut data = frame_data("local");
            change(&mut data);
            let changed: Frame = data.into();
            assert!(!frames[0].same_boundary(&changed));
            frames.push(changed);
        }
        for iteration in [2, 3] {
            let mut data = frame_data("local");
            data.kind = FrameKind::Loop {
                site: "loop".into(),
                iteration,
            }
            .into();
            frames.push(data.into());
        }
        let index = PhysicalType::parse("index@native.index/0").unwrap();
        let boolean = PhysicalType::parse("bool@native.bool/0").unwrap();
        for inputs in [
            vec![("x".into(), index.clone())],
            vec![("y".into(), index.clone())],
            vec![("x".into(), boolean.clone())],
            vec![("x".into(), index.clone()), ("y".into(), boolean.clone())],
            vec![("y".into(), boolean), ("x".into(), index)],
        ] {
            let mut data = frame_data("local");
            data.inputs = inputs.into();
            frames.push(data.into());
        }
        for a in &frames {
            for b in &frames {
                assert_eq!(a.same_boundary(b), old(a, b));
            }
        }
    }

    #[test]
    fn frame_boundary_uses_flat_inputs_and_excludes_services() {
        let ty = PhysicalType::parse("index@native.index/0").unwrap();
        let inputs = vec![("x".into(), ty.clone()), ("capture".into(), ty)];
        let mut a = frame_data("local");
        a.inputs = inputs.clone().into();
        let a: Frame = a.into();
        let mut b = frame_data("local");
        b.inputs = FrameInputs::with_captures(inputs[..1].to_vec(), inputs[1..].into());
        b.services.push(ServicePort {
            name: "random".into(),
            contract: ServiceContract::RandomBls12381Field,
            input_index: 0,
        });
        let b: Frame = b.into();
        assert_ne!(a.services(), b.services());
        assert!(a.same_boundary(&b));
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
        let b = frame("generated_msb");
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
                    retained: Retained::NONE,
                }
                .domain_bytes()
            };
        let expected = domain(&a, &lsb, &origin, "fold");
        assert_eq!(expected, domain(&b, &msb, &origin, "fold"));
        assert_ne!(expected, domain(&b, &msb, &origin, "another"));
        let mut other = origin.clone();
        other.definition = "DifferentAlgorithm".into();
        assert_ne!(expected, domain(&b, &msb, &other, "fold"));
        let mut data = frame_data("generated_msb");
        data.origin.session = "other-session".into();
        let b: Frame = data.into();
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
            retained: Retained::NONE,
        }
        .domain_bytes();
        let expected = br#"["zkc.local-domain/0",["zkc.origin/0","s","main","root",[]],"P","round",["Add",[["F","bls12-381.fr"]]],"op",["field.add",["bls12-381.fr"]],[]]"#;
        assert_eq!(bytes, expected);
    }
}
