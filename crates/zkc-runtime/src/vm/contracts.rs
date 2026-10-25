//! Trusted immutable admission inventory. Artifact declarations select contracts;
//! only the composition root can contribute representations and implementations.
use super::{
    AdmissionError, BoundSignature, ErrorCode, Limits, LogicalType, OperationBinding, PhysicalType,
    Representation, ResolvedBinding, Type, operations,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

type Result<T> = std::result::Result<T, AdmissionError>;

fn representation_name(name: &str) -> bool {
    name.len() <= 256
        && name
            .bytes()
            .next()
            .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-' | b'/'))
}

/// Process-local catalog identity, never an artifact or deployment digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CatalogId(u64);
impl CatalogId {
    fn fresh() -> Self {
        // This allocates identities only. It contains no installation inventory,
        // mutable policy or registration, and is never consulted during execution.
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(
            NEXT.try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
                .expect("admission catalog identity space exhausted"),
        )
    }
}

/// Process-local identity of an immutable catalog and authorization view.
/// Equality supports conservative computation reuse; it grants no permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthorizationId(u64);
impl AuthorizationId {
    fn fresh() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(
            NEXT.try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
                .expect("authorization identity space exhausted"),
        )
    }
}

/// Compact installation identity scoped to the immutable contributing catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImplementationId {
    catalog: CatalogId,
    slot: u32,
}

/// An admitted physical representation. Names are trusted static deployment
/// constants; the scoped slot, rather than the name alone, identifies a layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExtensionRepresentation {
    catalog: CatalogId,
    slot: u32,
    name: &'static str,
}
impl ExtensionRepresentation {
    pub fn name(self) -> &'static str {
        self.name
    }
}

/// A trusted implementation premise, not a timing property inferred by the VM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TimingRequirement {
    /// No operand timing guarantee has been supplied.
    Unspecified,
    /// The trusted implementation owner promises operand-independent timing.
    OperandIndependent,
    /// Execution may reveal operand-dependent timing.
    VariableTime,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ImplementationRequirements {
    pub timing: TimingRequirement,
    /// Zero-based input positions whose values may affect timing. Variable-time
    /// implementations enumerate these explicitly; unspecified timing has no evidence.
    pub timing_operands: &'static [usize],
}
impl Default for ImplementationRequirements {
    fn default() -> Self {
        Self {
            timing: TimingRequirement::Unspecified,
            timing_operands: &[],
        }
    }
}

impl ImplementationRequirements {
    fn validate(self, inputs: usize) -> Result<()> {
        if !self
            .timing_operands
            .windows(2)
            .all(|pair| pair[0] < pair[1])
            || self.timing_operands.iter().any(|&index| index >= inputs)
            || match self.timing {
                TimingRequirement::VariableTime => inputs != 0 && self.timing_operands.is_empty(),
                _ => !self.timing_operands.is_empty(),
            }
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "implementation-timing-operands",
            ));
        }
        Ok(())
    }
}

/// Exact external byte language, independent of the in-memory representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum WireCodec {
    /// The canonical expected-type ZKCV value frames.
    Native,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TimingGrant {
    declaration: OperationBinding,
    id: Option<ImplementationId>,
    requirements: ImplementationRequirements,
}

/// Explicit deployment authorization. Roles, determinism and provider names do
/// not grant either permission. This policy makes no whole-program timing claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecutionPolicy {
    pub allow_unspecified_timing: bool,
    pub allow_variable_time: bool,
}
impl ExecutionPolicy {
    pub const fn general_purpose() -> Self {
        Self {
            allow_unspecified_timing: true,
            allow_variable_time: true,
        }
    }
    pub const fn operand_independent() -> Self {
        Self {
            allow_unspecified_timing: false,
            allow_variable_time: false,
        }
    }
    pub fn permits(self, requirements: ImplementationRequirements) -> bool {
        match requirements.timing {
            TimingRequirement::Unspecified => self.allow_unspecified_timing,
            TimingRequirement::OperandIndependent => true,
            TimingRequirement::VariableTime => self.allow_variable_time,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct ExactImplementation {
    pub declaration: OperationBinding,
    pub signature: BoundSignature,
    pub id: ImplementationId,
    pub requirements: ImplementationRequirements,
}

/// Storage rule contributed by the owner of an aggregate representation.
#[derive(Clone, Debug)]
pub enum AggregateChildRule {
    AnyAdmitted,
    Repeated {
        element: PhysicalType,
        maximum_length: u64,
    },
}
#[derive(Clone, Debug)]
struct AggregateRepresentation {
    representation: ExtensionRepresentation,
    constructor: Type,
    children: AggregateChildRule,
    native_frame: bool,
}
impl AggregateRepresentation {
    fn accepts(&self, ty: &PhysicalType) -> bool {
        if ty.kind() != self.constructor
            || ty.representation() != Representation::Extension(self.representation)
        {
            return false;
        }
        match &self.children {
            AggregateChildRule::AnyAdmitted => {
                matches!(self.constructor, Type::Sequence | Type::Variant)
            }
            AggregateChildRule::Repeated {
                element,
                maximum_length,
            } => {
                let length = match ty.kind() {
                    Type::FieldArray => ty.logical().field_array_parts().map(|(_, n)| n),
                    Type::FixedVector => ty.logical().fixed_vector_parts().map(|(_, n)| n),
                    _ => None,
                };
                length.is_some_and(|n| n <= *maximum_length)
                    && ty.children() == Some(std::slice::from_ref(element))
            }
        }
    }
}

/// Construction-time contribution owner. Freeze before admitting programs or
/// constructing installed handlers. A clone of `Contracts` shares its identity;
/// rebuilding an otherwise identical catalog creates distinct extension IDs.
pub struct ContractsBuilder {
    catalog: CatalogId,
    registry: operations::Registry,
    standard: bool,
    aggregates: BTreeMap<&'static str, AggregateRepresentation>,
    representations: BTreeMap<&'static str, BTreeMap<LogicalType, PhysicalType>>,
    implementations: usize,
    wire_permissions: BTreeSet<(PhysicalType, WireCodec)>,
}
impl ContractsBuilder {
    /// VM control constructors remain fixed; no standard implementation is installed.
    pub fn empty() -> Self {
        Self::new(false)
    }
    /// Explicit contribution of the existing Native domains and implementations.
    pub fn standard() -> Self {
        Self::new(true)
    }
    fn new(standard: bool) -> Self {
        let registry = if standard {
            operations::standard_registry()
        } else {
            operations::Registry::logical_only()
        };
        Self {
            catalog: CatalogId::fresh(),
            registry,
            standard,
            representations: BTreeMap::new(),
            aggregates: BTreeMap::new(),
            implementations: 0,
            // Fixed VM controls retain their existing transport contract even
            // when no numerical provider inventory has been contributed.
            wire_permissions: ["bool@native.bool/0", "index@native.index/0"]
                .into_iter()
                .map(|name| {
                    (
                        PhysicalType::parse(name).expect("VM control type"),
                        WireCodec::Native,
                    )
                })
                .collect(),
        }
    }
    /// Contribute one flat mathematical layout. Aggregate layouts, control
    /// constructors, resources, setup objects and codecs require their own contracts.
    pub fn add_representation(
        &mut self,
        name: &'static str,
        logical: LogicalType,
    ) -> Result<PhysicalType> {
        if !representation_name(name) {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "representation-identity",
            ));
        }
        if Representation::parse(name).is_ok()
            || self.aggregates.contains_key(name)
            || self
                .representations
                .get(name)
                .is_some_and(|layouts| layouts.contains_key(&logical))
        {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "duplicate-representation-owner",
            ));
        }
        if !matches!(
            logical.kind(),
            Type::Field
                | Type::Vector
                | Type::Polynomial
                | Type::Round
                | Type::Matrix
                | Type::Table
                | Type::Point
                | Type::Group
                | Type::Groups
        ) {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "extension-layout-kind",
            ));
        }
        if self
            .representations
            .values()
            .map(BTreeMap::len)
            .sum::<usize>()
            + self.aggregates.len()
            >= Limits::DEFINITIONS
        {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "representation-count",
            ));
        }
        let representation = self
            .representations
            .get(name)
            .and_then(|layouts| layouts.values().next())
            .map(|ty| match ty.representation() {
                Representation::Extension(id) => id,
                _ => unreachable!(),
            })
            .unwrap_or(ExtensionRepresentation {
                catalog: self.catalog,
                slot: (self.representations.len() + self.aggregates.len()) as u32,
                name,
            });
        let ty = PhysicalType::extension(logical.clone(), representation);
        self.representations
            .entry(name)
            .or_default()
            .insert(logical, ty.clone());
        Ok(ty)
    }
    /// Install one bounded storage rule in this catalog's representation inventory.
    pub fn add_aggregate_representation(
        &mut self,
        name: &'static str,
        constructor: Type,
        children: AggregateChildRule,
    ) -> Result<Representation> {
        if !representation_name(name) {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "representation-identity",
            ));
        }
        if Representation::parse(name).is_ok()
            || self.representations.contains_key(name)
            || self.aggregates.contains_key(name)
        {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "duplicate-representation-owner",
            ));
        }
        if self
            .representations
            .values()
            .map(BTreeMap::len)
            .sum::<usize>()
            + self.aggregates.len()
            >= Limits::DEFINITIONS
        {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "representation-count",
            ));
        }
        match &children {
            AggregateChildRule::AnyAdmitted
                if matches!(constructor, Type::Sequence | Type::Variant) => {}
            AggregateChildRule::Repeated {
                element,
                maximum_length,
            } if matches!(constructor, Type::FieldArray | Type::FixedVector)
                && *maximum_length <= super::NATURAL_ARGUMENT_LIMIT =>
            {
                self.check_type(element)?;
            }
            _ => {
                return Err(AdmissionError::new(
                    ErrorCode::Representation,
                    "aggregate-storage-rule",
                ));
            }
        }
        let representation = ExtensionRepresentation {
            catalog: self.catalog,
            slot: (self.representations.len() + self.aggregates.len()) as u32,
            name,
        };
        self.aggregates.insert(
            name,
            AggregateRepresentation {
                representation,
                constructor,
                children,
                native_frame: false,
            },
        );
        Ok(Representation::Extension(representation))
    }
    pub fn aggregate_type(
        &self,
        logical: LogicalType,
        representation: Representation,
        children: Vec<PhysicalType>,
    ) -> Result<PhysicalType> {
        let ty = PhysicalType::aggregate(logical, representation, children)?;
        self.check_type(&ty)?;
        Ok(ty)
    }
    /// Install a finite signature family in the existing implementation registry.
    pub fn add_implementation_family(
        &mut self,
        contract: &'static str,
        implementation: &'static str,
        family: super::AggregateImplementationFamily,
        requirements: ImplementationRequirements,
    ) -> Result<ImplementationId> {
        if self.implementations >= Limits::DEFINITIONS {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "implementation-count",
            ));
        }
        if implementation.is_empty()
            || implementation.len() > Limits::STRING_BYTES
            || !implementation.is_ascii()
            || implementation
                .bytes()
                .any(|b| b.is_ascii_whitespace() || b.is_ascii_control())
        {
            return Err(AdmissionError::new(
                ErrorCode::Name,
                "implementation-identity",
            ));
        }
        if !family.supports(contract) {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "aggregate-specialization",
            ));
        }
        if let super::AggregateImplementationFamily::FieldArray {
            representation,
            scalar,
            vector,
        }
        | super::AggregateImplementationFamily::FixedVector {
            representation,
            scalar,
            vector,
        } = &family
        {
            self.check_type(scalar)?;
            self.check_type(vector)?;
            if scalar.kind() != Type::Field
                || vector.kind() != Type::Vector
                || scalar.logical().identity() != vector.logical().identity()
            {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "aggregate-family-ports",
                ));
            }
            let logical = if family.kind() == Type::FieldArray {
                LogicalType::field_array(scalar.logical().identity(), 0)?
            } else {
                LogicalType::fixed_vector(scalar.logical().clone(), 0)?
            };
            self.aggregate_type(logical, *representation, vec![scalar.clone()])?;
        }
        let inputs = match contract {
            "sequence.empty" => 0,
            "sequence.append" | "sequence.at" | "field_array.get" | "fixed_vector.dot" => 2,
            _ => 1,
        };
        requirements.validate(inputs)?;
        let id = ImplementationId {
            catalog: self.catalog,
            slot: self.implementations as u32,
        };
        self.registry.add_family(
            implementation.into(),
            contract.into(),
            family,
            id,
            requirements,
        )?;
        self.implementations += 1;
        Ok(id)
    }
    /// Install an exact realization of an existing mathematical operation. The
    /// independent logical owner checks erasure, attributes and static arguments.
    /// This cannot introduce new logical effects or resource authority. Each
    /// direct conversion law must be explicitly supplied by the trusted caller.
    pub fn add_implementation(
        &mut self,
        declaration: OperationBinding,
        signature: BoundSignature,
        requirements: ImplementationRequirements,
    ) -> Result<ImplementationId> {
        if self.implementations >= Limits::DEFINITIONS {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "implementation-count",
            ));
        }
        if declaration.implementation.is_empty()
            || declaration.implementation.len() > Limits::STRING_BYTES
            || declaration
                .implementation
                .bytes()
                .any(|b| b.is_ascii_whitespace() || b.is_ascii_control())
            || !declaration.implementation.is_ascii()
        {
            return Err(AdmissionError::new(
                ErrorCode::Name,
                "implementation-identity",
            ));
        }
        requirements.validate(signature.inputs.len())?;
        let logical = operations::declared_logical_signature(&declaration)?;
        let erasure = super::OperationSignature {
            inputs: signature
                .inputs
                .iter()
                .map(PhysicalType::logical)
                .cloned()
                .collect(),
            outputs: signature
                .outputs
                .iter()
                .map(PhysicalType::logical)
                .cloned()
                .collect(),
            attributes: signature.attributes,
        };
        if logical != erasure {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "implementation-logical-ports",
            ));
        }
        for ty in signature.inputs.iter().chain(&signature.outputs) {
            self.check_type(ty)?;
        }
        let physical = declaration
            .physical_arguments
            .iter()
            .map(|p| parse_type(self.standard, &self.representations, &self.aggregates, p))
            .collect::<Result<Vec<_>>>()?;
        if declaration.contract == "representation.convert" {
            if declaration.arguments.len() != 1
                || physical.len() != 2
                || signature.inputs != physical[..1]
                || signature.outputs != physical[1..]
                || physical[0] == physical[1]
            {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "conversion-physical-ports",
                ));
            }
        } else if let Some(expected) = super::aggregate_bindings::exact_signature(
            &declaration,
            &logical,
            &physical,
            &signature,
        ) {
            if expected? != signature {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "implementation-physical-ports",
                ));
            }
        } else if !physical.is_empty() {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "unexpected-physical-arguments",
            ));
        }
        let id = ImplementationId {
            catalog: self.catalog,
            slot: self.implementations as u32,
        };
        self.registry.add_exact(ExactImplementation {
            declaration,
            signature,
            id,
            requirements,
        })?;
        self.implementations += 1;
        Ok(id)
    }
    /// The aggregate storage owner contributes its existing Native frame.
    /// Child permissions remain independent and are checked for every layout.
    pub fn allow_aggregate_native_message(&mut self, representation: Representation) -> Result<()> {
        let Representation::Extension(id) = representation else {
            return Err(AdmissionError::new(
                ErrorCode::Representation,
                "aggregate-wire-storage",
            ));
        };
        let owner = self
            .aggregates
            .get_mut(id.name())
            .filter(|o| o.representation == id)
            .ok_or_else(|| {
                AdmissionError::new(ErrorCode::Representation, "aggregate-wire-storage")
            })?;
        if !matches!(
            owner.constructor,
            Type::Sequence | Type::Variant | Type::FieldArray
        ) {
            return Err(AdmissionError::new(
                ErrorCode::Type,
                "aggregate-wire-storage",
            ));
        }
        owner.native_frame = true;
        Ok(())
    }
    /// Authorize this exact layout and codec. Aggregate permissions also require
    /// every selected child; leaf grants require an independently installed frame.
    pub fn add_wire_permission(&mut self, ty: PhysicalType, codec: WireCodec) -> Result<()> {
        self.check_type(&ty)?;
        if !ty.logical().is_native_message_data() || ty.is_affine() {
            return Err(AdmissionError::new(ErrorCode::Type, "wire-permission-type"));
        }
        if self.wire_permissions.len() >= Limits::DEFINITIONS {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "wire-permission-count",
            ));
        }
        if !self.wire_permissions.insert((ty, codec)) {
            return Err(AdmissionError::new(
                ErrorCode::Type,
                "duplicate-wire-permission",
            ));
        }
        Ok(())
    }
    fn check_type(&self, ty: &PhysicalType) -> Result<()> {
        check_type(self.standard, &self.representations, &self.aggregates, ty)
    }
    pub fn finish(self, policy: ExecutionPolicy) -> Contracts {
        Contracts {
            authorization: AuthorizationId::fresh(),
            context: Arc::new(ContractContext {
                registry: self.registry,
                standard: self.standard,
                representations: self.representations,
                aggregates: self.aggregates,
                wire_permissions: self.wire_permissions,
            }),
            policy,
            timing_grants: Arc::new(Vec::new()),
        }
    }
}

struct ContractContext {
    wire_permissions: BTreeSet<(PhysicalType, WireCodec)>,
    registry: operations::Registry,
    standard: bool,
    aggregates: BTreeMap<&'static str, AggregateRepresentation>,
    representations: BTreeMap<&'static str, BTreeMap<LogicalType, PhysicalType>>,
}
/// Immutable trusted context retained by each admitted Program. There is no
/// registration at execution time and no backend is constructed by admission.
#[derive(Clone)]
pub struct Contracts {
    authorization: AuthorizationId,
    timing_grants: Arc<Vec<TimingGrant>>,
    context: Arc<ContractContext>,
    policy: ExecutionPolicy,
}
impl std::fmt::Debug for Contracts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Contracts")
            .field("standard", &self.context.standard)
            .field("representations", &self.context.representations)
            .field("policy", &self.policy)
            .finish_non_exhaustive()
    }
}
impl Contracts {
    pub fn standard(policy: ExecutionPolicy) -> Self {
        ContractsBuilder::standard().finish(policy)
    }
    /// Discover trusted implementation owners without claiming realization for
    /// any particular arguments, permission or actual backend installation.
    pub fn installed_implementations(&self) -> Vec<(String, &'static str)> {
        self.context.registry.installed_implementations()
    }
    /// Instantiate logical ports and check an optional trusted implementation
    /// constraint independently of physical parameter selection and timing policy.
    pub fn logical_signature(
        &self,
        declaration: &OperationBinding,
    ) -> Result<super::OperationSignature<LogicalType>> {
        self.context.registry.logical_selection(declaration)
    }
    pub fn policy(&self) -> ExecutionPolicy {
        self.policy
    }
    /// Clones retain this identity. A catalog, policy or exact-grant change
    /// creates a distinct view, even if a later change restores the same policy.
    pub fn authorization_id(&self) -> AuthorizationId {
        self.authorization
    }
    /// An explicit trusted policy change retains the same immutable layout and
    /// installation identities. Previously admitted programs retain their policy.
    pub fn with_policy(&self, policy: ExecutionPolicy) -> Self {
        Self {
            authorization: if policy == self.policy {
                self.authorization
            } else {
                AuthorizationId::fresh()
            },
            context: self.context.clone(),
            timing_grants: self.timing_grants.clone(),
            policy,
        }
    }
    /// Grant an exact implementation's complete timing premise. This immutable
    /// view preserves catalog identity and cannot alter previously admitted code.
    pub fn with_timing_grant(
        &self,
        declaration: OperationBinding,
        requirements: ImplementationRequirements,
    ) -> Result<Self> {
        let physical = self.physical_arguments(&declaration)?;
        let (signature, id, expected) = self
            .context
            .registry
            .resolve_physical(&declaration, &physical)?;
        requirements.validate(signature.inputs.len())?;
        if expected != requirements {
            return Err(AdmissionError::new(
                ErrorCode::Backend,
                "timing-grant-requirements",
            ));
        }
        let grant = TimingGrant {
            declaration,
            id,
            requirements,
        };
        let mut view = self.clone();
        if !view.timing_grants.contains(&grant) {
            if view.timing_grants.len() >= Limits::DEFINITIONS {
                return Err(AdmissionError::new(ErrorCode::Limit, "timing-grant-count"));
            }
            Arc::make_mut(&mut view.timing_grants).push(grant);
            view.authorization = AuthorizationId::fresh();
        }
        Ok(view)
    }
    /// Eligibility only. Linking separately compares actual and expected ports,
    /// scoped identities and the complete independently authored requirements.
    pub fn permits_implementation(
        &self,
        declaration: &OperationBinding,
        id: Option<ImplementationId>,
        requirements: ImplementationRequirements,
    ) -> bool {
        self.policy.permits(requirements)
            || self.timing_grants.iter().any(|grant| {
                grant.declaration == *declaration
                    && grant.id == id
                    && grant.requirements == requirements
            })
    }
    /// Check complete layout ownership in this immutable catalog, including
    /// inactive alternatives. This does not grant a wire codec or execution policy.
    pub fn validate_type(&self, ty: &PhysicalType) -> Result<()> {
        check_type(
            self.context.standard,
            &self.context.representations,
            &self.context.aggregates,
            ty,
        )
    }
    pub fn permits_wire(&self, ty: &PhysicalType, codec: WireCodec) -> bool {
        self.validate_type(ty).is_ok()
            && permits_wire(
                self.context.standard,
                &self.context.aggregates,
                &self.context.wire_permissions,
                ty,
                codec,
            )
    }

    pub fn physical_type(&self, spelling: &str) -> Result<PhysicalType> {
        parse_type(
            self.context.standard,
            &self.context.representations,
            &self.context.aggregates,
            spelling,
        )
    }
    pub fn aggregate_type(
        &self,
        logical: LogicalType,
        representation: Representation,
        children: Vec<PhysicalType>,
    ) -> Result<PhysicalType> {
        let ty = PhysicalType::aggregate(logical, representation, children)?;
        check_type(
            self.context.standard,
            &self.context.representations,
            &self.context.aggregates,
            &ty,
        )?;
        Ok(ty)
    }
    fn physical_arguments(&self, declaration: &OperationBinding) -> Result<Vec<PhysicalType>> {
        declaration
            .physical_arguments
            .iter()
            .map(|s| self.physical_type(s))
            .collect()
    }
    /// Resolve exact choices only after trusted eligibility filtering. A caller
    /// ranking candidates must use this same operation before ranking them.
    pub fn resolve(&self, declaration: OperationBinding) -> Result<ResolvedBinding> {
        let physical = self.physical_arguments(&declaration)?;
        let (signature, id, requirements) = self
            .context
            .registry
            .resolve_physical(&declaration, &physical)?;
        if !self.permits_implementation(&declaration, id, requirements) {
            return Err(AdmissionError::new(
                ErrorCode::Backend,
                "implementation-permission",
            ));
        }
        for ty in signature.inputs.iter().chain(&signature.outputs) {
            check_type(
                self.context.standard,
                &self.context.representations,
                &self.context.aggregates,
                ty,
            )?;
        }
        if declaration.contract == "transcript.native.indexed.observe.data"
            && !self.permits_wire(&signature.inputs[1], WireCodec::Native)
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "transcript-native-wire",
            ));
        }
        let physical = if physical.is_empty() {
            let kind = if declaration.contract.starts_with("sequence.") {
                Some(Type::Sequence)
            } else if declaration.contract.starts_with("field_array.") {
                Some(Type::FieldArray)
            } else if declaration.contract.starts_with("fixed_vector.") {
                Some(Type::FixedVector)
            } else {
                None
            };
            kind.and_then(|kind| {
                signature
                    .inputs
                    .iter()
                    .chain(&signature.outputs)
                    .find(|ty| ty.kind() == kind)
                    .cloned()
            })
            .into_iter()
            .collect()
        } else {
            physical
        };
        ResolvedBinding::admitted(declaration, signature, id, requirements, physical)
    }
}

fn parse_type(
    standard: bool,
    representations: &BTreeMap<&'static str, BTreeMap<LogicalType, PhysicalType>>,
    aggregates: &BTreeMap<&'static str, AggregateRepresentation>,
    spelling: &str,
) -> Result<PhysicalType> {
    PhysicalType::parse_with(spelling, |logical, name, children| {
        let ty = if let Some(owner) = aggregates.get(name) {
            PhysicalType::formed_aggregate(
                logical,
                Representation::Extension(owner.representation),
                children.ok_or_else(|| {
                    AdmissionError::new(ErrorCode::Representation, "aggregate-physical-children")
                })?,
            )?
        } else if let Some(layouts) = representations.get(name) {
            if children.is_some() {
                return Err(AdmissionError::new(
                    ErrorCode::Representation,
                    "flat-layout-children",
                ));
            }
            layouts.get(&logical).cloned().ok_or_else(|| {
                AdmissionError::new(ErrorCode::Representation, "representation-logical-type")
            })?
        } else {
            let representation = Representation::parse(name)?;
            match children {
                Some(children) => {
                    PhysicalType::formed_aggregate(logical, representation, children)?
                }
                None => PhysicalType::new(logical, representation)?,
            }
        };
        // Each parsed child has already passed this same node check. Borrowed
        // descriptors supplied by callers use the complete recursive validator.
        check_type_node(standard, representations, aggregates, &ty)?;
        Ok(ty)
    })
}
fn check_type(
    standard: bool,
    representations: &BTreeMap<&'static str, BTreeMap<LogicalType, PhysicalType>>,
    aggregates: &BTreeMap<&'static str, AggregateRepresentation>,
    ty: &PhysicalType,
) -> Result<()> {
    check_type_node(standard, representations, aggregates, ty)?;
    for child in ty.children().unwrap_or_default() {
        check_type(standard, representations, aggregates, child)?;
    }
    Ok(())
}
fn check_type_node(
    standard: bool,
    representations: &BTreeMap<&'static str, BTreeMap<LogicalType, PhysicalType>>,
    aggregates: &BTreeMap<&'static str, AggregateRepresentation>,
    ty: &PhysicalType,
) -> Result<()> {
    let installed = match ty.representation() {
        Representation::Extension(id) => {
            aggregates
                .get(id.name())
                .is_some_and(|owner| owner.accepts(ty))
                || representations
                    .get(id.name())
                    .and_then(|layouts| layouts.get(ty.logical()))
                    .is_some_and(|expected| expected == ty)
        }
        representation => {
            let allowed = standard
                || matches!(
                    representation,
                    Representation::Bool
                        | Representation::Index
                        | Representation::Sequence
                        | Representation::Variant
                );
            allowed
                && match ty.children() {
                    Some(children) => PhysicalType::check_aggregate_children(
                        &ty.logical,
                        representation,
                        children,
                    )
                    .is_ok(),
                    None => PhysicalType::new(ty.logical().clone(), representation)
                        .is_ok_and(|expected| expected == *ty),
                }
        }
    };
    if !installed {
        return Err(AdmissionError::new(
            ErrorCode::Representation,
            "foreign-or-uninstalled-physical-type",
        ));
    }
    Ok(())
}

fn permits_wire(
    standard: bool,
    aggregates: &BTreeMap<&'static str, AggregateRepresentation>,
    permissions: &BTreeSet<(PhysicalType, WireCodec)>,
    ty: &PhysicalType,
    codec: WireCodec,
) -> bool {
    if ty.is_affine() {
        return false;
    }
    if let Some(children) = ty.children() {
        if !ty.logical().is_native_message_data() {
            return false;
        }
        let frame = permissions.contains(&(ty.clone(), codec))
            || match ty.representation() {
                Representation::Sequence | Representation::Variant => standard,
                Representation::FieldArray => standard && ty.has_native_array_frame(),
                Representation::Extension(id) => aggregates
                    .get(id.name())
                    .is_some_and(|owner| owner.representation == id && owner.native_frame),
                _ => false,
            };
        frame
            && children
                .iter()
                .all(|child| permits_wire(standard, aggregates, permissions, child, codec))
    } else {
        permissions.contains(&(ty.clone(), codec))
            || standard && codec == WireCodec::Native && ty.is_message_type()
    }
}
