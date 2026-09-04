"""Finite falsifier for cross-owner semantic closure laws."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Iterable


class Outcome(str, Enum):
    SUPPORTED = "Supported"
    UNSUPPORTED = "Unsupported"
    AFFIRMATIVE = "Affirmative"
    NEGATIVE = "Negative"
    MISSING_DEPENDENCY = "MissingDependency"
    CANNOT_ANSWER = "CannotAnswer"
    KIND_MISMATCH = "KindMismatch"
    REFUSED = "Refused"
    MALFORMED = "Malformed"
    LIMIT_EXCEEDED = "DeterministicLimitExceeded"
    CHECKER_FAILURE = "CheckerFailure"


@dataclass(frozen=True)
class Result:
    outcome: Outcome
    reasons: tuple[str, ...] = ()


class RunQualification(str, Enum):
    CAUSAL = "CausallyGenerated"
    REPLAY = "ReplayQualified"


@dataclass(frozen=True, eq=False)
class ExecutionBasis:
    protocol: str
    invocation: object
    completed_record: object
    qualification: RunQualification
    qualification_authority: object


_PUBLIC_TOKEN = object()
_CONFIDENTIAL_TOKEN = object()


class PublicRunAuthority:
    __slots__ = ("_basis", "_token")

    def __init__(self, basis: ExecutionBasis, token: object) -> None:
        if token is not _PUBLIC_TOKEN:
            raise TypeError("public run authority is owner-issued")
        self._basis = basis
        self._token = token


class ConfidentialRunCapability:
    __slots__ = ("coordinate", "_basis", "_token")

    def __init__(self, coordinate: str, basis: ExecutionBasis, token: object) -> None:
        if token is not _CONFIDENTIAL_TOKEN:
            raise TypeError("confidential run capability is owner-issued")
        self.coordinate = coordinate
        self._basis = basis
        self._token = token


def issue_public_run_authority(basis: ExecutionBasis) -> PublicRunAuthority:
    return PublicRunAuthority(basis, _PUBLIC_TOKEN)


def issue_confidential_run_capability(
    coordinate: str, basis: ExecutionBasis
) -> ConfidentialRunCapability:
    return ConfidentialRunCapability(coordinate, basis, _CONFIDENTIAL_TOKEN)


def _public_basis(value: object) -> ExecutionBasis | None:
    if type(value) is not PublicRunAuthority or value._token is not _PUBLIC_TOKEN:
        return None
    return value._basis


def _confidential_basis(value: object) -> ExecutionBasis | None:
    if (
        type(value) is not ConfidentialRunCapability
        or value._token is not _CONFIDENTIAL_TOKEN
    ):
        return None
    return value._basis


def check_run_grounding_basis(
    public: object | None,
    confidential: tuple[ConfidentialRunCapability, ...],
) -> Result:
    if type(confidential) is not tuple:
        return Result(Outcome.MALFORMED)
    coordinates = tuple(
        item.coordinate if type(item) is ConfidentialRunCapability else ""
        for item in confidential
    )
    if coordinates != tuple(sorted(set(coordinates))):
        return Result(Outcome.MALFORMED)
    if public is None and not confidential:
        return Result(Outcome.CANNOT_ANSWER)

    public_basis = None if public is None else _public_basis(public)
    if public is not None and public_basis is None:
        return Result(Outcome.REFUSED)
    private_bases = tuple(_confidential_basis(item) for item in confidential)
    if any(item is None for item in private_bases):
        return Result(Outcome.REFUSED)
    selected = public_basis if public_basis is not None else private_bases[0]
    if any(item is not selected for item in private_bases):
        return Result(Outcome.REFUSED)
    if confidential and selected.qualification is not RunQualification.CAUSAL:
        return Result(Outcome.REFUSED)
    return Result(Outcome.AFFIRMATIVE)


class ChallengeMode(str, Enum):
    FRESH = "Fresh"
    FIAT_SHAMIR = "FiatShamir"


class EndpointPurpose(str, Enum):
    VERIFIER = "VerifierEndpoint"
    GENERIC_PROVER = "GenericProverEndpoint"
    PLAN_PROVER = "PlanSpecializedProverEndpoint"
    CONTINUATION_PROVER = "PlanContinuationProverEndpoint"


class ConstructionFamily(str, Enum):
    CANONICAL_FRAMED = "CanonicalFramed"
    DUPLEX_SPONGE = "DuplexSponge"
    OTHER_AUTHENTICATED = "OtherAuthenticated"


SUPPORTED_CONSTRUCTION_FAMILIES = (
    ConstructionFamily.CANONICAL_FRAMED,
    ConstructionFamily.DUPLEX_SPONGE,
)


def admit_fiat_shamir_family_shape(family: object, challenge_count: object) -> Result:
    if type(family) is not ConstructionFamily:
        return Result(Outcome.KIND_MISMATCH)
    if family not in SUPPORTED_CONSTRUCTION_FAMILIES:
        return Result(Outcome.UNSUPPORTED, ("OtherTranscriptConstructionFamily",))
    if type(challenge_count) is not int or challenge_count < 0:
        return Result(Outcome.MALFORMED)
    if challenge_count == 0:
        return Result(Outcome.REFUSED, ("EmptyChallengeDomain",))
    return Result(Outcome.AFFIRMATIVE)


class UnsupportedReason(str, Enum):
    FRESH = "FreshEndpoint"
    GENERIC_PROVER = "GenericProverEndpoint"
    ORACLE = "StandardOracleEndpoint"
    MODULE_EFFECT = "ModuleEffectEndpoint"
    OTHER_CONSTRUCTION = "OtherTranscriptConstructionFamily"
    NO_CONTINUATION_ARM = "NoPlanContinuationArm"


@dataclass(frozen=True)
class EndpointRequest:
    challenge_mode: ChallengeMode
    purpose: EndpointPurpose
    construction_family: ConstructionFamily | None
    has_oracle: bool
    has_module_effect: bool
    plan_present: bool
    plan_realizes_present: bool
    plan_realizes: bool
    continuation_arm_count: int


def classify_endpoint_support(request: object) -> Result:
    if type(request) is not EndpointRequest:
        return Result(Outcome.MALFORMED)
    if (
        type(request.challenge_mode) is not ChallengeMode
        or type(request.purpose) is not EndpointPurpose
        or type(request.has_oracle) is not bool
        or type(request.has_module_effect) is not bool
        or type(request.plan_present) is not bool
        or type(request.plan_realizes_present) is not bool
        or type(request.plan_realizes) is not bool
        or type(request.continuation_arm_count) is not int
        or request.continuation_arm_count < 0
    ):
        return Result(Outcome.MALFORMED)
    if request.challenge_mode is ChallengeMode.FIAT_SHAMIR:
        if type(request.construction_family) is not ConstructionFamily:
            return Result(Outcome.MALFORMED)
    elif request.construction_family is not None:
        return Result(Outcome.MALFORMED)

    feature_reasons: list[UnsupportedReason] = []
    if request.challenge_mode is ChallengeMode.FRESH:
        feature_reasons.append(UnsupportedReason.FRESH)
    if request.purpose is EndpointPurpose.GENERIC_PROVER:
        feature_reasons.append(UnsupportedReason.GENERIC_PROVER)
    if request.has_oracle:
        feature_reasons.append(UnsupportedReason.ORACLE)
    if request.has_module_effect:
        feature_reasons.append(UnsupportedReason.MODULE_EFFECT)
    if request.construction_family in (
        ConstructionFamily.DUPLEX_SPONGE,
        ConstructionFamily.OTHER_AUTHENTICATED,
    ):
        feature_reasons.append(UnsupportedReason.OTHER_CONSTRUCTION)
    if feature_reasons:
        ordered = tuple(
            reason.value for reason in UnsupportedReason if reason in feature_reasons
        )
        return Result(Outcome.UNSUPPORTED, ordered)

    needs_plan = request.purpose in (
        EndpointPurpose.PLAN_PROVER,
        EndpointPurpose.CONTINUATION_PROVER,
    )
    if needs_plan:
        if not request.plan_present or not request.plan_realizes_present:
            return Result(Outcome.MISSING_DEPENDENCY)
        if not request.plan_realizes:
            return Result(Outcome.REFUSED)
    elif (
        request.plan_present
        or request.plan_realizes_present
        or request.plan_realizes
    ):
        return Result(Outcome.MALFORMED)
    if (
        request.purpose is EndpointPurpose.CONTINUATION_PROVER
        and request.continuation_arm_count == 0
    ):
        return Result(
            Outcome.UNSUPPORTED,
            (UnsupportedReason.NO_CONTINUATION_ARM.value,),
        )
    return Result(Outcome.SUPPORTED)


class CounterfactualRight(str, Enum):
    PROGRAM_SIBLING = "ProgramSibling"
    RERUN = "Rerun"


_RIGHT_CAPABILITY = {
    CounterfactualRight.PROGRAM_SIBLING: "program-sibling",
    CounterfactualRight.RERUN: "root-rerun",
}


def admit_counterfactual_rights(
    rights: tuple[object, ...], capabilities: tuple[str, ...]
) -> Result:
    if type(rights) is not tuple or type(capabilities) is not tuple:
        return Result(Outcome.MALFORMED)
    if rights != tuple(sorted(set(rights), key=lambda item: str(item))):
        return Result(Outcome.MALFORMED)
    if any(type(item) is not CounterfactualRight for item in rights):
        return Result(Outcome.REFUSED)
    if any(_RIGHT_CAPABILITY[item] not in capabilities for item in rights):
        return Result(Outcome.REFUSED)
    return Result(Outcome.AFFIRMATIVE)


COMMON_FAILURE_PARTITION = (
    "Unsupported",
    "MissingDependency",
    "CannotAnswer",
    "KindMismatch",
    "Refused",
    "Malformed",
    "DeterministicLimitExceeded",
    "CheckerFailure",
)


@dataclass(frozen=True)
class FailurePartitionRef:
    owner_profile: str
    body: tuple[str, ...]


@dataclass(frozen=True)
class FamilyContract:
    subject_schema: str
    question_schema: str
    conclusion_schema: str
    finite_cover_discharge_contract: str | None
    failure_partition: FailurePartitionRef


@dataclass(frozen=True)
class FamilyContractRef:
    owner_profile: str
    family: str


def common_failure_partition_ref(profile: str) -> FailurePartitionRef:
    return FailurePartitionRef(profile, COMMON_FAILURE_PARTITION)


def transport_family_projection(
    owner_profile: str,
    owner_catalog: dict[str, FamilyContract],
    families: Iterable[str],
) -> tuple[FamilyContractRef, ...]:
    result: list[FamilyContractRef] = []
    for family in families:
        contract = owner_catalog.get(family)
        if contract is None:
            raise ValueError("missing owner family contract")
        if contract.failure_partition != common_failure_partition_ref(owner_profile):
            raise ValueError("family contract uses another failure partition")
        result.append(FamilyContractRef(owner_profile, family))
    return tuple(result)


FS_CONSTRUCTION_DEFECT_ORDER = (
    "SharedCoreMismatch",
    "ConstructionCoreMismatch",
    "TargetConstructionMismatch",
    "PublicCoinEligibilityMissing",
    "OccurrenceDomainMismatch",
    "NonChallengeValueDomainMismatch",
    "ChallengeDomainMismatch",
    "TargetCoreFieldMismatch",
)


@dataclass(frozen=True)
class FSConstructionComparison:
    shared_core_matches: bool
    construction_core_matches: bool
    target_construction_matches: bool
    source_public_coin_eligible: bool
    occurrence_domains_match: bool
    nonchallenge_value_domains_match: bool
    challenge_domains_match: bool
    core_fields_match: bool


def check_fs_construction_comparison(candidate: object) -> Result:
    if type(candidate) is not FSConstructionComparison:
        return Result(Outcome.MALFORMED)
    predicates = (
        candidate.shared_core_matches,
        candidate.construction_core_matches,
        candidate.target_construction_matches,
        candidate.source_public_coin_eligible,
        candidate.occurrence_domains_match,
        candidate.nonchallenge_value_domains_match,
        candidate.challenge_domains_match,
        candidate.core_fields_match,
    )
    if any(type(value) is not bool for value in predicates):
        return Result(Outcome.MALFORMED)
    defects = tuple(
        tag
        for tag, predicate in zip(FS_CONSTRUCTION_DEFECT_ORDER, predicates)
        if not predicate
    )
    if defects:
        return Result(Outcome.NEGATIVE, defects)
    return Result(Outcome.AFFIRMATIVE)


@dataclass(frozen=True)
class AlgorithmContract:
    name: str
    input_abi: tuple[str, ...]
    output_abi: str
    completed_failure_row: tuple[str, ...] = ()


@dataclass(frozen=True)
class VerifierBounds:
    maximum_setup_roles: int
    maximum_context_roles: int
    exact_claim_count: int
    maximum_setup_bytes: int
    maximum_context_bytes: int
    maximum_claim_group_bytes: int
    maximum_evidence_bytes: int
    maximum_schedule_constraints: int
    maximum_group_check_steps: int
    maximum_opening_check_steps: int
    maximum_canonical_body_bytes: int


@dataclass(frozen=True)
class CommitmentProfile:
    setup_role_ordinals: tuple[int, ...]
    context_role_ordinals: tuple[int, ...]
    role_types_valid: bool
    claim_count: int
    schedule_atoms: tuple[str, ...]
    schedule_edges: tuple[tuple[str, str], ...]
    algorithms: tuple[AlgorithmContract, ...]
    declared_bounds: VerifierBounds
    derived_bounds: VerifierBounds
    required_bounds: VerifierBounds
    canonical_body_bytes: int


EXPECTED_COMMITMENT_ALGORITHMS = (
    AlgorithmContract(
        "PackSetupAssignment",
        ("setup-role-values",),
        "CommitmentSetupAssignment",
    ),
    AlgorithmContract(
        "PackVerificationContext",
        ("context-role-values",),
        "CommitmentVerificationContext",
    ),
    AlgorithmContract(
        "PackOpeningClaimGroup",
        ("ordered-opening-claims",),
        "OpeningClaimGroup",
    ),
    AlgorithmContract(
        "CheckClaimGroup",
        (
            "CommitmentSetupAssignment",
            "CommitmentVerificationContext",
            "OpeningClaimGroup",
        ),
        "RootBool",
    ),
    AlgorithmContract(
        "VerifyOpeningGroup",
        (
            "CommitmentSetupAssignment",
            "CommitmentVerificationContext",
            "OpeningClaimGroup",
            "OpeningEvidence",
        ),
        "RootBool",
    ),
    AlgorithmContract(
        "DeriveVerifierBounds",
        ("CommitmentOpeningVerifierStaticShape",),
        "CommitmentOpeningVerifierBounds",
    ),
)


COMMITMENT_DEFECT_ORDER = (
    "SetupRoleOrdinalMismatch",
    "ContextRoleOrdinalMismatch",
    "RoleTypeMismatch",
    "ScheduleAtomMismatch",
    "ScheduleCycle",
    "AlgorithmABIMismatch",
    "AlgorithmCompletedFailureRowNonempty",
    "IntrinsicBoundMismatch",
    "IntrinsicBoundInsufficient",
    "CanonicalBodyBoundExceeded",
)


def _has_cycle(nodes: tuple[str, ...], edges: tuple[tuple[str, str], ...]) -> bool:
    successors = {node: [] for node in nodes}
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        if source not in successors or target not in successors:
            return False
        successors[source].append(target)
        indegree[target] += 1
    ready = [node for node in nodes if indegree[node] == 0]
    visited = 0
    while ready:
        node = ready.pop()
        visited += 1
        for target in successors[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
    return visited != len(nodes)


def admit_commitment_profile(profile: object) -> Result:
    if type(profile) is not CommitmentProfile:
        return Result(Outcome.MALFORMED)
    scalar_shape = (
        type(profile.setup_role_ordinals) is tuple
        and type(profile.context_role_ordinals) is tuple
        and type(profile.role_types_valid) is bool
        and type(profile.claim_count) is int
        and profile.claim_count > 0
        and type(profile.schedule_atoms) is tuple
        and type(profile.schedule_edges) is tuple
        and type(profile.algorithms) is tuple
        and type(profile.declared_bounds) is VerifierBounds
        and type(profile.derived_bounds) is VerifierBounds
        and type(profile.required_bounds) is VerifierBounds
        and type(profile.canonical_body_bytes) is int
    )
    if not scalar_shape:
        return Result(Outcome.MALFORMED)
    defects: list[str] = []
    if profile.setup_role_ordinals != tuple(range(len(profile.setup_role_ordinals))):
        defects.append("SetupRoleOrdinalMismatch")
    if profile.context_role_ordinals != tuple(
        range(len(profile.context_role_ordinals))
    ):
        defects.append("ContextRoleOrdinalMismatch")
    if not profile.role_types_valid:
        defects.append("RoleTypeMismatch")
    if len(set(profile.schedule_atoms)) != len(profile.schedule_atoms) or any(
        source not in profile.schedule_atoms or target not in profile.schedule_atoms
        for source, target in profile.schedule_edges
    ):
        defects.append("ScheduleAtomMismatch")
    elif _has_cycle(profile.schedule_atoms, profile.schedule_edges):
        defects.append("ScheduleCycle")
    if any(type(contract) is not AlgorithmContract for contract in profile.algorithms):
        defects.append("AlgorithmABIMismatch")
    else:
        abi_projection = tuple(
            AlgorithmContract(contract.name, contract.input_abi, contract.output_abi)
            for contract in profile.algorithms
        )
        if abi_projection != EXPECTED_COMMITMENT_ALGORITHMS:
            defects.append("AlgorithmABIMismatch")
        if any(contract.completed_failure_row for contract in profile.algorithms):
            defects.append("AlgorithmCompletedFailureRowNonempty")
    if profile.declared_bounds != profile.derived_bounds:
        defects.append("IntrinsicBoundMismatch")
    declared = profile.declared_bounds
    required = profile.required_bounds
    maximum_fields = (
        "maximum_setup_bytes",
        "maximum_context_bytes",
        "maximum_claim_group_bytes",
        "maximum_evidence_bytes",
        "maximum_group_check_steps",
        "maximum_opening_check_steps",
    )
    if (
        declared.maximum_setup_roles < len(profile.setup_role_ordinals)
        or declared.maximum_context_roles < len(profile.context_role_ordinals)
        or declared.exact_claim_count != profile.claim_count
        or declared.maximum_schedule_constraints < len(profile.schedule_edges)
        or any(
            getattr(declared, field) < getattr(required, field)
            for field in maximum_fields
        )
    ):
        defects.append("IntrinsicBoundInsufficient")
    if profile.canonical_body_bytes > declared.maximum_canonical_body_bytes:
        defects.append("CanonicalBodyBoundExceeded")
    if defects:
        ordered = tuple(item for item in COMMITMENT_DEFECT_ORDER if item in defects)
        return Result(Outcome.NEGATIVE, ordered)
    return Result(Outcome.AFFIRMATIVE)


class DuplexMaterialRefusal(str, Enum):
    INVOCATION_CORE = "InvocationCoreMismatch"
    KEY_SET = "MaterialKeySetMismatch"
    SALT_LENGTH = "SaltLengthMismatch"
    LATE = "LatePreparation"


class InstanceValueOrigin(str, Enum):
    PUBLIC_INPUT = "PublicInput"
    CONSTANT = "Constant"
    DERIVED = "Derived"
    OCCURRENCE_OUTPUT = "OccurrenceOutput"


@dataclass(frozen=True)
class DuplexInstanceBinding:
    binding_ref: int
    origin: InstanceValueOrigin
    public_input_ref: int | None
    value_type_body: bytes


@dataclass(frozen=True)
class PublicInputDatum:
    value_type_body: bytes
    datum: bytes


@dataclass(frozen=True)
class InstanceEncodingResult:
    outcome: Outcome
    encoded: bytes = b""


def _meta_natural(value: int) -> bytes:
    return b"N" + value.to_bytes(8, "big")


def _meta_bytes(value: bytes) -> bytes:
    return b"Y" + len(value).to_bytes(4, "big") + value


def _meta_record(fields: tuple[tuple[int, bytes], ...]) -> bytes:
    payload = b"".join(
        key.to_bytes(4, "big") + len(value).to_bytes(4, "big") + value
        for key, value in fields
    )
    return b"R" + len(fields).to_bytes(4, "big") + payload


def _meta_sequence(values: tuple[bytes, ...]) -> bytes:
    payload = b"".join(len(value).to_bytes(4, "big") + value for value in values)
    return b"S" + len(values).to_bytes(4, "big") + payload


def encode_duplex_instance(
    bindings: object, public_inputs: object
) -> InstanceEncodingResult:
    if type(bindings) is not tuple or type(public_inputs) is not tuple:
        return InstanceEncodingResult(Outcome.MALFORMED)
    if any(type(binding) is not DuplexInstanceBinding for binding in bindings):
        return InstanceEncodingResult(Outcome.MALFORMED)
    if any(type(value) is not PublicInputDatum for value in public_inputs):
        return InstanceEncodingResult(Outcome.MALFORMED)
    refs = tuple(binding.binding_ref for binding in bindings)
    if refs != tuple(sorted(set(refs))) or any(
        type(ref) is not int or ref < 0 for ref in refs
    ):
        return InstanceEncodingResult(Outcome.MALFORMED)

    records: list[bytes] = []
    for binding in bindings:
        if binding.origin is not InstanceValueOrigin.PUBLIC_INPUT:
            return InstanceEncodingResult(Outcome.REFUSED)
        ref = binding.public_input_ref
        if type(ref) is not int or ref < 0 or ref >= len(public_inputs):
            return InstanceEncodingResult(Outcome.MISSING_DEPENDENCY)
        value = public_inputs[ref]
        if binding.value_type_body != value.value_type_body:
            return InstanceEncodingResult(Outcome.KIND_MISMATCH)
        records.append(
            _meta_record(
                (
                    (0, _meta_natural(binding.binding_ref)),
                    (1, _meta_bytes(binding.value_type_body)),
                    (2, _meta_bytes(value.datum)),
                )
            )
        )
    return InstanceEncodingResult(Outcome.AFFIRMATIVE, _meta_sequence(tuple(records)))


class SaltCarrierState(str, Enum):
    EXACT = "ExactLength"
    SHORT_WITHIN_CAPACITY = "ShortWithinCapacity"
    WRONG_CARRIER_TYPE = "WrongCarrierType"
    EXCEEDS_DECLARED_CAPACITY = "ExceedsDeclaredCapacity"


@dataclass(frozen=True)
class DuplexMaterialCandidate:
    invocation_core_matches: bool
    key_set_matches: bool
    salt_state: SaltCarrierState
    execution_started: bool


def prepare_duplex_material(candidate: object) -> Result:
    if type(candidate) is not DuplexMaterialCandidate:
        return Result(Outcome.MALFORMED)
    if (
        any(
            type(value) is not bool
            for value in (
                candidate.invocation_core_matches,
                candidate.key_set_matches,
                candidate.execution_started,
            )
        )
        or type(candidate.salt_state) is not SaltCarrierState
    ):
        return Result(Outcome.MALFORMED)
    if candidate.salt_state is SaltCarrierState.WRONG_CARRIER_TYPE:
        return Result(Outcome.KIND_MISMATCH)
    if candidate.salt_state is SaltCarrierState.EXCEEDS_DECLARED_CAPACITY:
        return Result(Outcome.MALFORMED)
    predicates = {
        DuplexMaterialRefusal.INVOCATION_CORE: not candidate.invocation_core_matches,
        DuplexMaterialRefusal.KEY_SET: not candidate.key_set_matches,
        DuplexMaterialRefusal.SALT_LENGTH: candidate.salt_state
        is SaltCarrierState.SHORT_WITHIN_CAPACITY,
        DuplexMaterialRefusal.LATE: candidate.execution_started,
    }
    reasons = tuple(
        reason.value for reason in DuplexMaterialRefusal if predicates[reason]
    )
    if reasons:
        return Result(Outcome.REFUSED, reasons)
    return Result(Outcome.AFFIRMATIVE)
