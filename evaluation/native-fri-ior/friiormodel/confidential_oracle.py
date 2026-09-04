"""Owner-local authority for an exact initial logical-Oracle carrier.

The native Core identifies the G0 coordinate but does not identify its
material.  This module gives the executable pressure case a causal path from
pre-execution owner input to a purpose-bound whole-carrier view.  Every object
that can reveal or authorize the carrier is process-local, non-copyable, and
non-serializable.  Public replay can check a committed proof, but a trace,
trace identity, verification result, or construction receipt cannot mint this
authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .classical import (
    CLASSICAL_DOMAINS,
    DEFAULT_APPLICATION_CONTEXT,
    DEFAULT_SALT_SEED,
    DEFAULT_SOURCE_COEFFICIENTS,
    DEFAULT_STATEMENT,
    EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID,
    EXACT_CLASSICAL_NATIVE_CORE,
    EXACT_CLASSICAL_ORACLE_DECLARATIONS,
    EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID,
    EXACT_NATIVE_TERMINAL_COORDINATE_ID,
    ClassicalCommittedCase,
    ClassicalLogicalOracle,
    ClassicalNativeTrace,
    GoldilocksElement,
    build_honest_classical_case,
    evaluate_polynomial,
    form_classical_public_environment,
    verify_native_trace,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    SemanticId,
    affirmative,
    encode_term,
    malformed,
    refused,
    semantic_id,
)


WHOLE_CARRIER_SCOPE = "WholeCarrier"
CAUSAL_QUALIFICATION = "CausallyGeneratedOnly"
EXACT_INITIAL_ORACLE_COORDINATE_ID = (
    EXACT_CLASSICAL_ORACLE_DECLARATIONS[0].identity
)


def _semantic_ref(value: object, field_name: str) -> SemanticId:
    if not isinstance(value, SemanticId):
        raise malformed(
            "confidential-initial-oracle:formation",
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-001",
            f"{field_name} requires a SemanticId",
        )
    return value


class _ProcessLocal:
    """Common denial surface for every live owner-local object."""

    __slots__ = ()

    def __copy__(self) -> None:
        raise TypeError("confidential initial-Oracle authority cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("confidential initial-Oracle authority cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("confidential initial-Oracle authority cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("confidential initial-Oracle authority cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("confidential initial-Oracle authority has no portable state")


_SUPPLY_REF_TOKEN = object()
_INVOCATION_REF_TOKEN = object()


class InitialOracleSupplyRef(_ProcessLocal):
    """Collision-free only through process-local object identity."""

    __slots__ = ("_authority",)

    def __init__(self, *, _token: object) -> None:
        if _token is not _SUPPLY_REF_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:supply-ref-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-002",
                "a supply reference is minted only by owner generation",
            )
        self._authority = _SUPPLY_REF_TOKEN

    def __repr__(self) -> str:
        return "InitialOracleSupplyRef(process_local=True)"


class NativeInvocationRef(_ProcessLocal):
    """One process-local occurrence of the otherwise static invocation shape."""

    __slots__ = ("_authority",)

    def __init__(self, *, _token: object) -> None:
        if _token is not _INVOCATION_REF_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:invocation-ref-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-003",
                "an invocation reference is minted only by causal generation",
            )
        self._authority = _INVOCATION_REF_TOKEN

    def __repr__(self) -> str:
        return "NativeInvocationRef(process_local=True)"


_SUPPLY_TOKEN = object()
_SUPPLY_CAPABILITY_TOKEN = object()


class InitialOracleSupplyOccurrence(_ProcessLocal):
    """Pre-execution G0 material with no portable material-derived identity."""

    __slots__ = (
        "_authority",
        "_native_core_id",
        "_protocol_id",
        "_public_environment_id",
        "_oracle_coordinate_id",
        "_fixation_coordinate_id",
        "_values",
        "_supply_ref",
    )

    def __init__(
        self,
        public_environment_id: SemanticId,
        values: tuple[GoldilocksElement, ...],
        *,
        _token: object,
    ) -> None:
        if _token is not _SUPPLY_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:supply-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-004",
                "initial material is issued only by the owner generation path",
            )
        _semantic_ref(public_environment_id, "public_environment_id")
        if (
            type(values) is not tuple
            or len(values) != CLASSICAL_DOMAINS[0].order
            or any(not isinstance(value, GoldilocksElement) for value in values)
        ):
            raise malformed(
                "confidential-initial-oracle:supply-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-005",
                "initial G0 material must cover the complete exact domain",
            )
        self._authority = _SUPPLY_TOKEN
        self._native_core_id = EXACT_CLASSICAL_NATIVE_CORE.identity
        self._protocol_id = EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID
        self._public_environment_id = public_environment_id
        self._oracle_coordinate_id = EXACT_INITIAL_ORACLE_COORDINATE_ID
        self._fixation_coordinate_id = EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID
        self._values = values
        self._supply_ref = InitialOracleSupplyRef(_token=_SUPPLY_REF_TOKEN)

    @property
    def native_core_id(self) -> SemanticId:
        return self._native_core_id

    @property
    def protocol_id(self) -> SemanticId:
        return self._protocol_id

    @property
    def public_environment_id(self) -> SemanticId:
        return self._public_environment_id

    @property
    def oracle_coordinate_id(self) -> SemanticId:
        return self._oracle_coordinate_id

    @property
    def fixation_coordinate_id(self) -> SemanticId:
        return self._fixation_coordinate_id

    def __repr__(self) -> str:
        return (
            "InitialOracleSupplyOccurrence("
            f"oracle_coordinate_id={self.oracle_coordinate_id.to_text()}, "
            "owner_local=True)"
        )


class InitialOracleSupplyCapability(_ProcessLocal):
    """Fresh bearer authority for one owner-local supply occurrence."""

    __slots__ = ("_authority", "_occurrence")

    def __init__(
        self,
        occurrence: InitialOracleSupplyOccurrence,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _SUPPLY_CAPABILITY_TOKEN
            or type(occurrence) is not InitialOracleSupplyOccurrence
            or occurrence._authority is not _SUPPLY_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:supply-capability-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-006",
                "a supply capability requires the live owner occurrence",
            )
        self._authority = _SUPPLY_CAPABILITY_TOKEN
        self._occurrence = occurrence

    def __repr__(self) -> str:
        return "InitialOracleSupplyCapability(owner_local=True)"


_CAUSAL_EXECUTION_TOKEN = object()


class CausalNativeExecutionAuthority(_ProcessLocal):
    """Authority that the exact trace was generated from one live G0 supply."""

    __slots__ = (
        "_authority",
        "_supply_capability",
        "_trace",
        "_invocation_ref",
        "_invocation_coordinate_id",
    )

    def __init__(
        self,
        supply_capability: InitialOracleSupplyCapability,
        trace: ClassicalNativeTrace,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _CAUSAL_EXECUTION_TOKEN
            or type(supply_capability) is not InitialOracleSupplyCapability
            or supply_capability._authority is not _SUPPLY_CAPABILITY_TOKEN
            or type(trace) is not ClassicalNativeTrace
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:causal-execution-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-007",
                "causal execution authority requires live owner generation state",
            )
        occurrence = supply_capability._occurrence
        initial = trace.oracles[0]
        if (
            trace.native_core_id != occurrence.native_core_id
            or trace.public_environment.identity != occurrence.public_environment_id
            or type(initial) is not ClassicalLogicalOracle
            or initial.layer != 0
            or initial.origin != "InitialOracle"
            or initial.values != occurrence._values
        ):
            raise ModelFailure(
                OutcomeClass.REFUSED,
                "confidential-initial-oracle:causal-execution-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-008",
                "the generated execution does not use the exact live initial supply",
            )
        self._authority = _CAUSAL_EXECUTION_TOKEN
        self._supply_capability = supply_capability
        self._trace = trace
        self._invocation_ref = NativeInvocationRef(_token=_INVOCATION_REF_TOKEN)
        self._invocation_coordinate_id = semantic_id(
            "classical-fri-native-invocation-coordinate",
            "classical-fri.native-invocation-coordinate.v1",
            {
                "native_core_id": occurrence.native_core_id.to_term(),
                "public_environment_id": occurrence.public_environment_id.to_term(),
            },
        )

    @property
    def invocation_coordinate_id(self) -> SemanticId:
        return self._invocation_coordinate_id

    def __repr__(self) -> str:
        return (
            "CausalNativeExecutionAuthority("
            f"invocation_coordinate_id={self.invocation_coordinate_id.to_text()}, "
            "owner_local=True)"
        )


class CausalClassicalCase(_ProcessLocal):
    """One exact case together with its non-portable generation authorities."""

    __slots__ = ("case", "supply_capability", "execution_authority")

    def __init__(
        self,
        case: ClassicalCommittedCase,
        supply_capability: InitialOracleSupplyCapability,
        execution_authority: CausalNativeExecutionAuthority,
    ) -> None:
        self.case = case
        self.supply_capability = supply_capability
        self.execution_authority = execution_authority

    def __repr__(self) -> str:
        return "CausalClassicalCase(owner_local=True)"


def build_causal_honest_classical_case(
    statement: Any = DEFAULT_STATEMENT,
    application_context: Any = DEFAULT_APPLICATION_CONTEXT,
    source_coefficients: tuple[GoldilocksElement, ...] = DEFAULT_SOURCE_COEFFICIENTS,
    *,
    salt_seed: bytes = DEFAULT_SALT_SEED,
    salts_by_layer: tuple[tuple[bytes, ...], ...] | None = None,
    terminal_scalar_override: GoldilocksElement | None = None,
) -> CausalClassicalCase:
    """Run the owner path, fixing G0 before the exact execution is generated."""

    if (
        type(source_coefficients) is not tuple
        or len(source_coefficients) != 8
        or any(not isinstance(value, GoldilocksElement) for value in source_coefficients)
    ):
        raise malformed(
            "confidential-initial-oracle:owner-generation",
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-009",
            "owner generation requires the exact eight-coefficient input",
        )
    public_environment = form_classical_public_environment(
        statement,
        application_context,
    )
    initial_values = tuple(
        evaluate_polynomial(source_coefficients, point)
        for point in CLASSICAL_DOMAINS[0].points()
    )
    occurrence = InitialOracleSupplyOccurrence(
        public_environment.identity,
        initial_values,
        _token=_SUPPLY_TOKEN,
    )
    supply_capability = InitialOracleSupplyCapability(
        occurrence,
        _token=_SUPPLY_CAPABILITY_TOKEN,
    )
    case = build_honest_classical_case(
        statement,
        application_context,
        source_coefficients,
        salt_seed=salt_seed,
        salts_by_layer=salts_by_layer,
        terminal_scalar_override=terminal_scalar_override,
    )
    execution_authority = CausalNativeExecutionAuthority(
        supply_capability,
        case.native_trace,
        _token=_CAUSAL_EXECUTION_TOKEN,
    )
    return CausalClassicalCase(case, supply_capability, execution_authority)


@dataclass(frozen=True, slots=True)
class ConfidentialInitialOracleDisclosurePolicy:
    """Portable policy coordinate; it contains no carrier-dependent field."""

    protocol_id: SemanticId
    native_core_id: SemanticId
    oracle_coordinate_id: SemanticId
    fixation_coordinate_id: SemanticId
    downstream_consumer_id: SemanticId
    purpose_id: SemanticId
    view_scope: str = WHOLE_CARRIER_SCOPE
    qualification: str = CAUSAL_QUALIFICATION

    def __post_init__(self) -> None:
        for field_name, value in (
            ("protocol_id", self.protocol_id),
            ("native_core_id", self.native_core_id),
            ("oracle_coordinate_id", self.oracle_coordinate_id),
            ("fixation_coordinate_id", self.fixation_coordinate_id),
            ("downstream_consumer_id", self.downstream_consumer_id),
            ("purpose_id", self.purpose_id),
        ):
            _semantic_ref(value, field_name)
        if self.view_scope != WHOLE_CARRIER_SCOPE:
            raise malformed(
                "confidential-initial-oracle:policy-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-010",
                "the bounded disclosure policy exposes only the whole carrier",
            )
        if self.qualification != CAUSAL_QUALIFICATION:
            raise malformed(
                "confidential-initial-oracle:policy-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-011",
                "the bounded disclosure policy requires causal generation",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "protocol_id": self.protocol_id.to_term(),
            "native_core_id": self.native_core_id.to_term(),
            "oracle_coordinate_id": self.oracle_coordinate_id.to_term(),
            "fixation_coordinate_id": self.fixation_coordinate_id.to_term(),
            "downstream_consumer_id": self.downstream_consumer_id.to_term(),
            "purpose_id": self.purpose_id.to_term(),
            "view_scope": self.view_scope,
            "qualification": self.qualification,
            "material_in_policy": False,
            "material_digest_in_policy": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "confidential-initial-oracle-disclosure-policy",
            "classical-fri.confidential-initial-oracle-policy.v1",
            self.to_term(),
        )


_CHECKED_POLICY_TOKEN = object()
_POLICY_CAPABILITY_TOKEN = object()


class CheckedConfidentialInitialOracleDisclosurePolicy(_ProcessLocal):
    __slots__ = ("_authority", "declaration")

    def __init__(
        self,
        declaration: ConfidentialInitialOracleDisclosurePolicy,
        *,
        _token: object,
    ) -> None:
        if _token is not _CHECKED_POLICY_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:checked-policy-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-012",
                "a checked policy is minted only by policy admission",
            )
        self._authority = _CHECKED_POLICY_TOKEN
        self.declaration = declaration

    def __repr__(self) -> str:
        return (
            "CheckedConfidentialInitialOracleDisclosurePolicy("
            f"policy_id={self.declaration.identity.to_text()}, process_local=True)"
        )


class ConfidentialInitialOracleDisclosurePolicyCapability(_ProcessLocal):
    __slots__ = ("_authority", "_checked")

    def __init__(
        self,
        checked: CheckedConfidentialInitialOracleDisclosurePolicy,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _POLICY_CAPABILITY_TOKEN
            or type(checked) is not CheckedConfidentialInitialOracleDisclosurePolicy
            or checked._authority is not _CHECKED_POLICY_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:policy-capability-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-013",
                "a policy capability requires the exact checked policy",
            )
        self._authority = _POLICY_CAPABILITY_TOKEN
        self._checked = checked

    @property
    def policy(self) -> ConfidentialInitialOracleDisclosurePolicy:
        return self._checked.declaration

    def __repr__(self) -> str:
        return (
            "ConfidentialInitialOracleDisclosurePolicyCapability("
            f"policy_id={self.policy.identity.to_text()}, process_local=True)"
        )


@dataclass(frozen=True, slots=True)
class ConfidentialInitialOraclePolicyAdmission:
    result: CheckResult
    checked: CheckedConfidentialInitialOracleDisclosurePolicy | None
    capability: ConfidentialInitialOracleDisclosurePolicyCapability | None


def admit_confidential_initial_oracle_disclosure_policy(
    declaration: object,
) -> ConfidentialInitialOraclePolicyAdmission:
    boundary = "confidential-initial-oracle:policy-admission"
    if type(declaration) is not ConfidentialInitialOracleDisclosurePolicy:
        return ConfidentialInitialOraclePolicyAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-020",
                "policy admission requires the exact declaration carrier",
            ),
            None,
            None,
        )
    if (
        declaration.protocol_id != EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID
        or declaration.native_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity
        or declaration.oracle_coordinate_id != EXACT_INITIAL_ORACLE_COORDINATE_ID
        or declaration.fixation_coordinate_id
        != EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID
    ):
        return ConfidentialInitialOraclePolicyAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-021",
                "the policy names a different Protocol, Core, Oracle, or fixation coordinate",
            ),
            None,
            None,
        )
    checked = CheckedConfidentialInitialOracleDisclosurePolicy(
        declaration,
        _token=_CHECKED_POLICY_TOKEN,
    )
    capability = ConfidentialInitialOracleDisclosurePolicyCapability(
        checked,
        _token=_POLICY_CAPABILITY_TOKEN,
    )
    return ConfidentialInitialOraclePolicyAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-100",
            "the value-free causal disclosure policy is admitted",
            subject=declaration.identity,
            view_scope=WHOLE_CARRIER_SCOPE,
            qualification=CAUSAL_QUALIFICATION,
        ),
        checked,
        capability,
    )


_VIEW_TOKEN = object()
_CHECKED_VIEW_TOKEN = object()
_VIEW_CAPABILITY_TOKEN = object()


@dataclass(frozen=True, slots=True)
class CausalNativeRunFact:
    """Value-free public fact issued while the causal execution is live."""

    protocol_id: SemanticId
    native_core_id: SemanticId
    public_environment_id: SemanticId
    invocation_coordinate_id: SemanticId
    initial_oracle_coordinate_id: SemanticId
    initial_oracle_fixation_coordinate_id: SemanticId
    terminal_occurrence_coordinate_id: SemanticId
    execution_terminal: str

    def __post_init__(self) -> None:
        for field_name, value in (
            ("protocol_id", self.protocol_id),
            ("native_core_id", self.native_core_id),
            ("public_environment_id", self.public_environment_id),
            ("invocation_coordinate_id", self.invocation_coordinate_id),
            ("initial_oracle_coordinate_id", self.initial_oracle_coordinate_id),
            (
                "initial_oracle_fixation_coordinate_id",
                self.initial_oracle_fixation_coordinate_id,
            ),
            (
                "terminal_occurrence_coordinate_id",
                self.terminal_occurrence_coordinate_id,
            ),
        ):
            _semantic_ref(value, field_name)
        if self.execution_terminal not in ("Accept", "Reject"):
            raise malformed(
                "confidential-initial-oracle:run-fact-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-017",
                "a public native-run fact has an Accept or Reject terminal",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "protocol_id": self.protocol_id.to_term(),
            "native_core_id": self.native_core_id.to_term(),
            "public_environment_id": self.public_environment_id.to_term(),
            "invocation_coordinate_id": self.invocation_coordinate_id.to_term(),
            "initial_oracle_coordinate_id": (
                self.initial_oracle_coordinate_id.to_term()
            ),
            "initial_oracle_fixation_coordinate_id": (
                self.initial_oracle_fixation_coordinate_id.to_term()
            ),
            "terminal_occurrence_coordinate_id": (
                self.terminal_occurrence_coordinate_id.to_term()
            ),
            "execution_terminal": self.execution_terminal,
            "trace_identity_serialized": False,
            "oracle_material_serialized": False,
            "terminal_value_serialized": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-native-run-fact",
            "classical-fri.native-run-fact.v1",
            self.to_term(),
        )


class ConfidentialInitialOracleView(_ProcessLocal):
    """A whole-carrier view retained only inside one live authority chain."""

    __slots__ = (
        "_authority",
        "_protocol_id",
        "_native_core_id",
        "_public_environment_id",
        "_oracle_coordinate_id",
        "_fixation_coordinate_id",
        "_invocation_coordinate_id",
        "_invocation_ref",
        "_supply_ref",
        "_policy",
        "_values",
        "_run_fact",
    )

    def __init__(
        self,
        execution: CausalNativeExecutionAuthority,
        policy: ConfidentialInitialOracleDisclosurePolicy,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _VIEW_TOKEN
            or not _has_live_causal_execution_authority(execution)
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:view-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-014",
                "a confidential view requires exact causal execution authority",
            )
        occurrence = execution._supply_capability._occurrence
        self._authority = _VIEW_TOKEN
        self._protocol_id = occurrence.protocol_id
        self._native_core_id = occurrence.native_core_id
        self._public_environment_id = occurrence.public_environment_id
        self._oracle_coordinate_id = occurrence.oracle_coordinate_id
        self._fixation_coordinate_id = occurrence.fixation_coordinate_id
        self._invocation_coordinate_id = execution.invocation_coordinate_id
        self._invocation_ref = execution._invocation_ref
        self._supply_ref = occurrence._supply_ref
        self._policy = policy
        self._values = occurrence._values
        verification = verify_native_trace(execution._trace)
        self._run_fact = CausalNativeRunFact(
            protocol_id=occurrence.protocol_id,
            native_core_id=occurrence.native_core_id,
            public_environment_id=occurrence.public_environment_id,
            invocation_coordinate_id=execution.invocation_coordinate_id,
            initial_oracle_coordinate_id=occurrence.oracle_coordinate_id,
            initial_oracle_fixation_coordinate_id=(
                occurrence.fixation_coordinate_id
            ),
            terminal_occurrence_coordinate_id=EXACT_NATIVE_TERMINAL_COORDINATE_ID,
            execution_terminal=(
                "Accept"
                if verification.outcome is OutcomeClass.AFFIRMATIVE
                else "Reject"
            ),
        )

    @property
    def policy_id(self) -> SemanticId:
        return self._policy.identity

    def __repr__(self) -> str:
        return (
            "ConfidentialInitialOracleView("
            f"policy_id={self.policy_id.to_text()}, owner_local=True)"
        )


class CheckedConfidentialInitialOracleViewAuthority(_ProcessLocal):
    __slots__ = ("_authority", "_view")

    def __init__(self, view: ConfidentialInitialOracleView, *, _token: object) -> None:
        if (
            _token is not _CHECKED_VIEW_TOKEN
            or type(view) is not ConfidentialInitialOracleView
            or view._authority is not _VIEW_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:checked-view-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-015",
                "checked view authority requires the issuer-created view",
            )
        self._authority = _CHECKED_VIEW_TOKEN
        self._view = view

    def __repr__(self) -> str:
        return "CheckedConfidentialInitialOracleViewAuthority(process_local=True)"


class ConfidentialInitialOracleViewCapability(_ProcessLocal):
    __slots__ = ("_authority", "_checked")

    def __init__(
        self,
        checked: CheckedConfidentialInitialOracleViewAuthority,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _VIEW_CAPABILITY_TOKEN
            or type(checked) is not CheckedConfidentialInitialOracleViewAuthority
            or checked._authority is not _CHECKED_VIEW_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "confidential-initial-oracle:view-capability-formation",
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-016",
                "a view capability requires exact checked view authority",
            )
        self._authority = _VIEW_CAPABILITY_TOKEN
        self._checked = checked

    @property
    def policy_id(self) -> SemanticId:
        return self._checked._view.policy_id

    def __repr__(self) -> str:
        return (
            "ConfidentialInitialOracleViewCapability("
            f"policy_id={self.policy_id.to_text()}, process_local=True)"
        )


@dataclass(frozen=True, slots=True)
class ConfidentialInitialOracleViewAdmission:
    result: CheckResult
    checked_authority: CheckedConfidentialInitialOracleViewAuthority | None
    capability: ConfidentialInitialOracleViewCapability | None


def issue_confidential_initial_oracle_view(
    execution_authority: object,
    policy_capability: object,
) -> ConfidentialInitialOracleViewAdmission:
    boundary = "confidential-initial-oracle:view-issuance"
    if not _has_live_causal_execution_authority(execution_authority):
        return ConfidentialInitialOracleViewAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-022",
                "a raw trace or replay result is not causal execution authority",
            ),
            None,
            None,
        )
    if (
        type(policy_capability)
        is not ConfidentialInitialOracleDisclosurePolicyCapability
        or policy_capability._authority is not _POLICY_CAPABILITY_TOKEN
        or policy_capability._checked._authority is not _CHECKED_POLICY_TOKEN
    ):
        return ConfidentialInitialOracleViewAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-023",
                "view issuance requires the live checked-policy capability",
            ),
            None,
            None,
        )
    occurrence = execution_authority._supply_capability._occurrence
    policy = policy_capability.policy
    if (
        policy.protocol_id != occurrence.protocol_id
        or policy.native_core_id != occurrence.native_core_id
        or policy.oracle_coordinate_id != occurrence.oracle_coordinate_id
        or policy.fixation_coordinate_id != occurrence.fixation_coordinate_id
    ):
        return ConfidentialInitialOracleViewAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-CONFIDENTIAL-024",
                "the policy belongs to a different Protocol, Core, Oracle, or fixation coordinate",
            ),
            None,
            None,
        )
    view = ConfidentialInitialOracleView(
        execution_authority,
        policy,
        _token=_VIEW_TOKEN,
    )
    checked = CheckedConfidentialInitialOracleViewAuthority(
        view,
        _token=_CHECKED_VIEW_TOKEN,
    )
    capability = ConfidentialInitialOracleViewCapability(
        checked,
        _token=_VIEW_CAPABILITY_TOKEN,
    )
    return ConfidentialInitialOracleViewAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-101",
            "the causal whole-carrier view is available under the exact policy",
            subject=policy.identity,
            protocol_id=occurrence.protocol_id,
            invocation_coordinate_id=execution_authority.invocation_coordinate_id,
            oracle_coordinate_id=occurrence.oracle_coordinate_id,
            fixation_coordinate_id=occurrence.fixation_coordinate_id,
            material_serialized=False,
            material_digest_serialized=False,
        ),
        checked,
        capability,
    )


def _has_live_causal_execution_authority(value: object) -> bool:
    return (
        type(value) is CausalNativeExecutionAuthority
        and value._authority is _CAUSAL_EXECUTION_TOKEN
        and type(value._supply_capability) is InitialOracleSupplyCapability
        and value._supply_capability._authority is _SUPPLY_CAPABILITY_TOKEN
        and value._supply_capability._occurrence._authority is _SUPPLY_TOKEN
        and value._invocation_ref._authority is _INVOCATION_REF_TOKEN
    )


def _read_causal_execution_binding(
    value: object,
) -> tuple[
    SemanticId,
    SemanticId,
    SemanticId,
    SemanticId,
    SemanticId,
    NativeInvocationRef,
    InitialOracleSupplyRef,
]:
    if not _has_live_causal_execution_authority(value):
        raise ModelFailure(
            OutcomeClass.MISSING_DEPENDENCY,
            "confidential-initial-oracle:causal-read",
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-025",
            "the exact causal execution authority is unavailable",
        )
    occurrence = value._supply_capability._occurrence
    return (
        occurrence.protocol_id,
        occurrence.native_core_id,
        occurrence.public_environment_id,
        occurrence.oracle_coordinate_id,
        occurrence.fixation_coordinate_id,
        value._invocation_ref,
        occurrence._supply_ref,
    )


def _read_confidential_initial_oracle_view(
    capability: object,
) -> ConfidentialInitialOracleView:
    if (
        type(capability) is not ConfidentialInitialOracleViewCapability
        or capability._authority is not _VIEW_CAPABILITY_TOKEN
        or capability._checked._authority is not _CHECKED_VIEW_TOKEN
        or capability._checked._view._authority is not _VIEW_TOKEN
    ):
        raise ModelFailure(
            OutcomeClass.MISSING_DEPENDENCY,
            "confidential-initial-oracle:view-read",
            "FRI-IOR-CLASSICAL-CONFIDENTIAL-026",
            "the exact confidential view capability is unavailable",
        )
    return capability._checked._view


__all__ = [
    "CAUSAL_QUALIFICATION",
    "CausalClassicalCase",
    "CausalNativeRunFact",
    "CausalNativeExecutionAuthority",
    "CheckedConfidentialInitialOracleDisclosurePolicy",
    "CheckedConfidentialInitialOracleViewAuthority",
    "ConfidentialInitialOracleDisclosurePolicy",
    "ConfidentialInitialOracleDisclosurePolicyCapability",
    "ConfidentialInitialOraclePolicyAdmission",
    "ConfidentialInitialOracleView",
    "ConfidentialInitialOracleViewAdmission",
    "ConfidentialInitialOracleViewCapability",
    "EXACT_INITIAL_ORACLE_COORDINATE_ID",
    "InitialOracleSupplyCapability",
    "InitialOracleSupplyOccurrence",
    "InitialOracleSupplyRef",
    "NativeInvocationRef",
    "WHOLE_CARRIER_SCOPE",
    "admit_confidential_initial_oracle_disclosure_policy",
    "build_causal_honest_classical_case",
    "issue_confidential_initial_oracle_view",
]
