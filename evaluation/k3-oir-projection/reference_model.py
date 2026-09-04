"""Bounded K3-D exact endpoint-graph translation-validation instrument.

The imported executable K2/K3-B Schnorr carrier is retained as a behavioral
control, but it is older than the selected owner schemas.  Positive cases use
an explicit future-owner P01 contract fixture containing the exact codec,
slot, fibre, Statement-flow, completion, claim, terminal, FS, and recipe facts
that K3-D reads.  The instrument never silently synthesizes those facts from
the legacy carrier.

PIR extraction and OIR construction are independently implemented.  Local OIR
admission receives no source object.  A third checker compares the complete
canonical endpoint graphs exactly inside this bounded executable model.  The
instrument currently uses a deterministic JSON carrier for those graphs; it
does not claim byte identity with the durable K1 ``MetaValueV0`` bodies.  The
four constraints once represented as source-owned ``absence`` rows are now
graph-formation laws: the complete ABI, static completion interface, static
FS, and Plan graph make them finitely decidable without a second
identity-bearing universe.

This is a finite falsifier, not a durable K2/K3-B inhabitance claim, final OIR
syntax, compiler proof, execution model, or cryptographic-security claim.  It
imports K3-B canonically and reaches K1/K2 only through it.  K3-C is absent.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass, replace
from enum import Enum
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Callable, Mapping, Sequence


_K3_NAME = "_zkc_k3_dependent_surfaces"
_K3_PATH = (
    Path(__file__).resolve().parents[1] / "k3-dependent-surfaces" / "reference_model.py"
)
if _K3_NAME in sys.modules:
    k3 = sys.modules[_K3_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K3_NAME, _K3_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host fault
        raise ImportError(f"cannot load K3-B from {_K3_PATH}")
    k3 = importlib.util.module_from_spec(_spec)
    sys.modules[_K3_NAME] = k3
    _spec.loader.exec_module(k3)
k2 = k3.k2
k1 = k3.k1


def _profile_catalog(kind: str, *declarations: str) -> object:
    return k1.DatumSeq(
        (
            k1.DatumRecord(
                (
                    (0, k1.Symbol(kind)),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(k1.Symbol(item) for item in declarations)
                        ),
                    ),
                )
            ),
        )
    )


def _profile_imports(*profiles: object) -> tuple[object, ...]:
    return tuple(
        sorted(
            (profile.identity for profile in profiles),
            key=lambda identifier: identifier.internal_reference(),
        )
    )


@dataclass(frozen=True)
class K3DSemanticProfiles:
    endpoint_graph: object
    source_view: object
    projection: object
    k3b_profiles: object = field(compare=False, repr=False)

    def __post_init__(self) -> None:
        profiles = (
            self.endpoint_graph,
            self.source_view,
            self.projection,
        )
        if any(type(item) is not k1.SemanticLanguageProfile for item in profiles):
            raise TypeError("K3-D semantic profiles have the wrong exact shape")
        if self.endpoint_graph.profile_imports != _profile_imports(
            self.k3b_profiles.interface_plan
        ):
            raise ValueError("the endpoint-graph profile must import Interface/Plan")
        if self.source_view.profile_imports != _profile_imports(self.endpoint_graph):
            raise ValueError("the source-view profile must import the endpoint graph")
        if self.projection.profile_imports != _profile_imports(self.source_view):
            raise ValueError("the projection profile must import the source view")

    @property
    def endpoint_graph_bundle(self) -> dict[object, object]:
        upstream = k3.k3b_root_profile_preimages(self.k3b_profiles)[
            self.k3b_profiles.interface_plan.identity
        ]
        return {**upstream, self.endpoint_graph.identity: self.endpoint_graph}

    @property
    def source_view_bundle(self) -> dict[object, object]:
        return {**self.endpoint_graph_bundle, self.source_view.identity: self.source_view}

    @property
    def projection_bundle(self) -> dict[object, object]:
        return {**self.source_view_bundle, self.projection.identity: self.projection}

    @property
    def bundle(self) -> dict[object, object]:
        return self.projection_bundle


def make_k3d_semantic_profiles(
    *,
    k3b_profiles: object = None,
    endpoint_graph_law: bytes = b"zkc-k3d-endpoint-graph-law-v0",
    source_view_law: bytes = b"zkc-k3d-pir-source-view-law-v0",
    projection_law: bytes = b"zkc-k3d-source-relative-projection-law-v0",
) -> K3DSemanticProfiles:
    upstream = (
        k3.K3B_SEMANTIC_PROFILES if k3b_profiles is None else k3b_profiles
    )
    endpoint_graph = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.oir.endpoint-graph"),
        0,
        _profile_imports(upstream.interface_plan),
        (k1.Symbol("oir.endpoint"),),
        _profile_catalog("oir.endpoint-declaration", "endpoint-graph-body-v0"),
        endpoint_graph_law,
    )
    source_view = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.endpoint-source-view"),
        0,
        _profile_imports(endpoint_graph),
        tuple(
            k1.Symbol(item)
            for item in sorted(
                (
                    "pir.endpoint-owner-schema-set",
                    "pir.endpoint-owner-adapter-consumer",
                    "pir.endpoint-owner-adapter-purpose",
                    "pir.endpoint-owner-supplement",
                    "pir.endpoint-owner-supplement-authority-binding",
                    "pir.endpoint-owner-supplement-binding-payload",
                    "pir.endpoint-owner-supplement-no-policy",
                    "pir.endpoint-owner-supplement-policy-closure",
                    "pir.endpoint-owner-supplement-requirement",
                    "pir.endpoint-read-manifest",
                    "pir.endpoint-source-view",
                )
            )
        ),
        _profile_catalog(
            "pir.endpoint-source-declaration",
            "owner-schema-set-body-v0",
            "owner-supplement-body-v0",
            "owner-supplement-authority-v0",
            "read-manifest-body-v0",
            "source-view-body-v0",
        ),
        source_view_law,
    )
    projection = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.oir.endpoint-projection"),
        0,
        _profile_imports(source_view),
        (k1.Symbol("oir.projection-proposition"),),
        _profile_catalog(
            "oir.projection-declaration",
            "source-relative-exact-graph-equality-v0",
        ),
        projection_law,
    )
    return K3DSemanticProfiles(
        endpoint_graph,
        source_view,
        projection,
        upstream,
    )


K3D_SEMANTIC_PROFILES = make_k3d_semantic_profiles()
K3D_PROFILE_BUNDLE = K3D_SEMANTIC_PROFILES.bundle
SOURCE_PROFILE = K3D_SEMANTIC_PROFILES.source_view.identity
OIR_PROFILE = K3D_SEMANTIC_PROFILES.endpoint_graph.identity
RELATION_PROFILE = K3D_SEMANTIC_PROFILES.projection.identity
CHECKER_BASIS_LABEL = "k3d.exact-equality-checker.v0"
ENDPOINT_CONTRACT_LAW = "EndpointContractLawV0"
MAX_GRAPH_ITEMS = 1 << 14
MAX_WORK = 1 << 17


class OutcomeKind(str, Enum):
    AFFIRMATIVE = "affirmative"
    NEGATIVE = "negative"
    UNSUPPORTED = "unsupported"
    MISSING_DEPENDENCY = "missing-dependency"
    KIND_MISMATCH = "kind-mismatch"
    MALFORMED = "malformed"
    REFUSED = "refused"
    DETERMINISTIC_LIMIT_EXCEEDED = "deterministic-limit-exceeded"
    CHECKER_FAILURE = "checker-failure"


@dataclass(frozen=True)
class Mismatch:
    code: str
    path: str
    expected: str = ""
    observed: str = ""


@dataclass(frozen=True)
class Answer:
    kind: OutcomeKind
    value: object | None = None
    reason: str = ""
    mismatches: tuple[Mismatch, ...] = ()
    unsupported_reasons: tuple[SupportReason, ...] = ()


def _answer(
    kind: OutcomeKind,
    value: object | None = None,
    reason: str = "",
    mismatches: Sequence[Mismatch] = (),
    unsupported_reasons: Sequence[SupportReason] = (),
) -> Answer:
    return Answer(
        kind,
        value,
        reason,
        tuple(mismatches),
        tuple(unsupported_reasons),
    )


class EndpointRole(str, Enum):
    VERIFIER = "verifier"
    PROVER = "prover"


class ProjectionPurpose(str, Enum):
    FS_VERIFIER = "fs-verifier-endpoint"
    FS_PLAN_PROVER = "fs-plan-specialized-prover-endpoint"


class SupportReason(str, Enum):
    FRESH_ENDPOINT = "fresh-endpoint"
    GENERIC_PROVER_ENDPOINT = "generic-prover-endpoint"
    STANDARD_ORACLE_ENDPOINT = "standard-oracle-endpoint"
    MODULE_EFFECT_ENDPOINT = "module-effect-endpoint"


class DependencyKind(str, Enum):
    CORE = "interactive-core"
    CONSTRUCTION = "transcript-construction"
    ALGORITHM = "portable-algorithm"
    EVALUATION = "evaluation-contract"
    CODEC_LAW = "interface-codec-law"


class InvocationClass(str, Enum):
    PUBLIC = "public"
    VERIFIER_PRIVATE = "verifier-private"


class CodecKind(str, Enum):
    IDENTITY = "identity"
    RECORD = "record"
    VARIANT = "variant"
    BOUNDED_SEQUENCE = "bounded-sequence"
    GENERAL = "general"


class StatementFlowKind(str, Enum):
    SUPPLIES_INVOCATION = "supplies-invocation"
    EXPOSES_OPENED_BINDING = "exposes-opened-binding"


class TransportActor(str, Enum):
    PROVER = "prover"
    VERIFIER = "verifier"
    PUBLIC_DERIVATION = "public-derivation"


class TransportDestination(str, Enum):
    PROVER = "prover"
    VERIFIER = "verifier"
    EXTERNAL_APPLICATION = "external-application"


class PresenceKind(str, Enum):
    ALWAYS = "always"
    ACTIVITY_OF = "activity-of"


class CompletionTargetKind(str, Enum):
    CORE_TERMINAL = "core-terminal"
    FS_FAILURE = "fiat-shamir-failure"


class CompletionCoordinateKind(str, Enum):
    TERMINAL_OUTPUT = "terminal-public-output"
    FS_FAILURE_PAYLOAD = "fs-failure-domain-payload"
    FS_FAILURE_CHALLENGE = "fs-failure-challenge"
    FS_FAILURE_PREFIX_COUNT = "fs-failure-prefix-count"
    FS_FAILURE_PREFIX_STATE = "fs-failure-prefix-state"
    FS_FAILURE_DRAWS = "fs-failure-draws"
    FS_FAILURE_FINAL_STATE = "fs-failure-final-state"


class ValueRefKind(str, Enum):
    INVOCATION = "invocation-target"
    CONSTANT = "constant"
    PURE_NODE = "pure-node"
    OCCURRENCE_OUTPUT = "occurrence-output"


class EndpointValueAccessRouteKind(str, Enum):
    INVOCATION_DECODE = "invocation-decode"
    CONSTANT = "constant"
    PURE_EVAL = "pure-eval"
    PLAN_MOVE = "plan-move"
    LOCAL_VERIFIER_MESSAGE = "local-verifier-message"
    LOCAL_CHECK = "local-check"
    CHALLENGE_INTERPRET = "challenge-interpret"
    INBOUND_TRANSPORT = "inbound-transport"
    RECONSTRUCT_VERIFIER_MESSAGE = "reconstruct-verifier-message"
    RECONSTRUCT_CHECK = "reconstruct-check"


class SpineEventKind(str, Enum):
    FS_INITIALIZATION = "fs-initialization"
    SCOPE_OPENING = "scope-opening"
    PUBLIC_BINDING = "public-binding"
    CORE_OCCURRENCE = "core-occurrence"


class SpineOwner(str, Enum):
    LOCAL = "local"
    COUNTERPARTY = "counterparty"
    LOCAL_PUBLIC_DERIVATION = "local-public-derivation"


class SemanticOccurrenceKind(str, Enum):
    PROVER_MESSAGE = "prover-message"
    VERIFIER_MESSAGE = "verifier-message"
    CHALLENGE = "challenge"
    CHECK = "check"
    REDUCTION = "reduction"
    TERMINAL = "terminal"


class StaticObligationKind(str, Enum):
    SLOT_INGRESS = "slot-ingress"
    PLAN_DECISION = "plan-decision"
    K2_FRAME = "k2-frame"
    LOCAL_OCCURRENCE = "local-occurrence"
    CHALLENGE_INTERPRET = "challenge-interpret"
    PRESENTATION = "presentation"


class CodecDirection(str, Enum):
    ENCODE = "encode"
    DECODE = "decode"


class PresentationKind(str, Enum):
    EXTERNAL_SUPPLY = "external-supply"
    STATEMENT = "statement"
    TRANSPORT = "transport"
    COMPLETION_TAG = "completion-tag"
    COMPLETION_PAYLOAD = "completion-payload"


class ClaimUsage(str, Enum):
    LINEAR = "linear"
    REUSABLE = "reusable"


class ClaimSourceKind(str, Enum):
    BINDING = "binding"
    REDUCTION_OUTPUT = "reduction-output"


class AnchorKind(str, Enum):
    REDUCTION = "reduction-application"
    TERMINAL = "terminal-claim-closure"


class ClaimDisposition(str, Enum):
    CONSUME = "consume"
    DISCHARGE = "discharge"


class RequirementFamily(str, Enum):
    LOCAL_EVALUATOR = "local-portable-evaluator"
    COUNTERPARTY = "counterparty-contract"
    PRIVATE_MATERIAL_INGRESS = "private-material-ingress"
    PRIVATE_RANDOMNESS_INGRESS = "private-randomness-ingress"
    STATE_STORAGE = "state-storage"


class CompletionInterfaceKind(str, Enum):
    VERIFIER_COMPLETIONS = "verifier-completions"
    NO_SOURCE_SEMANTIC_COMPLETION = "no-source-semantic-completion"


class PlanOperandKind(str, Enum):
    VIEW_PUBLIC_INPUT = "view-public-input"
    VIEW_OCCURRENCE = "view-occurrence"
    PRIVATE_MATERIAL = "private-material"
    PRIVATE_RANDOMNESS = "private-randomness"
    STATE_BEFORE = "state-before"
    CONSTANT = "constant"
    NODE_OUTPUT = "node-output"


class PlanMoveKind(str, Enum):
    MESSAGE_VALUE = "message-value"
    ORACLE_VALUE = "oracle-value"
    MODULE_MOVE = "module-move"


class PlanUpdateKind(str, Enum):
    KEEP = "keep"
    REPLACE = "replace"


class FieldDispositionKind(str, Enum):
    RELEVANT = "projection-relevant"
    JOIN_ONLY = "source-join-only"
    INERT = "inert-for-purpose"
    UNSUPPORTED = "unsupported-by-k3d"


class ViewSink(str, Enum):
    DEPENDENCY = "dependency"
    TYPE = "type"
    CONSTANT = "constant"
    PURE_NODE = "pure-node"
    ABI = "abi"
    SPINE = "spine"
    STATIC_FS = "static-fs"
    CLAIM = "claim"
    ANCHOR = "anchor"
    PLAN = "plan"


@dataclass(frozen=True)
class Dependency:
    kind: DependencyKind
    subject_kind: str
    exact_id: str


@dataclass(frozen=True)
class ValueTypeAtom:
    canonical_body: str


@dataclass(frozen=True)
class GraphValueRef:
    kind: ValueRefKind
    ref: int
    output_ordinal: int = 0


@dataclass(frozen=True)
class EndpointValueAccessRoute:
    kind: EndpointValueAccessRouteKind
    owner_ref: int
    secondary_ref: int | None = None


@dataclass(frozen=True)
class EndpointValueAccess:
    value: GraphValueRef
    route: EndpointValueAccessRoute


@dataclass(frozen=True)
class ConstantNode:
    type_ref: int
    value: object


@dataclass(frozen=True)
class PureNode:
    algorithm_dependency: int
    evaluation_dependency: int
    inputs: tuple[GraphValueRef, ...]
    result_type_ref: int


@dataclass(frozen=True)
class CodecNode:
    kind: CodecKind
    value_type_ref: int | None = None
    external_type_ref: int | None = None
    semantic_type_ref: int | None = None
    children: tuple[tuple[int, int], ...] = ()
    general_law_dependency: int | None = None
    interface_codec_id: object | None = None


@dataclass(frozen=True)
class AbiSlot:
    external_key: str
    codec_ref: int


@dataclass(frozen=True)
class InvocationTarget:
    invocation_class: InvocationClass
    type_ref: int


@dataclass(frozen=True)
class InvocationFibre:
    slot_ref: int
    target_refs: tuple[int, ...]


@dataclass(frozen=True)
class StatementAlias:
    slot_ref: int
    binding_spine_ref: int
    flow: StatementFlowKind
    invocation_target_ref: int | None
    external_statement: str = ""


@dataclass(frozen=True)
class TransportEdge:
    target_spine_ref: int
    source: TransportActor
    destination: TransportDestination
    slot_ref: int


@dataclass(frozen=True)
class CompletionCoordinate:
    kind: CompletionCoordinateKind
    terminal_spine_ref: int | None = None
    output_ordinal: int | None = None


@dataclass(frozen=True)
class CompletionVariant:
    target: CompletionTargetKind
    terminal_spine_ref: int | None
    external_tag: str
    payload_bindings: tuple[tuple[CompletionCoordinate, int], ...]


@dataclass(frozen=True)
class RoleAbiGraph:
    codec_nodes: tuple[CodecNode, ...]
    slots: tuple[AbiSlot, ...]
    invocation_targets: tuple[InvocationTarget, ...]
    invocation_fibres: tuple[InvocationFibre, ...]
    statement_aliases: tuple[StatementAlias, ...]
    transport_edges: tuple[TransportEdge, ...]
    completion_variants: tuple[CompletionVariant, ...]


@dataclass(frozen=True)
class Activity:
    algorithm_dependency: int | None = None
    evaluation_dependency: int | None = None
    inputs: tuple[GraphValueRef, ...] = ()


@dataclass(frozen=True)
class ProverMessageAction:
    channel_ref: str
    value_type_ref: int


@dataclass(frozen=True)
class VerifierMessageAction:
    channel_ref: str
    algorithm_dependency: int
    evaluation_dependency: int
    inputs: tuple[GraphValueRef, ...]
    result_type_ref: int


@dataclass(frozen=True)
class ChallengeAction:
    challenge_law_ref: int


@dataclass(frozen=True)
class CheckAction:
    algorithm_dependency: int
    evaluation_dependency: int
    inputs: tuple[GraphValueRef, ...]
    result_type_ref: int


@dataclass(frozen=True)
class ReductionAction:
    pass


@dataclass(frozen=True)
class TerminalAction:
    pass


SpineAction = (
    ProverMessageAction
    | VerifierMessageAction
    | ChallengeAction
    | CheckAction
    | ReductionAction
    | TerminalAction
)


@dataclass(frozen=True)
class SpineEvent:
    kind: SpineEventKind
    scope_event_ref: int | None = None
    parent_scope_event_ref: int | None = None
    original_scope_path: tuple[int, ...] = ()
    original_binding_ordinal: int | None = None
    binding_class: str = ""
    binding_value: GraphValueRef | None = None
    original_occurrence_ordinal: int | None = None
    opens_before_occurrence_ordinal: int | None = None
    activity: Activity = Activity()
    action: SpineAction | None = None


@dataclass(frozen=True)
class FrameRecipe:
    family: str
    core_dependency: int | None = None
    construction_dependency: int | None = None
    application_domain: bytes | None = None
    original_scope_path: tuple[int, ...] = ()
    original_binding_ordinal: int | None = None
    original_occurrence_ordinal: int | None = None
    original_challenge_ordinal: int | None = None
    challenge_input_ordinal: int | None = None
    activity_spine_ref: int | None = None
    type_ref: int | None = None
    value: GraphValueRef | None = None
    binding_class: str = ""


@dataclass(frozen=True)
class NamespaceRecipe:
    construction_dependency: int
    core_dependency: int
    original_scope_path: tuple[int, ...]
    original_challenge_ordinal: int
    domain_ref: str
    value_type_ref: int
    correlation: str


@dataclass(frozen=True)
class ChallengeLaw:
    original_challenge_ordinal: int
    value_type_ref: int
    domain_ref: str
    fresh_law_ref: str
    correlation: str
    reduction_use: str
    conditions: tuple[GraphValueRef, ...]
    draw_bytes: int
    maximum_draws: int
    accept_algorithm_dependency: int
    accept_evaluation_dependency: int
    decode_algorithm_dependency: int
    decode_evaluation_dependency: int


@dataclass(frozen=True)
class StaticFsSemantics:
    core_dependency: int
    construction_dependency: int
    state_type_ref: int
    bytes_type_ref: int
    natural_type_ref: int
    initial_state: bytes
    absorb_algorithm_dependency: int
    absorb_evaluation_dependency: int
    squeeze_algorithm_dependency: int
    squeeze_evaluation_dependency: int
    advance_algorithm_dependency: int
    advance_evaluation_dependency: int
    application_domain: bytes
    sampling_exhausted_failure: str
    derived_prefix_law: str
    challenge_transition_law: str
    challenge_laws: tuple[ChallengeLaw, ...]


@dataclass(frozen=True)
class ClaimAtom:
    contract_ref: str
    usage: ClaimUsage
    scope_event_ref: int
    source_kind: ClaimSourceKind
    source_ref: int
    output_ordinal: int | None = None


@dataclass(frozen=True)
class ReductionPublication:
    publication_spine_ref: int
    next_challenge_law_ref: int | None


@dataclass(frozen=True)
class ReductionOutputRow:
    output_ordinal: int
    contract_ref: str
    claim_refs: tuple[int, ...]


@dataclass(frozen=True)
class AnchoredObligation:
    kind: AnchorKind
    contract_ref: str | None
    scope_event_ref: int | None
    apply_spine_ref: int | None
    input_claim_refs: tuple[int, ...]
    side_inputs: tuple[GraphValueRef, ...]
    required_challenge_law_refs: tuple[int, ...]
    publications: tuple[ReductionPublication, ...]
    output_claims: tuple[ReductionOutputRow, ...]
    terminal_spine_ref: int | None
    verdict: str | None
    public_outputs: tuple[GraphValueRef, ...]
    required_check_spine_refs: tuple[int, ...]
    claim_dispositions: tuple[tuple[int, ClaimDisposition], ...]


@dataclass(frozen=True)
class PlanValueRef:
    kind: PlanOperandKind
    ref: int
    value_type_ref: int
    literal: object | None = None


@dataclass(frozen=True)
class PlanPrivateMaterial:
    kind: str
    type_ref: int


@dataclass(frozen=True)
class PlanRandomness:
    type_ref: int
    first_available_decision_ref: int


@dataclass(frozen=True)
class PlanState:
    type_ref: int
    initial: PlanValueRef


@dataclass(frozen=True)
class PlanRecipeNode:
    decision_ref: int
    algorithm_dependency: int
    evaluation_dependency: int
    inputs: tuple[PlanValueRef, ...]
    result_type_ref: int


@dataclass(frozen=True)
class PlanMove:
    decision_ref: int
    kind: PlanMoveKind
    value: PlanValueRef


@dataclass(frozen=True)
class PlanUpdate:
    decision_ref: int
    state_ref: int
    kind: PlanUpdateKind
    value: PlanValueRef | None


@dataclass(frozen=True)
class PlanGraph:
    private_material: tuple[PlanPrivateMaterial, ...]
    randomness: tuple[PlanRandomness, ...]
    state: tuple[PlanState, ...]
    recipe_nodes: tuple[PlanRecipeNode, ...]
    moves: tuple[PlanMove, ...]
    updates: tuple[PlanUpdate, ...]


@dataclass(frozen=True)
class EndpointSemanticGraph:
    role: EndpointRole
    exact_used_dependencies: tuple[Dependency, ...]
    value_types: tuple[ValueTypeAtom, ...]
    constants: tuple[ConstantNode, ...]
    pure_nodes: tuple[PureNode, ...]
    role_abi_graph: RoleAbiGraph
    endpoint_spine: tuple[SpineEvent, ...]
    static_fs_semantics: StaticFsSemantics
    claims: tuple[ClaimAtom, ...]
    anchored_obligations: tuple[AnchoredObligation, ...]
    optional_plan_graph: PlanGraph | None


@dataclass(frozen=True)
class EndpointStaticObligation:
    """One law-referential static obligation, never a runtime trace entry."""

    kind: StaticObligationKind
    owner_ref: int | None = None
    secondary_ref: int | None = None
    frame_recipe: FrameRecipe | None = None
    codec_direction: CodecDirection | None = None
    presentation_kind: PresentationKind | None = None


@dataclass(frozen=True)
class DerivedRequirement:
    family: RequirementFamily
    use_site: str
    spine_event_ref: int | None = None
    counterparty: EndpointRole | None = None
    role_abi_edge_ref: int | None = None
    algorithm_dependency: int | None = None
    evaluation_dependency: int | None = None
    plan_ref: int | None = None
    kind: str | None = None
    type_ref: int | None = None
    first_available_decision_spine_ref: int | None = None
    initializer: PlanValueRef | None = None
    updates: tuple[PlanUpdate, ...] = ()


@dataclass(frozen=True)
class DerivedCompletionInterface:
    kind: CompletionInterfaceKind
    completion_variant_refs: tuple[int, ...]


@dataclass(frozen=True)
class DerivedEndpointContract:
    static_obligations: tuple[EndpointStaticObligation, ...]
    requirements: tuple[DerivedRequirement, ...]
    completion_interface: DerivedCompletionInterface


@dataclass(frozen=True)
class EndpointSourceView:
    profile: object
    purpose: ProjectionPurpose
    semantic_graph: EndpointSemanticGraph


@dataclass(frozen=True)
class OirEndpoint:
    semantic_profile: object
    semantic_graph: EndpointSemanticGraph
    asserted_id: object


# Explicit future-owner fixture carriers.  ``*_key`` fields are private
# construction coordinates; only their semantic payload and dense rebase enter
# the endpoint graph.


@dataclass(frozen=True)
class OwnerCodec:
    codec_key: str
    kind: CodecKind
    value_type: object | None = None
    external_type: object | None = None
    semantic_type: object | None = None
    children: tuple[tuple[int, str], ...] = ()
    general_law_id: object | None = None
    interface_codec_id: object | None = None


@dataclass(frozen=True)
class OwnerSlot:
    slot_key: str
    external_key: str
    codec_key: str


@dataclass(frozen=True)
class OwnerInvocationFibre:
    slot_key: str
    invocation_inputs: tuple[str, ...]


@dataclass(frozen=True)
class OwnerStatementAlias:
    slot_key: str
    binding_input: str
    flow: StatementFlowKind
    invocation_input: str | None
    external_statement: str = ""


@dataclass(frozen=True)
class OwnerTransport:
    occurrence: str
    source: TransportActor
    destination: TransportDestination
    slot_key: str


@dataclass(frozen=True)
class OwnerCompletionBinding:
    coordinate: CompletionCoordinateKind
    slot_key: str
    output_ordinal: int | None = None


@dataclass(frozen=True)
class OwnerCompletion:
    target: CompletionTargetKind
    terminal_occurrence: str | None
    external_tag: str
    bindings: tuple[OwnerCompletionBinding, ...]


@dataclass(frozen=True)
class OwnerInterfaceSurface:
    codecs: tuple[OwnerCodec, ...]
    slots: tuple[OwnerSlot, ...]
    invocation_fibres: tuple[OwnerInvocationFibre, ...]
    statement_aliases: tuple[OwnerStatementAlias, ...]
    transports: tuple[OwnerTransport, ...]
    completions: tuple[OwnerCompletion, ...]


@dataclass(frozen=True)
class OwnerClaim:
    claim_key: str
    contract_ref: str
    usage: ClaimUsage
    scope: str
    source_kind: ClaimSourceKind
    source_name: str
    output_ordinal: int | None = None


@dataclass(frozen=True)
class OwnerReduction:
    reduction_name: str
    contract_ref: str
    output_contracts: tuple[str, ...]


@dataclass(frozen=True)
class OwnerTerminal:
    terminal_occurrence: str
    verdict: str
    public_outputs: tuple[object, ...]
    required_checks: tuple[str, ...]
    claim_dispositions: tuple[tuple[str, ClaimDisposition], ...]


@dataclass(frozen=True)
class OwnerCoreSurface:
    claims: tuple[OwnerClaim, ...]
    reductions: tuple[OwnerReduction, ...]
    terminal: OwnerTerminal


@dataclass(frozen=True)
class OwnerChallengeSemantics:
    occurrence: str
    domain_ref: str
    fresh_law_ref: str
    correlation: str
    reduction_use: str
    accept_algorithm_id: object
    accept_evaluation_id: object
    decode_algorithm_id: object
    decode_evaluation_id: object


@dataclass(frozen=True)
class OwnerFsSurface:
    state_type: object
    bytes_type: object
    natural_type: object
    initial_state: bytes
    absorb_algorithm_id: object
    absorb_evaluation_id: object
    squeeze_algorithm_id: object
    squeeze_evaluation_id: object
    advance_algorithm_id: object
    advance_evaluation_id: object
    sampling_exhausted_failure: str
    challenges: tuple[OwnerChallengeSemantics, ...]


@dataclass(frozen=True)
class OwnerPlanOperand:
    kind: PlanOperandKind
    name: str = ""
    node_ordinal: int | None = None
    literal_type: object | None = None
    literal: object | None = None


@dataclass(frozen=True)
class OwnerPlanRecipeNode:
    algorithm_id: object
    evaluation_id: object
    inputs: tuple[OwnerPlanOperand, ...]
    output_type: object


@dataclass(frozen=True)
class OwnerPlanRecipe:
    decision: str
    nodes: tuple[OwnerPlanRecipeNode, ...]
    move_kind: PlanMoveKind
    move: OwnerPlanOperand
    state_after: tuple[tuple[str, PlanUpdateKind, OwnerPlanOperand | None], ...]


@dataclass(frozen=True)
class OwnerPlanSurface:
    recipes: tuple[OwnerPlanRecipe, ...]
    derived_exports: tuple[tuple[str, str, OwnerPlanOperand, object], ...] = ()
    has_module_recipe: bool = False


@dataclass(frozen=True)
class FutureOwnerSurface:
    """Future-only facts admitted under the bounded K3-D supplement law.

    This inert carrier is not authority.  Projection may consume it only
    through an ``IssuedFutureOwnerSupplement`` minted by the owner-side
    admission boundary and then joined to live K2/K3-B owner views.
    """

    core: OwnerCoreSurface
    fs: OwnerFsSurface
    interface: OwnerInterfaceSurface
    plan: OwnerPlanSurface | None


FutureOwnerSupplement = FutureOwnerSurface


_FUTURE_OWNER_SUPPLEMENT_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class FutureOwnerSupplementCapability:
    supplement_id: object
    authority_binding: object
    consumer_id: object
    purpose_id: object
    purpose: ProjectionPurpose
    source_fingerprint: bytes
    supplement: FutureOwnerSurface
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER:
            raise ValueError("only the bounded future owner may mint a capability")

    def __copy__(self) -> "FutureOwnerSupplementCapability":
        raise ValueError("live supplement capabilities cannot be copied")

    def __deepcopy__(self, _memo: object) -> "FutureOwnerSupplementCapability":
        raise ValueError("live supplement capabilities cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live supplement capabilities cannot be serialized")


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class IssuedFutureOwnerSupplement:
    supplement_id: object
    authority_binding: object
    authority_binding_id: object
    purpose: ProjectionPurpose
    source_fingerprint: bytes
    supplement: FutureOwnerSurface
    capability: FutureOwnerSupplementCapability
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER:
            raise ValueError("only the bounded future owner may issue a supplement")

    def __repr__(self) -> str:
        return "IssuedFutureOwnerSupplement(<live>)"

    def __copy__(self) -> "IssuedFutureOwnerSupplement":
        raise ValueError("live supplement authority cannot be copied")

    def __deepcopy__(self, _memo: object) -> "IssuedFutureOwnerSupplement":
        raise ValueError("live supplement authority cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live supplement authority cannot be serialized")


_PROVISIONAL_SUPPLEMENT_CAPABILITIES: dict[
    int, FutureOwnerSupplementCapability
] = {}
_PROVISIONAL_SUPPLEMENT_AUTHORITIES: dict[int, IssuedFutureOwnerSupplement] = {}
_LIVE_SUPPLEMENT_CAPABILITIES: dict[int, FutureOwnerSupplementCapability] = {}
_LIVE_SUPPLEMENT_AUTHORITIES: dict[int, IssuedFutureOwnerSupplement] = {}


@dataclass(frozen=True)
class ProjectionRequest:
    core: object
    construction: object | None
    interpretation: object
    interface: object
    role: EndpointRole
    plan: object | None
    future_owner: FutureOwnerSurface | None
    provenance: str = "k3d:p01"
    source_label: str = "source"
    runtime_receipt: object | None = None
    admitted_module_effect: bool = False
    supplement_authority: IssuedFutureOwnerSupplement | None = None


FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS = (
    "core.claims[*].contract_ref/usage/source-law",
    "core.reductions[*].contract_ref/output_contracts",
    "core.terminal.verdict/public_outputs",
    "fs.state-and-scalar-types",
    "fs.absorb/squeeze/advance-algorithm-and-evaluation",
    "fs.challenges[*].domain/fresh/correlation/reduction/evaluator-laws",
    "interface.codecs[*].shape/type-tree/general-law",
    "interface.invocation_fibres",
    "interface.public-derivation-transports",
    "interface.completions",
    "plan.recipes[*].evaluation-and-multi-node-graph",
    "plan.derived_exports[*].value-expression",
)


@dataclass(frozen=True)
class OwnerFieldDisposition:
    path: str
    verifier_kind: FieldDispositionKind
    verifier_sinks: tuple[ViewSink, ...]
    prover_kind: FieldDispositionKind
    prover_sinks: tuple[ViewSink, ...]


def _stable(value: object) -> object:
    if type(value) is k1.TypedContentId:
        return {
            "kind": value.subject_kind,
            "regime": _stable(value.semantic_regime),
            "id": value.internal_reference().hex(),
        }
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, bytes):
        return {"bytes": value.hex()}
    if is_dataclass(value):
        return {
            item.name: _stable(getattr(value, item.name))
            for item in fields(value)
            if not item.name.startswith("_issuer") and item.name != "asserted_id"
        }
    if isinstance(value, (tuple, list)):
        return [_stable(item) for item in value]
    if isinstance(value, Mapping):
        return {
            str(key): _stable(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if value is None or type(value) in {str, int, bool}:
        return value
    raise TypeError(f"unsupported canonical payload {type(value).__name__}")


def canonical_bytes(value: object) -> bytes:
    return json.dumps(
        _stable(value), sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _semantic_id(subject_kind: str, value: object) -> object:
    profile_by_kind = {
        "pir.endpoint-owner-schema-set": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-adapter-consumer": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-adapter-purpose": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-supplement": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-supplement-binding-payload": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-supplement-no-policy": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-supplement-policy-closure": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-owner-supplement-requirement": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-read-manifest": K3D_SEMANTIC_PROFILES.source_view,
        "pir.endpoint-source-view": K3D_SEMANTIC_PROFILES.source_view,
        "oir.endpoint": K3D_SEMANTIC_PROFILES.endpoint_graph,
        "oir.projection-proposition": K3D_SEMANTIC_PROFILES.projection,
    }
    try:
        profile = profile_by_kind[subject_kind]
    except KeyError as error:
        raise TypeError(f"K3-D subject kind {subject_kind!r} has no language profile") from error
    identifier = k1.profiled_content_id(
        subject_kind,
        profile.identity,
        k1.BytesValue(canonical_bytes(value)),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    profile_bundle = {
        K3D_SEMANTIC_PROFILES.endpoint_graph.identity: (
            K3D_SEMANTIC_PROFILES.endpoint_graph_bundle
        ),
        K3D_SEMANTIC_PROFILES.source_view.identity: (
            K3D_SEMANTIC_PROFILES.source_view_bundle
        ),
        K3D_SEMANTIC_PROFILES.projection.identity: (
            K3D_SEMANTIC_PROFILES.projection_bundle
        ),
    }[profile.identity]
    k1.authenticate_profiled_semantic_content(
        identifier,
        profile.identity,
        k1.BytesValue(canonical_bytes(value)),
        profile_bundle,
        supported_profiles=(profile.identity,),
    )
    return identifier


# This is an evaluator coordinate, not a profiled semantic subject or
# transferable authority.  The selected projection relation profile owns the
# operation law that interprets it.
CHECKER_BASIS = CHECKER_BASIS_LABEL


def _id_text(value: object, expected_kind: str | None = None) -> str:
    if type(value) is not k1.TypedContentId:
        raise TypeError("dependency is not an exact K1 TypedContentId")
    value.__post_init__()
    if expected_kind is not None and value.subject_kind != expected_kind:
        raise TypeError(f"expected {expected_kind}, got {value.subject_kind}")
    if value.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise TypeError("dependency uses another semantic regime")
    return value.internal_reference().hex()


def _type_body(value_type: object) -> str:
    if type(value_type) is not k1.ValueType:
        raise TypeError("expected exact K1 ValueType")
    return k1.encode_datum(k1.value_type_datum(value_type)).hex()


def _fixed_ref(subject_kind: str, label: str) -> object:
    return k1.content_id(
        subject_kind,
        k1.encode_datum(
            k1.DatumRecord(((0, k1.Symbol(f"k3d:{label}")),))
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _algorithm(label: str) -> object:
    return _fixed_ref("foundation.canonical-algorithm", label)


def _evaluation(label: str) -> object:
    return _fixed_ref("foundation.evaluation-contract", label)


def _purpose(role: EndpointRole) -> ProjectionPurpose:
    return (
        ProjectionPurpose.FS_VERIFIER
        if role is EndpointRole.VERIFIER
        else ProjectionPurpose.FS_PLAN_PROVER
    )


def _other_role(role: EndpointRole) -> EndpointRole:
    return (
        EndpointRole.PROVER if role is EndpointRole.VERIFIER else EndpointRole.VERIFIER
    )


def _sort_type(sort: object) -> object:
    return k3.value_type_for_sort(sort)


def _value_ref_owner_type(core: object, ref: object) -> object:
    if ref.kind is k2.RefKind.INPUT:
        item = next(item for item in core.inputs if item.name == ref.name)
        return _sort_type(item.value_sort)
    item = next(item for item in core.schedule if item.name == ref.name)
    return _occurrence_type(core, item)


def _occurrence_type(core: object, occurrence: object) -> object:
    if occurrence.kind is k2.OccurrenceKind.PROVER_MESSAGE:
        return _sort_type(occurrence.prover_value_sort)
    if occurrence.kind is k2.OccurrenceKind.VERIFIER_MESSAGE:
        assert occurrence.verifier_rule is not None
        if occurrence.verifier_rule.kind is k2.VerifierRuleKind.COPY:
            return _value_ref_owner_type(core, occurrence.dependencies[0])
        if occurrence.verifier_rule.kind is k2.VerifierRuleKind.SHA256:
            return k3.BYTES
        return k3.NAT
    if occurrence.kind is k2.OccurrenceKind.CHALLENGE:
        return k3.NAT
    return k3.BOOL


def _scope_path(core: object, scope_name: str) -> tuple[int, ...]:
    by_name = {item.name: item for item in core.scopes}
    indexes = {item.name: index for index, item in enumerate(core.scopes)}
    path: list[int] = []
    current: str | None = scope_name
    while current is not None:
        path.append(indexes[current])
        current = by_name[current].parent
    return tuple(reversed(path))


def _dedupe_sorted_dependencies(rows: Sequence[Dependency]) -> tuple[Dependency, ...]:
    unique = {canonical_bytes(row): row for row in rows}
    return tuple(unique[key] for key in sorted(unique))


def _dedupe_sorted_types(rows: Sequence[object]) -> tuple[ValueTypeAtom, ...]:
    return tuple(
        ValueTypeAtom(item) for item in sorted({_type_body(value) for value in rows})
    )


def _dep_index(
    rows: Sequence[Dependency], exact_id: object, kind: DependencyKind
) -> int:
    exact = _id_text(exact_id)
    return next(
        index
        for index, row in enumerate(rows)
        if row.kind is kind and row.exact_id == exact
    )


def _type_index(rows: Sequence[ValueTypeAtom], value_type: object) -> int:
    body = _type_body(value_type)
    return next(index for index, row in enumerate(rows) if row.canonical_body == body)


def _dependency(kind: DependencyKind, value: object) -> Dependency:
    return Dependency(kind, value.subject_kind, _id_text(value))


# ---------------------------------------------------------------------------
# Explicit future-owner contract fixtures
# ---------------------------------------------------------------------------


def _owner_challenge(name: str) -> OwnerChallengeSemantics:
    return OwnerChallengeSemantics(
        name,
        _id_text(_fixed_ref("pir.challenge-domain", f"domain:{name}")),
        _id_text(_fixed_ref("pir.fresh-coin-law", f"fresh:{name}")),
        "independent",
        "proof-critical",
        _algorithm(f"fs-accept:{name}"),
        _evaluation(f"fs-accept:{name}"),
        _algorithm(f"fs-decode:{name}"),
        _evaluation(f"fs-decode:{name}"),
    )


def _owner_fs(core: object, construction: object) -> OwnerFsSurface:
    return OwnerFsSurface(
        k3.BYTES32,
        k3.BYTES,
        k3.NAT,
        k2.INITIAL_TRANSCRIPT_STATE,
        _algorithm("fs-absorb"),
        _evaluation("fs-absorb"),
        _algorithm("fs-squeeze"),
        _evaluation("fs-squeeze"),
        _algorithm("fs-advance"),
        _evaluation("fs-advance"),
        "sampling-exhausted-v0",
        tuple(
            _owner_challenge(item.name)
            for item in core.schedule
            if item.kind is k2.OccurrenceKind.CHALLENGE
        ),
    )


def _codec_for_type(
    value_type: object,
    interface_codec_id: object = None,
) -> OwnerCodec:
    codec_id = k3.IDENTITY_CODEC if interface_codec_id is None else interface_codec_id
    body = _type_body(value_type)
    identity = codec_id == k3.IDENTITY_CODEC
    return OwnerCodec(
        f"interface:{_id_text(codec_id)}:{body}",
        CodecKind.IDENTITY if identity else CodecKind.GENERAL,
        value_type=value_type,
        general_law_id=(
            None
            if identity
            else _fixed_ref(
                "foundation.codec-law",
                f"interface-codec:{_id_text(codec_id)}",
            )
        ),
        interface_codec_id=codec_id,
    )


def _future_interface(
    core: object,
    interface: object | None = None,
    *,
    public_derivations: Sequence[str] = (),
) -> OwnerInterfaceSurface:
    if interface is None:
        interface = k3.default_interface(
            core,
            None,
            k2.ChallengeInterpretation.FRESH,
            expose_all_transports=True,
        )
    input_assignment = {item.core_input: item for item in interface.inputs}
    transport_exposure = {item.occurrence: item for item in interface.transports}

    codec_uses: list[tuple[object, object]] = [
        (_sort_type(item.value_sort), input_assignment[item.name].codec_id)
        for item in core.inputs
    ]
    codec_uses.extend(
        (
            _occurrence_type(core, item),
            transport_exposure[item.name].codec_id,
        )
        for item in core.schedule
        if item.kind
        in {
            k2.OccurrenceKind.PROVER_MESSAGE,
            k2.OccurrenceKind.VERIFIER_MESSAGE,
        }
    )
    codec_uses.extend(
        (item, k3.IDENTITY_CODEC) for item in (k3.BYTES, k3.NAT, k3.BYTES32)
    )
    codecs_by_use = {
        (_type_body(value_type), _id_text(codec_id)): _codec_for_type(
            value_type, codec_id
        )
        for value_type, codec_id in codec_uses
    }
    codecs = tuple(codecs_by_use[key] for key in sorted(codecs_by_use))

    def codec_key(
        value_type: object,
        codec_id: object = k3.IDENTITY_CODEC,
    ) -> str:
        return codecs_by_use[(_type_body(value_type), _id_text(codec_id))].codec_key

    slots: list[OwnerSlot] = []
    fibres: list[OwnerInvocationFibre] = []
    aliases: list[OwnerStatementAlias] = []
    transports: list[OwnerTransport] = []
    for item in core.inputs:
        assignment = input_assignment[item.name]
        key = f"input:{item.name}"
        slots.append(
            OwnerSlot(
                key,
                assignment.external_coordinate,
                codec_key(_sort_type(item.value_sort), assignment.codec_id),
            )
        )
        fibres.append(OwnerInvocationFibre(key, (item.name,)))
    assignment_by_binding = {
        (item.scope, item.name): input_assignment[item.name] for item in core.inputs
    }
    for member in interface.statements:
        assignment = assignment_by_binding[
            (member.binding.scope, member.binding.input_name)
        ]
        aliases.append(
            OwnerStatementAlias(
                f"input:{assignment.core_input}",
                member.binding.input_name,
                StatementFlowKind.SUPPLIES_INVOCATION,
                assignment.core_input,
                member.external_statement,
            )
        )
    for item in core.schedule:
        if item.kind not in {
            k2.OccurrenceKind.PROVER_MESSAGE,
            k2.OccurrenceKind.VERIFIER_MESSAGE,
        }:
            continue
        exposure = transport_exposure[item.name]
        key = f"transport:{item.name}"
        slots.append(
            OwnerSlot(
                key,
                exposure.external_coordinate,
                codec_key(_occurrence_type(core, item), exposure.codec_id),
            )
        )
        source = (
            TransportActor.PROVER
            if item.kind is k2.OccurrenceKind.PROVER_MESSAGE
            else TransportActor.VERIFIER
        )
        destination = (
            TransportDestination.VERIFIER
            if source is TransportActor.PROVER
            else TransportDestination.PROVER
        )
        transports.append(OwnerTransport(item.name, source, destination, key))
    for name in public_derivations:
        item = next(item for item in core.schedule if item.name == name)
        if item.kind is not k2.OccurrenceKind.CHALLENGE:
            raise ValueError("public derivation fixture must name a challenge")
        key = f"public-derivation:{name}"
        slots.append(
            OwnerSlot(
                key,
                f"public.{name}",
                codec_key(_occurrence_type(core, item)),
            )
        )
        transports.append(
            OwnerTransport(
                name,
                TransportActor.PUBLIC_DERIVATION,
                TransportDestination.EXTERNAL_APPLICATION,
                key,
            )
        )

    terminal = next(
        item for item in core.schedule if item.kind is k2.OccurrenceKind.TERMINAL
    )
    terminal_completion = OwnerCompletion(
        CompletionTargetKind.CORE_TERMINAL,
        terminal.name,
        "core-terminal",
        (),
    )
    failure_types = (
        (CompletionCoordinateKind.FS_FAILURE_PAYLOAD, k3.BYTES),
        (CompletionCoordinateKind.FS_FAILURE_CHALLENGE, k3.BYTES),
        (CompletionCoordinateKind.FS_FAILURE_PREFIX_COUNT, k3.NAT),
        (CompletionCoordinateKind.FS_FAILURE_PREFIX_STATE, k3.BYTES32),
        (CompletionCoordinateKind.FS_FAILURE_DRAWS, k3.BYTES),
        (CompletionCoordinateKind.FS_FAILURE_FINAL_STATE, k3.BYTES32),
    )
    bindings: list[OwnerCompletionBinding] = []
    for coordinate, value_type in failure_types:
        key = f"completion:{coordinate.value}"
        slots.append(OwnerSlot(key, key, codec_key(value_type)))
        bindings.append(OwnerCompletionBinding(coordinate, key))
    failure_completion = OwnerCompletion(
        CompletionTargetKind.FS_FAILURE,
        None,
        "fiat-shamir-failure",
        tuple(bindings),
    )
    return OwnerInterfaceSurface(
        codecs,
        tuple(slots),
        tuple(fibres),
        tuple(aliases),
        tuple(transports),
        (terminal_completion, failure_completion),
    )


def _owner_plan_operand(read: object) -> OwnerPlanOperand:
    kind = {
        k3.PlanReadKind.PRIVATE_MATERIAL: PlanOperandKind.PRIVATE_MATERIAL,
        k3.PlanReadKind.PRIVATE_RANDOMNESS: PlanOperandKind.PRIVATE_RANDOMNESS,
        k3.PlanReadKind.STATE_BEFORE: PlanOperandKind.STATE_BEFORE,
        k3.PlanReadKind.PUBLIC_INPUT_VIEW: PlanOperandKind.VIEW_PUBLIC_INPUT,
        k3.PlanReadKind.PRIOR_OCCURRENCE_VIEW: PlanOperandKind.VIEW_OCCURRENCE,
    }[read.kind]
    return OwnerPlanOperand(kind, read.name)


def _future_plan(core: object, plan: object) -> OwnerPlanSurface:
    occurrences = {item.name: item for item in core.schedule}
    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    recipes: list[OwnerPlanRecipe] = []
    for route in sorted(
        plan.decision_routes, key=lambda item: occurrence_index[item.occurrence]
    ):
        inputs = tuple(_owner_plan_operand(item) for item in route.reads)
        node = OwnerPlanRecipeNode(
            route.implementation_algorithm_id,
            _evaluation(f"plan:{route.occurrence}"),
            inputs,
            _occurrence_type(core, occurrences[route.occurrence]),
        )
        state_after = tuple(
            (
                item.state,
                PlanUpdateKind.KEEP
                if item.kind is k3.StateAfterKind.KEEP
                else PlanUpdateKind.REPLACE,
                None
                if item.kind is k3.StateAfterKind.KEEP
                else OwnerPlanOperand(PlanOperandKind.NODE_OUTPUT, node_ordinal=0),
            )
            for item in route.state_after
        )
        recipes.append(
            OwnerPlanRecipe(
                route.occurrence,
                (node,),
                PlanMoveKind.MESSAGE_VALUE,
                OwnerPlanOperand(PlanOperandKind.NODE_OUTPUT, node_ordinal=0),
                state_after,
            )
        )
    exports = tuple(
        (
            item.key,
            item.source_decision,
            OwnerPlanOperand(PlanOperandKind.NODE_OUTPUT, node_ordinal=0),
            item.value_type,
        )
        for item in plan.exports
    )
    return OwnerPlanSurface(tuple(recipes), exports)


def _future_core(core: object) -> OwnerCoreSurface:
    reductions = tuple(
        OwnerReduction(
            item.name,
            f"contract:{item.name}",
            tuple(f"claim-contract:{name}" for name in item.output_claims),
        )
        for item in core.reductions
    )
    claims: list[OwnerClaim] = []
    statement_bindings = tuple(
        item for item in core.inputs if item.role is k2.InputRole.STATEMENT
    )
    if core.initial_claims and len(statement_bindings) != 1:
        raise ValueError(
            "the bounded initial-claim supplement law requires exactly one "
            "Statement binding"
        )
    for name in core.initial_claims:
        statement = statement_bindings[0]
        claims.append(
            OwnerClaim(
                name,
                f"claim-contract:{name}",
                ClaimUsage.LINEAR,
                statement.scope,
                ClaimSourceKind.BINDING,
                statement.name,
            )
        )
    for reduction in core.reductions:
        for output_ordinal, name in enumerate(reduction.output_claims):
            claims.append(
                OwnerClaim(
                    name,
                    f"claim-contract:{name}",
                    ClaimUsage.LINEAR,
                    reduction.scope,
                    ClaimSourceKind.REDUCTION_OUTPUT,
                    reduction.name,
                    output_ordinal,
                )
            )
    terminal = next(
        item for item in core.schedule if item.kind is k2.OccurrenceKind.TERMINAL
    )
    checks = tuple(
        item.name for item in core.schedule if item.kind is k2.OccurrenceKind.CHECK
    )
    dispositions = tuple(
        (use.claim, ClaimDisposition.CONSUME)
        for use in core.claim_uses
        if use.consumer == terminal.name
    )
    return OwnerCoreSurface(
        tuple(claims),
        reductions,
        OwnerTerminal(
            terminal.name,
            "all-required-checks-true",
            (),
            checks,
            dispositions,
        ),
    )


def _future_owner(
    core: object,
    construction: object,
    plan: object | None,
    *,
    interface: object | None = None,
    public_derivations: Sequence[str] = (),
) -> FutureOwnerSurface:
    return FutureOwnerSurface(
        _future_core(core),
        _owner_fs(core, construction),
        _future_interface(
            core,
            interface,
            public_derivations=public_derivations,
        ),
        None if plan is None else _future_plan(core, plan),
    )


def future_owner_supplement(
    core: object,
    construction: object,
    interface: object,
    plan: object | None,
    *,
    public_derivations: Sequence[str] = (),
) -> FutureOwnerSupplement:
    """Build an inert fixture candidate; this function mints no authority."""

    return _future_owner(
        core,
        construction,
        plan,
        interface=interface,
        public_derivations=public_derivations,
    )


def _supplement_source_fingerprint(request: ProjectionRequest) -> bytes:
    if request.construction is None:
        raise ValueError("future-owner supplement requires one FS construction")
    protocol = k3.protocol_id(
        request.core,
        request.construction,
        request.interpretation,
    )
    interface = k3.interface_id(
        request.core,
        request.construction,
        request.interpretation,
        request.interface,
    )
    plan = (
        None
        if request.plan is None
        else k3.plan_id(
            request.core,
            request.construction,
            request.interpretation,
            request.plan,
        )
    )
    return canonical_bytes(
        (
            k2.core_id(request.core),
            k2.construction_id(request.core, request.construction),
            protocol,
            interface,
            plan,
            _purpose(request.role),
        )
    )


def _profiled_source_datum_id(subject_kind: str, body: object) -> object:
    if subject_kind != "pir.endpoint-owner-supplement-authority-binding":
        raise TypeError("unsupported profiled K3-D source datum")
    identifier = k1.profiled_content_id(
        subject_kind,
        SOURCE_PROFILE,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    k1.authenticate_profiled_semantic_content(
        identifier,
        SOURCE_PROFILE,
        body,
        K3D_SEMANTIC_PROFILES.source_view_bundle,
        supported_profiles=(SOURCE_PROFILE,),
    )
    return identifier


def issue_future_owner_supplement(request: object) -> Answer:
    """Form one inert provisional supplement admission.

    The returned bearer is not live projection authority.  K3-D activates the
    exact same bearer only after joining and checking every available K2/K3-B
    owner view in :func:`check_projection_owner_adapter`.
    """

    if type(request) is not ProjectionRequest:
        return _answer(OutcomeKind.MALFORMED, reason="wrong supplement request carrier")
    if request.future_owner is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY,
            reason="future-owner supplement candidate is absent",
        )
    shape = _validate_future_owner_shape(request)
    if shape.kind is not OutcomeKind.AFFIRMATIVE:
        return shape
    overlap = _validate_future_owner_overlap(request)
    if overlap.kind is not OutcomeKind.AFFIRMATIVE:
        return overlap
    try:
        fingerprint = _supplement_source_fingerprint(request)
        supplement_id = _semantic_id(
            "pir.endpoint-owner-supplement",
            (fingerprint, request.future_owner),
        )
        consumer_id = _semantic_id(
            "pir.endpoint-owner-adapter-consumer",
            "checked-projection-owner-adapter-v0",
        )
        purpose_id = _semantic_id(
            "pir.endpoint-owner-adapter-purpose",
            (supplement_id, _purpose(request.role)),
        )
        owner = k1.Symbol("pir")
        family = k1.Symbol("endpoint-owner-supplement")
        requirement_id = _semantic_id(
            "pir.endpoint-owner-supplement-requirement",
            (
                supplement_id,
                consumer_id,
                purpose_id,
                "fresh-identical-bearer-capability-v0",
            ),
        )
        requirement = k1.OwnerCapabilityRequirement(owner, family, requirement_id)
        no_policy_id = _semantic_id(
            "pir.endpoint-owner-supplement-no-policy",
            (supplement_id, "no-owner-operation-after-admission-v0"),
        )
        closure_id = _semantic_id(
            "pir.endpoint-owner-supplement-policy-closure",
            (supplement_id, no_policy_id),
        )
        payload_id = _semantic_id(
            "pir.endpoint-owner-supplement-binding-payload",
            (supplement_id, fingerprint, consumer_id, purpose_id),
        )
        binding = k1.PortableSourceAuthorityBinding(
            owner,
            family,
            supplement_id,
            payload_id,
            k1.OwnerDefinesNoOperationPolicy(no_policy_id),
            closure_id,
            requirement,
        )
        binding_id = _profiled_source_datum_id(
            "pir.endpoint-owner-supplement-authority-binding",
            binding.body(),
        )
        capability = FutureOwnerSupplementCapability(
            supplement_id,
            binding,
            consumer_id,
            purpose_id,
            _purpose(request.role),
            fingerprint,
            request.future_owner,
            _FUTURE_OWNER_SUPPLEMENT_ISSUER,
        )
        issued = IssuedFutureOwnerSupplement(
            supplement_id,
            binding,
            binding_id,
            _purpose(request.role),
            fingerprint,
            request.future_owner,
            capability,
            _FUTURE_OWNER_SUPPLEMENT_ISSUER,
        )
        _PROVISIONAL_SUPPLEMENT_CAPABILITIES[id(capability)] = capability
        _PROVISIONAL_SUPPLEMENT_AUTHORITIES[id(issued)] = issued
    except (TypeError, ValueError, k1.ModelError) as error:
        return _answer(
            OutcomeKind.REFUSED,
            reason=f"future-owner supplement authority failed: {error}",
        )
    return _answer(OutcomeKind.AFFIRMATIVE, issued)


def bind_future_owner_supplement(request: object) -> Answer:
    """Return a request carrying the exact owner-issued supplement authority."""

    issued = issue_future_owner_supplement(request)
    if issued.kind is not OutcomeKind.AFFIRMATIVE:
        return issued
    assert type(request) is ProjectionRequest
    return _answer(
        OutcomeKind.AFFIRMATIVE,
        replace(request, supplement_authority=issued.value),
    )


def _require_bound_supplement(request: ProjectionRequest) -> ProjectionRequest:
    bound = bind_future_owner_supplement(request)
    if bound.kind is not OutcomeKind.AFFIRMATIVE:
        raise ValueError(f"fixture supplement admission failed: {bound.reason}")
    assert type(bound.value) is ProjectionRequest
    return bound.value


def p01_request(role: EndpointRole = EndpointRole.VERIFIER) -> ProjectionRequest:
    case = k3.schnorr_case()
    plan = case.plan if role is EndpointRole.PROVER else None
    return _require_bound_supplement(
        ProjectionRequest(
            case.core,
            case.construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            role,
            plan,
            future_owner_supplement(
                case.core,
                case.construction,
                case.interface,
                plan,
            ),
        )
    )


def p01_requests() -> tuple[ProjectionRequest, ProjectionRequest]:
    return p01_request(EndpointRole.VERIFIER), p01_request(EndpointRole.PROVER)


def live_p01_request(role: EndpointRole = EndpointRole.VERIFIER) -> ProjectionRequest:
    return replace(
        p01_request(role),
        future_owner=None,
        supplement_authority=None,
        provenance="live-k3b-carrier",
    )


def trivial_requests() -> tuple[ProjectionRequest, ProjectionRequest]:
    core = k2.Core(
        (),
        (k2.ScopeDecl("root", None, None),),
        (k2.Occurrence("terminal", k2.OccurrenceKind.TERMINAL),),
    )
    construction = k2.TranscriptConstruction(b"zkc/k3d/trivial/v0")
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    interface = k3.default_interface(core, construction, interpretation)
    plan = k3.ProverPlan(
        k3.protocol_id(core, construction, interpretation), (), (), (), (), ()
    )
    k3.check_plan_realizes(core, construction, interpretation, plan)
    verifier = _require_bound_supplement(
        ProjectionRequest(
            core,
            construction,
            interpretation,
            interface,
            EndpointRole.VERIFIER,
            None,
            future_owner_supplement(core, construction, interface, None),
            "independent-trivial-control",
        )
    )
    prover = _require_bound_supplement(
        ProjectionRequest(
            core,
            construction,
            interpretation,
            interface,
            EndpointRole.PROVER,
            plan,
            future_owner_supplement(core, construction, interface, plan),
            "independent-trivial-control",
        )
    )
    return verifier, prover


def verifier_message_requests(
    *,
    guarded: bool = False,
) -> tuple[ProjectionRequest, ProjectionRequest]:
    case = k3.schnorr_case()
    message = k2.Occurrence(
        "verifier-tag",
        k2.OccurrenceKind.VERIFIER_MESSAGE,
        guard=k2.Predicate(k2.PredicateKind.NEVER) if guarded else k2.Predicate(),
        verifier_rule=k2.VerifierRule(k2.VerifierRuleKind.CONSTANT_INT, (7,)),
    )
    core = replace(
        case.core,
        schedule=(case.core.schedule[0], message) + case.core.schedule[1:],
    )
    construction = case.construction
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    interface = k3.default_interface(
        core, construction, interpretation, expose_all_transports=True
    )
    plan = replace(
        case.plan,
        protocol_id=k3.protocol_id(core, construction, interpretation),
    )
    k3.check_plan_realizes(core, construction, interpretation, plan)
    verifier = _require_bound_supplement(
        ProjectionRequest(
            core,
            construction,
            interpretation,
            interface,
            EndpointRole.VERIFIER,
            None,
            future_owner_supplement(core, construction, interface, None),
            "verifier-message-control",
        )
    )
    prover = _require_bound_supplement(
        ProjectionRequest(
            core,
            construction,
            interpretation,
            interface,
            EndpointRole.PROVER,
            plan,
            future_owner_supplement(core, construction, interface, plan),
            "verifier-message-control",
        )
    )
    return verifier, prover


def nested_scope_requests() -> tuple[ProjectionRequest, ProjectionRequest]:
    case = k3.schnorr_case()
    challenge = replace(case.core.schedule[1], scope="challenge-scope")
    core = replace(
        case.core,
        scopes=case.core.scopes
        + (k2.ScopeDecl("challenge-scope", "root", "challenge"),),
        schedule=(case.core.schedule[0], challenge) + case.core.schedule[2:],
    )
    construction = case.construction
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    interface = k3.default_interface(
        core, construction, interpretation, expose_all_transports=True
    )
    plan = replace(
        case.plan,
        protocol_id=k3.protocol_id(core, construction, interpretation),
    )
    k3.check_plan_realizes(core, construction, interpretation, plan)
    return (
        _require_bound_supplement(
            ProjectionRequest(
                core,
                construction,
                interpretation,
                interface,
                EndpointRole.VERIFIER,
                None,
                future_owner_supplement(core, construction, interface, None),
                "nested-scope",
            )
        ),
        _require_bound_supplement(
            ProjectionRequest(
                core,
                construction,
                interpretation,
                interface,
                EndpointRole.PROVER,
                plan,
                future_owner_supplement(core, construction, interface, plan),
                "nested-scope",
            )
        ),
    )


def stateful_p01_request() -> ProjectionRequest:
    request = p01_request(EndpointRole.PROVER)
    assert request.plan is not None
    plan = request.plan
    private = plan.private_material + (
        k3.PrivateMaterialDecl(
            "acc0", k3.PrivateMaterialKind.CONFIDENTIAL_CONTEXT, k3.NAT
        ),
    )
    state = (k3.PersistentStrategyState("acc", k3.NAT, "acc0"),)
    routes = tuple(
        replace(
            route,
            reads=route.reads + (k3.PlanRead(k3.PlanReadKind.STATE_BEFORE, "acc"),),
            state_after=(
                k3.StateAfterBinding(
                    "acc",
                    k3.StateAfterKind.REPLACE_WITH_DECISION_OUTPUT
                    if index == 0
                    else k3.StateAfterKind.KEEP,
                ),
            ),
        )
        for index, route in enumerate(plan.decision_routes)
    )
    changed = replace(
        plan,
        private_material=private,
        persistent_state=state,
        decision_routes=routes,
    )
    k3.check_plan_realizes(
        request.core, request.construction, request.interpretation, changed
    )
    return _require_bound_supplement(
        replace(
            request,
            plan=changed,
            future_owner=future_owner_supplement(
                request.core,
                request.construction,
                request.interface,
                changed,
            ),
            supplement_authority=None,
            provenance="stateful-p01",
        )
    )


def public_derivation_requests(
    count: int,
) -> tuple[ProjectionRequest, ProjectionRequest]:
    if count not in {0, 1, 2}:
        raise ValueError("bounded public-derivation control supports 0, 1, or 2")
    if count < 2:
        verifier, prover = p01_requests()
        names = () if count == 0 else ("challenge",)
        return (
            _require_bound_supplement(
                replace(
                    verifier,
                    future_owner=future_owner_supplement(
                        verifier.core,
                        verifier.construction,
                        verifier.interface,
                        None,
                        public_derivations=names,
                    ),
                    supplement_authority=None,
                ),
            ),
            _require_bound_supplement(
                replace(
                    prover,
                    future_owner=future_owner_supplement(
                        prover.core,
                        prover.construction,
                        prover.interface,
                        prover.plan,
                        public_derivations=names,
                    ),
                    supplement_authority=None,
                ),
            ),
        )
    case = k3.schnorr_case()
    second = k2.Occurrence(
        "challenge-2",
        k2.OccurrenceKind.CHALLENGE,
        dependencies=(k2.ValueRef.input("statement"),),
        challenge_domain=k2.ChallengeDomain(13),
    )
    schedule = case.core.schedule[:2] + (second,) + case.core.schedule[2:]
    reduction = replace(
        case.core.reductions[0],
        required_challenges=("challenge", "challenge-2"),
    )
    core = replace(case.core, schedule=schedule, reductions=(reduction,))
    construction = case.construction
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    interface = k3.default_interface(
        core, construction, interpretation, expose_all_transports=True
    )
    routes = tuple(
        replace(
            route,
            reads=route.reads
            + (
                (k3.PlanRead(k3.PlanReadKind.PRIOR_OCCURRENCE_VIEW, "challenge-2"),)
                if route.occurrence == "response"
                else ()
            ),
        )
        for route in case.plan.decision_routes
    )
    plan = replace(
        case.plan,
        protocol_id=k3.protocol_id(core, construction, interpretation),
        decision_routes=routes,
    )
    k3.check_plan_realizes(core, construction, interpretation, plan)
    names = ("challenge", "challenge-2")
    return (
        _require_bound_supplement(
            ProjectionRequest(
                core,
                construction,
                interpretation,
                interface,
                EndpointRole.VERIFIER,
                None,
                future_owner_supplement(
                    core,
                    construction,
                    interface,
                    None,
                    public_derivations=names,
                ),
                "two-public-derivations",
            )
        ),
        _require_bound_supplement(
            ProjectionRequest(
                core,
                construction,
                interpretation,
                interface,
                EndpointRole.PROVER,
                plan,
                future_owner_supplement(
                    core,
                    construction,
                    interface,
                    plan,
                    public_derivations=names,
                ),
                "two-public-derivations",
            )
        ),
    )


# ---------------------------------------------------------------------------
# Fixed-law owner schema and read manifest
# ---------------------------------------------------------------------------


_OWNER_SCHEMA_FIELDS: tuple[tuple[str, object | None, tuple[str, ...]], ...] = (
    ("Protocol", None, ("core_id", "challenge_interpretation")),
    (
        "Core",
        k2.Core,
        (
            "inputs",
            "scopes",
            "schedule",
            "extensions",
            "initial_claims",
            "reductions",
            "claim_uses",
        ),
    ),
    ("InputDecl", k2.InputDecl, ("name", "role", "scope", "value_sort")),
    ("ScopeDecl", k2.ScopeDecl, ("name", "parent", "open_before")),
    (
        "Occurrence",
        k2.Occurrence,
        (
            "name",
            "kind",
            "scope",
            "dependencies",
            "guard",
            "verifier_rule",
            "challenge_domain",
            "oracle_name",
            "check_predicate",
            "prover_value_sort",
            "challenge_domain_ref",
            "fresh_law",
            "correlation",
            "reduction_use",
        ),
    ),
    ("Predicate", k2.Predicate, ("kind", "refs", "parameters")),
    ("ValueRef", k2.ValueRef, ("kind", "name")),
    ("VerifierRule", k2.VerifierRule, ("kind", "parameters")),
    ("ChallengeDomain", k2.ChallengeDomain, ("modulus",)),
    ("RequiredPublication", k2.RequiredPublication, ("publication", "next_challenge")),
    (
        "ReductionDecl",
        k2.ReductionDecl,
        (
            "name",
            "at_occurrence",
            "scope",
            "input_claims",
            "side_inputs",
            "required_challenges",
            "required_publications",
            "output_claims",
        ),
    ),
    ("ClaimConsumerUse", k2.ClaimConsumerUse, ("claim", "consumer")),
    (
        "TranscriptConstruction",
        k2.TranscriptConstruction,
        (
            "application_domain",
            "sample_bytes",
            "max_attempts",
            "state_bytes",
            "version",
            "challenge_rules",
        ),
    ),
    (
        "ProtocolInterface",
        k3.ProtocolInterface,
        ("protocol_id", "inputs", "statements", "transports"),
    ),
    (
        "InputAssignment",
        k3.InputAssignment,
        ("external_coordinate", "core_input", "role", "visibility", "codec_id"),
    ),
    ("StatementAssignment", k3.StatementAssignment, ("external_statement", "binding")),
    ("BindingRef", k3.BindingRef, ("scope", "input_name")),
    (
        "TransportExposure",
        k3.TransportExposure,
        ("external_coordinate", "occurrence", "role", "codec_id"),
    ),
    (
        "ProverPlan",
        k3.ProverPlan,
        (
            "protocol_id",
            "private_material",
            "randomness_requirements",
            "persistent_state",
            "decision_routes",
            "exports",
        ),
    ),
    ("PrivateMaterialDecl", k3.PrivateMaterialDecl, ("key", "kind", "value_type")),
    (
        "PrivateRandomnessRequirement",
        k3.PrivateRandomnessRequirement,
        ("name", "value_type", "first_available_at"),
    ),
    (
        "PersistentStrategyState",
        k3.PersistentStrategyState,
        ("name", "value_type", "initial_private_material"),
    ),
    ("PlanRead", k3.PlanRead, ("kind", "name")),
    ("StateAfterBinding", k3.StateAfterBinding, ("state", "kind")),
    (
        "DecisionRoute",
        k3.DecisionRoute,
        (
            "occurrence",
            "move_kind",
            "reads",
            "state_after",
            "implementation_algorithm_id",
        ),
    ),
    ("PlanExport", k3.PlanExport, ("key", "source_decision", "value_type")),
    (
        "OwnerCodec",
        OwnerCodec,
        (
            "codec_key",
            "kind",
            "value_type",
            "external_type",
            "semantic_type",
            "children",
            "general_law_id",
            "interface_codec_id",
        ),
    ),
    ("OwnerSlot", OwnerSlot, ("slot_key", "external_key", "codec_key")),
    ("OwnerInvocationFibre", OwnerInvocationFibre, ("slot_key", "invocation_inputs")),
    (
        "OwnerStatementAlias",
        OwnerStatementAlias,
        (
            "slot_key",
            "binding_input",
            "flow",
            "invocation_input",
            "external_statement",
        ),
    ),
    (
        "OwnerTransport",
        OwnerTransport,
        ("occurrence", "source", "destination", "slot_key"),
    ),
    (
        "OwnerCompletionBinding",
        OwnerCompletionBinding,
        ("coordinate", "slot_key", "output_ordinal"),
    ),
    (
        "OwnerCompletion",
        OwnerCompletion,
        ("target", "terminal_occurrence", "external_tag", "bindings"),
    ),
    (
        "OwnerInterfaceSurface",
        OwnerInterfaceSurface,
        (
            "codecs",
            "slots",
            "invocation_fibres",
            "statement_aliases",
            "transports",
            "completions",
        ),
    ),
    (
        "OwnerClaim",
        OwnerClaim,
        (
            "claim_key",
            "contract_ref",
            "usage",
            "scope",
            "source_kind",
            "source_name",
            "output_ordinal",
        ),
    ),
    (
        "OwnerReduction",
        OwnerReduction,
        ("reduction_name", "contract_ref", "output_contracts"),
    ),
    (
        "OwnerTerminal",
        OwnerTerminal,
        (
            "terminal_occurrence",
            "verdict",
            "public_outputs",
            "required_checks",
            "claim_dispositions",
        ),
    ),
    ("OwnerCoreSurface", OwnerCoreSurface, ("claims", "reductions", "terminal")),
    (
        "OwnerChallengeSemantics",
        OwnerChallengeSemantics,
        (
            "occurrence",
            "domain_ref",
            "fresh_law_ref",
            "correlation",
            "reduction_use",
            "accept_algorithm_id",
            "accept_evaluation_id",
            "decode_algorithm_id",
            "decode_evaluation_id",
        ),
    ),
    (
        "OwnerFsSurface",
        OwnerFsSurface,
        (
            "state_type",
            "bytes_type",
            "natural_type",
            "initial_state",
            "absorb_algorithm_id",
            "absorb_evaluation_id",
            "squeeze_algorithm_id",
            "squeeze_evaluation_id",
            "advance_algorithm_id",
            "advance_evaluation_id",
            "sampling_exhausted_failure",
            "challenges",
        ),
    ),
    (
        "OwnerPlanOperand",
        OwnerPlanOperand,
        ("kind", "name", "node_ordinal", "literal_type", "literal"),
    ),
    (
        "OwnerPlanRecipeNode",
        OwnerPlanRecipeNode,
        ("algorithm_id", "evaluation_id", "inputs", "output_type"),
    ),
    (
        "OwnerPlanRecipe",
        OwnerPlanRecipe,
        ("decision", "nodes", "move_kind", "move", "state_after"),
    ),
    (
        "OwnerPlanSurface",
        OwnerPlanSurface,
        ("recipes", "derived_exports", "has_module_recipe"),
    ),
    ("FutureOwnerSurface", FutureOwnerSurface, ("core", "fs", "interface", "plan")),
)


OWNER_SCHEMA_PATHS: tuple[str, ...] = tuple(
    f"{owner}.{field_name}"
    for owner, _carrier, field_names in _OWNER_SCHEMA_FIELDS
    for field_name in field_names
)


def reflected_owner_schema_paths(
    *,
    additions: Sequence[str] = (),
) -> tuple[str, ...]:
    result: list[str] = ["Protocol.core_id", "Protocol.challenge_interpretation"]
    for owner, carrier, _field_names in _OWNER_SCHEMA_FIELDS:
        if carrier is None:
            continue
        result.extend(f"{owner}.{item.name}" for item in fields(carrier))
    result.extend(additions)
    return tuple(result)


ROOT_GRAMMAR_LAW = "RootGrammarLawV0"
READ_LAW = "K3DReadLawV0"
OWNER_SCHEMA_SET_BODY = (
    ROOT_GRAMMAR_LAW,
)
OWNER_SCHEMA_SET_ID = _semantic_id(
    "pir.endpoint-owner-schema-set",
    OWNER_SCHEMA_SET_BODY,
)


def read_manifest_body(purpose: ProjectionPurpose) -> tuple[object, ...]:
    return (
        purpose,
        _id_text(OWNER_SCHEMA_SET_ID, "pir.endpoint-owner-schema-set"),
        READ_LAW,
    )


def read_manifest_id(purpose: ProjectionPurpose) -> object:
    return _semantic_id("pir.endpoint-read-manifest", read_manifest_body(purpose))


def audit_owner_schema(*, additions: Sequence[str] = ()) -> Answer:
    expected = OWNER_SCHEMA_PATHS
    observed = reflected_owner_schema_paths(additions=additions)
    if len(expected) != len(set(expected)):
        return _answer(
            OutcomeKind.CHECKER_FAILURE, reason="duplicate selected owner path"
        )
    if len(observed) != len(set(observed)):
        return _answer(
            OutcomeKind.UNSUPPORTED,
            reason="owner grammar has duplicate or unknown path",
        )
    if set(expected) != set(observed):
        missing = sorted(set(expected) - set(observed))
        extra = sorted(set(observed) - set(expected))
        return _answer(
            OutcomeKind.UNSUPPORTED,
            reason=f"fixed owner grammar mismatch missing={missing} extra={extra}",
        )
    return _answer(OutcomeKind.AFFIRMATIVE, OWNER_SCHEMA_SET_ID)


_MULTISINK_PATHS: Mapping[str, tuple[ViewSink, ...]] = {
    "Protocol.challenge_interpretation": (ViewSink.DEPENDENCY, ViewSink.STATIC_FS),
    "Core.inputs": (ViewSink.ABI, ViewSink.SPINE, ViewSink.TYPE),
    "Core.schedule": (ViewSink.ANCHOR, ViewSink.PLAN, ViewSink.SPINE),
    "Core.reductions": (ViewSink.ANCHOR, ViewSink.CLAIM, ViewSink.SPINE),
    "TranscriptConstruction.application_domain": (
        ViewSink.DEPENDENCY,
        ViewSink.STATIC_FS,
    ),
    "OwnerFsSurface.challenges": (
        ViewSink.DEPENDENCY,
        ViewSink.STATIC_FS,
        ViewSink.TYPE,
    ),
    "OwnerInterfaceSurface.codecs": (ViewSink.ABI, ViewSink.DEPENDENCY, ViewSink.TYPE),
    "OwnerPlanRecipeNode.algorithm_id": (ViewSink.DEPENDENCY, ViewSink.PLAN),
    "OwnerPlanRecipeNode.evaluation_id": (ViewSink.DEPENDENCY, ViewSink.PLAN),
    "PrivateMaterialDecl.kind": (ViewSink.PLAN,),
    "PrivateMaterialDecl.value_type": (ViewSink.PLAN, ViewSink.TYPE),
}


def owner_field_disposition(
    path: str,
    purpose: ProjectionPurpose,
) -> OwnerFieldDisposition:
    if path not in OWNER_SCHEMA_PATHS:
        raise KeyError(path)
    inert = {
        "PlanExport.key",
        "PlanExport.source_decision",
        "PlanExport.value_type",
        "OwnerPlanSurface.derived_exports",
        "PrivateMaterialDecl.key",
    }
    join = {
        "Protocol.core_id",
        "ProtocolInterface.protocol_id",
        "ProverPlan.protocol_id",
    }
    unsupported = {
        "Core.extensions",
        "Occurrence.oracle_name",
        "OwnerPlanSurface.has_module_recipe",
    }
    sinks = tuple(
        sorted(
            _MULTISINK_PATHS.get(path, (ViewSink.SPINE,)), key=lambda item: item.value
        )
    )

    def disposition(
        for_prover: bool,
    ) -> tuple[FieldDispositionKind, tuple[ViewSink, ...]]:
        if path in unsupported:
            return FieldDispositionKind.UNSUPPORTED, ()
        if path in join:
            return FieldDispositionKind.JOIN_ONLY, ()
        if path in inert or (for_prover and path == "Core.inputs" and False):
            return FieldDispositionKind.INERT, ()
        if not for_prover and path.startswith(
            (
                "ProverPlan.",
                "PrivateMaterialDecl.",
                "PrivateRandomnessRequirement.",
                "PersistentStrategyState.",
                "PlanRead.",
                "StateAfterBinding.",
                "DecisionRoute.",
                "PlanExport.",
                "OwnerPlan",
            )
        ):
            return FieldDispositionKind.INERT, ()
        return FieldDispositionKind.RELEVANT, sinks

    verifier_kind, verifier_sinks = disposition(False)
    prover_kind, prover_sinks = disposition(True)
    row = OwnerFieldDisposition(
        path,
        verifier_kind,
        verifier_sinks,
        prover_kind,
        prover_sinks,
    )
    selected_kind = (
        verifier_kind if purpose is ProjectionPurpose.FS_VERIFIER else prover_kind
    )
    selected_sinks = (
        verifier_sinks if purpose is ProjectionPurpose.FS_VERIFIER else prover_sinks
    )
    if selected_kind is FieldDispositionKind.RELEVANT and (
        not selected_sinks
        or selected_sinks
        != tuple(sorted(set(selected_sinks), key=lambda item: item.value))
    ):
        raise RuntimeError("ProjectionRelevant must carry a sorted nonempty sink set")
    if selected_kind is not FieldDispositionKind.RELEVANT and selected_sinks:
        raise RuntimeError("non-relevant disposition cannot carry view sinks")
    return row


_SUPPORT_ISSUER = object()
_OWNER_ADAPTER_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class CheckedProjectionOwnerAdapter:
    _issuer: object
    request: ProjectionRequest
    purpose: ProjectionPurpose
    k2_static_views: tuple[object, ...]
    checked_fs_construction: object
    fs_construction_view: object
    interface_view: object
    checked_plan: object | None
    supplement: IssuedFutureOwnerSupplement
    supplement_only_paths: tuple[str, ...]

    def __post_init__(self) -> None:
        if self._issuer is not _OWNER_ADAPTER_ISSUER:
            raise ValueError("only K3-D may issue a checked projection-owner adapter")

    def __repr__(self) -> str:
        return "CheckedProjectionOwnerAdapter(<live>)"

    def __copy__(self) -> "CheckedProjectionOwnerAdapter":
        raise ValueError("checked owner adapters cannot be copied")

    def __deepcopy__(self, _memo: object) -> "CheckedProjectionOwnerAdapter":
        raise ValueError("checked owner adapters cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("checked owner adapters cannot be serialized")


_LIVE_OWNER_ADAPTERS: dict[int, CheckedProjectionOwnerAdapter] = {}


def _is_live_joined_supplement(
    request: ProjectionRequest,
    authority: object,
) -> bool:
    if (
        type(authority) is not IssuedFutureOwnerSupplement
        or authority._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER
        or _LIVE_SUPPLEMENT_AUTHORITIES.get(id(authority)) is not authority
        or type(authority.capability) is not FutureOwnerSupplementCapability
        or _LIVE_SUPPLEMENT_CAPABILITIES.get(id(authority.capability))
        is not authority.capability
        or authority.capability._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER
        or authority.capability.authority_binding is not authority.authority_binding
        or authority.capability.supplement is not authority.supplement
        or authority.capability.supplement_id != authority.supplement_id
        or authority.capability.purpose is not authority.purpose
        or authority.capability.source_fingerprint != authority.source_fingerprint
        or authority.supplement is not request.future_owner
        or request.supplement_authority is not authority
        or authority.purpose is not _purpose(request.role)
    ):
        return False
    try:
        fingerprint = _supplement_source_fingerprint(request)
        supplement_id = _semantic_id(
            "pir.endpoint-owner-supplement",
            (fingerprint, request.future_owner),
        )
        expected_consumer_id = _semantic_id(
            "pir.endpoint-owner-adapter-consumer",
            "checked-projection-owner-adapter-v0",
        )
        expected_purpose_id = _semantic_id(
            "pir.endpoint-owner-adapter-purpose",
            (supplement_id, _purpose(request.role)),
        )
        authority.authority_binding.body()
        return (
            authority.source_fingerprint == fingerprint
            and authority.supplement_id == supplement_id
            and authority.authority_binding.owner_source_coordinate
            == supplement_id
            and authority.authority_binding_id
            == _profiled_source_datum_id(
                "pir.endpoint-owner-supplement-authority-binding",
                authority.authority_binding.body(),
            )
            and authority.capability.consumer_id == expected_consumer_id
            and authority.capability.purpose_id == expected_purpose_id
        )
    except (AttributeError, TypeError, ValueError, k1.ModelError):
        return False


def _is_live_owner_adapter(
    adapter: object,
    *,
    expected_request: ProjectionRequest | None = None,
) -> bool:
    if (
        type(adapter) is not CheckedProjectionOwnerAdapter
        or adapter._issuer is not _OWNER_ADAPTER_ISSUER
        or _LIVE_OWNER_ADAPTERS.get(id(adapter)) is not adapter
        or type(adapter.request) is not ProjectionRequest
        or (expected_request is not None and adapter.request is not expected_request)
        or adapter.purpose is not _purpose(adapter.request.role)
        or adapter.supplement_only_paths != FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS
        or not _is_live_joined_supplement(adapter.request, adapter.supplement)
    ):
        return False
    authority = adapter.supplement
    consumer_id = authority.capability.consumer_id
    purpose_id = authority.capability.purpose_id
    try:
        _static_view_payload(adapter.k2_static_views, consumer_id, purpose_id)
        if not k2.validate_issued_pir_static_view(
            adapter.fs_construction_view,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose_id,
        ):
            return False
        if not k3.validate_issued_protocol_interface_correspondence_view(
            adapter.interface_view,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose_id,
        ):
            return False
        checked_fs = adapter.checked_fs_construction
        if (
            type(checked_fs) is not k2.CheckedFSConstructionIssue
            or k2._FS_CONSTRUCTION_LIVE_ISSUES.get(id(checked_fs)) is not checked_fs
            or type(checked_fs.capability) is not k2.CheckedFSConstructionCapability
            or k2._FS_CONSTRUCTION_LIVE_CAPABILITIES.get(id(checked_fs.capability))
            is not checked_fs.capability
            or checked_fs.capability.consumer_id != consumer_id
            or checked_fs.capability.purpose_id != purpose_id
            or checked_fs.capability.result is not checked_fs.result
            or checked_fs.capability.source_binding is not checked_fs.source_binding
            or checked_fs.capability._sources[0] is not adapter.request.core
            or checked_fs.capability._sources[1] is not adapter.request.core
            or checked_fs.capability._sources[2] is not adapter.request.construction
        ):
            return False
        if adapter.request.role is EndpointRole.VERIFIER:
            return adapter.checked_plan is None
        expected_plan = k3.check_plan_realizes(
            adapter.request.core,
            adapter.request.construction,
            adapter.request.interpretation,
            adapter.request.plan,
        )
        return (
            type(adapter.checked_plan) is k3.CheckedPlanRealizes
            and adapter.checked_plan.protocol_id == expected_plan.protocol_id
            and adapter.checked_plan.plan_id == expected_plan.plan_id
        )
    except (AttributeError, IndexError, TypeError, ValueError, k1.ModelError):
        return False


def _closed_static_manifest(
    kind: object,
    requested: tuple[object, ...],
) -> tuple[object, ...]:
    return k2.required_static_view_read_closure(kind, requested)


def _lift_owner_view_failure(result: object, label: str) -> Answer | None:
    if result.kind is k2.QualifiedViewOutcomeKind.AFFIRMATIVE:
        return None
    try:
        kind = OutcomeKind(result.kind.value)
    except (AttributeError, ValueError):
        kind = OutcomeKind.CHECKER_FAILURE
    return _answer(kind, reason=f"{label} owner view failed: {result.detail}")


def _issue_k2_adapter_views(
    request: ProjectionRequest,
    consumer_id: object,
    purpose_id: object,
) -> Answer:
    core_requests = (
        (
            k2.StaticViewKind.PUBLIC_BINDING,
            (k2.StaticViewField.PB_BINDINGS,),
        ),
        (
            k2.StaticViewKind.PUBLIC_COIN,
            (k2.StaticViewField.PC_CHALLENGES,),
        ),
        (
            k2.StaticViewKind.EFFECT,
            (
                k2.StaticViewField.EF_MESSAGES,
                k2.StaticViewField.EF_ORACLES,
                k2.StaticViewField.EF_TERMINALS,
                k2.StaticViewField.EF_EXTENSIONS,
            ),
        ),
        (
            k2.StaticViewKind.CLAIM_REDUCTION,
            (k2.StaticViewField.CR_TERMINAL_DISPOSITIONS,),
        ),
    ) + (
        (
            k2.StaticViewKind.STRATEGY_DECISION,
            (
                k2.StaticViewField.SD_GUARANTEED_READS,
                k2.StaticViewField.SD_LEGAL_MOVE_TYPES,
            ),
        ),
    ) * (request.role is EndpointRole.PROVER)
    issued: list[object] = []
    for kind, leaves in core_requests:
        manifest = _closed_static_manifest(kind, leaves)
        result = k2.issue_core_static_view(
            request.core,
            kind,
            manifest,
            consumer_id=consumer_id,
            purpose_id=purpose_id,
        )
        failure = _lift_owner_view_failure(result, kind.value)
        if failure is not None:
            return failure
        issued.append(result.value)

    construction_requests = (
        (
            k2.StaticViewKind.TRANSCRIPT_DECLARATION,
            (k2.StaticViewField.TD_FRAME_SCHEDULE,),
        ),
        (
            k2.StaticViewKind.REQUIRED_INFLUENCE,
            (k2.StaticViewField.RI_PREFIX_LAW,),
        ),
        (
            k2.StaticViewKind.CHALLENGE_TRANSITION,
            (k2.StaticViewField.CT_RETRY_FAILURE,),
        ),
    )
    for kind, leaves in construction_requests:
        manifest = _closed_static_manifest(kind, leaves)
        result = k2.issue_construction_static_view(
            request.core,
            request.construction,
            kind,
            manifest,
            consumer_id=consumer_id,
            purpose_id=purpose_id,
        )
        failure = _lift_owner_view_failure(result, kind.value)
        if failure is not None:
            return failure
        issued.append(result.value)
    return _answer(OutcomeKind.AFFIRMATIVE, tuple(issued))


def _issue_fs_adapter_view(
    request: ProjectionRequest,
    consumer_id: object,
    purpose_id: object,
) -> Answer:
    checked = k2.check_fs_construction(
        request.core,
        request.core,
        request.construction,
        consumer_id=consumer_id,
        purpose_id=purpose_id,
    )
    failure = _lift_owner_view_failure(checked, "checked FS construction")
    if failure is not None:
        return failure
    manifest = _closed_static_manifest(
        k2.StaticViewKind.FS_CONSTRUCTION,
        (k2.StaticViewField.FS_CONCLUSION,),
    )
    view = k2.issue_fs_construction_view(
        checked.value,
        manifest,
        expected_consumer_id=consumer_id,
        expected_purpose_id=purpose_id,
        view_consumer_id=consumer_id,
        view_purpose_id=purpose_id,
    )
    failure = _lift_owner_view_failure(view, "FS construction")
    if failure is not None:
        return failure
    return _answer(OutcomeKind.AFFIRMATIVE, (checked.value, view.value))


def _issue_interface_adapter_view(
    request: ProjectionRequest,
    consumer_id: object,
    purpose_id: object,
) -> Answer:
    requested = tuple(
        k3.ProtocolInterfaceRead(
            k3.ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT,
            item.core_input,
        )
        for item in request.interface.inputs
    ) + tuple(
        k3.ProtocolInterfaceRead(
            k3.ProtocolInterfaceReadKind.STATEMENT_MEMBER,
            item.external_statement,
        )
        for item in request.interface.statements
    ) + tuple(
        k3.ProtocolInterfaceRead(
            k3.ProtocolInterfaceReadKind.TRANSPORT_ENTRY,
            item.occurrence,
        )
        for item in request.interface.transports
    )
    try:
        manifest = k3.CorrespondenceReadManifest(
            k3.required_protocol_interface_read_closure(
                request.interface,
                requested,
            )
        )
    except k3.K3Error as error:
        return _answer(
            OutcomeKind.MALFORMED,
            reason=f"Interface read closure failed: {error}",
        )
    except Exception as error:
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"Interface read closure checker failed: {error}",
        )
    result = k3.issue_protocol_interface_correspondence_view(
        request.core,
        request.construction,
        request.interpretation,
        request.interface,
        manifest,
        consumer_id=consumer_id,
        purpose_id=purpose_id,
    )
    failure = _lift_owner_view_failure(result, "ProtocolInterface")
    if failure is not None:
        return failure
    if not k3.validate_issued_protocol_interface_correspondence_view(
        result.value,
        expected_consumer_id=consumer_id,
        expected_purpose_id=purpose_id,
    ):
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason="ProtocolInterface owner authority is not exact",
        )
    return _answer(OutcomeKind.AFFIRMATIVE, result.value)


def _static_view_payload(
    issued: Sequence[object],
    consumer_id: object,
    purpose_id: object,
) -> Mapping[object, object]:
    values: dict[object, object] = {}
    for item in issued:
        if type(item) is not k2.IssuedPIRStaticView:
            raise ValueError("K2 adapter view has the wrong issued carrier")
        if not k2.validate_issued_pir_static_view(
            item,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose_id,
        ):
            raise ValueError("K2 adapter view authority is not exact")
        for entry in item.projection.entries:
            if entry.field in values:
                raise ValueError("K2 adapter views duplicate one owner field")
            values[entry.field] = entry.value
    return MappingProxyType(values)


def check_projection_owner_adapter(
    request: object,
    *,
    work_limit: int = MAX_WORK,
) -> Answer:
    """Join live owner views with one owner-admitted, purpose-bound supplement."""

    if type(work_limit) is not int or work_limit <= 0:
        return _answer(OutcomeKind.MALFORMED, reason="work limit must be positive")
    if type(request) is not ProjectionRequest:
        return _answer(OutcomeKind.MALFORMED, reason="wrong projection request carrier")
    authority = request.supplement_authority
    if authority is None or request.future_owner is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY,
            reason="owner-admitted future supplement authority is absent",
        )
    try:
        fingerprint = _supplement_source_fingerprint(request)
        provisional_authority = (
            _PROVISIONAL_SUPPLEMENT_AUTHORITIES.get(id(authority)) is authority
        )
        live_authority = _LIVE_SUPPLEMENT_AUTHORITIES.get(id(authority)) is authority
        provisional_capability = (
            type(authority) is IssuedFutureOwnerSupplement
            and type(authority.capability) is FutureOwnerSupplementCapability
            and _PROVISIONAL_SUPPLEMENT_CAPABILITIES.get(id(authority.capability))
            is authority.capability
        )
        live_capability = (
            type(authority) is IssuedFutureOwnerSupplement
            and type(authority.capability) is FutureOwnerSupplementCapability
            and _LIVE_SUPPLEMENT_CAPABILITIES.get(id(authority.capability))
            is authority.capability
        )
        if (
            type(authority) is not IssuedFutureOwnerSupplement
            or authority._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER
            or not (provisional_authority or live_authority)
            or type(authority.capability) is not FutureOwnerSupplementCapability
            or not (provisional_capability or live_capability)
            or provisional_authority != provisional_capability
            or live_authority != live_capability
            or authority.capability._issuer is not _FUTURE_OWNER_SUPPLEMENT_ISSUER
            or authority.capability.authority_binding is not authority.authority_binding
            or authority.capability.supplement_id != authority.supplement_id
            or authority.capability.supplement is not authority.supplement
            or authority.capability.purpose is not authority.purpose
            or authority.capability.source_fingerprint != authority.source_fingerprint
            or authority.supplement is not request.future_owner
            or authority.purpose is not _purpose(request.role)
            or authority.source_fingerprint != fingerprint
            or authority.supplement_id
            != _semantic_id(
                "pir.endpoint-owner-supplement",
                (fingerprint, request.future_owner),
            )
        ):
            raise ValueError("future supplement capability is stale or mismatched")
        authority.authority_binding.body()
        if authority.authority_binding.owner_source_coordinate != authority.supplement_id:
            raise ValueError("supplement authority binding names another source")
        if authority.authority_binding_id != _profiled_source_datum_id(
            "pir.endpoint-owner-supplement-authority-binding",
            authority.authority_binding.body(),
        ):
            raise ValueError("supplement authority-binding identity is stale")
        expected_consumer_id = _semantic_id(
            "pir.endpoint-owner-adapter-consumer",
            "checked-projection-owner-adapter-v0",
        )
        expected_purpose_id = _semantic_id(
            "pir.endpoint-owner-adapter-purpose",
            (authority.supplement_id, authority.purpose),
        )
        if (
            authority.capability.consumer_id != expected_consumer_id
            or authority.capability.purpose_id != expected_purpose_id
        ):
            raise ValueError("supplement capability consumer or purpose is stale")
    except (AttributeError, TypeError, ValueError, k1.ModelError) as error:
        return _answer(
            OutcomeKind.REFUSED,
            reason=f"future supplement authority refused: {error}",
        )

    consumer_id = authority.capability.consumer_id
    purpose_id = authority.capability.purpose_id
    k2_views = _issue_k2_adapter_views(request, consumer_id, purpose_id)
    if k2_views.kind is not OutcomeKind.AFFIRMATIVE:
        return k2_views
    fs_view = _issue_fs_adapter_view(request, consumer_id, purpose_id)
    if fs_view.kind is not OutcomeKind.AFFIRMATIVE:
        return fs_view
    interface_view = _issue_interface_adapter_view(
        request,
        consumer_id,
        purpose_id,
    )
    if interface_view.kind is not OutcomeKind.AFFIRMATIVE:
        return interface_view
    try:
        payload = _static_view_payload(k2_views.value, consumer_id, purpose_id)
    except (TypeError, ValueError) as error:
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"owner-view authority check failed: {error}",
        )
    overlap = _validate_future_owner_overlap(
        request,
        static_payload=payload,
        interface_view=interface_view.value.view,
    )
    if overlap.kind is not OutcomeKind.AFFIRMATIVE:
        return overlap
    checked_plan = None
    if request.role is EndpointRole.PROVER:
        try:
            checked_plan = k3.check_plan_realizes(
                request.core,
                request.construction,
                request.interpretation,
                request.plan,
            )
        except (k2.ModelError, k3.K3Error) as error:
            return _answer(
                OutcomeKind.REFUSED,
                reason=f"PlanRealizes authority failed: {error}",
            )
        except Exception as error:
            return _answer(
                OutcomeKind.CHECKER_FAILURE,
                reason=f"PlanRealizes authority checker failed: {error}",
            )
    # The owner-side carrier is deliberately provisional until all available
    # independent owner views and the exact Plan join have agreed.  Only this
    # point activates the identical bearer for consumption by the checked
    # adapter; failed joins never leave live supplement authority behind.
    if provisional_authority:
        _PROVISIONAL_SUPPLEMENT_AUTHORITIES.pop(id(authority), None)
        _PROVISIONAL_SUPPLEMENT_CAPABILITIES.pop(id(authority.capability), None)
        _LIVE_SUPPLEMENT_AUTHORITIES[id(authority)] = authority
        _LIVE_SUPPLEMENT_CAPABILITIES[id(authority.capability)] = authority.capability
    checked_fs, issued_fs_view = fs_view.value
    adapter = CheckedProjectionOwnerAdapter(
        _OWNER_ADAPTER_ISSUER,
        request,
        _purpose(request.role),
        k2_views.value,
        checked_fs,
        issued_fs_view,
        interface_view.value,
        checked_plan,
        authority,
        FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS,
    )
    _LIVE_OWNER_ADAPTERS[id(adapter)] = adapter
    return _answer(OutcomeKind.AFFIRMATIVE, adapter)


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class SupportedExtractionBasis:
    _issuer: object
    request: ProjectionRequest
    purpose: ProjectionPurpose
    adapter: CheckedProjectionOwnerAdapter
    schema_set_id: object
    manifest_id: object

    def __post_init__(self) -> None:
        if self._issuer is not _SUPPORT_ISSUER:
            raise ValueError("only K3-D may issue a supported extraction basis")

    def __repr__(self) -> str:
        return "SupportedExtractionBasis(<live>)"

    def __copy__(self) -> "SupportedExtractionBasis":
        raise ValueError("live support bases cannot be copied")

    def __deepcopy__(self, _memo: object) -> "SupportedExtractionBasis":
        raise ValueError("live support bases cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live support bases cannot be serialized")


_LIVE_SUPPORT_BASES: dict[int, SupportedExtractionBasis] = {}


def _is_live_support_basis(basis: object) -> bool:
    return (
        type(basis) is SupportedExtractionBasis
        and basis._issuer is _SUPPORT_ISSUER
        and _LIVE_SUPPORT_BASES.get(id(basis)) is basis
        and type(basis.request) is ProjectionRequest
        and _is_live_owner_adapter(
            basis.adapter,
            expected_request=basis.request,
        )
        and basis.adapter.request is basis.request
        and basis.purpose is _purpose(basis.request.role)
        and basis.adapter.purpose is basis.purpose
        and basis.schema_set_id == OWNER_SCHEMA_SET_ID
        and basis.manifest_id == read_manifest_id(basis.purpose)
    )


def classify_support(request: object, *, work_limit: int = MAX_WORK) -> Answer:
    if type(work_limit) is not int or work_limit <= 0:
        return _answer(
            OutcomeKind.MALFORMED, reason="work limit must be a positive integer"
        )
    if work_limit < 64:
        return _answer(
            OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED, reason="support traversal limit"
        )
    if type(request) is not ProjectionRequest or type(request.role) is not EndpointRole:
        return _answer(OutcomeKind.MALFORMED, reason="wrong projection request carrier")
    schema = audit_owner_schema()
    if schema.kind is not OutcomeKind.AFFIRMATIVE:
        return schema
    try:
        k2.admit_core(request.core)
    except k2.ModelError as error:
        return _answer(OutcomeKind.MALFORMED, reason=f"Core admission failed: {error}")
    except Exception as error:
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"Core admission checker failed: {error}",
        )
    if request.interpretation not in {
        k2.ChallengeInterpretation.FRESH,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
    }:
        return _answer(OutcomeKind.MALFORMED, reason="unknown challenge interpretation")
    if (
        request.future_owner is not None
        and request.future_owner.plan is not None
        and request.future_owner.plan.has_module_recipe
    ):
        return _answer(
            OutcomeKind.KIND_MISMATCH,
            reason="future Plan module recipe lies outside the selected owner grammar",
        )
    unsupported: set[SupportReason] = set()
    if request.interpretation is k2.ChallengeInterpretation.FRESH:
        unsupported.add(SupportReason.FRESH_ENDPOINT)
    if request.core.extensions or any(
        item.kind
        in {
            k2.OccurrenceKind.ORACLE_PUBLISH,
            k2.OccurrenceKind.ORACLE_QUERY,
            k2.OccurrenceKind.ORACLE_ANSWER,
        }
        for item in request.core.schedule
    ):
        unsupported.add(SupportReason.STANDARD_ORACLE_ENDPOINT)
    if request.admitted_module_effect:
        unsupported.add(SupportReason.MODULE_EFFECT_ENDPOINT)
    if (
        request.role is EndpointRole.PROVER
        and request.plan is None
    ):
        unsupported.add(SupportReason.GENERIC_PROVER_ENDPOINT)
    if unsupported:
        reasons = tuple(sorted(unsupported, key=lambda item: item.value))
        return _answer(
            OutcomeKind.UNSUPPORTED,
            reason=", ".join(item.value for item in reasons),
            unsupported_reasons=reasons,
        )
    if request.future_owner is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY,
            reason=(
                "current K2/K3-B evaluation carrier does not inhabit the "
                "selected future-owner schema"
            ),
        )
    if request.construction is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY, reason="FS construction is missing"
        )
    try:
        request.construction.admit()
        protocol = k3.protocol_id(
            request.core, request.construction, request.interpretation
        )
    except (k2.ModelError, k3.K3Error) as error:
        return _answer(
            OutcomeKind.REFUSED, reason=f"FS Protocol admission failed: {error}"
        )
    except Exception as error:
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"FS Protocol admission checker failed: {error}",
        )
    if type(request.interface) is not k3.ProtocolInterface:
        return _answer(OutcomeKind.MALFORMED, reason="wrong current Interface carrier")
    if request.interface.protocol_id != protocol:
        return _answer(
            OutcomeKind.KIND_MISMATCH, reason="Interface names another Protocol"
        )
    try:
        k3.admit_interface(
            request.core,
            request.construction,
            request.interpretation,
            request.interface,
        )
    except (k2.ModelError, k3.K3Error) as error:
        return _answer(
            OutcomeKind.MALFORMED, reason=f"Interface admission failed: {error}"
        )
    except Exception as error:
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"Interface admission checker failed: {error}",
        )
    if request.role is EndpointRole.VERIFIER:
        if request.plan is not None or request.future_owner.plan is not None:
            return _answer(
                OutcomeKind.MALFORMED, reason="Verifier endpoint cannot consume Plan"
            )
    else:
        try:
            k3.check_plan_realizes(
                request.core,
                request.construction,
                request.interpretation,
                request.plan,
            )
        except (k2.ModelError, k3.K3Error) as error:
            return _answer(OutcomeKind.REFUSED, reason=f"PlanRealizes failed: {error}")
        except Exception as error:
            return _answer(
                OutcomeKind.CHECKER_FAILURE,
                reason=f"PlanRealizes checker failed: {error}",
            )
    purpose = _purpose(request.role)
    for path in OWNER_SCHEMA_PATHS:
        owner_field_disposition(path, purpose)
    adapter = check_projection_owner_adapter(request, work_limit=work_limit)
    if adapter.kind is not OutcomeKind.AFFIRMATIVE:
        return adapter
    basis = SupportedExtractionBasis(
        _SUPPORT_ISSUER,
        request,
        purpose,
        adapter.value,
        OWNER_SCHEMA_SET_ID,
        read_manifest_id(purpose),
    )
    _LIVE_SUPPORT_BASES[id(basis)] = basis
    return _answer(OutcomeKind.AFFIRMATIVE, basis)


# ---------------------------------------------------------------------------
# Exact source-quotient extraction
# ---------------------------------------------------------------------------


def _profile_label(prefix: str, value: object) -> str:
    digest = hashlib.sha256(canonical_bytes(value)).hexdigest()[:24]
    return f"{prefix}:{digest}"


def _predicate_pair(prefix: str, predicate: object) -> tuple[object, object]:
    label = _profile_label(prefix, predicate)
    return _algorithm(label), _evaluation(label)


def _verifier_rule_pair(rule: object) -> tuple[object, object]:
    label = _profile_label("verifier-rule", rule)
    return _algorithm(label), _evaluation(label)


def _selected_input(input_decl: object, role: EndpointRole) -> bool:
    return (
        input_decl.role is not k2.InputRole.VERIFIER_PRIVATE
        or role is EndpointRole.VERIFIER
    )


def _selected_codec_keys(request: ProjectionRequest) -> set[str]:
    assert request.future_owner is not None
    interface = request.future_owner.interface
    slot_keys = {
        f"input:{item.name}"
        for item in request.core.inputs
        if _selected_input(item, request.role)
    }
    slot_keys.update(
        item.slot_key
        for item in interface.transports
        if item.source is not TransportActor.PUBLIC_DERIVATION
        or request.role is EndpointRole.VERIFIER
    )
    if request.role is EndpointRole.VERIFIER:
        slot_keys.update(
            binding.slot_key
            for completion in interface.completions
            for binding in completion.bindings
        )
    return {slot.codec_key for slot in interface.slots if slot.slot_key in slot_keys}


def _source_dependency_table(request: ProjectionRequest) -> tuple[Dependency, ...]:
    assert request.construction is not None and request.future_owner is not None
    owner = request.future_owner
    rows: list[Dependency] = [
        _dependency(DependencyKind.CORE, k2.core_id(request.core)),
        _dependency(
            DependencyKind.CONSTRUCTION,
            k2.construction_id(request.core, request.construction),
        ),
    ]

    fs_pairs = (
        (owner.fs.absorb_algorithm_id, owner.fs.absorb_evaluation_id),
        (owner.fs.squeeze_algorithm_id, owner.fs.squeeze_evaluation_id),
        (owner.fs.advance_algorithm_id, owner.fs.advance_evaluation_id),
    ) + tuple(
        pair
        for challenge in owner.fs.challenges
        for pair in (
            (challenge.accept_algorithm_id, challenge.accept_evaluation_id),
            (challenge.decode_algorithm_id, challenge.decode_evaluation_id),
        )
    )
    for algorithm, evaluation in fs_pairs:
        rows.append(_dependency(DependencyKind.ALGORITHM, algorithm))
        rows.append(_dependency(DependencyKind.EVALUATION, evaluation))

    for occurrence in request.core.schedule:
        if occurrence.guard.kind is not k2.PredicateKind.ALWAYS:
            algorithm, evaluation = _predicate_pair("guard", occurrence.guard)
            rows.extend(
                (
                    _dependency(DependencyKind.ALGORITHM, algorithm),
                    _dependency(DependencyKind.EVALUATION, evaluation),
                )
            )
        if occurrence.kind is k2.OccurrenceKind.VERIFIER_MESSAGE:
            algorithm, evaluation = _verifier_rule_pair(occurrence.verifier_rule)
            rows.extend(
                (
                    _dependency(DependencyKind.ALGORITHM, algorithm),
                    _dependency(DependencyKind.EVALUATION, evaluation),
                )
            )
        if occurrence.kind is k2.OccurrenceKind.CHECK:
            algorithm, evaluation = _predicate_pair("check", occurrence.check_predicate)
            rows.extend(
                (
                    _dependency(DependencyKind.ALGORITHM, algorithm),
                    _dependency(DependencyKind.EVALUATION, evaluation),
                )
            )

    selected_codec_keys = _selected_codec_keys(request)
    for codec in owner.interface.codecs:
        if codec.codec_key not in selected_codec_keys:
            continue
        if codec.kind is CodecKind.GENERAL and codec.general_law_id is not None:
            rows.append(_dependency(DependencyKind.CODEC_LAW, codec.general_law_id))
    if owner.plan is not None:
        for recipe in owner.plan.recipes:
            for node in recipe.nodes:
                rows.append(_dependency(DependencyKind.ALGORITHM, node.algorithm_id))
                rows.append(_dependency(DependencyKind.EVALUATION, node.evaluation_id))
    return _dedupe_sorted_dependencies(rows)


def _source_type_table(request: ProjectionRequest) -> tuple[ValueTypeAtom, ...]:
    assert request.future_owner is not None
    owner = request.future_owner
    rows: list[object] = []
    if any(item.kind is k2.OccurrenceKind.CHECK for item in request.core.schedule):
        rows.append(k3.BOOL)
    rows.extend(_sort_type(item.value_sort) for item in request.core.inputs)
    rows.extend(
        _occurrence_type(request.core, item)
        for item in request.core.schedule
        if item.kind is not k2.OccurrenceKind.TERMINAL
    )
    rows.extend((owner.fs.state_type, owner.fs.bytes_type, owner.fs.natural_type))
    selected_codec_keys = _selected_codec_keys(request)
    for codec in owner.interface.codecs:
        if codec.codec_key not in selected_codec_keys:
            continue
        rows.extend(
            item
            for item in (codec.value_type, codec.external_type, codec.semantic_type)
            if item is not None
        )
    if request.plan is not None:
        rows.extend(item.value_type for item in request.plan.private_material)
        rows.extend(item.value_type for item in request.plan.randomness_requirements)
        rows.extend(item.value_type for item in request.plan.persistent_state)
    if owner.plan is not None:
        for recipe in owner.plan.recipes:
            rows.extend(item.output_type for item in recipe.nodes)
            for node in recipe.nodes:
                rows.extend(
                    operand.literal_type
                    for operand in node.inputs
                    if operand.literal_type is not None
                )
    return _dedupe_sorted_types(rows)


@dataclass(frozen=True)
class _SpineLayout:
    events: tuple[SpineEvent, ...]
    scope_refs: Mapping[str, int]
    binding_refs: Mapping[str, int]
    occurrence_refs: Mapping[str, int]
    reduction_refs: Mapping[str, int]


def _source_spine_layout(request: ProjectionRequest) -> _SpineLayout:
    core = request.core
    events: list[SpineEvent] = [SpineEvent(SpineEventKind.FS_INITIALIZATION)]
    scope_refs: dict[str, int] = {}
    binding_refs: dict[str, int] = {}
    occurrence_refs: dict[str, int] = {}
    reduction_refs: dict[str, int] = {}
    scopes_by_open: dict[str | None, list[object]] = {}
    for scope in core.scopes:
        scopes_by_open.setdefault(scope.open_before, []).append(scope)
    selected_input_ref = {
        item.name: index
        for index, item in enumerate(
            declaration
            for declaration in core.inputs
            if _selected_input(declaration, request.role)
        )
    }

    def add_scope(scope: object) -> None:
        parent_ref = None if scope.parent is None else scope_refs[scope.parent]
        scope_ref = len(events)
        events.append(
            SpineEvent(
                SpineEventKind.SCOPE_OPENING,
                parent_scope_event_ref=parent_ref,
                original_scope_path=_scope_path(core, scope.name),
                opens_before_occurrence_ordinal=(
                    None
                    if scope.open_before is None
                    else next(
                        index
                        for index, item in enumerate(core.schedule)
                        if item.name == scope.open_before
                    )
                ),
            )
        )
        scope_refs[scope.name] = scope_ref
        for binding_ordinal, item in enumerate(core.inputs):
            if item.scope != scope.name or not _selected_input(item, request.role):
                continue
            binding_refs[item.name] = len(events)
            events.append(
                SpineEvent(
                    SpineEventKind.PUBLIC_BINDING,
                    scope_event_ref=scope_ref,
                    original_binding_ordinal=binding_ordinal,
                    binding_class=item.role.value,
                    binding_value=GraphValueRef(
                        ValueRefKind.INVOCATION,
                        selected_input_ref[item.name],
                    ),
                )
            )

    for scope in scopes_by_open.get(None, ()):
        add_scope(scope)
    reductions_at: dict[str, list[object]] = {}
    for reduction in core.reductions:
        reductions_at.setdefault(reduction.at_occurrence, []).append(reduction)
    for occurrence_ordinal, occurrence in enumerate(core.schedule):
        for scope in scopes_by_open.get(occurrence.name, ()):
            add_scope(scope)
        occurrence_refs[occurrence.name] = len(events)
        events.append(
            SpineEvent(
                SpineEventKind.CORE_OCCURRENCE,
                scope_event_ref=scope_refs[occurrence.scope],
                original_occurrence_ordinal=occurrence_ordinal,
            )
        )
        for reduction in reductions_at.get(occurrence.name, ()):
            reduction_refs[reduction.name] = len(events)
            events.append(
                SpineEvent(
                    SpineEventKind.CORE_OCCURRENCE,
                    scope_event_ref=scope_refs[reduction.scope],
                )
            )
    return _SpineLayout(
        tuple(events),
        MappingProxyType(scope_refs),
        MappingProxyType(binding_refs),
        MappingProxyType(occurrence_refs),
        MappingProxyType(reduction_refs),
    )


def _source_value_ref(
    request: ProjectionRequest,
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
    value_ref: object,
) -> GraphValueRef:
    if value_ref.kind is k2.RefKind.INPUT:
        if value_ref.name not in invocation_refs:
            raise ValueError("endpoint action reads an unavailable invocation target")
        return GraphValueRef(ValueRefKind.INVOCATION, invocation_refs[value_ref.name])
    if value_ref.name not in layout.occurrence_refs:
        raise ValueError("endpoint action reads an unknown occurrence")
    return GraphValueRef(
        ValueRefKind.OCCURRENCE_OUTPUT,
        layout.occurrence_refs[value_ref.name],
        0,
    )


@dataclass(frozen=True)
class _AbiBuild:
    graph: RoleAbiGraph
    invocation_refs: Mapping[str, int]
    transport_refs: Mapping[str, tuple[int, ...]]


def _source_abi(
    request: ProjectionRequest,
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
) -> _AbiBuild:
    assert request.future_owner is not None
    owner = request.future_owner.interface
    selected_inputs = tuple(
        item for item in request.core.inputs if _selected_input(item, request.role)
    )

    slot_reason: set[str] = {f"input:{item.name}" for item in selected_inputs}
    for edge in owner.transports:
        if (
            edge.source is not TransportActor.PUBLIC_DERIVATION
            or request.role is EndpointRole.VERIFIER
        ):
            slot_reason.add(edge.slot_key)
    if request.role is EndpointRole.VERIFIER:
        slot_reason.update(
            binding.slot_key for item in owner.completions for binding in item.bindings
        )
    selected_slots = tuple(item for item in owner.slots if item.slot_key in slot_reason)
    selected_slot_keys = {item.slot_key for item in selected_slots}
    codec_keys = {item.codec_key for item in selected_slots}
    selected_codecs = tuple(
        item for item in owner.codecs if item.codec_key in codec_keys
    )
    codec_ref = {item.codec_key: index for index, item in enumerate(selected_codecs)}
    slot_ref = {item.slot_key: index for index, item in enumerate(selected_slots)}

    codecs: list[CodecNode] = []
    for item in selected_codecs:
        children = tuple((ordinal, codec_ref[key]) for ordinal, key in item.children)
        codecs.append(
            CodecNode(
                item.kind,
                None
                if item.value_type is None
                else _type_index(types, item.value_type),
                None
                if item.external_type is None
                else _type_index(types, item.external_type),
                None
                if item.semantic_type is None
                else _type_index(types, item.semantic_type),
                children,
                (
                    None
                    if item.general_law_id is None
                    else _dep_index(
                        _source_dependency_table(request),
                        item.general_law_id,
                        DependencyKind.CODEC_LAW,
                    )
                ),
                item.interface_codec_id,
            )
        )
    slots = tuple(
        AbiSlot(item.external_key, codec_ref[item.codec_key]) for item in selected_slots
    )
    invocation_targets = tuple(
        InvocationTarget(
            InvocationClass.VERIFIER_PRIVATE
            if item.role is k2.InputRole.VERIFIER_PRIVATE
            else InvocationClass.PUBLIC,
            _type_index(types, _sort_type(item.value_sort)),
        )
        for item in selected_inputs
    )
    invocation_refs = {item.name: index for index, item in enumerate(selected_inputs)}
    fibre_by_slot = {item.slot_key: item for item in owner.invocation_fibres}
    fibres: list[InvocationFibre] = []
    for slot in selected_slots:
        owner_fibre = fibre_by_slot.get(slot.slot_key)
        if owner_fibre is None:
            continue
        refs = tuple(
            invocation_refs[name]
            for name in owner_fibre.invocation_inputs
            if name in invocation_refs
        )
        if refs:
            fibres.append(InvocationFibre(slot_ref[slot.slot_key], refs))
    aliases = tuple(
        StatementAlias(
            slot_ref[item.slot_key],
            layout.binding_refs[item.binding_input],
            item.flow,
            (
                None
                if item.invocation_input is None
                else invocation_refs[item.invocation_input]
            ),
            item.external_statement,
        )
        for item in owner.statement_aliases
        if item.slot_key in selected_slot_keys
        and item.binding_input in layout.binding_refs
        and (item.invocation_input is None or item.invocation_input in invocation_refs)
    )
    transports: list[TransportEdge] = []
    transport_refs: dict[str, list[int]] = {}
    for item in owner.transports:
        if item.slot_key not in selected_slot_keys:
            continue
        target_ref = layout.occurrence_refs[item.occurrence]
        index = len(transports)
        transports.append(
            TransportEdge(
                target_ref,
                item.source,
                item.destination,
                slot_ref[item.slot_key],
            )
        )
        transport_refs.setdefault(item.occurrence, []).append(index)
    completions: list[CompletionVariant] = []
    if request.role is EndpointRole.VERIFIER:
        for item in owner.completions:
            terminal_ref = (
                None
                if item.terminal_occurrence is None
                else layout.occurrence_refs[item.terminal_occurrence]
            )
            bindings = tuple(
                sorted(
                    (
                        (
                            CompletionCoordinate(
                                binding.coordinate,
                                terminal_ref
                                if binding.coordinate
                                is CompletionCoordinateKind.TERMINAL_OUTPUT
                                else None,
                                binding.output_ordinal,
                            ),
                            slot_ref[binding.slot_key],
                        )
                        for binding in item.bindings
                    ),
                    key=lambda pair: canonical_bytes(pair[0]),
                )
            )
            completions.append(
                CompletionVariant(
                    item.target,
                    terminal_ref,
                    item.external_tag,
                    bindings,
                )
            )
    return _AbiBuild(
        RoleAbiGraph(
            tuple(codecs),
            slots,
            invocation_targets,
            tuple(fibres),
            aliases,
            tuple(transports),
            tuple(completions),
        ),
        MappingProxyType(invocation_refs),
        MappingProxyType({key: tuple(value) for key, value in transport_refs.items()}),
    )


def _source_plan_value(
    operand: OwnerPlanOperand,
    *,
    request: ProjectionRequest,
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
    private_refs: Mapping[str, int],
    randomness_refs: Mapping[str, int],
    state_refs: Mapping[str, int],
    node_refs: Mapping[tuple[str, int], int],
    decision: str,
) -> PlanValueRef:
    assert request.plan is not None
    private = {item.key: item for item in request.plan.private_material}
    randomness = {item.name: item for item in request.plan.randomness_requirements}
    states = {item.name: item for item in request.plan.persistent_state}
    occurrence_by_name = {item.name: item for item in request.core.schedule}
    input_by_name = {item.name: item for item in request.core.inputs}
    if operand.kind is PlanOperandKind.PRIVATE_MATERIAL:
        item = private[operand.name]
        return PlanValueRef(
            operand.kind,
            private_refs[operand.name],
            _type_index(types, item.value_type),
        )
    if operand.kind is PlanOperandKind.PRIVATE_RANDOMNESS:
        item = randomness[operand.name]
        return PlanValueRef(
            operand.kind,
            randomness_refs[operand.name],
            _type_index(types, item.value_type),
        )
    if operand.kind is PlanOperandKind.STATE_BEFORE:
        item = states[operand.name]
        return PlanValueRef(
            operand.kind,
            state_refs[operand.name],
            _type_index(types, item.value_type),
        )
    if operand.kind is PlanOperandKind.VIEW_PUBLIC_INPUT:
        item = input_by_name[operand.name]
        return PlanValueRef(
            operand.kind,
            invocation_refs[operand.name],
            _type_index(types, _sort_type(item.value_sort)),
        )
    if operand.kind is PlanOperandKind.VIEW_OCCURRENCE:
        item = occurrence_by_name[operand.name]
        return PlanValueRef(
            operand.kind,
            layout.occurrence_refs[operand.name],
            _type_index(types, _occurrence_type(request.core, item)),
        )
    if operand.kind is PlanOperandKind.NODE_OUTPUT:
        if operand.node_ordinal is None:
            raise ValueError("node-output operand lacks an ordinal")
        ref = node_refs[(decision, operand.node_ordinal)]
        recipe = next(
            item
            for item in request.future_owner.plan.recipes
            if item.decision == decision
        )
        return PlanValueRef(
            operand.kind,
            ref,
            _type_index(types, recipe.nodes[operand.node_ordinal].output_type),
        )
    if operand.kind is PlanOperandKind.CONSTANT:
        if operand.literal_type is None:
            raise ValueError("literal Plan operand lacks a type")
        return PlanValueRef(
            operand.kind,
            0,
            _type_index(types, operand.literal_type),
            operand.literal,
        )
    raise ValueError("unknown Plan operand kind")


@dataclass(frozen=True)
class _PlanBuild:
    graph: PlanGraph | None
    decision_refs: Mapping[str, int]


def _source_plan(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> _PlanBuild:
    if request.role is EndpointRole.VERIFIER:
        return _PlanBuild(None, MappingProxyType({}))
    assert request.plan is not None
    assert request.future_owner is not None and request.future_owner.plan is not None
    owner = request.future_owner.plan
    recipes = tuple(
        sorted(owner.recipes, key=lambda item: layout.occurrence_refs[item.decision])
    )
    decision_refs = {
        item.decision: layout.occurrence_refs[item.decision] for item in recipes
    }

    used_private = {
        operand.name
        for recipe in recipes
        for node in recipe.nodes
        for operand in node.inputs
        if operand.kind is PlanOperandKind.PRIVATE_MATERIAL
    }
    used_randomness = {
        operand.name
        for recipe in recipes
        for node in recipe.nodes
        for operand in node.inputs
        if operand.kind is PlanOperandKind.PRIVATE_RANDOMNESS
    }
    used_state = {
        operand.name
        for recipe in recipes
        for node in recipe.nodes
        for operand in node.inputs
        if operand.kind is PlanOperandKind.STATE_BEFORE
    }
    used_state.update(
        name for recipe in recipes for name, _kind, _value in recipe.state_after
    )
    state_by_name = {item.name: item for item in request.plan.persistent_state}
    used_private.update(
        state_by_name[name].initial_private_material
        for name in used_state
        if state_by_name[name].initial_private_material is not None
    )

    selected_private = tuple(
        item for item in request.plan.private_material if item.key in used_private
    )
    selected_randomness = tuple(
        item
        for item in request.plan.randomness_requirements
        if item.name in used_randomness
    )
    selected_state = tuple(
        item for item in request.plan.persistent_state if item.name in used_state
    )
    private_refs = {item.key: index for index, item in enumerate(selected_private)}
    randomness_refs = {
        item.name: index for index, item in enumerate(selected_randomness)
    }
    state_refs = {item.name: index for index, item in enumerate(selected_state)}
    node_refs: dict[tuple[str, int], int] = {}
    cursor = 0
    for recipe in recipes:
        for ordinal, _node in enumerate(recipe.nodes):
            node_refs[(recipe.decision, ordinal)] = cursor
            cursor += 1

    private_graph = tuple(
        PlanPrivateMaterial(item.kind.value, _type_index(types, item.value_type))
        for item in selected_private
    )
    randomness_graph = tuple(
        PlanRandomness(
            _type_index(types, item.value_type),
            decision_refs[item.first_available_at],
        )
        for item in selected_randomness
    )
    state_graph: list[PlanState] = []
    for item in selected_state:
        if item.initial_private_material is None:
            raise ValueError("bounded state requires an explicit private initializer")
        initializer = PlanValueRef(
            PlanOperandKind.PRIVATE_MATERIAL,
            private_refs[item.initial_private_material],
            _type_index(types, item.value_type),
        )
        state_graph.append(PlanState(_type_index(types, item.value_type), initializer))

    nodes: list[PlanRecipeNode] = []
    moves: list[PlanMove] = []
    updates: list[PlanUpdate] = []
    for recipe in recipes:
        decision_ref = decision_refs[recipe.decision]
        for node in recipe.nodes:
            inputs = tuple(
                _source_plan_value(
                    operand,
                    request=request,
                    types=types,
                    layout=layout,
                    invocation_refs=invocation_refs,
                    private_refs=private_refs,
                    randomness_refs=randomness_refs,
                    state_refs=state_refs,
                    node_refs=node_refs,
                    decision=recipe.decision,
                )
                for operand in node.inputs
            )
            nodes.append(
                PlanRecipeNode(
                    decision_ref,
                    _dep_index(
                        dependencies, node.algorithm_id, DependencyKind.ALGORITHM
                    ),
                    _dep_index(
                        dependencies, node.evaluation_id, DependencyKind.EVALUATION
                    ),
                    inputs,
                    _type_index(types, node.output_type),
                )
            )
        move_value = _source_plan_value(
            recipe.move,
            request=request,
            types=types,
            layout=layout,
            invocation_refs=invocation_refs,
            private_refs=private_refs,
            randomness_refs=randomness_refs,
            state_refs=state_refs,
            node_refs=node_refs,
            decision=recipe.decision,
        )
        moves.append(PlanMove(decision_ref, recipe.move_kind, move_value))
        for state_name, kind, value in recipe.state_after:
            updates.append(
                PlanUpdate(
                    decision_ref,
                    state_refs[state_name],
                    kind,
                    None
                    if value is None
                    else _source_plan_value(
                        value,
                        request=request,
                        types=types,
                        layout=layout,
                        invocation_refs=invocation_refs,
                        private_refs=private_refs,
                        randomness_refs=randomness_refs,
                        state_refs=state_refs,
                        node_refs=node_refs,
                        decision=recipe.decision,
                    ),
                )
            )
    return _PlanBuild(
        PlanGraph(
            private_graph,
            randomness_graph,
            tuple(state_graph),
            tuple(nodes),
            tuple(moves),
            tuple(updates),
        ),
        MappingProxyType(decision_refs),
    )


def _source_claims_and_anchors(
    request: ProjectionRequest,
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> tuple[tuple[ClaimAtom, ...], tuple[AnchoredObligation, ...]]:
    assert request.future_owner is not None
    owner = request.future_owner.core
    claim_ref = {item.claim_key: index for index, item in enumerate(owner.claims)}
    claims = tuple(
        ClaimAtom(
            item.contract_ref,
            item.usage,
            layout.scope_refs[item.scope],
            item.source_kind,
            (
                layout.binding_refs[item.source_name]
                if item.source_kind is ClaimSourceKind.BINDING
                else layout.reduction_refs[item.source_name]
            ),
            item.output_ordinal,
        )
        for item in owner.claims
    )
    challenge_ref = {
        item.name: index
        for index, item in enumerate(
            occurrence
            for occurrence in request.core.schedule
            if occurrence.kind is k2.OccurrenceKind.CHALLENGE
        )
    }
    reduction_owner = {item.reduction_name: item for item in owner.reductions}
    anchors: list[AnchoredObligation] = []
    for reduction in request.core.reductions:
        anchors.append(
            AnchoredObligation(
                AnchorKind.REDUCTION,
                reduction_owner[reduction.name].contract_ref,
                layout.scope_refs[reduction.scope],
                layout.reduction_refs[reduction.name],
                tuple(claim_ref[name] for name in reduction.input_claims),
                tuple(
                    _source_value_ref(request, layout, invocation_refs, item)
                    for item in reduction.side_inputs
                ),
                tuple(challenge_ref[name] for name in reduction.required_challenges),
                tuple(
                    ReductionPublication(
                        layout.occurrence_refs[item.publication],
                        None
                        if item.next_challenge is None
                        else challenge_ref[item.next_challenge],
                    )
                    for item in reduction.required_publications
                ),
                tuple(
                    ReductionOutputRow(
                        output_ordinal,
                        contract_ref,
                        tuple(
                            claim_ref[item.claim_key]
                            for item in owner.claims
                            if item.source_kind is ClaimSourceKind.REDUCTION_OUTPUT
                            and item.source_name == reduction.name
                            and item.output_ordinal == output_ordinal
                        ),
                    )
                    for output_ordinal, contract_ref in enumerate(
                        reduction_owner[reduction.name].output_contracts
                    )
                ),
                None,
                None,
                (),
                (),
                (),
            )
        )
    terminal = owner.terminal
    anchors.append(
        AnchoredObligation(
            AnchorKind.TERMINAL,
            None,
            None,
            None,
            (),
            (),
            (),
            (),
            (),
            layout.occurrence_refs[terminal.terminal_occurrence],
            terminal.verdict,
            tuple(
                _source_value_ref(request, layout, invocation_refs, item)
                for item in terminal.public_outputs
            ),
            tuple(layout.occurrence_refs[name] for name in terminal.required_checks),
            tuple(
                (claim_ref[name], disposition)
                for name, disposition in terminal.claim_dispositions
            ),
        )
    )
    return claims, tuple(anchors)


def _source_static_fs(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> StaticFsSemantics:
    assert request.construction is not None and request.future_owner is not None
    owner = request.future_owner.fs
    core_dep = _dep_index(dependencies, k2.core_id(request.core), DependencyKind.CORE)
    construction_dep = _dep_index(
        dependencies,
        k2.construction_id(request.core, request.construction),
        DependencyKind.CONSTRUCTION,
    )
    owner_by_name = {item.occurrence: item for item in owner.challenges}
    laws: list[ChallengeLaw] = []
    for ordinal, occurrence in enumerate(request.core.schedule):
        if occurrence.kind is not k2.OccurrenceKind.CHALLENGE:
            continue
        assert occurrence.challenge_domain is not None
        item = owner_by_name[occurrence.name]
        type_ref = _type_index(types, _occurrence_type(request.core, occurrence))
        laws.append(
            ChallengeLaw(
                ordinal,
                type_ref,
                item.domain_ref,
                item.fresh_law_ref,
                item.correlation,
                item.reduction_use,
                tuple(
                    _source_value_ref(request, layout, invocation_refs, ref)
                    for ref in occurrence.dependencies
                ),
                request.construction.sample_bytes,
                request.construction.max_attempts,
                _dep_index(
                    dependencies,
                    item.accept_algorithm_id,
                    DependencyKind.ALGORITHM,
                ),
                _dep_index(
                    dependencies,
                    item.accept_evaluation_id,
                    DependencyKind.EVALUATION,
                ),
                _dep_index(
                    dependencies,
                    item.decode_algorithm_id,
                    DependencyKind.ALGORITHM,
                ),
                _dep_index(
                    dependencies,
                    item.decode_evaluation_id,
                    DependencyKind.EVALUATION,
                ),
            )
        )
    return StaticFsSemantics(
        core_dep,
        construction_dep,
        _type_index(types, owner.state_type),
        _type_index(types, owner.bytes_type),
        _type_index(types, owner.natural_type),
        owner.initial_state,
        _dep_index(dependencies, owner.absorb_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(dependencies, owner.absorb_evaluation_id, DependencyKind.EVALUATION),
        _dep_index(dependencies, owner.squeeze_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(
            dependencies, owner.squeeze_evaluation_id, DependencyKind.EVALUATION
        ),
        _dep_index(dependencies, owner.advance_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(
            dependencies, owner.advance_evaluation_id, DependencyKind.EVALUATION
        ),
        request.construction.application_domain,
        owner.sampling_exhausted_failure,
        "K2DerivedPrefixLawV0",
        "K2AdvanceBeforeAcceptRetryLawV0",
        tuple(laws),
    )


def _source_complete_spine(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    abi: _AbiBuild,
    plan: _PlanBuild,
    anchor_count: int,
) -> tuple[SpineEvent, ...]:
    occurrence_by_ref = {
        ref: next(item for item in request.core.schedule if item.name == name)
        for name, ref in layout.occurrence_refs.items()
    }
    reduction_by_ref = {
        ref: next(item for item in request.core.reductions if item.name == name)
        for name, ref in layout.reduction_refs.items()
    }
    challenge_law_ref = {
        item.name: index
        for index, item in enumerate(
            occurrence
            for occurrence in request.core.schedule
            if occurrence.kind is k2.OccurrenceKind.CHALLENGE
        )
    }
    result: list[SpineEvent] = []
    for event_ref, event in enumerate(layout.events):
        if event.kind is not SpineEventKind.CORE_OCCURRENCE:
            result.append(event)
            continue
        if event_ref in reduction_by_ref:
            result.append(
                replace(
                    event,
                    action=ReductionAction(),
                )
            )
            continue
        occurrence = occurrence_by_ref[event_ref]
        activity = Activity()
        if occurrence.guard.kind is not k2.PredicateKind.ALWAYS:
            algorithm, evaluation = _predicate_pair("guard", occurrence.guard)
            activity = Activity(
                _dep_index(dependencies, algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, evaluation, DependencyKind.EVALUATION),
                tuple(
                    _source_value_ref(request, layout, abi.invocation_refs, item)
                    for item in occurrence.guard.refs
                ),
            )
        if occurrence.kind is k2.OccurrenceKind.PROVER_MESSAGE:
            edges = abi.transport_refs.get(occurrence.name, ())
            if len(edges) != 1:
                raise ValueError("a selected prover message needs one transport edge")
            action: SpineAction = ProverMessageAction(
                _id_text(
                    _fixed_ref("pir.message-channel", f"channel:{occurrence.name}")
                ),
                _type_index(types, _occurrence_type(request.core, occurrence)),
            )
        elif occurrence.kind is k2.OccurrenceKind.VERIFIER_MESSAGE:
            edges = abi.transport_refs.get(occurrence.name, ())
            if len(edges) != 1:
                raise ValueError("a selected verifier message needs one transport edge")
            algorithm, evaluation = _verifier_rule_pair(occurrence.verifier_rule)
            action = VerifierMessageAction(
                _id_text(
                    _fixed_ref("pir.message-channel", f"channel:{occurrence.name}")
                ),
                _dep_index(dependencies, algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, evaluation, DependencyKind.EVALUATION),
                tuple(
                    _source_value_ref(request, layout, abi.invocation_refs, item)
                    for item in occurrence.dependencies
                ),
                _type_index(types, _occurrence_type(request.core, occurrence)),
            )
        elif occurrence.kind is k2.OccurrenceKind.CHALLENGE:
            action = ChallengeAction(challenge_law_ref[occurrence.name])
        elif occurrence.kind is k2.OccurrenceKind.CHECK:
            algorithm, evaluation = _predicate_pair("check", occurrence.check_predicate)
            action = CheckAction(
                _dep_index(dependencies, algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, evaluation, DependencyKind.EVALUATION),
                tuple(
                    _source_value_ref(request, layout, abi.invocation_refs, item)
                    for item in occurrence.check_predicate.refs
                ),
                _type_index(types, k3.BOOL),
            )
        elif occurrence.kind is k2.OccurrenceKind.TERMINAL:
            action = TerminalAction()
        else:
            raise ValueError("unsupported occurrence reached source extraction")
        result.append(replace(event, activity=activity, action=action))
    return tuple(result)


def _require_unique_owner_rows(
    rows: object,
    key: Callable[[object], object],
    label: str,
) -> tuple[object, ...]:
    if type(rows) is not tuple:
        raise TypeError(f"{label} must be one exact tuple")
    keys = tuple(key(item) for item in rows)
    if len(keys) != len(set(keys)):
        raise ValueError(f"{label} contain duplicate keys")
    return keys


def _validate_future_owner_shape(request: ProjectionRequest) -> Answer:
    if request.future_owner is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY,
            reason="selected future-owner source carrier is absent",
        )
    owner = request.future_owner
    try:
        if (
            type(owner) is not FutureOwnerSurface
            or type(owner.core) is not OwnerCoreSurface
            or type(owner.fs) is not OwnerFsSurface
            or type(owner.interface) is not OwnerInterfaceSurface
        ):
            raise TypeError("future-owner supplement has the wrong exact carrier")

        if any(type(item) is not OwnerCodec for item in owner.interface.codecs):
            raise TypeError("Interface codec rows have the wrong exact carrier")
        codec_keys = _require_unique_owner_rows(
            owner.interface.codecs,
            lambda item: item.codec_key,
            "Interface codec rows",
        )
        if any(type(item) is not OwnerSlot for item in owner.interface.slots):
            raise TypeError("Interface slot rows have the wrong exact carrier")
        slot_keys = _require_unique_owner_rows(
            owner.interface.slots,
            lambda item: item.slot_key,
            "Interface slot rows",
        )
        if any(
            type(key) is not str or not key for key in (*codec_keys, *slot_keys)
        ):
            raise ValueError("Interface codec and slot keys must be nonempty strings")
        if any(item.codec_key not in codec_keys for item in owner.interface.slots):
            raise ValueError("Interface slot names an unknown codec")
        if any(
            type(item) is not OwnerInvocationFibre
            for item in owner.interface.invocation_fibres
        ):
            raise TypeError("Interface fibre rows have the wrong exact carrier")
        _require_unique_owner_rows(
            owner.interface.invocation_fibres,
            lambda item: item.slot_key,
            "Interface invocation fibres",
        )
        if any(
            fibre.slot_key not in slot_keys
            or type(fibre.invocation_inputs) is not tuple
            for fibre in owner.interface.invocation_fibres
        ):
            raise ValueError("Interface invocation fibre names an unknown slot")
        flattened_inputs = tuple(
            name
            for fibre in owner.interface.invocation_fibres
            for name in fibre.invocation_inputs
        )
        input_names = tuple(item.name for item in request.core.inputs)
        if (
            len(flattened_inputs) != len(set(flattened_inputs))
            or set(flattened_inputs) != set(input_names)
            or len(flattened_inputs) != len(input_names)
        ):
            raise ValueError(
                "Interface invocation fibres do not cover Core inputs exactly"
            )

        if any(
            type(item) is not OwnerStatementAlias
            for item in owner.interface.statement_aliases
        ):
            raise TypeError("Statement aliases have the wrong exact carrier")
        _require_unique_owner_rows(
            owner.interface.statement_aliases,
            lambda item: item.external_statement,
            "Interface Statement aliases",
        )
        _require_unique_owner_rows(
            owner.interface.statement_aliases,
            lambda item: (item.binding_input, item.slot_key),
            "Interface Statement binding aliases",
        )
        if any(
            type(item.external_statement) is not str
            or not item.external_statement
            or item.slot_key not in slot_keys
            or type(item.flow) is not StatementFlowKind
            for item in owner.interface.statement_aliases
        ):
            raise ValueError("Interface Statement alias is malformed")

        occurrence_by_name = {item.name: item for item in request.core.schedule}
        message_names = {
            item.name
            for item in request.core.schedule
            if item.kind
            in {
                k2.OccurrenceKind.PROVER_MESSAGE,
                k2.OccurrenceKind.VERIFIER_MESSAGE,
            }
        }
        if any(
            type(item) is not OwnerTransport
            for item in owner.interface.transports
        ):
            raise TypeError("Interface transports have the wrong exact carrier")
        transport_occurrences = _require_unique_owner_rows(
            owner.interface.transports,
            lambda item: item.occurrence,
            "Interface transports",
        )
        observed_messages = {
            item.occurrence
            for item in owner.interface.transports
            if item.source is not TransportActor.PUBLIC_DERIVATION
        }
        if observed_messages != message_names:
            raise ValueError(
                "Interface transport graph does not cover messages exactly"
            )
        if any(
            item.occurrence not in occurrence_by_name
            or item.slot_key not in slot_keys
            or type(item.source) is not TransportActor
            or type(item.destination) is not TransportDestination
            for item in owner.interface.transports
        ):
            raise ValueError("Interface transport is malformed")
        if len(transport_occurrences) != len(owner.interface.transports):
            raise AssertionError("transport uniqueness helper lost cardinality")
        for transport in owner.interface.transports:
            occurrence = occurrence_by_name[transport.occurrence]
            if transport.source is TransportActor.PUBLIC_DERIVATION:
                if (
                    occurrence.kind is not k2.OccurrenceKind.CHALLENGE
                    or transport.destination
                    is not TransportDestination.EXTERNAL_APPLICATION
                ):
                    raise ValueError(
                        "public-derivation transport is not one exact challenge export"
                    )
            elif occurrence.kind not in {
                k2.OccurrenceKind.PROVER_MESSAGE,
                k2.OccurrenceKind.VERIFIER_MESSAGE,
            }:
                raise ValueError("non-public transport is not one message exposure")

        if any(
            type(item) is not OwnerChallengeSemantics
            for item in owner.fs.challenges
        ):
            raise TypeError("FS challenge rows have the wrong exact carrier")
        _require_unique_owner_rows(
            owner.fs.challenges,
            lambda item: item.occurrence,
            "FS challenge rows",
        )
        challenge_sequence = tuple(
            item.name
            for item in request.core.schedule
            if item.kind is k2.OccurrenceKind.CHALLENGE
        )
        challenge_names = set(challenge_sequence)
        if (
            {item.occurrence for item in owner.fs.challenges} != challenge_names
            or len(owner.fs.challenges) != len(challenge_names)
            or tuple(item.occurrence for item in owner.fs.challenges)
            != challenge_sequence
        ):
            raise ValueError("FS surface does not cover challenges exactly")

        if any(type(item) is not OwnerReduction for item in owner.core.reductions):
            raise TypeError("Core reduction rows have the wrong exact carrier")
        _require_unique_owner_rows(
            owner.core.reductions,
            lambda item: item.reduction_name,
            "Core reduction rows",
        )
        reduction_sequence = tuple(item.name for item in request.core.reductions)
        reduction_names = set(reduction_sequence)
        if (
            {item.reduction_name for item in owner.core.reductions}
            != reduction_names
            or len(owner.core.reductions) != len(reduction_names)
            or tuple(item.reduction_name for item in owner.core.reductions)
            != reduction_sequence
        ):
            raise ValueError("Core surface does not cover reductions exactly")
        reduction_by_name = {
            item.reduction_name: item for item in owner.core.reductions
        }
        if any(
            type(item.output_contracts) is not tuple
            or any(
                type(contract) is not str or not contract
                for contract in item.output_contracts
            )
            for item in owner.core.reductions
        ):
            raise ValueError("reduction output-contract rows are malformed")
        if any(type(item) is not OwnerClaim for item in owner.core.claims):
            raise TypeError("Core claim rows have the wrong exact carrier")
        _require_unique_owner_rows(
            owner.core.claims,
            lambda item: item.claim_key,
            "Core claim rows",
        )
        if any(
            type(claim.source_kind) is not ClaimSourceKind
            or type(claim.usage) is not ClaimUsage
            or type(claim.scope) is not str
            or not claim.scope
            or type(claim.source_name) is not str
            or not claim.source_name
            or (
                claim.source_kind is ClaimSourceKind.BINDING
                and claim.output_ordinal is not None
            )
            for claim in owner.core.claims
        ):
            raise ValueError("Core claim origin row is malformed")
        if any(
            claim.source_kind is ClaimSourceKind.REDUCTION_OUTPUT
            and (
                claim.source_name not in reduction_by_name
                or claim.output_ordinal is None
                or not 0
                <= claim.output_ordinal
                < len(reduction_by_name[claim.source_name].output_contracts)
            )
            for claim in owner.core.claims
        ):
            raise ValueError("reduction claim lies outside declared output contracts")
        if type(owner.core.terminal) is not OwnerTerminal:
            raise TypeError("Core terminal has the wrong exact carrier")
        terminals = [
            item.name
            for item in request.core.schedule
            if item.kind is k2.OccurrenceKind.TERMINAL
        ]
        if terminals != [owner.core.terminal.terminal_occurrence]:
            raise ValueError("Core surface terminal anchor is not exact")

        if any(
            type(item) is not OwnerCompletion
            for item in owner.interface.completions
        ):
            raise TypeError("Interface completions have the wrong exact carrier")
        completion_targets = _require_unique_owner_rows(
            owner.interface.completions,
            lambda item: item.target,
            "Interface completion targets",
        )
        _require_unique_owner_rows(
            owner.interface.completions,
            lambda item: item.external_tag,
            "Interface completion tags",
        )
        expected_completion_sequence = (
            CompletionTargetKind.CORE_TERMINAL,
            CompletionTargetKind.FS_FAILURE,
        )
        expected_completion_targets = set(expected_completion_sequence)
        if (
            set(completion_targets) != expected_completion_targets
            or len(completion_targets) != len(expected_completion_targets)
            or completion_targets != expected_completion_sequence
        ):
            raise ValueError("Interface completion surface is not exactly closed")
        expected_failure_coordinates = {
            CompletionCoordinateKind.FS_FAILURE_PAYLOAD,
            CompletionCoordinateKind.FS_FAILURE_CHALLENGE,
            CompletionCoordinateKind.FS_FAILURE_PREFIX_COUNT,
            CompletionCoordinateKind.FS_FAILURE_PREFIX_STATE,
            CompletionCoordinateKind.FS_FAILURE_DRAWS,
            CompletionCoordinateKind.FS_FAILURE_FINAL_STATE,
        }
        for completion in owner.interface.completions:
            if (
                type(completion.external_tag) is not str
                or not completion.external_tag
                or type(completion.bindings) is not tuple
                or any(
                    type(binding) is not OwnerCompletionBinding
                    for binding in completion.bindings
                )
            ):
                raise ValueError("Interface completion row is malformed")
            _require_unique_owner_rows(
                completion.bindings,
                lambda item: (item.coordinate, item.output_ordinal),
                f"{completion.target.value} completion bindings",
            )
            if any(
                binding.slot_key not in slot_keys
                or type(binding.coordinate) is not CompletionCoordinateKind
                for binding in completion.bindings
            ):
                raise ValueError("completion binding names an unknown slot")
            if completion.target is CompletionTargetKind.CORE_TERMINAL:
                ordinals = tuple(
                    binding.output_ordinal for binding in completion.bindings
                )
                if (
                    completion.terminal_occurrence
                    != owner.core.terminal.terminal_occurrence
                    or any(
                        binding.coordinate
                        is not CompletionCoordinateKind.TERMINAL_OUTPUT
                        for binding in completion.bindings
                    )
                    or ordinals
                    != tuple(range(len(owner.core.terminal.public_outputs)))
                ):
                    raise ValueError("terminal completion bindings are not exact")
            elif (
                completion.terminal_occurrence is not None
                or {binding.coordinate for binding in completion.bindings}
                != expected_failure_coordinates
                or len(completion.bindings) != len(expected_failure_coordinates)
                or any(
                    binding.output_ordinal is not None
                    for binding in completion.bindings
                )
            ):
                raise ValueError("FS-failure completion bindings are not exact")

        if request.role is EndpointRole.PROVER:
            if request.plan is None or type(owner.plan) is not OwnerPlanSurface:
                raise ValueError("Prover source lacks a Plan surface")
            if any(type(item) is not OwnerPlanRecipe for item in owner.plan.recipes):
                raise TypeError("Plan recipes have the wrong exact carrier")
            _require_unique_owner_rows(
                owner.plan.recipes,
                lambda item: item.decision,
                "Plan recipe rows",
            )
            decisions = {
                item.name
                for item in request.core.schedule
                if item.kind is k2.OccurrenceKind.PROVER_MESSAGE
            }
            if (
                {item.decision for item in owner.plan.recipes} != decisions
                or len(owner.plan.recipes) != len(decisions)
            ):
                raise ValueError("Plan recipe graph does not cover decisions exactly")
            _require_unique_owner_rows(
                owner.plan.derived_exports,
                lambda item: item[0],
                "Plan derived exports",
            )
            if any(
                type(item) is not tuple
                or len(item) != 4
                or type(item[0]) is not str
                or not item[0]
                or type(item[1]) is not str
                or not item[1]
                or type(item[2]) is not OwnerPlanOperand
                for item in owner.plan.derived_exports
            ):
                raise ValueError("Plan derived-export row is malformed")
        elif owner.plan is not None:
            raise ValueError("Verifier source unexpectedly carries a Plan surface")
    except (AttributeError, KeyError, TypeError, ValueError) as error:
        # This operation validates whether a formed owner carrier inhabits the
        # selected extraction profile.  Failure here does not refute a formed
        # projection proposition; no such proposition exists yet.
        return _answer(OutcomeKind.REFUSED, reason=f"owner-source inadequacy: {error}")
    return _answer(OutcomeKind.AFFIRMATIVE, owner)


def _validate_future_owner_overlap(
    request: ProjectionRequest,
    *,
    static_payload: Mapping[object, object] | None = None,
    interface_view: object | None = None,
) -> Answer:
    """Check every coordinate shared with current K2/K3-B owner surfaces."""

    if request.future_owner is None:
        return _answer(
            OutcomeKind.MISSING_DEPENDENCY,
            reason="selected future-owner supplement is absent",
        )
    owner = request.future_owner
    try:
        payload = {} if static_payload is None else static_payload
        transcript_algorithms = payload.get(
            k2.StaticViewField.TD_ALGORITHMS,
            (request.construction.version, k2.INITIAL_TRANSCRIPT_STATE),
        )
        if owner.fs.initial_state != transcript_algorithms[1]:
            raise ValueError("FS initial state disagrees with Construction ownership")

        initial_claims = payload.get(
            k2.StaticViewField.CR_CLAIMS,
            request.core.initial_claims,
        )
        reductions = payload.get(
            k2.StaticViewField.CR_REDUCTIONS,
            request.core.reductions,
        )
        claim_uses = payload.get(
            k2.StaticViewField.CR_TERMINAL_DISPOSITIONS,
            request.core.claim_uses,
        )
        schedule = payload.get(
            k2.StaticViewField.EF_OCCURRENCE_SCHEDULE,
            request.core.schedule,
        )
        public_bindings = payload.get(
            k2.StaticViewField.PB_BINDINGS,
            tuple(
                (
                    item.scope,
                    item.name,
                    item.role,
                    item.value_sort,
                    "invocation-public-input",
                )
                for item in request.core.inputs
                if item.role is not k2.InputRole.VERIFIER_PRIVATE
            ),
        )
        statement_bindings = tuple(
            row for row in public_bindings if row[2] is k2.InputRole.STATEMENT
        )
        if initial_claims and len(statement_bindings) != 1:
            raise ValueError(
                "bounded initial claims require one exact owner-issued Statement "
                "binding"
            )
        expected_claim_origins: dict[
            str, tuple[str, ClaimSourceKind, str, int | None]
        ] = {}
        for claim_name in initial_claims:
            if claim_name in expected_claim_origins:
                raise ValueError("Core initial claim names are duplicated")
            statement_scope, statement_name, *_rest = statement_bindings[0]
            expected_claim_origins[claim_name] = (
                statement_scope,
                ClaimSourceKind.BINDING,
                statement_name,
                None,
            )
        for reduction in reductions:
            for output_ordinal, claim_name in enumerate(reduction.output_claims):
                if claim_name in expected_claim_origins:
                    raise ValueError("Core claim origins are not uniquely keyed")
                expected_claim_origins[claim_name] = (
                    reduction.scope,
                    ClaimSourceKind.REDUCTION_OUTPUT,
                    reduction.name,
                    output_ordinal,
                )
        owner_claims = {item.claim_key: item for item in owner.core.claims}
        if (
            set(owner_claims) != set(expected_claim_origins)
            or len(owner.core.claims) != len(expected_claim_origins)
            or tuple(item.claim_key for item in owner.core.claims)
            != tuple(expected_claim_origins)
        ):
            raise ValueError("supplement claim coverage disagrees with Core")
        for claim_name, expected_origin in expected_claim_origins.items():
            claim = owner_claims[claim_name]
            observed_origin = (
                claim.scope,
                claim.source_kind,
                claim.source_name,
                claim.output_ordinal,
            )
            if observed_origin != expected_origin:
                raise ValueError(
                    "supplement claim origin disagrees with the owner-issued Core view"
                )
        owner_reductions = {
            item.reduction_name: item for item in owner.core.reductions
        }
        if len(owner_reductions) != len(reductions):
            raise ValueError("supplement reduction cardinality disagrees with Core")
        for reduction in reductions:
            row = owner_reductions[reduction.name]
            if len(row.output_contracts) != len(reduction.output_claims):
                raise ValueError("supplement reduction output arity disagrees with Core")
        expected_checks = tuple(
            item.name
            for item in schedule
            if item.kind is k2.OccurrenceKind.CHECK
        )
        if owner.core.terminal.required_checks != expected_checks:
            raise ValueError("supplement terminal checks disagree with Core")
        expected_dispositions = tuple(
            (item.claim, ClaimDisposition.CONSUME)
            for item in claim_uses
            if item.consumer == owner.core.terminal.terminal_occurrence
        )
        if owner.core.terminal.claim_dispositions != expected_dispositions:
            raise ValueError("supplement terminal claim uses disagree with Core")

        if interface_view is None:
            interface_inputs = request.interface.inputs
            interface_statements = request.interface.statements
            interface_transports_rows = request.interface.transports
        else:
            if (
                type(interface_view) is not k3.ProtocolInterfaceCorrespondenceView
                or interface_view.protocol_interface_id
                != k3.interface_id(
                    request.core,
                    request.construction,
                    request.interpretation,
                    request.interface,
                )
            ):
                raise ValueError("live Interface view names another owner")
            interface_inputs = tuple(
                entry.value
                for entry in interface_view.entries
                if entry.read.kind
                is k3.ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT
            )
            interface_statements = tuple(
                entry.value
                for entry in interface_view.entries
                if entry.read.kind is k3.ProtocolInterfaceReadKind.STATEMENT_MEMBER
            )
            interface_transports_rows = tuple(
                entry.value
                for entry in interface_view.entries
                if entry.read.kind is k3.ProtocolInterfaceReadKind.TRANSPORT_ENTRY
            )
        slots = {item.slot_key: item for item in owner.interface.slots}
        codecs = {item.codec_key: item for item in owner.interface.codecs}
        fibres = {item.slot_key: item for item in owner.interface.invocation_fibres}
        for assignment in interface_inputs:
            slot_key = f"input:{assignment.core_input}"
            slot = slots.get(slot_key)
            if slot is None or slot.external_key != assignment.external_coordinate:
                raise ValueError("supplement invocation slot disagrees with Interface")
            codec = codecs[slot.codec_key]
            if codec.interface_codec_id != assignment.codec_id:
                raise ValueError("supplement invocation codec disagrees with Interface")
            declaration = next(
                item for item in request.core.inputs if item.name == assignment.core_input
            )
            if (
                codec.value_type is None
                or _type_body(codec.value_type)
                != _type_body(_sort_type(declaration.value_sort))
            ):
                raise ValueError("supplement invocation codec type disagrees with Core")
            fibre = fibres.get(slot_key)
            if fibre is None or fibre.invocation_inputs != (assignment.core_input,):
                raise ValueError("bounded supplement invocation fibre is not exact")

        owner_statements = {
            item.external_statement: item for item in owner.interface.statement_aliases
        }
        if (
            set(owner_statements)
            != {item.external_statement for item in interface_statements}
            or len(owner.interface.statement_aliases) != len(interface_statements)
        ):
            raise ValueError("supplement Statement names disagree with Interface")
        for member in interface_statements:
            alias = owner_statements[member.external_statement]
            if (
                alias.binding_input != member.binding.input_name
                or alias.slot_key != f"input:{member.binding.input_name}"
                or alias.invocation_input != member.binding.input_name
            ):
                raise ValueError("supplement Statement binding disagrees with Interface")

        owner_transports = {
            item.occurrence: item
            for item in owner.interface.transports
            if item.source is not TransportActor.PUBLIC_DERIVATION
        }
        interface_transports = {
            item.occurrence: item for item in interface_transports_rows
        }
        message_names = {
            item.name
            for item in schedule
            if item.kind
            in {
                k2.OccurrenceKind.PROVER_MESSAGE,
                k2.OccurrenceKind.VERIFIER_MESSAGE,
            }
        }
        if set(interface_transports) != message_names:
            raise ValueError(
                "selected endpoint profile requires exact Interface message exposure"
            )
        if (
            set(owner_transports) != set(interface_transports)
            or len(owner_transports) != len(interface_transports)
        ):
            raise ValueError("supplement transports disagree with Interface")
        transport_roles = {
            k3.TransportRole.PROVER_TO_VERIFIER: (
                TransportActor.PROVER,
                TransportDestination.VERIFIER,
            ),
            k3.TransportRole.VERIFIER_TO_PROVER: (
                TransportActor.VERIFIER,
                TransportDestination.PROVER,
            ),
        }
        for occurrence, exposure in interface_transports.items():
            edge = owner_transports[occurrence]
            expected_source, expected_destination = transport_roles[exposure.role]
            slot = slots.get(edge.slot_key)
            if (
                edge.source is not expected_source
                or edge.destination is not expected_destination
                or slot is None
                or slot.external_key != exposure.external_coordinate
                or codecs[slot.codec_key].interface_codec_id != exposure.codec_id
            ):
                raise ValueError("supplement transport row disagrees with Interface")

        if request.role is EndpointRole.PROVER:
            if request.plan is None or owner.plan is None:
                raise ValueError("prover supplement lacks its checked Plan")
            routes = {item.occurrence: item for item in request.plan.decision_routes}
            view_decisions = payload.get(
                k2.StaticViewField.SD_DECISION_POINTS,
                tuple(
                    item
                    for item in schedule
                    if item.kind is k2.OccurrenceKind.PROVER_MESSAGE
                ),
            )
            if set(routes) != {item.name for item in view_decisions}:
                raise ValueError("Plan routes disagree with owner-issued decision view")
            recipes = {item.decision: item for item in owner.plan.recipes}
            if set(recipes) != set(routes):
                raise ValueError("supplement recipes disagree with Plan decisions")
            read_kinds = {
                k3.PlanReadKind.PRIVATE_MATERIAL: PlanOperandKind.PRIVATE_MATERIAL,
                k3.PlanReadKind.PRIVATE_RANDOMNESS: PlanOperandKind.PRIVATE_RANDOMNESS,
                k3.PlanReadKind.STATE_BEFORE: PlanOperandKind.STATE_BEFORE,
                k3.PlanReadKind.PUBLIC_INPUT_VIEW: PlanOperandKind.VIEW_PUBLIC_INPUT,
                k3.PlanReadKind.PRIOR_OCCURRENCE_VIEW: PlanOperandKind.VIEW_OCCURRENCE,
            }
            for decision, route in routes.items():
                recipe = recipes[decision]
                if len(recipe.nodes) != 1:
                    raise ValueError("bounded supplement recipe must have one owner node")
                node = recipe.nodes[0]
                expected_inputs = tuple(
                    OwnerPlanOperand(read_kinds[item.kind], item.name)
                    for item in route.reads
                )
                expected_move = (
                    PlanMoveKind.MESSAGE_VALUE
                    if route.move_kind is k3.MoveKind.MESSAGE_VALUE
                    else PlanMoveKind.ORACLE_OBJECT
                )
                expected_updates = tuple(
                    (
                        item.state,
                        PlanUpdateKind.KEEP
                        if item.kind is k3.StateAfterKind.KEEP
                        else PlanUpdateKind.REPLACE,
                        None
                        if item.kind is k3.StateAfterKind.KEEP
                        else OwnerPlanOperand(
                            PlanOperandKind.NODE_OUTPUT,
                            node_ordinal=0,
                        ),
                    )
                    for item in route.state_after
                )
                if (
                    node.algorithm_id != route.implementation_algorithm_id
                    or node.inputs != expected_inputs
                    or recipe.move_kind is not expected_move
                    or recipe.move
                    != OwnerPlanOperand(PlanOperandKind.NODE_OUTPUT, node_ordinal=0)
                    or recipe.state_after != expected_updates
                ):
                    raise ValueError("supplement recipe overlap disagrees with Plan")
            expected_exports = tuple(
                (item.key, item.source_decision, item.value_type)
                for item in request.plan.exports
            )
            observed_exports = tuple(
                (key, source, value_type)
                for key, source, _operand, value_type in owner.plan.derived_exports
            )
            if observed_exports != expected_exports:
                raise ValueError("supplement exports disagree with Plan")
    except (AttributeError, IndexError, KeyError, StopIteration, TypeError, ValueError) as error:
        return _answer(
            OutcomeKind.REFUSED,
            reason=f"future-owner overlap mismatch: {error}",
        )
    return _answer(OutcomeKind.AFFIRMATIVE, owner)


_EXTRACTION_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class CheckedEndpointSourceView:
    _issuer: object
    request: ProjectionRequest
    basis: SupportedExtractionBasis
    adapter: CheckedProjectionOwnerAdapter
    view: EndpointSourceView
    view_id: object
    schema_set_id: object
    manifest_id: object

    def __post_init__(self) -> None:
        if self._issuer is not _EXTRACTION_ISSUER:
            raise ValueError("only K3-D may issue a checked endpoint source view")

    def __repr__(self) -> str:
        return "CheckedEndpointSourceView(<live>)"

    def __copy__(self) -> "CheckedEndpointSourceView":
        raise ValueError("live source views cannot be copied")

    def __deepcopy__(self, _memo: object) -> "CheckedEndpointSourceView":
        raise ValueError("live source views cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live source views cannot be serialized")


_LIVE_CHECKED_SOURCE_VIEWS: dict[int, CheckedEndpointSourceView] = {}


def endpoint_source_view_id(view: EndpointSourceView) -> object:
    if view.profile != SOURCE_PROFILE:
        raise TypeError("endpoint source view names an unsupported language profile")
    return _semantic_id(
        "pir.endpoint-source-view",
        (view.purpose, view.semantic_graph),
    )


def _is_live_checked_source_view(source: object) -> bool:
    if (
        type(source) is not CheckedEndpointSourceView
        or source._issuer is not _EXTRACTION_ISSUER
        or _LIVE_CHECKED_SOURCE_VIEWS.get(id(source)) is not source
        or type(source.request) is not ProjectionRequest
        or not _is_live_support_basis(source.basis)
        or source.basis.request is not source.request
        or source.adapter is not source.basis.adapter
        or type(source.view) is not EndpointSourceView
        or source.view.profile != SOURCE_PROFILE
        or source.view.purpose is not _purpose(source.request.role)
        or source.schema_set_id != OWNER_SCHEMA_SET_ID
        or source.manifest_id != read_manifest_id(source.view.purpose)
    ):
        return False
    try:
        return source.view_id == endpoint_source_view_id(source.view)
    except (TypeError, ValueError):
        return False


def _extract_source_graph(basis: SupportedExtractionBasis) -> EndpointSemanticGraph:
    request = basis.request
    dependencies = _source_dependency_table(request)
    types = _source_type_table(request)
    layout = _source_spine_layout(request)
    abi = _source_abi(request, types, layout)
    plan = _source_plan(request, dependencies, types, layout, abi.invocation_refs)
    claims, anchors = _source_claims_and_anchors(request, layout, abi.invocation_refs)
    spine = _source_complete_spine(
        request, dependencies, types, layout, abi, plan, len(anchors)
    )
    static_fs = _source_static_fs(
        request, dependencies, types, layout, abi.invocation_refs
    )
    return EndpointSemanticGraph(
        request.role,
        dependencies,
        types,
        (),
        (),
        abi.graph,
        spine,
        static_fs,
        claims,
        anchors,
        plan.graph,
    )


def extract_endpoint_source_view(
    basis: object,
    *,
    work_limit: int = MAX_WORK,
) -> Answer:
    if type(work_limit) is not int or work_limit <= 0:
        return _answer(OutcomeKind.MALFORMED, reason="work limit must be positive")
    if not _is_live_support_basis(basis):
        return _answer(
            OutcomeKind.REFUSED, reason="missing affirmative support capability"
        )
    assert type(basis) is SupportedExtractionBasis
    request = basis.request
    try:
        graph = _extract_source_graph(basis)
        if len(canonical_bytes(graph)) > 1 << 20:
            return _answer(
                OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED,
                reason="source graph exceeds the canonical byte limit",
            )
        estimated_work = len(OWNER_SCHEMA_PATHS) + sum(
            len(value)
            for value in (
                graph.exact_used_dependencies,
                graph.value_types,
                graph.endpoint_spine,
                graph.claims,
                graph.anchored_obligations,
            )
        )
        if estimated_work > work_limit:
            return _answer(
                OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED,
                reason="source extraction exceeds the request work limit",
            )
        view = EndpointSourceView(SOURCE_PROFILE, basis.purpose, graph)
        checked = CheckedEndpointSourceView(
            _EXTRACTION_ISSUER,
            request,
            basis,
            basis.adapter,
            view,
            endpoint_source_view_id(view),
            basis.schema_set_id,
            basis.manifest_id,
        )
        _LIVE_CHECKED_SOURCE_VIEWS[id(checked)] = checked
        return _answer(OutcomeKind.AFFIRMATIVE, checked)
    except (KeyError, StopIteration, TypeError, ValueError) as error:
        # The owner surface was already admitted by the exact adequacy gate.
        # A later deterministic extractor disagreement is a checker defect,
        # never semantic evidence against ProjectionCorrect.
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"source extraction failed after owner admission: {error}",
        )


def derive_source_view(request: object, *, work_limit: int = MAX_WORK) -> Answer:
    support = classify_support(request, work_limit=work_limit)
    if support.kind is not OutcomeKind.AFFIRMATIVE:
        return support
    return extract_endpoint_source_view(support.value, work_limit=work_limit)


# ---------------------------------------------------------------------------
# Independently authored target construction
# ---------------------------------------------------------------------------


def _target_dependency_table(request: ProjectionRequest) -> tuple[Dependency, ...]:
    """Construct the target dependency table without consuming a source view."""

    assert request.construction is not None and request.future_owner is not None
    owner = request.future_owner
    identities: list[tuple[DependencyKind, object]] = [
        (
            DependencyKind.CONSTRUCTION,
            k2.construction_id(request.core, request.construction),
        ),
        (DependencyKind.CORE, k2.core_id(request.core)),
    ]
    identities.extend(
        (
            (DependencyKind.ALGORITHM, algorithm),
            (DependencyKind.EVALUATION, evaluation),
        )[which]
        for algorithm, evaluation in (
            (owner.fs.absorb_algorithm_id, owner.fs.absorb_evaluation_id),
            (owner.fs.squeeze_algorithm_id, owner.fs.squeeze_evaluation_id),
            (owner.fs.advance_algorithm_id, owner.fs.advance_evaluation_id),
        )
        for which in (0, 1)
    )
    for challenge in owner.fs.challenges:
        for algorithm, evaluation in (
            (challenge.accept_algorithm_id, challenge.accept_evaluation_id),
            (challenge.decode_algorithm_id, challenge.decode_evaluation_id),
        ):
            identities.append((DependencyKind.ALGORITHM, algorithm))
            identities.append((DependencyKind.EVALUATION, evaluation))
    for occurrence in request.core.schedule:
        operator_pairs: list[tuple[object, object]] = []
        if occurrence.guard.kind is not k2.PredicateKind.ALWAYS:
            operator_pairs.append(_predicate_pair("guard", occurrence.guard))
        if occurrence.kind is k2.OccurrenceKind.VERIFIER_MESSAGE:
            operator_pairs.append(_verifier_rule_pair(occurrence.verifier_rule))
        if occurrence.kind is k2.OccurrenceKind.CHECK:
            operator_pairs.append(_predicate_pair("check", occurrence.check_predicate))
        for algorithm, evaluation in operator_pairs:
            identities.append((DependencyKind.ALGORITHM, algorithm))
            identities.append((DependencyKind.EVALUATION, evaluation))
    selected_codec_keys = _selected_codec_keys(request)
    for codec in owner.interface.codecs:
        if codec.codec_key not in selected_codec_keys:
            continue
        if codec.kind is CodecKind.GENERAL:
            if codec.general_law_id is None:
                raise ValueError("General codec lacks an exact law dependency")
            identities.append((DependencyKind.CODEC_LAW, codec.general_law_id))
    if owner.plan is not None:
        for recipe in owner.plan.recipes:
            for node in recipe.nodes:
                identities.append((DependencyKind.ALGORITHM, node.algorithm_id))
                identities.append((DependencyKind.EVALUATION, node.evaluation_id))
    rows = tuple(_dependency(kind, identifier) for kind, identifier in identities)
    unique = {canonical_bytes(row): row for row in rows}
    return tuple(unique[key] for key in sorted(unique))


def _target_type_table(request: ProjectionRequest) -> tuple[ValueTypeAtom, ...]:
    assert request.future_owner is not None
    owner = request.future_owner
    candidates: list[object] = [
        owner.fs.state_type,
        owner.fs.bytes_type,
        owner.fs.natural_type,
    ]
    if any(item.kind is k2.OccurrenceKind.CHECK for item in request.core.schedule):
        candidates.append(k3.BOOL)
    for declaration in request.core.inputs:
        candidates.append(_sort_type(declaration.value_sort))
    for occurrence in request.core.schedule:
        if occurrence.kind is not k2.OccurrenceKind.TERMINAL:
            candidates.append(_occurrence_type(request.core, occurrence))
    selected_codec_keys = _selected_codec_keys(request)
    for codec in owner.interface.codecs:
        if codec.codec_key not in selected_codec_keys:
            continue
        for candidate in (codec.value_type, codec.external_type, codec.semantic_type):
            if candidate is not None:
                candidates.append(candidate)
    if request.plan is not None:
        candidates.extend(item.value_type for item in request.plan.private_material)
        candidates.extend(
            item.value_type for item in request.plan.randomness_requirements
        )
        candidates.extend(item.value_type for item in request.plan.persistent_state)
    if owner.plan is not None:
        for recipe in owner.plan.recipes:
            for node in recipe.nodes:
                candidates.append(node.output_type)
                candidates.extend(
                    item.literal_type
                    for item in node.inputs
                    if item.literal_type is not None
                )
    bodies = sorted({_type_body(candidate) for candidate in candidates})
    return tuple(ValueTypeAtom(body) for body in bodies)


def _target_spine_layout(request: ProjectionRequest) -> _SpineLayout:
    """Rebase source coordinates by a second, target-local traversal."""

    core = request.core
    scope_position = {item.name: index for index, item in enumerate(core.scopes)}
    occurrence_position = {item.name: index for index, item in enumerate(core.schedule)}
    pending_scopes: dict[int, list[object]] = {}
    for scope in core.scopes:
        boundary = (
            -1 if scope.open_before is None else occurrence_position[scope.open_before]
        )
        pending_scopes.setdefault(boundary, []).append(scope)
    reduction_boundary: dict[int, list[object]] = {}
    for reduction in core.reductions:
        reduction_boundary.setdefault(
            occurrence_position[reduction.at_occurrence], []
        ).append(reduction)

    events: list[SpineEvent] = [SpineEvent(SpineEventKind.FS_INITIALIZATION)]
    scope_refs: dict[str, int] = {}
    binding_refs: dict[str, int] = {}
    occurrence_refs: dict[str, int] = {}
    reduction_refs: dict[str, int] = {}
    selected_input_ref = {
        item.name: index
        for index, item in enumerate(
            declaration
            for declaration in core.inputs
            if _selected_input(declaration, request.role)
        )
    }

    def emit_scopes(boundary: int) -> None:
        for scope in pending_scopes.get(boundary, ()):
            path_names: list[str] = []
            cursor: object | None = scope
            by_name = {item.name: item for item in core.scopes}
            while cursor is not None:
                path_names.append(cursor.name)
                cursor = None if cursor.parent is None else by_name[cursor.parent]
            path_names.reverse()
            scope_refs[scope.name] = len(events)
            events.append(
                SpineEvent(
                    SpineEventKind.SCOPE_OPENING,
                    parent_scope_event_ref=(
                        None if scope.parent is None else scope_refs[scope.parent]
                    ),
                    original_scope_path=tuple(
                        scope_position[name] for name in path_names
                    ),
                    opens_before_occurrence_ordinal=(
                        None if boundary < 0 else boundary
                    ),
                )
            )
            for binding_ordinal, declaration in enumerate(core.inputs):
                if declaration.scope != scope.name or not _selected_input(
                    declaration, request.role
                ):
                    continue
                binding_refs[declaration.name] = len(events)
                events.append(
                    SpineEvent(
                        SpineEventKind.PUBLIC_BINDING,
                        scope_event_ref=scope_refs[scope.name],
                        original_binding_ordinal=binding_ordinal,
                        binding_class=declaration.role.value,
                        binding_value=GraphValueRef(
                            ValueRefKind.INVOCATION,
                            selected_input_ref[declaration.name],
                        ),
                    )
                )

    emit_scopes(-1)
    for ordinal, occurrence in enumerate(core.schedule):
        emit_scopes(ordinal)
        occurrence_refs[occurrence.name] = len(events)
        events.append(
            SpineEvent(
                SpineEventKind.CORE_OCCURRENCE,
                scope_event_ref=scope_refs[occurrence.scope],
                original_occurrence_ordinal=ordinal,
            )
        )
        for reduction in reduction_boundary.get(ordinal, ()):
            reduction_refs[reduction.name] = len(events)
            events.append(
                SpineEvent(
                    SpineEventKind.CORE_OCCURRENCE,
                    scope_event_ref=scope_refs[reduction.scope],
                )
            )
    return _SpineLayout(
        tuple(events),
        MappingProxyType(scope_refs),
        MappingProxyType(binding_refs),
        MappingProxyType(occurrence_refs),
        MappingProxyType(reduction_refs),
    )


def _target_value_ref(
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
    value_ref: object,
) -> GraphValueRef:
    if value_ref.kind is k2.RefKind.INPUT:
        return GraphValueRef(ValueRefKind.INVOCATION, invocation_refs[value_ref.name])
    return GraphValueRef(
        ValueRefKind.OCCURRENCE_OUTPUT,
        layout.occurrence_refs[value_ref.name],
        0,
    )


def _target_abi(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
) -> _AbiBuild:
    assert request.future_owner is not None
    owner = request.future_owner.interface
    selected_inputs = [
        item for item in request.core.inputs if _selected_input(item, request.role)
    ]
    invocation_refs = {item.name: index for index, item in enumerate(selected_inputs)}

    wanted_slots = {f"input:{item.name}" for item in selected_inputs}
    for transport in owner.transports:
        if (
            transport.source is not TransportActor.PUBLIC_DERIVATION
            or request.role is EndpointRole.VERIFIER
        ):
            wanted_slots.add(transport.slot_key)
    if request.role is EndpointRole.VERIFIER:
        wanted_slots |= {
            binding.slot_key
            for completion in owner.completions
            for binding in completion.bindings
        }
    slots_owner = [item for item in owner.slots if item.slot_key in wanted_slots]
    slot_refs = {item.slot_key: index for index, item in enumerate(slots_owner)}
    wanted_codecs = {item.codec_key for item in slots_owner}
    codecs_owner = [item for item in owner.codecs if item.codec_key in wanted_codecs]
    codec_refs = {item.codec_key: index for index, item in enumerate(codecs_owner)}

    codec_nodes: list[CodecNode] = []
    for item in codecs_owner:
        law_ref = None
        if item.general_law_id is not None:
            law_ref = _dep_index(
                dependencies, item.general_law_id, DependencyKind.CODEC_LAW
            )
        codec_nodes.append(
            CodecNode(
                item.kind,
                None
                if item.value_type is None
                else _type_index(types, item.value_type),
                None
                if item.external_type is None
                else _type_index(types, item.external_type),
                None
                if item.semantic_type is None
                else _type_index(types, item.semantic_type),
                tuple((ordinal, codec_refs[key]) for ordinal, key in item.children),
                law_ref,
                item.interface_codec_id,
            )
        )
    slots = tuple(
        AbiSlot(item.external_key, codec_refs[item.codec_key]) for item in slots_owner
    )
    targets = tuple(
        InvocationTarget(
            InvocationClass.VERIFIER_PRIVATE
            if item.role is k2.InputRole.VERIFIER_PRIVATE
            else InvocationClass.PUBLIC,
            _type_index(types, _sort_type(item.value_sort)),
        )
        for item in selected_inputs
    )
    fibres: list[InvocationFibre] = []
    for fibre in owner.invocation_fibres:
        if fibre.slot_key not in slot_refs:
            continue
        target_refs = tuple(
            invocation_refs[name]
            for name in fibre.invocation_inputs
            if name in invocation_refs
        )
        if target_refs:
            fibres.append(InvocationFibre(slot_refs[fibre.slot_key], target_refs))
    aliases = tuple(
        StatementAlias(
            slot_refs[item.slot_key],
            layout.binding_refs[item.binding_input],
            item.flow,
            None
            if item.invocation_input is None
            else invocation_refs[item.invocation_input],
            item.external_statement,
        )
        for item in owner.statement_aliases
        if item.slot_key in slot_refs and item.binding_input in layout.binding_refs
    )
    transports: list[TransportEdge] = []
    by_occurrence: dict[str, list[int]] = {}
    for item in owner.transports:
        if item.slot_key not in slot_refs:
            continue
        target = layout.occurrence_refs[item.occurrence]
        by_occurrence.setdefault(item.occurrence, []).append(len(transports))
        transports.append(
            TransportEdge(
                target,
                item.source,
                item.destination,
                slot_refs[item.slot_key],
            )
        )
    completions: list[CompletionVariant] = []
    if request.role is EndpointRole.VERIFIER:
        for item in owner.completions:
            terminal = (
                None
                if item.terminal_occurrence is None
                else layout.occurrence_refs[item.terminal_occurrence]
            )
            completions.append(
                CompletionVariant(
                    item.target,
                    terminal,
                    item.external_tag,
                    tuple(
                        sorted(
                            (
                                (
                                    CompletionCoordinate(
                                        binding.coordinate,
                                        terminal
                                        if binding.coordinate
                                        is CompletionCoordinateKind.TERMINAL_OUTPUT
                                        else None,
                                        binding.output_ordinal,
                                    ),
                                    slot_refs[binding.slot_key],
                                )
                                for binding in item.bindings
                            ),
                            key=lambda pair: canonical_bytes(pair[0]),
                        )
                    ),
                )
            )
    return _AbiBuild(
        RoleAbiGraph(
            tuple(codec_nodes),
            slots,
            targets,
            tuple(fibres),
            aliases,
            tuple(transports),
            tuple(completions),
        ),
        MappingProxyType(invocation_refs),
        MappingProxyType({key: tuple(value) for key, value in by_occurrence.items()}),
    )


def _target_plan(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> _PlanBuild:
    if request.role is EndpointRole.VERIFIER:
        return _PlanBuild(None, MappingProxyType({}))
    assert request.plan is not None
    assert request.future_owner is not None and request.future_owner.plan is not None
    owner = request.future_owner.plan
    recipe_order = sorted(
        owner.recipes, key=lambda item: layout.occurrence_refs[item.decision]
    )
    decision_refs = {
        recipe.decision: layout.occurrence_refs[recipe.decision]
        for recipe in recipe_order
    }

    private_names: set[str] = set()
    random_names: set[str] = set()
    state_names: set[str] = set()
    for recipe in recipe_order:
        for node in recipe.nodes:
            for operand in node.inputs:
                if operand.kind is PlanOperandKind.PRIVATE_MATERIAL:
                    private_names.add(operand.name)
                elif operand.kind is PlanOperandKind.PRIVATE_RANDOMNESS:
                    random_names.add(operand.name)
                elif operand.kind is PlanOperandKind.STATE_BEFORE:
                    state_names.add(operand.name)
        state_names.update(name for name, _kind, _value in recipe.state_after)
    state_decl = {item.name: item for item in request.plan.persistent_state}
    for name in tuple(state_names):
        initializer = state_decl[name].initial_private_material
        if initializer is not None:
            private_names.add(initializer)
    private_decl = [
        item for item in request.plan.private_material if item.key in private_names
    ]
    random_decl = [
        item
        for item in request.plan.randomness_requirements
        if item.name in random_names
    ]
    states = [
        item for item in request.plan.persistent_state if item.name in state_names
    ]
    private_refs = {item.key: index for index, item in enumerate(private_decl)}
    random_refs = {item.name: index for index, item in enumerate(random_decl)}
    state_refs = {item.name: index for index, item in enumerate(states)}
    node_refs: dict[tuple[str, int], int] = {}
    for recipe in recipe_order:
        for ordinal, _node in enumerate(recipe.nodes):
            node_refs[(recipe.decision, ordinal)] = len(node_refs)

    input_decl = {item.name: item for item in request.core.inputs}
    occurrence_decl = {item.name: item for item in request.core.schedule}
    private_by_name = {item.key: item for item in request.plan.private_material}
    random_by_name = {item.name: item for item in request.plan.randomness_requirements}

    def translate(operand: OwnerPlanOperand, decision: str) -> PlanValueRef:
        if operand.kind is PlanOperandKind.PRIVATE_MATERIAL:
            declaration = private_by_name[operand.name]
            return PlanValueRef(
                operand.kind,
                private_refs[operand.name],
                _type_index(types, declaration.value_type),
            )
        if operand.kind is PlanOperandKind.PRIVATE_RANDOMNESS:
            declaration = random_by_name[operand.name]
            return PlanValueRef(
                operand.kind,
                random_refs[operand.name],
                _type_index(types, declaration.value_type),
            )
        if operand.kind is PlanOperandKind.STATE_BEFORE:
            declaration = state_decl[operand.name]
            return PlanValueRef(
                operand.kind,
                state_refs[operand.name],
                _type_index(types, declaration.value_type),
            )
        if operand.kind is PlanOperandKind.VIEW_PUBLIC_INPUT:
            declaration = input_decl[operand.name]
            return PlanValueRef(
                operand.kind,
                invocation_refs[operand.name],
                _type_index(types, _sort_type(declaration.value_sort)),
            )
        if operand.kind is PlanOperandKind.VIEW_OCCURRENCE:
            occurrence = occurrence_decl[operand.name]
            return PlanValueRef(
                operand.kind,
                layout.occurrence_refs[operand.name],
                _type_index(types, _occurrence_type(request.core, occurrence)),
            )
        if operand.kind is PlanOperandKind.NODE_OUTPUT:
            if operand.node_ordinal is None:
                raise ValueError("target node output has no ordinal")
            recipe = next(item for item in recipe_order if item.decision == decision)
            return PlanValueRef(
                operand.kind,
                node_refs[(decision, operand.node_ordinal)],
                _type_index(types, recipe.nodes[operand.node_ordinal].output_type),
            )
        if operand.kind is PlanOperandKind.CONSTANT:
            if operand.literal_type is None:
                raise ValueError("target literal has no type")
            return PlanValueRef(
                operand.kind,
                0,
                _type_index(types, operand.literal_type),
                operand.literal,
            )
        raise ValueError("target encountered an unknown Plan operand")

    private_graph = tuple(
        PlanPrivateMaterial(item.kind.value, _type_index(types, item.value_type))
        for item in private_decl
    )
    random_graph = tuple(
        PlanRandomness(
            _type_index(types, item.value_type),
            decision_refs[item.first_available_at],
        )
        for item in random_decl
    )
    state_graph = tuple(
        PlanState(
            _type_index(types, item.value_type),
            PlanValueRef(
                PlanOperandKind.PRIVATE_MATERIAL,
                private_refs[item.initial_private_material],
                _type_index(types, item.value_type),
            ),
        )
        for item in states
        if item.initial_private_material is not None
    )
    if len(state_graph) != len(states):
        raise ValueError("bounded target Plan state lacks a typed initializer")

    nodes: list[PlanRecipeNode] = []
    moves: list[PlanMove] = []
    updates: list[PlanUpdate] = []
    for recipe in recipe_order:
        decision_ref = decision_refs[recipe.decision]
        for node in recipe.nodes:
            nodes.append(
                PlanRecipeNode(
                    decision_ref,
                    _dep_index(
                        dependencies, node.algorithm_id, DependencyKind.ALGORITHM
                    ),
                    _dep_index(
                        dependencies, node.evaluation_id, DependencyKind.EVALUATION
                    ),
                    tuple(translate(item, recipe.decision) for item in node.inputs),
                    _type_index(types, node.output_type),
                )
            )
        moves.append(
            PlanMove(
                decision_ref,
                recipe.move_kind,
                translate(recipe.move, recipe.decision),
            )
        )
        updates.extend(
            PlanUpdate(
                decision_ref,
                state_refs[state_name],
                kind,
                None if value is None else translate(value, recipe.decision),
            )
            for state_name, kind, value in recipe.state_after
        )
    return _PlanBuild(
        PlanGraph(
            private_graph,
            random_graph,
            state_graph,
            tuple(nodes),
            tuple(moves),
            tuple(updates),
        ),
        MappingProxyType(decision_refs),
    )


def _target_claims_and_anchors(
    request: ProjectionRequest,
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> tuple[tuple[ClaimAtom, ...], tuple[AnchoredObligation, ...]]:
    assert request.future_owner is not None
    owner = request.future_owner.core
    claim_refs = {item.claim_key: index for index, item in enumerate(owner.claims)}
    claims: list[ClaimAtom] = []
    for item in owner.claims:
        if item.source_kind is ClaimSourceKind.BINDING:
            source_ref = layout.binding_refs[item.source_name]
        else:
            source_ref = layout.reduction_refs[item.source_name]
        claims.append(
            ClaimAtom(
                item.contract_ref,
                item.usage,
                layout.scope_refs[item.scope],
                item.source_kind,
                source_ref,
                item.output_ordinal,
            )
        )
    challenge_refs = {
        occurrence.name: index
        for index, occurrence in enumerate(
            item
            for item in request.core.schedule
            if item.kind is k2.OccurrenceKind.CHALLENGE
        )
    }
    reduction_owner = {item.reduction_name: item for item in owner.reductions}
    anchors: list[AnchoredObligation] = []
    for reduction in request.core.reductions:
        anchors.append(
            AnchoredObligation(
                AnchorKind.REDUCTION,
                reduction_owner[reduction.name].contract_ref,
                layout.scope_refs[reduction.scope],
                layout.reduction_refs[reduction.name],
                tuple(claim_refs[name] for name in reduction.input_claims),
                tuple(
                    _target_value_ref(layout, invocation_refs, ref)
                    for ref in reduction.side_inputs
                ),
                tuple(challenge_refs[name] for name in reduction.required_challenges),
                tuple(
                    ReductionPublication(
                        layout.occurrence_refs[item.publication],
                        None
                        if item.next_challenge is None
                        else challenge_refs[item.next_challenge],
                    )
                    for item in reduction.required_publications
                ),
                tuple(
                    ReductionOutputRow(
                        output_ordinal,
                        contract_ref,
                        tuple(
                            claim_refs[claim.claim_key]
                            for claim in owner.claims
                            if claim.source_kind is ClaimSourceKind.REDUCTION_OUTPUT
                            and claim.source_name == reduction.name
                            and claim.output_ordinal == output_ordinal
                        ),
                    )
                    for output_ordinal, contract_ref in enumerate(
                        reduction_owner[reduction.name].output_contracts
                    )
                ),
                None,
                None,
                (),
                (),
                (),
            )
        )
    terminal = owner.terminal
    anchors.append(
        AnchoredObligation(
            AnchorKind.TERMINAL,
            None,
            None,
            None,
            (),
            (),
            (),
            (),
            (),
            layout.occurrence_refs[terminal.terminal_occurrence],
            terminal.verdict,
            tuple(
                _target_value_ref(layout, invocation_refs, ref)
                for ref in terminal.public_outputs
            ),
            tuple(layout.occurrence_refs[name] for name in terminal.required_checks),
            tuple(
                (claim_refs[name], disposition)
                for name, disposition in terminal.claim_dispositions
            ),
        )
    )
    return tuple(claims), tuple(anchors)


def _target_static_fs(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    invocation_refs: Mapping[str, int],
) -> StaticFsSemantics:
    assert request.construction is not None and request.future_owner is not None
    construction = request.construction
    owner = request.future_owner.fs
    core_ref = _dep_index(dependencies, k2.core_id(request.core), DependencyKind.CORE)
    construction_ref = _dep_index(
        dependencies,
        k2.construction_id(request.core, construction),
        DependencyKind.CONSTRUCTION,
    )
    challenge_owner = {item.occurrence: item for item in owner.challenges}
    challenge_laws: list[ChallengeLaw] = []
    for ordinal in range(len(request.core.schedule)):
        occurrence = request.core.schedule[ordinal]
        if occurrence.kind is not k2.OccurrenceKind.CHALLENGE:
            continue
        assert occurrence.challenge_domain is not None
        declaration = challenge_owner[occurrence.name]
        result_type = _type_index(types, _occurrence_type(request.core, occurrence))
        challenge_laws.append(
            ChallengeLaw(
                ordinal,
                result_type,
                declaration.domain_ref,
                declaration.fresh_law_ref,
                declaration.correlation,
                declaration.reduction_use,
                tuple(
                    _target_value_ref(layout, invocation_refs, item)
                    for item in occurrence.dependencies
                ),
                construction.sample_bytes,
                construction.max_attempts,
                _dep_index(
                    dependencies,
                    declaration.accept_algorithm_id,
                    DependencyKind.ALGORITHM,
                ),
                _dep_index(
                    dependencies,
                    declaration.accept_evaluation_id,
                    DependencyKind.EVALUATION,
                ),
                _dep_index(
                    dependencies,
                    declaration.decode_algorithm_id,
                    DependencyKind.ALGORITHM,
                ),
                _dep_index(
                    dependencies,
                    declaration.decode_evaluation_id,
                    DependencyKind.EVALUATION,
                ),
            )
        )
    return StaticFsSemantics(
        core_ref,
        construction_ref,
        _type_index(types, owner.state_type),
        _type_index(types, owner.bytes_type),
        _type_index(types, owner.natural_type),
        owner.initial_state,
        _dep_index(dependencies, owner.absorb_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(dependencies, owner.absorb_evaluation_id, DependencyKind.EVALUATION),
        _dep_index(dependencies, owner.squeeze_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(
            dependencies, owner.squeeze_evaluation_id, DependencyKind.EVALUATION
        ),
        _dep_index(dependencies, owner.advance_algorithm_id, DependencyKind.ALGORITHM),
        _dep_index(
            dependencies, owner.advance_evaluation_id, DependencyKind.EVALUATION
        ),
        construction.application_domain,
        owner.sampling_exhausted_failure,
        "K2DerivedPrefixLawV0",
        "K2AdvanceBeforeAcceptRetryLawV0",
        tuple(challenge_laws),
    )


def _target_complete_spine(
    request: ProjectionRequest,
    dependencies: tuple[Dependency, ...],
    types: tuple[ValueTypeAtom, ...],
    layout: _SpineLayout,
    abi: _AbiBuild,
    plan: _PlanBuild,
    anchors: tuple[AnchoredObligation, ...],
) -> tuple[SpineEvent, ...]:
    occurrence_name = {ref: name for name, ref in layout.occurrence_refs.items()}
    reduction_name = {ref: name for name, ref in layout.reduction_refs.items()}
    occurrence_map = {item.name: item for item in request.core.schedule}
    reduction_map = {item.name: item for item in request.core.reductions}
    challenge_refs = {
        item.name: index
        for index, item in enumerate(
            candidate
            for candidate in request.core.schedule
            if candidate.kind is k2.OccurrenceKind.CHALLENGE
        )
    }
    completed: list[SpineEvent] = []
    for ref, skeleton in enumerate(layout.events):
        if skeleton.kind is not SpineEventKind.CORE_OCCURRENCE:
            completed.append(skeleton)
            continue
        if ref in reduction_name:
            name = reduction_name[ref]
            _ = reduction_map[name]
            completed.append(replace(skeleton, action=ReductionAction()))
            continue
        occurrence = occurrence_map[occurrence_name[ref]]
        if occurrence.guard.kind is k2.PredicateKind.ALWAYS:
            activity = Activity()
        else:
            guard_algorithm, guard_evaluation = _predicate_pair(
                "guard", occurrence.guard
            )
            activity = Activity(
                _dep_index(dependencies, guard_algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, guard_evaluation, DependencyKind.EVALUATION),
                tuple(
                    _target_value_ref(layout, abi.invocation_refs, item)
                    for item in occurrence.guard.refs
                ),
            )
        if occurrence.kind is k2.OccurrenceKind.PROVER_MESSAGE:
            edges = abi.transport_refs.get(occurrence.name, ())
            if len(edges) != 1:
                raise ValueError("target prover message transport is not exact")
            action: SpineAction = ProverMessageAction(
                _id_text(
                    _fixed_ref("pir.message-channel", f"channel:{occurrence.name}")
                ),
                _type_index(types, _occurrence_type(request.core, occurrence)),
            )
        elif occurrence.kind is k2.OccurrenceKind.VERIFIER_MESSAGE:
            edges = abi.transport_refs.get(occurrence.name, ())
            if len(edges) != 1:
                raise ValueError("target verifier message transport is not exact")
            algorithm, evaluation = _verifier_rule_pair(occurrence.verifier_rule)
            action = VerifierMessageAction(
                _id_text(
                    _fixed_ref("pir.message-channel", f"channel:{occurrence.name}")
                ),
                _dep_index(dependencies, algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, evaluation, DependencyKind.EVALUATION),
                tuple(
                    _target_value_ref(layout, abi.invocation_refs, item)
                    for item in occurrence.dependencies
                ),
                _type_index(types, _occurrence_type(request.core, occurrence)),
            )
        elif occurrence.kind is k2.OccurrenceKind.CHALLENGE:
            action = ChallengeAction(challenge_refs[occurrence.name])
        elif occurrence.kind is k2.OccurrenceKind.CHECK:
            algorithm, evaluation = _predicate_pair("check", occurrence.check_predicate)
            action = CheckAction(
                _dep_index(dependencies, algorithm, DependencyKind.ALGORITHM),
                _dep_index(dependencies, evaluation, DependencyKind.EVALUATION),
                tuple(
                    _target_value_ref(layout, abi.invocation_refs, item)
                    for item in occurrence.check_predicate.refs
                ),
                _type_index(types, k3.BOOL),
            )
        elif occurrence.kind is k2.OccurrenceKind.TERMINAL:
            action = TerminalAction()
        else:
            raise ValueError("unsupported occurrence reached target construction")
        completed.append(replace(skeleton, activity=activity, action=action))
    return tuple(completed)


def _construct_target_graph(
    adapter: CheckedProjectionOwnerAdapter,
) -> EndpointSemanticGraph:
    if (
        type(adapter) is not CheckedProjectionOwnerAdapter
        or adapter._issuer is not _OWNER_ADAPTER_ISSUER
        or _LIVE_OWNER_ADAPTERS.get(id(adapter)) is not adapter
    ):
        raise ValueError("target construction lacks a checked owner adapter")
    request = adapter.request
    dependencies = _target_dependency_table(request)
    types = _target_type_table(request)
    layout = _target_spine_layout(request)
    abi = _target_abi(request, dependencies, types, layout)
    plan = _target_plan(request, dependencies, types, layout, abi.invocation_refs)
    claims, anchors = _target_claims_and_anchors(request, layout, abi.invocation_refs)
    spine = _target_complete_spine(
        request, dependencies, types, layout, abi, plan, anchors
    )
    static_fs = _target_static_fs(
        request, dependencies, types, layout, abi.invocation_refs
    )
    return EndpointSemanticGraph(
        request.role,
        dependencies,
        types,
        (),
        (),
        abi.graph,
        spine,
        static_fs,
        claims,
        anchors,
        plan.graph,
    )


def oir_endpoint_id(endpoint: OirEndpoint | EndpointSemanticGraph) -> object:
    if type(endpoint) is OirEndpoint:
        if endpoint.semantic_profile != OIR_PROFILE:
            raise TypeError("OIR endpoint names an unsupported language profile")
        graph = endpoint.semantic_graph
    else:
        graph = endpoint
    return _semantic_id("oir.endpoint", graph)


def remint(endpoint: OirEndpoint) -> OirEndpoint:
    provisional = OirEndpoint(endpoint.semantic_profile, endpoint.semantic_graph, None)
    return replace(provisional, asserted_id=oir_endpoint_id(provisional))


def project_supported_endpoint(basis: object) -> Answer:
    """Construct one candidate from the exact basis used by both graph lanes."""

    if type(basis) is not SupportedExtractionBasis:
        return _answer(
            OutcomeKind.MALFORMED,
            reason="wrong supported-extraction-basis carrier",
        )
    if not _is_live_support_basis(basis):
        return _answer(
            OutcomeKind.REFUSED,
            reason="target construction lacks a live supported extraction basis",
        )
    try:
        graph = _construct_target_graph(basis.adapter)
        if len(canonical_bytes(graph)) > 1 << 20:
            return _answer(
                OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED,
                reason="target graph exceeds the canonical byte limit",
            )
        return _answer(
            OutcomeKind.AFFIRMATIVE,
            remint(OirEndpoint(OIR_PROFILE, graph, None)),
        )
    except (KeyError, StopIteration, TypeError, ValueError) as error:
        # Target construction is an implementation step preceding local OIR
        # admission and proposition formation.  It cannot produce a semantic
        # counterexample to a proposition that has not been formed.
        return _answer(
            OutcomeKind.CHECKER_FAILURE,
            reason=f"target construction failed after source admission: {error}",
        )


def project(request: object, *, work_limit: int = MAX_WORK) -> Answer:
    """Convenience wrapper that classifies once, then projects its exact basis."""

    support = classify_support(request, work_limit=work_limit)
    if support.kind is not OutcomeKind.AFFIRMATIVE:
        return support
    return project_supported_endpoint(support.value)


# ---------------------------------------------------------------------------
# Source-blind local OIR admission
# ---------------------------------------------------------------------------


def _require_index(index: object, size: int, what: str) -> int:
    if type(index) is not int or not 0 <= index < size:
        raise ValueError(f"{what} is outside its owner-local table")
    return index


def _occurrence_output_type(graph: EndpointSemanticGraph, spine_ref: int) -> int:
    event = graph.endpoint_spine[
        _require_index(spine_ref, len(graph.endpoint_spine), "spine ref")
    ]
    action = event.action
    if type(action) is ProverMessageAction:
        return action.value_type_ref
    if type(action) is VerifierMessageAction:
        return action.result_type_ref
    if type(action) is ChallengeAction:
        return graph.static_fs_semantics.challenge_laws[
            action.challenge_law_ref
        ].value_type_ref
    if type(action) is CheckAction:
        return action.result_type_ref
    raise ValueError("this spine action has no endpoint value output")


def _graph_value_type(graph: EndpointSemanticGraph, value: GraphValueRef) -> int:
    if type(value) is not GraphValueRef or type(value.kind) is not ValueRefKind:
        raise ValueError("endpoint value ref has the wrong exact shape")
    if value.kind is ValueRefKind.INVOCATION:
        _require_index(
            value.ref,
            len(graph.role_abi_graph.invocation_targets),
            "invocation target ref",
        )
        if value.output_ordinal != 0:
            raise ValueError("invocation ref carries foreign coordinates")
        return graph.role_abi_graph.invocation_targets[value.ref].type_ref
    if value.kind is ValueRefKind.CONSTANT:
        _require_index(value.ref, len(graph.constants), "constant ref")
        if value.output_ordinal != 0:
            raise ValueError("constant ref carries foreign coordinates")
        return graph.constants[value.ref].type_ref
    if value.kind is ValueRefKind.PURE_NODE:
        _require_index(value.ref, len(graph.pure_nodes), "pure-node ref")
        if value.output_ordinal != 0:
            raise ValueError("pure-node ref carries foreign coordinates")
        return graph.pure_nodes[value.ref].result_type_ref
    if value.kind is ValueRefKind.OCCURRENCE_OUTPUT:
        if value.output_ordinal != 0:
            raise ValueError("bounded occurrence outputs have only ordinal zero")
        return _occurrence_output_type(graph, value.ref)
    raise ValueError("unknown endpoint value-ref kind")


def _validate_value_ref(
    graph: EndpointSemanticGraph,
    value: GraphValueRef,
    *,
    before_spine_ref: int | None = None,
    expected_type: int | None = None,
) -> None:
    actual_type = _graph_value_type(graph, value)
    _require_index(actual_type, len(graph.value_types), "value type ref")
    if expected_type is not None and actual_type != expected_type:
        raise ValueError("endpoint value ref has the wrong exact type")
    if (
        before_spine_ref is not None
        and value.kind is ValueRefKind.OCCURRENCE_OUTPUT
        and value.ref >= before_spine_ref
    ):
        raise ValueError("endpoint occurrence output does not point backward")


def _validate_role_abi(graph: EndpointSemanticGraph) -> None:
    abi = graph.role_abi_graph
    for index, codec in enumerate(abi.codec_nodes):
        if type(codec.kind) is not CodecKind:
            raise ValueError("codec has an unknown kind")
        _id_text(codec.interface_codec_id, "foundation.canonical-algorithm")
        if codec.kind is CodecKind.IDENTITY:
            if codec.value_type_ref is None:
                raise ValueError("Identity codec lacks its value type")
            _require_index(codec.value_type_ref, len(graph.value_types), "codec type")
            if (
                any(
                    item is not None
                    for item in (
                        codec.external_type_ref,
                        codec.semantic_type_ref,
                        codec.general_law_dependency,
                    )
                )
                or codec.children
            ):
                raise ValueError("Identity codec carries another codec variant")
        elif codec.kind is CodecKind.GENERAL:
            if codec.general_law_dependency is None:
                raise ValueError("General codec lacks a law dependency")
            _require_index(
                codec.general_law_dependency,
                len(graph.exact_used_dependencies),
                "General codec law",
            )
        else:
            for ordinal, child in codec.children:
                if type(ordinal) is not int or ordinal < 0:
                    raise ValueError("structural codec child ordinal is malformed")
                if child >= index:
                    raise ValueError("structural codec child must point backward")
    external_keys = tuple(item.external_key for item in abi.slots)
    if len(external_keys) != len(set(external_keys)):
        raise ValueError("ABI external slot keys are not unique")
    for slot in abi.slots:
        _require_index(slot.codec_ref, len(abi.codec_nodes), "slot codec ref")
    covered_targets: list[int] = []
    for fibre in abi.invocation_fibres:
        _require_index(fibre.slot_ref, len(abi.slots), "fibre slot")
        if not fibre.target_refs:
            raise ValueError("invocation fibre must be nonempty")
        for target in fibre.target_refs:
            _require_index(target, len(abi.invocation_targets), "invocation target")
            covered_targets.append(target)
    if covered_targets != list(range(len(abi.invocation_targets))):
        raise ValueError("invocation fibres do not exactly partition targets in order")
    for target in abi.invocation_targets:
        if type(target.invocation_class) is not InvocationClass:
            raise ValueError("invocation target has an unknown class")
        _require_index(target.type_ref, len(graph.value_types), "invocation type")
        if (
            graph.role is EndpointRole.PROVER
            and target.invocation_class is InvocationClass.VERIFIER_PRIVATE
        ):
            raise ValueError("Prover ABI contains a verifier-private invocation target")
    statement_slots: set[int] = set()
    external_statements: set[str] = set()
    for alias in abi.statement_aliases:
        _require_index(alias.slot_ref, len(abi.slots), "Statement slot")
        _require_index(
            alias.binding_spine_ref, len(graph.endpoint_spine), "Statement binding"
        )
        if (
            graph.endpoint_spine[alias.binding_spine_ref].kind
            is not SpineEventKind.PUBLIC_BINDING
        ):
            raise ValueError("Statement alias does not name a binding event")
        if alias.slot_ref in statement_slots:
            raise ValueError("Statement slot has duplicate aliases")
        statement_slots.add(alias.slot_ref)
        if (
            type(alias.external_statement) is not str
            or not alias.external_statement
            or alias.external_statement in external_statements
        ):
            raise ValueError("external Statement name is malformed or duplicated")
        external_statements.add(alias.external_statement)
        if alias.flow is StatementFlowKind.SUPPLIES_INVOCATION:
            if alias.invocation_target_ref is None:
                raise ValueError("Supplying Statement lacks an invocation target")
            _require_index(
                alias.invocation_target_ref,
                len(abi.invocation_targets),
                "Statement invocation target",
            )
        elif alias.invocation_target_ref is not None:
            raise ValueError("opened-binding Statement carries an invocation target")
    transport_targets: set[tuple[int, TransportActor]] = set()
    for edge in abi.transport_edges:
        _require_index(
            edge.target_spine_ref, len(graph.endpoint_spine), "transport target"
        )
        _require_index(edge.slot_ref, len(abi.slots), "transport slot")
        action = graph.endpoint_spine[edge.target_spine_ref].action
        if edge.source is TransportActor.PROVER:
            if type(action) is not ProverMessageAction:
                raise ValueError("Prover transport does not target a Prover message")
        elif edge.source is TransportActor.VERIFIER:
            if type(action) is not VerifierMessageAction:
                raise ValueError(
                    "Verifier transport does not target a Verifier message"
                )
        elif (
            type(action) is not ChallengeAction
            or edge.destination is not TransportDestination.EXTERNAL_APPLICATION
            or graph.role is not EndpointRole.VERIFIER
        ):
            raise ValueError(
                "public derivation has the wrong target, destination, or owner"
            )
        key = (edge.target_spine_ref, edge.source)
        if key in transport_targets:
            raise ValueError("transport target/actor pair is duplicated")
        transport_targets.add(key)
    completion_tags = tuple(item.external_tag for item in abi.completion_variants)
    if len(completion_tags) != len(set(completion_tags)):
        raise ValueError("completion tags are duplicated")
    if graph.role is EndpointRole.PROVER and abi.completion_variants:
        raise ValueError("Prover ABI invents a semantic completion")
    for completion in abi.completion_variants:
        if type(completion.external_tag) is not str or not completion.external_tag:
            raise ValueError("completion envelope lacks its external tag")
        if completion.target is CompletionTargetKind.CORE_TERMINAL:
            if completion.terminal_spine_ref is None:
                raise ValueError("terminal completion lacks its terminal")
            _require_index(
                completion.terminal_spine_ref,
                len(graph.endpoint_spine),
                "completion terminal",
            )
        elif completion.terminal_spine_ref is not None:
            raise ValueError("FS failure completion carries a terminal ref")
        for coordinate, slot_ref in completion.payload_bindings:
            if type(coordinate.kind) is not CompletionCoordinateKind:
                raise ValueError("completion coordinate kind is malformed")
            _require_index(slot_ref, len(abi.slots), "completion slot")
        coordinates = tuple(item[0] for item in completion.payload_bindings)
        if len(coordinates) != len(set(coordinates)):
            raise ValueError("completion payload coordinates are duplicated")
        if coordinates != tuple(sorted(coordinates, key=canonical_bytes)):
            raise ValueError("completion payload coordinates are not canonical")
    slot_uses = {item.slot_ref for item in abi.invocation_fibres}
    slot_uses.update(item.slot_ref for item in abi.statement_aliases)
    slot_uses.update(item.slot_ref for item in abi.transport_edges)
    slot_uses.update(
        slot_ref
        for completion in abi.completion_variants
        for _coordinate, slot_ref in completion.payload_bindings
    )
    if slot_uses != set(range(len(abi.slots))):
        raise ValueError("ABI slot table contains a phantom or omitted use")


def _validate_spine(graph: EndpointSemanticGraph) -> None:
    spine = graph.endpoint_spine
    if not spine or spine[0] != SpineEvent(SpineEventKind.FS_INITIALIZATION):
        raise ValueError("spine must begin with one exact FS initialization")
    if sum(item.kind is SpineEventKind.FS_INITIALIZATION for item in spine) != 1:
        raise ValueError("spine has duplicate FS initialization")
    binding_ordinals: set[int] = set()
    occurrence_ordinals: set[int] = set()
    terminal_refs: list[int] = []
    for ref, event in enumerate(spine):
        if type(event.kind) is not SpineEventKind:
            raise ValueError("spine event kind is malformed")
        if event.kind is SpineEventKind.SCOPE_OPENING:
            if not event.original_scope_path:
                raise ValueError("scope event lacks an original K2 path")
            if event.parent_scope_event_ref is not None:
                _require_index(event.parent_scope_event_ref, ref, "scope parent")
                if (
                    spine[event.parent_scope_event_ref].kind
                    is not SpineEventKind.SCOPE_OPENING
                ):
                    raise ValueError("scope parent does not name a scope event")
            if event.action is not None:
                raise ValueError("scope event carries a Core action")
        elif event.kind is SpineEventKind.PUBLIC_BINDING:
            if (
                event.scope_event_ref is None
                or event.original_binding_ordinal is None
                or not event.binding_class
                or event.binding_value is None
            ):
                raise ValueError("binding event lacks its source coordinates")
            _require_index(event.scope_event_ref, ref, "binding scope")
            if event.original_binding_ordinal in binding_ordinals:
                raise ValueError("binding ordinal is duplicated")
            binding_ordinals.add(event.original_binding_ordinal)
            _validate_value_ref(graph, event.binding_value, before_spine_ref=ref)
            if event.action is not None:
                raise ValueError("binding event carries a Core action")
        elif event.kind is SpineEventKind.CORE_OCCURRENCE:
            if event.scope_event_ref is None or event.action is None:
                raise ValueError("Core occurrence lacks scope or action")
            _require_index(event.scope_event_ref, ref, "occurrence scope")
            if event.original_occurrence_ordinal is not None:
                if event.original_occurrence_ordinal in occurrence_ordinals:
                    raise ValueError("original occurrence ordinal is duplicated")
                occurrence_ordinals.add(event.original_occurrence_ordinal)
            if event.activity.algorithm_dependency is None:
                if (
                    event.activity.evaluation_dependency is not None
                    or event.activity.inputs
                ):
                    raise ValueError("Always activity carries guard material")
            else:
                _require_index(
                    event.activity.algorithm_dependency,
                    len(graph.exact_used_dependencies),
                    "guard algorithm",
                )
                _require_index(
                    event.activity.evaluation_dependency,
                    len(graph.exact_used_dependencies),
                    "guard evaluation",
                )
                for value in event.activity.inputs:
                    _validate_value_ref(graph, value, before_spine_ref=ref)
            action = event.action
            if type(action) is ProverMessageAction:
                _require_index(
                    action.value_type_ref, len(graph.value_types), "message type"
                )
                matching = tuple(
                    edge
                    for edge in graph.role_abi_graph.transport_edges
                    if edge.target_spine_ref == ref
                    and edge.source is TransportActor.PROVER
                )
                if len(matching) != 1:
                    raise ValueError("prover action lacks one exact ABI transport")
            elif type(action) is VerifierMessageAction:
                for dependency in (
                    action.algorithm_dependency,
                    action.evaluation_dependency,
                ):
                    _require_index(
                        dependency,
                        len(graph.exact_used_dependencies),
                        "verifier-message dependency",
                    )
                for value in action.inputs:
                    _validate_value_ref(graph, value, before_spine_ref=ref)
                _require_index(
                    action.result_type_ref,
                    len(graph.value_types),
                    "message result type",
                )
                matching = tuple(
                    edge
                    for edge in graph.role_abi_graph.transport_edges
                    if edge.target_spine_ref == ref
                    and edge.source is TransportActor.VERIFIER
                )
                if len(matching) != 1:
                    raise ValueError("verifier action lacks one exact ABI transport")
            elif type(action) is ChallengeAction:
                _require_index(
                    action.challenge_law_ref,
                    len(graph.static_fs_semantics.challenge_laws),
                    "challenge law",
                )
            elif type(action) is CheckAction:
                for dependency in (
                    action.algorithm_dependency,
                    action.evaluation_dependency,
                ):
                    _require_index(
                        dependency,
                        len(graph.exact_used_dependencies),
                        "check dependency",
                    )
                for value in action.inputs:
                    _validate_value_ref(graph, value, before_spine_ref=ref)
                _require_index(
                    action.result_type_ref, len(graph.value_types), "check result type"
                )
            elif type(action) is ReductionAction:
                if event.original_occurrence_ordinal is not None:
                    raise ValueError(
                        "derived reduction event masquerades as a K2 occurrence"
                    )
            elif type(action) is TerminalAction:
                terminal_refs.append(ref)
            else:
                raise ValueError("Core occurrence has an unknown action")
    if terminal_refs != [len(spine) - 1]:
        raise ValueError("endpoint spine lacks one final terminal closure")


def _validate_fs(graph: EndpointSemanticGraph) -> None:
    fs = graph.static_fs_semantics
    for dependency in (
        fs.core_dependency,
        fs.construction_dependency,
        fs.absorb_algorithm_dependency,
        fs.absorb_evaluation_dependency,
        fs.squeeze_algorithm_dependency,
        fs.squeeze_evaluation_dependency,
        fs.advance_algorithm_dependency,
        fs.advance_evaluation_dependency,
    ):
        _require_index(dependency, len(graph.exact_used_dependencies), "FS dependency")
    for type_ref in (fs.state_type_ref, fs.bytes_type_ref, fs.natural_type_ref):
        _require_index(type_ref, len(graph.value_types), "FS value type")
    if fs.derived_prefix_law != "K2DerivedPrefixLawV0":
        raise ValueError("unknown FS prefix law")
    if fs.challenge_transition_law != "K2AdvanceBeforeAcceptRetryLawV0":
        raise ValueError("unknown FS challenge-transition law")
    actions: list[tuple[int, ChallengeAction]] = []
    for ref, event in enumerate(graph.endpoint_spine):
        if type(event.action) is ChallengeAction:
            actions.append((ref, event.action))
    if tuple(action.challenge_law_ref for _ref, action in actions) != tuple(
        range(len(fs.challenge_laws))
    ):
        raise ValueError("challenge actions do not cover static laws exactly")
    for (spine_ref, action), law in zip(actions, fs.challenge_laws, strict=True):
        event = graph.endpoint_spine[spine_ref]
        if event.original_occurrence_ordinal != law.original_challenge_ordinal:
            raise ValueError("challenge law loses its original K2 ordinal")
        if event.scope_event_ref is None:
            raise ValueError("challenge action has no exact scope event")
        scope = graph.endpoint_spine[event.scope_event_ref]
        if (
            scope.kind is not SpineEventKind.SCOPE_OPENING
            or not scope.original_scope_path
        ):
            raise ValueError("challenge namespace has no exact root-to-scope path")
        if law.draw_bytes <= 0 or law.maximum_draws <= 0:
            raise ValueError("challenge sampling bounds are malformed")
        for value in law.conditions:
            _validate_value_ref(graph, value, before_spine_ref=spine_ref)


def _validate_claims_anchors(graph: EndpointSemanticGraph) -> None:
    for claim in graph.claims:
        _require_index(claim.scope_event_ref, len(graph.endpoint_spine), "claim scope")
        if claim.source_kind is ClaimSourceKind.BINDING:
            if claim.output_ordinal is not None:
                raise ValueError("binding-sourced claim carries an output ordinal")
            _require_index(claim.source_ref, len(graph.endpoint_spine), "claim binding")
            if (
                graph.endpoint_spine[claim.source_ref].kind
                is not SpineEventKind.PUBLIC_BINDING
            ):
                raise ValueError("binding-sourced claim names another event kind")
        else:
            if claim.output_ordinal is None or claim.output_ordinal < 0:
                raise ValueError("reduction-sourced claim lacks an output ordinal")
            _require_index(
                claim.source_ref, len(graph.endpoint_spine), "claim reduction"
            )
            if (
                type(graph.endpoint_spine[claim.source_ref].action)
                is not ReductionAction
            ):
                raise ValueError("reduction-sourced claim names another event kind")
    reduction_actions: set[int] = set()
    terminal_actions: set[int] = set()
    for ref, event in enumerate(graph.endpoint_spine):
        if type(event.action) is ReductionAction:
            reduction_actions.add(ref)
        elif type(event.action) is TerminalAction:
            terminal_actions.add(ref)
    anchored_reductions: set[int] = set()
    anchored_terminals: set[int] = set()
    for anchor_ref, anchor in enumerate(graph.anchored_obligations):
        if anchor.kind is AnchorKind.REDUCTION:
            if anchor.apply_spine_ref is None:
                raise ValueError("reduction anchor is not linked from the spine")
            _require_index(
                anchor.apply_spine_ref, len(graph.endpoint_spine), "reduction spine"
            )
            if (
                type(graph.endpoint_spine[anchor.apply_spine_ref].action)
                is not ReductionAction
            ):
                raise ValueError("reduction anchor and action disagree")
            if anchor.apply_spine_ref in anchored_reductions:
                raise ValueError("reduction action has duplicate anchors")
            anchored_reductions.add(anchor.apply_spine_ref)
            for claim_ref in anchor.input_claim_refs:
                _require_index(claim_ref, len(graph.claims), "reduction input claim")
            for value in anchor.side_inputs:
                _validate_value_ref(
                    graph, value, before_spine_ref=anchor.apply_spine_ref
                )
            for law_ref in anchor.required_challenge_law_refs:
                _require_index(
                    law_ref,
                    len(graph.static_fs_semantics.challenge_laws),
                    "reduction challenge",
                )
            for publication in anchor.publications:
                _require_index(
                    publication.publication_spine_ref,
                    len(graph.endpoint_spine),
                    "reduction publication",
                )
                if publication.publication_spine_ref >= anchor.apply_spine_ref:
                    raise ValueError(
                        "reduction publication does not precede application"
                    )
                if publication.next_challenge_law_ref is not None:
                    _require_index(
                        publication.next_challenge_law_ref,
                        len(graph.static_fs_semantics.challenge_laws),
                        "publication next challenge",
                    )
            if tuple(item.output_ordinal for item in anchor.output_claims) != tuple(
                range(len(anchor.output_claims))
            ):
                raise ValueError("reduction output rows are not ordinal-complete")
            for output in anchor.output_claims:
                for claim_ref in output.claim_refs:
                    _require_index(
                        claim_ref, len(graph.claims), "reduction output claim"
                    )
                    claim = graph.claims[claim_ref]
                    if claim.contract_ref != output.contract_ref:
                        raise ValueError("reduction output contract and claim disagree")
                expected_claim_refs = tuple(
                    ref
                    for ref, claim in enumerate(graph.claims)
                    if claim.source_kind is ClaimSourceKind.REDUCTION_OUTPUT
                    and claim.source_ref == anchor.apply_spine_ref
                    and claim.output_ordinal == output.output_ordinal
                )
                if output.claim_refs != expected_claim_refs:
                    raise ValueError(
                        "reduction output row lacks complete matching claims"
                    )
            covered_claim_refs = {
                claim_ref
                for output in anchor.output_claims
                for claim_ref in output.claim_refs
            }
            all_reduction_claim_refs = {
                ref
                for ref, claim in enumerate(graph.claims)
                if claim.source_kind is ClaimSourceKind.REDUCTION_OUTPUT
                and claim.source_ref == anchor.apply_spine_ref
            }
            if covered_claim_refs != all_reduction_claim_refs:
                raise ValueError("reduction output rows omit a sourced claim")
        elif anchor.kind is AnchorKind.TERMINAL:
            if anchor.terminal_spine_ref is None:
                raise ValueError("terminal anchor is not linked from the spine")
            _require_index(
                anchor.terminal_spine_ref, len(graph.endpoint_spine), "terminal spine"
            )
            if (
                type(graph.endpoint_spine[anchor.terminal_spine_ref].action)
                is not TerminalAction
            ):
                raise ValueError("terminal anchor and action disagree")
            if anchor.terminal_spine_ref in anchored_terminals:
                raise ValueError("terminal action has duplicate anchors")
            anchored_terminals.add(anchor.terminal_spine_ref)
            for value in anchor.public_outputs:
                _validate_value_ref(
                    graph, value, before_spine_ref=anchor.terminal_spine_ref
                )
            for check_ref in anchor.required_check_spine_refs:
                _require_index(check_ref, len(graph.endpoint_spine), "required check")
                if type(graph.endpoint_spine[check_ref].action) is not CheckAction:
                    raise ValueError("terminal requires a non-check event")
                if check_ref >= anchor.terminal_spine_ref:
                    raise ValueError("required check does not precede terminal")
            for claim_ref, _disposition in anchor.claim_dispositions:
                _require_index(claim_ref, len(graph.claims), "terminal claim")
        else:
            raise ValueError("unknown anchored-obligation kind")
    if (
        reduction_actions != anchored_reductions
        or terminal_actions != anchored_terminals
    ):
        raise ValueError("anchors have missing or duplicate action ownership")
    if graph.role is EndpointRole.VERIFIER:
        terminal_anchors = [
            item
            for item in graph.anchored_obligations
            if item.kind is AnchorKind.TERMINAL
        ]
        completion_coordinates = [
            coordinate
            for completion in graph.role_abi_graph.completion_variants
            if completion.target is CompletionTargetKind.CORE_TERMINAL
            for coordinate, _slot in completion.payload_bindings
        ]
        expected_terminal_outputs = [
            (anchor.terminal_spine_ref, ordinal)
            for anchor in terminal_anchors
            for ordinal, _value in enumerate(anchor.public_outputs)
        ]
        observed_terminal_outputs = [
            (coordinate.terminal_spine_ref, coordinate.output_ordinal)
            for coordinate in completion_coordinates
            if coordinate.kind is CompletionCoordinateKind.TERMINAL_OUTPUT
        ]
        if observed_terminal_outputs != expected_terminal_outputs:
            raise ValueError("terminal public outputs and completion ABI disagree")


def _reachable_value_nodes(graph: EndpointSemanticGraph) -> tuple[set[int], set[int]]:
    constants: set[int] = set()
    pure_nodes: set[int] = set()

    def visit(value: GraphValueRef) -> None:
        if value.kind is ValueRefKind.CONSTANT:
            constants.add(value.ref)
        elif value.kind is ValueRefKind.PURE_NODE and value.ref not in pure_nodes:
            pure_nodes.add(value.ref)
            for child in graph.pure_nodes[value.ref].inputs:
                visit(child)

    for event in graph.endpoint_spine:
        if event.binding_value is not None:
            visit(event.binding_value)
        for value in event.activity.inputs:
            visit(value)
        action = event.action
        if type(action) in {VerifierMessageAction, CheckAction}:
            for value in action.inputs:
                visit(value)
    for law in graph.static_fs_semantics.challenge_laws:
        for value in law.conditions:
            visit(value)
    for anchor in graph.anchored_obligations:
        for value in anchor.side_inputs + anchor.public_outputs:
            visit(value)
    return constants, pure_nodes


def _plan_value_type(
    graph: EndpointSemanticGraph,
    plan: PlanGraph,
    value: PlanValueRef,
    *,
    decision_ref: int,
    before_node_ref: int | None = None,
) -> int:
    if type(value) is not PlanValueRef or type(value.kind) is not PlanOperandKind:
        raise ValueError("Plan value ref has the wrong exact shape")
    if value.kind is PlanOperandKind.PRIVATE_MATERIAL:
        _require_index(value.ref, len(plan.private_material), "private material")
        actual = plan.private_material[value.ref].type_ref
    elif value.kind is PlanOperandKind.PRIVATE_RANDOMNESS:
        _require_index(value.ref, len(plan.randomness), "private randomness")
        actual = plan.randomness[value.ref].type_ref
        if plan.randomness[value.ref].first_available_decision_ref > decision_ref:
            raise ValueError("Plan reads randomness before availability")
    elif value.kind is PlanOperandKind.STATE_BEFORE:
        _require_index(value.ref, len(plan.state), "Plan state")
        actual = plan.state[value.ref].type_ref
    elif value.kind is PlanOperandKind.NODE_OUTPUT:
        _require_index(value.ref, len(plan.recipe_nodes), "Plan recipe node")
        node = plan.recipe_nodes[value.ref]
        if node.decision_ref != decision_ref:
            raise ValueError("Plan recipe node crosses decision ownership")
        if before_node_ref is not None and value.ref >= before_node_ref:
            raise ValueError("Plan recipe node does not point backward")
        actual = node.result_type_ref
    elif value.kind is PlanOperandKind.VIEW_PUBLIC_INPUT:
        _require_index(
            value.ref,
            len(graph.role_abi_graph.invocation_targets),
            "Plan public view",
        )
        actual = graph.role_abi_graph.invocation_targets[value.ref].type_ref
        if (
            graph.role_abi_graph.invocation_targets[value.ref].invocation_class
            is not InvocationClass.PUBLIC
        ):
            raise ValueError("Prover Plan reads a verifier-private invocation target")
    elif value.kind is PlanOperandKind.VIEW_OCCURRENCE:
        actual = _occurrence_output_type(graph, value.ref)
        if value.ref >= decision_ref:
            raise ValueError("Plan occurrence read is not prior")
    elif value.kind is PlanOperandKind.CONSTANT:
        actual = value.value_type_ref
        if value.literal is None:
            raise ValueError("Plan literal lacks its value")
    else:
        raise ValueError("unknown Plan value-ref kind")
    if actual != value.value_type_ref:
        raise ValueError("Plan value ref carries the wrong exact type")
    _require_index(actual, len(graph.value_types), "Plan value type")
    return actual


def _validate_plan(graph: EndpointSemanticGraph) -> None:
    plan = graph.optional_plan_graph
    if graph.role is EndpointRole.VERIFIER:
        if plan is not None:
            raise ValueError("Verifier endpoint carries Prover Plan semantics")
        return
    if plan is None:
        raise ValueError("Prover endpoint lacks an exact specialized Plan graph")
    decision_spine_refs = tuple(
        ref
        for ref, event in enumerate(graph.endpoint_spine)
        if type(event.action) is ProverMessageAction
    )
    decision_set = set(decision_spine_refs)
    for item in plan.private_material:
        _require_index(item.type_ref, len(graph.value_types), "private material type")
    for item in plan.randomness:
        _require_index(item.type_ref, len(graph.value_types), "randomness type")
        if item.first_available_decision_ref not in decision_set:
            raise ValueError("randomness availability is not a Prover-message decision")
    for item in plan.state:
        _require_index(item.type_ref, len(graph.value_types), "state type")
        if item.initial.kind not in {
            PlanOperandKind.PRIVATE_MATERIAL,
            PlanOperandKind.CONSTANT,
        }:
            raise ValueError("state initializer is not private material or a constant")
        first_decision = (
            decision_spine_refs[0] if decision_spine_refs else len(graph.endpoint_spine)
        )
        _plan_value_type(graph, plan, item.initial, decision_ref=first_decision)
        if item.initial.value_type_ref != item.type_ref:
            raise ValueError("state initializer has another type")
    if tuple(node.decision_ref for node in plan.recipe_nodes) != tuple(
        sorted(node.decision_ref for node in plan.recipe_nodes)
    ):
        raise ValueError("Plan recipe nodes are not grouped by decision spine")
    for node_ref, node in enumerate(plan.recipe_nodes):
        if node.decision_ref not in decision_set:
            raise ValueError("Plan node owner is not a Prover-message decision")
        _require_index(
            node.algorithm_dependency,
            len(graph.exact_used_dependencies),
            "Plan algorithm",
        )
        _require_index(
            node.evaluation_dependency,
            len(graph.exact_used_dependencies),
            "Plan evaluation",
        )
        _require_index(node.result_type_ref, len(graph.value_types), "Plan result type")
        for value in node.inputs:
            _plan_value_type(
                graph,
                plan,
                value,
                decision_ref=node.decision_ref,
                before_node_ref=node_ref,
            )
    if tuple(item.decision_ref for item in plan.moves) != decision_spine_refs:
        raise ValueError("Plan moves do not exactly cover decisions")
    for move in plan.moves:
        _plan_value_type(graph, plan, move.value, decision_ref=move.decision_ref)
        if move.kind is not PlanMoveKind.MESSAGE_VALUE:
            raise ValueError("bounded Plan move is not a message value")
    seen_updates: set[tuple[int, int]] = set()
    for update in plan.updates:
        if update.decision_ref not in decision_set:
            raise ValueError("state update is not owned by a Prover-message decision")
        _require_index(update.state_ref, len(plan.state), "update state")
        key = (update.decision_ref, update.state_ref)
        if key in seen_updates:
            raise ValueError("Plan state update is duplicated")
        seen_updates.add(key)
        if update.kind is PlanUpdateKind.KEEP:
            if update.value is not None:
                raise ValueError("KEEP state update carries a value")
        else:
            if update.value is None:
                raise ValueError("REPLACE state update lacks a value")
            _plan_value_type(
                graph, plan, update.value, decision_ref=update.decision_ref
            )
            if update.value.value_type_ref != plan.state[update.state_ref].type_ref:
                raise ValueError("state update has another type")
    expected_updates = {
        (decision_ref, state_ref)
        for decision_ref in decision_spine_refs
        for state_ref in range(len(plan.state))
    }
    if seen_updates != expected_updates:
        raise ValueError("Plan state updates do not form complete decision/state rows")


def _used_dependency_refs(graph: EndpointSemanticGraph) -> set[int]:
    used = {
        graph.static_fs_semantics.core_dependency,
        graph.static_fs_semantics.construction_dependency,
        graph.static_fs_semantics.absorb_algorithm_dependency,
        graph.static_fs_semantics.absorb_evaluation_dependency,
        graph.static_fs_semantics.squeeze_algorithm_dependency,
        graph.static_fs_semantics.squeeze_evaluation_dependency,
        graph.static_fs_semantics.advance_algorithm_dependency,
        graph.static_fs_semantics.advance_evaluation_dependency,
    }
    for law in graph.static_fs_semantics.challenge_laws:
        used.update(
            {
                law.accept_algorithm_dependency,
                law.accept_evaluation_dependency,
                law.decode_algorithm_dependency,
                law.decode_evaluation_dependency,
            }
        )
    for node in graph.pure_nodes:
        used.update({node.algorithm_dependency, node.evaluation_dependency})
    for codec in graph.role_abi_graph.codec_nodes:
        if codec.general_law_dependency is not None:
            used.add(codec.general_law_dependency)
    for event in graph.endpoint_spine:
        if event.activity.algorithm_dependency is not None:
            used.update(
                {
                    event.activity.algorithm_dependency,
                    event.activity.evaluation_dependency,
                }
            )
        action = event.action
        if type(action) in {VerifierMessageAction, CheckAction}:
            used.update({action.algorithm_dependency, action.evaluation_dependency})
    if graph.optional_plan_graph is not None:
        for node in graph.optional_plan_graph.recipe_nodes:
            used.update({node.algorithm_dependency, node.evaluation_dependency})
    return {item for item in used if item is not None}


def _used_type_refs(graph: EndpointSemanticGraph) -> set[int]:
    used = {
        graph.static_fs_semantics.state_type_ref,
        graph.static_fs_semantics.bytes_type_ref,
        graph.static_fs_semantics.natural_type_ref,
    }
    used.update(item.type_ref for item in graph.role_abi_graph.invocation_targets)
    used.update(item.type_ref for item in graph.constants)
    used.update(item.result_type_ref for item in graph.pure_nodes)
    for codec in graph.role_abi_graph.codec_nodes:
        used.update(
            item
            for item in (
                codec.value_type_ref,
                codec.external_type_ref,
                codec.semantic_type_ref,
            )
            if item is not None
        )
    for law in graph.static_fs_semantics.challenge_laws:
        used.add(law.value_type_ref)
    for event in graph.endpoint_spine:
        action = event.action
        if type(action) is ProverMessageAction:
            used.add(action.value_type_ref)
        elif type(action) is VerifierMessageAction:
            used.add(action.result_type_ref)
        elif type(action) is CheckAction:
            used.add(action.result_type_ref)
    if graph.optional_plan_graph is not None:
        plan = graph.optional_plan_graph
        used.update(item.type_ref for item in plan.private_material)
        used.update(item.type_ref for item in plan.randomness)
        used.update(item.type_ref for item in plan.state)
        used.update(item.result_type_ref for item in plan.recipe_nodes)
        for value in (
            [item.initial for item in plan.state]
            + [item.value for item in plan.moves]
            + [item.value for item in plan.updates if item.value is not None]
            + [value for node in plan.recipe_nodes for value in node.inputs]
        ):
            used.add(value.value_type_ref)
    return used


def _validate_graph(
    graph: EndpointSemanticGraph,
    *,
    general_codec_evidence: Mapping[int, bool] | None = None,
) -> None:
    if type(graph) is not EndpointSemanticGraph or type(graph.role) is not EndpointRole:
        raise ValueError("OIR graph has the wrong exact carrier")
    if len(canonical_bytes(graph)) > 1 << 20:
        raise OverflowError("OIR graph exceeds the canonical byte bound")
    for table in (
        graph.exact_used_dependencies,
        graph.value_types,
        graph.constants,
        graph.pure_nodes,
        graph.endpoint_spine,
        graph.claims,
        graph.anchored_obligations,
    ):
        if type(table) is not tuple or len(table) > MAX_GRAPH_ITEMS:
            raise ValueError("OIR graph table violates its finite bound")
    if graph.exact_used_dependencies != tuple(
        sorted(graph.exact_used_dependencies, key=canonical_bytes)
    ) or len(graph.exact_used_dependencies) != len(set(graph.exact_used_dependencies)):
        raise ValueError("dependency table is not canonical and duplicate-free")
    if graph.value_types != tuple(
        sorted(graph.value_types, key=lambda item: item.canonical_body)
    ) or len(graph.value_types) != len(set(graph.value_types)):
        raise ValueError("type table is not canonical and duplicate-free")
    for index, constant in enumerate(graph.constants):
        _require_index(constant.type_ref, len(graph.value_types), "constant type")
        if index >= MAX_GRAPH_ITEMS:
            raise ValueError("constant table exceeds the bound")
    for index, node in enumerate(graph.pure_nodes):
        _require_index(
            node.algorithm_dependency,
            len(graph.exact_used_dependencies),
            "pure algorithm",
        )
        _require_index(
            node.evaluation_dependency,
            len(graph.exact_used_dependencies),
            "pure evaluation",
        )
        _require_index(node.result_type_ref, len(graph.value_types), "pure result type")
        for value in node.inputs:
            _validate_value_ref(graph, value)
            if value.kind is ValueRefKind.PURE_NODE and value.ref >= index:
                raise ValueError("pure-node graph is not topologically ordered")
    reachable_constants, reachable_pure_nodes = _reachable_value_nodes(graph)
    if reachable_constants != set(range(len(graph.constants))):
        raise ValueError("constant table contains a phantom or omitted node")
    if reachable_pure_nodes != set(range(len(graph.pure_nodes))):
        raise ValueError("pure-node table contains a phantom or omitted node")
    _validate_role_abi(graph)
    if any(item.kind is CodecKind.GENERAL for item in graph.role_abi_graph.codec_nodes):
        if general_codec_evidence is None:
            raise LookupError("General codec evidence is missing")
        required = {
            index
            for index, item in enumerate(graph.role_abi_graph.codec_nodes)
            if item.kind is CodecKind.GENERAL
        }
        if set(general_codec_evidence) != required or not all(
            general_codec_evidence.values()
        ):
            raise LookupError("General codec evidence is incomplete")
    _validate_spine(graph)
    _validate_fs(graph)
    _validate_claims_anchors(graph)
    _validate_plan(graph)
    derived = derive_endpoint_contract(graph)
    if len({canonical_bytes(item) for item in derived.static_obligations}) != len(
        derived.static_obligations
    ):
        raise ValueError("derived static obligations contain duplicate coordinates")
    if len({canonical_bytes(item) for item in derived.requirements}) != len(
        derived.requirements
    ):
        raise ValueError("derived endpoint requirements are duplicated")
    if graph.role is EndpointRole.VERIFIER:
        if derived.completion_interface != DerivedCompletionInterface(
            CompletionInterfaceKind.VERIFIER_COMPLETIONS,
            tuple(range(len(graph.role_abi_graph.completion_variants))),
        ):
            raise ValueError("Verifier derived completion interface is incomplete")
    elif derived.completion_interface != DerivedCompletionInterface(
        CompletionInterfaceKind.NO_SOURCE_SEMANTIC_COMPLETION,
        (),
    ):
        raise ValueError("Prover endpoint invents a semantic completion interface")
    if _used_dependency_refs(graph) != set(range(len(graph.exact_used_dependencies))):
        raise ValueError("dependency table contains a dead or omitted dependency")
    if _used_type_refs(graph) != set(range(len(graph.value_types))):
        raise ValueError("type table contains a dead or omitted type")


_ADMISSION_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class AdmittedOir:
    _issuer: object
    endpoint: OirEndpoint
    oir_id: object

    def __post_init__(self) -> None:
        if self._issuer is not _ADMISSION_ISSUER:
            raise ValueError("only local OIR admission may issue this capability")

    def __repr__(self) -> str:
        return "AdmittedOir(<live>)"

    def __copy__(self) -> "AdmittedOir":
        raise ValueError("live OIR admissions cannot be copied")

    def __deepcopy__(self, _memo: object) -> "AdmittedOir":
        raise ValueError("live OIR admissions cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live OIR admissions cannot be serialized")


_LIVE_ADMITTED_OIRS: dict[int, AdmittedOir] = {}


def _is_live_admitted_oir(admitted: object) -> bool:
    if (
        type(admitted) is not AdmittedOir
        or admitted._issuer is not _ADMISSION_ISSUER
        or _LIVE_ADMITTED_OIRS.get(id(admitted)) is not admitted
        or type(admitted.endpoint) is not OirEndpoint
        or admitted.endpoint.semantic_profile != OIR_PROFILE
    ):
        return False
    try:
        expected_id = oir_endpoint_id(admitted.endpoint)
    except (TypeError, ValueError):
        return False
    return (
        admitted.oir_id == expected_id
        and admitted.endpoint.asserted_id == expected_id
    )


def local_admit(
    endpoint: object,
    *,
    general_codec_evidence: Mapping[int, bool] | None = None,
) -> Answer:
    if type(endpoint) is not OirEndpoint:
        return _answer(OutcomeKind.MALFORMED, reason="wrong OIR endpoint carrier")
    if endpoint.semantic_profile != OIR_PROFILE:
        return _answer(OutcomeKind.KIND_MISMATCH, reason="unknown OIR semantic profile")
    try:
        expected_id = oir_endpoint_id(endpoint)
        if endpoint.asserted_id != expected_id:
            return _answer(OutcomeKind.MALFORMED, reason="asserted OirId is false")
        _validate_graph(
            endpoint.semantic_graph,
            general_codec_evidence=general_codec_evidence,
        )
    except LookupError as error:
        return _answer(OutcomeKind.MISSING_DEPENDENCY, reason=str(error))
    except OverflowError as error:
        return _answer(OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED, reason=str(error))
    except (KeyError, TypeError, ValueError) as error:
        return _answer(OutcomeKind.MALFORMED, reason=f"LocalOirValid failed: {error}")
    admitted = AdmittedOir(_ADMISSION_ISSUER, endpoint, expected_id)
    _LIVE_ADMITTED_OIRS[id(admitted)] = admitted
    return _answer(OutcomeKind.AFFIRMATIVE, admitted)


# ---------------------------------------------------------------------------
# Fixed derived-semantics law and static FS pressure controls
# ---------------------------------------------------------------------------


def derive_frame_recipes(graph: EndpointSemanticGraph) -> tuple[FrameRecipe, ...]:
    """Expand every exact K2 framing coordinate without runtime values."""

    fs = graph.static_fs_semantics
    rows: list[FrameRecipe] = [
        FrameRecipe("core-header", core_dependency=fs.core_dependency),
        FrameRecipe(
            "construction-header",
            construction_dependency=fs.construction_dependency,
        ),
        FrameRecipe("application-domain", application_domain=fs.application_domain),
    ]
    for spine_ref, event in enumerate(graph.endpoint_spine):
        if event.kind is SpineEventKind.SCOPE_OPENING:
            rows.append(
                FrameRecipe(
                    "scope-open",
                    original_scope_path=event.original_scope_path,
                )
            )
        elif event.kind is SpineEventKind.PUBLIC_BINDING:
            rows.append(
                FrameRecipe(
                    "public-binding",
                    original_binding_ordinal=event.original_binding_ordinal,
                    activity_spine_ref=spine_ref,
                    type_ref=(
                        None
                        if event.binding_value is None
                        else _graph_value_type(graph, event.binding_value)
                    ),
                    value=event.binding_value,
                    binding_class=event.binding_class,
                )
            )
        elif event.kind is SpineEventKind.CORE_OCCURRENCE:
            action = event.action
            if event.activity.algorithm_dependency is not None:
                rows.append(
                    FrameRecipe(
                        "guard-outcome",
                        original_occurrence_ordinal=event.original_occurrence_ordinal,
                        activity_spine_ref=spine_ref,
                    )
                )
            if type(action) in {ProverMessageAction, VerifierMessageAction}:
                rows.append(
                    FrameRecipe(
                        "message",
                        original_occurrence_ordinal=event.original_occurrence_ordinal,
                        activity_spine_ref=spine_ref,
                        type_ref=(
                            action.value_type_ref
                            if type(action) is ProverMessageAction
                            else action.result_type_ref
                        ),
                        value=GraphValueRef(ValueRefKind.OCCURRENCE_OUTPUT, spine_ref),
                    )
                )
            elif type(action) is ChallengeAction:
                law = fs.challenge_laws[action.challenge_law_ref]
                for input_ordinal, value in enumerate(law.conditions):
                    rows.append(
                        FrameRecipe(
                            "challenge-condition",
                            original_occurrence_ordinal=event.original_occurrence_ordinal,
                            original_challenge_ordinal=law.original_challenge_ordinal,
                            challenge_input_ordinal=input_ordinal,
                            activity_spine_ref=spine_ref,
                            type_ref=_graph_value_type(graph, value),
                            value=value,
                        )
                    )
    return tuple(rows)


def derive_namespace_recipe(
    graph: EndpointSemanticGraph,
    challenge_law_ref: int,
) -> NamespaceRecipe:
    """Derive the per-draw namespace recipe; it is not graph identity data."""

    law_ref = _require_index(
        challenge_law_ref,
        len(graph.static_fs_semantics.challenge_laws),
        "challenge law",
    )
    matches = tuple(
        (spine_ref, event)
        for spine_ref, event in enumerate(graph.endpoint_spine)
        if type(event.action) is ChallengeAction
        and event.action.challenge_law_ref == law_ref
    )
    if len(matches) != 1:
        raise ValueError("challenge law does not have one exact spine action")
    _spine_ref, event = matches[0]
    if event.scope_event_ref is None:
        raise ValueError("challenge has no scope event")
    scope = graph.endpoint_spine[event.scope_event_ref]
    if scope.kind is not SpineEventKind.SCOPE_OPENING:
        raise ValueError("challenge scope ref is not a scope-opening event")
    law = graph.static_fs_semantics.challenge_laws[law_ref]
    return NamespaceRecipe(
        graph.static_fs_semantics.construction_dependency,
        graph.static_fs_semantics.core_dependency,
        scope.original_scope_path,
        law.original_challenge_ordinal,
        law.domain_ref,
        law.value_type_ref,
        law.correlation,
    )


def derive_endpoint_value_access(
    graph: EndpointSemanticGraph,
) -> tuple[EndpointValueAccess, ...]:
    """Derive the transient graph-only ``EndpointValueAccessV0`` fixed point.

    Access rows are derivation state, not OIR identity and not a fourth field
    of :class:`DerivedEndpointContract`.  Every demanded endpoint value must
    have exactly one route; resolving a route may add ordered predecessor
    values to the finite worklist.
    """

    seeds: list[GraphValueRef] = []
    fs = graph.static_fs_semantics
    abi = graph.role_abi_graph

    for spine_ref, event in enumerate(graph.endpoint_spine):
        if event.binding_value is not None:
            seeds.append(event.binding_value)
        seeds.extend(event.activity.inputs)
        action = event.action
        if type(action) in {ProverMessageAction, VerifierMessageAction}:
            seeds.append(GraphValueRef(ValueRefKind.OCCURRENCE_OUTPUT, spine_ref))
        elif type(action) is ChallengeAction:
            seeds.extend(fs.challenge_laws[action.challenge_law_ref].conditions)
        if graph.role is EndpointRole.VERIFIER and type(action) in {
            VerifierMessageAction,
            CheckAction,
        }:
            seeds.extend(action.inputs)

    if graph.role is EndpointRole.VERIFIER:
        for anchor in graph.anchored_obligations:
            seeds.extend(anchor.side_inputs)
            seeds.extend(anchor.public_outputs)

    plan = graph.optional_plan_graph
    if plan is not None:
        for node in plan.recipe_nodes:
            for operand in node.inputs:
                if operand.kind is PlanOperandKind.VIEW_PUBLIC_INPUT:
                    seeds.append(GraphValueRef(ValueRefKind.INVOCATION, operand.ref))
                elif operand.kind is PlanOperandKind.VIEW_OCCURRENCE:
                    seeds.append(
                        GraphValueRef(ValueRefKind.OCCURRENCE_OUTPUT, operand.ref)
                    )

    for target_ref in range(len(abi.invocation_targets)):
        seeds.append(GraphValueRef(ValueRefKind.INVOCATION, target_ref))
    for alias in abi.statement_aliases:
        if alias.flow is StatementFlowKind.EXPOSES_OPENED_BINDING:
            binding = graph.endpoint_spine[alias.binding_spine_ref]
            assert binding.binding_value is not None
            seeds.append(binding.binding_value)
    for edge in abi.transport_edges:
        seeds.append(
            GraphValueRef(ValueRefKind.OCCURRENCE_OUTPUT, edge.target_spine_ref)
        )
    if graph.role is EndpointRole.VERIFIER:
        terminal_anchors = {
            item.terminal_spine_ref: item
            for item in graph.anchored_obligations
            if item.kind is AnchorKind.TERMINAL
        }
        for completion in abi.completion_variants:
            for coordinate, _slot_ref in completion.payload_bindings:
                if coordinate.kind is not CompletionCoordinateKind.TERMINAL_OUTPUT:
                    continue
                if (
                    coordinate.terminal_spine_ref not in terminal_anchors
                    or coordinate.output_ordinal is None
                ):
                    raise ValueError("completion output has no terminal value route")
                anchor = terminal_anchors[coordinate.terminal_spine_ref]
                if not 0 <= coordinate.output_ordinal < len(anchor.public_outputs):
                    raise ValueError("completion output ordinal has no endpoint value")
                seeds.append(anchor.public_outputs[coordinate.output_ordinal])

    pending: dict[bytes, GraphValueRef] = {
        canonical_bytes(value): value for value in seeds
    }
    resolved: dict[bytes, EndpointValueAccess] = {}

    def add(values: Sequence[GraphValueRef]) -> None:
        for value in values:
            key = canonical_bytes(value)
            if key not in resolved:
                pending[key] = value

    def inbound_transport(
        spine_ref: int,
        actor: TransportActor,
    ) -> tuple[int, ...]:
        return tuple(
            ref
            for ref, edge in enumerate(abi.transport_edges)
            if edge.target_spine_ref == spine_ref and edge.source is actor
        )

    while pending:
        key = min(pending)
        value = pending.pop(key)
        _validate_value_ref(graph, value)
        if value.kind is ValueRefKind.INVOCATION:
            matches = tuple(
                fibre.slot_ref
                for fibre in abi.invocation_fibres
                if value.ref in fibre.target_refs
            )
            if len(matches) != 1:
                raise ValueError("invocation value lacks one exact decode route")
            route = EndpointValueAccessRoute(
                EndpointValueAccessRouteKind.INVOCATION_DECODE,
                value.ref,
                matches[0],
            )
        elif value.kind is ValueRefKind.CONSTANT:
            route = EndpointValueAccessRoute(
                EndpointValueAccessRouteKind.CONSTANT,
                value.ref,
            )
        elif value.kind is ValueRefKind.PURE_NODE:
            node = graph.pure_nodes[value.ref]
            route = EndpointValueAccessRoute(
                EndpointValueAccessRouteKind.PURE_EVAL,
                value.ref,
            )
            add(node.inputs)
        else:
            event = graph.endpoint_spine[value.ref]
            action = event.action
            if type(action) is ProverMessageAction:
                if graph.role is EndpointRole.PROVER:
                    if plan is None:
                        raise ValueError("local Prover message lacks a Plan route")
                    moves = tuple(
                        item for item in plan.moves if item.decision_ref == value.ref
                    )
                    if len(moves) != 1:
                        raise ValueError("Prover message lacks one exact Plan move")
                    route = EndpointValueAccessRoute(
                        EndpointValueAccessRouteKind.PLAN_MOVE,
                        value.ref,
                    )
                else:
                    edges = inbound_transport(value.ref, TransportActor.PROVER)
                    if len(edges) != 1:
                        raise ValueError(
                            "counterparty Prover value lacks one transport"
                        )
                    route = EndpointValueAccessRoute(
                        EndpointValueAccessRouteKind.INBOUND_TRANSPORT,
                        edges[0],
                    )
            elif type(action) is VerifierMessageAction:
                if graph.role is EndpointRole.VERIFIER:
                    route = EndpointValueAccessRoute(
                        EndpointValueAccessRouteKind.LOCAL_VERIFIER_MESSAGE,
                        value.ref,
                    )
                    add(action.inputs)
                else:
                    edges = inbound_transport(value.ref, TransportActor.VERIFIER)
                    if len(edges) == 1:
                        route = EndpointValueAccessRoute(
                            EndpointValueAccessRouteKind.INBOUND_TRANSPORT,
                            edges[0],
                        )
                    elif not edges:
                        route = EndpointValueAccessRoute(
                            EndpointValueAccessRouteKind.RECONSTRUCT_VERIFIER_MESSAGE,
                            value.ref,
                        )
                        add(action.inputs)
                    else:
                        raise ValueError("Verifier message has multiple value routes")
            elif type(action) is CheckAction:
                if graph.role is EndpointRole.VERIFIER:
                    route = EndpointValueAccessRoute(
                        EndpointValueAccessRouteKind.LOCAL_CHECK,
                        value.ref,
                    )
                else:
                    route = EndpointValueAccessRoute(
                        EndpointValueAccessRouteKind.RECONSTRUCT_CHECK,
                        value.ref,
                    )
                add(action.inputs)
            elif type(action) is ChallengeAction:
                route = EndpointValueAccessRoute(
                    EndpointValueAccessRouteKind.CHALLENGE_INTERPRET,
                    value.ref,
                    action.challenge_law_ref,
                )
                add(fs.challenge_laws[action.challenge_law_ref].conditions)
            else:
                raise ValueError("demanded occurrence value has no endpoint route")
        resolved[key] = EndpointValueAccess(value, route)

    result = tuple(sorted(resolved.values(), key=canonical_bytes))
    if len({canonical_bytes(item.value) for item in result}) != len(result):
        raise ValueError("endpoint value access has duplicate value routes")
    return result


def derive_endpoint_contract(
    graph: EndpointSemanticGraph,
) -> DerivedEndpointContract:
    """Apply the shared bounded static ``EndpointContractLawV0`` accessor.

    The returned rows index exact static duties induced by the graph.  They do
    not instantiate runtime draws, state versions, decoder results, dynamic
    ports, completion aggregation, execution traces, or concrete outcomes.
    """

    obligations: list[EndpointStaticObligation] = []
    requirements: list[DerivedRequirement] = []

    def obligation(
        kind: StaticObligationKind,
        owner_ref: int | None = None,
        *,
        secondary_ref: int | None = None,
        frame_recipe: FrameRecipe | None = None,
        codec_direction: CodecDirection | None = None,
        presentation_kind: PresentationKind | None = None,
    ) -> None:
        obligations.append(
            EndpointStaticObligation(
                kind,
                owner_ref,
                secondary_ref,
                frame_recipe,
                codec_direction,
                presentation_kind,
            )
        )

    def evaluator(
        use_site: str,
        algorithm: int,
        evaluation: int,
        *,
        spine_ref: int | None = None,
    ) -> None:
        requirements.append(
            DerivedRequirement(
                RequirementFamily.LOCAL_EVALUATOR,
                use_site,
                spine_event_ref=spine_ref,
                algorithm_dependency=algorithm,
                evaluation_dependency=evaluation,
            )
        )

    abi = graph.role_abi_graph
    external_supply_slots = tuple(
        sorted({item.slot_ref for item in abi.invocation_fibres})
    )
    for slot_ref in external_supply_slots:
        obligation(StaticObligationKind.SLOT_INGRESS, slot_ref)
        obligation(
            StaticObligationKind.PRESENTATION,
            slot_ref,
            codec_direction=CodecDirection.DECODE,
            presentation_kind=PresentationKind.EXTERNAL_SUPPLY,
        )

    frame_recipes = derive_frame_recipes(graph)
    for recipe in frame_recipes:
        obligation(StaticObligationKind.K2_FRAME, frame_recipe=recipe)

    for alias_ref, alias in enumerate(abi.statement_aliases):
        if alias.flow is StatementFlowKind.EXPOSES_OPENED_BINDING:
            obligation(
                StaticObligationKind.PRESENTATION,
                alias_ref,
                codec_direction=CodecDirection.ENCODE,
                presentation_kind=PresentationKind.STATEMENT,
            )

    local_transport_actor = (
        TransportActor.VERIFIER
        if graph.role is EndpointRole.VERIFIER
        else TransportActor.PROVER
    )
    local_transport_destination = (
        TransportDestination.VERIFIER
        if graph.role is EndpointRole.VERIFIER
        else TransportDestination.PROVER
    )
    for edge_ref, edge in enumerate(abi.transport_edges):
        directions: list[CodecDirection] = []
        if edge.source is local_transport_actor or (
            graph.role is EndpointRole.VERIFIER
            and edge.source is TransportActor.PUBLIC_DERIVATION
        ):
            directions.append(CodecDirection.ENCODE)
        if edge.destination is local_transport_destination:
            directions.append(CodecDirection.DECODE)
        for direction in directions:
            obligation(
                StaticObligationKind.PRESENTATION,
                edge_ref,
                codec_direction=direction,
                presentation_kind=PresentationKind.TRANSPORT,
            )
        if edge.source in {TransportActor.PROVER, TransportActor.VERIFIER}:
            requirements.append(
                DerivedRequirement(
                    RequirementFamily.COUNTERPARTY,
                    f"counterparty-transport:{edge_ref}",
                    counterparty=_other_role(graph.role),
                    role_abi_edge_ref=edge_ref,
                )
            )

    if graph.role is EndpointRole.VERIFIER:
        for completion_ref, completion in enumerate(abi.completion_variants):
            obligation(
                StaticObligationKind.PRESENTATION,
                completion_ref,
                codec_direction=CodecDirection.ENCODE,
                presentation_kind=PresentationKind.COMPLETION_TAG,
            )
            for coordinate_ordinal, _binding in enumerate(completion.payload_bindings):
                obligation(
                    StaticObligationKind.PRESENTATION,
                    completion_ref,
                    secondary_ref=coordinate_ordinal,
                    codec_direction=CodecDirection.ENCODE,
                    presentation_kind=PresentationKind.COMPLETION_PAYLOAD,
                )

    for spine_ref, event in enumerate(graph.endpoint_spine):
        action = event.action
        if event.activity.algorithm_dependency is not None:
            evaluator(
                f"guard:{spine_ref}",
                event.activity.algorithm_dependency,
                event.activity.evaluation_dependency,
                spine_ref=spine_ref,
            )
        if type(action) is ChallengeAction:
            obligation(
                StaticObligationKind.CHALLENGE_INTERPRET,
                spine_ref,
                secondary_ref=action.challenge_law_ref,
            )
            continue
        local = (
            graph.role is EndpointRole.PROVER and type(action) is ProverMessageAction
        ) or (
            graph.role is EndpointRole.VERIFIER
            and type(action)
            in {
                VerifierMessageAction,
                CheckAction,
                ReductionAction,
                TerminalAction,
            }
        )
        if local:
            obligation(StaticObligationKind.LOCAL_OCCURRENCE, spine_ref)
        elif type(action) in {
            ProverMessageAction,
            VerifierMessageAction,
            CheckAction,
            ReductionAction,
            TerminalAction,
        }:
            requirements.append(
                DerivedRequirement(
                    RequirementFamily.COUNTERPARTY,
                    f"counterparty-action:{spine_ref}",
                    spine_event_ref=spine_ref,
                    counterparty=_other_role(graph.role),
                )
            )
        if graph.role is EndpointRole.VERIFIER and type(action) in {
            VerifierMessageAction,
            CheckAction,
        }:
            evaluator(
                (
                    f"verifier-message:{spine_ref}"
                    if type(action) is VerifierMessageAction
                    else f"check:{spine_ref}"
                ),
                action.algorithm_dependency,
                action.evaluation_dependency,
                spine_ref=spine_ref,
            )

    fs = graph.static_fs_semantics
    for frame_ref, _recipe in enumerate(frame_recipes):
        evaluator(
            f"fs-absorb:{frame_ref}",
            fs.absorb_algorithm_dependency,
            fs.absorb_evaluation_dependency,
        )
    challenge_spine_refs = {
        event.action.challenge_law_ref: spine_ref
        for spine_ref, event in enumerate(graph.endpoint_spine)
        if type(event.action) is ChallengeAction
    }
    for law_ref, law in enumerate(fs.challenge_laws):
        spine_ref = challenge_spine_refs[law_ref]
        evaluator(
            f"fs-squeeze:{law_ref}",
            fs.squeeze_algorithm_dependency,
            fs.squeeze_evaluation_dependency,
            spine_ref=spine_ref,
        )
        evaluator(
            f"fs-advance:{law_ref}",
            fs.advance_algorithm_dependency,
            fs.advance_evaluation_dependency,
            spine_ref=spine_ref,
        )
        evaluator(
            f"challenge-accept:{law_ref}",
            law.accept_algorithm_dependency,
            law.accept_evaluation_dependency,
            spine_ref=spine_ref,
        )
        evaluator(
            f"challenge-decode:{law_ref}",
            law.decode_algorithm_dependency,
            law.decode_evaluation_dependency,
            spine_ref=spine_ref,
        )

    plan = graph.optional_plan_graph
    if plan is not None:
        for ref, item in enumerate(plan.private_material):
            requirements.append(
                DerivedRequirement(
                    RequirementFamily.PRIVATE_MATERIAL_INGRESS,
                    "plan-prelude",
                    plan_ref=ref,
                    kind=item.kind,
                    type_ref=item.type_ref,
                )
            )
        for ref, item in enumerate(plan.randomness):
            requirements.append(
                DerivedRequirement(
                    RequirementFamily.PRIVATE_RANDOMNESS_INGRESS,
                    "plan-randomness",
                    plan_ref=ref,
                    type_ref=item.type_ref,
                    first_available_decision_spine_ref=item.first_available_decision_ref,
                )
            )
        for ref, item in enumerate(plan.state):
            requirements.append(
                DerivedRequirement(
                    RequirementFamily.STATE_STORAGE,
                    "plan-state",
                    plan_ref=ref,
                    type_ref=item.type_ref,
                    initializer=item.initial,
                    updates=tuple(
                        update for update in plan.updates if update.state_ref == ref
                    ),
                )
            )
        for node_ref, node in enumerate(plan.recipe_nodes):
            evaluator(
                f"plan-node:{node_ref}",
                node.algorithm_dependency,
                node.evaluation_dependency,
                spine_ref=node.decision_ref,
            )
        for move in plan.moves:
            obligation(StaticObligationKind.PLAN_DECISION, move.decision_ref)

    value_access = derive_endpoint_value_access(graph)
    for access in value_access:
        route = access.route
        if route.kind is EndpointValueAccessRouteKind.PURE_EVAL:
            node = graph.pure_nodes[route.owner_ref]
            evaluator(
                f"pure-node:{route.owner_ref}",
                node.algorithm_dependency,
                node.evaluation_dependency,
            )
        elif route.kind is EndpointValueAccessRouteKind.RECONSTRUCT_VERIFIER_MESSAGE:
            action = graph.endpoint_spine[route.owner_ref].action
            assert type(action) is VerifierMessageAction
            evaluator(
                f"public-reconstruction-verifier-message:{route.owner_ref}",
                action.algorithm_dependency,
                action.evaluation_dependency,
                spine_ref=route.owner_ref,
            )
        elif route.kind is EndpointValueAccessRouteKind.RECONSTRUCT_CHECK:
            action = graph.endpoint_spine[route.owner_ref].action
            assert type(action) is CheckAction
            evaluator(
                f"public-reconstruction:{route.owner_ref}",
                action.algorithm_dependency,
                action.evaluation_dependency,
                spine_ref=route.owner_ref,
            )

    def presentation_slot(item: EndpointStaticObligation) -> int | None:
        if item.kind is not StaticObligationKind.PRESENTATION:
            return None
        if item.presentation_kind is PresentationKind.EXTERNAL_SUPPLY:
            return item.owner_ref
        if item.presentation_kind is PresentationKind.STATEMENT:
            assert item.owner_ref is not None
            return abi.statement_aliases[item.owner_ref].slot_ref
        if item.presentation_kind is PresentationKind.TRANSPORT:
            assert item.owner_ref is not None
            return abi.transport_edges[item.owner_ref].slot_ref
        if item.presentation_kind is PresentationKind.COMPLETION_PAYLOAD:
            assert item.owner_ref is not None and item.secondary_ref is not None
            return abi.completion_variants[item.owner_ref].payload_bindings[
                item.secondary_ref
            ][1]
        return None

    def general_leaves(codec_ref: int) -> tuple[int, ...]:
        codec = abi.codec_nodes[codec_ref]
        if codec.kind is CodecKind.GENERAL:
            return (codec_ref,)
        result: list[int] = []
        for _ordinal, child_ref in codec.children:
            result.extend(general_leaves(child_ref))
        return tuple(result)

    for presentation_ref, item in enumerate(obligations):
        slot_ref = presentation_slot(item)
        if slot_ref is None:
            continue
        for general_ref in general_leaves(abi.slots[slot_ref].codec_ref):
            dependency = abi.codec_nodes[general_ref].general_law_dependency
            assert dependency is not None
            evaluator(
                f"codec-presentation:{presentation_ref}:{general_ref}",
                dependency,
                dependency,
            )

    obligations.sort(key=canonical_bytes)
    requirements.sort(key=canonical_bytes)
    if len({canonical_bytes(item) for item in obligations}) != len(obligations):
        raise ValueError("derived static obligations are duplicated")
    if len({canonical_bytes(item) for item in requirements}) != len(requirements):
        raise ValueError("derived endpoint requirements are duplicated")
    completion_interface = DerivedCompletionInterface(
        (
            CompletionInterfaceKind.VERIFIER_COMPLETIONS
            if graph.role is EndpointRole.VERIFIER
            else CompletionInterfaceKind.NO_SOURCE_SEMANTIC_COMPLETION
        ),
        (
            tuple(range(len(abi.completion_variants)))
            if graph.role is EndpointRole.VERIFIER
            else ()
        ),
    )
    return DerivedEndpointContract(
        tuple(obligations),
        tuple(requirements),
        completion_interface,
    )


# ---------------------------------------------------------------------------
# Proposition formation and the third exact-equality checker
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProjectionProposition:
    purpose: ProjectionPurpose
    source_view_id: object
    target_oir_id: object
    relation_profile: object


_PROPOSITION_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class FormedProjectionProposition:
    _issuer: object
    body: ProjectionProposition
    proposition_id: object

    def __post_init__(self) -> None:
        if self._issuer is not _PROPOSITION_ISSUER:
            raise ValueError("only K3-D may form a projection proposition")

    def __repr__(self) -> str:
        return "FormedProjectionProposition(<live>)"

    def __copy__(self) -> "FormedProjectionProposition":
        raise ValueError("formed propositions cannot be copied")

    def __deepcopy__(self, _memo: object) -> "FormedProjectionProposition":
        raise ValueError("formed propositions cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("formed propositions cannot be serialized")


_LIVE_FORMED_PROPOSITIONS: dict[int, FormedProjectionProposition] = {}


_VALIDATION_REQUEST_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class ProjectionValidationRequest:
    proposition: FormedProjectionProposition
    source: CheckedEndpointSourceView
    target: AdmittedOir
    basis: SupportedExtractionBasis
    adapter: CheckedProjectionOwnerAdapter
    checker_basis: object
    work_limit: int
    source_handles: tuple[str, ...]
    schema_set_id: object
    manifest_id: object
    provenance: str
    source_label: str
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _VALIDATION_REQUEST_ISSUER:
            raise ValueError("only K3-D may form a projection-validation request")

    def __repr__(self) -> str:
        return "ProjectionValidationRequest(<live>)"

    def __copy__(self) -> "ProjectionValidationRequest":
        raise ValueError("live validation requests cannot be copied")

    def __deepcopy__(self, _memo: object) -> "ProjectionValidationRequest":
        raise ValueError("live validation requests cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("live validation requests cannot be serialized")


_LIVE_VALIDATION_REQUESTS: dict[int, ProjectionValidationRequest] = {}


_PROJECTED_ISSUER = object()


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class CheckedProjection:
    _issuer: object
    proposition: FormedProjectionProposition
    source_view_id: object
    oir_id: object
    validation_request_fingerprint: str
    validation: ProjectionValidationRequest

    def __post_init__(self) -> None:
        if self._issuer is not _PROJECTED_ISSUER:
            raise ValueError("only the projection checker may issue this capability")

    def __repr__(self) -> str:
        return "CheckedProjection(<live>)"

    def __copy__(self) -> "CheckedProjection":
        raise ValueError("checked projections cannot be copied")

    def __deepcopy__(self, _memo: object) -> "CheckedProjection":
        raise ValueError("checked projections cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ValueError("checked projections cannot be serialized")


_LIVE_CHECKED_PROJECTIONS: dict[int, CheckedProjection] = {}


def projection_proposition_id(proposition: ProjectionProposition) -> object:
    if proposition.relation_profile != RELATION_PROFILE:
        raise TypeError("projection proposition names an unsupported language profile")
    return _semantic_id(
        "oir.projection-proposition",
        (
            proposition.purpose,
            proposition.source_view_id,
            proposition.target_oir_id,
        ),
    )


def _is_live_formed_proposition(proposition: object) -> bool:
    if (
        type(proposition) is not FormedProjectionProposition
        or proposition._issuer is not _PROPOSITION_ISSUER
        or _LIVE_FORMED_PROPOSITIONS.get(id(proposition)) is not proposition
        or type(proposition.body) is not ProjectionProposition
    ):
        return False
    try:
        return proposition.proposition_id == projection_proposition_id(
            proposition.body
        )
    except (TypeError, ValueError):
        return False


def _source_handles(request: ProjectionRequest) -> tuple[str, ...]:
    assert request.construction is not None
    handles = [
        _id_text(
            k3.protocol_id(request.core, request.construction, request.interpretation)
        ),
        _id_text(
            k3.interface_id(
                request.core,
                request.construction,
                request.interpretation,
                request.interface,
            )
        ),
    ]
    if request.plan is not None:
        handles.append(
            _id_text(
                k3.plan_id(
                    request.core,
                    request.construction,
                    request.interpretation,
                    request.plan,
                )
            )
        )
    return tuple(handles)


def form_projection_proposition(
    source: object,
    target: object,
    *,
    relation_profile: object = RELATION_PROFILE,
) -> Answer:
    if not _is_live_checked_source_view(source):
        return _answer(OutcomeKind.REFUSED, reason="source view is not checked")
    if not _is_live_admitted_oir(target):
        return _answer(OutcomeKind.REFUSED, reason="target OIR is not locally admitted")
    assert type(source) is CheckedEndpointSourceView
    assert type(target) is AdmittedOir
    if relation_profile != RELATION_PROFILE:
        return _answer(
            OutcomeKind.KIND_MISMATCH, reason="unknown projection relation profile"
        )
    expected_role = (
        EndpointRole.VERIFIER
        if source.view.purpose is ProjectionPurpose.FS_VERIFIER
        else EndpointRole.PROVER
    )
    if (
        source.view.semantic_graph.role is not expected_role
        or target.endpoint.semantic_graph.role is not expected_role
    ):
        return _answer(
            OutcomeKind.KIND_MISMATCH, reason="purpose and endpoint role disagree"
        )
    body = ProjectionProposition(
        source.view.purpose,
        source.view_id,
        target.oir_id,
        relation_profile,
    )
    formed = FormedProjectionProposition(
        _PROPOSITION_ISSUER,
        body,
        projection_proposition_id(body),
    )
    _LIVE_FORMED_PROPOSITIONS[id(formed)] = formed
    return _answer(OutcomeKind.AFFIRMATIVE, formed)


def projection_validation_request_fingerprint(
    request: ProjectionValidationRequest,
) -> str:
    """Return an inert diagnostic fingerprint for one live request.

    This value is not a semantic ID, authority, cache key, or reconstruction
    route.  The identical live request remains authoritative.
    """

    return hashlib.sha256(
        canonical_bytes(
            (
                request.proposition.proposition_id,
                request.source_handles,
                request.schema_set_id,
                request.manifest_id,
                request.checker_basis,
                request.work_limit,
                request.provenance,
                request.source_label,
            )
        )
    ).hexdigest()


def _is_live_validation_request(validation: object) -> bool:
    if (
        type(validation) is not ProjectionValidationRequest
        or validation._issuer is not _VALIDATION_REQUEST_ISSUER
        or _LIVE_VALIDATION_REQUESTS.get(id(validation)) is not validation
        or not _is_live_formed_proposition(validation.proposition)
        or not _is_live_checked_source_view(validation.source)
        or not _is_live_admitted_oir(validation.target)
        or validation.basis is not validation.source.basis
        or validation.adapter is not validation.source.adapter
        or validation.checker_basis != CHECKER_BASIS
        or type(validation.work_limit) is not int
        or validation.work_limit <= 0
    ):
        return False
    try:
        body = validation.proposition.body
        return (
            validation.source_handles == _source_handles(validation.source.request)
            and validation.schema_set_id == validation.source.schema_set_id
            and validation.schema_set_id == OWNER_SCHEMA_SET_ID
            and validation.manifest_id == validation.source.manifest_id
            and validation.manifest_id
            == read_manifest_id(validation.source.view.purpose)
            and validation.provenance == validation.source.request.provenance
            and validation.source_label == validation.source.request.source_label
            and validation.proposition.proposition_id
            == projection_proposition_id(body)
            and body.source_view_id == validation.source.view_id
            and body.target_oir_id == validation.target.oir_id
            and body.purpose is validation.source.view.purpose
            and body.relation_profile == RELATION_PROFILE
        )
    except (AssertionError, AttributeError, TypeError, ValueError):
        return False


def _is_live_checked_projection(checked: object) -> bool:
    if (
        type(checked) is not CheckedProjection
        or checked._issuer is not _PROJECTED_ISSUER
        or _LIVE_CHECKED_PROJECTIONS.get(id(checked)) is not checked
        or not _is_live_validation_request(checked.validation)
        or checked.proposition is not checked.validation.proposition
    ):
        return False
    try:
        return (
            checked.source_view_id == checked.validation.source.view_id
            and checked.oir_id == checked.validation.target.oir_id
            and checked.validation_request_fingerprint
            == projection_validation_request_fingerprint(checked.validation)
        )
    except (AttributeError, TypeError, ValueError):
        return False


def form_projection_validation_request(
    source: object,
    target: object,
    *,
    work_limit: int = MAX_WORK,
) -> Answer:
    proposition = form_projection_proposition(source, target)
    if proposition.kind is not OutcomeKind.AFFIRMATIVE:
        return proposition
    if type(work_limit) is not int or work_limit <= 0:
        return _answer(
            OutcomeKind.MALFORMED, reason="validation work limit must be positive"
        )
    assert type(source) is CheckedEndpointSourceView
    assert type(target) is AdmittedOir
    try:
        result = ProjectionValidationRequest(
            proposition.value,
            source,
            target,
            source.basis,
            source.adapter,
            CHECKER_BASIS,
            work_limit,
            _source_handles(source.request),
            source.schema_set_id,
            source.manifest_id,
            source.request.provenance,
            source.request.source_label,
            _VALIDATION_REQUEST_ISSUER,
        )
        if (
            source.schema_set_id != OWNER_SCHEMA_SET_ID
            or source.manifest_id != read_manifest_id(source.view.purpose)
        ):
            raise ValueError("source authority carries stale schema or manifest IDs")
        _LIVE_VALIDATION_REQUESTS[id(result)] = result
    except (TypeError, ValueError) as error:
        return _answer(
            OutcomeKind.MALFORMED, reason=f"validation authority malformed: {error}"
        )
    return _answer(OutcomeKind.AFFIRMATIVE, result)


def _graph_mismatches(
    expected: EndpointSemanticGraph,
    observed: EndpointSemanticGraph,
) -> tuple[Mismatch, ...]:
    rows: list[Mismatch] = []
    for item in fields(EndpointSemanticGraph):
        left = getattr(expected, item.name)
        right = getattr(observed, item.name)
        if canonical_bytes(left) != canonical_bytes(right):
            rows.append(
                Mismatch(
                    "graph-mismatch",
                    f"semantic_graph.{item.name}",
                    hashlib.sha256(canonical_bytes(left)).hexdigest(),
                    hashlib.sha256(canonical_bytes(right)).hexdigest(),
                )
            )
    if not rows and canonical_bytes(expected) != canonical_bytes(observed):
        rows.append(Mismatch("graph-mismatch", "semantic_graph"))
    return tuple(rows)


def check_projection(
    validation: object,
    *,
    simulate_checker_failure: bool = False,
) -> Answer:
    """Decide only a supported, formed exact-graph projection question."""

    if type(validation) is not ProjectionValidationRequest:
        return _answer(OutcomeKind.MALFORMED, reason="wrong validation-request carrier")
    if (
        validation._issuer is not _VALIDATION_REQUEST_ISSUER
        or _LIVE_VALIDATION_REQUESTS.get(id(validation)) is not validation
        or not _is_live_formed_proposition(validation.proposition)
        or not _is_live_checked_source_view(validation.source)
        or not _is_live_admitted_oir(validation.target)
        or validation.basis is not validation.source.basis
        or validation.adapter is not validation.source.adapter
    ):
        return _answer(
            OutcomeKind.REFUSED, reason="validation capabilities are not live"
        )
    try:
        expected_handles = _source_handles(validation.source.request)
        expected_manifest = read_manifest_id(validation.source.view.purpose)
        expected_proposition_id = projection_proposition_id(
            validation.proposition.body
        )
    except (AssertionError, TypeError, ValueError) as error:
        return _answer(
            OutcomeKind.REFUSED,
            reason=f"validation authority cannot be recomputed: {error}",
        )
    if (
        validation.source_handles != expected_handles
        or validation.schema_set_id != validation.source.schema_set_id
        or validation.schema_set_id != OWNER_SCHEMA_SET_ID
        or validation.manifest_id != validation.source.manifest_id
        or validation.manifest_id != expected_manifest
        or validation.provenance != validation.source.request.provenance
        or validation.source_label != validation.source.request.source_label
        or validation.proposition.proposition_id != expected_proposition_id
    ):
        return _answer(
            OutcomeKind.REFUSED,
            reason="validation request fields disagree with live formation authority",
        )
    if validation.checker_basis != CHECKER_BASIS:
        return _answer(OutcomeKind.KIND_MISMATCH, reason="checker basis changed")
    if simulate_checker_failure:
        return _answer(
            OutcomeKind.CHECKER_FAILURE, reason="injected checker process fault"
        )
    work = len(canonical_bytes(validation.source.view.semantic_graph)) + len(
        canonical_bytes(validation.target.endpoint.semantic_graph)
    )
    if work > validation.work_limit:
        return _answer(
            OutcomeKind.DETERMINISTIC_LIMIT_EXCEEDED,
            reason="exact graph comparison exceeds its deterministic work limit",
        )
    expected_body = validation.proposition.body
    if (
        expected_body.source_view_id != validation.source.view_id
        or expected_body.target_oir_id != validation.target.oir_id
        or expected_body.purpose is not validation.source.view.purpose
        or expected_body.relation_profile != RELATION_PROFILE
    ):
        return _answer(
            OutcomeKind.REFUSED, reason="proposition and live authorities disagree"
        )
    mismatches = _graph_mismatches(
        validation.source.view.semantic_graph,
        validation.target.endpoint.semantic_graph,
    )
    if mismatches:
        return _answer(
            OutcomeKind.NEGATIVE,
            reason="exact endpoint semantic graphs differ",
            mismatches=mismatches,
        )
    request_fingerprint = projection_validation_request_fingerprint(validation)
    checked = CheckedProjection(
        _PROJECTED_ISSUER,
        validation.proposition,
        validation.source.view_id,
        validation.target.oir_id,
        request_fingerprint,
        validation,
    )
    _LIVE_CHECKED_PROJECTIONS[id(checked)] = checked
    return _answer(
        OutcomeKind.AFFIRMATIVE,
        checked,
    )


@dataclass(frozen=True)
class ProjectionPipelineRun:
    """One staged convenience run without fabricated downstream outcomes.

    ``None`` means that the stage was not attempted because an earlier stage
    did not affirm.  It is process state, not another semantic outcome kind.
    """

    produced: Answer
    admitted: Answer | None
    checked: Answer | None

    def __iter__(self):
        return iter((self.produced, self.admitted, self.checked))


def project_admit_check(
    request: ProjectionRequest,
    *,
    work_limit: int = MAX_WORK,
) -> ProjectionPipelineRun:
    produced = project(request, work_limit=work_limit)
    if produced.kind is not OutcomeKind.AFFIRMATIVE:
        return ProjectionPipelineRun(produced, None, None)
    admitted = local_admit(produced.value)
    if admitted.kind is not OutcomeKind.AFFIRMATIVE:
        return ProjectionPipelineRun(produced, admitted, None)
    source = derive_source_view(request, work_limit=work_limit)
    if source.kind is not OutcomeKind.AFFIRMATIVE:
        return ProjectionPipelineRun(produced, admitted, source)
    validation = form_projection_validation_request(
        source.value,
        admitted.value,
        work_limit=work_limit,
    )
    if validation.kind is not OutcomeKind.AFFIRMATIVE:
        return ProjectionPipelineRun(produced, admitted, validation)
    return ProjectionPipelineRun(
        produced,
        admitted,
        check_projection(validation.value),
    )


# ---------------------------------------------------------------------------
# Non-authoritative P01 complementary-endpoint pressure probe
# ---------------------------------------------------------------------------


def _dep_semantic(graph: EndpointSemanticGraph, ref: int) -> Dependency:
    return graph.exact_used_dependencies[
        _require_index(ref, len(graph.exact_used_dependencies), "pair dependency")
    ]


def _type_semantic(graph: EndpointSemanticGraph, ref: int) -> ValueTypeAtom:
    return graph.value_types[_require_index(ref, len(graph.value_types), "pair type")]


def _pair_value(graph: EndpointSemanticGraph, value: GraphValueRef) -> object:
    if value.kind is ValueRefKind.INVOCATION:
        target = graph.role_abi_graph.invocation_targets[value.ref]
        return (
            value.kind,
            target.invocation_class,
            _type_semantic(graph, target.type_ref),
        )
    if value.kind is ValueRefKind.CONSTANT:
        node = graph.constants[value.ref]
        return (value.kind, _type_semantic(graph, node.type_ref), node.value)
    if value.kind is ValueRefKind.PURE_NODE:
        node = graph.pure_nodes[value.ref]
        return (
            value.kind,
            _dep_semantic(graph, node.algorithm_dependency),
            _dep_semantic(graph, node.evaluation_dependency),
            tuple(_pair_value(graph, item) for item in node.inputs),
            _type_semantic(graph, node.result_type_ref),
        )
    return (value.kind, value.ref, value.output_ordinal)


def _pair_transport(graph: EndpointSemanticGraph, ref: int) -> object:
    edge = graph.role_abi_graph.transport_edges[ref]
    slot = graph.role_abi_graph.slots[edge.slot_ref]
    codec = graph.role_abi_graph.codec_nodes[slot.codec_ref]
    return (
        edge.target_spine_ref,
        edge.source,
        edge.destination,
        slot.external_key,
        codec.kind,
        codec.interface_codec_id,
        None
        if codec.value_type_ref is None
        else _type_semantic(graph, codec.value_type_ref),
    )


def _pair_spine(graph: EndpointSemanticGraph) -> tuple[object, ...]:
    rows: list[object] = []
    for event in graph.endpoint_spine:
        activity = (
            None
            if event.activity.algorithm_dependency is None
            else (
                _dep_semantic(graph, event.activity.algorithm_dependency),
                _dep_semantic(graph, event.activity.evaluation_dependency),
                tuple(_pair_value(graph, item) for item in event.activity.inputs),
            )
        )
        action = event.action
        if type(action) is ProverMessageAction:
            action_body: object = (
                "prover-message",
                action.channel_ref,
                _type_semantic(graph, action.value_type_ref),
            )
        elif type(action) is VerifierMessageAction:
            action_body = (
                "verifier-message",
                action.channel_ref,
                _dep_semantic(graph, action.algorithm_dependency),
                _dep_semantic(graph, action.evaluation_dependency),
                tuple(_pair_value(graph, item) for item in action.inputs),
                _type_semantic(graph, action.result_type_ref),
            )
        elif type(action) is ChallengeAction:
            action_body = ("challenge", action.challenge_law_ref)
        elif type(action) is CheckAction:
            action_body = (
                "check",
                _dep_semantic(graph, action.algorithm_dependency),
                _dep_semantic(graph, action.evaluation_dependency),
                tuple(_pair_value(graph, item) for item in action.inputs),
                _type_semantic(graph, action.result_type_ref),
            )
        elif type(action) is ReductionAction:
            action_body = ("reduction",)
        elif type(action) is TerminalAction:
            action_body = ("terminal",)
        else:
            action_body = None
        rows.append(
            (
                event.kind,
                event.scope_event_ref,
                event.parent_scope_event_ref,
                event.original_scope_path,
                event.original_binding_ordinal,
                event.binding_class,
                None
                if event.binding_value is None
                else _pair_value(graph, event.binding_value),
                event.original_occurrence_ordinal,
                event.opens_before_occurrence_ordinal,
                activity,
                action_body,
            )
        )
    return tuple(rows)


def _pair_fs(graph: EndpointSemanticGraph) -> object:
    fs = graph.static_fs_semantics
    return (
        _dep_semantic(graph, fs.core_dependency),
        _dep_semantic(graph, fs.construction_dependency),
        _type_semantic(graph, fs.state_type_ref),
        _type_semantic(graph, fs.bytes_type_ref),
        _type_semantic(graph, fs.natural_type_ref),
        fs.initial_state,
        _dep_semantic(graph, fs.absorb_algorithm_dependency),
        _dep_semantic(graph, fs.absorb_evaluation_dependency),
        _dep_semantic(graph, fs.squeeze_algorithm_dependency),
        _dep_semantic(graph, fs.squeeze_evaluation_dependency),
        _dep_semantic(graph, fs.advance_algorithm_dependency),
        _dep_semantic(graph, fs.advance_evaluation_dependency),
        fs.application_domain,
        fs.sampling_exhausted_failure,
        fs.derived_prefix_law,
        fs.challenge_transition_law,
        tuple(
            (
                law.original_challenge_ordinal,
                _type_semantic(graph, law.value_type_ref),
                law.domain_ref,
                law.fresh_law_ref,
                law.correlation,
                law.reduction_use,
                tuple(_pair_value(graph, item) for item in law.conditions),
                law.draw_bytes,
                law.maximum_draws,
                _dep_semantic(graph, law.accept_algorithm_dependency),
                _dep_semantic(graph, law.accept_evaluation_dependency),
                _dep_semantic(graph, law.decode_algorithm_dependency),
                _dep_semantic(graph, law.decode_evaluation_dependency),
                (
                    _dep_semantic(
                        graph,
                        derive_namespace_recipe(graph, law_ref).construction_dependency,
                    ),
                    _dep_semantic(
                        graph,
                        derive_namespace_recipe(graph, law_ref).core_dependency,
                    ),
                    derive_namespace_recipe(graph, law_ref).original_scope_path,
                    derive_namespace_recipe(graph, law_ref).original_challenge_ordinal,
                    derive_namespace_recipe(graph, law_ref).domain_ref,
                    _type_semantic(
                        graph,
                        derive_namespace_recipe(graph, law_ref).value_type_ref,
                    ),
                    derive_namespace_recipe(graph, law_ref).correlation,
                ),
            )
            for law_ref, law in enumerate(fs.challenge_laws)
        ),
    )


def _pair_abi(graph: EndpointSemanticGraph) -> object:
    abi = graph.role_abi_graph
    public_targets = tuple(
        _type_semantic(graph, item.type_ref)
        for item in abi.invocation_targets
        if item.invocation_class is InvocationClass.PUBLIC
    )
    cross_role_transports = tuple(
        _pair_transport(graph, index)
        for index, edge in enumerate(abi.transport_edges)
        if edge.source in {TransportActor.PROVER, TransportActor.VERIFIER}
    )
    statement = tuple(
        (
            abi.slots[item.slot_ref].external_key,
            item.binding_spine_ref,
            item.flow,
            item.invocation_target_ref,
            item.external_statement,
        )
        for item in abi.statement_aliases
    )
    return public_targets, cross_role_transports, statement


def pressure_probe_p01_endpoint_pair(
    verifier: object,
    prover: object,
) -> tuple[Mismatch, ...]:
    """Pressure-test one P01 duality hypothesis without minting authority.

    This helper is deliberately not an endpoint-pair judgment, proposition,
    profile, validation request, or capability.  It compares two independently
    admitted endpoints to falsify the bounded P01 normalizers below.  It
    returns only an ordinary tuple of observations and makes no liveness,
    acceptance, completeness, or semantic ``Negative`` claim.
    Authoritative endpoint pairing is deferred beyond K3-D.
    """

    if not _is_live_admitted_oir(verifier) or not _is_live_admitted_oir(prover):
        raise TypeError("P01 pair pressure probe requires independently admitted OIRs")
    assert type(verifier) is AdmittedOir
    assert type(prover) is AdmittedOir
    verifier_graph = verifier.endpoint.semantic_graph
    prover_graph = prover.endpoint.semantic_graph
    if (
        verifier_graph.role is not EndpointRole.VERIFIER
        or prover_graph.role is not EndpointRole.PROVER
    ):
        raise ValueError("P01 pressure-probe endpoint roles are not complementary")
    checks = (
        ("endpoint-spine", _pair_spine(verifier_graph), _pair_spine(prover_graph)),
        ("static-fs", _pair_fs(verifier_graph), _pair_fs(prover_graph)),
        ("role-abi", _pair_abi(verifier_graph), _pair_abi(prover_graph)),
        ("claims", verifier_graph.claims, prover_graph.claims),
        (
            "anchors",
            verifier_graph.anchored_obligations,
            prover_graph.anchored_obligations,
        ),
    )
    mismatches = tuple(
        Mismatch(
            "pair-mismatch",
            path,
            hashlib.sha256(canonical_bytes(left)).hexdigest(),
            hashlib.sha256(canonical_bytes(right)).hexdigest(),
        )
        for path, left, right in checks
        if canonical_bytes(left) != canonical_bytes(right)
    )
    verifier_completion_targets = tuple(
        item.target for item in verifier_graph.role_abi_graph.completion_variants
    )
    if (
        verifier_completion_targets.count(CompletionTargetKind.CORE_TERMINAL) != 1
        or verifier_completion_targets.count(CompletionTargetKind.FS_FAILURE) != 1
        or len(verifier_completion_targets) != 2
    ):
        mismatches += (Mismatch("pair-mismatch", "verifier-completion-closure"),)
    if prover_graph.role_abi_graph.completion_variants:
        mismatches += (Mismatch("pair-mismatch", "prover-completion-absence"),)
    return mismatches


def constant_pure_control() -> OirEndpoint:
    """Return one locally admitted synthetic graph that exercises value nodes."""

    candidate = project(p01_request(EndpointRole.VERIFIER))
    if (
        candidate.kind is not OutcomeKind.AFFIRMATIVE
    ):  # pragma: no cover - fixture fault
        raise RuntimeError(candidate)
    endpoint = candidate.value
    graph = endpoint.semantic_graph
    check = next(
        event.action
        for event in graph.endpoint_spine
        if type(event.action) is CheckAction
    )
    nat_ref = _type_index(graph.value_types, k3.NAT)
    constant = ConstantNode(nat_ref, 7)
    pure = PureNode(
        check.algorithm_dependency,
        check.evaluation_dependency,
        (GraphValueRef(ValueRefKind.CONSTANT, 0),),
        nat_ref,
    )
    terminal_anchor_ref = next(
        index
        for index, item in enumerate(graph.anchored_obligations)
        if item.kind is AnchorKind.TERMINAL
    )
    anchors = list(graph.anchored_obligations)
    terminal = anchors[terminal_anchor_ref]
    anchors[terminal_anchor_ref] = replace(
        terminal,
        public_outputs=(GraphValueRef(ValueRefKind.PURE_NODE, 0),),
    )
    abi = graph.role_abi_graph
    nat_codec = next(
        index
        for index, item in enumerate(abi.codec_nodes)
        if item.kind is CodecKind.IDENTITY and item.value_type_ref == nat_ref
    )
    slot_ref = len(abi.slots)
    slots = abi.slots + (AbiSlot("completion.terminal-output.0", nat_codec),)
    completions = list(abi.completion_variants)
    terminal_completion_ref = next(
        index
        for index, item in enumerate(completions)
        if item.target is CompletionTargetKind.CORE_TERMINAL
    )
    terminal_completion = completions[terminal_completion_ref]
    completions[terminal_completion_ref] = replace(
        terminal_completion,
        payload_bindings=(
            (
                CompletionCoordinate(
                    CompletionCoordinateKind.TERMINAL_OUTPUT,
                    terminal.terminal_spine_ref,
                    0,
                ),
                slot_ref,
            ),
        ),
    )
    changed = replace(
        graph,
        constants=(constant,),
        pure_nodes=(pure,),
        role_abi_graph=replace(
            abi,
            slots=slots,
            completion_variants=tuple(completions),
        ),
        anchored_obligations=tuple(anchors),
    )
    return remint(replace(endpoint, semantic_graph=changed))


def public_reconstruction_control() -> OirEndpoint:
    """Synthetic local-OIR control: a public binding demands a prior Check value.

    This is deliberately not claimed as a current K2 carrier inhabitant.  It
    pressures graph-local ``EndpointPublicClosureV0`` and the derived
    ``PublicReconstruction(Check)`` requirement only.
    """

    candidate = project(p01_request(EndpointRole.PROVER))
    if candidate.kind is not OutcomeKind.AFFIRMATIVE:  # pragma: no cover
        raise RuntimeError(candidate)
    endpoint = candidate.value
    graph = endpoint.semantic_graph
    check_ref = next(
        ref
        for ref, event in enumerate(graph.endpoint_spine)
        if type(event.action) is CheckAction
    )
    terminal_ref = next(
        ref
        for ref, event in enumerate(graph.endpoint_spine)
        if type(event.action) is TerminalAction
    )
    binding_ordinal = 1 + max(
        item.original_binding_ordinal
        for item in graph.endpoint_spine
        if item.original_binding_ordinal is not None
    )
    binding = SpineEvent(
        SpineEventKind.PUBLIC_BINDING,
        scope_event_ref=graph.endpoint_spine[check_ref].scope_event_ref,
        original_binding_ordinal=binding_ordinal,
        binding_class="public-reconstructed-check",
        binding_value=GraphValueRef(ValueRefKind.OCCURRENCE_OUTPUT, check_ref),
    )
    spine = (
        graph.endpoint_spine[:terminal_ref]
        + (binding,)
        + graph.endpoint_spine[terminal_ref:]
    )
    anchors = tuple(
        replace(item, terminal_spine_ref=terminal_ref + 1)
        if item.kind is AnchorKind.TERMINAL
        else item
        for item in graph.anchored_obligations
    )
    completions = tuple(
        replace(
            item,
            terminal_spine_ref=terminal_ref + 1,
            payload_bindings=tuple(
                (
                    replace(coordinate, terminal_spine_ref=terminal_ref + 1)
                    if coordinate.terminal_spine_ref == terminal_ref
                    else coordinate,
                    slot_ref,
                )
                for coordinate, slot_ref in item.payload_bindings
            ),
        )
        if item.target is CompletionTargetKind.CORE_TERMINAL
        else item
        for item in graph.role_abi_graph.completion_variants
    )
    changed = replace(
        graph,
        endpoint_spine=spine,
        anchored_obligations=anchors,
        role_abi_graph=replace(
            graph.role_abi_graph,
            completion_variants=completions,
        ),
    )
    return remint(replace(endpoint, semantic_graph=changed))
