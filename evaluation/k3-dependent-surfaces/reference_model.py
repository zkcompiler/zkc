"""Bounded executable research model for the K3-B dependent surfaces.

This module is deliberately a research instrument rather than repository
authority.  It imports the K2 executable model (and therefore K1) instead of
creating another identity or execution foundation.  The new code exercises
only the seams that K3-B must select: external Interface assignment, prover
Plan shape, occurrence-explicit relation correspondence, run-issued
grounding, three non-substitutable value-bridge lanes, typed grounding facts,
and an exact bounded carrier experiment.

The model is finite and fail closed.  It does not claim protocol-family
completeness, cryptographic security, theorem applicability, MLIR syntax, or
production conformance.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from enum import Enum
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Mapping, Sequence


# ---------------------------------------------------------------------------
# K1/K2 imports: one identity and execution foundation
# ---------------------------------------------------------------------------


_K2_NAME = "_zkc_k2_protocol_fiat_shamir"
_K2_PATH = (
    Path(__file__).resolve().parents[1]
    / "k2-protocol-fiat-shamir"
    / "reference_model.py"
)
if _K2_NAME in sys.modules:
    k2 = sys.modules[_K2_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K2_NAME, _K2_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load K2 reference model from {_K2_PATH}")
    k2 = importlib.util.module_from_spec(_spec)
    sys.modules[_K2_NAME] = k2
    _spec.loader.exec_module(k2)

k1 = k2.k1


# ---------------------------------------------------------------------------
# Shared finite helpers and typed refusals
# ---------------------------------------------------------------------------


MAX_INTERFACE_ENTRIES = 256
MAX_PLAN_INPUTS = 256
MAX_PLAN_ROUTES = 512
MAX_RELATION_OCCURRENCES = 512
MAX_EQUATION_NODES = 1024
MAX_ARTIFACT_FACTS = 512
MAX_ARTIFACT_SELECTORS = 512
MAX_ARTIFACT_OBSERVATIONS = 512
MAX_RUN_READS = 1024
MAX_SELECTOR_INDEX = (1 << 32) - 1


class K3Error(ValueError):
    """Base class for one supported K3-B refusal."""


class UnsupportedK3BSemanticProfileError(K3Error):
    pass


class MalformedK3BSemanticProfileError(K3Error):
    pass


class RefusedK3BSemanticProfileError(K3Error):
    pass


class KindMismatchK3Error(K3Error):
    """A formed coordinate belongs to the wrong typed semantic lane."""


class RefusedK3AuthorityError(K3Error):
    """A formed same-kind source or authority substitution is not authorized."""


class InterfaceError(K3Error):
    pass


class PlanError(K3Error):
    pass


class RelationError(K3Error):
    pass


class GroundingError(K3Error):
    pass


class BridgeError(K3Error):
    pass


class ArtifactError(K3Error):
    pass


class CarrierError(K3Error):
    pass


class MissingCarrierField(CarrierError):
    pass


class UnknownCarrierField(CarrierError):
    pass


class UnsupportedCarrierFeature(CarrierError):
    pass


class _NonTransferableAuthority:
    """Process-local bearer state whose object identity is authoritative."""

    __hash__ = None

    def __copy__(self) -> object:
        raise K3Error("live authority cannot be copied")

    def __deepcopy__(self, _memo: object) -> object:
        raise K3Error("live authority cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise K3Error("live authority cannot be serialized")


def _ascii(text: str, what: str) -> str:
    if (
        type(text) is not str
        or not text
        or any(ord(ch) < 0x21 or ord(ch) > 0x7E for ch in text)
    ):
        raise K3Error(f"{what} must be nonempty printable ASCII without spaces")
    return text


def _profile_catalog(catalog_kind: str, declarations: tuple[str, ...]) -> object:
    return k1.DatumSeq(
        (
            k1.DatumRecord(
                (
                    (0, k1.Symbol(catalog_kind)),
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


# This is the exact target Relations subject catalog.  Catalog routing is a
# smaller claim than body support: this bounded instrument constructs only the
# subset named by RELATIONS_BOUNDED_BODY_KINDS below.
RELATIONS_SEMANTIC_SUBJECT_KINDS_V0 = (
    "relations.artifact-comparison-question",
    "relations.artifact-observation",
    "relations.artifact-profile",
    "relations.artifact-profile-count-question",
    "relations.commitment-grounding",
    "relations.correspondence-question",
    "relations.definition",
    "relations.definition-model-question",
    "relations.grounding-equation",
    "relations.instance",
    "relations.interface",
    "relations.plan-witness-binding",
    "relations.protocol-binding",
    "relations.recursion-binding-coverage-schema",
    "relations.refinement-question",
    "relations.semantic-model",
    "relations.source-binding-payload",
    "relations.source-capability-requirement",
    "relations.source-consumer",
    "relations.source-no-policy",
    "relations.source-policy-closure",
    "relations.source-purpose",
    "relations.transform",
    "relations.value-bridge",
)

# These are module-declaration contract grammars, not RelationsId subjects.
# Their bodies are committed through their owning SemanticModuleId; the
# bounded fixture references below must therefore never advertise them as
# supported Relations-profile subjects.
RELATIONS_DECLARATION_CONTRACT_KINDS_V0 = (
    "relations.artifact-fact",
    "relations.artifact-format",
    "relations.artifact-interpreter",
    "relations.commitment-construction",
    "relations.definition-language",
    "relations.definition-model-law",
    "relations.loss-export",
    "relations.loss-source-premise",
    "relations.model-assumption",
    "relations.oracle-access-law",
    "relations.private-transform-contract",
    "relations.refinement-law",
    "relations.satisfaction-evaluator",
    "relations.value-bridge-law",
)

# Subject kinds for which this finite executable contains a bounded body
# constructor.  This does not claim that each proxy body is the final durable
# schema.  Absence means that only target-catalog routing is exercised here,
# not formation, admission, or operational semantics.
RELATIONS_BOUNDED_BODY_KINDS = frozenset(
    {
        "relations.definition",
        "relations.grounding-equation",
        "relations.interface",
        "relations.plan-witness-binding",
        "relations.protocol-binding",
        "relations.source-binding-payload",
        "relations.source-capability-requirement",
        "relations.source-consumer",
        "relations.source-no-policy",
        "relations.source-policy-closure",
        "relations.source-purpose",
        "relations.transform",
        "relations.value-bridge",
    }
)
RELATIONS_UNIMPLEMENTED_TARGET_BODY_KINDS = frozenset(
    RELATIONS_SEMANTIC_SUBJECT_KINDS_V0
) - RELATIONS_BOUNDED_BODY_KINDS

# These two names survive only inside bounded legacy fixture mechanics.  A run
# value is an owner-local occurrence in the target, and the bridge image test
# is represented by a declaration-owned portable algorithm.  Neither name is
# a durable Relations semantic subject or declaration-contract kind.
RELATIONS_BOUNDED_LEGACY_REFERENCE_KINDS = frozenset(
    {
        "relations.grounded-value-occurrence",
        "relations.predicate",
    }
)
_RELATIONS_BOUNDED_NONPROFILED_REFERENCE_KINDS = frozenset(
    RELATIONS_DECLARATION_CONTRACT_KINDS_V0
) | RELATIONS_BOUNDED_LEGACY_REFERENCE_KINDS


def _validate_relations_catalog_partition() -> None:
    semantic = RELATIONS_SEMANTIC_SUBJECT_KINDS_V0
    declarations = RELATIONS_DECLARATION_CONTRACT_KINDS_V0
    if semantic != tuple(sorted(semantic)) or len(semantic) != len(set(semantic)):
        raise K3Error("Relations semantic subject catalog must be sorted and unique")
    if declarations != tuple(sorted(declarations)) or len(declarations) != len(
        set(declarations)
    ):
        raise K3Error(
            "Relations declaration-contract catalog must be sorted and unique"
        )
    if set(semantic) & set(declarations):
        raise K3Error(
            "Relations subjects and module declaration contracts must be disjoint"
        )
    if not RELATIONS_BOUNDED_BODY_KINDS.issubset(semantic):
        raise K3Error(
            "bounded Relations body coverage must be a subset of the target catalog"
        )
    if RELATIONS_BOUNDED_LEGACY_REFERENCE_KINDS & (
        set(semantic) | set(declarations)
    ):
        raise K3Error("legacy fixture references must stay outside both catalogs")


_validate_relations_catalog_partition()


@dataclass(frozen=True)
class K3BSemanticProfiles:
    k2_profiles: object
    interface_plan: object
    relations_correspondence: object

    def __post_init__(self) -> None:
        if type(self.k2_profiles) is not k2.K2SemanticProfiles or any(
            type(item) is not k1.SemanticLanguageProfile
            for item in (self.interface_plan, self.relations_correspondence)
        ):
            raise K3Error("K3-B semantic profiles have the wrong exact shape")
        if self.interface_plan.profile_imports != _profile_imports(
            self.k2_profiles.interaction,
            self.k2_profiles.transcript_fs,
        ):
            raise K3Error(
                "the Interface/Plan profile must import exactly the K2 "
                "languages it interprets"
            )
        if self.relations_correspondence.profile_imports != _profile_imports(
            self.interface_plan
        ):
            raise K3Error("the Relations profile must import Interface/Plan")
        if self.relations_correspondence.declaration_catalogs != k1.DatumSeq(()):
            raise K3Error(
                "the Relations profile-local declaration catalog must be exactly empty"
            )

    @property
    def bundle(self) -> dict[object, object]:
        return {
            **self.k2_profiles.bundle,
            self.interface_plan.identity: self.interface_plan,
            self.relations_correspondence.identity: self.relations_correspondence,
        }


def make_k3b_semantic_profiles(
    *,
    k2_profiles: object = k2.K2_SEMANTIC_PROFILES,
    interface_plan_law: bytes = b"zkc-k3b-interface-plan-law-v0",
    relations_law: bytes = b"zkc-k3b-relations-correspondence-law-v0",
) -> K3BSemanticProfiles:
    if type(k2_profiles) is not k2.K2SemanticProfiles:
        raise K3Error("K3-B needs one exact K2 profile bundle")
    interface_plan = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.interface-plan"),
        0,
        _profile_imports(
            k2_profiles.interaction,
            k2_profiles.transcript_fs,
        ),
        tuple(
            k1.Symbol(item)
            for item in sorted(
                (
                    "pir.plan-witness-surface",
                    "pir.protocol-interface",
                    "pir.prover-plan",
                    "pir.source-binding-payload",
                    "pir.source-capability-requirement",
                    "pir.source-consumer",
                    "pir.source-no-policy",
                    "pir.source-policy-closure",
                    "pir.source-purpose",
                )
            )
        ),
        _profile_catalog(
            "pir.interface-plan-declaration",
            (
                "interface-and-plan-owner-view-catalog-v0",
                "pir-source-authority-envelope-specialization-v0",
                "plan-witness-surface-body-v0",
                "protocol-interface-body-v0",
                "prover-plan-body-v0",
            ),
        ),
        interface_plan_law,
    )
    relations_correspondence = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.relations.correspondence"),
        0,
        _profile_imports(interface_plan),
        tuple(k1.Symbol(item) for item in RELATIONS_SEMANTIC_SUBJECT_KINDS_V0),
        k1.DatumSeq(()),
        relations_law,
    )
    return K3BSemanticProfiles(
        k2_profiles,
        interface_plan,
        relations_correspondence,
    )


K3B_SEMANTIC_PROFILES = make_k3b_semantic_profiles()
K3B_PROFILE_BUNDLE = K3B_SEMANTIC_PROFILES.bundle
PIR_INTERFACE_PLAN_PROFILE = K3B_SEMANTIC_PROFILES.interface_plan
PIR_INTERFACE_PLAN_PROFILE_ID = PIR_INTERFACE_PLAN_PROFILE.identity
RELATIONS_PROFILE = K3B_SEMANTIC_PROFILES.relations_correspondence
RELATIONS_PROFILE_ID = RELATIONS_PROFILE.identity
# The maximal convenience bundle contains the unrelated K2 public-view profile
# for callers that need every K2/K3-B preimage.  It is not an exact root
# closure for either K3-B language.
K3B_PROFILE_PREIMAGES = K3B_PROFILE_BUNDLE


def k3b_root_profile_preimages(
    profiles: K3BSemanticProfiles,
) -> Mapping[object, dict[object, object]]:
    if type(profiles) is not K3BSemanticProfiles:
        raise K3Error("K3-B root closures need one exact profile bundle")
    interface = {
        profiles.k2_profiles.interaction.identity: profiles.k2_profiles.interaction,
        profiles.k2_profiles.transcript_fs.identity: profiles.k2_profiles.transcript_fs,
        profiles.interface_plan.identity: profiles.interface_plan,
    }
    relations = {
        **interface,
        profiles.relations_correspondence.identity: profiles.relations_correspondence,
    }
    return MappingProxyType(
        {
            profiles.interface_plan.identity: interface,
            profiles.relations_correspondence.identity: relations,
        }
    )


K3B_ROOT_PROFILE_PREIMAGES = k3b_root_profile_preimages(K3B_SEMANTIC_PROFILES)
PIR_INTERFACE_PLAN_PROFILE_PREIMAGES = K3B_ROOT_PROFILE_PREIMAGES[
    PIR_INTERFACE_PLAN_PROFILE_ID
]
RELATIONS_PROFILE_PREIMAGES = K3B_ROOT_PROFILE_PREIMAGES[RELATIONS_PROFILE_ID]


@dataclass(frozen=True)
class K3BSemanticProfileSupport:
    supported_profile_ids: frozenset[object]

    def __post_init__(self) -> None:
        if type(self.supported_profile_ids) is not frozenset:
            raise K3Error("K3-B profile support must be one exact frozen ID set")
        for identifier in self.supported_profile_ids:
            if (
                type(identifier) is not k1.TypedContentId
                or identifier.subject_kind != k1.SEMANTIC_LANGUAGE_PROFILE_KIND
                or identifier.semantic_regime != k1.SEMANTIC_REGIME_ID
            ):
                raise K3Error("K3-B profile support contains a non-profile ID")


def make_k3b_profile_support(
    *bundles: K3BSemanticProfiles,
) -> K3BSemanticProfileSupport:
    if not bundles or any(type(item) is not K3BSemanticProfiles for item in bundles):
        raise K3Error("K3-B profile support needs exact profile bundles")
    return K3BSemanticProfileSupport(
        frozenset(
            identifier
            for bundle in bundles
            for identifier in bundle.bundle
        )
    )


def make_k3b_selected_profile_support(
    *profiles: object,
) -> K3BSemanticProfileSupport:
    if not profiles or any(
        type(profile) is not k1.SemanticLanguageProfile for profile in profiles
    ):
        raise K3Error("K3-B selected-profile support needs exact profiles")
    return K3BSemanticProfileSupport(
        frozenset(profile.identity for profile in profiles)
    )


K3B_PROFILE_SUPPORT = make_k3b_profile_support(K3B_SEMANTIC_PROFILES)
K3B_INTERFACE_PROFILE_SUPPORT = make_k3b_selected_profile_support(
    PIR_INTERFACE_PLAN_PROFILE
)
K3B_RELATIONS_PROFILE_SUPPORT = make_k3b_selected_profile_support(
    RELATIONS_PROFILE
)

_PIR_SOURCE_AUTHORITY_SUBJECT_KINDS = frozenset(
    {
        "pir.source-binding-payload",
        "pir.source-capability-requirement",
        "pir.source-consumer",
        "pir.source-no-policy",
        "pir.source-policy-closure",
        "pir.source-purpose",
    }
)
_RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS = frozenset(
    {
        "relations.source-binding-payload",
        "relations.source-capability-requirement",
        "relations.source-consumer",
        "relations.source-no-policy",
        "relations.source-policy-closure",
        "relations.source-purpose",
    }
)


def _require_supported_k3b_profile(
    profiles: K3BSemanticProfiles,
    profile_support: K3BSemanticProfileSupport,
    selected_profile: object,
    *,
    required_subject_kinds: frozenset[str] = frozenset(),
) -> None:
    if (
        type(profiles) is not K3BSemanticProfiles
        or type(profile_support) is not K3BSemanticProfileSupport
        or type(selected_profile) is not k1.SemanticLanguageProfile
    ):
        raise MalformedK3BSemanticProfileError(
            "K3-B issuance needs exact profiles and evaluator support"
        )
    profiles.__post_init__()
    profile_support.__post_init__()
    root_preimages = k3b_root_profile_preimages(profiles)
    preimages = root_preimages.get(selected_profile.identity)
    if preimages is None:
        raise MalformedK3BSemanticProfileError(
            "K3-B issuance selected no profile from its exact bundle"
        )
    try:
        context = k1.effective_semantic_context(
            selected_profile.identity,
            preimages,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except (k1.ModelError, k1.CanonicalError) as error:
        raise MalformedK3BSemanticProfileError(
            "K3-B profile import closure is not authenticated"
        ) from error
    authenticated_ids = {
        identifier for identifier, _profile in context.authenticated_profiles
    }
    if authenticated_ids != set(preimages):
        raise RefusedK3BSemanticProfileError(
            "K3-B root profile bundle is not its exact no-extra closure"
        )
    if selected_profile.identity not in profile_support.supported_profile_ids:
        raise UnsupportedK3BSemanticProfileError(
            "K3-B evaluator does not support the selected root profile"
        )
    supported_subject_kinds = {
        item.value for item in selected_profile.supported_subject_kinds
    }
    if not required_subject_kinds.issubset(supported_subject_kinds):
        raise RefusedK3BSemanticProfileError(
            "K3-B selected profile does not support every issued subject kind"
        )


def _authenticate_k3b_profiled_subject(
    identifier: object,
    subject_kind: str,
    domain_body: object,
    *,
    profiles: K3BSemanticProfiles,
    profile_support: K3BSemanticProfileSupport,
    selected_profile: object,
) -> None:
    _require_supported_k3b_profile(
        profiles,
        profile_support,
        selected_profile,
        required_subject_kinds=frozenset({subject_kind}),
    )
    supported_profiles = tuple(
        sorted(
            profile_support.supported_profile_ids,
            key=lambda item: item.internal_reference(),
        )
    )
    k1.authenticate_profiled_semantic_content(
        identifier,
        selected_profile.identity,
        domain_body,
        k3b_root_profile_preimages(profiles)[selected_profile.identity],
        supported_profiles=supported_profiles,
    )


def _bounded_unique(names: Sequence[str], bound: int, what: str) -> None:
    if len(names) > bound:
        raise K3Error(f"{what} exceed their finite bound")
    for name in names:
        _ascii(name, what)
    if len(names) != len(set(names)):
        raise K3Error(f"{what} must be unique")


def _id_datum(
    identifier: object,
    expected_subject_kind: str | tuple[str, ...] | None = None,
) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise K3Error("semantic reference must be one exact K1 TypedContentId")
    identifier.__post_init__()
    if identifier.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise K3Error("semantic reference belongs to an unsupported semantic regime")
    if expected_subject_kind is not None:
        expected = (
            (expected_subject_kind,)
            if type(expected_subject_kind) is str
            else expected_subject_kind
        )
        if identifier.subject_kind not in expected:
            raise K3Error(
                f"semantic reference has subject kind {identifier.subject_kind!r}; "
                f"expected one of {expected!r}"
            )
    return k1.BytesValue(identifier.internal_reference())


def _semantic_id(
    subject_kind: str,
    body: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    if subject_kind in {
        "pir.plan-witness-surface",
        "pir.protocol-interface",
        "pir.prover-plan",
        "pir.source-binding-payload",
        "pir.source-capability-requirement",
        "pir.source-consumer",
        "pir.source-no-policy",
        "pir.source-policy-closure",
        "pir.source-purpose",
    }:
        profile = profiles.interface_plan
    elif subject_kind in RELATIONS_SEMANTIC_SUBJECT_KINDS_V0:
        profile = profiles.relations_correspondence
    elif subject_kind in _RELATIONS_BOUNDED_NONPROFILED_REFERENCE_KINDS:
        # The reference model has no SemanticModule carrier.  It represents a
        # module declaration reference (and two explicitly legacy local
        # fixture references) by an unprofiled typed content ID.  This keeps
        # existing finite fixtures usable without falsely routing these names
        # through RelationsProfileId.
        return k1.content_id(
            subject_kind,
            k1.encode_datum(body),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    elif subject_kind.startswith(("pir.", "relations.")):
        raise K3Error(
            "K3-B cannot identify an owner subject outside its exact profile catalog"
        )
    else:
        return k1.content_id(
            subject_kind,
            k1.encode_datum(body),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    return k1.profiled_content_id(
        subject_kind,
        profile.identity,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def fixture_semantic_ref(
    subject_kind: str,
    label: str,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    """Create one K1-backed exact reference for a bounded fixture meaning."""

    return _semantic_id(
        subject_kind,
        k1.DatumRecord(((0, k1.Symbol(_ascii(label, "fixture label"))),)),
        profiles=profiles,
    )


BYTES = k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(0, 1 << 16))
BYTES32 = k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(32, 32))
BYTES96 = k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(0, 96))
NAT = k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema((1 << 64) - 1))
BOOL = k1.ValueType(k1.BOOL_DOMAIN, k1.BOOL_SCHEMA)
ORACLE_CELLS = k1.ValueType(
    k1.SEQUENCE_DOMAIN,
    k1.SeqSchema(k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(0, 256)), 64),
)


def value_type_for_sort(sort: object) -> object:
    if sort is k2.ValueSort.BYTES:
        return BYTES
    if sort is k2.ValueSort.NAT:
        return NAT
    if sort is k2.ValueSort.BOOL:
        return BOOL
    if sort is k2.ValueSort.ORACLE:
        return ORACLE_CELLS
    raise K3Error("unsupported K2 value sort")


IDENTITY_CODEC = fixture_semantic_ref("foundation.canonical-algorithm", "identity-codec")


def protocol_id(
    core: object,
    construction: object | None,
    interpretation: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    """Delegate to K2's single owner implementation of Protocol identity."""

    try:
        return k2.protocol_id(
            core,
            construction,
            interpretation,
            profiles=profiles.k2_profiles,
        )
    except k2.ModelError as error:
        raise K3Error(str(error)) from error


# ---------------------------------------------------------------------------
# Interface: external assignment and Statement meaning are separate questions
# ---------------------------------------------------------------------------


class ExternalVisibility(str, Enum):
    PUBLIC = "public"
    VERIFIER_CONFIDENTIAL = "verifier-confidential"


class ExternalInputRole(str, Enum):
    STATEMENT = "statement"
    CONTEXT = "context"
    PARAMETER = "parameter"
    VERIFIER_PRIVATE = "verifier-private"


class TransportRole(str, Enum):
    PROVER_TO_VERIFIER = "prover-to-verifier"
    VERIFIER_TO_PROVER = "verifier-to-prover"
    ORACLE_PUBLICATION = "oracle-publication"
    ORACLE_QUERY = "oracle-query"
    ORACLE_ANSWER = "oracle-answer"


@dataclass(frozen=True)
class BindingRef:
    scope: str
    input_name: str


@dataclass(frozen=True)
class InputAssignment:
    external_coordinate: str
    core_input: str
    role: ExternalInputRole
    visibility: ExternalVisibility
    codec_id: object = IDENTITY_CODEC


@dataclass(frozen=True)
class StatementAssignment:
    external_statement: str
    binding: BindingRef


@dataclass(frozen=True)
class TransportExposure:
    external_coordinate: str
    occurrence: str
    role: TransportRole
    codec_id: object = IDENTITY_CODEC


@dataclass(frozen=True)
class ProtocolInterface:
    protocol_id: object
    inputs: tuple[InputAssignment, ...]
    statements: tuple[StatementAssignment, ...]
    transports: tuple[TransportExposure, ...] = ()


_INPUT_ROLE = {
    k2.InputRole.STATEMENT: (
        ExternalInputRole.STATEMENT,
        ExternalVisibility.PUBLIC,
    ),
    k2.InputRole.PUBLIC_CONTEXT: (
        ExternalInputRole.CONTEXT,
        ExternalVisibility.PUBLIC,
    ),
    k2.InputRole.PUBLIC_PARAMETER: (
        ExternalInputRole.PARAMETER,
        ExternalVisibility.PUBLIC,
    ),
    k2.InputRole.VERIFIER_PRIVATE: (
        ExternalInputRole.VERIFIER_PRIVATE,
        ExternalVisibility.VERIFIER_CONFIDENTIAL,
    ),
}

_TRANSPORT_ROLE = {
    k2.OccurrenceKind.PROVER_MESSAGE: TransportRole.PROVER_TO_VERIFIER,
    k2.OccurrenceKind.VERIFIER_MESSAGE: TransportRole.VERIFIER_TO_PROVER,
    k2.OccurrenceKind.ORACLE_PUBLISH: TransportRole.ORACLE_PUBLICATION,
    k2.OccurrenceKind.ORACLE_QUERY: TransportRole.ORACLE_QUERY,
    k2.OccurrenceKind.ORACLE_ANSWER: TransportRole.ORACLE_ANSWER,
}


def binding_refs(core: object) -> tuple[BindingRef, ...]:
    k2.admit_core(core)
    return tuple(
        BindingRef(item.scope, item.name)
        for item in core.inputs
        if item.role is k2.InputRole.STATEMENT
    )


def admit_interface(
    core: object,
    construction: object | None,
    interpretation: object,
    interface: ProtocolInterface,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> None:
    k2.admit_core(core)
    if type(interface) is not ProtocolInterface:
        raise InterfaceError("Interface has the wrong exact shape")
    if interface.protocol_id != protocol_id(
        core,
        construction,
        interpretation,
        profiles=profiles,
    ):
        raise InterfaceError("Interface names the wrong Protocol")
    if len(interface.inputs) > MAX_INTERFACE_ENTRIES:
        raise InterfaceError("Interface input assignment exceeds its bound")
    input_names = tuple(item.core_input for item in interface.inputs)
    external_names = tuple(item.external_coordinate for item in interface.inputs)
    try:
        _bounded_unique(input_names, MAX_INTERFACE_ENTRIES, "Interface Core inputs")
        _bounded_unique(external_names, MAX_INTERFACE_ENTRIES, "external input coordinates")
    except K3Error as error:
        raise InterfaceError(str(error)) from error
    expected_inputs = {item.name: item for item in core.inputs}
    if set(input_names) != set(expected_inputs):
        raise InterfaceError(
            "Interface must assign exactly every public and verifier-private Core input"
        )
    for assignment in interface.inputs:
        if type(assignment) is not InputAssignment:
            raise InterfaceError("Interface input assignment has the wrong shape")
        expected_role, expected_visibility = _INPUT_ROLE[
            expected_inputs[assignment.core_input].role
        ]
        if (
            assignment.role is not expected_role
            or assignment.visibility is not expected_visibility
        ):
            raise InterfaceError("Interface input role or visibility disagrees with Core")
        _id_datum(assignment.codec_id, "foundation.canonical-algorithm")

    # Statement coverage is deliberately not inferred from the input lens.
    statement_external = tuple(item.external_statement for item in interface.statements)
    try:
        _bounded_unique(statement_external, MAX_INTERFACE_ENTRIES, "external Statements")
    except K3Error as error:
        raise InterfaceError(str(error)) from error
    expected_bindings = set(binding_refs(core))
    observed_bindings = {item.binding for item in interface.statements}
    if observed_bindings != expected_bindings:
        raise InterfaceError(
            "external Statement coverage must equal the scoped Statement BindingRef set"
        )
    if any(type(item) is not StatementAssignment for item in interface.statements):
        raise InterfaceError("Statement assignment has the wrong exact shape")

    occurrence_by_name = {item.name: item for item in core.schedule}
    transport_external = tuple(item.external_coordinate for item in interface.transports)
    transport_occurrences = tuple(item.occurrence for item in interface.transports)
    try:
        _bounded_unique(transport_external, MAX_INTERFACE_ENTRIES, "transport coordinates")
        _bounded_unique(transport_occurrences, MAX_INTERFACE_ENTRIES, "transport occurrences")
    except K3Error as error:
        raise InterfaceError(str(error)) from error
    for exposure in interface.transports:
        occurrence = occurrence_by_name.get(exposure.occurrence)
        if occurrence is None:
            raise InterfaceError("transport exposure names an unknown occurrence")
        expected = _TRANSPORT_ROLE.get(occurrence.kind)
        if expected is None or exposure.role is not expected:
            raise InterfaceError("transport role disagrees with occurrence kind")
        _id_datum(exposure.codec_id, "foundation.canonical-algorithm")


def interface_body(
    core: object,
    construction: object | None,
    interpretation: object,
    interface: ProtocolInterface,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    admit_interface(
        core,
        construction,
        interpretation,
        interface,
        profiles=profiles,
    )
    return k1.DatumRecord(
        (
            (0, k1.Symbol("k3.protocol-interface.probe.v0")),
            (1, _id_datum(interface.protocol_id, "pir.protocol")),
            (
                2,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.external_coordinate)),
                                (1, k1.Symbol(item.core_input)),
                                (2, k1.Symbol(item.role.value)),
                                (3, k1.Symbol(item.visibility.value)),
                                (4, _id_datum(item.codec_id, "foundation.canonical-algorithm")),
                            )
                        )
                        for item in interface.inputs
                    )
                ),
            ),
            (
                3,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.external_statement)),
                                (1, k1.Symbol(item.binding.scope)),
                                (2, k1.Symbol(item.binding.input_name)),
                            )
                        )
                        for item in interface.statements
                    )
                ),
            ),
            (
                4,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.external_coordinate)),
                                (1, k1.Symbol(item.occurrence)),
                                (2, k1.Symbol(item.role.value)),
                                (3, _id_datum(item.codec_id, "foundation.canonical-algorithm")),
                            )
                        )
                        for item in interface.transports
                    )
                ),
            ),
        )
    )


def interface_id(
    core: object,
    construction: object | None,
    interpretation: object,
    interface: ProtocolInterface,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "pir.protocol-interface",
        interface_body(
            core,
            construction,
            interpretation,
            interface,
            profiles=profiles,
        ),
        profiles=profiles,
    )


def default_interface(
    core: object,
    construction: object | None,
    interpretation: object,
    *,
    expose_all_transports: bool = False,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> ProtocolInterface:
    k2.admit_core(core)
    assignments = tuple(
        InputAssignment(
            f"input.{item.name}",
            item.name,
            _INPUT_ROLE[item.role][0],
            _INPUT_ROLE[item.role][1],
        )
        for item in core.inputs
    )
    statements = tuple(
        StatementAssignment(f"statement.{item.name}", BindingRef(item.scope, item.name))
        for item in core.inputs
        if item.role is k2.InputRole.STATEMENT
    )
    transports = (
        tuple(
            TransportExposure(
                f"effect.{item.name}",
                item.name,
                _TRANSPORT_ROLE[item.kind],
            )
            for item in core.schedule
            if item.kind in _TRANSPORT_ROLE
        )
        if expose_all_transports
        else ()
    )
    result = ProtocolInterface(
        protocol_id(core, construction, interpretation, profiles=profiles),
        assignments,
        statements,
        transports,
    )
    admit_interface(
        core,
        construction,
        interpretation,
        result,
        profiles=profiles,
    )
    return result


# ---------------------------------------------------------------------------
# Exact owner-issued correspondence read views
# ---------------------------------------------------------------------------


class ProtocolInterfaceReadKind(str, Enum):
    INVOCATION_ASSIGNMENT = "invocation-assignment"
    STATEMENT_MEMBER = "statement-member"
    TRANSPORT_ENTRY = "transport-entry"
    EXTERNAL_SLOT = "external-slot"
    INTERFACE_CODEC = "interface-codec"


@dataclass(frozen=True)
class ProtocolInterfaceRead:
    kind: ProtocolInterfaceReadKind
    coordinate: object


class RelationsReadKind(str, Enum):
    RELATION_TRANSFORM = "relation-transform"


@dataclass(frozen=True)
class RelationsRead:
    kind: RelationsReadKind
    coordinate: object


@dataclass(frozen=True)
class CorrespondenceReadManifest:
    protocol_interface: tuple[ProtocolInterfaceRead, ...]
    relations: tuple[RelationsRead, ...] = ()


@dataclass(frozen=True)
class RelationTransform:
    name: str
    input_interface_ids: tuple[object, ...]
    output_interface_ids: tuple[object, ...]
    public_derivation_id: object


def relation_transform_body(
    transform: RelationTransform,
) -> object:
    _ascii(transform.name, "relation transform")
    if (
        type(transform.input_interface_ids) is not tuple
        or not transform.input_interface_ids
        or type(transform.output_interface_ids) is not tuple
        or not transform.output_interface_ids
    ):
        raise RelationError("relation transform needs nonempty Interface domains")
    inputs = tuple(
        _id_datum(identifier, "relations.interface")
        for identifier in transform.input_interface_ids
    )
    outputs = tuple(
        _id_datum(identifier, "relations.interface")
        for identifier in transform.output_interface_ids
    )
    derivation = _id_datum(
        transform.public_derivation_id,
        "foundation.canonical-algorithm",
    )
    return k1.DatumRecord(
        (
            (0, k1.Symbol(transform.name)),
            (1, k1.DatumSeq(inputs)),
            (2, k1.DatumSeq(outputs)),
            (3, derivation),
        )
    )


def relation_transform_id(
    transform: RelationTransform,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "relations.transform",
        relation_transform_body(transform),
        profiles=profiles,
    )


_INTERFACE_READ_ORDER = MappingProxyType(
    {kind: index for index, kind in enumerate(ProtocolInterfaceReadKind)}
)
_RELATIONS_READ_ORDER = MappingProxyType(
    {kind: index for index, kind in enumerate(RelationsReadKind)}
)


def _read_coordinate_bytes(value: object) -> bytes:
    if type(value) is str:
        return value.encode("ascii")
    if type(value) is k1.TypedContentId:
        value.__post_init__()
        return value.internal_reference()
    raise K3Error("correspondence read has the wrong coordinate type")


def _interface_read_key(read: ProtocolInterfaceRead) -> tuple[int, bytes]:
    if type(read) is not ProtocolInterfaceRead or type(read.kind) is not ProtocolInterfaceReadKind:
        raise InterfaceError("Interface correspondence read has the wrong shape")
    return _INTERFACE_READ_ORDER[read.kind], _read_coordinate_bytes(read.coordinate)


def _relations_read_key(read: RelationsRead) -> tuple[int, bytes]:
    if type(read) is not RelationsRead or type(read.kind) is not RelationsReadKind:
        raise RelationError("Relations correspondence read has the wrong shape")
    return _RELATIONS_READ_ORDER[read.kind], _read_coordinate_bytes(read.coordinate)


def _source_authority_id(
    profile: object,
    subject_kind: str,
    body: object,
) -> object:
    if type(profile) is not k1.SemanticLanguageProfile:
        raise K3Error("source authority identity needs one exact semantic profile")
    return k1.profiled_content_id(
        subject_kind,
        profile.identity,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _source_authority_ref(identifier: object, what: str) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise KindMismatchK3Error(
            f"{what} must be one exact SemanticContentId coordinate"
        )
    try:
        identifier.__post_init__()
    except (k1.ModelError, k1.CanonicalError) as error:
        raise K3Error(f"{what} is a malformed SemanticContentId coordinate") from error
    if identifier.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise KindMismatchK3Error(
            f"{what} belongs to another semantic regime"
        )
    return k1.BytesValue(identifier.internal_reference())


def _require_semantic_coordinate(
    identifier: object,
    expected_subject_kind: str,
    what: str,
) -> None:
    _source_authority_ref(identifier, what)
    assert type(identifier) is k1.TypedContentId
    if identifier.subject_kind != expected_subject_kind:
        raise KindMismatchK3Error(
            f"{what} has subject kind {identifier.subject_kind!r}; "
            f"expected {expected_subject_kind!r}"
        )


def _source_authority_role_id(
    profile: object,
    subject_kind: str,
    family: object,
    identifier: object,
    what: str,
) -> object:
    return _source_authority_id(
        profile,
        subject_kind,
        k1.DatumRecord(
            (
                (0, family),
                (1, _source_authority_ref(identifier, what)),
            )
        ),
    )


def _source_authority_components(
    profile: object,
    subject_namespace: str,
    owner_domain: str,
    capability_family: str,
    source_body: object,
    manifest_body: object,
    consumer_coordinate: object,
    purpose_coordinate: object,
    *,
    pir_owner_compiler: object | None = None,
    pir_source_family: object | None = None,
) -> tuple[object, object, object, object, object, object]:
    family = k1.Symbol(_ascii(capability_family, "capability family"))
    owner_consumer_id = _source_authority_role_id(
        profile,
        f"{subject_namespace}.source-consumer",
        family,
        consumer_coordinate,
        "authority consumer",
    )
    owner_purpose_id = _source_authority_role_id(
        profile,
        f"{subject_namespace}.source-purpose",
        family,
        purpose_coordinate,
        "authority purpose",
    )
    consumer_ref = _source_authority_ref(
        owner_consumer_id,
        "authority consumer role",
    )
    purpose_ref = _source_authority_ref(
        owner_purpose_id,
        "authority purpose role",
    )
    if subject_namespace == "pir":
        if (
            owner_domain != "pir"
            or type(pir_owner_compiler) is not k2.PIRSourceOwnerCompiler
            or type(pir_source_family) is not k2.PIRSourceFamily
        ):
            raise K3Error("PIR source authority selected no exact owner compiler")

        def compile_body(subject_kind: object, local_body: object) -> object:
            return k2.compile_pir_source_subject_body(
                pir_owner_compiler,
                subject_kind,
                pir_source_family,
                local_body,
            )

        payload_body = compile_body(
            k2.PIRSourceSubjectKind.BINDING_PAYLOAD,
            k1.DatumRecord(((0, source_body), (1, manifest_body))),
        )
        no_policy_body = compile_body(
            k2.PIRSourceSubjectKind.NO_POLICY,
            k1.DatumRecord(
                (
                    (
                        0,
                        _source_authority_ref(
                            profile.identity,
                            "authority owner profile",
                        ),
                    ),
                )
            ),
        )
        requirement_body = compile_body(
            k2.PIRSourceSubjectKind.CAPABILITY_REQUIREMENT,
            k1.DatumRecord(((0, consumer_ref), (1, purpose_ref))),
        )
    else:
        if pir_owner_compiler is not None or pir_source_family is not None:
            raise K3Error("non-PIR authority cannot select a PIR source compiler")
        payload_body = k1.DatumRecord(
            (
                (0, k1.Symbol(owner_domain)),
                (1, family),
                (2, source_body),
                (3, manifest_body),
                (4, consumer_ref),
                (5, purpose_ref),
            )
        )
        no_policy_body = k1.DatumRecord(
            (
                (0, family),
                (1, _source_authority_ref(
                    _source_authority_id(
                        profile,
                        f"{subject_namespace}.source-binding-payload",
                        payload_body,
                    ),
                    "authority payload",
                )),
                (2, k1.Symbol("owner-defines-no-additional-operation-policy")),
            )
        )
        requirement_body = k1.DatumRecord(
            (
                (0, family),
                (1, _source_authority_ref(
                    _source_authority_id(
                        profile,
                        f"{subject_namespace}.source-binding-payload",
                        payload_body,
                    ),
                    "authority payload",
                )),
                (2, consumer_ref),
                (3, purpose_ref),
                (4, k1.Symbol("fresh-identical-bearer-capability")),
            )
        )
    payload_id = _source_authority_id(
        profile,
        f"{subject_namespace}.source-binding-payload",
        payload_body,
    )
    no_policy_id = _source_authority_id(
        profile,
        f"{subject_namespace}.source-no-policy",
        no_policy_body,
    )
    requirement_id = _source_authority_id(
        profile,
        f"{subject_namespace}.source-capability-requirement",
        requirement_body,
    )
    if subject_namespace == "pir":
        closure_body = compile_body(
            k2.PIRSourceSubjectKind.POLICY_CLOSURE,
            k1.DatumRecord(
                (
                    (0, _source_authority_ref(payload_id, "authority payload")),
                    (1, _source_authority_ref(no_policy_id, "no-policy declaration")),
                    (2, _source_authority_ref(requirement_id, "capability requirement")),
                )
            ),
        )
    else:
        closure_body = k1.DatumRecord(
            (
                (0, family),
                (1, _source_authority_ref(payload_id, "authority payload")),
                (2, _source_authority_ref(no_policy_id, "no-policy declaration")),
                (3, _source_authority_ref(requirement_id, "capability requirement")),
            )
        )
    closure_id = _source_authority_id(
        profile,
        f"{subject_namespace}.source-policy-closure",
        closure_body,
    )
    requirement = k1.OwnerCapabilityRequirement(
        k1.Symbol(owner_domain),
        family,
        requirement_id,
    )
    return (
        consumer_coordinate,
        purpose_coordinate,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    )


def _correspondence_read_datum(read: object) -> object:
    if type(read) is ProtocolInterfaceRead:
        kind = read.kind.value
        _interface_read_key(read)
    elif type(read) is RelationsRead:
        kind = read.kind.value
        _relations_read_key(read)
    else:
        raise K3Error("correspondence read has the wrong exact shape")
    coordinate = (
        k1.DatumVariant(0, k1.Symbol(read.coordinate))
        if type(read.coordinate) is str
        else k1.DatumVariant(1, _id_datum(read.coordinate))
    )
    return k1.DatumRecord(((0, k1.Symbol(kind)), (1, coordinate)))


def _correspondence_manifest_body(reads: tuple[object, ...]) -> object:
    return k1.DatumSeq(tuple(_correspondence_read_datum(read) for read in reads))


_INTERFACE_OWNER_FIELD_ORDINAL = MappingProxyType(
    {
        ProtocolInterfaceReadKind.INTERFACE_CODEC: 1,
        ProtocolInterfaceReadKind.EXTERNAL_SLOT: 2,
        ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT: 3,
        ProtocolInterfaceReadKind.STATEMENT_MEMBER: 4,
        ProtocolInterfaceReadKind.TRANSPORT_ENTRY: 5,
    }
)


def _protocol_interface_owner_manifest_body(
    reads: tuple[ProtocolInterfaceRead, ...],
) -> object:
    """Form the Interface owner payload's path-and-boundary manifest body."""

    seen: dict[ProtocolInterfaceReadKind, int] = {}
    coordinates: list[object] = []
    for read in reads:
        _interface_read_key(read)
        ordinal = seen.get(read.kind, 0)
        seen[read.kind] = ordinal + 1
        boundary_arm = (
            4
            if read.kind is ProtocolInterfaceReadKind.INTERFACE_CODEC
            else 3
        )
        coordinates.append(
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.DatumSeq(
                            (
                                k1.DatumVariant(
                                    0,
                                    k1.Nat(_INTERFACE_OWNER_FIELD_ORDINAL[read.kind]),
                                ),
                                k1.DatumVariant(2, k1.Nat(ordinal)),
                            )
                        ),
                    ),
                    (1, k1.DatumVariant(boundary_arm, k1.UNIT)),
                )
            )
        )
    return k1.DatumSeq(tuple(coordinates))


def _canonical_interface_reads(
    reads: set[ProtocolInterfaceRead],
) -> tuple[ProtocolInterfaceRead, ...]:
    return tuple(sorted(reads, key=_interface_read_key))


def required_protocol_interface_read_closure(
    interface: ProtocolInterface,
    requested: tuple[ProtocolInterfaceRead, ...],
) -> tuple[ProtocolInterfaceRead, ...]:
    """Derive the exact slot/codec closure, independently of returned entries."""

    if type(requested) is not tuple:
        raise InterfaceError("Interface correspondence manifest must be a tuple")
    input_by_core = {item.core_input: item for item in interface.inputs}
    input_by_external = {item.external_coordinate: item for item in interface.inputs}
    statement_by_external = {
        item.external_statement: item for item in interface.statements
    }
    transport_by_external = {
        item.external_coordinate: item for item in interface.transports
    }
    transport_by_occurrence = {item.occurrence: item for item in interface.transports}
    closure = set(requested)
    changed = True
    while changed:
        changed = False
        additions: set[ProtocolInterfaceRead] = set()
        for read in tuple(closure):
            _interface_read_key(read)
            if read.kind is ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT:
                if type(read.coordinate) is not str or read.coordinate not in input_by_core:
                    raise InterfaceError("invocation read names no exact assignment")
                assignment = input_by_core[read.coordinate]
                additions.update(
                    {
                        ProtocolInterfaceRead(
                            ProtocolInterfaceReadKind.EXTERNAL_SLOT,
                            assignment.external_coordinate,
                        ),
                        ProtocolInterfaceRead(
                            ProtocolInterfaceReadKind.INTERFACE_CODEC,
                            assignment.codec_id,
                        ),
                    }
                )
            elif read.kind is ProtocolInterfaceReadKind.STATEMENT_MEMBER:
                if type(read.coordinate) is not str or read.coordinate not in statement_by_external:
                    raise InterfaceError("Statement read names no exact member")
                member = statement_by_external[read.coordinate]
                assignment = input_by_core.get(member.binding.input_name)
                if assignment is None:
                    raise InterfaceError("Statement member has no invocation/slot source")
                additions.add(
                    ProtocolInterfaceRead(
                        ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT,
                        assignment.core_input,
                    )
                )
            elif read.kind is ProtocolInterfaceReadKind.TRANSPORT_ENTRY:
                if type(read.coordinate) is not str or read.coordinate not in transport_by_occurrence:
                    raise InterfaceError("transport read names no exact entry")
                exposure = transport_by_occurrence[read.coordinate]
                additions.update(
                    {
                        ProtocolInterfaceRead(
                            ProtocolInterfaceReadKind.EXTERNAL_SLOT,
                            exposure.external_coordinate,
                        ),
                        ProtocolInterfaceRead(
                            ProtocolInterfaceReadKind.INTERFACE_CODEC,
                            exposure.codec_id,
                        ),
                    }
                )
            elif read.kind is ProtocolInterfaceReadKind.EXTERNAL_SLOT:
                if type(read.coordinate) is not str:
                    raise InterfaceError("external-slot read needs one exact key")
                use = input_by_external.get(read.coordinate)
                transport = transport_by_external.get(read.coordinate)
                if (use is None) == (transport is None):
                    raise InterfaceError("external-slot read is absent or aliased")
                codec_id = use.codec_id if use is not None else transport.codec_id
                additions.add(
                    ProtocolInterfaceRead(
                        ProtocolInterfaceReadKind.INTERFACE_CODEC,
                        codec_id,
                    )
                )
            else:
                _id_datum(
                    read.coordinate,
                    "foundation.canonical-algorithm",
                )
                if not any(
                    item.codec_id == read.coordinate
                    for item in (*interface.inputs, *interface.transports)
                ):
                    raise InterfaceError("codec read names no exact Interface use")
        old_size = len(closure)
        closure.update(additions)
        changed = len(closure) != old_size
    return _canonical_interface_reads(closure)


def external_statement_read_manifest(
    interface: ProtocolInterface,
    members: tuple[str, ...],
) -> CorrespondenceReadManifest:
    if type(members) is not tuple or not members or len(members) != len(set(members)):
        raise InterfaceError("external Statement selection must be nonempty and unique")
    requested = tuple(
        ProtocolInterfaceRead(ProtocolInterfaceReadKind.STATEMENT_MEMBER, member)
        for member in members
    )
    return CorrespondenceReadManifest(
        required_protocol_interface_read_closure(interface, requested)
    )


def claim_reduction_transform_read_manifest(
    transform_ids: tuple[object, ...],
) -> CorrespondenceReadManifest:
    if type(transform_ids) is not tuple or not transform_ids:
        raise RelationError("claim/reduction shape needs at least one transform")
    reads = tuple(
        RelationsRead(RelationsReadKind.RELATION_TRANSFORM, identifier)
        for identifier in transform_ids
    )
    canonical = tuple(sorted(set(reads), key=_relations_read_key))
    if canonical != reads:
        raise RelationError("transform reads must be canonical and unique")
    return CorrespondenceReadManifest((), canonical)


@dataclass(frozen=True)
class ProtocolInterfaceCorrespondenceEntry:
    read: ProtocolInterfaceRead
    value: object


_INTERFACE_CORRESPONDENCE_VIEW_ISSUER = object()


@dataclass(frozen=True, slots=True)
class ProtocolInterfaceCorrespondenceView:
    protocol_interface_id: object
    requested_reads: tuple[ProtocolInterfaceRead, ...]
    entries: tuple[ProtocolInterfaceCorrespondenceEntry, ...]
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _INTERFACE_CORRESPONDENCE_VIEW_ISSUER:
            raise InterfaceError("only PIR may issue an Interface correspondence view")


ExactProtocolInterfaceViewAuthorityBinding = k1.OwnerLocalSourceAuthorityBinding


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class ProtocolInterfaceViewCapability(_NonTransferableAuthority):
    view: ProtocolInterfaceCorrespondenceView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _source: ProtocolInterface
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _INTERFACE_CORRESPONDENCE_VIEW_ISSUER:
            raise InterfaceError("only PIR may issue an Interface view capability")


@dataclass(frozen=True, eq=False, repr=False)
class IssuedProtocolInterfaceCorrespondenceView(_NonTransferableAuthority):
    view: ProtocolInterfaceCorrespondenceView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    capability: ProtocolInterfaceViewCapability
    _issuer: object


_INTERFACE_VIEW_LIVE_CAPABILITIES: dict[int, object] = {}
_INTERFACE_VIEW_LIVE_ISSUANCES: dict[int, object] = {}


def _interface_view_authority_components(
    view: ProtocolInterfaceCorrespondenceView,
    consumer_coordinate: object,
    purpose_coordinate: object,
    profiles: K3BSemanticProfiles,
) -> tuple[object, object, object, object, object, object]:
    return _source_authority_components(
        profiles.interface_plan,
        "pir",
        "pir",
        "interface-correspondence-view",
        _id_datum(view.protocol_interface_id, "pir.protocol-interface"),
        _protocol_interface_owner_manifest_body(view.requested_reads),
        consumer_coordinate,
        purpose_coordinate,
        pir_owner_compiler=k2.PIRSourceOwnerCompiler.INTERFACE_PLAN,
        pir_source_family=k2.PIRSourceFamily.INTERFACE_VIEW,
    )


def issue_protocol_interface_correspondence_view(
    core: object,
    construction: object | None,
    interpretation: object,
    interface: ProtocolInterface,
    manifest: CorrespondenceReadManifest,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    consumer_id: object,
    purpose_id: object,
) -> object:
    try:
        _source_authority_ref(consumer_id, "authority consumer coordinate")
        _source_authority_ref(purpose_id, "authority purpose coordinate")
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.interface_plan,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"pir.protocol-interface"})
            ),
        )
        admit_interface(
            core,
            construction,
            interpretation,
            interface,
            profiles=profiles,
        )
        if type(manifest) is not CorrespondenceReadManifest or manifest.relations:
            raise InterfaceError("Interface owner received the wrong submanifest")
        canonical = tuple(sorted(set(manifest.protocol_interface), key=_interface_read_key))
        if canonical != manifest.protocol_interface:
            raise InterfaceError("Interface submanifest is not canonical and unique")
        required = required_protocol_interface_read_closure(
            interface,
            manifest.protocol_interface,
        )
    except UnsupportedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.UNSUPPORTED,
            detail=(str(error),),
        )
    except RefusedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.REFUSED,
            detail=(str(error),),
        )
    except MalformedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    except KindMismatchK3Error as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.KIND_MISMATCH,
            detail=(str(error),),
        )
    except InterfaceError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    except K3Error as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    if required != manifest.protocol_interface:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MISSING_DEPENDENCY,
            detail=tuple(item for item in required if item not in manifest.protocol_interface),
        )
    input_by_core = {item.core_input: item for item in interface.inputs}
    input_by_external = {item.external_coordinate: item for item in interface.inputs}
    statement_by_external = {
        item.external_statement: item for item in interface.statements
    }
    transport_by_occurrence = {item.occurrence: item for item in interface.transports}
    transport_by_external = {
        item.external_coordinate: item for item in interface.transports
    }

    def resolve(read: ProtocolInterfaceRead) -> object:
        if read.kind is ProtocolInterfaceReadKind.INVOCATION_ASSIGNMENT:
            return input_by_core[read.coordinate]
        if read.kind is ProtocolInterfaceReadKind.STATEMENT_MEMBER:
            return statement_by_external[read.coordinate]
        if read.kind is ProtocolInterfaceReadKind.TRANSPORT_ENTRY:
            return transport_by_occurrence[read.coordinate]
        if read.kind is ProtocolInterfaceReadKind.EXTERNAL_SLOT:
            return input_by_external.get(read.coordinate) or transport_by_external[read.coordinate]
        return (
            read.coordinate,
            tuple(
                item.external_coordinate
                for item in (*interface.inputs, *interface.transports)
                if item.codec_id == read.coordinate
            ),
        )

    entries = tuple(
        ProtocolInterfaceCorrespondenceEntry(read, resolve(read))
        for read in manifest.protocol_interface
    )
    protocol_interface_id = interface_id(
        core,
        construction,
        interpretation,
        interface,
        profiles=profiles,
    )
    _authenticate_k3b_profiled_subject(
        protocol_interface_id,
        "pir.protocol-interface",
        interface_body(
            core,
            construction,
            interpretation,
            interface,
            profiles=profiles,
        ),
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profiles.interface_plan,
    )
    view = ProtocolInterfaceCorrespondenceView(
        protocol_interface_id,
        manifest.protocol_interface,
        entries,
        _INTERFACE_CORRESPONDENCE_VIEW_ISSUER,
    )
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _interface_view_authority_components(
        view,
        consumer_id,
        purpose_id,
        profiles,
    )
    binding = k1.OwnerLocalSourceAuthorityBinding(
        k1.Symbol("pir"),
        k1.Symbol("interface-correspondence-view"),
        view,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    k1.validate_owner_local_source_authority_binding(binding)
    capability = ProtocolInterfaceViewCapability(
        view,
        binding,
        consumer_id,
        purpose_id,
        interface,
        _INTERFACE_CORRESPONDENCE_VIEW_ISSUER,
    )
    _INTERFACE_VIEW_LIVE_CAPABILITIES[id(capability)] = capability
    issued = IssuedProtocolInterfaceCorrespondenceView(
        view,
        binding,
        capability,
        _INTERFACE_CORRESPONDENCE_VIEW_ISSUER,
    )
    _INTERFACE_VIEW_LIVE_ISSUANCES[id(issued)] = issued
    return k2.QualifiedViewOutcome(
        k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        issued,
    )


def validate_issued_protocol_interface_correspondence_view(
    issued: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> bool:
    if (
        type(issued) is not IssuedProtocolInterfaceCorrespondenceView
        or _INTERFACE_VIEW_LIVE_ISSUANCES.get(id(issued)) is not issued
        or issued._issuer is not _INTERFACE_CORRESPONDENCE_VIEW_ISSUER
        or type(issued.capability) is not ProtocolInterfaceViewCapability
        or _INTERFACE_VIEW_LIVE_CAPABILITIES.get(id(issued.capability))
        is not issued.capability
        or issued.capability._issuer is not _INTERFACE_CORRESPONDENCE_VIEW_ISSUER
        or issued.capability.view is not issued.view
        or issued.capability.source_binding is not issued.source_binding
        or type(issued.source_binding) is not k1.OwnerLocalSourceAuthorityBinding
        or issued.source_binding.owner_local_coordinate is not issued.view
    ):
        return False
    consumer_id = (
        issued.capability.consumer_id
        if expected_consumer_id is None
        else expected_consumer_id
    )
    purpose_id = (
        issued.capability.purpose_id
        if expected_purpose_id is None
        else expected_purpose_id
    )
    if (
        issued.capability.consumer_id != consumer_id
        or issued.capability.purpose_id != purpose_id
    ):
        return False
    try:
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.interface_plan,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"pir.protocol-interface"})
            ),
        )
        k1.validate_owner_local_source_authority_binding(issued.source_binding)
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _interface_view_authority_components(
            issued.view,
            consumer_id,
            purpose_id,
            profiles,
        )
    except (K3Error, k1.ModelError, k1.CanonicalError):
        return False
    binding = issued.source_binding
    return (
        binding.owner_domain == k1.Symbol("pir")
        and binding.capability_family
        == k1.Symbol("interface-correspondence-view")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    )


@dataclass(frozen=True)
class RelationsCorrespondenceEntry:
    read: RelationsRead
    value: RelationTransform


_RELATIONS_CORRESPONDENCE_VIEW_ISSUER = object()


@dataclass(frozen=True, slots=True)
class RelationsCorrespondenceView:
    requested_reads: tuple[RelationsRead, ...]
    entries: tuple[RelationsCorrespondenceEntry, ...]
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _RELATIONS_CORRESPONDENCE_VIEW_ISSUER:
            raise RelationError("only Relations may issue its correspondence view")


ExactRelationsCorrespondenceViewAuthorityBinding = k1.OwnerLocalSourceAuthorityBinding


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class RelationsCorrespondenceViewCapability(_NonTransferableAuthority):
    view: RelationsCorrespondenceView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _sources: tuple[RelationTransform, ...]
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _RELATIONS_CORRESPONDENCE_VIEW_ISSUER:
            raise RelationError("only Relations may issue a correspondence capability")


@dataclass(frozen=True, eq=False, repr=False)
class IssuedRelationsCorrespondenceView(_NonTransferableAuthority):
    view: RelationsCorrespondenceView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    capability: RelationsCorrespondenceViewCapability
    _issuer: object


_RELATIONS_VIEW_LIVE_CAPABILITIES: dict[int, object] = {}
_RELATIONS_VIEW_LIVE_ISSUANCES: dict[int, object] = {}


def _relations_view_authority_components(
    view: RelationsCorrespondenceView,
    consumer_coordinate: object,
    purpose_coordinate: object,
    profiles: K3BSemanticProfiles,
) -> tuple[object, object, object, object, object, object]:
    return _source_authority_components(
        profiles.relations_correspondence,
        "relations",
        "relations",
        "relations-correspondence-view",
        k1.DatumRecord(
            ((0, _correspondence_manifest_body(view.requested_reads)),)
        ),
        _correspondence_manifest_body(view.requested_reads),
        consumer_coordinate,
        purpose_coordinate,
    )


def issue_relations_correspondence_view(
    transforms: tuple[RelationTransform, ...],
    manifest: CorrespondenceReadManifest,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    consumer_id: object,
    purpose_id: object,
) -> object:
    try:
        _source_authority_ref(consumer_id, "authority consumer coordinate")
        _source_authority_ref(purpose_id, "authority purpose coordinate")
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.relations_correspondence,
            required_subject_kinds=(
                _RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"relations.transform"})
            ),
        )
        if type(manifest) is not CorrespondenceReadManifest or manifest.protocol_interface:
            raise RelationError("Relations owner received the wrong submanifest")
        transform_by_id: dict[object, RelationTransform] = {}
        for transform in transforms:
            transform_id = relation_transform_id(transform, profiles=profiles)
            _authenticate_k3b_profiled_subject(
                transform_id,
                "relations.transform",
                relation_transform_body(transform),
                profiles=profiles,
                profile_support=profile_support,
                selected_profile=profiles.relations_correspondence,
            )
            transform_by_id[transform_id] = transform
        if len(transform_by_id) != len(transforms):
            raise RelationError("relation transforms must have distinct identities")
        canonical = tuple(sorted(set(manifest.relations), key=_relations_read_key))
        if canonical != manifest.relations:
            raise RelationError("Relations submanifest is not canonical and unique")
        for read in manifest.relations:
            if read.kind is not RelationsReadKind.RELATION_TRANSFORM:
                raise RelationError("Relations submanifest has an unsupported read kind")
            _require_semantic_coordinate(
                read.coordinate,
                "relations.transform",
                "relation transform read coordinate",
            )
        requested_transform_ids = {
            read.coordinate
            for read in manifest.relations
            if read.kind is RelationsReadKind.RELATION_TRANSFORM
        }
        missing_transform_ids = requested_transform_ids - set(transform_by_id)
        if missing_transform_ids:
            raise KeyError(
                min(
                    missing_transform_ids,
                    key=lambda identifier: identifier.internal_reference(),
                )
            )
        if set(transform_by_id) != requested_transform_ids:
            raise RelationError(
                "Relations sources must equal the exact requested transform set"
            )
        entries = tuple(
            RelationsCorrespondenceEntry(read, transform_by_id[read.coordinate])
            for read in manifest.relations
        )
    except UnsupportedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.UNSUPPORTED,
            detail=(str(error),),
        )
    except RefusedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.REFUSED,
            detail=(str(error),),
        )
    except MalformedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    except KindMismatchK3Error as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.KIND_MISMATCH,
            detail=(str(error),),
        )
    except KeyError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MISSING_DEPENDENCY,
            detail=(error.args[0],),
        )
    except RelationError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    except K3Error as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    view = RelationsCorrespondenceView(
        manifest.relations,
        entries,
        _RELATIONS_CORRESPONDENCE_VIEW_ISSUER,
    )
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _relations_view_authority_components(
        view,
        consumer_id,
        purpose_id,
        profiles,
    )
    binding = k1.OwnerLocalSourceAuthorityBinding(
        k1.Symbol("relations"),
        k1.Symbol("relations-correspondence-view"),
        view,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    k1.validate_owner_local_source_authority_binding(binding)
    capability = RelationsCorrespondenceViewCapability(
        view,
        binding,
        consumer_id,
        purpose_id,
        transforms,
        _RELATIONS_CORRESPONDENCE_VIEW_ISSUER,
    )
    _RELATIONS_VIEW_LIVE_CAPABILITIES[id(capability)] = capability
    issued = IssuedRelationsCorrespondenceView(
        view,
        binding,
        capability,
        _RELATIONS_CORRESPONDENCE_VIEW_ISSUER,
    )
    _RELATIONS_VIEW_LIVE_ISSUANCES[id(issued)] = issued
    return k2.QualifiedViewOutcome(
        k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        issued,
    )


def validate_issued_relations_correspondence_view(
    issued: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> bool:
    if (
        type(issued) is not IssuedRelationsCorrespondenceView
        or _RELATIONS_VIEW_LIVE_ISSUANCES.get(id(issued)) is not issued
        or issued._issuer is not _RELATIONS_CORRESPONDENCE_VIEW_ISSUER
        or type(issued.capability) is not RelationsCorrespondenceViewCapability
        or _RELATIONS_VIEW_LIVE_CAPABILITIES.get(id(issued.capability))
        is not issued.capability
        or issued.capability._issuer is not _RELATIONS_CORRESPONDENCE_VIEW_ISSUER
        or issued.capability.view is not issued.view
        or issued.capability.source_binding is not issued.source_binding
        or type(issued.source_binding) is not k1.OwnerLocalSourceAuthorityBinding
        or issued.source_binding.owner_local_coordinate is not issued.view
    ):
        return False
    consumer_id = (
        issued.capability.consumer_id
        if expected_consumer_id is None
        else expected_consumer_id
    )
    purpose_id = (
        issued.capability.purpose_id
        if expected_purpose_id is None
        else expected_purpose_id
    )
    if (
        issued.capability.consumer_id != consumer_id
        or issued.capability.purpose_id != purpose_id
    ):
        return False
    try:
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.relations_correspondence,
            required_subject_kinds=(
                _RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"relations.transform"})
            ),
        )
        k1.validate_owner_local_source_authority_binding(issued.source_binding)
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _relations_view_authority_components(
            issued.view,
            consumer_id,
            purpose_id,
            profiles,
        )
    except (K3Error, k1.ModelError, k1.CanonicalError):
        return False
    binding = issued.source_binding
    return (
        binding.owner_domain == k1.Symbol("relations")
        and binding.capability_family
        == k1.Symbol("relations-correspondence-view")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    )


# ---------------------------------------------------------------------------
# Plan: one implementation of the K2 decision boundary, never Relation meaning
# ---------------------------------------------------------------------------


class PrivateMaterialKind(str, Enum):
    WITNESS_INGRESS = "witness-ingress"
    ADVICE = "advice"
    CONFIDENTIAL_CONTEXT = "confidential-context"


class PlanReadKind(str, Enum):
    PRIVATE_MATERIAL = "private-material"
    PRIVATE_RANDOMNESS = "private-randomness"
    STATE_BEFORE = "state-before"
    PUBLIC_INPUT_VIEW = "public-input-view"
    PRIOR_OCCURRENCE_VIEW = "prior-occurrence-view"


class MoveKind(str, Enum):
    MESSAGE_VALUE = "message-value"
    ORACLE_OBJECT = "oracle-object"


class StateAfterKind(str, Enum):
    KEEP = "keep"
    REPLACE_WITH_DECISION_OUTPUT = "replace-with-decision-output"


@dataclass(frozen=True)
class PrivateMaterialDecl:
    key: str
    kind: PrivateMaterialKind
    value_type: object


@dataclass(frozen=True)
class PrivateRandomnessRequirement:
    name: str
    value_type: object
    first_available_at: str


@dataclass(frozen=True)
class PersistentStrategyState:
    name: str
    value_type: object
    initial_private_material: str | None


@dataclass(frozen=True)
class PlanRead:
    kind: PlanReadKind
    name: str


@dataclass(frozen=True)
class StateAfterBinding:
    state: str
    kind: StateAfterKind


@dataclass(frozen=True)
class DecisionRoute:
    occurrence: str
    move_kind: MoveKind
    reads: tuple[PlanRead, ...]
    state_after: tuple[StateAfterBinding, ...]
    implementation_algorithm_id: object


@dataclass(frozen=True)
class PlanExport:
    key: str
    source_decision: str
    value_type: object


@dataclass(frozen=True)
class ProverPlan:
    protocol_id: object
    private_material: tuple[PrivateMaterialDecl, ...]
    randomness_requirements: tuple[PrivateRandomnessRequirement, ...]
    persistent_state: tuple[PersistentStrategyState, ...]
    decision_routes: tuple[DecisionRoute, ...]
    exports: tuple[PlanExport, ...]


def _decision_occurrences(core: object) -> tuple[object, ...]:
    return tuple(
        item
        for item in core.schedule
        if item.kind
        in {k2.OccurrenceKind.PROVER_MESSAGE, k2.OccurrenceKind.ORACLE_PUBLISH}
    )


def _decision_output_type(occurrence: object) -> object:
    if occurrence.kind is k2.OccurrenceKind.ORACLE_PUBLISH:
        return ORACLE_CELLS
    if occurrence.kind is k2.OccurrenceKind.PROVER_MESSAGE:
        return value_type_for_sort(occurrence.prover_value_sort)
    raise PlanError("occurrence is not a K2 prover decision")


def _private_influenced_occurrences(core: object) -> set[str]:
    """Return the legacy K2 occurrences whose fact or activity is private-tainted."""

    k2.admit_core(core)
    tainted: set[object] = {
        k2.ValueRef.input(item.name)
        for item in core.inputs
        if item.role is k2.InputRole.VERIFIER_PRIVATE
    }
    tainted_names: set[str] = set()
    prior_checks: list[object] = []
    for occurrence in core.schedule:
        sources = set(occurrence.dependencies) | set(occurrence.guard.refs)
        if occurrence.check_predicate is not None:
            sources.update(occurrence.check_predicate.refs)
        if occurrence.kind is k2.OccurrenceKind.TERMINAL:
            sources.update(prior_checks)
        output = k2.ValueRef.occurrence(occurrence.name)
        if sources & tainted:
            tainted.add(output)
            tainted_names.add(occurrence.name)
        if occurrence.kind is k2.OccurrenceKind.CHECK:
            prior_checks.append(output)
    return tainted_names


def _guard_implies(use_guard: object, source_guard: object) -> bool:
    """Use the closed K2 implication rule selected by the durable Core model."""

    return (
        source_guard.kind is k2.PredicateKind.ALWAYS
        or use_guard == source_guard
    )


def _guaranteed_public_input_read(
    core: object,
    decision: object,
    input_name: str,
) -> bool:
    """Apply the legacy K2 scope-opening rule to one public invocation input."""

    declaration = next((item for item in core.inputs if item.name == input_name), None)
    if declaration is None or declaration.role is k2.InputRole.VERIFIER_PRIVATE:
        return False
    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    decision_index = occurrence_index[decision.name]
    scopes = {item.name: item for item in core.scopes}
    scope = scopes[declaration.scope]
    while scope.parent is not None:
        if (
            scope.open_before is None
            or occurrence_index[scope.open_before] > decision_index
        ):
            return False
        scope = scopes[scope.parent]
    return True


def _guaranteed_prior_occurrence_read(
    core: object,
    decision: object,
    source_name: str,
) -> bool:
    """Bounded K2-owner read predicate for the legacy executable vocabulary."""

    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    source = next((item for item in core.schedule if item.name == source_name), None)
    if source is None or occurrence_index[source_name] >= occurrence_index[decision.name]:
        return False
    if source.kind not in {
        k2.OccurrenceKind.PROVER_MESSAGE,
        k2.OccurrenceKind.VERIFIER_MESSAGE,
        k2.OccurrenceKind.CHALLENGE,
        k2.OccurrenceKind.ORACLE_PUBLISH,
        k2.OccurrenceKind.ORACLE_QUERY,
        k2.OccurrenceKind.ORACLE_ANSWER,
    }:
        return False
    if not _guard_implies(decision.guard, source.guard):
        return False
    # This is a ProverView question, not a public-export question.  A
    # deterministic Verifier message may disclose a value derived from a
    # verifier-private input to the prover while remaining ineligible for a
    # public RelationRunView.
    return True


_PLAN_REALIZES_ISSUER = object()


@dataclass(frozen=True)
class CheckedPlanRealizes:
    _issuer: object
    protocol_id: object
    plan_id: object


def check_plan_realizes(
    core: object,
    construction: object | None,
    interpretation: object,
    plan: ProverPlan,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CheckedPlanRealizes:
    """Check decision coverage and owner-derived all-path read availability."""

    admit_plan(
        core,
        construction,
        interpretation,
        plan,
        profiles=profiles,
    )
    decisions = _decision_occurrences(core)
    decision_by_name = {item.name: item for item in decisions}
    route_by_name = {item.occurrence: item for item in plan.decision_routes}
    if set(route_by_name) != set(decision_by_name):
        raise PlanError("Plan must route exactly every K2 prover decision point")
    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    randomness = {item.name: item for item in plan.randomness_requirements}
    for route in plan.decision_routes:
        decision = decision_by_name[route.occurrence]
        for read in route.reads:
            if read.kind is PlanReadKind.PRIVATE_RANDOMNESS:
                first = randomness[read.name].first_available_at
                if occurrence_index[first] > occurrence_index[decision.name]:
                    raise PlanError(
                        "Plan route reads private randomness before its boundary"
                    )
            elif read.kind is PlanReadKind.PUBLIC_INPUT_VIEW:
                if not _guaranteed_public_input_read(core, decision, read.name):
                    raise PlanError(
                        "Plan route reads a public input before its K2 scope opens"
                    )
            elif read.kind is PlanReadKind.PRIOR_OCCURRENCE_VIEW:
                if not _guaranteed_prior_occurrence_read(core, decision, read.name):
                    raise PlanError(
                        "Plan route read is not one exact all-path K2 guaranteed read"
                    )
    return CheckedPlanRealizes(
        _PLAN_REALIZES_ISSUER,
        plan.protocol_id,
        plan_id(
            core,
            construction,
            interpretation,
            plan,
            profiles=profiles,
        ),
    )


def admit_plan(
    core: object,
    construction: object | None,
    interpretation: object,
    plan: ProverPlan,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> None:
    k2.admit_core(core)
    if (
        type(plan) is not ProverPlan
        or plan.protocol_id
        != protocol_id(
            core,
            construction,
            interpretation,
            profiles=profiles,
        )
    ):
        raise PlanError("Plan must name one exact admitted Protocol")
    if (
        len(plan.private_material) > MAX_PLAN_INPUTS
        or len(plan.randomness_requirements) > MAX_PLAN_INPUTS
        or len(plan.persistent_state) > MAX_PLAN_INPUTS
        or len(plan.decision_routes) > MAX_PLAN_ROUTES
        or len(plan.exports) > MAX_PLAN_INPUTS
    ):
        raise PlanError("Plan exceeds its finite bounds")
    private_by_name = {item.key: item for item in plan.private_material}
    if len(private_by_name) != len(plan.private_material):
        raise PlanError("Plan private-material keys must be unique")
    for item in plan.private_material:
        _ascii(item.key, "Plan private material")
        if type(item.kind) is not PrivateMaterialKind or type(item.value_type) is not k1.ValueType:
            raise PlanError("Plan private material has the wrong typed shape")

    randomness_by_name = {item.name: item for item in plan.randomness_requirements}
    if len(randomness_by_name) != len(plan.randomness_requirements):
        raise PlanError("private-randomness requirements must be unique")
    state_by_name = {item.name: item for item in plan.persistent_state}
    if len(state_by_name) != len(plan.persistent_state):
        raise PlanError("persistent strategy-state slots must be unique")
    decisions = _decision_occurrences(core)
    decision_by_name = {item.name: item for item in decisions}
    for item in plan.randomness_requirements:
        _ascii(item.name, "private-randomness requirement")
        if (
            type(item.value_type) is not k1.ValueType
            or item.first_available_at not in decision_by_name
        ):
            raise PlanError("private-randomness requirement has a bad type or boundary")
    for item in plan.persistent_state:
        _ascii(item.name, "persistent strategy-state slot")
        if type(item.value_type) is not k1.ValueType:
            raise PlanError("persistent state must carry one K1 ValueType")
        if item.initial_private_material is not None:
            source = private_by_name.get(item.initial_private_material)
            if source is None or source.value_type != item.value_type:
                raise PlanError("persistent state initializer is missing or mistyped")

    route_by_name = {item.occurrence: item for item in plan.decision_routes}
    if len(route_by_name) != len(plan.decision_routes):
        raise PlanError("Plan decision routes must be unique")
    if not set(route_by_name).issubset(decision_by_name):
        raise PlanError("Plan decision route names no K2 prover decision point")
    occurrence_by_name = {item.name: item for item in core.schedule}
    input_by_name = {item.name: item for item in core.inputs}
    for route in plan.decision_routes:
        occurrence = decision_by_name[route.occurrence]
        if (
            len(route.reads) > MAX_PLAN_INPUTS
            or len(route.state_after) > MAX_PLAN_INPUTS
        ):
            raise PlanError("Plan route reads or state updates exceed their finite bound")
        expected_move = (
            MoveKind.ORACLE_OBJECT
            if occurrence.kind is k2.OccurrenceKind.ORACLE_PUBLISH
            else MoveKind.MESSAGE_VALUE
        )
        if route.move_kind is not expected_move:
            raise PlanError("Plan route chooses the wrong legal move kind")
        _id_datum(
            route.implementation_algorithm_id, "foundation.canonical-algorithm"
        )
        if len(route.reads) != len(set(route.reads)):
            raise PlanError("Plan route reads must be unique")
        for read in route.reads:
            if type(read) is not PlanRead or type(read.kind) is not PlanReadKind:
                raise PlanError("Plan read has the wrong exact shape")
            if read.kind is PlanReadKind.PRIVATE_MATERIAL:
                if read.name not in private_by_name:
                    raise PlanError("Plan route reads undeclared private material")
            elif read.kind is PlanReadKind.PRIVATE_RANDOMNESS:
                requirement = randomness_by_name.get(read.name)
                if requirement is None:
                    raise PlanError("Plan route reads undeclared private randomness")
            elif read.kind is PlanReadKind.STATE_BEFORE:
                if read.name not in state_by_name:
                    raise PlanError("Plan route reads undeclared persistent state")
            elif read.kind is PlanReadKind.PUBLIC_INPUT_VIEW:
                declaration = input_by_name.get(read.name)
                if declaration is None or declaration.role is k2.InputRole.VERIFIER_PRIVATE:
                    raise PlanError("Plan route escapes the K2 public ProverView")
            else:
                if read.name not in occurrence_by_name:
                    raise PlanError("Plan route names no K2 occurrence")
        state_after = {item.state: item for item in route.state_after}
        if len(state_after) != len(route.state_after) or set(state_after) != set(state_by_name):
            raise PlanError("every decision route needs one total state-after map")
        output_type = _decision_output_type(occurrence)
        for update in route.state_after:
            if type(update) is not StateAfterBinding or type(update.kind) is not StateAfterKind:
                raise PlanError("state-after binding has the wrong exact shape")
            if (
                update.kind is StateAfterKind.REPLACE_WITH_DECISION_OUTPUT
                and state_by_name[update.state].value_type != output_type
            ):
                raise PlanError("decision output cannot replace a differently typed state slot")

    export_by_name = {item.key: item for item in plan.exports}
    if len(export_by_name) != len(plan.exports):
        raise PlanError("WitnessSurfaceKey values must be unique")
    if set(export_by_name) & set(private_by_name):
        raise PlanError("private material and derived witness exports share no key")
    for item in plan.exports:
        _ascii(item.key, "WitnessSurfaceKey")
        if type(item.value_type) is not k1.ValueType:
            raise PlanError("Plan export must carry one K1 ValueType")
        source = next(
            (
                occurrence
                for occurrence in decisions
                if occurrence.name == item.source_decision
            ),
            None,
        )
        if source is None:
            raise PlanError("Plan decision export names no decision output")
        if item.source_decision not in route_by_name:
            raise PlanError("Plan decision export names no admitted decision recipe")
        if _decision_output_type(source) != item.value_type:
            raise PlanError("Plan decision export type disagrees with its source output")


def plan_body(
    core: object,
    construction: object | None,
    interpretation: object,
    plan: ProverPlan,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    admit_plan(
        core,
        construction,
        interpretation,
        plan,
        profiles=profiles,
    )
    return k1.DatumRecord(
        (
            (0, k1.Symbol("k3.prover-plan.probe.v0")),
            (1, _id_datum(plan.protocol_id, "pir.protocol")),
            (
                2,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.key)),
                                (1, k1.Symbol(item.kind.value)),
                                (2, k1.value_type_datum(item.value_type)),
                            )
                        )
                        for item in plan.private_material
                    )
                ),
            ),
            (
                3,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.name)),
                                (1, k1.value_type_datum(item.value_type)),
                                (2, k1.Symbol(item.first_available_at)),
                            )
                        )
                        for item in plan.randomness_requirements
                    )
                ),
            ),
            (
                4,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.name)),
                                (1, k1.value_type_datum(item.value_type)),
                                (
                                    2,
                                    k1.DatumVariant(0, k1.UNIT)
                                    if item.initial_private_material is None
                                    else k1.DatumVariant(
                                        1, k1.Symbol(item.initial_private_material)
                                    ),
                                ),
                            )
                        )
                        for item in plan.persistent_state
                    )
                ),
            ),
            (
                5,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.occurrence)),
                                (1, k1.Symbol(item.move_kind.value)),
                                (
                                    2,
                                    k1.DatumSeq(
                                        tuple(
                                            k1.DatumRecord(
                                                (
                                                    (0, k1.Symbol(read.kind.value)),
                                                    (1, k1.Symbol(read.name)),
                                                )
                                            )
                                            for read in item.reads
                                        )
                                    ),
                                ),
                                (
                                    3,
                                    k1.DatumSeq(
                                        tuple(
                                            k1.DatumRecord(
                                                (
                                                    (0, k1.Symbol(update.state)),
                                                    (1, k1.Symbol(update.kind.value)),
                                                )
                                            )
                                            for update in item.state_after
                                        )
                                    ),
                                ),
                                (
                                    4,
                                    _id_datum(
                                        item.implementation_algorithm_id,
                                        "foundation.canonical-algorithm",
                                    ),
                                ),
                            )
                        )
                        for item in plan.decision_routes
                    )
                ),
            ),
            (
                6,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(item.key)),
                                (1, k1.Symbol(item.source_decision)),
                                (2, k1.value_type_datum(item.value_type)),
                            )
                        )
                        for item in plan.exports
                    )
                ),
            ),
        )
    )


def plan_id(
    core: object,
    construction: object | None,
    interpretation: object,
    plan: ProverPlan,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "pir.prover-plan",
        plan_body(
            core,
            construction,
            interpretation,
            plan,
            profiles=profiles,
        ),
        profiles=profiles,
    )


def plan_is_relation_free_by_construction() -> bool:
    """Mechanical guard against putting relation meaning back into Plan."""

    plan_classes = (
        PrivateMaterialDecl,
        PrivateRandomnessRequirement,
        PersistentStrategyState,
        PlanRead,
        DecisionRoute,
        PlanExport,
        ProverPlan,
    )
    return all(
        "relation" not in str(field.type).lower()
        for cls in plan_classes
        for field in fields(cls)
    )


class PlanWitnessEntryKind(str, Enum):
    WITNESS_INGRESS = "witness-ingress"
    DERIVED_WITNESS_EXPORT = "derived-witness-export"


@dataclass(frozen=True)
class PlanWitnessSurfaceEntry:
    key: str
    kind: PlanWitnessEntryKind
    value_type: object


@dataclass(frozen=True)
class PlanWitnessSurface:
    protocol_id: object
    entries: tuple[PlanWitnessSurfaceEntry, ...]


def derive_plan_witness_surface(
    core: object,
    construction: object | None,
    interpretation: object,
    plan: ProverPlan,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> PlanWitnessSurface:
    admit_plan(
        core,
        construction,
        interpretation,
        plan,
        profiles=profiles,
    )
    ingress = tuple(
        PlanWitnessSurfaceEntry(
            item.key, PlanWitnessEntryKind.WITNESS_INGRESS, item.value_type
        )
        for item in plan.private_material
        if item.kind is PrivateMaterialKind.WITNESS_INGRESS
    )
    derived = tuple(
        PlanWitnessSurfaceEntry(
            item.key,
            PlanWitnessEntryKind.DERIVED_WITNESS_EXPORT,
            item.value_type,
        )
        for item in plan.exports
    )
    entries = tuple(sorted(ingress + derived, key=lambda item: item.key))
    if len(entries) != len({item.key for item in entries}):
        raise PlanError("PlanWitnessSurface keys must be unique")
    return PlanWitnessSurface(plan.protocol_id, entries)


def plan_witness_surface_id(
    surface: PlanWitnessSurface,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    if type(surface) is not PlanWitnessSurface:
        raise PlanError("PlanWitnessSurface has the wrong exact shape")
    _id_datum(surface.protocol_id, "pir.protocol")
    if len(surface.entries) > MAX_PLAN_INPUTS:
        raise PlanError("PlanWitnessSurface exceeds its finite bound")
    keys = tuple(item.key for item in surface.entries)
    try:
        _bounded_unique(keys, MAX_PLAN_INPUTS, "WitnessSurfaceKey values")
    except K3Error as error:
        raise PlanError(str(error)) from error
    for item in surface.entries:
        if (
            type(item) is not PlanWitnessSurfaceEntry
            or type(item.kind) is not PlanWitnessEntryKind
            or type(item.value_type) is not k1.ValueType
        ):
            raise PlanError("PlanWitnessSurface entry has the wrong typed shape")
    return _semantic_id(
        "pir.plan-witness-surface",
        k1.DatumRecord(
            (
                (0, _id_datum(surface.protocol_id, "pir.protocol")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(item.key)),
                                    (1, k1.Symbol(item.kind.value)),
                                    (2, k1.value_type_datum(item.value_type)),
                                )
                            )
                            for item in surface.entries
                        )
                    ),
                ),
            )
        ),
        profiles=profiles,
    )


# ---------------------------------------------------------------------------
# Relations: four roles and two acyclic binding families
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RelationDefinitionRef:
    """One inert exact reference to a Relations-owned definition.

    Generic fixtures do not implement the durable definition language. The
    selected Schnorr fixed-setup subset below is the sole executable definition
    body, and no definition identity commits to a satisfaction evaluator.
    """

    definition_id: object


@dataclass(frozen=True)
class SchnorrRelationDefinition:
    """The bounded, Relations-owned fixed setup for the selected Schnorr relation."""

    generator: int
    scalar_modulus: int
    group_modulus: int


def admit_schnorr_relation_definition(
    definition: SchnorrRelationDefinition,
) -> None:
    if type(definition) is not SchnorrRelationDefinition:
        raise RelationError("Schnorr relation definition has the wrong exact shape")
    if any(
        type(value) is not int
        for value in (
            definition.generator,
            definition.scalar_modulus,
            definition.group_modulus,
        )
    ):
        raise RelationError("Schnorr relation parameters must be exact naturals")
    if (
        definition.group_modulus <= 2
        or definition.scalar_modulus <= 1
        or not 1 < definition.generator < definition.group_modulus
    ):
        raise RelationError("Schnorr relation parameters are outside their domains")
    if pow(
        definition.generator,
        definition.scalar_modulus,
        definition.group_modulus,
    ) != 1:
        raise RelationError("Schnorr generator is not in the declared scalar subgroup")


def schnorr_relation_definition_body(
    definition: SchnorrRelationDefinition,
) -> object:
    admit_schnorr_relation_definition(definition)
    return k1.DatumRecord(
        (
            (0, k1.Symbol("schnorr-discrete-log-knowledge-v0")),
            (1, k1.Nat(definition.generator)),
            (2, k1.Nat(definition.scalar_modulus)),
            (3, k1.Nat(definition.group_modulus)),
        )
    )


def schnorr_relation_definition_id(
    definition: SchnorrRelationDefinition,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "relations.definition",
        schnorr_relation_definition_body(definition),
        profiles=profiles,
    )


def selected_schnorr_relation_definition() -> SchnorrRelationDefinition:
    return SchnorrRelationDefinition(2, 11, 23)


class RelationDefinitionField(str, Enum):
    GENERATOR = "payload.generator"
    SCALAR_MODULUS = "payload.scalar-modulus"
    GROUP_MODULUS = "payload.group-modulus"


_RELATION_DEFINITION_FIELD_ORDER = MappingProxyType(
    {field: index for index, field in enumerate(RelationDefinitionField)}
)


@dataclass(frozen=True)
class RelationDefinitionViewCoordinate:
    definition_id: object
    semantic_profile_id: object


@dataclass(frozen=True)
class RelationDefinitionFieldCoordinate:
    view_coordinate: RelationDefinitionViewCoordinate
    field: RelationDefinitionField


@dataclass(frozen=True)
class RelationDefinitionViewEntry:
    coordinate: RelationDefinitionFieldCoordinate
    value: int


_RELATION_DEFINITION_VIEW_ISSUER = object()


@dataclass(frozen=True, slots=True)
class RelationDefinitionView:
    coordinate: RelationDefinitionViewCoordinate
    manifest: tuple[RelationDefinitionFieldCoordinate, ...]
    entries: tuple[RelationDefinitionViewEntry, ...]
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _RELATION_DEFINITION_VIEW_ISSUER:
            raise RelationError("only Relations may issue a definition view")


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class RelationDefinitionViewCapability(_NonTransferableAuthority):
    view: RelationDefinitionView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _source: SchnorrRelationDefinition
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _RELATION_DEFINITION_VIEW_ISSUER:
            raise RelationError("only Relations may issue a definition capability")


@dataclass(frozen=True, eq=False, repr=False)
class IssuedRelationDefinitionView(_NonTransferableAuthority):
    view: RelationDefinitionView
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    capability: RelationDefinitionViewCapability
    _issuer: object


_RELATION_DEFINITION_VIEW_LIVE_CAPABILITIES: dict[int, object] = {}
_RELATION_DEFINITION_VIEW_LIVE_ISSUANCES: dict[int, object] = {}


def relation_definition_field_coordinate(
    definition: SchnorrRelationDefinition,
    field: RelationDefinitionField,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> RelationDefinitionFieldCoordinate:
    if type(field) is not RelationDefinitionField:
        raise RelationError("relation definition field has the wrong exact kind")
    return RelationDefinitionFieldCoordinate(
        RelationDefinitionViewCoordinate(
            schnorr_relation_definition_id(definition, profiles=profiles),
            profiles.relations_correspondence.identity,
        ),
        field,
    )


def schnorr_fixed_setup_manifest(
    definition: SchnorrRelationDefinition,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> tuple[RelationDefinitionFieldCoordinate, ...]:
    return tuple(
        relation_definition_field_coordinate(definition, field, profiles=profiles)
        for field in RelationDefinitionField
    )


def _relation_definition_field_coordinate_body(
    coordinate: RelationDefinitionFieldCoordinate,
) -> object:
    if (
        type(coordinate) is not RelationDefinitionFieldCoordinate
        or type(coordinate.view_coordinate) is not RelationDefinitionViewCoordinate
        or type(coordinate.field) is not RelationDefinitionField
    ):
        raise RelationError("relation definition field coordinate is malformed")
    return k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    coordinate.view_coordinate.definition_id,
                    "relations.definition",
                ),
            ),
            (
                1,
                _id_datum(
                    coordinate.view_coordinate.semantic_profile_id,
                    "foundation.semantic-language-profile",
                ),
            ),
            (2, k1.Symbol(coordinate.field.value)),
        )
    )


def _relation_definition_manifest_body(
    manifest: tuple[RelationDefinitionFieldCoordinate, ...],
) -> object:
    return k1.DatumSeq(
        tuple(_relation_definition_field_coordinate_body(item) for item in manifest)
    )


def _relation_definition_view_authority_components(
    view: RelationDefinitionView,
    consumer_coordinate: object,
    purpose_coordinate: object,
    profiles: K3BSemanticProfiles,
) -> tuple[object, object, object, object, object, object]:
    return _source_authority_components(
        profiles.relations_correspondence,
        "relations",
        "relations",
        "relation-definition-view",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        view.coordinate.definition_id,
                        "relations.definition",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        view.coordinate.semantic_profile_id,
                        "foundation.semantic-language-profile",
                    ),
                ),
            )
        ),
        _relation_definition_manifest_body(view.manifest),
        consumer_coordinate,
        purpose_coordinate,
    )


def _relation_definition_field_value(
    definition: SchnorrRelationDefinition,
    field: RelationDefinitionField,
) -> int:
    if field is RelationDefinitionField.GENERATOR:
        return definition.generator
    if field is RelationDefinitionField.SCALAR_MODULUS:
        return definition.scalar_modulus
    return definition.group_modulus


def issue_relation_definition_view(
    definition: SchnorrRelationDefinition,
    manifest: tuple[RelationDefinitionFieldCoordinate, ...],
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    consumer_id: object,
    purpose_id: object,
) -> object:
    try:
        _source_authority_ref(consumer_id, "authority consumer coordinate")
        _source_authority_ref(purpose_id, "authority purpose coordinate")
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.relations_correspondence,
            required_subject_kinds=(
                _RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"relations.definition"})
            ),
        )
        body = schnorr_relation_definition_body(definition)
        definition_id = schnorr_relation_definition_id(definition, profiles=profiles)
        _authenticate_k3b_profiled_subject(
            definition_id,
            "relations.definition",
            body,
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=profiles.relations_correspondence,
        )
        expected_view_coordinate = RelationDefinitionViewCoordinate(
            definition_id,
            profiles.relations_correspondence.identity,
        )
        if type(manifest) is not tuple or not manifest:
            raise RelationError("relation definition manifest must be nonempty")
        for item in manifest:
            if (
                type(item) is not RelationDefinitionFieldCoordinate
                or type(item.view_coordinate) is not RelationDefinitionViewCoordinate
                or type(item.field) is not RelationDefinitionField
            ):
                raise RelationError("relation definition manifest is malformed")
            _require_semantic_coordinate(
                item.view_coordinate.definition_id,
                "relations.definition",
                "relation definition view coordinate",
            )
            _require_semantic_coordinate(
                item.view_coordinate.semantic_profile_id,
                "foundation.semantic-language-profile",
                "relation definition profile coordinate",
            )
            if item.view_coordinate != expected_view_coordinate:
                raise RefusedK3AuthorityError(
                    "relation definition manifest substitutes another "
                    "same-kind definition or profile"
                )
        canonical = tuple(
            sorted(
                set(manifest),
                key=lambda item: _RELATION_DEFINITION_FIELD_ORDER[item.field],
            )
        )
        if canonical != manifest:
            raise RelationError("relation definition manifest is not canonical and unique")
        entries = tuple(
            RelationDefinitionViewEntry(
                item,
                _relation_definition_field_value(definition, item.field),
            )
            for item in manifest
        )
    except UnsupportedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.UNSUPPORTED,
            detail=(str(error),),
        )
    except RefusedK3BSemanticProfileError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.REFUSED,
            detail=(str(error),),
        )
    except RefusedK3AuthorityError as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.REFUSED,
            detail=(str(error),),
        )
    except KindMismatchK3Error as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.KIND_MISMATCH,
            detail=(str(error),),
        )
    except (MalformedK3BSemanticProfileError, RelationError, K3Error) as error:
        return k2.QualifiedViewOutcome(
            k2.QualifiedViewOutcomeKind.MALFORMED,
            detail=(str(error),),
        )
    view = RelationDefinitionView(
        expected_view_coordinate,
        manifest,
        entries,
        _RELATION_DEFINITION_VIEW_ISSUER,
    )
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _relation_definition_view_authority_components(
        view,
        consumer_id,
        purpose_id,
        profiles,
    )
    binding = k1.OwnerLocalSourceAuthorityBinding(
        k1.Symbol("relations"),
        k1.Symbol("relation-definition-view"),
        view,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    k1.validate_owner_local_source_authority_binding(binding)
    capability = RelationDefinitionViewCapability(
        view,
        binding,
        consumer_id,
        purpose_id,
        definition,
        _RELATION_DEFINITION_VIEW_ISSUER,
    )
    _RELATION_DEFINITION_VIEW_LIVE_CAPABILITIES[id(capability)] = capability
    issued = IssuedRelationDefinitionView(
        view,
        binding,
        capability,
        _RELATION_DEFINITION_VIEW_ISSUER,
    )
    _RELATION_DEFINITION_VIEW_LIVE_ISSUANCES[id(issued)] = issued
    return k2.QualifiedViewOutcome(k2.QualifiedViewOutcomeKind.AFFIRMATIVE, issued)


def validate_issued_relation_definition_view(
    issued: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
    profile_support: K3BSemanticProfileSupport = K3B_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> bool:
    if (
        type(issued) is not IssuedRelationDefinitionView
        or _RELATION_DEFINITION_VIEW_LIVE_ISSUANCES.get(id(issued)) is not issued
        or issued._issuer is not _RELATION_DEFINITION_VIEW_ISSUER
        or type(issued.capability) is not RelationDefinitionViewCapability
        or _RELATION_DEFINITION_VIEW_LIVE_CAPABILITIES.get(id(issued.capability))
        is not issued.capability
        or issued.capability._issuer is not _RELATION_DEFINITION_VIEW_ISSUER
        or issued.capability.view is not issued.view
        or issued.capability.source_binding is not issued.source_binding
        or type(issued.source_binding) is not k1.OwnerLocalSourceAuthorityBinding
        or issued.source_binding.owner_local_coordinate is not issued.view
    ):
        return False
    consumer_id = (
        issued.capability.consumer_id
        if expected_consumer_id is None
        else expected_consumer_id
    )
    purpose_id = (
        issued.capability.purpose_id
        if expected_purpose_id is None
        else expected_purpose_id
    )
    if (
        issued.capability.consumer_id != consumer_id
        or issued.capability.purpose_id != purpose_id
    ):
        return False
    try:
        _require_supported_k3b_profile(
            profiles,
            profile_support,
            profiles.relations_correspondence,
            required_subject_kinds=(
                _RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"relations.definition"})
            ),
        )
        definition = issued.capability._source
        expected_id = schnorr_relation_definition_id(definition, profiles=profiles)
        expected_coordinate = RelationDefinitionViewCoordinate(
            expected_id,
            profiles.relations_correspondence.identity,
        )
        expected_entries = tuple(
            RelationDefinitionViewEntry(
                item,
                _relation_definition_field_value(definition, item.field),
            )
            for item in issued.view.manifest
        )
        if (
            issued.view.coordinate != expected_coordinate
            or issued.view.entries != expected_entries
        ):
            return False
        k1.validate_owner_local_source_authority_binding(issued.source_binding)
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _relation_definition_view_authority_components(
            issued.view,
            consumer_id,
            purpose_id,
            profiles,
        )
    except (K3Error, k1.ModelError, k1.CanonicalError):
        return False
    binding = issued.source_binding
    return (
        binding.owner_domain == k1.Symbol("relations")
        and binding.capability_family == k1.Symbol("relation-definition-view")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    )


@dataclass(frozen=True)
class RelationSlot:
    name: str
    value_type: object


@dataclass(frozen=True)
class RelationOracleStatementDecl:
    name: str
    public_binding_type: object
    material_type: object
    index_type: object
    answer_type: object
    access_law_id: object


@dataclass(frozen=True)
class RelationInterface:
    definition_id: object
    public_instance: tuple[RelationSlot, ...]
    private_witness: tuple[RelationSlot, ...]
    oracle_statements: tuple[RelationOracleStatementDecl, ...]
    phase_inputs: tuple[RelationSlot, ...]
    requires_claim: bool = True


def admit_relation_definition_ref(definition: RelationDefinitionRef) -> None:
    if type(definition) is not RelationDefinitionRef:
        raise RelationError("relation definition reference has the wrong exact shape")
    _id_datum(definition.definition_id, "relations.definition")


def fixture_relation_definition_ref(label: str) -> RelationDefinitionRef:
    """Create only an inert typed fixture reference, never a definition body."""

    result = RelationDefinitionRef(
        fixture_semantic_ref("relations.definition", _ascii(label, "relation label"))
    )
    admit_relation_definition_ref(result)
    return result


def _slot_body(slot: RelationSlot) -> object:
    return k1.DatumRecord(
        ((0, k1.Symbol(slot.name)), (1, k1.value_type_datum(slot.value_type)))
    )


def admit_relation_interface(interface: RelationInterface) -> None:
    if type(interface) is not RelationInterface:
        raise RelationError("relation Interface has the wrong exact shape")
    _id_datum(interface.definition_id, "relations.definition")
    if type(interface.requires_claim) is not bool:
        raise RelationError("relation claim requirement must be Boolean")
    all_named = (
        interface.public_instance
        + interface.private_witness
        + interface.phase_inputs
    )
    names = tuple(item.name for item in all_named) + tuple(
        item.name for item in interface.oracle_statements
    )
    try:
        _bounded_unique(names, MAX_RELATION_OCCURRENCES, "relation Interface slots")
    except K3Error as error:
        raise RelationError(str(error)) from error
    for slot in all_named:
        if type(slot) is not RelationSlot or type(slot.value_type) is not k1.ValueType:
            raise RelationError("relation slot must carry one exact K1 ValueType")
    for slot in interface.oracle_statements:
        if type(slot) is not RelationOracleStatementDecl:
            raise RelationError("OracleStatement has the wrong exact shape")
        for value_type in (
            slot.public_binding_type,
            slot.material_type,
            slot.index_type,
            slot.answer_type,
        ):
            if type(value_type) is not k1.ValueType:
                raise RelationError("OracleStatement fields need exact K1 ValueTypes")
        _id_datum(slot.access_law_id, "relations.oracle-access-law")


def relation_interface_id(
    interface: RelationInterface,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    admit_relation_interface(interface)
    return _semantic_id(
        "relations.interface",
        k1.DatumRecord(
            (
                (0, _id_datum(interface.definition_id, "relations.definition")),
                (1, k1.DatumSeq(tuple(_slot_body(x) for x in interface.public_instance))),
                (2, k1.DatumSeq(tuple(_slot_body(x) for x in interface.private_witness))),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(x.name)),
                                    (1, k1.value_type_datum(x.public_binding_type)),
                                    (2, k1.value_type_datum(x.material_type)),
                                    (3, k1.value_type_datum(x.index_type)),
                                    (4, k1.value_type_datum(x.answer_type)),
                                    (
                                        5,
                                        _id_datum(
                                            x.access_law_id,
                                            "relations.oracle-access-law",
                                        ),
                                    ),
                                )
                            )
                            for x in interface.oracle_statements
                        )
                    ),
                ),
                (4, k1.DatumSeq(tuple(_slot_body(x) for x in interface.phase_inputs))),
                (5, interface.requires_claim),
            )
        ),
        profiles=profiles,
    )


class ValueBridgeLane(str, Enum):
    TOTAL_EQUIVALENCE = "total-equivalence"
    INJECTIVE_EMBEDDING = "injective-embedding"
    DIRECTIONAL_LOSSY = "directional-lossy"


class BridgeDirection(str, Enum):
    FORWARD = "forward"
    BACKWARD = "backward"


@dataclass(frozen=True)
class ValueBridge:
    name: str
    lane: ValueBridgeLane
    source_type: object
    target_type: object
    forward_algorithm_id: object
    inverse_algorithm_id: object | None = None
    image_predicate_id: object | None = None
    collision_relation_id: object | None = None
    source_premise_id: object | None = None
    quantitative_export_id: object | None = None


def admit_value_bridge(bridge: ValueBridge) -> None:
    if type(bridge) is not ValueBridge:
        raise BridgeError("value bridge has the wrong exact shape")
    _ascii(bridge.name, "value bridge")
    if type(bridge.source_type) is not k1.ValueType or type(bridge.target_type) is not k1.ValueType:
        raise BridgeError("value bridge endpoints must be exact K1 ValueTypes")
    _id_datum(bridge.forward_algorithm_id, "foundation.canonical-algorithm")
    if bridge.inverse_algorithm_id is not None:
        _id_datum(bridge.inverse_algorithm_id, "foundation.canonical-algorithm")
    if bridge.image_predicate_id is not None:
        _id_datum(bridge.image_predicate_id, "relations.predicate")
    if bridge.collision_relation_id is not None:
        _id_datum(bridge.collision_relation_id, "relations.definition")
    if bridge.source_premise_id is not None:
        _id_datum(bridge.source_premise_id, "relations.loss-source-premise")
    if bridge.quantitative_export_id is not None:
        _id_datum(bridge.quantitative_export_id, "relations.loss-export")
    if bridge.lane is ValueBridgeLane.TOTAL_EQUIVALENCE:
        if (
            bridge.inverse_algorithm_id is None
            or bridge.image_predicate_id is not None
            or bridge.collision_relation_id is not None
            or bridge.source_premise_id is not None
            or bridge.quantitative_export_id is not None
        ):
            raise BridgeError("total equivalence needs exactly forward and inverse algorithms")
    elif bridge.lane is ValueBridgeLane.INJECTIVE_EMBEDDING:
        if (
            bridge.inverse_algorithm_id is None
            or bridge.image_predicate_id is None
            or bridge.collision_relation_id is not None
            or bridge.source_premise_id is not None
            or bridge.quantitative_export_id is not None
        ):
            raise BridgeError("embedding needs inverse-on-image and image-predicate algorithms")
    elif bridge.lane is ValueBridgeLane.DIRECTIONAL_LOSSY:
        if (
            bridge.inverse_algorithm_id is not None
            or bridge.image_predicate_id is not None
            or bridge.collision_relation_id is None
            or bridge.source_premise_id is None
            or bridge.quantitative_export_id is None
        ):
            raise BridgeError(
                "lossy projection needs collision, source-premise, and loss-export declarations"
            )
    else:
        raise BridgeError("unsupported value bridge lane")


def value_bridge_id(
    bridge: ValueBridge,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    admit_value_bridge(bridge)

    def optional(identifier: object | None, expected: str) -> object:
        return (
            k1.DatumVariant(0, k1.UNIT)
            if identifier is None
            else k1.DatumVariant(1, _id_datum(identifier, expected))
        )

    return _semantic_id(
        "relations.value-bridge",
        k1.DatumRecord(
            (
                (0, k1.Symbol(bridge.name)),
                (1, k1.Symbol(bridge.lane.value)),
                (2, k1.value_type_datum(bridge.source_type)),
                (3, k1.value_type_datum(bridge.target_type)),
                (4, _id_datum(bridge.forward_algorithm_id, "foundation.canonical-algorithm")),
                (5, optional(bridge.inverse_algorithm_id, "foundation.canonical-algorithm")),
                (6, optional(bridge.image_predicate_id, "relations.predicate")),
                (7, optional(bridge.collision_relation_id, "relations.definition")),
                (
                    8,
                    optional(
                        bridge.source_premise_id,
                        "relations.loss-source-premise",
                    ),
                ),
                (
                    9,
                    optional(
                        bridge.quantitative_export_id,
                        "relations.loss-export",
                    ),
                ),
            )
        ),
        profiles=profiles,
    )


@dataclass(frozen=True)
class ValueRelation:
    bridge_id: object | None = None
    direction: BridgeDirection | None = None


SAME_EXACT_TYPE = ValueRelation()


def _bridge_registry(
    bridges: tuple[ValueBridge, ...],
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> dict[object, ValueBridge]:
    if len(bridges) > MAX_RELATION_OCCURRENCES:
        raise BridgeError("value bridge registry exceeds its finite bound")
    result: dict[object, ValueBridge] = {}
    for bridge in bridges:
        identifier = value_bridge_id(bridge, profiles=profiles)
        if identifier in result:
            raise BridgeError("value bridge registry contains a duplicate identity")
        result[identifier] = bridge
    return result


def _check_value_relation(
    source_type: object,
    target_type: object,
    relation: ValueRelation,
    bridges: Mapping[object, ValueBridge],
) -> None:
    if type(relation) is not ValueRelation:
        raise BridgeError("value relation has the wrong exact shape")
    if relation.bridge_id is None:
        if relation.direction is not None or source_type != target_type:
            raise BridgeError("SameExactType requires literal endpoint type equality")
        return
    _id_datum(relation.bridge_id, "relations.value-bridge")
    bridge = bridges.get(relation.bridge_id)
    if bridge is None or type(relation.direction) is not BridgeDirection:
        raise BridgeError("value relation names no admitted directed bridge")
    if relation.direction is BridgeDirection.FORWARD:
        expected = (bridge.source_type, bridge.target_type)
    else:
        if bridge.lane is ValueBridgeLane.DIRECTIONAL_LOSSY:
            raise BridgeError("lossy projection has no backward application")
        expected = (bridge.target_type, bridge.source_type)
    if (source_type, target_type) != expected:
        raise BridgeError("bridge direction does not match the exact edge endpoint types")


class ClaimOrigin(str, Enum):
    INITIAL = "initial"
    REDUCTION_OUTPUT = "reduction-output"


@dataclass(frozen=True)
class ClaimCoordinate:
    origin: ClaimOrigin
    claim: str
    producer: str | None = None


@dataclass(frozen=True)
class RelationInstanceOccurrence:
    name: str
    relation_interface_id: object


@dataclass(frozen=True)
class PublicSlotEdge:
    instance: str
    slot: str
    source: object  # BindingRef or exact K2 ValueRef
    value_relation: ValueRelation = SAME_EXACT_TYPE


@dataclass(frozen=True)
class PhaseSlotEdge:
    instance: str
    slot: str
    source: object  # exact K2 ValueRef
    value_relation: ValueRelation = SAME_EXACT_TYPE


@dataclass(frozen=True)
class OracleSlotEdge:
    instance: str
    slot: str
    publication: object
    query: object
    answer: object


@dataclass(frozen=True)
class ClaimEdge:
    instance: str
    claim: ClaimCoordinate


@dataclass(frozen=True)
class ProtocolRelationBinding:
    protocol_id: object
    relation_interface_ids: tuple[object, ...]
    instances: tuple[RelationInstanceOccurrence, ...]
    public_edges: tuple[PublicSlotEdge, ...]
    phase_edges: tuple[PhaseSlotEdge, ...]
    oracle_edges: tuple[OracleSlotEdge, ...]
    claim_edges: tuple[ClaimEdge, ...]


@dataclass(frozen=True)
class WitnessSlotEdge:
    slot: str
    witness_surface_key: str
    value_relation: ValueRelation = SAME_EXACT_TYPE


@dataclass(frozen=True)
class PlanWitnessBinding:
    plan_witness_surface_id: object
    relation_interface_id: object
    witness_edges: tuple[WitnessSlotEdge, ...]


_PROTOCOL_BINDING_ISSUER = object()
_PLAN_BINDING_ISSUER = object()


@dataclass(frozen=True)
class CheckedProtocolRelationBinding:
    _issuer: object
    _profiles: K3BSemanticProfiles
    binding_id: object
    binding: ProtocolRelationBinding
    missing_public: tuple[tuple[str, str], ...]
    missing_phase: tuple[tuple[str, str], ...]
    missing_oracle: tuple[tuple[str, str], ...]
    missing_claim: tuple[str, ...]

    @property
    def whole(self) -> bool:
        return not (
            self.missing_public
            or self.missing_phase
            or self.missing_oracle
            or self.missing_claim
        )


@dataclass(frozen=True)
class CheckedPlanWitnessBinding:
    _issuer: object
    _profiles: K3BSemanticProfiles
    binding_id: object
    binding: PlanWitnessBinding
    surface: PlanWitnessSurface
    missing_witness: tuple[str, ...]

    @property
    def whole(self) -> bool:
        return not self.missing_witness


def _claim_exists(core: object, coordinate: ClaimCoordinate) -> bool:
    if type(coordinate) is not ClaimCoordinate or type(coordinate.origin) is not ClaimOrigin:
        return False
    if coordinate.origin is ClaimOrigin.INITIAL:
        return coordinate.producer is None and coordinate.claim in core.initial_claims
    return any(
        step.name == coordinate.producer and coordinate.claim in step.output_claims
        for step in core.reductions
    )


def _core_value_types(core: object) -> dict[object, object]:
    sorts: dict[object, object] = {
        k2.ValueRef.input(item.name): item.value_sort for item in core.inputs
    }
    for occurrence in core.schedule:
        sorts[k2.ValueRef.occurrence(occurrence.name)] = k2._occurrence_sort(
            occurrence, sorts
        )
    return {ref: value_type_for_sort(sort) for ref, sort in sorts.items()}


def _statement_type(core: object, binding: BindingRef) -> object:
    if binding not in set(binding_refs(core)):
        raise RelationError("public edge names a non-Statement BindingRef")
    declaration = next(
        item
        for item in core.inputs
        if item.name == binding.input_name and item.scope == binding.scope
    )
    return value_type_for_sort(declaration.value_sort)


def _source_body(source: object) -> object:
    if type(source) is BindingRef:
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                ((0, k1.Symbol(source.scope)), (1, k1.Symbol(source.input_name)))
            ),
        )
    if type(source) is k2.ValueRef and type(source.kind) is k2.RefKind:
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                ((0, k1.Symbol(source.kind.value)), (1, k1.Symbol(source.name)))
            ),
        )
    raise RelationError("relation source has the wrong exact coordinate kind")


def _value_relation_body(relation: ValueRelation) -> object:
    if relation.bridge_id is None:
        return k1.DatumVariant(0, k1.UNIT)
    assert relation.direction is not None
    return k1.DatumVariant(
        1,
        k1.DatumRecord(
            (
                (0, _id_datum(relation.bridge_id, "relations.value-bridge")),
                (1, k1.Symbol(relation.direction.value)),
            )
        ),
    )


def protocol_relation_binding_id(
    binding: ProtocolRelationBinding,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    _id_datum(binding.protocol_id, "pir.protocol")
    return _semantic_id(
        "relations.protocol-binding",
        k1.DatumRecord(
            (
                (0, _id_datum(binding.protocol_id, "pir.protocol")),
                (1, k1.DatumSeq(tuple(_id_datum(x, "relations.interface") for x in binding.relation_interface_ids))),
                (2, k1.DatumSeq(tuple(k1.DatumRecord(((0, k1.Symbol(x.name)), (1, _id_datum(x.relation_interface_id, "relations.interface")))) for x in binding.instances))),
                (3, k1.DatumSeq(tuple(k1.DatumRecord(((0, k1.Symbol(x.instance)), (1, k1.Symbol(x.slot)), (2, _source_body(x.source)), (3, _value_relation_body(x.value_relation)))) for x in binding.public_edges))),
                (4, k1.DatumSeq(tuple(k1.DatumRecord(((0, k1.Symbol(x.instance)), (1, k1.Symbol(x.slot)), (2, _source_body(x.source)), (3, _value_relation_body(x.value_relation)))) for x in binding.phase_edges))),
                (5, k1.DatumSeq(tuple(k1.DatumRecord(((0, k1.Symbol(x.instance)), (1, k1.Symbol(x.slot)), (2, _source_body(x.publication)), (3, _source_body(x.query)), (4, _source_body(x.answer)))) for x in binding.oracle_edges))),
                (6, k1.DatumSeq(tuple(k1.DatumRecord(((0, k1.Symbol(x.instance)), (1, k1.Symbol(x.claim.origin.value)), (2, k1.Symbol(x.claim.claim)), (3, k1.DatumVariant(0, k1.UNIT) if x.claim.producer is None else k1.DatumVariant(1, k1.Symbol(x.claim.producer))))) for x in binding.claim_edges))),
            )
        ),
        profiles=profiles,
    )


def plan_witness_binding_id(
    binding: PlanWitnessBinding,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "relations.plan-witness-binding",
        k1.DatumRecord(
            (
                (0, _id_datum(binding.plan_witness_surface_id, "pir.plan-witness-surface")),
                (1, _id_datum(binding.relation_interface_id, "relations.interface")),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(x.slot)),
                                    (1, k1.Symbol(x.witness_surface_key)),
                                    (2, _value_relation_body(x.value_relation)),
                                )
                            )
                            for x in binding.witness_edges
                        )
                    ),
                ),
            )
        ),
        profiles=profiles,
    )


def _admitted_interfaces(
    interfaces: tuple[RelationInterface, ...],
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> dict[object, RelationInterface]:
    if len(interfaces) > MAX_RELATION_OCCURRENCES:
        raise RelationError("relation Interface set exceeds its finite bound")
    result: dict[object, RelationInterface] = {}
    for interface in interfaces:
        identifier = relation_interface_id(interface, profiles=profiles)
        if identifier in result:
            raise RelationError("relation Interfaces must have distinct identities")
        result[identifier] = interface
    return result


def check_protocol_relation_binding(
    core: object,
    construction: object | None,
    interpretation: object,
    interfaces: tuple[RelationInterface, ...],
    bridges: tuple[ValueBridge, ...],
    binding: ProtocolRelationBinding,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CheckedProtocolRelationBinding:
    k2.admit_core(core)
    if type(binding) is not ProtocolRelationBinding:
        raise RelationError("ProtocolRelationBinding has the wrong exact shape")
    if binding.protocol_id != protocol_id(
        core,
        construction,
        interpretation,
        profiles=profiles,
    ):
        raise RelationError("ProtocolRelationBinding names the wrong Protocol")
    sequences = (
        binding.relation_interface_ids,
        binding.instances,
        binding.public_edges,
        binding.phase_edges,
        binding.oracle_edges,
        binding.claim_edges,
    )
    if any(len(items) > MAX_RELATION_OCCURRENCES for items in sequences):
        raise RelationError("ProtocolRelationBinding exceeds its finite bounds")
    interface_by_id = _admitted_interfaces(interfaces, profiles=profiles)
    if len(binding.relation_interface_ids) != len(set(binding.relation_interface_ids)):
        raise RelationError("Protocol binding relation Interface IDs must be unique")
    for identifier in binding.relation_interface_ids:
        _id_datum(identifier, "relations.interface")
        if identifier not in interface_by_id:
            raise RelationError("Protocol binding names an unavailable relation Interface")
    instance_by_name = {item.name: item for item in binding.instances}
    if len(instance_by_name) != len(binding.instances):
        raise RelationError("relation instance occurrence names must be unique")
    for instance in binding.instances:
        _ascii(instance.name, "relation instance occurrence")
        if instance.relation_interface_id not in interface_by_id:
            raise RelationError("relation instance names an unavailable Interface")
    used_ids = {item.relation_interface_id for item in binding.instances}
    if used_ids != set(binding.relation_interface_ids):
        raise RelationError("Protocol binding Interface list must be exact-used")

    value_types = _core_value_types(core)
    bridge_by_id = _bridge_registry(bridges, profiles=profiles)
    public_keys: set[tuple[str, str]] = set()
    for edge in binding.public_edges:
        instance = instance_by_name.get(edge.instance)
        if instance is None:
            raise RelationError("public edge names no relation instance")
        interface = interface_by_id[instance.relation_interface_id]
        slot = next((x for x in interface.public_instance if x.name == edge.slot), None)
        if slot is None or (edge.instance, edge.slot) in public_keys:
            raise RelationError("public edge is unknown or duplicated")
        public_keys.add((edge.instance, edge.slot))
        source_type = (
            _statement_type(core, edge.source)
            if type(edge.source) is BindingRef
            else value_types.get(edge.source)
        )
        if source_type is None:
            raise RelationError("public edge names no typed K2 source")
        _check_value_relation(source_type, slot.value_type, edge.value_relation, bridge_by_id)

    phase_keys: set[tuple[str, str]] = set()
    for edge in binding.phase_edges:
        instance = instance_by_name.get(edge.instance)
        if instance is None:
            raise RelationError("phase edge names no relation instance")
        interface = interface_by_id[instance.relation_interface_id]
        slot = next((x for x in interface.phase_inputs if x.name == edge.slot), None)
        key = (edge.instance, edge.slot)
        source_type = value_types.get(edge.source) if type(edge.source) is k2.ValueRef else None
        if slot is None or key in phase_keys or source_type is None:
            raise RelationError("phase edge is unknown, duplicated, or untyped")
        phase_keys.add(key)
        _check_value_relation(source_type, slot.value_type, edge.value_relation, bridge_by_id)

    occurrence_by_name = {item.name: item for item in core.schedule}
    oracle_keys: set[tuple[str, str]] = set()
    for edge in binding.oracle_edges:
        instance = instance_by_name.get(edge.instance)
        if instance is None:
            raise RelationError("Oracle edge names no relation instance")
        interface = interface_by_id[instance.relation_interface_id]
        slot = next((x for x in interface.oracle_statements if x.name == edge.slot), None)
        key = (edge.instance, edge.slot)
        refs = (edge.publication, edge.query, edge.answer)
        if slot is None or key in oracle_keys or any(type(ref) is not k2.ValueRef for ref in refs):
            raise RelationError("Oracle edge is unknown, duplicated, or malformed")
        kinds = tuple(occurrence_by_name.get(ref.name) for ref in refs)
        if (
            any(item is None for item in kinds)
            or tuple(item.kind for item in kinds)
            != (
                k2.OccurrenceKind.ORACLE_PUBLISH,
                k2.OccurrenceKind.ORACLE_QUERY,
                k2.OccurrenceKind.ORACLE_ANSWER,
            )
            or tuple(value_types.get(ref) for ref in refs)
            != (slot.material_type, slot.index_type, slot.answer_type)
        ):
            raise RelationError("Oracle edge disagrees with exact lifecycle kinds or types")
        oracle_keys.add(key)

    claim_instances: set[str] = set()
    for edge in binding.claim_edges:
        if (
            edge.instance not in instance_by_name
            or edge.instance in claim_instances
            or not _claim_exists(core, edge.claim)
        ):
            raise RelationError("claim edge is duplicated or names no exact claim occurrence")
        claim_instances.add(edge.instance)

    expected_public = {(i.name, x.name) for i in binding.instances for x in interface_by_id[i.relation_interface_id].public_instance}
    expected_phase = {(i.name, x.name) for i in binding.instances for x in interface_by_id[i.relation_interface_id].phase_inputs}
    expected_oracle = {(i.name, x.name) for i in binding.instances for x in interface_by_id[i.relation_interface_id].oracle_statements}
    expected_claim = {i.name for i in binding.instances if interface_by_id[i.relation_interface_id].requires_claim}
    return CheckedProtocolRelationBinding(
        _PROTOCOL_BINDING_ISSUER,
        profiles,
        protocol_relation_binding_id(binding, profiles=profiles),
        binding,
        tuple(sorted(expected_public - public_keys)),
        tuple(sorted(expected_phase - phase_keys)),
        tuple(sorted(expected_oracle - oracle_keys)),
        tuple(sorted(expected_claim - claim_instances)),
    )


def check_plan_witness_binding(
    surface: PlanWitnessSurface,
    interface: RelationInterface,
    bridges: tuple[ValueBridge, ...],
    binding: PlanWitnessBinding,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CheckedPlanWitnessBinding:
    if type(binding) is not PlanWitnessBinding:
        raise RelationError("PlanWitnessBinding has the wrong exact shape")
    if binding.plan_witness_surface_id != plan_witness_surface_id(
        surface,
        profiles=profiles,
    ):
        raise RelationError("PlanWitnessBinding names the wrong witness surface")
    if len(binding.witness_edges) > MAX_RELATION_OCCURRENCES:
        raise RelationError("PlanWitnessBinding exceeds its finite bounds")
    if binding.relation_interface_id != relation_interface_id(
        interface,
        profiles=profiles,
    ):
        raise RelationError("Plan witness binding names the wrong relation Interface")
    surface_entries = {item.key: item for item in surface.entries}
    bridge_by_id = _bridge_registry(bridges, profiles=profiles)
    edge_keys: set[str] = set()
    for edge in binding.witness_edges:
        slot = next((x for x in interface.private_witness if x.name == edge.slot), None)
        if (
            slot is None
            or edge.slot in edge_keys
            or edge.witness_surface_key not in surface_entries
        ):
            raise RelationError("witness edge is unknown or duplicated")
        edge_keys.add(edge.slot)
        _check_value_relation(
            surface_entries[edge.witness_surface_key].value_type,
            slot.value_type,
            edge.value_relation,
            bridge_by_id,
        )
    expected = {x.name for x in interface.private_witness}
    return CheckedPlanWitnessBinding(
        _PLAN_BINDING_ISSUER,
        profiles,
        plan_witness_binding_id(binding, profiles=profiles),
        binding,
        surface,
        tuple(sorted(expected - edge_keys)),
    )


def require_whole_protocol_binding(result: CheckedProtocolRelationBinding) -> None:
    if (
        type(result) is not CheckedProtocolRelationBinding
        or result._issuer is not _PROTOCOL_BINDING_ISSUER
        or result.binding_id
        != protocol_relation_binding_id(
            result.binding,
            profiles=result._profiles,
        )
        or not result.whole
    ):
        raise RelationError("Protocol relation binding is not whole")


def require_whole_plan_binding(result: CheckedPlanWitnessBinding) -> None:
    if (
        type(result) is not CheckedPlanWitnessBinding
        or result._issuer is not _PLAN_BINDING_ISSUER
        or result.binding_id
        != plan_witness_binding_id(
            result.binding,
            profiles=result._profiles,
        )
        or result.binding.plan_witness_surface_id
        != plan_witness_surface_id(
            result.surface,
            profiles=result._profiles,
        )
        or not result.whole
    ):
        raise RelationError("Plan witness binding is not whole")


# ---------------------------------------------------------------------------
# Typed artifact facts, selectors, and a checked equation DAG
# ---------------------------------------------------------------------------


class FactKind(str, Enum):
    VALUE = "value"
    CONTENT_ID = "content-id"
    NATURAL = "natural"
    BOOLEAN = "boolean"
    OCCURRENCE_REF = "occurrence-ref"


@dataclass(frozen=True)
class FactType:
    kind: FactKind
    value_type: object | None = None


BOOL_FACT = FactType(FactKind.BOOLEAN)
NAT_FACT = FactType(FactKind.NATURAL)
ID_FACT = FactType(FactKind.CONTENT_ID)


@dataclass(frozen=True)
class ArtifactFactDecl:
    name: str
    fact_type: FactType


@dataclass(frozen=True)
class ArtifactFactSchema:
    name: str
    facts: tuple[ArtifactFactDecl, ...]


class ObservationState(str, Enum):
    UNREAD = "unread"
    OBSERVED = "observed"


@dataclass(frozen=True)
class ArtifactFactObservation:
    fact: str
    state: ObservationState
    values: tuple[object, ...] = ()


@dataclass(frozen=True)
class ArtifactObservation:
    schema: ArtifactFactSchema
    facts: tuple[ArtifactFactObservation, ...]


class SelectorKind(str, Enum):
    AT = "at"


@dataclass(frozen=True)
class ArtifactSelector:
    name: str
    source_fact: str
    kind: SelectorKind
    index: int


@dataclass(frozen=True)
class TypedAlgorithmRef:
    algorithm_id: object
    evaluation_contract_id: object
    input_types: tuple[FactType, ...]
    output_type: FactType


class EquationOp(str, Enum):
    SELECT = "select"
    CONSTANT = "constant"
    APPLY = "apply"
    EQUAL = "equal"


@dataclass(frozen=True)
class EquationNode:
    name: str
    op: EquationOp
    output_type: FactType
    dependencies: tuple[str, ...] = ()
    reference: str | object | None = None


@dataclass(frozen=True)
class GroundingEquation:
    name: str
    schema: ArtifactFactSchema
    selectors: tuple[ArtifactSelector, ...]
    nodes: tuple[EquationNode, ...]
    root: str


def _validate_fact_type(fact_type: FactType) -> None:
    if type(fact_type) is not FactType or type(fact_type.kind) is not FactKind:
        raise ArtifactError("artifact fact type has the wrong shape")
    if fact_type.kind is FactKind.VALUE:
        if type(fact_type.value_type) is not k1.ValueType:
            raise ArtifactError("Value fact needs one exact K1 ValueType")
    elif fact_type.value_type is not None:
        raise ArtifactError("non-Value fact cannot carry a ValueType")


def _fact_type_body(fact_type: FactType) -> object:
    _validate_fact_type(fact_type)
    return k1.DatumRecord(
        (
            (0, k1.Symbol(fact_type.kind.value)),
            (
                1,
                k1.DatumVariant(0, k1.UNIT)
                if fact_type.value_type is None
                else k1.DatumVariant(
                    1, k1.value_type_datum(fact_type.value_type)
                ),
            ),
        )
    )


def _validate_fact_value(fact_type: FactType, value: object) -> None:
    _validate_fact_type(fact_type)
    if fact_type.kind is FactKind.VALUE:
        if type(value) is not k1.CanonicalValue or value.value_type != fact_type.value_type:
            raise ArtifactError("Value fact needs one exact typed CanonicalValue")
        k1.admit_value(value.value_type, value.datum)
    elif fact_type.kind is FactKind.CONTENT_ID:
        _id_datum(value)
    elif fact_type.kind is FactKind.NATURAL:
        if type(value) is not int or value < 0:
            raise ArtifactError("natural fact must be one nonnegative integer")
    elif fact_type.kind is FactKind.BOOLEAN:
        if type(value) is not bool:
            raise ArtifactError("Boolean fact must be one exact Boolean")
    elif (
        fact_type.kind is FactKind.OCCURRENCE_REF
        and (
            type(value) is not k2.ValueRef
            or value.kind is not k2.RefKind.OCCURRENCE
        )
    ):
        raise ArtifactError("occurrence fact must be one exact occurrence ValueRef")


def _fact_value_body(fact_type: FactType, value: object) -> object:
    _validate_fact_value(fact_type, value)
    if fact_type.kind is FactKind.VALUE:
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (0, k1.value_type_datum(value.value_type)),
                    (1, value.datum),
                )
            ),
        )
    if fact_type.kind is FactKind.CONTENT_ID:
        return k1.DatumVariant(1, _id_datum(value))
    if fact_type.kind is FactKind.NATURAL:
        return k1.DatumVariant(2, k1.Nat(value))
    if fact_type.kind is FactKind.BOOLEAN:
        return k1.DatumVariant(3, value)
    return k1.DatumVariant(
        4,
        k1.DatumRecord(
            ((0, k1.Symbol(value.kind.value)), (1, k1.Symbol(value.name)))
        ),
    )


def admit_artifact_schema(schema: ArtifactFactSchema) -> None:
    if type(schema) is not ArtifactFactSchema:
        raise ArtifactError("artifact schema has the wrong exact shape")
    _ascii(schema.name, "artifact schema")
    names = tuple(item.name for item in schema.facts)
    try:
        _bounded_unique(names, MAX_ARTIFACT_FACTS, "artifact facts")
    except K3Error as error:
        raise ArtifactError(str(error)) from error
    for fact in schema.facts:
        if type(fact) is not ArtifactFactDecl:
            raise ArtifactError("artifact fact declaration has the wrong exact shape")
        _validate_fact_type(fact.fact_type)


def admit_artifact_observation(observation: ArtifactObservation) -> None:
    if type(observation) is not ArtifactObservation:
        raise ArtifactError("artifact observation has the wrong exact shape")
    admit_artifact_schema(observation.schema)
    if len(observation.facts) > MAX_ARTIFACT_OBSERVATIONS:
        raise ArtifactError("artifact observation exceeds its finite bound")
    declared = {item.name: item.fact_type for item in observation.schema.facts}
    observed = {item.fact: item for item in observation.facts}
    if len(observed) != len(observation.facts) or set(observed) != set(declared):
        raise ArtifactError("artifact observation must cover every declared fact once")
    for item in observation.facts:
        if type(item) is not ArtifactFactObservation or type(item.state) is not ObservationState:
            raise ArtifactError("artifact fact observation has the wrong exact shape")
        if len(item.values) > MAX_ARTIFACT_OBSERVATIONS:
            raise ArtifactError("artifact fact observation exceeds its finite bound")
        if item.state is ObservationState.UNREAD and item.values:
            raise ArtifactError("Unread artifact fact cannot carry observed values")
        if item.state is ObservationState.OBSERVED:
            for value in item.values:
                _validate_fact_value(declared[item.fact], value)


def admit_grounding_equation(equation: GroundingEquation) -> None:
    if type(equation) is not GroundingEquation:
        raise ArtifactError("grounding equation has the wrong exact shape")
    admit_artifact_schema(equation.schema)
    fact_types = {item.name: item.fact_type for item in equation.schema.facts}
    if len(equation.selectors) > MAX_ARTIFACT_SELECTORS:
        raise ArtifactError("artifact selectors exceed their finite bound")
    selectors = {item.name: item for item in equation.selectors}
    if len(selectors) != len(equation.selectors):
        raise ArtifactError("selector names must be unique")
    selector_types: dict[str, FactType] = {}
    for selector in equation.selectors:
        if type(selector) is not ArtifactSelector or selector.kind is not SelectorKind.AT:
            raise ArtifactError("only the bounded typed At selector is supported")
        current = fact_types.get(selector.source_fact)
        if (
            current is None
            or type(selector.index) is not int
            or selector.index < 0
            or selector.index > MAX_SELECTOR_INDEX
        ):
            raise ArtifactError("selector names a missing artifact fact")
        selector_types[selector.name] = current

    nodes = {item.name: item for item in equation.nodes}
    if len(nodes) != len(equation.nodes) or len(nodes) > MAX_EQUATION_NODES:
        raise ArtifactError("equation nodes must be unique and bounded")
    if equation.root not in nodes:
        raise ArtifactError("grounding equation root is missing")
    for node in equation.nodes:
        _validate_fact_type(node.output_type)
        if len(node.dependencies) > MAX_EQUATION_NODES:
            raise ArtifactError("equation node dependencies exceed their finite bound")
        if any(dependency not in nodes for dependency in node.dependencies):
            raise ArtifactError("equation node has a dangling dependency")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visiting:
            raise ArtifactError("grounding equation graph is cyclic")
        if name in visited:
            return
        visiting.add(name)
        for dependency in nodes[name].dependencies:
            visit(dependency)
        visiting.remove(name)
        visited.add(name)

    for name in nodes:
        visit(name)

    for node in equation.nodes:
        dependency_types = tuple(nodes[name].output_type for name in node.dependencies)
        if node.op is EquationOp.SELECT:
            if node.dependencies or type(node.reference) is not str:
                raise ArtifactError("Select node needs exactly one selector reference")
            if selector_types.get(node.reference) != node.output_type:
                raise ArtifactError("Select node type disagrees with its selector")
        elif node.op is EquationOp.CONSTANT:
            if node.dependencies:
                raise ArtifactError("Constant node needs a typed literal reference")
            _validate_fact_value(node.output_type, node.reference)
        elif node.op is EquationOp.APPLY:
            if type(node.reference) is not TypedAlgorithmRef:
                raise ArtifactError("Apply node needs one exact typed algorithm reference")
            _id_datum(
                node.reference.algorithm_id, "foundation.canonical-algorithm"
            )
            _id_datum(
                node.reference.evaluation_contract_id,
                "foundation.evaluation-contract",
            )
            for fact_type in node.reference.input_types + (node.reference.output_type,):
                _validate_fact_type(fact_type)
            if (
                dependency_types != node.reference.input_types
                or node.output_type != node.reference.output_type
            ):
                raise ArtifactError("Apply node disagrees with its authenticated typed ABI")
        elif node.op is EquationOp.EQUAL:
            if len(dependency_types) != 2 or dependency_types[0] != dependency_types[1]:
                raise ArtifactError("equality needs two values of the same exact fact type")
            if node.output_type != BOOL_FACT:
                raise ArtifactError("equality result must be Boolean")
        else:
            raise ArtifactError("unsupported equation operation")
    if nodes[equation.root].output_type != BOOL_FACT:
        raise ArtifactError("grounding equation root must be Boolean")


def grounding_equation_id(
    equation: GroundingEquation,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    admit_grounding_equation(equation)

    def reference_body(node: EquationNode) -> object:
        if node.op is EquationOp.SELECT:
            return k1.DatumVariant(0, k1.Symbol(node.reference))
        if node.op is EquationOp.CONSTANT:
            return k1.DatumVariant(
                1, _fact_value_body(node.output_type, node.reference)
            )
        if node.op is EquationOp.APPLY:
            reference = node.reference
            return k1.DatumVariant(
                2,
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                reference.algorithm_id,
                                "foundation.canonical-algorithm",
                            ),
                        ),
                        (
                            1,
                            _id_datum(
                                reference.evaluation_contract_id,
                                "foundation.evaluation-contract",
                            ),
                        ),
                        (
                            2,
                            k1.DatumSeq(
                                tuple(_fact_type_body(x) for x in reference.input_types)
                            ),
                        ),
                        (3, _fact_type_body(reference.output_type)),
                    )
                ),
            )
        return k1.DatumVariant(3, k1.UNIT)

    return _semantic_id(
        "relations.grounding-equation",
        k1.DatumRecord(
            (
                (0, k1.Symbol(equation.name)),
                (
                    1,
                    k1.DatumRecord(
                        (
                            (0, k1.Symbol(equation.schema.name)),
                            (
                                1,
                                k1.DatumSeq(
                                    tuple(
                                        k1.DatumRecord(
                                            (
                                                (0, k1.Symbol(fact.name)),
                                                (1, _fact_type_body(fact.fact_type)),
                                            )
                                        )
                                        for fact in equation.schema.facts
                                    )
                                ),
                            ),
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(selector.name)),
                                    (1, k1.Symbol(selector.source_fact)),
                                    (2, k1.Symbol(selector.kind.value)),
                                    (3, k1.Nat(selector.index)),
                                )
                            )
                            for selector in equation.selectors
                        )
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(node.name)),
                                    (1, k1.Symbol(node.op.value)),
                                    (2, _fact_type_body(node.output_type)),
                                    (
                                        3,
                                        k1.DatumSeq(
                                            tuple(
                                                k1.Symbol(dep)
                                                for dep in node.dependencies
                                            )
                                        ),
                                    ),
                                    (4, reference_body(node)),
                                )
                            )
                            for node in equation.nodes
                        )
                    ),
                ),
                (4, k1.Symbol(equation.root)),
            )
        ),
        profiles=profiles,
    )


# ---------------------------------------------------------------------------
# Run grounding: only a checked K2 execution path issues this attenuated view
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GroundedValue:
    coordinate: str
    value_id: object


_PIR_RUN_ISSUER = object()


class RelationRunQualification(str, Enum):
    REPLAY_QUALIFIED = "replay-qualified"
    CAUSALLY_GENERATED = "causally-generated"


class RunCoordinateKind(str, Enum):
    STATEMENT = "statement"
    PUBLIC_OCCURRENCE = "public-occurrence"


@dataclass(frozen=True)
class RelationRunCoordinate:
    kind: RunCoordinateKind
    source: object  # BindingRef or exact occurrence ValueRef


@dataclass(frozen=True)
class RelationRunEntry:
    coordinate: RelationRunCoordinate
    value_type: object
    value: object


@dataclass(frozen=True, slots=True)
class RelationRunView:
    protocol_id: object
    qualification: RelationRunQualification
    manifest: tuple[RelationRunCoordinate, ...]
    entries: tuple[RelationRunEntry, ...]
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _PIR_RUN_ISSUER:
            raise GroundingError("only PIR execution may issue a run-grounding view")


def _coordinate_body(coordinate: RelationRunCoordinate) -> object:
    if coordinate.kind is RunCoordinateKind.STATEMENT and type(coordinate.source) is BindingRef:
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (0, k1.Symbol(coordinate.source.scope)),
                    (1, k1.Symbol(coordinate.source.input_name)),
                )
            ),
        )
    if (
        coordinate.kind is RunCoordinateKind.PUBLIC_OCCURRENCE
        and type(coordinate.source) is k2.ValueRef
        and coordinate.source.kind is k2.RefKind.OCCURRENCE
    ):
        return k1.DatumVariant(1, k1.Symbol(coordinate.source.name))
    raise GroundingError("relation run coordinate has the wrong exact shape")


def _grounded_value_id(
    coordinate: RelationRunCoordinate,
    value: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    return _semantic_id(
        "relations.grounded-value-occurrence",
        k1.DatumRecord(((0, _coordinate_body(coordinate)), (1, k2._datum(value)))),
        profiles=profiles,
    )


def _public_occurrence_names(core: object) -> set[str]:
    private = _private_influenced_occurrences(core)
    public: set[str] = set()
    for occurrence in core.schedule:
        if occurrence.name in private:
            continue
        # The bounded K2 Oracle publication value is the confidential logical
        # Oracle body, not its public commitment.  Never export it here.
        if occurrence.kind is not k2.OccurrenceKind.ORACLE_PUBLISH:
            public.add(occurrence.name)
    return public


def issue_relation_run_view(
    core: object,
    construction: object | None,
    invocation: object,
    record: object,
    manifest: tuple[RelationRunCoordinate, ...],
    *,
    qualification: RelationRunQualification = RelationRunQualification.REPLAY_QUALIFIED,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> RelationRunView:
    """Replay one exact record and resolve one explicit public-only manifest."""

    if qualification is not RelationRunQualification.REPLAY_QUALIFIED:
        raise GroundingError(
            "the bounded probe has no live causal capability for CausallyGenerated"
        )
    checked = k2.replay(
        core,
        construction,
        invocation,
        record,
        profiles=profiles.k2_profiles,
    )
    admitted_values = k2.admit_invocation(core, invocation)
    if len(manifest) > MAX_RUN_READS or len(manifest) != len(set(manifest)):
        raise GroundingError("relation run manifest must be unique and bounded")
    statement_types = {
        BindingRef(item.scope, item.name): value_type_for_sort(item.value_sort)
        for item in core.inputs
        if item.role is k2.InputRole.STATEMENT
    }
    statement_values = {
        BindingRef(item.scope, item.name): admitted_values[item.name]
        for item in core.inputs
        if item.role is k2.InputRole.STATEMENT
    }
    public_occurrences = _public_occurrence_names(core)
    value_types = _core_value_types(core)
    executed = {
        k2.ValueRef.occurrence(entry.occurrence): entry.value
        for entry in checked.entries
        if entry.status is k2.EntryStatus.EXECUTED and entry.value is not None
    }
    entries: list[RelationRunEntry] = []
    for coordinate in manifest:
        _coordinate_body(coordinate)
        if coordinate.kind is RunCoordinateKind.STATEMENT:
            if coordinate.source not in statement_values:
                raise GroundingError("manifest requests a non-Statement or private binding")
            entries.append(
                RelationRunEntry(
                    coordinate,
                    statement_types[coordinate.source],
                    statement_values[coordinate.source],
                )
            )
        else:
            if coordinate.source.name not in public_occurrences:
                raise GroundingError("manifest requests a private or nonpublic occurrence")
            if coordinate.source not in executed:
                raise GroundingError("manifest requests an inactive occurrence")
            entries.append(
                RelationRunEntry(
                    coordinate,
                    value_types[coordinate.source],
                    executed[coordinate.source],
                )
            )
    return RelationRunView(
        protocol_id(
            core,
            None
            if record.interpretation is k2.ChallengeInterpretation.FRESH
            else construction,
            record.interpretation,
            profiles=profiles,
        ),
        qualification,
        manifest,
        tuple(entries),
        _PIR_RUN_ISSUER,
    )


@dataclass(frozen=True)
class RunGroundingResult:
    binding_id: object
    public_slots: tuple[GroundedValue, ...]
    phase_slots: tuple[GroundedValue, ...]
    oracle_observations: tuple[GroundedValue, ...]


def ground_whole_correspondence(
    checked_binding: CheckedProtocolRelationBinding,
    run_view: object,
) -> RunGroundingResult:
    require_whole_protocol_binding(checked_binding)
    if type(run_view) is not RelationRunView or run_view._issuer is not _PIR_RUN_ISSUER:
        raise GroundingError("run grounding requires one PIR-issued execution view")
    if run_view.protocol_id != checked_binding.binding.protocol_id:
        raise GroundingError("run-grounding view belongs to another Protocol")
    entries = {item.coordinate: item for item in run_view.entries}

    def coordinate_for(source: object) -> RelationRunCoordinate:
        return RelationRunCoordinate(
            RunCoordinateKind.STATEMENT
            if type(source) is BindingRef
            else RunCoordinateKind.PUBLIC_OCCURRENCE,
            source,
        )

    required = tuple(
        [coordinate_for(edge.source) for edge in checked_binding.binding.public_edges]
        + [coordinate_for(edge.source) for edge in checked_binding.binding.phase_edges]
        + [
            coordinate_for(source)
            for edge in checked_binding.binding.oracle_edges
            for source in (edge.query, edge.answer)
        ]
    )
    unique_required = tuple(dict.fromkeys(required))
    if set(unique_required) != set(run_view.manifest) or len(unique_required) != len(
        run_view.manifest
    ):
        raise GroundingError("run view manifest is not the exact binding read set")

    public: list[GroundedValue] = []
    for edge in checked_binding.binding.public_edges:
        coordinate_ref = coordinate_for(edge.source)
        try:
            value = entries[coordinate_ref].value
        except KeyError as error:
            raise GroundingError("PIR view lacks a required public occurrence") from error
        coordinate = f"public:{edge.instance}:{edge.slot}"
        public.append(
            GroundedValue(
                coordinate,
                _grounded_value_id(
                    coordinate_ref,
                    value,
                    profiles=checked_binding._profiles,
                ),
            )
        )

    phase: list[GroundedValue] = []
    for edge in checked_binding.binding.phase_edges:
        coordinate_ref = coordinate_for(edge.source)
        try:
            value = entries[coordinate_ref].value
        except KeyError as error:
            raise GroundingError("PIR view lacks a required phase occurrence") from error
        coordinate = f"phase:{edge.instance}:{edge.slot}"
        phase.append(
            GroundedValue(
                coordinate,
                _grounded_value_id(
                    coordinate_ref,
                    value,
                    profiles=checked_binding._profiles,
                ),
            )
        )

    oracle: list[GroundedValue] = []
    for edge in checked_binding.binding.oracle_edges:
        for label, source in (("query", edge.query), ("answer", edge.answer)):
            coordinate_ref = coordinate_for(source)
            try:
                value = entries[coordinate_ref].value
            except KeyError as error:
                raise GroundingError("PIR view lacks a required Oracle observation") from error
            coordinate = f"oracle-{label}:{edge.instance}:{edge.slot}"
            oracle.append(
                GroundedValue(
                    coordinate,
                    _grounded_value_id(
                        coordinate_ref,
                        value,
                        profiles=checked_binding._profiles,
                    ),
                )
            )
    return RunGroundingResult(
        checked_binding.binding_id,
        tuple(public),
        tuple(phase),
        tuple(oracle),
    )


# ---------------------------------------------------------------------------
# Exact bounded carrier for the K2 Protocol pair
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CarrierGraph:
    """The graph-carried Core and Protocol fields only."""

    core: object
    interpretation: object
    transcript_construction_id: object | None


@dataclass(frozen=True)
class CarrierDependencyEnvironment:
    """External preimages required for semantic admission, never serialization."""

    transcript_construction: object | None


CARRIER_PROFILE = "zkc.k3-dependent-carrier.probe.v2"


class FieldDisposition(str, Enum):
    GRAPH_CARRIED = "graph-carried"
    EXTERNAL_AUTHENTICATED_BODY = "external-authenticated-body"
    DERIVED_REFERENCE = "derived-reference"


_GRAPH_CARRIER_CLASSES = (
    k2.Core,
    k2.InputDecl,
    k2.ScopeDecl,
    k2.ValueRef,
    k2.Occurrence,
    k2.Predicate,
    k2.VerifierRule,
    k2.ChallengeDomain,
    k2.ProtocolDeclarationRef,
    k2.IndependentCoin,
    k2.JointCoinMember,
    k2.ExclusiveReductionUse,
    k2.SharedReductionUse,
    k2.ReductionDecl,
    k2.RequiredPublication,
    k2.ClaimConsumerUse,
)


def _field_names(cls: type[object]) -> set[str]:
    return {f"{cls.__name__}.{item.name}" for item in fields(cls)}


FROZEN_CARRIER_FIELD_DISPOSITION: Mapping[str, FieldDisposition] = MappingProxyType(
    {
        "ChallengeDomain.modulus": FieldDisposition.GRAPH_CARRIED,
        "ClaimConsumerUse.claim": FieldDisposition.GRAPH_CARRIED,
        "ClaimConsumerUse.consumer": FieldDisposition.GRAPH_CARRIED,
        "Core.claim_uses": FieldDisposition.GRAPH_CARRIED,
        "Core.extensions": FieldDisposition.GRAPH_CARRIED,
        "Core.initial_claims": FieldDisposition.GRAPH_CARRIED,
        "Core.inputs": FieldDisposition.GRAPH_CARRIED,
        "Core.reductions": FieldDisposition.GRAPH_CARRIED,
        "Core.schedule": FieldDisposition.GRAPH_CARRIED,
        "Core.scopes": FieldDisposition.GRAPH_CARRIED,
        "InputDecl.name": FieldDisposition.GRAPH_CARRIED,
        "InputDecl.role": FieldDisposition.GRAPH_CARRIED,
        "InputDecl.scope": FieldDisposition.GRAPH_CARRIED,
        "InputDecl.value_sort": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.challenge_domain": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.challenge_domain_ref": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.check_predicate": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.correlation": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.dependencies": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.guard": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.kind": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.name": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.oracle_name": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.prover_value_sort": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.fresh_law": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.reduction_use": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.scope": FieldDisposition.GRAPH_CARRIED,
        "Occurrence.verifier_rule": FieldDisposition.GRAPH_CARRIED,
        "Predicate.kind": FieldDisposition.GRAPH_CARRIED,
        "Predicate.parameters": FieldDisposition.GRAPH_CARRIED,
        "Predicate.refs": FieldDisposition.GRAPH_CARRIED,
        "ProtocolDeclarationRef.declaration_kind": FieldDisposition.GRAPH_CARRIED,
        "ProtocolDeclarationRef.local_name": FieldDisposition.GRAPH_CARRIED,
        "Protocol.core_id": FieldDisposition.DERIVED_REFERENCE,
        "Protocol.interpretation": FieldDisposition.GRAPH_CARRIED,
        "Protocol.transcript_construction_id": FieldDisposition.DERIVED_REFERENCE,
        "ReductionDecl.at_occurrence": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.input_claims": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.name": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.output_claims": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.required_challenges": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.required_publications": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.scope": FieldDisposition.GRAPH_CARRIED,
        "ReductionDecl.side_inputs": FieldDisposition.GRAPH_CARRIED,
        "RequiredPublication.next_challenge": FieldDisposition.GRAPH_CARRIED,
        "RequiredPublication.publication": FieldDisposition.GRAPH_CARRIED,
        "ScopeDecl.name": FieldDisposition.GRAPH_CARRIED,
        "ScopeDecl.open_before": FieldDisposition.GRAPH_CARRIED,
        "ScopeDecl.parent": FieldDisposition.GRAPH_CARRIED,
        "TranscriptConstruction.application_domain": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "TranscriptConstruction.challenge_rules": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "TranscriptConstruction.max_attempts": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "TranscriptConstruction.sample_bytes": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "TranscriptConstruction.state_bytes": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "TranscriptConstruction.version": (
            FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
        ),
        "ValueRef.kind": FieldDisposition.GRAPH_CARRIED,
        "ValueRef.name": FieldDisposition.GRAPH_CARRIED,
        "VerifierRule.kind": FieldDisposition.GRAPH_CARRIED,
        "VerifierRule.parameters": FieldDisposition.GRAPH_CARRIED,
        "JointCoinMember.group": FieldDisposition.GRAPH_CARRIED,
        "JointCoinMember.index": FieldDisposition.GRAPH_CARRIED,
        "JointCoinMember.prior_members": FieldDisposition.GRAPH_CARRIED,
        "SharedReductionUse.sharing_contract": FieldDisposition.GRAPH_CARRIED,
    }
)


def _observed_carrier_field_disposition() -> dict[str, FieldDisposition]:
    """Reflect implementation shape only; the expected manifest stays literal."""

    observed = {
        key: FieldDisposition.GRAPH_CARRIED
        for cls in _GRAPH_CARRIER_CLASSES
        for key in _field_names(cls)
    }
    observed.update(
        {
            key: FieldDisposition.EXTERNAL_AUTHENTICATED_BODY
            for key in _field_names(k2.TranscriptConstruction)
        }
    )
    observed.update(
        {
            "Protocol.core_id": FieldDisposition.DERIVED_REFERENCE,
            "Protocol.interpretation": FieldDisposition.GRAPH_CARRIED,
            "Protocol.transcript_construction_id": FieldDisposition.DERIVED_REFERENCE,
        }
    )
    return observed


def carrier_disposition_is_complete(
    observed: Mapping[str, FieldDisposition] | None = None,
) -> bool:
    actual = _observed_carrier_field_disposition() if observed is None else dict(observed)
    return actual == dict(FROZEN_CARRIER_FIELD_DISPOSITION)


def form_carrier_graph(graph: CarrierGraph) -> None:
    if type(graph) is not CarrierGraph:
        raise CarrierError("carrier graph has the wrong exact shape")
    try:
        k2.admit_core(graph.core)
        if graph.interpretation is k2.ChallengeInterpretation.FRESH:
            if graph.transcript_construction_id is not None:
                raise CarrierError("Fresh carrier graph must not name a construction")
        elif graph.interpretation is k2.ChallengeInterpretation.FIAT_SHAMIR:
            if graph.transcript_construction_id is None:
                raise CarrierError("Fiat--Shamir carrier graph must name a construction")
            _id_datum(
                graph.transcript_construction_id,
                "pir.transcript-construction",
            )
        else:
            raise CarrierError("carrier graph has an unsupported interpretation")
    except (K3Error, ValueError) as error:
        raise CarrierError(str(error)) from error


def carrier_protocol_id(
    graph: CarrierGraph,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> object:
    form_carrier_graph(graph)
    construction_ref = (
        k1.DatumVariant(0, k1.UNIT)
        if graph.transcript_construction_id is None
        else k1.DatumVariant(
            1,
            _id_datum(
                graph.transcript_construction_id,
                "pir.transcript-construction",
            ),
        )
    )
    profile = (
        profiles.k2_profiles.interaction
        if graph.interpretation is k2.ChallengeInterpretation.FRESH
        else profiles.k2_profiles.transcript_fs
    )
    return k1.profiled_content_id(
        "pir.protocol",
        profile.identity,
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        k2.core_id(
                            graph.core,
                            profiles=profiles.k2_profiles,
                        ),
                        "pir.interactive-core",
                    ),
                ),
                (1, construction_ref),
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def carrier_graph_for(
    core: object,
    interpretation: object,
    transcript_construction: object | None,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CarrierGraph:
    construction_id = (
        None
        if transcript_construction is None
        else k2.construction_id(
            core,
            transcript_construction,
            profiles=profiles.k2_profiles,
        )
    )
    graph = CarrierGraph(core, interpretation, construction_id)
    form_carrier_graph(graph)
    return graph


def admit_carrier_graph(
    graph: CarrierGraph,
    dependencies: CarrierDependencyEnvironment,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> None:
    form_carrier_graph(graph)
    if type(dependencies) is not CarrierDependencyEnvironment:
        raise CarrierError("carrier dependency environment has the wrong exact shape")
    construction = dependencies.transcript_construction
    try:
        expected_protocol = protocol_id(
            graph.core,
            construction,
            graph.interpretation,
            profiles=profiles,
        )
    except (K3Error, ValueError) as error:
        raise CarrierError(str(error)) from error
    if expected_protocol != carrier_protocol_id(graph, profiles=profiles):
        raise CarrierError(
            "external transcript construction does not match the graph reference"
        )


def require_imported_verification_carrier_support() -> None:
    raise UnsupportedCarrierFeature(
        "the bounded K2 executable has no exact ModuleEffectRef payload; "
        "imported verification is formed-but-unsupported"
    )


_DATACLASS_TYPES = {
    cls.__name__: cls
    for cls in (
        k2.ValueRef,
        k2.InputDecl,
        k2.ScopeDecl,
        k2.Predicate,
        k2.VerifierRule,
        k2.ChallengeDomain,
        k2.ProtocolDeclarationRef,
        k2.IndependentCoin,
        k2.JointCoinMember,
        k2.ExclusiveReductionUse,
        k2.SharedReductionUse,
        k2.Occurrence,
        k2.RequiredPublication,
        k2.ReductionDecl,
        k2.ClaimConsumerUse,
        k2.Core,
        CarrierGraph,
    )
}
_ENUM_TYPES = {
    cls.__name__: cls
    for cls in (
        k2.RefKind,
        k2.InputRole,
        k2.ValueSort,
        k2.PredicateKind,
        k2.VerifierRuleKind,
        k2.OccurrenceKind,
        k2.ChallengeInterpretation,
    )
}
_KNOWN_VALUE_TYPES = {
    k1.encode_datum(k1.value_type_datum(value_type)).hex(): value_type
    for value_type in (BYTES, BYTES32, BYTES96, NAT, BOOL, ORACLE_CELLS)
}


def _lower_carrier_value(value: object) -> object:
    if value is None or type(value) in {str, int, bool}:
        return value
    if type(value) is bytes:
        return {"__bytes__": value.hex()}
    if type(value) is tuple:
        return {"__tuple__": [_lower_carrier_value(item) for item in value]}
    if isinstance(value, Enum):
        return {"__enum__": type(value).__name__, "value": value.value}
    if type(value) is k1.TypedContentId:
        return {"__content_id__": value.internal_reference().hex()}
    if type(value) is k1.ValueType:
        return {
            "__value_type__": k1.encode_datum(k1.value_type_datum(value)).hex()
        }
    if type(value).__name__ in _DATACLASS_TYPES and hasattr(value, "__dataclass_fields__"):
        return {
            "__type__": type(value).__name__,
            **{
                item.name: _lower_carrier_value(getattr(value, item.name))
                for item in fields(value)
            },
        }
    raise UnsupportedCarrierFeature(f"unsupported carrier value type: {type(value).__name__}")


def _exact_keys(mapping: Mapping[str, object], expected: set[str], what: str) -> None:
    missing = expected - set(mapping)
    extra = set(mapping) - expected
    if missing:
        raise MissingCarrierField(f"{what} is missing fields: {sorted(missing)!r}")
    if extra:
        raise UnknownCarrierField(f"{what} has unknown fields: {sorted(extra)!r}")


def _read_carrier_value(value: object) -> object:
    if value is None or type(value) in {str, int, bool}:
        return value
    if type(value) is not dict:
        raise CarrierError("carrier value has no exact tagged shape")
    mapping: Mapping[str, object] = value
    if "__bytes__" in mapping:
        _exact_keys(mapping, {"__bytes__"}, "byte carrier")
        try:
            return bytes.fromhex(mapping["__bytes__"])  # type: ignore[arg-type]
        except (TypeError, ValueError) as error:
            raise CarrierError("byte carrier is malformed") from error
    if "__tuple__" in mapping:
        _exact_keys(mapping, {"__tuple__"}, "tuple carrier")
        items = mapping["__tuple__"]
        if type(items) is not list:
            raise CarrierError("tuple carrier payload must be a list")
        return tuple(_read_carrier_value(item) for item in items)
    if "__enum__" in mapping:
        _exact_keys(mapping, {"__enum__", "value"}, "Enum carrier")
        cls = _ENUM_TYPES.get(mapping["__enum__"])
        if cls is None:
            raise UnsupportedCarrierFeature("unknown carrier Enum type")
        try:
            return cls(mapping["value"])
        except (TypeError, ValueError) as error:
            raise UnsupportedCarrierFeature("unsupported carrier Enum value") from error
    if "__content_id__" in mapping:
        _exact_keys(mapping, {"__content_id__"}, "content-ID carrier")
        try:
            return k1.decode_content_reference(
                bytes.fromhex(mapping["__content_id__"])  # type: ignore[arg-type]
            )
        except (TypeError, ValueError, k1.CanonicalError) as error:
            raise CarrierError("content-ID carrier is malformed") from error
    if "__value_type__" in mapping:
        _exact_keys(mapping, {"__value_type__"}, "ValueType carrier")
        result = _KNOWN_VALUE_TYPES.get(mapping["__value_type__"])
        if result is None:
            raise UnsupportedCarrierFeature("ValueType is formed but unsupported by this reader")
        return result
    if "__type__" in mapping:
        type_name = mapping["__type__"]
        cls = _DATACLASS_TYPES.get(type_name)
        if cls is None:
            raise UnsupportedCarrierFeature("unknown semantic carrier record type")
        expected = {"__type__"} | {item.name for item in fields(cls)}
        _exact_keys(mapping, expected, f"{type_name} carrier")
        kwargs = {
            item.name: _read_carrier_value(mapping[item.name]) for item in fields(cls)
        }
        try:
            return cls(**kwargs)
        except (TypeError, ValueError) as error:
            raise CarrierError(f"{type_name} carrier cannot be formed") from error
    raise UnknownCarrierField("mapping carries no recognized semantic tag")


def lower_carrier(
    graph: CarrierGraph,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> dict[str, object]:
    """Serialize only the canonical graph; dependency preimages stay external."""

    form_carrier_graph(graph)
    return {
        "profile": CARRIER_PROFILE,
        "graph": _lower_carrier_value(graph),
        "asserted_core_id": k2.core_id(
            graph.core,
            profiles=profiles.k2_profiles,
        ).internal_reference().hex(),
        "asserted_protocol_id": carrier_protocol_id(
            graph,
            profiles=profiles,
        ).internal_reference().hex(),
    }


def read_carrier(
    carrier: object,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CarrierGraph:
    """Authenticate carrier shape and identity without admitting dependencies."""

    if type(carrier) is not dict:
        raise CarrierError("carrier root must be one exact mapping")
    _exact_keys(
        carrier,
        {
            "profile",
            "graph",
            "asserted_core_id",
            "asserted_protocol_id",
        },
        "carrier root",
    )
    if carrier["profile"] != CARRIER_PROFILE:
        raise UnsupportedCarrierFeature("unsupported carrier profile")
    graph = _read_carrier_value(carrier["graph"])
    if type(graph) is not CarrierGraph:
        raise CarrierError("carrier graph does not reconstruct CarrierGraph")
    form_carrier_graph(graph)
    expected_core = k2.core_id(
        graph.core,
        profiles=profiles.k2_profiles,
    ).internal_reference().hex()
    if carrier["asserted_core_id"] != expected_core:
        raise CarrierError("asserted Core ID does not authenticate reconstructed body")
    expected_protocol = carrier_protocol_id(
        graph,
        profiles=profiles,
    ).internal_reference().hex()
    if carrier["asserted_protocol_id"] != expected_protocol:
        raise CarrierError("asserted Protocol ID does not authenticate graph fields")
    return graph


def authenticate_carrier(
    carrier: object,
    dependencies: CarrierDependencyEnvironment,
    *,
    profiles: K3BSemanticProfiles = K3B_SEMANTIC_PROFILES,
) -> CarrierGraph:
    graph = read_carrier(carrier, profiles=profiles)
    admit_carrier_graph(graph, dependencies, profiles=profiles)
    return graph


# ---------------------------------------------------------------------------
# Constructive protocol-family pressure cases
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DependentSurfaceCase:
    name: str
    core: object
    construction: object | None
    invocation: object | None
    strategy: object | None
    interface: ProtocolInterface
    plan: ProverPlan
    definitions: tuple[RelationDefinitionRef, ...]
    relation_interfaces: tuple[RelationInterface, ...]
    protocol_binding: ProtocolRelationBinding
    plan_binding: PlanWitnessBinding
    bridges: tuple[ValueBridge, ...] = ()
    definition_sources: tuple[SchnorrRelationDefinition, ...] = ()


def _algorithm(label: str) -> object:
    return fixture_semantic_ref("foundation.canonical-algorithm", label)


def _simple_relation(
    name: str,
    *,
    public: tuple[RelationSlot, ...],
    witness: tuple[RelationSlot, ...] = (),
    oracle: tuple[RelationOracleStatementDecl, ...] = (),
    phase: tuple[RelationSlot, ...] = (),
) -> tuple[RelationDefinitionRef, RelationInterface]:
    definition = fixture_relation_definition_ref(name)
    interface = RelationInterface(
        definition.definition_id, public, witness, oracle, phase
    )
    return definition, interface


def _empty_plan_binding(
    plan: ProverPlan,
    core: object,
    construction: object | None,
    interpretation: object,
    relation_interface: RelationInterface,
) -> PlanWitnessBinding:
    surface = derive_plan_witness_surface(core, construction, interpretation, plan)
    return PlanWitnessBinding(
        plan_witness_surface_id(surface),
        relation_interface_id(relation_interface),
        (),
    )


def schnorr_case() -> DependentSurfaceCase:
    core, construction, invocation, strategy = k2.schnorr_fixture()
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    interface = default_interface(
        core, construction, interpretation, expose_all_transports=True
    )
    plan = ProverPlan(
        protocol_id(core, construction, interpretation),
        (
            PrivateMaterialDecl("secret", PrivateMaterialKind.WITNESS_INGRESS, NAT),
        ),
        (PrivateRandomnessRequirement("nonce", NAT, "commitment"),),
        (),
        (
            DecisionRoute(
                "commitment",
                MoveKind.MESSAGE_VALUE,
                (PlanRead(PlanReadKind.PRIVATE_RANDOMNESS, "nonce"),),
                (),
                _algorithm("schnorr-commit"),
            ),
            DecisionRoute(
                "response",
                MoveKind.MESSAGE_VALUE,
                (
                    PlanRead(PlanReadKind.PRIVATE_MATERIAL, "secret"),
                    PlanRead(PlanReadKind.PRIVATE_RANDOMNESS, "nonce"),
                    PlanRead(PlanReadKind.PRIOR_OCCURRENCE_VIEW, "challenge"),
                ),
                (),
                _algorithm("schnorr-response"),
            ),
        ),
        (),
    )
    definition_source = selected_schnorr_relation_definition()
    definition = RelationDefinitionRef(
        schnorr_relation_definition_id(definition_source)
    )
    relation_interface = RelationInterface(
        definition.definition_id,
        (RelationSlot("statement", NAT),),
        (RelationSlot("secret", NAT),),
        (),
        (),
    )
    relation_id = relation_interface_id(relation_interface)
    instances = (RelationInstanceOccurrence("knowledge-instance", relation_id),)
    protocol_binding = ProtocolRelationBinding(
        plan.protocol_id,
        (relation_id,),
        instances,
        (
            PublicSlotEdge(
                "knowledge-instance", "statement", BindingRef("root", "statement")
            ),
        ),
        (),
        (),
        (
            ClaimEdge(
                "knowledge-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "knowledge")
            ),
        ),
    )
    surface = derive_plan_witness_surface(core, construction, interpretation, plan)
    plan_binding = PlanWitnessBinding(
        plan_witness_surface_id(surface),
        relation_id,
        (WitnessSlotEdge("secret", "secret"),),
    )
    return DependentSurfaceCase(
        "schnorr",
        core,
        construction,
        invocation,
        strategy,
        interface,
        plan,
        (definition,),
        (relation_interface,),
        protocol_binding,
        plan_binding,
        (),
        (definition_source,),
    )


def verifier_private_case() -> DependentSurfaceCase:
    core = k2.Core(
        inputs=(
            k2.InputDecl("statement", k2.InputRole.STATEMENT),
            k2.InputDecl("verifier-secret", k2.InputRole.VERIFIER_PRIVATE),
        ),
        scopes=(k2.ScopeDecl("root", None, None),),
        schedule=(
            k2.Occurrence(
                "private-derived",
                k2.OccurrenceKind.VERIFIER_MESSAGE,
                dependencies=(k2.ValueRef.input("verifier-secret"),),
                verifier_rule=k2.VerifierRule(k2.VerifierRuleKind.COPY),
            ),
            k2.Occurrence("terminal", k2.OccurrenceKind.TERMINAL),
        ),
        initial_claims=("fresh-only",),
        claim_uses=(k2.ClaimConsumerUse("fresh-only", "terminal"),),
    )
    construction = k2.TranscriptConstruction(b"zkc/k3/verifier-private/v0")
    invocation = k2.Invocation(
        MappingProxyType({"statement": b"public", "verifier-secret": b"secret"})
    )
    interpretation = k2.ChallengeInterpretation.FRESH
    plan = ProverPlan(protocol_id(core, None, interpretation), (), (), (), (), ())
    definition, relation_interface = _simple_relation(
        "fresh-statement", public=(RelationSlot("statement", BYTES),), witness=()
    )
    relation_id = relation_interface_id(relation_interface)
    instances = (RelationInstanceOccurrence("fresh-instance", relation_id),)
    protocol_binding = ProtocolRelationBinding(
        plan.protocol_id,
        (relation_id,),
        instances,
        (
            PublicSlotEdge(
                "fresh-instance", "statement", BindingRef("root", "statement")
            ),
        ),
        (),
        (),
        (ClaimEdge("fresh-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "fresh-only")),),
    )
    plan_binding = _empty_plan_binding(
        plan, core, None, interpretation, relation_interface
    )
    return DependentSurfaceCase(
        "verifier-private",
        core,
        construction,
        invocation,
        k2.ScriptedStrategy({}),
        default_interface(core, None, interpretation, expose_all_transports=True),
        plan,
        (definition,),
        (relation_interface,),
        protocol_binding,
        plan_binding,
    )


def fri_oracle_case() -> DependentSurfaceCase:
    core, construction, invocation, strategy = k2.oracle_fixture()
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    plan = ProverPlan(
        protocol_id(core, construction, interpretation),
        (
            PrivateMaterialDecl("polynomial", PrivateMaterialKind.WITNESS_INGRESS, ORACLE_CELLS),
            PrivateMaterialDecl("merkle-advice", PrivateMaterialKind.ADVICE, BYTES32),
        ),
        (),
        (),
        (
            DecisionRoute(
                "oracle",
                MoveKind.ORACLE_OBJECT,
                (
                    PlanRead(PlanReadKind.PRIVATE_MATERIAL, "polynomial"),
                    PlanRead(PlanReadKind.PRIVATE_MATERIAL, "merkle-advice"),
                ),
                (),
                _algorithm("fri-publish-oracle"),
            ),
        ),
        (),
    )
    definition, relation_interface = _simple_relation(
        "fri-oracle-relation",
        public=(RelationSlot("statement", BYTES),),
        witness=(RelationSlot("polynomial", ORACLE_CELLS),),
        oracle=(
            RelationOracleStatementDecl(
                "oracle",
                BYTES,
                ORACLE_CELLS,
                NAT,
                BYTES,
                fixture_semantic_ref(
                    "relations.oracle-access-law", "fri-oracle-access"
                ),
            ),
        ),
        phase=(RelationSlot("query-coin", NAT),),
    )
    relation_id = relation_interface_id(relation_interface)
    instances = (RelationInstanceOccurrence("fri-instance", relation_id),)
    protocol_binding = ProtocolRelationBinding(
        plan.protocol_id,
        (relation_id,),
        instances,
        (
            PublicSlotEdge(
                "fri-instance", "statement", BindingRef("root", "statement")
            ),
        ),
        (
            PhaseSlotEdge(
                "fri-instance", "query-coin", k2.ValueRef.occurrence("query_coin")
            ),
        ),
        (
            OracleSlotEdge(
                "fri-instance",
                "oracle",
                k2.ValueRef.occurrence("oracle"),
                k2.ValueRef.occurrence("query"),
                k2.ValueRef.occurrence("answer"),
            ),
        ),
        (ClaimEdge("fri-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "oracle-claim")),),
    )
    surface = derive_plan_witness_surface(core, construction, interpretation, plan)
    plan_binding = PlanWitnessBinding(
        plan_witness_surface_id(surface),
        relation_id,
        (WitnessSlotEdge("polynomial", "polynomial"),),
    )
    return DependentSurfaceCase(
        "fri-oracle",
        core,
        construction,
        invocation,
        strategy,
        default_interface(
            core, construction, interpretation, expose_all_transports=True
        ),
        plan,
        (definition,),
        (relation_interface,),
        protocol_binding,
        plan_binding,
    )


def r1cs_case() -> DependentSurfaceCase:
    """Construct a typed R1CS attachment; no R1CS evaluator is claimed."""

    core = k2.Core(
        inputs=(
            k2.InputDecl("instance", k2.InputRole.STATEMENT),
            k2.InputDecl("constraint-system", k2.InputRole.PUBLIC_PARAMETER),
        ),
        scopes=(k2.ScopeDecl("root", None, None),),
        schedule=(
            k2.Occurrence("proof", k2.OccurrenceKind.PROVER_MESSAGE),
            k2.Occurrence(
                "verify",
                k2.OccurrenceKind.CHECK,
                dependencies=(
                    k2.ValueRef.occurrence("proof"),
                    k2.ValueRef.input("instance"),
                ),
                check_predicate=k2.Predicate(
                    k2.PredicateKind.BYTES_EQUAL,
                    (
                        k2.ValueRef.occurrence("proof"),
                        k2.ValueRef.input("instance"),
                    ),
                ),
            ),
            k2.Occurrence("terminal", k2.OccurrenceKind.TERMINAL),
        ),
        initial_claims=("r1cs-sat",),
        claim_uses=(k2.ClaimConsumerUse("r1cs-sat", "terminal"),),
    )
    construction = k2.TranscriptConstruction(b"zkc/k3/r1cs/v0")
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    plan = ProverPlan(
        protocol_id(core, construction, interpretation),
        (PrivateMaterialDecl("assignment", PrivateMaterialKind.WITNESS_INGRESS, BYTES),),
        (),
        (),
        (
            DecisionRoute(
                "proof",
                MoveKind.MESSAGE_VALUE,
                (PlanRead(PlanReadKind.PRIVATE_MATERIAL, "assignment"),),
                (),
                _algorithm("r1cs-prove"),
            ),
        ),
        (),
    )
    definition, relation_interface = _simple_relation(
        "r1cs",
        public=(
            RelationSlot("instance", BYTES),
            RelationSlot("constraint-system", BYTES),
        ),
        witness=(RelationSlot("assignment", BYTES),),
    )
    relation_id = relation_interface_id(relation_interface)
    instances = (RelationInstanceOccurrence("r1cs-instance", relation_id),)
    protocol_binding = ProtocolRelationBinding(
        plan.protocol_id,
        (relation_id,),
        instances,
        (
            PublicSlotEdge(
                "r1cs-instance", "instance", BindingRef("root", "instance")
            ),
            PublicSlotEdge(
                "r1cs-instance",
                "constraint-system",
                k2.ValueRef.input("constraint-system"),
            ),
        ),
        (),
        (),
        (ClaimEdge("r1cs-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "r1cs-sat")),),
    )
    surface = derive_plan_witness_surface(core, construction, interpretation, plan)
    plan_binding = PlanWitnessBinding(
        plan_witness_surface_id(surface),
        relation_id,
        (WitnessSlotEdge("assignment", "assignment"),),
    )
    return DependentSurfaceCase(
        "r1cs",
        core,
        construction,
        None,
        None,
        default_interface(
            core, construction, interpretation, expose_all_transports=True
        ),
        plan,
        (definition,),
        (relation_interface,),
        protocol_binding,
        plan_binding,
    )


def r1cs_grounding_equation() -> GroundingEquation:
    digest_type = FactType(FactKind.VALUE, BYTES32)
    schema = ArtifactFactSchema(
        "r1cs-artifact",
        (
            ArtifactFactDecl("matrix-digest", digest_type),
            ArtifactFactDecl("constraint-count", NAT_FACT),
            ArtifactFactDecl("relation-id", ID_FACT),
        ),
    )
    selector = ArtifactSelector(
        "matrix-digest-at-zero", "matrix-digest", SelectorKind.AT, 0
    )
    declared = k1.admit_value(BYTES32, k1.BytesValue(b"d" * 32))
    return GroundingEquation(
        "r1cs-material-grounding",
        schema,
        (selector,),
        (
            EquationNode(
                "observed",
                EquationOp.SELECT,
                digest_type,
                reference="matrix-digest-at-zero",
            ),
            EquationNode(
                "declared", EquationOp.CONSTANT, digest_type, reference=declared
            ),
            EquationNode(
                "matches",
                EquationOp.EQUAL,
                BOOL_FACT,
                dependencies=("observed", "declared"),
            ),
        ),
        "matches",
    )


def nova_case() -> DependentSurfaceCase:
    """Construct two input instances and one folded output occurrence."""

    core = k2.Core(
        inputs=(
            k2.InputDecl("left-accumulator", k2.InputRole.STATEMENT),
            k2.InputDecl("right-accumulator", k2.InputRole.STATEMENT),
        ),
        scopes=(k2.ScopeDecl("root", None, None),),
        schedule=(
            k2.Occurrence("left-commit", k2.OccurrenceKind.PROVER_MESSAGE),
            k2.Occurrence("right-commit", k2.OccurrenceKind.PROVER_MESSAGE),
            k2.Occurrence(
                "rho",
                k2.OccurrenceKind.CHALLENGE,
                dependencies=(
                    k2.ValueRef.input("left-accumulator"),
                    k2.ValueRef.input("right-accumulator"),
                ),
                challenge_domain=k2.ChallengeDomain(23),
            ),
            k2.Occurrence("folded-commit", k2.OccurrenceKind.PROVER_MESSAGE),
            k2.Occurrence(
                "verify-fold",
                k2.OccurrenceKind.CHECK,
                dependencies=(
                    k2.ValueRef.input("left-accumulator"),
                    k2.ValueRef.input("right-accumulator"),
                ),
                check_predicate=k2.Predicate(
                    k2.PredicateKind.BYTES_EQUAL,
                    (
                        k2.ValueRef.input("left-accumulator"),
                        k2.ValueRef.input("right-accumulator"),
                    ),
                ),
            ),
            k2.Occurrence("terminal", k2.OccurrenceKind.TERMINAL),
        ),
        initial_claims=("left", "right"),
        reductions=(
            k2.ReductionDecl(
                "fold",
                "verify-fold",
                "root",
                ("left", "right"),
                (
                    k2.ValueRef.occurrence("left-commit"),
                    k2.ValueRef.occurrence("right-commit"),
                    k2.ValueRef.occurrence("rho"),
                    k2.ValueRef.occurrence("folded-commit"),
                ),
                ("rho",),
                (
                    k2.RequiredPublication("left-commit", "rho"),
                    k2.RequiredPublication("right-commit", "rho"),
                    k2.RequiredPublication("folded-commit", None),
                ),
                ("folded",),
            ),
        ),
        claim_uses=(
            k2.ClaimConsumerUse("left", "fold"),
            k2.ClaimConsumerUse("right", "fold"),
            k2.ClaimConsumerUse("folded", "terminal"),
        ),
    )
    construction = k2.TranscriptConstruction(b"zkc/k3/nova/v0")
    interpretation = k2.ChallengeInterpretation.FIAT_SHAMIR
    plan = ProverPlan(
        protocol_id(core, construction, interpretation),
        (
            PrivateMaterialDecl("w-left", PrivateMaterialKind.WITNESS_INGRESS, BYTES),
            PrivateMaterialDecl("w-right", PrivateMaterialKind.WITNESS_INGRESS, BYTES),
            PrivateMaterialDecl("initial-fold-state", PrivateMaterialKind.CONFIDENTIAL_CONTEXT, BYTES),
        ),
        (),
        (PersistentStrategyState("fold-state", BYTES, "initial-fold-state"),),
        (
            DecisionRoute(
                "left-commit",
                MoveKind.MESSAGE_VALUE,
                (PlanRead(PlanReadKind.PRIVATE_MATERIAL, "w-left"),),
                (StateAfterBinding("fold-state", StateAfterKind.KEEP),),
                _algorithm("nova-left"),
            ),
            DecisionRoute(
                "right-commit",
                MoveKind.MESSAGE_VALUE,
                (PlanRead(PlanReadKind.PRIVATE_MATERIAL, "w-right"),),
                (StateAfterBinding("fold-state", StateAfterKind.KEEP),),
                _algorithm("nova-right"),
            ),
            DecisionRoute(
                "folded-commit",
                MoveKind.MESSAGE_VALUE,
                (
                    PlanRead(PlanReadKind.PRIVATE_MATERIAL, "w-left"),
                    PlanRead(PlanReadKind.PRIVATE_MATERIAL, "w-right"),
                    PlanRead(PlanReadKind.STATE_BEFORE, "fold-state"),
                    PlanRead(PlanReadKind.PRIOR_OCCURRENCE_VIEW, "rho"),
                ),
                (
                    StateAfterBinding(
                        "fold-state", StateAfterKind.REPLACE_WITH_DECISION_OUTPUT
                    ),
                ),
                _algorithm("nova-fold"),
            ),
        ),
        (PlanExport("w-folded-export", "folded-commit", BYTES),),
    )
    definition, relation_interface = _simple_relation(
        "relaxed-r1cs",
        public=(RelationSlot("accumulator", BYTES),),
        witness=(RelationSlot("witness", BYTES),),
    )
    relation_id = relation_interface_id(relation_interface)
    instances = (
        RelationInstanceOccurrence("left-instance", relation_id),
        RelationInstanceOccurrence("right-instance", relation_id),
        RelationInstanceOccurrence("folded-instance", relation_id),
    )
    protocol_binding = ProtocolRelationBinding(
        plan.protocol_id,
        (relation_id,),
        instances,
        (
            PublicSlotEdge(
                "left-instance", "accumulator", BindingRef("root", "left-accumulator")
            ),
            PublicSlotEdge(
                "right-instance",
                "accumulator",
                BindingRef("root", "right-accumulator"),
            ),
            PublicSlotEdge(
                "folded-instance",
                "accumulator",
                k2.ValueRef.occurrence("folded-commit"),
            ),
        ),
        (),
        (),
        (
            ClaimEdge("left-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "left")),
            ClaimEdge(
                "right-instance", ClaimCoordinate(ClaimOrigin.INITIAL, "right")
            ),
            ClaimEdge(
                "folded-instance",
                ClaimCoordinate(ClaimOrigin.REDUCTION_OUTPUT, "folded", "fold"),
            ),
        ),
    )
    surface = derive_plan_witness_surface(core, construction, interpretation, plan)
    plan_binding = PlanWitnessBinding(
        plan_witness_surface_id(surface),
        relation_id,
        (WitnessSlotEdge("witness", "w-folded-export"),),
    )
    return DependentSurfaceCase(
        "nova",
        core,
        construction,
        None,
        None,
        default_interface(
            core, construction, interpretation, expose_all_transports=True
        ),
        plan,
        (definition,),
        (relation_interface,),
        protocol_binding,
        plan_binding,
    )


def three_bridge_fixtures() -> tuple[ValueBridge, ValueBridge, ValueBridge]:
    forward = _algorithm("bridge-forward")
    inverse = _algorithm("bridge-inverse")
    image = fixture_semantic_ref("relations.predicate", "bridge-image")
    collision = fixture_semantic_ref("relations.definition", "sha256-216-collision")
    premise = fixture_semantic_ref(
        "relations.loss-source-premise", "preimage-availability"
    )
    export = fixture_semantic_ref(
        "relations.loss-export", "preimage-loss-export"
    )
    return (
        ValueBridge(
            "field-canonical-equivalence",
            ValueBridgeLane.TOTAL_EQUIVALENCE,
            NAT,
            NAT,
            forward,
            inverse_algorithm_id=inverse,
        ),
        ValueBridge(
            "bytes-into-tagged-bytes",
            ValueBridgeLane.INJECTIVE_EMBEDDING,
            BYTES32,
            BYTES96,
            forward,
            inverse_algorithm_id=inverse,
            image_predicate_id=image,
        ),
        ValueBridge(
            "sha256-216",
            ValueBridgeLane.DIRECTIONAL_LOSSY,
            BYTES32,
            BYTES,
            forward,
            collision_relation_id=collision,
            source_premise_id=premise,
            quantitative_export_id=export,
        ),
    )
