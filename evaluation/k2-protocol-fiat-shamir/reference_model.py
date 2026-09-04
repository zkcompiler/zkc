"""Bounded executable candidate for the K2 Protocol/Fiat--Shamir kernel.

This module is a research instrument, not repository authority.  It imports
K1's canonical ``Datum`` and typed content-identity machinery and adds only the
finite protocol surface needed by the K2 fixtures.  The model deliberately
separates three questions:

* ``admit_core`` checks one exact finite interaction schedule;
* ``generate`` asks an online prover strategy for each current move through a
  restricted prefix view; and
* ``replay`` checks a completed record without claiming that a causal strategy
  generated it.

The same literal ``Core`` is interpreted with fresh public coins or with an
admitted transcript construction.  Transcript influence is derived from the
Core; there is no per-message author-controlled "absorb" bit.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Callable, Mapping, Protocol, TypeAlias


# ---------------------------------------------------------------------------
# K1 foundation import
# ---------------------------------------------------------------------------


_K1_NAME = "_zkc_k1_executable_foundations"
_K1_PATH = (
    Path(__file__).resolve().parents[1]
    / "k1-executable-foundations"
    / "reference_model.py"
)
if _K1_NAME in sys.modules:
    k1 = sys.modules[_K1_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K1_NAME, _K1_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load K1 reference model from {_K1_PATH}")
    k1 = importlib.util.module_from_spec(_spec)
    sys.modules[_K1_NAME] = k1
    _spec.loader.exec_module(k1)


# ---------------------------------------------------------------------------
# Finite carriers and typed refusals
# ---------------------------------------------------------------------------


MAX_INPUTS = 128
MAX_SCOPES = 64
MAX_OCCURRENCES = 512
MAX_DEPENDENCIES = 64
MAX_CLAIMS = 256
MAX_ORACLE_CELLS = 4096
MAX_CELL_BYTES = 1 << 16


class ModelError(ValueError):
    """Base class for a K2 model refusal."""


class AdmissionError(ModelError):
    """The Core or construction is outside the selected K2 surface."""


class InvocationError(ModelError):
    """An invocation does not provide the Core's exact input surface."""


class FreshResolutionError(ModelError):
    """A Fresh challenge resolver is missing or returned an invalid value."""


class ReplayError(ModelError):
    """A completed record is not an exact run of the selected interpretation."""


class ExecutionError(ModelError):
    """A deterministic protocol operation is undefined on this invocation."""


class FutureReadError(ModelError):
    """A strategy attempted to observe an occurrence not yet available."""


class UnsupportedSemanticProfileError(ModelError):
    """A formed profile bundle is not supported by the selected evaluator."""


class MalformedSemanticProfileError(ModelError):
    """A profile bundle or exact import closure has malformed shape."""


class RefusedSemanticProfileError(ModelError):
    """A formed profile cannot issue the requested subject kind."""


def _language_profile_catalog(
    catalog_kind: str,
    declarations: tuple[str, ...],
) -> object:
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


def _named_declaration_body(name: str) -> object:
    return k1.DatumRecord(((0, k1.Symbol(name)),))


def _language_profile_catalogs(
    catalogs: Mapping[str, tuple[str, ...]],
) -> object:
    """Form named finite catalogs in the owner's kind and ordinal order."""

    return k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Symbol(kind)),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(
                                _named_declaration_body(name)
                                for name in declarations
                            )
                        ),
                    ),
                )
            )
            for kind, declarations in sorted(catalogs.items())
        )
    )


_CANONICAL_CHECKER_DECLARATION_CATALOGS = MappingProxyType(
    {
        "pir.evaluator-signature": (
            "canonical-framed-evaluator-v0",
            "canonical-framed-construction-check-v0",
        ),
        "pir.failure-schema": (
            "canonical-framed-outcome-partition-v0",
            "canonical-framed-construction-defects-v0",
        ),
        "pir.semantic-law": (
            "canonical-framed-admission-and-execution-v0",
            "canonical-framed-body-grammar-v0",
            "canonical-framed-prefix-and-domain-v0",
            "canonical-framed-same-core-construction-v0",
            "canonical-framed-source-views-v0",
            "canonical-framed-protocol-execution-v0",
            "canonical-framed-replay-v0",
        ),
        "pir.transcript-declaration": (
            "fs-protocol-body-v1",
            "pir-transcript-and-fs-view-catalog-v0",
            "pir-source-authority-envelope-specialization-v0",
            "transcript-construction-body-v1",
        ),
    }
)


def _sorted_profile_imports(*profiles: object) -> tuple[object, ...]:
    return tuple(
        sorted(
            (profile.identity for profile in profiles),
            key=lambda identifier: identifier.internal_reference(),
        )
    )


@dataclass(frozen=True)
class K2SemanticProfiles:
    interaction: object
    transcript_fs: object
    public_view: object

    def __post_init__(self) -> None:
        if any(
            type(item) is not k1.SemanticLanguageProfile
            for item in (self.interaction, self.transcript_fs, self.public_view)
        ):
            raise ModelError("K2 semantic profiles have the wrong exact shape")
        if self.transcript_fs.profile_imports != _sorted_profile_imports(
            self.interaction
        ):
            raise ModelError("the Transcript/FS profile must import Interaction")
        if self.public_view.profile_imports != _sorted_profile_imports(
            self.interaction
        ):
            raise ModelError("the public-view profile must import only Interaction")

    @property
    def bundle(self) -> dict[object, object]:
        return {
            profile.identity: profile
            for profile in (
                self.interaction,
                self.transcript_fs,
                self.public_view,
            )
        }


def make_k2_semantic_profiles(
    *,
    interaction_law: bytes = b"zkc-k2-interaction-core-fresh-law-v0",
    transcript_fs_law: bytes = b"zkc-k2-transcript-fs-law-v0",
    public_view_law: bytes = b"zkc-k2-public-view-export-law-v0",
) -> K2SemanticProfiles:
    interaction = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.interaction-core-fresh"),
        0,
        (),
        tuple(
            k1.Symbol(item)
            for item in sorted(
                (
                    "pir.interactive-core",
                    "pir.invocation",
                    "pir.protocol",
                    "pir.source-binding-payload",
                    "pir.source-capability-requirement",
                    "pir.source-consumer",
                    "pir.source-no-policy",
                    "pir.source-policy-closure",
                    "pir.source-purpose",
                )
            )
        ),
        _language_profile_catalog(
            "pir.interaction-declaration",
            (
                "core-body-v1",
                "fresh-protocol-body-v1",
                "pir-core-and-execution-view-catalog-v0",
                "pir-source-authority-envelope-specialization-v0",
                "core-invocation-body-v1",
            ),
        ),
        interaction_law,
    )
    transcript_fs = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.transcript-fs"),
        0,
        _sorted_profile_imports(interaction),
        tuple(
            k1.Symbol(item)
            for item in sorted(
                (
                    "pir.protocol",
                    "pir.source-binding-payload",
                    "pir.source-capability-requirement",
                    "pir.source-consumer",
                    "pir.source-no-policy",
                    "pir.source-policy-closure",
                    "pir.source-purpose",
                    "pir.checker-contract",
                    "pir.transcript-construction",
                )
            )
        ),
        _language_profile_catalogs(_CANONICAL_CHECKER_DECLARATION_CATALOGS),
        transcript_fs_law,
    )
    public_view = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.public-view-export"),
        0,
        _sorted_profile_imports(interaction),
        tuple(
            k1.Symbol(item)
            for item in sorted(
                (
                    "pir.public-setup-invocation-view",
                    "pir.source-binding-payload",
                    "pir.source-capability-requirement",
                    "pir.source-consumer",
                    "pir.source-no-policy",
                    "pir.source-policy-closure",
                    "pir.source-purpose",
                )
            )
        ),
        _language_profile_catalog(
            "pir.public-view-declaration",
            (
                "pir-source-authority-envelope-specialization-v0",
                "public-setup-invocation-view-body-v1",
            ),
        ),
        public_view_law,
    )
    return K2SemanticProfiles(interaction, transcript_fs, public_view)


K2_SEMANTIC_PROFILES = make_k2_semantic_profiles()
K2_PROFILE_BUNDLE = K2_SEMANTIC_PROFILES.bundle
PIR_INTERACTION_PROFILE = K2_SEMANTIC_PROFILES.interaction
PIR_INTERACTION_PROFILE_ID = PIR_INTERACTION_PROFILE.identity
PIR_TRANSCRIPT_PROFILE = K2_SEMANTIC_PROFILES.transcript_fs
PIR_TRANSCRIPT_PROFILE_ID = PIR_TRANSCRIPT_PROFILE.identity
# The selected K2 split deliberately uses one Transcript/FS profile.  These
# aliases expose the FS-facing name without pretending there is a second law.
PIR_FS_PROFILE = PIR_TRANSCRIPT_PROFILE
PIR_FS_PROFILE_ID = PIR_TRANSCRIPT_PROFILE_ID
PIR_PUBLIC_SETUP_PROFILE = K2_SEMANTIC_PROFILES.public_view
PIR_PUBLIC_SETUP_PROFILE_ID = PIR_PUBLIC_SETUP_PROFILE.identity


def k2_root_profile_preimages(
    profiles: K2SemanticProfiles,
) -> Mapping[object, Mapping[object, object]]:
    if type(profiles) is not K2SemanticProfiles:
        raise ModelError("K2 root closures need one exact profile bundle")
    interaction = {profiles.interaction.identity: profiles.interaction}
    transcript = {
        **interaction,
        profiles.transcript_fs.identity: profiles.transcript_fs,
    }
    public_view = {
        **interaction,
        profiles.public_view.identity: profiles.public_view,
    }
    return MappingProxyType(
        {
            profiles.interaction.identity: interaction,
            profiles.transcript_fs.identity: transcript,
            profiles.public_view.identity: public_view,
        }
    )


K2_ROOT_PROFILE_PREIMAGES = k2_root_profile_preimages(K2_SEMANTIC_PROFILES)
PIR_INTERACTION_PROFILE_PREIMAGES = K2_ROOT_PROFILE_PREIMAGES[
    PIR_INTERACTION_PROFILE_ID
]
PIR_TRANSCRIPT_PROFILE_PREIMAGES = K2_ROOT_PROFILE_PREIMAGES[
    PIR_TRANSCRIPT_PROFILE_ID
]
PIR_PUBLIC_SETUP_PROFILE_PREIMAGES = K2_ROOT_PROFILE_PREIMAGES[
    PIR_PUBLIC_SETUP_PROFILE_ID
]
# Convenience superset for consumers that need all K2 profile preimages.  It is
# not an exact root closure; use the root-specific maps above for
# authentication.
K2_PROFILE_PREIMAGES = K2_PROFILE_BUNDLE


@dataclass(frozen=True)
class K2SemanticProfileSupport:
    supported_profile_ids: frozenset[object]

    def __post_init__(self) -> None:
        if type(self.supported_profile_ids) is not frozenset:
            raise ModelError("K2 profile support must be one exact frozen ID set")
        for identifier in self.supported_profile_ids:
            if (
                type(identifier) is not k1.TypedContentId
                or identifier.subject_kind
                != k1.SEMANTIC_LANGUAGE_PROFILE_KIND
                or identifier.semantic_regime != k1.SEMANTIC_REGIME_ID
            ):
                raise ModelError("K2 profile support contains a non-profile ID")


def make_k2_profile_support(
    *bundles: K2SemanticProfiles,
) -> K2SemanticProfileSupport:
    if not bundles or any(type(item) is not K2SemanticProfiles for item in bundles):
        raise ModelError("K2 profile support needs exact profile bundles")
    return K2SemanticProfileSupport(
        frozenset(
            identifier
            for bundle in bundles
            for identifier in bundle.bundle
        )
    )


K2_PROFILE_SUPPORT = make_k2_profile_support(K2_SEMANTIC_PROFILES)


def make_k2_selected_profile_support(
    *profiles: object,
) -> K2SemanticProfileSupport:
    if not profiles or any(
        type(profile) is not k1.SemanticLanguageProfile for profile in profiles
    ):
        raise ModelError("K2 selected-profile support needs exact profiles")
    return K2SemanticProfileSupport(
        frozenset(profile.identity for profile in profiles)
    )


K2_INTERACTION_PROFILE_SUPPORT = make_k2_selected_profile_support(
    PIR_INTERACTION_PROFILE
)
K2_TRANSCRIPT_PROFILE_SUPPORT = make_k2_selected_profile_support(
    PIR_TRANSCRIPT_PROFILE
)
K2_PUBLIC_SETUP_PROFILE_SUPPORT = make_k2_selected_profile_support(
    PIR_PUBLIC_SETUP_PROFILE
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


def _require_supported_k2_profiles(
    profiles: K2SemanticProfiles,
    profile_support: K2SemanticProfileSupport,
    selected_profile: object,
    *,
    required_subject_kinds: frozenset[str] = frozenset(),
) -> None:
    if (
        type(profiles) is not K2SemanticProfiles
        or type(profile_support) is not K2SemanticProfileSupport
    ):
        raise MalformedSemanticProfileError(
            "K2 issuance needs exact profiles and evaluator support"
        )
    profiles.__post_init__()
    profile_support.__post_init__()
    root_preimages = k2_root_profile_preimages(profiles)
    if (
        type(selected_profile) is not k1.SemanticLanguageProfile
        or selected_profile.identity not in root_preimages
    ):
        raise MalformedSemanticProfileError(
            "K2 issuance selected no profile from its exact bundle"
        )
    preimages = root_preimages[selected_profile.identity]
    try:
        context = k1.effective_semantic_context(
            selected_profile.identity,
            preimages,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
        authenticated_ids = {
            identifier for identifier, _profile in context.authenticated_profiles
        }
        if authenticated_ids != set(preimages):
            raise RefusedSemanticProfileError(
                "K2 root profile bundle is not its exact no-extra closure"
            )
    except (k1.ModelError, k1.CanonicalError) as error:
        raise MalformedSemanticProfileError(
            "K2 profile import closure is not authenticated"
        ) from error
    if selected_profile.identity not in profile_support.supported_profile_ids:
        raise UnsupportedSemanticProfileError(
            "K2 evaluator does not support the selected root profile"
        )
    supported_subject_kinds = {
        item.value for item in selected_profile.supported_subject_kinds
    }
    if not required_subject_kinds.issubset(supported_subject_kinds):
        raise RefusedSemanticProfileError(
            "K2 selected profile does not support every issued subject kind"
        )


def _authenticate_k2_profiled_subject(
    identifier: object,
    subject_kind: str,
    domain_body: object,
    *,
    profiles: K2SemanticProfiles,
    profile_support: K2SemanticProfileSupport,
    selected_profile: object,
) -> None:
    _require_supported_k2_profiles(
        profiles,
        profile_support,
        selected_profile,
        required_subject_kinds=frozenset({subject_kind}),
    )
    datum = k1.decode_datum(domain_body) if type(domain_body) is bytes else domain_body
    supported_profiles = tuple(
        sorted(
            profile_support.supported_profile_ids,
            key=lambda item: item.internal_reference(),
        )
    )
    k1.authenticate_profiled_semantic_content(
        identifier,
        selected_profile.identity,
        datum,
        k2_root_profile_preimages(profiles)[selected_profile.identity],
        supported_profiles=supported_profiles,
    )


@dataclass(frozen=True)
class SamplingExhausted(ModelError):
    namespaces: tuple[bytes, ...]
    terminal_state: bytes
    attempts: int

    def __str__(self) -> str:
        return f"sampling exhausted after {self.attempts} attempts"


class InputRole(str, Enum):
    STATEMENT = "statement"
    PUBLIC_CONTEXT = "public-context"
    PUBLIC_PARAMETER = "public-parameter"
    VERIFIER_PRIVATE = "verifier-private"


class ValueSort(str, Enum):
    BYTES = "bytes"
    NAT = "nat"
    BOOL = "bool"
    ORACLE = "oracle"


class OccurrenceKind(str, Enum):
    PROVER_MESSAGE = "prover-message"
    VERIFIER_MESSAGE = "verifier-message"
    CHALLENGE = "challenge"
    CHECK = "check"
    TERMINAL = "terminal"
    ORACLE_PUBLISH = "oracle-publish"
    ORACLE_QUERY = "oracle-query"
    ORACLE_ANSWER = "oracle-answer"


class RefKind(str, Enum):
    INPUT = "input"
    OCCURRENCE = "occurrence"


@dataclass(frozen=True)
class ValueRef:
    kind: RefKind
    name: str

    @classmethod
    def input(cls, name: str) -> "ValueRef":
        return cls(RefKind.INPUT, name)

    @classmethod
    def occurrence(cls, name: str) -> "ValueRef":
        return cls(RefKind.OCCURRENCE, name)


@dataclass(frozen=True)
class InputDecl:
    name: str
    role: InputRole
    scope: str = "root"
    value_sort: ValueSort = ValueSort.BYTES


@dataclass(frozen=True)
class ScopeDecl:
    """One unconditional lexical scope activation.

    ``open_before=None`` means open during initialization.  Otherwise the
    scope opens immediately before the named occurrence, against the current
    transcript state.  Opening never resets the state.
    """

    name: str
    parent: str | None
    open_before: str | None


class PredicateKind(str, Enum):
    ALWAYS = "always"
    NEVER = "never"
    BOOL = "bool"
    BYTES_EQUAL = "bytes-equal"
    SCHNORR = "fixture-schnorr"
    LEADING_ZERO_BITS = "fixture-leading-zero-bits"


@dataclass(frozen=True)
class Predicate:
    """A bounded pure fixture predicate, the permitted non-K1 guard lane."""

    kind: PredicateKind = PredicateKind.ALWAYS
    refs: tuple[ValueRef, ...] = ()
    parameters: tuple[int, ...] = ()


class VerifierRuleKind(str, Enum):
    COPY = "copy"
    SHA256 = "sha2-256"
    CONSTANT_INT = "constant-int"


@dataclass(frozen=True)
class VerifierRule:
    kind: VerifierRuleKind
    parameters: tuple[int, ...] = ()


@dataclass(frozen=True)
class ChallengeDomain:
    modulus: int


@dataclass(frozen=True)
class Occurrence:
    name: str
    kind: OccurrenceKind
    scope: str = "root"
    dependencies: tuple[ValueRef, ...] = ()
    guard: Predicate = Predicate()
    verifier_rule: VerifierRule | None = None
    challenge_domain: ChallengeDomain | None = None
    oracle_name: str | None = None
    check_predicate: Predicate | None = None
    prover_value_sort: ValueSort = ValueSort.BYTES


@dataclass(frozen=True)
class RequiredPublication:
    publication: str
    next_challenge: str | None


@dataclass(frozen=True)
class ReductionDecl:
    name: str
    at_occurrence: str
    scope: str
    input_claims: tuple[str, ...]
    side_inputs: tuple[ValueRef, ...]
    required_challenges: tuple[str, ...]
    required_publications: tuple[RequiredPublication, ...]
    output_claims: tuple[str, ...]


@dataclass(frozen=True)
class ClaimConsumerUse:
    claim: str
    consumer: str


@dataclass(frozen=True)
class Core:
    inputs: tuple[InputDecl, ...]
    scopes: tuple[ScopeDecl, ...]
    schedule: tuple[Occurrence, ...]
    extensions: tuple[str, ...] = ()
    initial_claims: tuple[str, ...] = ()
    reductions: tuple[ReductionDecl, ...] = ()
    claim_uses: tuple[ClaimConsumerUse, ...] = ()


@dataclass(frozen=True)
class OracleObject:
    cells: tuple[bytes, ...]


Value: TypeAlias = bytes | int | bool | OracleObject


@dataclass(frozen=True)
class Invocation:
    values: Mapping[str, Value]


@dataclass(frozen=True)
class InfluenceAtom:
    """One finite, coordinate-bearing transcript-influence obligation."""

    kind: str
    coordinates: tuple[str, ...]


@dataclass(frozen=True)
class Frame:
    tag: str
    payload: bytes
    atom: InfluenceAtom


@dataclass(frozen=True)
class InfluenceComparison:
    required: tuple[InfluenceAtom, ...]
    observed: tuple[InfluenceAtom, ...]
    missing: tuple[InfluenceAtom, ...]


class EntryStatus(str, Enum):
    EXECUTED = "executed"
    SKIPPED = "skipped"


@dataclass(frozen=True)
class RunEntry:
    occurrence: str
    kind: OccurrenceKind
    status: EntryStatus
    value: Value | None
    prefix_state: bytes | None = None
    draw_namespaces: tuple[bytes, ...] = ()
    sampling_attempts: int | None = None
    influence: InfluenceComparison | None = None


@dataclass(frozen=True)
class RunRecord:
    core_id: object
    construction_id: object | None
    invocation_id: object
    interpretation: "ChallengeInterpretation"
    entries: tuple[RunEntry, ...]
    transcript_frames: tuple[Frame, ...]
    terminal_state: bytes | None


class ChallengeInterpretation(str, Enum):
    FRESH = "fresh-public-coins"
    FIAT_SHAMIR = "fiat-shamir"


class NoncompletionReason(str, Enum):
    STRATEGY_STOPPED = "strategy-stopped"
    FUTURE_READ = "future-read"
    INVALID_MOVE = "invalid-move"


@dataclass(frozen=True)
class Noncompletion:
    reason: NoncompletionReason
    at_occurrence: str
    detail: str


@dataclass(frozen=True)
class Completed:
    record: RunRecord


GenerationResult: TypeAlias = Completed | Noncompletion


class StrategyStopped(Exception):
    """A strategy may decline a move without creating a Core terminal."""


class ProverStrategy(Protocol):
    def move(self, occurrence: Occurrence, view: "ProverView") -> Value:
        ...


@dataclass(frozen=True)
class FreshChallengeRequest:
    """One challenge-time request issued only by the Fresh execution lane."""

    occurrence: str
    domain: ChallengeDomain


class FreshChallengeResolver(Protocol):
    def resolve(self, request: FreshChallengeRequest) -> int:
        ...


class ScriptedFreshResolver:
    """Deterministic runtime resolver for bounded fixtures and falsifiers."""

    def __init__(self, values: Mapping[str, int]) -> None:
        self._values = MappingProxyType(dict(values))
        self._requests: list[FreshChallengeRequest] = []

    @property
    def requests(self) -> tuple[FreshChallengeRequest, ...]:
        return tuple(self._requests)

    def resolve(self, request: FreshChallengeRequest) -> int:
        self._requests.append(request)
        try:
            return self._values[request.occurrence]
        except KeyError as error:
            raise FreshResolutionError(
                f"fresh resolver has no value for challenge {request.occurrence!r}"
            ) from error


# ---------------------------------------------------------------------------
# Canonical K1-backed identity
# ---------------------------------------------------------------------------


def _symbol(text: str, what: str) -> object:
    if type(text) is not str or not text or any(ord(ch) < 0x21 or ord(ch) > 0x7E for ch in text):
        raise AdmissionError(f"{what} must be nonempty printable ASCII without spaces")
    return k1.Symbol(text)


def _datum(value: Value | None) -> object:
    if value is None:
        return k1.DatumVariant(0, k1.UNIT)
    if type(value) is bytes:
        return k1.DatumVariant(1, k1.BytesValue(value))
    if type(value) is int:
        if value < 0:
            raise ModelError("fixture values use nonnegative integers")
        return k1.DatumVariant(2, k1.Nat(value))
    if type(value) is bool:
        return k1.DatumVariant(3, value)
    if type(value) is OracleObject:
        return k1.DatumVariant(
            4,
            k1.DatumSeq(tuple(k1.BytesValue(cell) for cell in value.cells)),
        )
    raise ModelError(f"unsupported fixture value: {type(value)!r}")


def _appendix_ref(value: int, what: str) -> object:
    """Form one exact Appendix-A natural reference coordinate."""

    if type(value) is not int or not 0 <= value < 1 << 64:
        raise ModelError(f"{what} must be an unsigned 64-bit natural")
    return k1.Nat(value)


def appendix_guard_outcome_frame_body(
    occurrence_ref: int,
    active: bool,
) -> object:
    """Form the exact K2 Appendix-A GuardOutcome frame body.

    K1 Boolean values are MetaBooleanFalse/MetaBooleanTrue scalar datums.  In
    particular, this body deliberately does not wrap ``active`` in a generic
    MetaVariant.
    """

    if type(active) is not bool:
        raise ModelError("guard outcome must be one exact K1 Boolean")
    return k1.DatumVariant(
        5,
        k1.DatumRecord(
            (
                (0, _appendix_ref(occurrence_ref, "occurrence reference")),
                (1, active),
            )
        ),
    )


def appendix_oracle_lookup_result_type(element_type: object) -> object:
    """Form ``RootVariant<[(0, RootUnit), (1, element_type)]>`` exactly."""

    if type(element_type) is not k1.ValueType:
        raise ModelError("Oracle element type must be one exact K1 ValueType")
    if element_type.domain.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise ModelError("Oracle element type crosses the K2 fixture regime")
    unit_type = k1.ValueType(k1.UNIT_DOMAIN, k1.UNIT_SCHEMA)
    return k1.ValueType(
        k1.VARIANT_DOMAIN,
        k1.VariantSchema(((0, unit_type), (1, element_type))),
    )


def appendix_oracle_answer_frame_body(
    occurrence_ref: int,
    oracle_ref: int,
    element_type: object,
    answer: object,
) -> object:
    """Form one exact K2 Appendix-A OracleAnswer frame body.

    The type carried in field 2 is the derived lookup-result sum, never the
    element type.  Admission at that sum makes both absent and present answers
    formable before the frame is returned.
    """

    result_type = appendix_oracle_lookup_result_type(element_type)
    admitted = k1.admit_value(result_type, answer)
    return k1.DatumVariant(
        10,
        k1.DatumRecord(
            (
                (0, _appendix_ref(occurrence_ref, "occurrence reference")),
                (1, _appendix_ref(oracle_ref, "Oracle reference")),
                (2, k1.value_type_datum(result_type)),
                (3, admitted.datum),
            )
        ),
    )


def _ref_datum(ref: ValueRef) -> object:
    return k1.DatumRecord(
        ((0, k1.Symbol(ref.kind.value)), (1, _symbol(ref.name, "reference name")))
    )


def _validate_ref(ref: object) -> ValueRef:
    if type(ref) is not ValueRef or type(ref.kind) is not RefKind:
        raise AdmissionError("value reference has the wrong exact shape")
    _symbol(ref.name, "reference name")
    return ref


def _predicate_datum(predicate: Predicate) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol("fixture-bounded-pure-predicate-v0")),
            (1, k1.Symbol(predicate.kind.value)),
            (2, k1.DatumSeq(tuple(_ref_datum(ref) for ref in predicate.refs))),
            (3, k1.DatumSeq(tuple(k1.Nat(item) for item in predicate.parameters))),
        )
    )


def core_body(core: Core) -> bytes:
    """Return the exact K1 canonical body; schedule order is identity-bearing."""

    admit_core(core)
    datum = k1.DatumRecord(
        (
            (0, k1.Symbol("k2.protocol-core.v1")),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "input name")),
                                (1, k1.Symbol(item.role.value)),
                                (2, _symbol(item.scope, "input scope")),
                                (3, k1.Symbol(item.value_sort.value)),
                            )
                        )
                        for item in core.inputs
                    )
                ),
            ),
            (
                2,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "scope name")),
                                (
                                    1,
                                    k1.DatumVariant(
                                        0 if item.parent is None else 1,
                                        k1.UNIT
                                        if item.parent is None
                                        else _symbol(item.parent, "parent scope"),
                                    ),
                                ),
                                (
                                    2,
                                    k1.DatumVariant(
                                        0 if item.open_before is None else 1,
                                        k1.UNIT
                                        if item.open_before is None
                                        else _symbol(item.open_before, "scope opening"),
                                    ),
                                ),
                            )
                        )
                        for item in core.scopes
                    )
                ),
            ),
            (
                3,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "occurrence name")),
                                (1, k1.Symbol(item.kind.value)),
                                (2, _symbol(item.scope, "occurrence scope")),
                                (
                                    3,
                                    k1.DatumSeq(
                                        tuple(_ref_datum(ref) for ref in item.dependencies)
                                    ),
                                ),
                                (4, _predicate_datum(item.guard)),
                                (
                                    5,
                                    k1.DatumVariant(
                                        0 if item.verifier_rule is None else 1,
                                        k1.UNIT
                                        if item.verifier_rule is None
                                        else k1.DatumRecord(
                                            (
                                                (
                                                    0,
                                                    k1.Symbol(item.verifier_rule.kind.value),
                                                ),
                                                (
                                                    1,
                                                    k1.DatumSeq(
                                                        tuple(
                                                            k1.Nat(value)
                                                            for value in item.verifier_rule.parameters
                                                        )
                                                    ),
                                                ),
                                            )
                                        ),
                                    ),
                                ),
                                (
                                    6,
                                    k1.DatumVariant(
                                        0 if item.challenge_domain is None else 1,
                                        k1.UNIT
                                        if item.challenge_domain is None
                                        else k1.Nat(item.challenge_domain.modulus),
                                    ),
                                ),
                                (
                                    7,
                                    k1.DatumVariant(
                                        0 if item.oracle_name is None else 1,
                                        k1.UNIT
                                        if item.oracle_name is None
                                        else _symbol(item.oracle_name, "oracle name"),
                                    ),
                                ),
                                (
                                    8,
                                    k1.DatumVariant(
                                        0 if item.check_predicate is None else 1,
                                        k1.UNIT
                                        if item.check_predicate is None
                                        else _predicate_datum(item.check_predicate),
                                    ),
                                ),
                                (9, k1.Symbol(item.prover_value_sort.value)),
                            )
                        )
                        for item in core.schedule
                    )
                ),
            ),
            (4, k1.DatumSeq(tuple(_symbol(item, "extension") for item in core.extensions))),
            (5, k1.DatumSeq(tuple(_symbol(item, "claim") for item in core.initial_claims))),
            (
                6,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(step.name, "reduction name")),
                                (1, _symbol(step.at_occurrence, "reduction occurrence")),
                                (2, _symbol(step.scope, "reduction scope")),
                                (
                                    3,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(claim, "input claim")
                                            for claim in step.input_claims
                                        )
                                    ),
                                ),
                                (
                                    4,
                                    k1.DatumSeq(
                                        tuple(_ref_datum(ref) for ref in step.side_inputs)
                                    ),
                                ),
                                (
                                    5,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(challenge, "required challenge")
                                            for challenge in step.required_challenges
                                        )
                                    ),
                                ),
                                (
                                    6,
                                    k1.DatumSeq(
                                        tuple(
                                            k1.DatumRecord(
                                                (
                                                    (
                                                        0,
                                                        _symbol(
                                                            required.publication,
                                                            "required publication",
                                                        ),
                                                    ),
                                                    (
                                                        1,
                                                        k1.DatumVariant(
                                                            0,
                                                            k1.UNIT,
                                                        )
                                                        if required.next_challenge is None
                                                        else k1.DatumVariant(
                                                            1,
                                                            _symbol(
                                                                required.next_challenge,
                                                                "publication challenge",
                                                            ),
                                                        ),
                                                    ),
                                                )
                                            )
                                            for required in step.required_publications
                                        )
                                    ),
                                ),
                                (
                                    7,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(claim, "output claim")
                                            for claim in step.output_claims
                                        )
                                    ),
                                ),
                            )
                        )
                        for step in core.reductions
                    )
                ),
            ),
            (
                7,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(use.claim, "consumed claim")),
                                (1, _symbol(use.consumer, "claim consumer")),
                            )
                        )
                        for use in core.claim_uses
                    )
                ),
            ),
        )
    )
    return k1.encode_datum(datum)


def _profiled_identity(
    subject_kind: str,
    profile: object,
    encoded_domain_body: bytes,
) -> object:
    if type(profile) is not k1.SemanticLanguageProfile:
        raise ModelError("semantic identity needs one exact language profile")
    return k1.profiled_content_id(
        subject_kind,
        profile.identity,
        k1.decode_datum(encoded_domain_body),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def core_id(
    core: Core,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    return _profiled_identity(
        "pir.interactive-core",
        profiles.interaction,
        core_body(core),
    )


def invocation_body(core: Core, invocation: Invocation) -> bytes:
    values = admit_invocation(core, invocation)
    datum = k1.DatumRecord(
        (
            (
                0,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            ((0, _symbol(item.name, "input name")), (1, _datum(values[item.name])))
                        )
                        for item in core.inputs
                    )
                ),
            ),
        )
    )
    return k1.encode_datum(datum)


def invocation_id(
    core: Core,
    invocation: Invocation,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    return _profiled_identity(
        "pir.invocation",
        profiles.interaction,
        invocation_body(core, invocation),
    )


# ---------------------------------------------------------------------------
# Structural admission
# ---------------------------------------------------------------------------


KNOWN_EXTENSIONS = frozenset({"native-oracle-v0"})


def _bounded_unique(items: tuple[str, ...], limit: int, what: str) -> None:
    if len(items) > limit:
        raise AdmissionError(f"{what} exceeds the finite bound {limit}")
    if len(set(items)) != len(items):
        raise AdmissionError(f"{what} must be unique")
    for item in items:
        _symbol(item, what)


def _sort_accepts(value: Value, expected: ValueSort) -> bool:
    return {
        ValueSort.BYTES: type(value) is bytes,
        ValueSort.NAT: type(value) is int and value >= 0,
        ValueSort.BOOL: type(value) is bool,
        ValueSort.ORACLE: type(value) is OracleObject,
    }[expected]


def _validate_predicate(
    predicate: Predicate,
    available: set[ValueRef],
    sorts: Mapping[ValueRef, ValueSort],
) -> None:
    if type(predicate) is not Predicate or type(predicate.kind) is not PredicateKind:
        raise AdmissionError("guards/checks must use an exact bounded predicate")
    if len(predicate.refs) > MAX_DEPENDENCIES:
        raise AdmissionError("predicate dependency bound exceeded")
    if type(predicate.refs) is not tuple or type(predicate.parameters) is not tuple:
        raise AdmissionError("predicate aggregates must be immutable tuples")
    for ref in predicate.refs:
        _validate_ref(ref)
    if any(ref not in available for ref in predicate.refs):
        raise AdmissionError("predicate references a value outside its exact prefix")
    expected = {
        PredicateKind.ALWAYS: (0, 0),
        PredicateKind.NEVER: (0, 0),
        PredicateKind.BOOL: (1, 0),
        PredicateKind.BYTES_EQUAL: (2, 0),
        PredicateKind.SCHNORR: (6, 1),
        PredicateKind.LEADING_ZERO_BITS: (1, 1),
    }[predicate.kind]
    if len(predicate.refs) != expected[0] or len(predicate.parameters) != expected[1]:
        raise AdmissionError("predicate arity does not match its frozen fixture law")
    if any(type(item) is not int or item < 0 for item in predicate.parameters):
        raise AdmissionError("predicate parameters must be nonnegative exact integers")
    if predicate.kind is PredicateKind.SCHNORR and predicate.parameters[0] <= 1:
        raise AdmissionError("Schnorr fixture order must exceed one")
    if (
        predicate.kind is PredicateKind.LEADING_ZERO_BITS
        and predicate.parameters[0] > 256
    ):
        raise AdmissionError("grinding fixture work factor exceeds SHA-256 width")
    expected_sorts = {
        PredicateKind.ALWAYS: (),
        PredicateKind.NEVER: (),
        PredicateKind.BOOL: (ValueSort.BOOL,),
        PredicateKind.BYTES_EQUAL: (ValueSort.BYTES, ValueSort.BYTES),
        PredicateKind.SCHNORR: (ValueSort.NAT,) * 6,
        PredicateKind.LEADING_ZERO_BITS: (ValueSort.BYTES,),
    }[predicate.kind]
    if tuple(sorts[ref] for ref in predicate.refs) != expected_sorts:
        raise AdmissionError("predicate reference sorts do not match its frozen law")


def _occurrence_sort(
    occurrence: Occurrence,
    sorts: Mapping[ValueRef, ValueSort],
) -> ValueSort:
    if occurrence.kind is OccurrenceKind.PROVER_MESSAGE:
        return occurrence.prover_value_sort
    if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
        assert occurrence.verifier_rule is not None
        if occurrence.verifier_rule.kind is VerifierRuleKind.COPY:
            return sorts[occurrence.dependencies[0]]
        if occurrence.verifier_rule.kind is VerifierRuleKind.SHA256:
            if any(sorts[ref] is not ValueSort.BYTES for ref in occurrence.dependencies):
                raise AdmissionError("SHA-256 verifier inputs must be byte strings")
            return ValueSort.BYTES
        return ValueSort.NAT
    return {
        OccurrenceKind.CHALLENGE: ValueSort.NAT,
        OccurrenceKind.CHECK: ValueSort.BOOL,
        OccurrenceKind.TERMINAL: ValueSort.BOOL,
        OccurrenceKind.ORACLE_PUBLISH: ValueSort.ORACLE,
        OccurrenceKind.ORACLE_QUERY: ValueSort.NAT,
        OccurrenceKind.ORACLE_ANSWER: ValueSort.BYTES,
    }[occurrence.kind]


def admit_core(core: Core) -> None:
    if type(core) is not Core:
        raise AdmissionError("Core must have the exact immutable carrier")
    if (
        type(core.inputs) is not tuple
        or type(core.scopes) is not tuple
        or type(core.schedule) is not tuple
        or type(core.extensions) is not tuple
        or type(core.initial_claims) is not tuple
        or type(core.reductions) is not tuple
        or type(core.claim_uses) is not tuple
    ):
        raise AdmissionError("Core aggregates must be immutable tuples")

    input_names = tuple(item.name for item in core.inputs)
    _bounded_unique(input_names, MAX_INPUTS, "input names")
    if any(
        type(item) is not InputDecl
        or type(item.role) is not InputRole
        or type(item.value_sort) is not ValueSort
        or item.value_sort is ValueSort.ORACLE
        for item in core.inputs
    ):
        raise AdmissionError("input declarations have the wrong exact shape")

    scope_names = tuple(item.name for item in core.scopes)
    _bounded_unique(scope_names, MAX_SCOPES, "scope names")
    if not core.scopes or core.scopes[0] != ScopeDecl("root", None, None):
        raise AdmissionError("the first scope must be the initially open root scope")
    occurrence_names = tuple(item.name for item in core.schedule)
    _bounded_unique(occurrence_names, MAX_OCCURRENCES, "occurrence names")
    occurrence_index = {name: index for index, name in enumerate(occurrence_names)}
    scope_index = {name: index for index, name in enumerate(scope_names)}
    for index, scope in enumerate(core.scopes):
        if type(scope) is not ScopeDecl:
            raise AdmissionError("scope declarations have the wrong exact shape")
        if index == 0:
            continue
        if scope.parent not in scope_index or scope_index[scope.parent] >= index:
            raise AdmissionError("nested scope parent must precede the child")
        if scope.open_before not in occurrence_index:
            raise AdmissionError("nested scope must open before a named occurrence")
        parent = core.scopes[scope_index[scope.parent]]
        parent_open = -1 if parent.open_before is None else occurrence_index[parent.open_before]
        if occurrence_index[scope.open_before] < parent_open:
            raise AdmissionError("nested scope cannot open before its parent")
    if any(item.scope not in scope_index for item in core.inputs):
        raise AdmissionError("every input must belong to a declared scope")

    if not core.schedule:
        raise AdmissionError("a Core needs a nonempty exact total schedule")
    if sum(item.kind is OccurrenceKind.TERMINAL for item in core.schedule) != 1:
        raise AdmissionError("a Core needs exactly one terminal occurrence")
    if core.schedule[-1].kind is not OccurrenceKind.TERMINAL:
        raise AdmissionError("the unique terminal must close the total schedule")

    inputs_by_scope: dict[str, tuple[ValueRef, ...]] = {
        scope: tuple(
            ValueRef.input(item.name) for item in core.inputs if item.scope == scope
        )
        for scope in scope_names
    }
    available: set[ValueRef] = set(inputs_by_scope["root"])
    input_by_name = {item.name: item for item in core.inputs}
    sorts: dict[ValueRef, ValueSort] = {
        ref: input_by_name[ref.name].value_sort for ref in available
    }
    scopes_opening_at: dict[int, tuple[str, ...]] = {}
    for scope in core.scopes[1:]:
        assert scope.open_before is not None
        opening_index = occurrence_index[scope.open_before]
        scopes_opening_at[opening_index] = (
            *scopes_opening_at.get(opening_index, ()),
            scope.name,
        )
    published: dict[str, int] = {}
    queries: dict[str, tuple[str, int]] = {}
    answered_queries: set[str] = set()
    oracle_seen = False
    for index, occurrence in enumerate(core.schedule):
        for opening_scope in scopes_opening_at.get(index, ()):
            available.update(inputs_by_scope[opening_scope])
            sorts.update(
                {
                    ref: input_by_name[ref.name].value_sort
                    for ref in inputs_by_scope[opening_scope]
                }
            )
        if type(occurrence) is not Occurrence or type(occurrence.kind) is not OccurrenceKind:
            raise AdmissionError("occurrences have the wrong exact shape")
        _symbol(occurrence.name, "occurrence name")
        if occurrence.scope not in scope_index:
            raise AdmissionError("occurrence names an unknown scope")
        scope = core.scopes[scope_index[occurrence.scope]]
        open_index = -1 if scope.open_before is None else occurrence_index[scope.open_before]
        if index < open_index:
            raise AdmissionError("occurrence precedes activation of its scope")
        if type(occurrence.prover_value_sort) is not ValueSort:
            raise AdmissionError("prover value sort has the wrong exact shape")
        if (
            occurrence.kind is not OccurrenceKind.PROVER_MESSAGE
            and occurrence.prover_value_sort is not ValueSort.BYTES
        ):
            raise AdmissionError("only prover messages may select a prover value sort")
        if type(occurrence.dependencies) is not tuple or len(occurrence.dependencies) > MAX_DEPENDENCIES:
            raise AdmissionError("occurrence dependencies exceed their exact bound")
        for ref in occurrence.dependencies:
            _validate_ref(ref)
        if len(set(occurrence.dependencies)) != len(occurrence.dependencies):
            raise AdmissionError("occurrence dependencies must be unique")
        if any(ref not in available for ref in occurrence.dependencies):
            raise AdmissionError("occurrence dependency is not in the exact prior prefix")
        if (
            occurrence.kind is OccurrenceKind.PROVER_MESSAGE
            and occurrence.dependencies
        ):
            raise AdmissionError(
                "prover messages have no authored dependency field"
            )
        _validate_predicate(occurrence.guard, available, sorts)

        if occurrence.kind is OccurrenceKind.CHALLENGE:
            if type(occurrence.challenge_domain) is not ChallengeDomain:
                raise AdmissionError("challenge occurrence needs an exact domain")
            if type(occurrence.challenge_domain.modulus) is not int or occurrence.challenge_domain.modulus <= 1:
                raise AdmissionError("challenge modulus must be an exact integer above one")
        elif occurrence.challenge_domain is not None:
            raise AdmissionError("only a challenge may carry a challenge domain")

        if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
            if (
                type(occurrence.verifier_rule) is not VerifierRule
                or type(occurrence.verifier_rule.kind) is not VerifierRuleKind
                or type(occurrence.verifier_rule.parameters) is not tuple
                or any(
                    type(item) is not int or item < 0
                    for item in occurrence.verifier_rule.parameters
                )
            ):
                raise AdmissionError("verifier message needs one deterministic rule")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.CONSTANT_INT
                and (
                    occurrence.dependencies
                    or len(occurrence.verifier_rule.parameters) != 1
                )
            ):
                raise AdmissionError("constant verifier rule has exact arity zero-to-one")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.COPY
                and (
                    len(occurrence.dependencies) != 1
                    or occurrence.verifier_rule.parameters
                )
            ):
                raise AdmissionError("copy verifier rule has exact arity one-to-one")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.SHA256
                and occurrence.verifier_rule.parameters
            ):
                raise AdmissionError("SHA-256 verifier rule carries no parameters")
        elif occurrence.verifier_rule is not None:
            raise AdmissionError("only verifier messages may carry a verifier rule")

        if occurrence.kind is OccurrenceKind.CHECK:
            if occurrence.guard.kind is not PredicateKind.ALWAYS:
                raise AdmissionError("checks use dependencies as their predicate, not a path guard")
            if len(occurrence.dependencies) == 0:
                raise AdmissionError("check needs dependencies")
            if occurrence.check_predicate is None:
                raise AdmissionError("check needs an identity-bearing Bool predicate")
            _validate_predicate(occurrence.check_predicate, available, sorts)
            if occurrence.check_predicate.refs != occurrence.dependencies:
                raise AdmissionError("check predicate must use the exact dependency tuple")
        elif occurrence.check_predicate is not None:
            raise AdmissionError("only a check may carry a check predicate")

        if occurrence.kind in {
            OccurrenceKind.ORACLE_PUBLISH,
            OccurrenceKind.ORACLE_QUERY,
            OccurrenceKind.ORACLE_ANSWER,
        }:
            oracle_seen = True
            if occurrence.oracle_name is None:
                raise AdmissionError("oracle occurrence must name its oracle")
            _symbol(occurrence.oracle_name, "oracle name")
        elif occurrence.oracle_name is not None:
            raise AdmissionError("non-oracle occurrence cannot name an oracle")

        if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH:
            assert occurrence.oracle_name is not None
            if occurrence.oracle_name in published:
                raise AdmissionError("an immutable native oracle is published exactly once")
            published[occurrence.oracle_name] = index
        elif occurrence.kind is OccurrenceKind.ORACLE_QUERY:
            assert occurrence.oracle_name is not None
            if occurrence.oracle_name not in published or published[occurrence.oracle_name] >= index:
                raise AdmissionError("native oracle query must follow publication")
            if len(occurrence.dependencies) != 1:
                raise AdmissionError("native oracle query has exactly one index source")
            if sorts[occurrence.dependencies[0]] is not ValueSort.NAT:
                raise AdmissionError("native oracle query index source must have Nat sort")
            queries[occurrence.name] = (occurrence.oracle_name, index)
        elif occurrence.kind is OccurrenceKind.ORACLE_ANSWER:
            assert occurrence.oracle_name is not None
            if len(occurrence.dependencies) != 1:
                raise AdmissionError("native oracle answer names exactly one query")
            ref = occurrence.dependencies[0]
            if ref.kind is not RefKind.OCCURRENCE or ref.name not in queries:
                raise AdmissionError("native oracle answer must reference a prior query")
            query_oracle, _ = queries[ref.name]
            if query_oracle != occurrence.oracle_name or ref.name in answered_queries:
                raise AdmissionError("native oracle answer mismatches or repeats its query")
            answered_queries.add(ref.name)

        occurrence_ref = ValueRef.occurrence(occurrence.name)
        available.add(occurrence_ref)
        sorts[occurrence_ref] = _occurrence_sort(occurrence, sorts)

    if set(queries) != answered_queries:
        raise AdmissionError("every native oracle query needs exactly one answer")
    extension_names = tuple(core.extensions)
    _bounded_unique(extension_names, 16, "extensions")
    unknown = set(extension_names) - KNOWN_EXTENSIONS
    if unknown:
        raise AdmissionError(f"unsupported extension: {sorted(unknown)!r}")
    if oracle_seen != ("native-oracle-v0" in core.extensions):
        raise AdmissionError("native oracle events and extension declaration must agree")

    claim_names = tuple(core.initial_claims)
    _bounded_unique(claim_names, MAX_CLAIMS, "initial claims")
    live = set(claim_names)
    produced = set(claim_names)
    reduction_names = tuple(step.name for step in core.reductions)
    _bounded_unique(reduction_names, MAX_CLAIMS, "reduction names")
    if any(type(use) is not ClaimConsumerUse for use in core.claim_uses):
        raise AdmissionError("claim consumer uses have the wrong exact shape")
    uses_by_consumer: dict[str, list[str]] = {}
    for use in core.claim_uses:
        _symbol(use.claim, "consumed claim")
        _symbol(use.consumer, "claim consumer")
        uses_by_consumer.setdefault(use.consumer, []).append(use.claim)
    if len(core.claim_uses) != len({use.claim for use in core.claim_uses}):
        raise AdmissionError("claim use must be linear")
    if any(len(set(items)) != len(items) for items in uses_by_consumer.values()):
        raise AdmissionError("claim use must be linear")

    def ref_available_before(ref: ValueRef, step_index: int) -> bool:
        if ref.kind is RefKind.OCCURRENCE:
            return ref.name in occurrence_index and occurrence_index[ref.name] < step_index
        item = input_by_name.get(ref.name)
        if item is None:
            return False
        declared_scope = core.scopes[scope_index[item.scope]]
        opening = -1 if declared_scope.open_before is None else occurrence_index[declared_scope.open_before]
        return opening <= step_index

    previous_step_index = -1
    oracle_publication_by_name = {
        item.oracle_name: item.name
        for item in core.schedule
        if item.kind is OccurrenceKind.ORACLE_PUBLISH
    }

    def publication_dependencies(ref: ValueRef) -> set[str]:
        """Derive prover publications in one finite value-dependency closure."""

        pending = [ref]
        seen: set[ValueRef] = set()
        result: set[str] = set()
        while pending:
            current = pending.pop()
            if current in seen or current.kind is not RefKind.OCCURRENCE:
                continue
            seen.add(current)
            if current.name not in occurrence_index:
                continue
            source = core.schedule[occurrence_index[current.name]]
            if source.kind in {
                OccurrenceKind.PROVER_MESSAGE,
                OccurrenceKind.ORACLE_PUBLISH,
            }:
                result.add(source.name)
            if source.kind in {
                OccurrenceKind.ORACLE_QUERY,
                OccurrenceKind.ORACLE_ANSWER,
            }:
                publication = oracle_publication_by_name.get(source.oracle_name)
                if publication is not None:
                    result.add(publication)
            pending.extend(source.dependencies)
        return result

    for step in core.reductions:
        if type(step) is not ReductionDecl or step.at_occurrence not in occurrence_index:
            raise AdmissionError("reduction declaration names an unknown occurrence")
        step_index = occurrence_index[step.at_occurrence]
        if step_index < previous_step_index:
            raise AdmissionError("reduction declarations must follow schedule order")
        previous_step_index = step_index
        if step.scope not in scope_index or core.schedule[step_index].scope != step.scope:
            raise AdmissionError("reduction scope must equal its application scope")
        aggregates = (
            step.input_claims,
            step.side_inputs,
            step.required_challenges,
            step.required_publications,
            step.output_claims,
        )
        if any(type(items) is not tuple for items in aggregates):
            raise AdmissionError("reduction aggregates must be immutable tuples")
        if len(set(step.input_claims)) != len(step.input_claims) or len(set(step.output_claims)) != len(step.output_claims):
            raise AdmissionError("reduction claims cannot repeat")
        if tuple(uses_by_consumer.pop(step.name, ())) != step.input_claims:
            raise AdmissionError("reduction input claims need exact consumer uses")
        if any(name not in live for name in step.input_claims):
            raise AdmissionError("claim use must be linear and presently live")
        if any(name in produced for name in step.output_claims):
            raise AdmissionError("claim names are single-assignment")
        for ref in step.side_inputs:
            _validate_ref(ref)
            if not ref_available_before(ref, step_index):
                raise AdmissionError("reduction side input is not available at application")
        if len(set(step.required_challenges)) != len(step.required_challenges):
            raise AdmissionError("required challenges must be unique")
        for challenge in step.required_challenges:
            if challenge not in occurrence_index or core.schedule[occurrence_index[challenge]].kind is not OccurrenceKind.CHALLENGE:
                raise AdmissionError("reduction required challenge is not a challenge occurrence")
            if occurrence_index[challenge] >= step_index:
                raise AdmissionError("reduction required challenge must precede application")
        publication_names = tuple(
            required.publication for required in step.required_publications
        )
        if len(set(publication_names)) != len(publication_names):
            raise AdmissionError("required publication occurrences must be unique")
        if tuple(
            sorted(publication_names, key=occurrence_index.__getitem__)
        ) != publication_names:
            raise AdmissionError("required publications must follow occurrence order")
        for required in step.required_publications:
            if type(required) is not RequiredPublication:
                raise AdmissionError("required publication has the wrong exact shape")
            if required.publication not in occurrence_index:
                raise AdmissionError("required publication names an unknown occurrence")
            publication = core.schedule[occurrence_index[required.publication]]
            if publication.kind not in {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.ORACLE_PUBLISH}:
                raise AdmissionError("required publication must be prover-controlled")
            publication_index = occurrence_index[required.publication]
            if publication_index >= step_index:
                raise AdmissionError("required publication must precede reduction application")
            following = tuple(
                challenge
                for challenge in step.required_challenges
                if occurrence_index[challenge] > publication_index
            )
            expected_next = min(
                following,
                key=occurrence_index.__getitem__,
                default=None,
            )
            if required.next_challenge != expected_next:
                raise AdmissionError(
                    "required publication must name its least following challenge"
                )
        dependency_publications: set[str] = set()
        for ref in step.side_inputs:
            dependency_publications.update(publication_dependencies(ref))
        if not dependency_publications.issubset(set(publication_names)):
            raise AdmissionError(
                "reduction side-input publication closure is incomplete"
            )
        live.difference_update(step.input_claims)
        live.update(step.output_claims)
        produced.update(step.output_claims)

    terminal_name = core.schedule[-1].name
    terminal_uses = uses_by_consumer.pop(terminal_name, [])
    if uses_by_consumer:
        raise AdmissionError("claim use names an unknown consumer")
    if len(terminal_uses) != len(set(terminal_uses)) or set(terminal_uses) != live:
        raise AdmissionError("terminal closure must consume every live claim exactly once")


def is_public_coin_eligible(core: Core) -> bool:
    """Compute dependency-sensitive private influence to verifier consumers."""

    admit_core(core)
    tainted = {
        ValueRef.input(item.name)
        for item in core.inputs
        if item.role is InputRole.VERIFIER_PRIVATE
    }
    checks: list[ValueRef] = []
    reductions_at: dict[str, list[ReductionDecl]] = {}
    for reduction in core.reductions:
        reductions_at.setdefault(reduction.at_occurrence, []).append(reduction)
    for item in core.schedule:
        sources = set(item.dependencies) | set(item.guard.refs)
        if item.check_predicate is not None:
            sources.update(item.check_predicate.refs)
        if item.kind is OccurrenceKind.TERMINAL:
            sources.update(checks)
        consumer = item.kind in {
            OccurrenceKind.PROVER_MESSAGE,
            OccurrenceKind.VERIFIER_MESSAGE,
            OccurrenceKind.CHALLENGE,
            OccurrenceKind.ORACLE_PUBLISH,
            OccurrenceKind.ORACLE_QUERY,
            OccurrenceKind.ORACLE_ANSWER,
            OccurrenceKind.CHECK,
            OccurrenceKind.TERMINAL,
        }
        if consumer and sources & tainted:
            return False
        output = ValueRef.occurrence(item.name)
        if sources & tainted:
            tainted.add(output)
        if item.kind is OccurrenceKind.CHECK:
            checks.append(output)
        for reduction in reductions_at.get(item.name, ()):
            reduction_sources = set(reduction.side_inputs)
            reduction_sources.update(
                ValueRef.occurrence(name) for name in reduction.required_challenges
            )
            reduction_sources.update(
                ValueRef.occurrence(required.publication)
                for required in reduction.required_publications
            )
            reduction_sources.add(output)
            if reduction_sources & tainted:
                return False
    return True


def admit_invocation(core: Core, invocation: Invocation) -> Mapping[str, Value]:
    admit_core(core)
    if type(invocation) is not Invocation or not isinstance(invocation.values, Mapping):
        raise InvocationError("invocation has the wrong finite mapping shape")
    expected = tuple(item.name for item in core.inputs)
    if set(invocation.values) != set(expected):
        raise InvocationError("invocation must provide exactly every declared input")
    copied: dict[str, Value] = {}
    declarations = {item.name: item for item in core.inputs}
    for name in expected:
        value = invocation.values[name]
        _datum(value)
        if type(value) is OracleObject:
            raise InvocationError("native oracles are published, not invocation inputs")
        if not _sort_accepts(value, declarations[name].value_sort):
            raise InvocationError("invocation value does not match its declared sort")
        copied[name] = value
    return MappingProxyType(copied)


# ---------------------------------------------------------------------------
# Exact transcript construction and derived influence
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TranscriptConstruction:
    application_domain: bytes
    sample_bytes: int = 8
    max_attempts: int = 16
    state_bytes: int = 32
    version: str = "k2-sha256-duplex-fixture-v1"

    def admit(self) -> None:
        if type(self.application_domain) is not bytes or not self.application_domain:
            raise AdmissionError("transcript application domain must be nonempty bytes")
        if type(self.sample_bytes) is not int or not 1 <= self.sample_bytes <= 32:
            raise AdmissionError("sample width must be in 1..32 octets")
        if type(self.max_attempts) is not int or not 1 <= self.max_attempts <= 256:
            raise AdmissionError("sampling attempt bound must be in 1..256")
        if self.state_bytes != 32 or self.version != "k2-sha256-duplex-fixture-v1":
            raise AdmissionError("unsupported exact transcript transition suite")


@dataclass(frozen=True)
class ChallengeSample:
    value: int
    state: bytes
    attempts: int
    namespaces: tuple[bytes, ...]


INITIAL_TRANSCRIPT_STATE = hashlib.sha256(b"zkc/k2/initial-state/v1").digest()


def construction_body(
    core: Core,
    construction: TranscriptConstruction,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> bytes:
    admit_core(core)
    construction.admit()
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, k1.Symbol("k2.transcript-construction.v1")),
                (
                    1,
                    k1.BytesValue(
                        core_id(core, profiles=profiles).internal_reference()
                    ),
                ),
                (2, k1.BytesValue(INITIAL_TRANSCRIPT_STATE)),
                (3, k1.BytesValue(construction.application_domain)),
                (4, k1.Nat(construction.sample_bytes)),
                (5, k1.Nat(construction.max_attempts)),
                (6, k1.Nat(construction.state_bytes)),
                (7, k1.Symbol(construction.version)),
                (8, k1.Symbol("init=fixed-state-then-core-construction-domain-frames")),
                (9, k1.Symbol("absorb=SHA256(frame(absorb)||frame(state)||frame(atom)||frame(payload))")),
                (10, k1.Symbol("squeeze=SHA256(frame(squeeze)||frame(state)||frame(draw-namespace)||frame(requested-bytes))[:requested-bytes]")),
                (11, k1.Symbol("advance=SHA256(frame(advance)||frame(state)||frame(draw-namespace)||frame(requested-bytes)||frame(block))")),
                (12, k1.Symbol("decode=big-endian-rejection-into-[0,modulus)")),
            )
        )
    )


def construction_id(
    core: Core,
    construction: TranscriptConstruction,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    return _profiled_identity(
        "pir.transcript-construction",
        profiles.transcript_fs,
        construction_body(core, construction, profiles=profiles),
    )


def _content_ref_datum(identifier: object, expected_kind: str) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise ModelError("semantic reference must be one exact K1 TypedContentId")
    identifier.__post_init__()
    if (
        identifier.semantic_regime != k1.SEMANTIC_REGIME_ID
        or identifier.subject_kind != expected_kind
    ):
        raise ModelError("semantic reference has the wrong regime or subject kind")
    return k1.BytesValue(identifier.internal_reference())


def protocol_body(
    core: Core,
    construction: TranscriptConstruction | None,
    interpretation: ChallengeInterpretation,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    """Form the exact bounded Protocol domain body."""

    admit_core(core)
    if interpretation is ChallengeInterpretation.FRESH:
        if construction is not None:
            raise AdmissionError("Fresh Protocol does not carry a construction")
        interpretation_body = k1.DatumVariant(0, k1.UNIT)
    elif interpretation is ChallengeInterpretation.FIAT_SHAMIR:
        if construction is None:
            raise AdmissionError("Fiat--Shamir Protocol requires a construction")
        construction.admit()
        if not is_public_coin_eligible(core):
            raise AdmissionError("Fiat--Shamir Protocol requires public-coin eligibility")
        interpretation_body = k1.DatumVariant(
            1,
            _content_ref_datum(
                construction_id(core, construction, profiles=profiles),
                "pir.transcript-construction",
            ),
        )
    else:
        raise AdmissionError("unsupported challenge interpretation")
    return k1.DatumRecord(
        (
            (
                0,
                _content_ref_datum(
                    core_id(core, profiles=profiles),
                    "pir.interactive-core",
                ),
            ),
            (1, interpretation_body),
        )
    )


def protocol_id(
    core: Core,
    construction: TranscriptConstruction | None,
    interpretation: ChallengeInterpretation,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    """Form the exact bounded Protocol identity used by every downstream lane."""

    profile = (
        profiles.interaction
        if interpretation is ChallengeInterpretation.FRESH
        else profiles.transcript_fs
    )
    return k1.profiled_content_id(
        "pir.protocol",
        profile.identity,
        protocol_body(
            core,
            construction,
            interpretation,
            profiles=profiles,
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


# ---------------------------------------------------------------------------
# Exact owner-issued static and public-setup views
# ---------------------------------------------------------------------------


class StaticViewKind(str, Enum):
    PUBLIC_BINDING = "public-binding-view"
    STRATEGY_DECISION = "strategy-decision-view"
    PUBLIC_COIN = "public-coin-view"
    EFFECT = "effect-view"
    CLAIM_REDUCTION = "claim-reduction-view"
    EXECUTION = "execution-view"
    TRANSCRIPT_DECLARATION = "transcript-declaration-view"
    REQUIRED_INFLUENCE = "required-influence-view"
    CHALLENGE_TRANSITION = "challenge-transition-view"
    FS_CONSTRUCTION = "fs-construction-view"


class StaticViewOwnerKind(str, Enum):
    CORE = "core"
    PROTOCOL = "protocol"
    CONSTRUCTION = "construction"
    FS_RESULT = "fs-result"


class StaticViewField(str, Enum):
    PB_CORE_ID = "public-binding.core-id"
    PB_SCOPE_OPENINGS = "public-binding.scope-openings"
    PB_BINDINGS = "public-binding.bindings"
    SD_CORE_ID = "strategy-decision.core-id"
    SD_DECISION_POINTS = "strategy-decision.decision-points"
    SD_PROVER_VIEW_FORMATION = "strategy-decision.prover-view-formation"
    SD_GUARANTEED_READS = "strategy-decision.guaranteed-reads"
    SD_LEGAL_MOVE_TYPES = "strategy-decision.legal-move-types"
    PC_CORE_ID = "public-coin.core-id"
    PC_ELIGIBILITY = "public-coin.eligibility"
    PC_PRIVATE_CLOSURE = "public-coin.verifier-private-closure"
    PC_CHALLENGES = "public-coin.challenges"
    EF_CORE_ID = "effect.core-id"
    EF_OCCURRENCE_SCHEDULE = "effect.occurrence-schedule"
    EF_VALUE_PRODUCER_GRAPH = "effect.value-producer-graph"
    EF_MESSAGES = "effect.messages"
    EF_ORACLES = "effect.oracles"
    EF_CHECKS = "effect.checks"
    EF_TERMINALS = "effect.terminals"
    EF_EXTENSIONS = "effect.extensions"
    CR_CORE_ID = "claim-reduction.core-id"
    CR_CLAIMS = "claim-reduction.claims"
    CR_REDUCTIONS = "claim-reduction.reductions"
    CR_TERMINAL_DISPOSITIONS = "claim-reduction.terminal-dispositions"
    EX_PROTOCOL_ID = "execution.protocol-id"
    EX_CORE_ID = "execution.core-id"
    EX_INTERPRETATION = "execution.interpretation"
    EX_VISIBLE_HISTORY = "execution.visible-history-law"
    EX_RESOLVER = "execution.resolver-coordinates"
    EX_GENERATION = "execution.generated-execution-law"
    EX_RUN_RECORD = "execution.run-record-schema"
    EX_REPLAY = "execution.replay-law"
    EX_RELATION_RUN = "execution.relation-run-view-law"
    TD_CONSTRUCTION_ID = "transcript-declaration.construction-id"
    TD_CORE_ID = "transcript-declaration.core-id"
    TD_ALGORITHMS = "transcript-declaration.algorithms"
    TD_APPLICATION_DOMAIN = "transcript-declaration.application-domain"
    TD_FRAME_SCHEDULE = "transcript-declaration.frame-schedule"
    RI_CONSTRUCTION_ID = "required-influence.construction-id"
    RI_CORE_ID = "required-influence.core-id"
    RI_REQUIREMENTS = "required-influence.requirements"
    RI_PREFIX_LAW = "required-influence.prefix-law"
    CT_CONSTRUCTION_ID = "challenge-transition.construction-id"
    CT_CORE_ID = "challenge-transition.core-id"
    CT_NAMESPACE = "challenge-transition.namespace"
    CT_SAMPLER = "challenge-transition.sampler"
    CT_RETRY_FAILURE = "challenge-transition.retry-failure"
    FS_RESULT_REF = "fs-construction.result-ref"
    FS_RESULT_SCHEMA = "fs-construction.result-schema"
    FS_SOURCE_PROTOCOL = "fs-construction.source-protocol"
    FS_TARGET_PROTOCOL = "fs-construction.target-protocol"
    FS_SHARED_CORE = "fs-construction.shared-core"
    FS_CONSTRUCTION_ID = "fs-construction.construction-id"
    FS_MAPS = "fs-construction.maps"
    FS_CONCLUSION = "fs-construction.conclusion"


_VIEW_FIELDS: Mapping[StaticViewKind, tuple[StaticViewField, ...]] = MappingProxyType(
    {
        StaticViewKind.PUBLIC_BINDING: (
            StaticViewField.PB_CORE_ID,
            StaticViewField.PB_SCOPE_OPENINGS,
            StaticViewField.PB_BINDINGS,
        ),
        StaticViewKind.STRATEGY_DECISION: (
            StaticViewField.SD_CORE_ID,
            StaticViewField.SD_DECISION_POINTS,
            StaticViewField.SD_PROVER_VIEW_FORMATION,
            StaticViewField.SD_GUARANTEED_READS,
            StaticViewField.SD_LEGAL_MOVE_TYPES,
        ),
        StaticViewKind.PUBLIC_COIN: (
            StaticViewField.PC_CORE_ID,
            StaticViewField.PC_ELIGIBILITY,
            StaticViewField.PC_PRIVATE_CLOSURE,
            StaticViewField.PC_CHALLENGES,
        ),
        StaticViewKind.EFFECT: (
            StaticViewField.EF_CORE_ID,
            StaticViewField.EF_OCCURRENCE_SCHEDULE,
            StaticViewField.EF_VALUE_PRODUCER_GRAPH,
            StaticViewField.EF_MESSAGES,
            StaticViewField.EF_ORACLES,
            StaticViewField.EF_CHECKS,
            StaticViewField.EF_TERMINALS,
            StaticViewField.EF_EXTENSIONS,
        ),
        StaticViewKind.CLAIM_REDUCTION: (
            StaticViewField.CR_CORE_ID,
            StaticViewField.CR_CLAIMS,
            StaticViewField.CR_REDUCTIONS,
            StaticViewField.CR_TERMINAL_DISPOSITIONS,
        ),
        StaticViewKind.EXECUTION: (
            StaticViewField.EX_PROTOCOL_ID,
            StaticViewField.EX_CORE_ID,
            StaticViewField.EX_INTERPRETATION,
            StaticViewField.EX_VISIBLE_HISTORY,
            StaticViewField.EX_RESOLVER,
            StaticViewField.EX_GENERATION,
            StaticViewField.EX_RUN_RECORD,
            StaticViewField.EX_REPLAY,
            StaticViewField.EX_RELATION_RUN,
        ),
        StaticViewKind.TRANSCRIPT_DECLARATION: (
            StaticViewField.TD_CONSTRUCTION_ID,
            StaticViewField.TD_CORE_ID,
            StaticViewField.TD_ALGORITHMS,
            StaticViewField.TD_APPLICATION_DOMAIN,
            StaticViewField.TD_FRAME_SCHEDULE,
        ),
        StaticViewKind.REQUIRED_INFLUENCE: (
            StaticViewField.RI_CONSTRUCTION_ID,
            StaticViewField.RI_CORE_ID,
            StaticViewField.RI_REQUIREMENTS,
            StaticViewField.RI_PREFIX_LAW,
        ),
        StaticViewKind.CHALLENGE_TRANSITION: (
            StaticViewField.CT_CONSTRUCTION_ID,
            StaticViewField.CT_CORE_ID,
            StaticViewField.CT_NAMESPACE,
            StaticViewField.CT_SAMPLER,
            StaticViewField.CT_RETRY_FAILURE,
        ),
        StaticViewKind.FS_CONSTRUCTION: (
            StaticViewField.FS_RESULT_REF,
            StaticViewField.FS_RESULT_SCHEMA,
            StaticViewField.FS_SOURCE_PROTOCOL,
            StaticViewField.FS_TARGET_PROTOCOL,
            StaticViewField.FS_SHARED_CORE,
            StaticViewField.FS_CONSTRUCTION_ID,
            StaticViewField.FS_MAPS,
            StaticViewField.FS_CONCLUSION,
        ),
    }
)
_FIELD_ORDER = MappingProxyType(
    {field: index for index, field in enumerate(StaticViewField)}
)


@dataclass(frozen=True)
class StaticViewCoordinate:
    owner_kind: StaticViewOwnerKind
    owner_id: object
    view_kind: StaticViewKind
    semantic_profile_id: object


@dataclass(frozen=True)
class StaticViewEntry:
    field: StaticViewField
    value: object


@dataclass(frozen=True)
class StaticViewProjection:
    coordinate: StaticViewCoordinate
    manifest: tuple[StaticViewField, ...]
    entries: tuple[StaticViewEntry, ...]


class StaticViewAtomicLeaf(str, Enum):
    """Closed leaf names exported by the bounded static-view resolvers."""

    CHALLENGE_OCCURRENCE = "challenge-occurrence"
    CHALLENGE_DOMAIN = "challenge-domain"


@dataclass(frozen=True)
class PIRStaticViewAtomicCoordinate:
    """One exact atomic leaf below an owner-qualified static-view entry.

    ``sequence_ordinal`` is local to the selected static-view field.  It is
    deliberately distinct from ``schedule_ordinal``, which is local to the
    owning Core schedule.  Consumers therefore cannot silently use a schedule
    position as an index into a filtered view field.
    """

    view_coordinate: StaticViewCoordinate
    field: StaticViewField
    sequence_ordinal: int
    schedule_ordinal: int
    occurrence_name: str
    leaf: StaticViewAtomicLeaf


@dataclass(frozen=True)
class PublicCoinChallengeProjection:
    """Exact occurrence and nominal-domain leaves for one public coin."""

    challenge_coordinate: PIRStaticViewAtomicCoordinate
    domain_coordinate: PIRStaticViewAtomicCoordinate
    challenge_domain: ChallengeDomain


class _NonTransferableAuthority:
    """Process-local bearer state: identity, not structural equality, matters."""

    __hash__ = None

    def __copy__(self) -> object:
        raise ModelError("live authority cannot be copied")

    def __deepcopy__(self, _memo: object) -> object:
        raise ModelError("live authority cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ModelError("live authority cannot be serialized")


def _any_content_ref(identifier: object, what: str) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise ModelError(f"{what} must be one exact typed content ID")
    identifier.__post_init__()
    if identifier.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise ModelError(f"{what} belongs to another semantic regime")
    return k1.BytesValue(identifier.internal_reference())


def _authority_id(profile: object, subject_kind: str, body: object) -> object:
    if type(profile) is not k1.SemanticLanguageProfile:
        raise ModelError("authority identity needs one exact semantic profile")
    return k1.profiled_content_id(
        subject_kind,
        profile.identity,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


class PIRSourceOwnerCompiler(str, Enum):
    """The closed PIR owner compiler selected for one source family."""

    INTERACTION = "interaction"
    CANONICAL_FRAMED = "canonical-framed"
    DUPLEX_SPONGE = "duplex-sponge"
    PUBLIC_SETUP = "public-setup"
    INTERFACE_PLAN = "interface-plan"


_CHECKER_CONTRACT_DECLARATIONS = MappingProxyType(
    {
        PIRSourceOwnerCompiler.CANONICAL_FRAMED: (
            ("pir.evaluator-signature", "canonical-framed-construction-check-v0"),
            ("pir.semantic-law", "canonical-framed-same-core-construction-v0"),
            ("pir.failure-schema", "canonical-framed-construction-defects-v0"),
        ),
        PIRSourceOwnerCompiler.DUPLEX_SPONGE: (
            ("pir.evaluator-signature", "duplex-sponge-construction-check-v0"),
            ("pir.semantic-law", "duplex-sponge-same-core-construction-v0"),
            ("pir.failure-schema", "duplex-sponge-construction-defects-v0"),
        ),
    }
)


class PIRSourceFamily(str, Enum):
    STATIC_VIEW = "StaticView"
    CHECKED_CONSTRUCTION = "CheckedConstruction"
    PUBLIC_SETUP_INVOCATION_VIEW = "PublicSetupInvocationView"
    INTERFACE_VIEW = "InterfaceView"
    CONFIDENTIAL_INITIAL_ORACLE = "ConfidentialInitialOracle"
    CONFIDENTIAL_PLAN_WITNESS = "ConfidentialPlanWitness"


class PIRSourceSubjectKind(str, Enum):
    BINDING_PAYLOAD = "pir.source-binding-payload"
    CAPABILITY_REQUIREMENT = "pir.source-capability-requirement"
    NO_POLICY = "pir.source-no-policy"
    POLICY_CLOSURE = "pir.source-policy-closure"


def _source_subject_arms(
    common: Mapping[PIRSourceFamily, int],
    no_policy: Mapping[PIRSourceFamily, int] | None = None,
) -> Mapping[PIRSourceSubjectKind, Mapping[PIRSourceFamily, int]]:
    common_arms = MappingProxyType(dict(common))
    no_policy_arms = common_arms if no_policy is None else MappingProxyType(dict(no_policy))
    return MappingProxyType(
        {
            PIRSourceSubjectKind.BINDING_PAYLOAD: common_arms,
            PIRSourceSubjectKind.CAPABILITY_REQUIREMENT: common_arms,
            PIRSourceSubjectKind.NO_POLICY: no_policy_arms,
            PIRSourceSubjectKind.POLICY_CLOSURE: common_arms,
        }
    )


_PIR_SOURCE_COMPILER_ARMS = MappingProxyType(
    {
        PIRSourceOwnerCompiler.INTERACTION: _source_subject_arms(
            {
                PIRSourceFamily.STATIC_VIEW: 0,
                PIRSourceFamily.CONFIDENTIAL_INITIAL_ORACLE: 1,
            },
            {PIRSourceFamily.STATIC_VIEW: 0},
        ),
        PIRSourceOwnerCompiler.CANONICAL_FRAMED: _source_subject_arms(
            {
                PIRSourceFamily.STATIC_VIEW: 0,
                PIRSourceFamily.CHECKED_CONSTRUCTION: 1,
            }
        ),
        PIRSourceOwnerCompiler.DUPLEX_SPONGE: _source_subject_arms(
            {
                PIRSourceFamily.STATIC_VIEW: 0,
                PIRSourceFamily.CHECKED_CONSTRUCTION: 1,
            }
        ),
        PIRSourceOwnerCompiler.PUBLIC_SETUP: _source_subject_arms(
            {PIRSourceFamily.PUBLIC_SETUP_INVOCATION_VIEW: 0}
        ),
        PIRSourceOwnerCompiler.INTERFACE_PLAN: _source_subject_arms(
            {
                PIRSourceFamily.INTERFACE_VIEW: 0,
                PIRSourceFamily.CONFIDENTIAL_PLAN_WITNESS: 1,
            },
            {PIRSourceFamily.INTERFACE_VIEW: 0},
        ),
    }
)


def compile_pir_source_subject_body(
    owner_compiler: PIRSourceOwnerCompiler,
    subject_kind: PIRSourceSubjectKind,
    family: PIRSourceFamily,
    family_local_body: object,
) -> object:
    """Apply one owner's bound source compiler to its tagged family value."""

    if type(owner_compiler) is not PIRSourceOwnerCompiler:
        raise ModelError("source subject selected no exact PIR owner compiler")
    if type(subject_kind) is not PIRSourceSubjectKind:
        raise ModelError("source subject selected no exact PIR subject compiler")
    if type(family) is not PIRSourceFamily:
        raise ModelError("source subject selected no exact tagged PIR family")
    try:
        arm = _PIR_SOURCE_COMPILER_ARMS[owner_compiler][subject_kind][family]
    except KeyError as error:
        raise ModelError("the selected PIR owner compiler does not issue this family") from error
    return k1.DatumVariant(arm, family_local_body)


def _authority_role_id(
    profile: object,
    subject_kind: str,
    family: object,
    coordinate: object,
    what: str,
) -> tuple[object, object]:
    body = k1.DatumRecord(
        (
            (0, family),
            (1, _any_content_ref(coordinate, what)),
        )
    )
    return _authority_id(profile, subject_kind, body), body


def _source_owner_compiler(
    profile: object,
    source_family: PIRSourceFamily,
    profiles: K2SemanticProfiles,
) -> PIRSourceOwnerCompiler:
    if profile.identity == profiles.interaction.identity:
        compiler = PIRSourceOwnerCompiler.INTERACTION
    elif profile.identity == profiles.transcript_fs.identity:
        compiler = PIRSourceOwnerCompiler.CANONICAL_FRAMED
    elif profile.identity == profiles.public_view.identity:
        compiler = PIRSourceOwnerCompiler.PUBLIC_SETUP
    else:
        raise ModelError("source authority selected no owner profile compiler")
    if source_family not in _PIR_SOURCE_COMPILER_ARMS[compiler][
        PIRSourceSubjectKind.BINDING_PAYLOAD
    ]:
        raise ModelError("source authority family is not issued by the owner profile")
    return compiler


def _authority_components(
    profile: object,
    source_family: PIRSourceFamily,
    capability_family: str,
    binding_payload_local_body: object,
    purpose_label: str,
    consumer_id: object | None,
    purpose_id: object | None,
    *,
    profiles: K2SemanticProfiles,
    profile_support: K2SemanticProfileSupport,
) -> tuple[object, object, object, object, object, object]:
    family = _symbol(capability_family, "capability family")
    owner_compiler = _source_owner_compiler(profile, source_family, profiles)
    if consumer_id is None:
        default_consumer_body = k1.DatumRecord(
            ((0, family), (1, k1.Symbol("bounded-downstream-consumer")))
        )
        consumer_id = _authority_id(
            profile,
            "pir.source-consumer",
            default_consumer_body,
        )
        _authenticate_k2_profiled_subject(
            consumer_id,
            "pir.source-consumer",
            default_consumer_body,
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=profile,
        )
    owner_consumer_id, owner_consumer_body = _authority_role_id(
        profile,
        "pir.source-consumer",
        family,
        consumer_id,
        "authority consumer",
    )
    _authenticate_k2_profiled_subject(
        owner_consumer_id,
        "pir.source-consumer",
        owner_consumer_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    if purpose_id is None:
        default_purpose_body = k1.DatumRecord(
            (
                (0, family),
                (1, _symbol(purpose_label, "authority purpose")),
            )
        )
        purpose_id = _authority_id(
            profile,
            "pir.source-purpose",
            default_purpose_body,
        )
        _authenticate_k2_profiled_subject(
            purpose_id,
            "pir.source-purpose",
            default_purpose_body,
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=profile,
        )
    owner_purpose_id, owner_purpose_body = _authority_role_id(
        profile,
        "pir.source-purpose",
        family,
        purpose_id,
        "authority purpose",
    )
    _authenticate_k2_profiled_subject(
        owner_purpose_id,
        "pir.source-purpose",
        owner_purpose_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    consumer_ref = _any_content_ref(owner_consumer_id, "authority consumer role")
    purpose_ref = _any_content_ref(owner_purpose_id, "authority purpose role")
    payload_body = compile_pir_source_subject_body(
        owner_compiler,
        PIRSourceSubjectKind.BINDING_PAYLOAD,
        source_family,
        binding_payload_local_body,
    )
    payload_id = _authority_id(
        profile,
        "pir.source-binding-payload",
        payload_body,
    )
    _authenticate_k2_profiled_subject(
        payload_id,
        "pir.source-binding-payload",
        payload_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    no_policy_body = compile_pir_source_subject_body(
        owner_compiler,
        PIRSourceSubjectKind.NO_POLICY,
        source_family,
        k1.DatumRecord(
            ((0, _any_content_ref(profile.identity, "authority owner profile")),)
        ),
    )
    no_policy_id = _authority_id(
        profile,
        "pir.source-no-policy",
        no_policy_body,
    )
    _authenticate_k2_profiled_subject(
        no_policy_id,
        "pir.source-no-policy",
        no_policy_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    requirement_body = compile_pir_source_subject_body(
        owner_compiler,
        PIRSourceSubjectKind.CAPABILITY_REQUIREMENT,
        source_family,
        k1.DatumRecord(((0, consumer_ref), (1, purpose_ref))),
    )
    requirement_id = _authority_id(
        profile,
        "pir.source-capability-requirement",
        requirement_body,
    )
    _authenticate_k2_profiled_subject(
        requirement_id,
        "pir.source-capability-requirement",
        requirement_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    closure_body = compile_pir_source_subject_body(
        owner_compiler,
        PIRSourceSubjectKind.POLICY_CLOSURE,
        source_family,
        k1.DatumRecord(
            (
                (0, _any_content_ref(payload_id, "authority payload")),
                (1, _any_content_ref(no_policy_id, "no-policy declaration")),
                (2, _any_content_ref(requirement_id, "capability requirement")),
            )
        ),
    )
    closure_id = _authority_id(
        profile,
        "pir.source-policy-closure",
        closure_body,
    )
    _authenticate_k2_profiled_subject(
        closure_id,
        "pir.source-policy-closure",
        closure_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profile,
    )
    requirement = k1.OwnerCapabilityRequirement(
        k1.Symbol("pir"),
        family,
        requirement_id,
    )
    return (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    )


def _pir_atomic_boundary_body(arm: int) -> object:
    if type(arm) is not int or not 0 <= arm <= 9:
        raise ModelError("PIR atomic-boundary arm is outside the owner union")
    return k1.DatumVariant(arm, k1.UNIT)


def _pir_atom_description(atomic_boundary_arm: int) -> object:
    return k1.DatumVariant(3, _pir_atomic_boundary_body(atomic_boundary_arm))


def _pir_record_description(
    fields: tuple[tuple[str, object], ...],
) -> object:
    return k1.DatumVariant(
        0,
        k1.DatumSeq(
            tuple(
                k1.DatumRecord(((0, k1.Symbol(name)), (1, description)))
                for name, description in fields
            )
        ),
    )


def _pir_variant_description(
    arms: tuple[tuple[str, object], ...],
) -> object:
    return k1.DatumVariant(
        1,
        k1.DatumSeq(
            tuple(
                k1.DatumRecord(((0, k1.Symbol(name)), (1, description)))
                for name, description in arms
            )
        ),
    )


def _pir_sequence_description(element: object) -> object:
    return k1.DatumVariant(2, element)


def _checked_fs_result_schema_body() -> object:
    """Finite PIRDescriptionBody for the checked result carried by this model."""

    content_ref = _pir_atom_description(4)
    reference_pair = _pir_record_description(
        (
            ("source", _pir_atom_description(7)),
            ("target", _pir_atom_description(7)),
        )
    )
    reference_map = _pir_sequence_description(reference_pair)
    return _pir_record_description(
        (
            ("source_protocol_id", content_ref),
            ("target_protocol_id", content_ref),
            ("shared_core_id", content_ref),
            ("transcript_construction_id", content_ref),
            ("occurrence_map", reference_map),
            ("value_map", reference_map),
            ("challenge_map", reference_map),
            ("conclusion", _pir_atom_description(3)),
        )
    )


def _checked_duplex_fs_result_schema_body() -> object:
    """Owner PIRDescriptionBody for the checked duplex result."""

    content_ref = _pir_atom_description(4)
    reference = _pir_atom_description(7)
    profile_law = _pir_atom_description(8)
    reference_pair = _pir_record_description(
        (("source", reference), ("target", reference))
    )
    reference_map = _pir_sequence_description(reference_pair)
    reference_sequence = _pir_sequence_description(reference)
    material_coordinate = _pir_record_description(
        (
            (
                "site",
                _pir_variant_description(
                    (
                        ("None", _pir_atom_description(0)),
                        ("Occurrence", reference),
                        ("Challenge", reference),
                    )
                ),
            ),
            ("ordinal", _pir_atom_description(1)),
        )
    )
    material_schema = _pir_record_description(
        (
            ("coordinate", material_coordinate),
            ("value_type", _pir_atom_description(5)),
            ("length", _pir_atom_description(1)),
        )
    )
    schedule_correspondence = _pir_record_description(
        (
            ("source", reference_sequence),
            ("target", reference_sequence),
            ("map", reference_map),
            ("law", profile_law),
        )
    )
    return _pir_record_description(
        (
            ("source_protocol_id", content_ref),
            ("target_protocol_id", content_ref),
            ("shared_core_id", content_ref),
            ("transcript_construction_id", content_ref),
            ("occurrence_map", reference_map),
            ("value_map", reference_map),
            ("challenge_map", reference_map),
            (
                "instance_projection",
                _pir_record_description(
                    (("bindings", reference_sequence), ("law", profile_law))
                ),
            ),
            (
                "construction_material_map",
                _pir_record_description(
                    (("target", material_coordinate), ("schema", material_schema))
                ),
            ),
            ("prover_schedule_correspondence", schedule_correspondence),
            ("verifier_schedule_correspondence", schedule_correspondence),
            ("conclusion", _pir_atom_description(3)),
        )
    )


_CORE_STATIC_VIEW_ARMS = MappingProxyType(
    {
        StaticViewKind.PUBLIC_BINDING: 0,
        StaticViewKind.STRATEGY_DECISION: 1,
        StaticViewKind.PUBLIC_COIN: 2,
        StaticViewKind.EFFECT: 3,
        StaticViewKind.CLAIM_REDUCTION: 4,
    }
)
_CANONICAL_CONSTRUCTION_VIEW_ARMS = MappingProxyType(
    {
        StaticViewKind.TRANSCRIPT_DECLARATION: 0,
        StaticViewKind.REQUIRED_INFLUENCE: 1,
        StaticViewKind.CHALLENGE_TRANSITION: 2,
    }
)


def _interaction_static_view_coordinate_body(
    coordinate: StaticViewCoordinate,
) -> object:
    if coordinate.owner_kind is StaticViewOwnerKind.CORE:
        try:
            view_arm = _CORE_STATIC_VIEW_ARMS[coordinate.view_kind]
        except KeyError as error:
            raise ModelError("Interaction Core coordinate has another profile's view kind") from error
        owner = k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (0, _any_content_ref(coordinate.owner_id, "static-view Core")),
                    (1, k1.DatumVariant(view_arm, k1.UNIT)),
                )
            ),
        )
    elif (
        coordinate.owner_kind is StaticViewOwnerKind.PROTOCOL
        and coordinate.view_kind is StaticViewKind.EXECUTION
    ):
        owner = k1.DatumVariant(
            1,
            k1.DatumRecord(
                ((0, _any_content_ref(coordinate.owner_id, "static-view Protocol")),)
            ),
        )
    else:
        raise ModelError("Interaction coordinate has another profile's owner kind")
    return k1.DatumRecord(
        (
            (0, owner),
            (
                1,
                _any_content_ref(
                    coordinate.semantic_profile_id,
                    "static-view semantic profile",
                ),
            ),
        )
    )


def _canonical_static_view_coordinate_body(
    coordinate: StaticViewCoordinate,
    source: object,
) -> object:
    if (
        coordinate.owner_kind is StaticViewOwnerKind.PROTOCOL
        and coordinate.view_kind is StaticViewKind.EXECUTION
    ):
        owner = k1.DatumVariant(
            0,
            k1.DatumRecord(
                ((0, _any_content_ref(coordinate.owner_id, "static-view Protocol")),)
            ),
        )
    elif coordinate.owner_kind is StaticViewOwnerKind.CONSTRUCTION:
        try:
            view_arm = _CANONICAL_CONSTRUCTION_VIEW_ARMS[coordinate.view_kind]
        except KeyError as error:
            raise ModelError("canonical construction coordinate has another view kind") from error
        owner = k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (
                        0,
                        _any_content_ref(
                            coordinate.owner_id,
                            "static-view transcript construction",
                        ),
                    ),
                    (1, k1.DatumVariant(view_arm, k1.UNIT)),
                )
            ),
        )
    elif (
        coordinate.owner_kind is StaticViewOwnerKind.FS_RESULT
        and coordinate.view_kind is StaticViewKind.FS_CONSTRUCTION
        and type(source) is CheckedFSConstructionIssue
    ):
        result = source.result
        owner = k1.DatumVariant(
            2,
            k1.DatumRecord(
                (
                    (0, _any_content_ref(result.source_protocol_id, "fresh Protocol")),
                    (1, _any_content_ref(result.target_protocol_id, "Fiat-Shamir Protocol")),
                    (2, _any_content_ref(result.shared_core_id, "shared Core")),
                    (
                        3,
                        _any_content_ref(
                            result.transcript_construction_id,
                            "transcript construction",
                        ),
                    ),
                    (4, _checked_fs_result_schema_body()),
                )
            ),
        )
    else:
        raise ModelError("canonical coordinate has another profile's owner kind")
    return k1.DatumRecord(
        (
            (0, owner),
            (
                1,
                _any_content_ref(
                    coordinate.semantic_profile_id,
                    "static-view semantic profile",
                ),
            ),
        )
    )


_STATIC_VIEW_ID_FIELDS = frozenset(
    {
        StaticViewField.PB_CORE_ID,
        StaticViewField.SD_CORE_ID,
        StaticViewField.PC_CORE_ID,
        StaticViewField.EF_CORE_ID,
        StaticViewField.CR_CORE_ID,
        StaticViewField.EX_PROTOCOL_ID,
        StaticViewField.EX_CORE_ID,
        StaticViewField.TD_CONSTRUCTION_ID,
        StaticViewField.TD_CORE_ID,
        StaticViewField.RI_CONSTRUCTION_ID,
        StaticViewField.RI_CORE_ID,
        StaticViewField.CT_CONSTRUCTION_ID,
        StaticViewField.CT_CORE_ID,
        StaticViewField.FS_SOURCE_PROTOCOL,
        StaticViewField.FS_TARGET_PROTOCOL,
        StaticViewField.FS_SHARED_CORE,
        StaticViewField.FS_CONSTRUCTION_ID,
    }
)
_STATIC_VIEW_LAW_FIELDS = frozenset(
    {
        StaticViewField.SD_PROVER_VIEW_FORMATION,
        StaticViewField.EX_VISIBLE_HISTORY,
        StaticViewField.EX_GENERATION,
        StaticViewField.EX_REPLAY,
        StaticViewField.EX_RELATION_RUN,
        StaticViewField.RI_PREFIX_LAW,
        StaticViewField.CT_NAMESPACE,
        StaticViewField.CT_RETRY_FAILURE,
    }
)


def _static_view_field_boundary_body(field: StaticViewField) -> object:
    if field in _STATIC_VIEW_ID_FIELDS:
        return _pir_atomic_boundary_body(4)  # Bytes / ContentRef bytes
    if field is StaticViewField.PC_ELIGIBILITY:
        return _pir_atomic_boundary_body(2)  # MetaBoolean
    if field in _STATIC_VIEW_LAW_FIELDS:
        return _pir_atomic_boundary_body(8)  # PIRProfileLawReference
    if field is StaticViewField.TD_APPLICATION_DOMAIN:
        return _pir_atomic_boundary_body(7)  # PIRReference
    return _pir_atomic_boundary_body(3)  # bounded model's closed symbolic leaf


def _static_view_field_coordinate_body(
    coordinate_body: object,
    view_kind: StaticViewKind,
    field: StaticViewField,
) -> object:
    try:
        ordinal = _VIEW_FIELDS[view_kind].index(field)
    except (KeyError, ValueError) as error:
        raise ModelError("static-view manifest field is outside the selected schema") from error
    return k1.DatumRecord(
        (
            (0, coordinate_body),
            (1, k1.DatumSeq((k1.DatumVariant(0, k1.Nat(ordinal)),))),
            (2, _static_view_field_boundary_body(field)),
        )
    )


def _static_binding_payload_local_body(
    projection: StaticViewProjection,
    source: object,
    owner_compiler: PIRSourceOwnerCompiler,
) -> object:
    if owner_compiler is PIRSourceOwnerCompiler.INTERACTION:
        coordinate_body = _interaction_static_view_coordinate_body(
            projection.coordinate
        )
    elif owner_compiler is PIRSourceOwnerCompiler.CANONICAL_FRAMED:
        coordinate_body = _canonical_static_view_coordinate_body(
            projection.coordinate,
            source,
        )
    else:
        raise ModelError("bounded protocol static view selected an unavailable owner compiler")
    manifest_body = k1.DatumSeq(
        tuple(
            _static_view_field_coordinate_body(
                coordinate_body,
                projection.coordinate.view_kind,
                field,
            )
            for field in projection.manifest
        )
    )
    return k1.DatumRecord(((0, coordinate_body), (1, manifest_body)))


def _static_authority_profile(
    coordinate: StaticViewCoordinate,
    profiles: K2SemanticProfiles,
) -> object:
    if coordinate.semantic_profile_id == profiles.interaction.identity:
        profile = profiles.interaction
    elif coordinate.semantic_profile_id == profiles.transcript_fs.identity:
        profile = profiles.transcript_fs
    else:
        raise ModelError("static-view coordinate selects no K2 owner profile")
    if (
        coordinate.owner_kind is StaticViewOwnerKind.CORE
        and profile is not profiles.interaction
    ):
        raise ModelError("Core static views must select the Interaction profile")
    if (
        coordinate.owner_kind
        in {StaticViewOwnerKind.CONSTRUCTION, StaticViewOwnerKind.FS_RESULT}
        and profile is not profiles.transcript_fs
    ):
        raise ModelError("Transcript and checked-FS views need the Transcript profile")
    return profile


ExactPIRStaticViewAuthorityBinding = k1.OwnerLocalSourceAuthorityBinding


_STATIC_VIEW_ISSUER = object()
_STATIC_VIEW_LIVE_CAPABILITIES: dict[int, object] = {}
_STATIC_VIEW_LIVE_ISSUANCES: dict[int, object] = {}


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class PIRStaticViewCapability(_NonTransferableAuthority):
    coordinate: StaticViewCoordinate
    projection: StaticViewProjection
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _source: object
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _STATIC_VIEW_ISSUER:
            raise ModelError("only PIR may issue a static-view capability")


@dataclass(frozen=True, eq=False, repr=False)
class IssuedPIRStaticView(_NonTransferableAuthority):
    projection: StaticViewProjection
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    capability: PIRStaticViewCapability
    _issuer: object


class QualifiedViewOutcomeKind(str, Enum):
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
class QualifiedViewOutcome:
    kind: QualifiedViewOutcomeKind
    value: object | None = None
    detail: tuple[object, ...] = ()


_VIEW_REQUIRED: Mapping[StaticViewField, frozenset[StaticViewField]] = MappingProxyType(
    {
        StaticViewField.PB_BINDINGS: frozenset(
            {StaticViewField.PB_CORE_ID, StaticViewField.PB_SCOPE_OPENINGS}
        ),
        StaticViewField.SD_DECISION_POINTS: frozenset(
            {StaticViewField.SD_CORE_ID}
        ),
        StaticViewField.SD_PROVER_VIEW_FORMATION: frozenset(
            {StaticViewField.SD_CORE_ID, StaticViewField.SD_DECISION_POINTS}
        ),
        StaticViewField.SD_GUARANTEED_READS: frozenset(
            {
                StaticViewField.SD_CORE_ID,
                StaticViewField.SD_DECISION_POINTS,
                StaticViewField.SD_PROVER_VIEW_FORMATION,
            }
        ),
        StaticViewField.SD_LEGAL_MOVE_TYPES: frozenset(
            {StaticViewField.SD_CORE_ID, StaticViewField.SD_DECISION_POINTS}
        ),
        StaticViewField.PC_CHALLENGES: frozenset(
            {
                StaticViewField.PC_CORE_ID,
                StaticViewField.PC_ELIGIBILITY,
                StaticViewField.PC_PRIVATE_CLOSURE,
            }
        ),
        StaticViewField.EF_MESSAGES: frozenset(
            {
                StaticViewField.EF_CORE_ID,
                StaticViewField.EF_OCCURRENCE_SCHEDULE,
                StaticViewField.EF_VALUE_PRODUCER_GRAPH,
            }
        ),
        StaticViewField.EF_ORACLES: frozenset(
            {
                StaticViewField.EF_CORE_ID,
                StaticViewField.EF_OCCURRENCE_SCHEDULE,
                StaticViewField.EF_VALUE_PRODUCER_GRAPH,
            }
        ),
        StaticViewField.EF_CHECKS: frozenset(
            {
                StaticViewField.EF_CORE_ID,
                StaticViewField.EF_OCCURRENCE_SCHEDULE,
                StaticViewField.EF_VALUE_PRODUCER_GRAPH,
            }
        ),
        StaticViewField.EF_TERMINALS: frozenset(
            {
                StaticViewField.EF_CORE_ID,
                StaticViewField.EF_OCCURRENCE_SCHEDULE,
                StaticViewField.EF_VALUE_PRODUCER_GRAPH,
                StaticViewField.EF_CHECKS,
            }
        ),
        StaticViewField.CR_REDUCTIONS: frozenset(
            {StaticViewField.CR_CORE_ID, StaticViewField.CR_CLAIMS}
        ),
        StaticViewField.CR_TERMINAL_DISPOSITIONS: frozenset(
            {
                StaticViewField.CR_CORE_ID,
                StaticViewField.CR_CLAIMS,
                StaticViewField.CR_REDUCTIONS,
            }
        ),
        StaticViewField.EX_VISIBLE_HISTORY: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
            }
        ),
        StaticViewField.EX_RESOLVER: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
            }
        ),
        StaticViewField.EX_GENERATION: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
                StaticViewField.EX_VISIBLE_HISTORY,
            }
        ),
        StaticViewField.EX_RUN_RECORD: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
            }
        ),
        StaticViewField.EX_REPLAY: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
                StaticViewField.EX_RUN_RECORD,
            }
        ),
        StaticViewField.EX_RELATION_RUN: frozenset(
            {
                StaticViewField.EX_PROTOCOL_ID,
                StaticViewField.EX_CORE_ID,
                StaticViewField.EX_INTERPRETATION,
                StaticViewField.EX_RUN_RECORD,
                StaticViewField.EX_REPLAY,
            }
        ),
        StaticViewField.TD_APPLICATION_DOMAIN: frozenset(
            {
                StaticViewField.TD_CONSTRUCTION_ID,
                StaticViewField.TD_CORE_ID,
                StaticViewField.TD_ALGORITHMS,
            }
        ),
        StaticViewField.TD_FRAME_SCHEDULE: frozenset(
            {
                StaticViewField.TD_CONSTRUCTION_ID,
                StaticViewField.TD_CORE_ID,
                StaticViewField.TD_ALGORITHMS,
                StaticViewField.TD_APPLICATION_DOMAIN,
            }
        ),
        StaticViewField.RI_REQUIREMENTS: frozenset(
            {StaticViewField.RI_CONSTRUCTION_ID, StaticViewField.RI_CORE_ID}
        ),
        StaticViewField.RI_PREFIX_LAW: frozenset(
            {
                StaticViewField.RI_CONSTRUCTION_ID,
                StaticViewField.RI_CORE_ID,
                StaticViewField.RI_REQUIREMENTS,
            }
        ),
        StaticViewField.CT_NAMESPACE: frozenset(
            {StaticViewField.CT_CONSTRUCTION_ID, StaticViewField.CT_CORE_ID}
        ),
        StaticViewField.CT_SAMPLER: frozenset(
            {
                StaticViewField.CT_CONSTRUCTION_ID,
                StaticViewField.CT_CORE_ID,
                StaticViewField.CT_NAMESPACE,
            }
        ),
        StaticViewField.CT_RETRY_FAILURE: frozenset(
            {
                StaticViewField.CT_CONSTRUCTION_ID,
                StaticViewField.CT_CORE_ID,
                StaticViewField.CT_NAMESPACE,
                StaticViewField.CT_SAMPLER,
            }
        ),
        StaticViewField.FS_MAPS: frozenset(
            {
                StaticViewField.FS_RESULT_REF,
                StaticViewField.FS_RESULT_SCHEMA,
                StaticViewField.FS_SOURCE_PROTOCOL,
                StaticViewField.FS_TARGET_PROTOCOL,
                StaticViewField.FS_SHARED_CORE,
                StaticViewField.FS_CONSTRUCTION_ID,
            }
        ),
        StaticViewField.FS_CONCLUSION: frozenset(
            {StaticViewField.FS_MAPS}
        ),
    }
)


def required_static_view_read_closure(
    kind: StaticViewKind,
    requested: tuple[StaticViewField, ...],
) -> tuple[StaticViewField, ...]:
    allowed = set(_VIEW_FIELDS[kind])
    closure = set(requested)
    if not closure <= allowed:
        raise ModelError("view manifest contains a field from another owner schema")
    changed = True
    while changed:
        changed = False
        for field in tuple(closure):
            for required in _VIEW_REQUIRED.get(field, ()):
                if required not in closure:
                    closure.add(required)
                    changed = True
    return tuple(sorted(closure, key=_FIELD_ORDER.__getitem__))


def _validate_static_view_manifest(
    kind: StaticViewKind,
    manifest: tuple[StaticViewField, ...],
) -> QualifiedViewOutcome | None:
    if type(manifest) is not tuple or not manifest:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    if any(type(field) is not StaticViewField for field in manifest):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    expected_order = tuple(sorted(set(manifest), key=_FIELD_ORDER.__getitem__))
    if manifest != expected_order:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    try:
        closure = required_static_view_read_closure(kind, manifest)
    except (KeyError, ModelError):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.KIND_MISMATCH)
    if closure != manifest:
        missing = tuple(field for field in closure if field not in manifest)
        return QualifiedViewOutcome(
            QualifiedViewOutcomeKind.MISSING_DEPENDENCY,
            detail=missing,
        )
    return None


def _decision_occurrences(core: Core) -> tuple[Occurrence, ...]:
    return tuple(
        item
        for item in core.schedule
        if item.kind in {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.ORACLE_PUBLISH}
    )


def _value_producer_graph(core: Core) -> tuple[object, ...]:
    sorts: dict[ValueRef, ValueSort] = {
        ValueRef.input(item.name): item.value_sort for item in core.inputs
    }
    result: list[object] = [
        ("input", item.name, item.role, item.scope, item.value_sort)
        for item in core.inputs
    ]
    for item in core.schedule:
        sort = _occurrence_sort(item, sorts)
        result.append(
            (
                "occurrence",
                item.name,
                item.kind,
                item.scope,
                item.dependencies,
                item.guard,
                sort,
            )
        )
        sorts[ValueRef.occurrence(item.name)] = sort
    return tuple(result)


def _core_static_payload(
    core: Core,
    kind: StaticViewKind,
    profiles: K2SemanticProfiles,
) -> Mapping[StaticViewField, object]:
    admit_core(core)
    cid = core_id(core, profiles=profiles)
    if kind is StaticViewKind.PUBLIC_BINDING:
        bindings = tuple(
            (
                item.scope,
                item.name,
                item.role,
                item.value_sort,
                "invocation-public-input",
            )
            for item in core.inputs
            if item.role is not InputRole.VERIFIER_PRIVATE
        )
        return MappingProxyType(
            {
                StaticViewField.PB_CORE_ID: cid,
                StaticViewField.PB_SCOPE_OPENINGS: core.scopes,
                StaticViewField.PB_BINDINGS: bindings,
            }
        )
    if kind is StaticViewKind.STRATEGY_DECISION:
        decisions = _decision_occurrences(core)
        schedule_index = {
            occurrence.name: index
            for index, occurrence in enumerate(core.schedule)
        }

        def visible_public_inputs(decision: Occurrence) -> tuple[str, ...]:
            decision_index = schedule_index[decision.name]
            open_scope_names = {
                scope.name
                for scope in core.scopes
                if scope.open_before is None
                or schedule_index[scope.open_before] <= decision_index
            }
            return tuple(
                item.name
                for item in core.inputs
                if item.role is not InputRole.VERIFIER_PRIVATE
                and item.scope in open_scope_names
            )

        reads = tuple(
            (
                decision.name,
                visible_public_inputs(decision),
                tuple(
                    item.name
                    for item in core.schedule[: schedule_index[decision.name]]
                    if item.guard.kind is PredicateKind.ALWAYS
                ),
            )
            for decision in decisions
        )
        return MappingProxyType(
            {
                StaticViewField.SD_CORE_ID: cid,
                StaticViewField.SD_DECISION_POINTS: decisions,
                StaticViewField.SD_PROVER_VIEW_FORMATION: "prefix-only-public-k2-v1",
                StaticViewField.SD_GUARANTEED_READS: reads,
                StaticViewField.SD_LEGAL_MOVE_TYPES: tuple(
                    (item.name, _occurrence_sort(item, {})) for item in decisions
                ),
            }
        )
    if kind is StaticViewKind.PUBLIC_COIN:
        challenges = tuple(
            item for item in core.schedule if item.kind is OccurrenceKind.CHALLENGE
        )
        return MappingProxyType(
            {
                StaticViewField.PC_CORE_ID: cid,
                StaticViewField.PC_ELIGIBILITY: is_public_coin_eligible(core),
                StaticViewField.PC_PRIVATE_CLOSURE: tuple(
                    item.name
                    for item in core.inputs
                    if item.role is InputRole.VERIFIER_PRIVATE
                ),
                StaticViewField.PC_CHALLENGES: challenges,
            }
        )
    if kind is StaticViewKind.EFFECT:
        def by_kind(kinds: set[OccurrenceKind]) -> tuple[Occurrence, ...]:
            return tuple(item for item in core.schedule if item.kind in kinds)

        return MappingProxyType(
            {
                StaticViewField.EF_CORE_ID: cid,
                StaticViewField.EF_OCCURRENCE_SCHEDULE: core.schedule,
                StaticViewField.EF_VALUE_PRODUCER_GRAPH: _value_producer_graph(core),
                StaticViewField.EF_MESSAGES: by_kind(
                    {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.VERIFIER_MESSAGE}
                ),
                StaticViewField.EF_ORACLES: by_kind(
                    {
                        OccurrenceKind.ORACLE_PUBLISH,
                        OccurrenceKind.ORACLE_QUERY,
                        OccurrenceKind.ORACLE_ANSWER,
                    }
                ),
                StaticViewField.EF_CHECKS: by_kind({OccurrenceKind.CHECK}),
                StaticViewField.EF_TERMINALS: by_kind({OccurrenceKind.TERMINAL}),
                StaticViewField.EF_EXTENSIONS: core.extensions,
            }
        )
    if kind is StaticViewKind.CLAIM_REDUCTION:
        return MappingProxyType(
            {
                StaticViewField.CR_CORE_ID: cid,
                StaticViewField.CR_CLAIMS: core.initial_claims,
                StaticViewField.CR_REDUCTIONS: core.reductions,
                StaticViewField.CR_TERMINAL_DISPOSITIONS: core.claim_uses,
            }
        )
    raise ModelError("view kind is not Core-owned")


def _issue_static_projection(
    coordinate: StaticViewCoordinate,
    manifest: tuple[StaticViewField, ...],
    payload: Mapping[StaticViewField, object],
    source: object,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    try:
        profile = _static_authority_profile(coordinate, profiles)
        owner_subject_kind = {
            StaticViewOwnerKind.CORE: "pir.interactive-core",
            StaticViewOwnerKind.PROTOCOL: "pir.protocol",
            StaticViewOwnerKind.CONSTRUCTION: "pir.transcript-construction",
        }.get(coordinate.owner_kind)
        required_subject_kinds = _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS | (
            frozenset()
            if owner_subject_kind is None
            else frozenset({owner_subject_kind})
        )
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profile,
            required_subject_kinds=required_subject_kinds,
        )
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except (MalformedSemanticProfileError, ModelError):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    refusal = _validate_static_view_manifest(coordinate.view_kind, manifest)
    if refusal is not None:
        return refusal
    try:
        entries = tuple(StaticViewEntry(field, payload[field]) for field in manifest)
    except KeyError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.CHECKER_FAILURE)
    projection = StaticViewProjection(coordinate, manifest, entries)
    owner_compiler = _source_owner_compiler(
        profile,
        PIRSourceFamily.STATIC_VIEW,
        profiles,
    )
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _authority_components(
        profile,
        PIRSourceFamily.STATIC_VIEW,
        "static-view",
        _static_binding_payload_local_body(
            projection,
            source,
            owner_compiler,
        ),
        coordinate.view_kind.value,
        consumer_id,
        purpose_id,
        profiles=profiles,
        profile_support=profile_support,
    )
    binding = k1.OwnerLocalSourceAuthorityBinding(
        k1.Symbol("pir"),
        k1.Symbol("static-view"),
        projection,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    k1.validate_owner_local_source_authority_binding(binding)
    capability = PIRStaticViewCapability(
        coordinate,
        projection,
        binding,
        consumer_id,
        purpose_id,
        source,
        _STATIC_VIEW_ISSUER,
    )
    _STATIC_VIEW_LIVE_CAPABILITIES[id(capability)] = capability
    issued = IssuedPIRStaticView(
        projection,
        binding,
        capability,
        _STATIC_VIEW_ISSUER,
    )
    _STATIC_VIEW_LIVE_ISSUANCES[id(issued)] = issued
    return QualifiedViewOutcome(
        QualifiedViewOutcomeKind.AFFIRMATIVE,
        issued,
    )


def validate_issued_pir_static_view(
    issued: object,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> bool:
    """Validate the exact K1 envelope and identical live bearer objects."""

    if (
        type(issued) is not IssuedPIRStaticView
        or _STATIC_VIEW_LIVE_ISSUANCES.get(id(issued)) is not issued
        or issued._issuer is not _STATIC_VIEW_ISSUER
        or type(issued.capability) is not PIRStaticViewCapability
        or _STATIC_VIEW_LIVE_CAPABILITIES.get(id(issued.capability))
        is not issued.capability
        or issued.capability._issuer is not _STATIC_VIEW_ISSUER
        or issued.capability.source_binding is not issued.source_binding
        or issued.capability.projection is not issued.projection
        or issued.capability.coordinate is not issued.projection.coordinate
        or type(issued.source_binding) is not k1.OwnerLocalSourceAuthorityBinding
        or issued.source_binding.owner_local_coordinate is not issued.projection
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
        profile = _static_authority_profile(issued.projection.coordinate, profiles)
        owner_subject_kind = {
            StaticViewOwnerKind.CORE: "pir.interactive-core",
            StaticViewOwnerKind.PROTOCOL: "pir.protocol",
            StaticViewOwnerKind.CONSTRUCTION: "pir.transcript-construction",
        }.get(issued.projection.coordinate.owner_kind)
        required_subject_kinds = _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS | (
            frozenset()
            if owner_subject_kind is None
            else frozenset({owner_subject_kind})
        )
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profile,
            required_subject_kinds=required_subject_kinds,
        )
        k1.validate_owner_local_source_authority_binding(issued.source_binding)
        owner_compiler = _source_owner_compiler(
            profile,
            PIRSourceFamily.STATIC_VIEW,
            profiles,
        )
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _authority_components(
            profile,
            PIRSourceFamily.STATIC_VIEW,
            "static-view",
            _static_binding_payload_local_body(
                issued.projection,
                issued.capability._source,
                owner_compiler,
            ),
            issued.projection.coordinate.view_kind.value,
            consumer_id,
            purpose_id,
            profiles=profiles,
            profile_support=profile_support,
        )
    except (ModelError, k1.ModelError, k1.CanonicalError):
        return False
    binding = issued.source_binding
    return (
        binding.owner_domain == k1.Symbol("pir")
        and binding.capability_family == k1.Symbol("static-view")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    )


def resolve_public_coin_challenge_projection(
    issued: object,
    challenge_entry_ordinal: int,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> PublicCoinChallengeProjection:
    """Resolve one exact challenge-domain leaf from a live PublicCoinView.

    This is an owner operation, not structural decoding of a copied tuple.  It
    authenticates the live view and its consumer/purpose binding, checks the
    field against the exact owning Core, and returns both the filtered-field
    ordinal and the distinct Core-schedule ordinal.
    """

    if type(challenge_entry_ordinal) is not int or challenge_entry_ordinal < 0:
        raise ModelError("public-coin challenge entry ordinal must be a natural")
    if not validate_issued_pir_static_view(
        issued,
        profiles=profiles,
        profile_support=profile_support,
        expected_consumer_id=expected_consumer_id,
        expected_purpose_id=expected_purpose_id,
    ):
        raise ModelError("public-coin challenge projection lacks live PIR authority")
    assert type(issued) is IssuedPIRStaticView
    projection = issued.projection
    coordinate = projection.coordinate
    if (
        coordinate.owner_kind is not StaticViewOwnerKind.CORE
        or coordinate.view_kind is not StaticViewKind.PUBLIC_COIN
        or StaticViewField.PC_CHALLENGES not in projection.manifest
    ):
        raise ModelError("static view is not an issued PublicCoinView challenge field")
    selected_entries = tuple(
        entry
        for entry in projection.entries
        if entry.field is StaticViewField.PC_CHALLENGES
    )
    if len(selected_entries) != 1 or type(selected_entries[0].value) is not tuple:
        raise ModelError("PublicCoinView has no unique immutable challenge sequence")
    challenges = selected_entries[0].value
    if challenge_entry_ordinal >= len(challenges):
        raise ModelError("public-coin challenge entry ordinal is out of range")
    challenge = challenges[challenge_entry_ordinal]
    if (
        type(challenge) is not Occurrence
        or challenge.kind is not OccurrenceKind.CHALLENGE
        or type(challenge.challenge_domain) is not ChallengeDomain
    ):
        raise ModelError("PublicCoinView entry is not one finite challenge")
    core = issued.capability._source
    if type(core) is not Core:
        raise ModelError("PublicCoinView live source is not its owning Core")
    admit_core(core)
    expected_challenges = tuple(
        occurrence
        for occurrence in core.schedule
        if occurrence.kind is OccurrenceKind.CHALLENGE
    )
    if challenges != expected_challenges or core_id(core, profiles=profiles) != coordinate.owner_id:
        raise ModelError("PublicCoinView challenge field is detached from its owning Core")
    schedule_ordinals = tuple(
        ordinal
        for ordinal, occurrence in enumerate(core.schedule)
        if occurrence is challenge
    )
    if len(schedule_ordinals) != 1:
        raise ModelError("PublicCoinView challenge has no unique Core schedule position")
    schedule_ordinal = schedule_ordinals[0]

    def atomic(leaf: StaticViewAtomicLeaf) -> PIRStaticViewAtomicCoordinate:
        return PIRStaticViewAtomicCoordinate(
            coordinate,
            StaticViewField.PC_CHALLENGES,
            challenge_entry_ordinal,
            schedule_ordinal,
            challenge.name,
            leaf,
        )

    return PublicCoinChallengeProjection(
        atomic(StaticViewAtomicLeaf.CHALLENGE_OCCURRENCE),
        atomic(StaticViewAtomicLeaf.CHALLENGE_DOMAIN),
        challenge.challenge_domain,
    )


def issue_core_static_view(
    core: Core,
    kind: StaticViewKind,
    manifest: tuple[StaticViewField, ...],
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    if kind not in {
        StaticViewKind.PUBLIC_BINDING,
        StaticViewKind.STRATEGY_DECISION,
        StaticViewKind.PUBLIC_COIN,
        StaticViewKind.EFFECT,
        StaticViewKind.CLAIM_REDUCTION,
    }:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.KIND_MISMATCH)
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.interaction,
            required_subject_kinds=frozenset({"pir.interactive-core"}),
        )
        cid = core_id(core, profiles=profiles)
        _authenticate_k2_profiled_subject(
            cid,
            "pir.interactive-core",
            core_body(core),
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=profiles.interaction,
        )
        payload = _core_static_payload(core, kind, profiles)
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except ModelError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    coordinate = StaticViewCoordinate(
        StaticViewOwnerKind.CORE,
        cid,
        kind,
        profiles.interaction.identity,
    )
    return _issue_static_projection(
        coordinate,
        manifest,
        payload,
        core,
        profiles=profiles,
        profile_support=profile_support,
        consumer_id=consumer_id,
        purpose_id=purpose_id,
    )


def issue_execution_view(
    core: Core,
    construction: TranscriptConstruction | None,
    interpretation: ChallengeInterpretation,
    manifest: tuple[StaticViewField, ...],
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    owner_profile = (
        profiles.interaction
        if interpretation is ChallengeInterpretation.FRESH
        else profiles.transcript_fs
    )
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            owner_profile,
            required_subject_kinds=frozenset({"pir.protocol"}),
        )
        pid = protocol_id(
            core,
            construction,
            interpretation,
            profiles=profiles,
        )
        _authenticate_k2_profiled_subject(
            pid,
            "pir.protocol",
            protocol_body(
                core,
                construction,
                interpretation,
                profiles=profiles,
            ),
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=owner_profile,
        )
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except ModelError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    payload = MappingProxyType(
        {
            StaticViewField.EX_PROTOCOL_ID: pid,
            StaticViewField.EX_CORE_ID: core_id(core, profiles=profiles),
            StaticViewField.EX_INTERPRETATION: interpretation,
            StaticViewField.EX_VISIBLE_HISTORY: "prefix-only-visible-history-v1",
            StaticViewField.EX_RESOLVER: (
                "fresh-request" if interpretation is ChallengeInterpretation.FRESH else "fs-transition"
            ),
            StaticViewField.EX_GENERATION: "online-strategy-step-v1",
            StaticViewField.EX_RUN_RECORD: RunRecord,
            StaticViewField.EX_REPLAY: "exact-record-replay-v1",
            StaticViewField.EX_RELATION_RUN: "public-relation-run-view-v1",
        }
    )
    coordinate = StaticViewCoordinate(
        StaticViewOwnerKind.PROTOCOL,
        pid,
        StaticViewKind.EXECUTION,
        owner_profile.identity,
    )
    return _issue_static_projection(
        coordinate,
        manifest,
        payload,
        (core, construction, interpretation),
        profiles=profiles,
        profile_support=profile_support,
        consumer_id=consumer_id,
        purpose_id=purpose_id,
    )


def _construction_static_payload(
    core: Core,
    construction: TranscriptConstruction,
    kind: StaticViewKind,
    profiles: K2SemanticProfiles,
) -> Mapping[StaticViewField, object]:
    admit_core(core)
    construction.admit()
    cid = core_id(core, profiles=profiles)
    tid = construction_id(core, construction, profiles=profiles)
    if kind is StaticViewKind.TRANSCRIPT_DECLARATION:
        return MappingProxyType(
            {
                StaticViewField.TD_CONSTRUCTION_ID: tid,
                StaticViewField.TD_CORE_ID: cid,
                StaticViewField.TD_ALGORITHMS: (
                    construction.version,
                    INITIAL_TRANSCRIPT_STATE,
                    construction.state_bytes,
                ),
                StaticViewField.TD_APPLICATION_DOMAIN: construction.application_domain,
                StaticViewField.TD_FRAME_SCHEDULE: tuple(
                    (index, item.name, item.kind) for index, item in enumerate(core.schedule)
                ),
            }
        )
    if kind is StaticViewKind.REQUIRED_INFLUENCE:
        requirements = tuple(
            (
                index,
                item.name,
                tuple(
                    (scope.name, scope.parent, scope.open_before)
                    for scope in core.scopes
                    if scope.open_before is None
                    or core.schedule.index(item) >= (
                        0
                        if scope.open_before is None
                        else next(
                            position
                            for position, occurrence in enumerate(core.schedule)
                            if occurrence.name == scope.open_before
                        )
                    )
                ),
                tuple(
                    (
                        prior.name,
                        required_influence_kinds(prior),
                        prior.guard.kind is not PredicateKind.ALWAYS,
                    )
                    for prior in core.schedule[:index]
                ),
                item.dependencies,
                tuple(
                    (reduction.name, publication.publication)
                    for reduction in core.reductions
                    for publication in reduction.required_publications
                    if publication.next_challenge == item.name
                ),
            )
            for index, item in enumerate(core.schedule)
            if item.kind is OccurrenceKind.CHALLENGE
        )
        return MappingProxyType(
            {
                StaticViewField.RI_CONSTRUCTION_ID: tid,
                StaticViewField.RI_CORE_ID: cid,
                StaticViewField.RI_REQUIREMENTS: requirements,
                StaticViewField.RI_PREFIX_LAW: "ordered-required-influence-subtrace-v1",
            }
        )
    if kind is StaticViewKind.CHALLENGE_TRANSITION:
        return MappingProxyType(
            {
                StaticViewField.CT_CONSTRUCTION_ID: tid,
                StaticViewField.CT_CORE_ID: cid,
                StaticViewField.CT_NAMESPACE: "core-construction-occurrence-draw-v1",
                StaticViewField.CT_SAMPLER: (
                    construction.sample_bytes,
                    construction.max_attempts,
                    "big-endian-rejection",
                ),
                StaticViewField.CT_RETRY_FAILURE: (
                    "advance-before-decode",
                    SamplingExhausted,
                ),
            }
        )
    raise ModelError("view kind is not construction-owned")


def issue_construction_static_view(
    core: Core,
    construction: TranscriptConstruction,
    kind: StaticViewKind,
    manifest: tuple[StaticViewField, ...],
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    if kind not in {
        StaticViewKind.TRANSCRIPT_DECLARATION,
        StaticViewKind.REQUIRED_INFLUENCE,
        StaticViewKind.CHALLENGE_TRANSITION,
    }:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.KIND_MISMATCH)
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.transcript_fs,
            required_subject_kinds=frozenset({"pir.transcript-construction"}),
        )
        payload = _construction_static_payload(core, construction, kind, profiles)
        tid = construction_id(core, construction, profiles=profiles)
        _authenticate_k2_profiled_subject(
            tid,
            "pir.transcript-construction",
            construction_body(core, construction, profiles=profiles),
            profiles=profiles,
            profile_support=profile_support,
            selected_profile=profiles.transcript_fs,
        )
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except ModelError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    coordinate = StaticViewCoordinate(
        StaticViewOwnerKind.CONSTRUCTION,
        tid,
        kind,
        profiles.transcript_fs.identity,
    )
    return _issue_static_projection(
        coordinate,
        manifest,
        payload,
        (core, construction),
        profiles=profiles,
        profile_support=profile_support,
        consumer_id=consumer_id,
        purpose_id=purpose_id,
    )


class FSConstructionDefect(str, Enum):
    SHARED_CORE_MISMATCH = "shared-core-mismatch"
    PUBLIC_COIN_INELIGIBLE = "public-coin-ineligible"


@dataclass(frozen=True)
class CheckedFSConstruction:
    source_protocol_id: object
    target_protocol_id: object
    shared_core_id: object
    transcript_construction_id: object
    occurrence_map: tuple[tuple[str, str], ...]
    value_map: tuple[tuple[str, str], ...]
    challenge_map: tuple[tuple[str, str], ...]
    conclusion: str = "structurally-constructed"


ExactCheckedFSConstructionAuthorityBinding = k1.OwnerLocalSourceAuthorityBinding


_FS_CONSTRUCTION_CHECK_ISSUER = object()
_FS_CONSTRUCTION_LIVE_CAPABILITIES: dict[int, object] = {}
_FS_CONSTRUCTION_LIVE_ISSUES: dict[int, object] = {}


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class CheckedFSConstructionCapability(_NonTransferableAuthority):
    result_ref: object
    result: CheckedFSConstruction
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _sources: object
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _FS_CONSTRUCTION_CHECK_ISSUER:
            raise ModelError("only the FS checker may issue checked authority")


@dataclass(frozen=True, eq=False, repr=False)
class CheckedFSConstructionIssue(_NonTransferableAuthority):
    result_ref: object
    result: CheckedFSConstruction
    source_binding: k1.OwnerLocalSourceAuthorityBinding
    capability: CheckedFSConstructionCapability
    _issuer: object


def _profile_local_declaration_ref(
    profile: object,
    declaration_kind: str,
    declaration_name: str,
) -> object:
    if type(profile) is not k1.SemanticLanguageProfile:
        raise ModelError("checker contract needs one exact owner profile")
    try:
        catalog = k1.profile_declaration_catalogs(profile).get(declaration_kind)
    except (k1.ModelError, k1.CanonicalError) as error:
        raise ModelError("checker contract owner catalog is malformed") from error
    if catalog is None:
        raise ModelError("checker contract declaration kind is absent")
    matches: list[int] = []
    for ordinal, body in enumerate(catalog.values):
        if type(body) is not k1.DatumRecord:
            continue
        fields = dict(body.fields)
        name = fields.get(0)
        if type(name) is k1.Symbol and name.value == declaration_name:
            matches.append(ordinal)
    if len(matches) != 1:
        raise ModelError("checker contract declaration name is not unique and present")
    return k1.ProfileLocalDeclarationRef(declaration_kind, matches[0])


def _checked_construction_checker_contract_body(
    profile: object,
    owner_compiler: PIRSourceOwnerCompiler,
    result_schema_body: object,
) -> object:
    try:
        declarations = _CHECKER_CONTRACT_DECLARATIONS[owner_compiler]
    except KeyError as error:
        raise ModelError("selected owner has no checked-construction contract") from error
    references = tuple(
        _profile_local_declaration_ref(profile, kind, name)
        for kind, name in declarations
    )
    try:
        reference_bodies = tuple(
            k1.profile_declaration_ref_datum(reference)
            for reference in references
        )
        k1.encode_datum(result_schema_body)
    except (k1.ModelError, k1.CanonicalError) as error:
        raise ModelError("checker contract body is not canonical") from error
    return k1.DatumRecord(
        (
            (0, reference_bodies[0]),
            (1, reference_bodies[1]),
            (2, reference_bodies[2]),
            (3, result_schema_body),
        )
    )


def _checked_construction_checker_contract_id(
    profile: object,
    owner_compiler: PIRSourceOwnerCompiler,
    result_schema_body: object,
) -> object:
    return _authority_id(
        profile,
        "pir.checker-contract",
        _checked_construction_checker_contract_body(
            profile,
            owner_compiler,
            result_schema_body,
        ),
    )


def _checked_fs_checker_contract_id(profile: object) -> object:
    return _checked_construction_checker_contract_id(
        profile,
        PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        _checked_fs_result_schema_body(),
    )


def _checked_construction_binding_payload_local_body(
    source_protocol_id: object,
    target_protocol_id: object,
    shared_core_id: object,
    transcript_construction_id: object,
    profile: object,
    owner_compiler: PIRSourceOwnerCompiler,
    result_schema_body: object,
) -> object:
    checker_contract_id = _checked_construction_checker_contract_id(
        profile,
        owner_compiler,
        result_schema_body,
    )
    return k1.DatumRecord(
        (
            (0, _any_content_ref(source_protocol_id, "fresh Protocol")),
            (1, _any_content_ref(target_protocol_id, "Fiat-Shamir Protocol")),
            (2, _any_content_ref(shared_core_id, "shared Core")),
            (
                3,
                _any_content_ref(
                    transcript_construction_id,
                    "transcript construction",
                ),
            ),
            (4, result_schema_body),
            (
                5,
                _any_content_ref(
                    checker_contract_id,
                    "checked-construction checker contract",
                ),
            ),
        )
    )


def _checked_fs_binding_payload_local_body(
    result: CheckedFSConstruction,
    profile: object,
) -> object:
    return _checked_construction_binding_payload_local_body(
        result.source_protocol_id,
        result.target_protocol_id,
        result.shared_core_id,
        result.transcript_construction_id,
        profile,
        PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        _checked_fs_result_schema_body(),
    )


def check_fs_construction(
    source_core: Core,
    target_core: Core,
    construction: TranscriptConstruction,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.transcript_fs,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset(
                    {
                        "pir.checker-contract",
                        "pir.protocol",
                        "pir.transcript-construction",
                    }
                )
            ),
        )
        admit_core(source_core)
        admit_core(target_core)
        construction.admit()
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except ModelError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    defects: list[FSConstructionDefect] = []
    source_core_id = core_id(source_core, profiles=profiles)
    target_core_id = core_id(target_core, profiles=profiles)
    if source_core_id != target_core_id:
        defects.append(FSConstructionDefect.SHARED_CORE_MISMATCH)
    if not is_public_coin_eligible(source_core) or not is_public_coin_eligible(target_core):
        defects.append(FSConstructionDefect.PUBLIC_COIN_INELIGIBLE)
    if defects:
        return QualifiedViewOutcome(
            QualifiedViewOutcomeKind.NEGATIVE,
            detail=tuple(defects),
        )
    source_protocol = protocol_id(
        source_core,
        None,
        ChallengeInterpretation.FRESH,
        profiles=profiles,
    )
    target_protocol = protocol_id(
        target_core,
        construction,
        ChallengeInterpretation.FIAT_SHAMIR,
        profiles=profiles,
    )
    _authenticate_k2_profiled_subject(
        target_protocol,
        "pir.protocol",
        protocol_body(
            target_core,
            construction,
            ChallengeInterpretation.FIAT_SHAMIR,
            profiles=profiles,
        ),
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profiles.transcript_fs,
    )
    transcript_construction_id = construction_id(
        source_core,
        construction,
        profiles=profiles,
    )
    _authenticate_k2_profiled_subject(
        transcript_construction_id,
        "pir.transcript-construction",
        construction_body(source_core, construction, profiles=profiles),
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profiles.transcript_fs,
    )
    checker_contract_body = _checked_construction_checker_contract_body(
        profiles.transcript_fs,
        PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        _checked_fs_result_schema_body(),
    )
    _authenticate_k2_profiled_subject(
        _checked_fs_checker_contract_id(profiles.transcript_fs),
        "pir.checker-contract",
        checker_contract_body,
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profiles.transcript_fs,
    )
    challenges = tuple(
        item.name
        for item in source_core.schedule
        if item.kind is OccurrenceKind.CHALLENGE
    )
    occurrences = tuple(item.name for item in source_core.schedule)
    nonchallenge_values = tuple(item.name for item in source_core.inputs) + tuple(
        item.name
        for item in source_core.schedule
        if item.kind is not OccurrenceKind.CHALLENGE
    )
    result = CheckedFSConstruction(
        source_protocol,
        target_protocol,
        source_core_id,
        transcript_construction_id,
        tuple((name, name) for name in occurrences),
        tuple((name, name) for name in nonchallenge_values),
        tuple((name, name) for name in challenges),
    )
    result_ref = object()
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _authority_components(
        profiles.transcript_fs,
        PIRSourceFamily.CHECKED_CONSTRUCTION,
        "checked-fs-construction",
        _checked_fs_binding_payload_local_body(
            result,
            profiles.transcript_fs,
        ),
        "issue-fs-construction-view",
        consumer_id,
        purpose_id,
        profiles=profiles,
        profile_support=profile_support,
    )
    binding = k1.OwnerLocalSourceAuthorityBinding(
        k1.Symbol("pir"),
        k1.Symbol("checked-fs-construction"),
        result_ref,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    k1.validate_owner_local_source_authority_binding(binding)
    capability = CheckedFSConstructionCapability(
        result_ref,
        result,
        binding,
        consumer_id,
        purpose_id,
        (source_core, target_core, construction),
        _FS_CONSTRUCTION_CHECK_ISSUER,
    )
    _FS_CONSTRUCTION_LIVE_CAPABILITIES[id(capability)] = capability
    issued = CheckedFSConstructionIssue(
        result_ref,
        result,
        binding,
        capability,
        _FS_CONSTRUCTION_CHECK_ISSUER,
    )
    _FS_CONSTRUCTION_LIVE_ISSUES[id(issued)] = issued
    return QualifiedViewOutcome(
        QualifiedViewOutcomeKind.AFFIRMATIVE,
        issued,
    )


def issue_fs_construction_view(
    checked: object,
    manifest: tuple[StaticViewField, ...],
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
    view_consumer_id: object | None = None,
    view_purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    if type(checked) is not CheckedFSConstructionIssue:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MISSING_DEPENDENCY)
    consumer_id = (
        checked.capability.consumer_id
        if expected_consumer_id is None
        else expected_consumer_id
    )
    purpose_id = (
        checked.capability.purpose_id
        if expected_purpose_id is None
        else expected_purpose_id
    )
    if (
        _FS_CONSTRUCTION_LIVE_ISSUES.get(id(checked)) is not checked
        or checked._issuer is not _FS_CONSTRUCTION_CHECK_ISSUER
        or type(checked.capability) is not CheckedFSConstructionCapability
        or _FS_CONSTRUCTION_LIVE_CAPABILITIES.get(id(checked.capability))
        is not checked.capability
        or checked.capability._issuer is not _FS_CONSTRUCTION_CHECK_ISSUER
        or checked.capability.result_ref is not checked.result_ref
        or checked.capability.result is not checked.result
        or checked.capability.source_binding is not checked.source_binding
        or checked.capability.consumer_id != consumer_id
        or checked.capability.purpose_id != purpose_id
        or type(checked.source_binding) is not k1.OwnerLocalSourceAuthorityBinding
        or checked.source_binding.owner_local_coordinate is not checked.result_ref
    ):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.transcript_fs,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset(
                    {
                        "pir.checker-contract",
                        "pir.protocol",
                        "pir.transcript-construction",
                    }
                )
            ),
        )
        k1.validate_owner_local_source_authority_binding(checked.source_binding)
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _authority_components(
            profiles.transcript_fs,
            PIRSourceFamily.CHECKED_CONSTRUCTION,
            "checked-fs-construction",
            _checked_fs_binding_payload_local_body(
                checked.result,
                profiles.transcript_fs,
            ),
            "issue-fs-construction-view",
            consumer_id,
            purpose_id,
            profiles=profiles,
            profile_support=profile_support,
        )
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except MalformedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    except (ModelError, k1.ModelError, k1.CanonicalError):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    binding = checked.source_binding
    if not (
        binding.owner_domain == k1.Symbol("pir")
        and binding.capability_family == k1.Symbol("checked-fs-construction")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    ):
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    result = checked.result
    payload = MappingProxyType(
        {
            StaticViewField.FS_RESULT_REF: checked.result_ref,
            StaticViewField.FS_RESULT_SCHEMA: CheckedFSConstruction,
            StaticViewField.FS_SOURCE_PROTOCOL: result.source_protocol_id,
            StaticViewField.FS_TARGET_PROTOCOL: result.target_protocol_id,
            StaticViewField.FS_SHARED_CORE: result.shared_core_id,
            StaticViewField.FS_CONSTRUCTION_ID: result.transcript_construction_id,
            StaticViewField.FS_MAPS: (
                result.occurrence_map,
                result.value_map,
                result.challenge_map,
            ),
            StaticViewField.FS_CONCLUSION: result.conclusion,
        }
    )
    coordinate = StaticViewCoordinate(
        StaticViewOwnerKind.FS_RESULT,
        checked.result_ref,
        StaticViewKind.FS_CONSTRUCTION,
        profiles.transcript_fs.identity,
    )
    return _issue_static_projection(
        coordinate,
        manifest,
        payload,
        checked,
        profiles=profiles,
        profile_support=profile_support,
        consumer_id=view_consumer_id,
        purpose_id=view_purpose_id,
    )


@dataclass(frozen=True)
class PublicSetupBindingRef:
    scope: str
    input_name: str


@dataclass(frozen=True)
class PublicSetupInvocationEntry:
    binding_ref: PublicSetupBindingRef
    role: InputRole
    value_sort: ValueSort
    value: Value


@dataclass(frozen=True)
class PublicSetupInvocationView:
    protocol_id: object
    core_id: object
    entries: tuple[PublicSetupInvocationEntry, ...]
    run_established: tuple[PublicSetupBindingRef, ...]


ExactPublicSetupInvocationViewAuthorityBinding = k1.PortableSourceAuthorityBinding


_PUBLIC_SETUP_VIEW_ISSUER = object()
_PUBLIC_SETUP_LIVE_CAPABILITIES: dict[int, object] = {}
_PUBLIC_SETUP_LIVE_ISSUANCES: dict[int, object] = {}


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class PublicSetupInvocationViewCapability(_NonTransferableAuthority):
    view_id: object
    view: PublicSetupInvocationView
    source_binding: k1.PortableSourceAuthorityBinding
    consumer_id: object
    purpose_id: object
    _invocation: Invocation
    _issuer: object

    def __post_init__(self) -> None:
        if self._issuer is not _PUBLIC_SETUP_VIEW_ISSUER:
            raise ModelError("only PIR may issue a public-setup view capability")


@dataclass(frozen=True, eq=False, repr=False)
class IssuedPublicSetupInvocationView(_NonTransferableAuthority):
    view_id: object
    view: PublicSetupInvocationView
    source_binding: k1.PortableSourceAuthorityBinding
    capability: PublicSetupInvocationViewCapability
    _issuer: object


def public_setup_invocation_view_body(view: PublicSetupInvocationView) -> bytes:
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, _content_ref_datum(view.protocol_id, "pir.protocol")),
                (1, _content_ref_datum(view.core_id, "pir.interactive-core")),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, _symbol(item.binding_ref.scope, "setup scope")),
                                    (1, _symbol(item.binding_ref.input_name, "setup input")),
                                    (
                                        2,
                                        k1.DatumVariant(
                                            0 if item.role is InputRole.PUBLIC_CONTEXT else 1,
                                            k1.UNIT,
                                        ),
                                    ),
                                    (3, _symbol(item.value_sort.value, "setup value sort")),
                                    (4, _datum(item.value)),
                                )
                            )
                            for item in view.entries
                        )
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            _symbol(item.input_name, "run-established binding")
                            for item in view.run_established
                        )
                    ),
                ),
            )
        )
    )


def public_setup_invocation_view_id(
    view: PublicSetupInvocationView,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> object:
    return _profiled_identity(
        "pir.public-setup-invocation-view",
        profiles.public_view,
        public_setup_invocation_view_body(view),
    )


def _public_setup_binding_payload_local_body(
    view_id: object,
    view: PublicSetupInvocationView,
) -> object:
    return k1.DatumRecord(
        (
            (0, _any_content_ref(view_id, "public-setup view")),
            (1, _any_content_ref(view.protocol_id, "public-setup protocol")),
        )
    )


def issue_public_setup_invocation_view(
    core: Core,
    construction: TranscriptConstruction | None,
    interpretation: ChallengeInterpretation,
    invocation: Invocation,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    consumer_id: object | None = None,
    purpose_id: object | None = None,
) -> QualifiedViewOutcome:
    try:
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.public_view,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"pir.public-setup-invocation-view"})
            ),
        )
        values = admit_invocation(core, invocation)
        pid = protocol_id(
            core,
            construction,
            interpretation,
            profiles=profiles,
        )
    except UnsupportedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.UNSUPPORTED)
    except RefusedSemanticProfileError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.REFUSED)
    except ModelError:
        return QualifiedViewOutcome(QualifiedViewOutcomeKind.MALFORMED)
    entries = tuple(
        PublicSetupInvocationEntry(
            PublicSetupBindingRef(item.scope, item.name),
            item.role,
            item.value_sort,
            values[item.name],
        )
        for item in core.inputs
        if item.role in {InputRole.PUBLIC_CONTEXT, InputRole.PUBLIC_PARAMETER}
    )
    # This bounded Schnorr carrier represents public bindings only as invocation
    # inputs, so every covered binding is invocation-determined.  The authored
    # body nevertheless carries the complementary sequence explicitly.
    view = PublicSetupInvocationView(
        pid,
        core_id(core, profiles=profiles),
        entries,
        (),
    )
    view_id = public_setup_invocation_view_id(view, profiles=profiles)
    _authenticate_k2_profiled_subject(
        view_id,
        "pir.public-setup-invocation-view",
        public_setup_invocation_view_body(view),
        profiles=profiles,
        profile_support=profile_support,
        selected_profile=profiles.public_view,
    )
    (
        consumer_id,
        purpose_id,
        payload_id,
        no_policy_id,
        closure_id,
        requirement,
    ) = _authority_components(
        profiles.public_view,
        PIRSourceFamily.PUBLIC_SETUP_INVOCATION_VIEW,
        "public-setup-invocation-view",
        _public_setup_binding_payload_local_body(view_id, view),
        "consume-public-setup-invocation-view",
        consumer_id,
        purpose_id,
        profiles=profiles,
        profile_support=profile_support,
    )
    binding = k1.PortableSourceAuthorityBinding(
        k1.Symbol("pir"),
        k1.Symbol("public-setup-invocation-view"),
        view_id,
        payload_id,
        k1.OwnerDefinesNoOperationPolicy(no_policy_id),
        closure_id,
        requirement,
    )
    binding.body()
    capability = PublicSetupInvocationViewCapability(
        view_id,
        view,
        binding,
        consumer_id,
        purpose_id,
        invocation,
        _PUBLIC_SETUP_VIEW_ISSUER,
    )
    _PUBLIC_SETUP_LIVE_CAPABILITIES[id(capability)] = capability
    issued = IssuedPublicSetupInvocationView(
        view_id,
        view,
        binding,
        capability,
        _PUBLIC_SETUP_VIEW_ISSUER,
    )
    _PUBLIC_SETUP_LIVE_ISSUANCES[id(issued)] = issued
    return QualifiedViewOutcome(
        QualifiedViewOutcomeKind.AFFIRMATIVE,
        issued,
    )


def validate_issued_public_setup_invocation_view(
    issued: object,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
    profile_support: K2SemanticProfileSupport = K2_PROFILE_SUPPORT,
    expected_consumer_id: object | None = None,
    expected_purpose_id: object | None = None,
) -> bool:
    """Validate portable metadata plus the exact live PIR bearer capability."""

    if (
        type(issued) is not IssuedPublicSetupInvocationView
        or _PUBLIC_SETUP_LIVE_ISSUANCES.get(id(issued)) is not issued
        or issued._issuer is not _PUBLIC_SETUP_VIEW_ISSUER
        or type(issued.capability) is not PublicSetupInvocationViewCapability
        or _PUBLIC_SETUP_LIVE_CAPABILITIES.get(id(issued.capability))
        is not issued.capability
        or issued.capability._issuer is not _PUBLIC_SETUP_VIEW_ISSUER
        or issued.capability.view_id is not issued.view_id
        or issued.capability.view is not issued.view
        or issued.capability.source_binding is not issued.source_binding
        or type(issued.source_binding) is not k1.PortableSourceAuthorityBinding
        or issued.source_binding.owner_source_coordinate != issued.view_id
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
        _require_supported_k2_profiles(
            profiles,
            profile_support,
            profiles.public_view,
            required_subject_kinds=(
                _PIR_SOURCE_AUTHORITY_SUBJECT_KINDS
                | frozenset({"pir.public-setup-invocation-view"})
            ),
        )
        issued.source_binding.body()
        (
            _,
            _,
            payload_id,
            no_policy_id,
            closure_id,
            requirement,
        ) = _authority_components(
            profiles.public_view,
            PIRSourceFamily.PUBLIC_SETUP_INVOCATION_VIEW,
            "public-setup-invocation-view",
            _public_setup_binding_payload_local_body(
                issued.view_id,
                issued.view,
            ),
            "consume-public-setup-invocation-view",
            consumer_id,
            purpose_id,
            profiles=profiles,
            profile_support=profile_support,
        )
    except (ModelError, k1.ModelError, k1.CanonicalError):
        return False
    binding = issued.source_binding
    return (
        binding.owner_domain == k1.Symbol("pir")
        and binding.capability_family
        == k1.Symbol("public-setup-invocation-view")
        and binding.owner_binding_payload == payload_id
        and type(binding.operation_policy) is k1.OwnerDefinesNoOperationPolicy
        and binding.operation_policy.owner_no_policy_declaration == no_policy_id
        and binding.owner_policy_closure == closure_id
        and binding.capability_requirement == requirement
    )


def _frame_bytes(body: bytes) -> bytes:
    if type(body) is not bytes:
        raise ModelError("transcript framing accepts exact bytes")
    return len(body).to_bytes(8, "big") + body


def _initial_state() -> bytes:
    return INITIAL_TRANSCRIPT_STATE


def _atom(kind: str, *coordinates: str) -> InfluenceAtom:
    _symbol(kind, "influence kind")
    for coordinate in coordinates:
        _symbol(coordinate, "influence coordinate")
    return InfluenceAtom(kind, tuple(coordinates))


def _atom_bytes(atom: InfluenceAtom) -> bytes:
    if type(atom) is not InfluenceAtom or type(atom.coordinates) is not tuple:
        raise ModelError("influence atom has the wrong exact carrier")
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, _symbol(atom.kind, "influence kind")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _symbol(item, "influence coordinate")
                            for item in atom.coordinates
                        )
                    ),
                ),
            )
        )
    )


def _absorb(state: bytes, frame: Frame) -> bytes:
    if type(state) is not bytes or len(state) != 32:
        raise ModelError("transcript state must be 32 exact octets")
    return hashlib.sha256(
        _frame_bytes(b"k2/absorb/v1")
        + _frame_bytes(state)
        + _frame_bytes(_atom_bytes(frame.atom))
        + _frame_bytes(frame.payload)
    ).digest()


def derive_occurrence_namespace(
    core: Core,
    construction: TranscriptConstruction,
    ordinal: int,
    draw_ordinal: int = 0,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> bytes:
    """Derive a collision-free canonical occurrence namespace.

    The namespace is the exact framed tuple, not an author-supplied label and
    not merely a digest.  Its two typed references and schedule ordinal make
    equality equivalent to equality of the complete tuple.
    """

    admit_core(core)
    construction.admit()
    if type(ordinal) is not int or not 0 <= ordinal < len(core.schedule):
        raise AdmissionError("challenge ordinal is outside the exact schedule")
    if (
        type(draw_ordinal) is not int
        or not 0 <= draw_ordinal < construction.max_attempts
    ):
        raise AdmissionError("draw ordinal is outside the construction bound")
    occurrence = core.schedule[ordinal]
    if occurrence.kind is not OccurrenceKind.CHALLENGE:
        raise AdmissionError("only a challenge occurrence has a squeeze namespace")
    scope_index = {scope.name: index for index, scope in enumerate(core.scopes)}
    scope_by_name = {scope.name: scope for scope in core.scopes}
    path: list[int] = []
    current: str | None = occurrence.scope
    while current is not None:
        path.append(scope_index[current])
        current = scope_by_name[current].parent
    path.reverse()
    assert occurrence.challenge_domain is not None
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (
                    0,
                    k1.BytesValue(
                        core_id(core, profiles=profiles).internal_reference()
                    ),
                ),
                (
                    1,
                    k1.BytesValue(
                        construction_id(
                            core,
                            construction,
                            profiles=profiles,
                        ).internal_reference()
                    ),
                ),
                (2, k1.DatumSeq(tuple(k1.Nat(index) for index in path))),
                (3, k1.Nat(ordinal)),
                (4, k1.Nat(draw_ordinal)),
                (5, k1.Nat(occurrence.challenge_domain.modulus)),
            )
        )
    )


def _squeeze_block(state: bytes, namespace: bytes, requested_bytes: int) -> bytes:
    if type(requested_bytes) is not int or not 1 <= requested_bytes <= 32:
        raise AdmissionError("requested squeeze length is outside the fixture bound")
    return hashlib.sha256(
        _frame_bytes(b"k2/squeeze/v0")
        + _frame_bytes(state)
        + _frame_bytes(namespace)
        + _frame_bytes(requested_bytes.to_bytes(8, "big"))
    ).digest()[:requested_bytes]


def _advance_state(
    state: bytes,
    namespace: bytes,
    requested_bytes: int,
    block: bytes,
) -> bytes:
    return hashlib.sha256(
        _frame_bytes(b"k2/advance/v0")
        + _frame_bytes(state)
        + _frame_bytes(namespace)
        + _frame_bytes(requested_bytes.to_bytes(8, "big"))
        + _frame_bytes(block)
    ).digest()


def squeeze_and_sample(
    state: bytes,
    core: Core,
    occurrence_ordinal: int,
    domain: ChallengeDomain,
    construction: TranscriptConstruction,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> ChallengeSample:
    construction.admit()
    if type(state) is not bytes or len(state) != construction.state_bytes:
        raise AdmissionError("squeeze state has the wrong exact carrier")
    if (
        type(occurrence_ordinal) is not int
        or not 0 <= occurrence_ordinal < len(core.schedule)
        or core.schedule[occurrence_ordinal].kind is not OccurrenceKind.CHALLENGE
    ):
        raise AdmissionError("sampling must name one exact challenge occurrence")
    if domain != core.schedule[occurrence_ordinal].challenge_domain:
        raise AdmissionError("sampling domain must equal the Core challenge domain")
    if type(domain) is not ChallengeDomain or type(domain.modulus) is not int or domain.modulus <= 1:
        raise AdmissionError("invalid challenge sampling domain")
    width = construction.sample_bytes
    space = 1 << (8 * width)
    if domain.modulus > space:
        raise AdmissionError("challenge modulus exceeds the exact sample word")
    accept_below = space - (space % domain.modulus)
    current = state
    namespaces: list[bytes] = []
    for attempt in range(construction.max_attempts):
        namespace = derive_occurrence_namespace(
            core,
            construction,
            occurrence_ordinal,
            attempt,
            profiles=profiles,
        )
        namespaces.append(namespace)
        block = _squeeze_block(current, namespace, width)
        if len(block) != width:
            raise AdmissionError("squeeze output length differs from requested length")
        current = _advance_state(current, namespace, width, block)
        raw = int.from_bytes(block[:width], "big")
        if raw < accept_below:
            return ChallengeSample(
                raw % domain.modulus,
                current,
                attempt + 1,
                tuple(namespaces),
            )
    raise SamplingExhausted(tuple(namespaces), current, construction.max_attempts)


def _value_bytes(value: Value) -> bytes:
    return k1.encode_datum(_datum(value))


def _scope_openings(core: Core) -> Mapping[str | None, tuple[ScopeDecl, ...]]:
    result: dict[str | None, list[ScopeDecl]] = {}
    for scope in core.scopes:
        result.setdefault(scope.open_before, []).append(scope)
    return MappingProxyType({key: tuple(value) for key, value in result.items()})


def required_influence_kinds(occurrence: Occurrence) -> tuple[str, ...]:
    """Return derived value influence; callers cannot remove these classes."""

    if occurrence.kind in {
        OccurrenceKind.PROVER_MESSAGE,
        OccurrenceKind.ORACLE_PUBLISH,
        OccurrenceKind.ORACLE_QUERY,
        OccurrenceKind.ORACLE_ANSWER,
    }:
        return (occurrence.kind.value,)
    if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
        return (occurrence.kind.value,)
    return ()


def _occurrence_atom(occurrence: Occurrence) -> InfluenceAtom | None:
    kinds = required_influence_kinds(occurrence)
    return None if not kinds else _atom(kinds[0], occurrence.name)


def _draw_atom(entry: RunEntry, ordinal: int, namespace: bytes) -> InfluenceAtom:
    return _atom("challenge-draw", entry.occurrence, str(ordinal), namespace.hex())


def extract_influence_atoms(
    frames: tuple[Frame, ...],
    prior_entries: tuple[RunEntry, ...] = (),
    core: Core | None = None,
) -> tuple[InfluenceAtom, ...]:
    """Extract the finite observed influence trace from an exact run prefix."""

    frame_atoms: list[InfluenceAtom] = []
    for frame in frames:
        if type(frame) is not Frame or frame.tag != frame.atom.kind:
            raise ReplayError("transcript frame and influence atom disagree")
        _atom_bytes(frame.atom)
        frame_atoms.append(frame.atom)

    draw_atoms = tuple(
        (entry_index, _draw_atom(entry, ordinal, namespace))
        for entry_index, entry in enumerate(prior_entries)
        for ordinal, namespace in enumerate(entry.draw_namespaces)
    )
    if core is None or not draw_atoms:
        atoms = frame_atoms + [atom for _, atom in draw_atoms]
    else:
        occurrence_index = {
            occurrence.name: index for index, occurrence in enumerate(core.schedule)
        }
        scope_index = {
            scope.name: (
                -1
                if scope.open_before is None
                else occurrence_index[scope.open_before]
            )
            for scope in core.scopes
        }

        def frame_rank(atom: InfluenceAtom) -> int:
            if atom.kind in {
                "core-header",
                "construction-header",
                "application-domain",
            }:
                return -1
            if atom.kind in {
                "scope-open",
                InputRole.STATEMENT.value,
                InputRole.PUBLIC_CONTEXT.value,
                InputRole.PUBLIC_PARAMETER.value,
            }:
                return scope_index[atom.coordinates[0]]
            return occurrence_index[atom.coordinates[0]]

        atoms = []
        draw_index = 0
        for atom in frame_atoms:
            rank = frame_rank(atom)
            while (
                draw_index < len(draw_atoms)
                and draw_atoms[draw_index][0] < rank
            ):
                atoms.append(draw_atoms[draw_index][1])
                draw_index += 1
            atoms.append(atom)
        atoms.extend(atom for _, atom in draw_atoms[draw_index:])
    if len(atoms) != len(set(atoms)):
        raise ReplayError("duplicate transcript influence atom")
    return tuple(atoms)


def required_influence_atoms(
    core: Core,
    construction: TranscriptConstruction,
    challenge_ordinal: int,
    prior_entries: tuple[RunEntry, ...],
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> tuple[InfluenceAtom, ...]:
    """Derive all finite obligations for one challenge from Core structure."""

    occurrence = core.schedule[challenge_ordinal]
    if occurrence.kind is not OccurrenceKind.CHALLENGE:
        raise AdmissionError("required influence is defined only for challenges")
    required: list[InfluenceAtom] = [
        _atom(
            "core-header",
            core_id(core, profiles=profiles).internal_reference().hex(),
        ),
        _atom(
            "construction-header",
            construction_id(
                core,
                construction,
                profiles=profiles,
            ).internal_reference().hex(),
        ),
        _atom("application-domain", construction.application_domain.hex()),
    ]
    scopes_by_opening = _scope_openings(core)

    def append_scope_openings(open_before: str | None) -> None:
        for scope in scopes_by_opening.get(open_before, ()):
            required.append(_atom("scope-open", scope.name))
            required.extend(
                _atom(item.role.value, item.scope, item.name)
                for item in core.inputs
                if item.scope == scope.name
                and item.role
                in {
                    InputRole.STATEMENT,
                    InputRole.PUBLIC_CONTEXT,
                    InputRole.PUBLIC_PARAMETER,
                }
            )

    append_scope_openings(None)
    by_name = {item.name: item for item in core.schedule}
    for entry in prior_entries:
        prior = by_name[entry.occurrence]
        append_scope_openings(prior.name)
        if prior.guard.kind is not PredicateKind.ALWAYS:
            required.append(
                _atom(
                    "guard-outcome",
                    prior.name,
                    "executed" if entry.status is EntryStatus.EXECUTED else "skipped",
                )
            )
        if entry.status is EntryStatus.EXECUTED:
            atom = _occurrence_atom(prior)
            if atom is not None:
                required.append(atom)
            required.extend(
                _draw_atom(entry, ordinal, namespace)
                for ordinal, namespace in enumerate(entry.draw_namespaces)
            )
    append_scope_openings(occurrence.name)
    if occurrence.guard.kind is not PredicateKind.ALWAYS:
        required.append(_atom("guard-outcome", occurrence.name, "executed"))
    required.extend(
        _atom("challenge-condition", occurrence.name, ref.kind.value, ref.name)
        for ref in occurrence.dependencies
    )
    for reduction in core.reductions:
        for publication in reduction.required_publications:
            if publication.next_challenge == occurrence.name:
                atom = _occurrence_atom(by_name[publication.publication])
                assert atom is not None
                required.append(atom)
    return tuple(dict.fromkeys(required))


def compare_influence(
    required: tuple[InfluenceAtom, ...],
    observed: tuple[InfluenceAtom, ...],
) -> InfluenceComparison:
    if len(required) != len(set(required)):
        raise ReplayError("duplicate required transcript influence atom")
    if len(observed) != len(set(observed)):
        raise ReplayError("duplicate transcript influence atom")

    # Greedily match the required trace in its declared order.  Extra observed
    # atoms are allowed, but an atom seen only before its required predecessor
    # cannot be reused after that predecessor and is therefore reported
    # missing.  This is an ordered-subtrace check, not set containment.
    observed_index = 0
    missing: list[InfluenceAtom] = []
    for required_atom in required:
        while (
            observed_index < len(observed)
            and observed[observed_index] != required_atom
        ):
            observed_index += 1
        if observed_index == len(observed):
            missing.append(required_atom)
        else:
            observed_index += 1

    return InfluenceComparison(
        required,
        observed,
        tuple(missing),
    )


# ---------------------------------------------------------------------------
# Causal generation and noncausal replay
# ---------------------------------------------------------------------------


class ProverView:
    """The only protocol-owned strategy input: current, finite, prefix-only."""

    __slots__ = ("_ordinal", "_public", "_history", "_index")

    def __init__(
        self,
        ordinal: int,
        public_values: Mapping[str, Value],
        history: tuple[RunEntry, ...],
        occurrence_index: Mapping[str, int],
    ) -> None:
        self._ordinal = ordinal
        self._public = MappingProxyType(dict(public_values))
        self._history = history
        self._index = MappingProxyType(dict(occurrence_index))

    def public_input(self, name: str) -> Value:
        if name not in self._public:
            raise FutureReadError(f"input {name!r} is not public to the strategy")
        return self._public[name]

    def read_occurrence(self, name: str) -> Value:
        index = self._index.get(name)
        if index is None or index >= self._ordinal:
            raise FutureReadError(f"occurrence {name!r} is not in the current prefix")
        entry = self._history[index]
        if entry.status is EntryStatus.SKIPPED or entry.value is None:
            raise FutureReadError(f"occurrence {name!r} has no visible value")
        return entry.value

    @property
    def visible_prefix(self) -> tuple[RunEntry, ...]:
        return self._history


def _resolve(ref: ValueRef, values: Mapping[ValueRef, Value]) -> Value:
    try:
        return values[ref]
    except KeyError as error:
        raise ExecutionError(f"dependency {ref.kind.value}:{ref.name} has no value") from error


def _predicate(predicate: Predicate, values: Mapping[ValueRef, Value]) -> bool:
    resolved = tuple(_resolve(ref, values) for ref in predicate.refs)
    if predicate.kind is PredicateKind.ALWAYS:
        return True
    if predicate.kind is PredicateKind.NEVER:
        return False
    if predicate.kind is PredicateKind.BOOL:
        if type(resolved[0]) is not bool:
            raise ExecutionError("Bool fixture predicate received a nonboolean")
        return resolved[0]
    if predicate.kind is PredicateKind.BYTES_EQUAL:
        return type(resolved[0]) is bytes and type(resolved[1]) is bytes and resolved[0] == resolved[1]
    if predicate.kind is PredicateKind.SCHNORR:
        if any(type(value) is not int for value in resolved):
            raise ExecutionError("Schnorr fixture predicate expects six integers")
        g, statement, commitment, challenge, response, modulus = resolved
        (order,) = predicate.parameters
        if modulus <= 2 or order <= 1:
            raise ExecutionError("invalid Schnorr fixture parameters")
        return pow(g, response % order, modulus) == (
            commitment * pow(statement, challenge % order, modulus)
        ) % modulus
    if predicate.kind is PredicateKind.LEADING_ZERO_BITS:
        value = resolved[0]
        bits = predicate.parameters[0]
        if type(value) is not bytes or not 0 <= bits <= 256:
            raise ExecutionError("invalid grinding fixture input")
        digest = hashlib.sha256(value).digest()
        return int.from_bytes(digest, "big") < (1 << (256 - bits))
    raise ExecutionError("unsupported fixture predicate")


def _core_reference_sorts(core: Core) -> Mapping[ValueRef, ValueSort]:
    """Return the exact admitted sort of every Core value reference."""

    admit_core(core)
    sorts: dict[ValueRef, ValueSort] = {
        ValueRef.input(item.name): item.value_sort for item in core.inputs
    }
    for occurrence in core.schedule:
        sorts[ValueRef.occurrence(occurrence.name)] = _occurrence_sort(
            occurrence, sorts
        )
    return MappingProxyType(sorts)


def _resolve_occurrence_ref(
    core: Core,
    occurrence_ref: ValueRef,
    expected_kind: OccurrenceKind,
) -> Occurrence:
    if (
        type(occurrence_ref) is not ValueRef
        or occurrence_ref.kind is not RefKind.OCCURRENCE
    ):
        raise ExecutionError("occurrence evaluation needs one exact occurrence ref")
    selected = tuple(
        occurrence
        for occurrence in core.schedule
        if occurrence.name == occurrence_ref.name
        and occurrence.kind is expected_kind
    )
    if len(selected) != 1:
        raise ExecutionError(
            f"occurrence ref does not select one admitted {expected_kind.value}"
        )
    return selected[0]


def _admit_exact_predicate_substitution(
    core: Core,
    predicates: tuple[Predicate, ...],
    substitution: Mapping[ValueRef, Value],
) -> Mapping[ValueRef, Value]:
    if not isinstance(substitution, Mapping):
        raise ExecutionError("predicate substitution must be one exact mapping")
    required = tuple(
        dict.fromkeys(ref for predicate in predicates for ref in predicate.refs)
    )
    supplied = tuple(substitution)
    if len(supplied) != len(required) or set(supplied) != set(required):
        raise ExecutionError(
            "predicate substitution must cover exactly its authenticated refs"
        )
    sorts = _core_reference_sorts(core)
    result: dict[ValueRef, Value] = {}
    for ref in required:
        if type(ref) is not ValueRef or ref not in sorts:
            raise ExecutionError("predicate substitution contains an unknown ref")
        value = substitution[ref]
        if not _sort_accepts(value, sorts[ref]):
            raise ExecutionError("predicate substitution value has the wrong Core sort")
        _datum(value)
        result[ref] = value
    return MappingProxyType(result)


def evaluate_check_ref(
    core: Core,
    check_ref: ValueRef,
    substitution: Mapping[ValueRef, Value],
) -> bool | None:
    """Evaluate one admitted Check under its exact closed substitution.

    ``None`` is the exact skipped result when the authenticated occurrence
    guard is false.  No relation predicate or external judgment is consulted.
    """

    admit_core(core)
    occurrence = _resolve_occurrence_ref(core, check_ref, OccurrenceKind.CHECK)
    assert occurrence.check_predicate is not None
    values = _admit_exact_predicate_substitution(
        core,
        (occurrence.guard, occurrence.check_predicate),
        substitution,
    )
    if not _predicate(occurrence.guard, values):
        return None
    return _predicate(occurrence.check_predicate, values)


def evaluate_terminal_ref(
    core: Core,
    terminal_ref: ValueRef,
    prior_check_outcomes: Mapping[ValueRef, bool | None],
    substitution: Mapping[ValueRef, Value],
) -> bool | None:
    """Apply the admitted terminal law to every prior Check outcome.

    The check map is exact and complete.  ``None`` denotes a skipped Check or,
    for the return value, a skipped terminal.  As in generated protocol execution,
    skipped checks do not make an executed terminal reject.
    """

    admit_core(core)
    terminal = _resolve_occurrence_ref(
        core, terminal_ref, OccurrenceKind.TERMINAL
    )
    terminal_ordinal = next(
        ordinal
        for ordinal, occurrence in enumerate(core.schedule)
        if occurrence is terminal
    )
    required_checks = tuple(
        ValueRef.occurrence(occurrence.name)
        for occurrence in core.schedule[:terminal_ordinal]
        if occurrence.kind is OccurrenceKind.CHECK
    )
    if not isinstance(prior_check_outcomes, Mapping):
        raise ExecutionError("terminal check outcomes must be one exact mapping")
    supplied = tuple(prior_check_outcomes)
    if len(supplied) != len(required_checks) or set(supplied) != set(required_checks):
        raise ExecutionError(
            "terminal check outcomes must cover exactly every prior Check ref"
        )
    for outcome in prior_check_outcomes.values():
        if outcome is not None and type(outcome) is not bool:
            raise ExecutionError("terminal check outcome is not Boolean or skipped")
    values = _admit_exact_predicate_substitution(
        core,
        (terminal.guard,),
        substitution,
    )
    if not _predicate(terminal.guard, values):
        return None
    return all(
        outcome is True
        for outcome in (
            prior_check_outcomes[check_ref]
            for check_ref in required_checks
        )
        if outcome is not None
    )


def _verifier_value(rule: VerifierRule, dependencies: tuple[Value, ...]) -> Value:
    if rule.kind is VerifierRuleKind.COPY:
        if len(dependencies) != 1:
            raise ExecutionError("copy rule needs one dependency")
        return dependencies[0]
    if rule.kind is VerifierRuleKind.SHA256:
        if any(type(item) is not bytes for item in dependencies):
            raise ExecutionError("SHA-256 verifier rule accepts byte strings")
        return hashlib.sha256(b"".join(dependencies)).digest()
    if rule.kind is VerifierRuleKind.CONSTANT_INT:
        if dependencies or len(rule.parameters) != 1:
            raise ExecutionError("constant-int rule has one parameter and no dependency")
        return rule.parameters[0]
    raise ExecutionError("unsupported verifier rule")


def _append_frame(
    state: bytes,
    frames: list[Frame],
    tag: str,
    payload: bytes,
    *coordinates: str,
) -> bytes:
    frame = Frame(tag, payload, _atom(tag, *coordinates))
    frames.append(frame)
    return _absorb(state, frame)


def _open_scopes(
    core: Core,
    scopes: tuple[ScopeDecl, ...],
    invocation_values: Mapping[str, Value],
    state: bytes,
    frames: list[Frame],
) -> bytes:
    for scope in scopes:
        state = _append_frame(
            state,
            frames,
            "scope-open",
            scope.name.encode("ascii"),
            scope.name,
        )
        for item in core.inputs:
            if item.scope == scope.name and item.role in {
                InputRole.STATEMENT,
                InputRole.PUBLIC_CONTEXT,
                InputRole.PUBLIC_PARAMETER,
            }:
                state = _append_frame(
                    state,
                    frames,
                    item.role.value,
                    k1.encode_datum(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "public binding name")),
                                (1, _datum(invocation_values[item.name])),
                            )
                        )
                    ),
                    item.scope,
                    item.name,
                )
    return state


def _execute(
    core: Core,
    construction: TranscriptConstruction,
    interpretation: ChallengeInterpretation,
    invocation: Invocation,
    strategy: ProverStrategy | None,
    expected_record: RunRecord | None,
    fresh_resolver: FreshChallengeResolver | None,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> GenerationResult:
    admit_core(core)
    is_fs = interpretation is ChallengeInterpretation.FIAT_SHAMIR
    if is_fs:
        construction.admit()
        if not is_public_coin_eligible(core):
            raise AdmissionError(
                "Fiat--Shamir requires a derived public-coin-eligible Core"
            )
    inputs = admit_invocation(core, invocation)
    expected_entries = None if expected_record is None else expected_record.entries
    if expected_entries is not None and len(expected_entries) != len(core.schedule):
        raise ReplayError("record does not have one entry per scheduled occurrence")
    if expected_record is not None:
        extract_influence_atoms(
            expected_record.transcript_frames,
            expected_record.entries,
            core,
        )

    cid = core_id(core, profiles=profiles)
    tid = (
        construction_id(core, construction, profiles=profiles)
        if is_fs
        else None
    )
    iid = invocation_id(core, invocation, profiles=profiles)
    if expected_record is not None:
        if (
            expected_record.core_id != cid
            or expected_record.construction_id != tid
            or expected_record.invocation_id != iid
            or expected_record.interpretation is not interpretation
        ):
            raise ReplayError("record identity axes do not match this run request")

    state: bytes | None = None
    frames: list[Frame] = []
    openings = _scope_openings(core)
    root_scopes = openings.get(None, ())
    public_values: dict[str, Value] = {
        item.name: inputs[item.name]
        for item in core.inputs
        if item.role is not InputRole.VERIFIER_PRIVATE
        and item.scope in {scope.name for scope in root_scopes}
    }
    if is_fs:
        assert tid is not None
        state = _initial_state()
        state = _append_frame(
            state,
            frames,
            "core-header",
            cid.internal_reference(),
            cid.internal_reference().hex(),
        )
        state = _append_frame(
            state,
            frames,
            "construction-header",
            tid.internal_reference(),
            tid.internal_reference().hex(),
        )
        state = _append_frame(
            state,
            frames,
            "application-domain",
            construction.application_domain,
            construction.application_domain.hex(),
        )
        state = _open_scopes(
            core,
            root_scopes,
            inputs,
            state,
            frames,
        )

    value_map: dict[ValueRef, Value] = {
        ValueRef.input(name): value for name, value in inputs.items()
    }
    entries: list[RunEntry] = []
    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    oracles: dict[str, OracleObject] = {}

    for ordinal, occurrence in enumerate(core.schedule):
        due_scopes = openings.get(occurrence.name, ())
        for opened_scope in due_scopes:
            for item in core.inputs:
                if (
                    item.scope == opened_scope.name
                    and item.role is not InputRole.VERIFIER_PRIVATE
                ):
                    public_values[item.name] = inputs[item.name]
        if is_fs:
            assert state is not None
            state = _open_scopes(
                core,
                due_scopes,
                inputs,
                state,
                frames,
            )
        executed = _predicate(occurrence.guard, value_map)
        if is_fs and occurrence.guard.kind is not PredicateKind.ALWAYS:
            assert state is not None
            state = _append_frame(
                state,
                frames,
                "guard-outcome",
                k1.encode_datum(
                    k1.DatumRecord(
                        (
                            (0, _symbol(occurrence.name, "occurrence name")),
                            (1, executed),
                        )
                    )
                ),
                occurrence.name,
                "executed" if executed else "skipped",
            )
        if not executed:
            entry = RunEntry(occurrence.name, occurrence.kind, EntryStatus.SKIPPED, None)
            entries.append(entry)
            continue

        dependencies = tuple(_resolve(ref, value_map) for ref in occurrence.dependencies)
        prefix: bytes | None = None
        draw_namespaces: tuple[bytes, ...] = ()
        attempts: int | None = None
        influence: InfluenceComparison | None = None

        if occurrence.kind in {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.ORACLE_PUBLISH}:
            if expected_entries is not None:
                value = expected_entries[ordinal].value
                if value is None:
                    raise ReplayError("executed prover occurrence has no recorded value")
            else:
                assert strategy is not None
                view = ProverView(ordinal, public_values, tuple(entries), occurrence_index)
                try:
                    value = strategy.move(occurrence, view)
                except FutureReadError as error:
                    return Noncompletion(NoncompletionReason.FUTURE_READ, occurrence.name, str(error))
                except StrategyStopped as error:
                    return Noncompletion(NoncompletionReason.STRATEGY_STOPPED, occurrence.name, str(error))
                try:
                    _datum(value)
                except ModelError as error:
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, str(error))
            expected_sort = (
                ValueSort.ORACLE
                if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH
                else occurrence.prover_value_sort
            )
            if not _sort_accepts(value, expected_sort):
                if expected_entries is not None:
                    raise ReplayError("prover value does not match its declared sort")
                return Noncompletion(
                    NoncompletionReason.INVALID_MOVE,
                    occurrence.name,
                    "prover value does not match its declared sort",
                )
            if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH:
                if type(value) is not OracleObject:
                    if expected_entries is not None:
                        raise ReplayError("oracle publication is not an immutable oracle object")
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, "oracle publication needs OracleObject")
                if type(value.cells) is not tuple or not 1 <= len(value.cells) <= MAX_ORACLE_CELLS or any(
                    type(cell) is not bytes or len(cell) > MAX_CELL_BYTES for cell in value.cells
                ):
                    if expected_entries is not None:
                        raise ReplayError("oracle object violates finite cell bounds")
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, "oracle object violates finite cell bounds")
                assert occurrence.oracle_name is not None
                oracles[occurrence.oracle_name] = value
        elif occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
            assert occurrence.verifier_rule is not None
            value = _verifier_value(occurrence.verifier_rule, dependencies)
        elif occurrence.kind is OccurrenceKind.CHALLENGE:
            assert occurrence.challenge_domain is not None
            if interpretation is ChallengeInterpretation.FRESH:
                if expected_entries is not None:
                    value = expected_entries[ordinal].value
                    if type(value) is not int:
                        raise ReplayError("recorded Fresh challenge is not an exact integer")
                else:
                    if fresh_resolver is None:
                        raise FreshResolutionError(
                            "Fresh generation needs a resolver at each challenge"
                        )
                    value = fresh_resolver.resolve(
                        FreshChallengeRequest(
                            occurrence.name,
                            occurrence.challenge_domain,
                        )
                    )
                    if type(value) is not int:
                        raise FreshResolutionError(
                            "fresh resolver returned a non-integer challenge"
                        )
                if not 0 <= value < occurrence.challenge_domain.modulus:
                    error_type = ReplayError if expected_entries is not None else FreshResolutionError
                    raise error_type("Fresh challenge is outside the declared domain")
            else:
                assert state is not None
                for ref, dependency in zip(occurrence.dependencies, dependencies):
                    state = _append_frame(
                        state,
                        frames,
                        "challenge-condition",
                        k1.encode_datum(
                            k1.DatumRecord(
                                (
                                    (0, _ref_datum(ref)),
                                    (1, _datum(dependency)),
                                )
                            )
                        ),
                        occurrence.name,
                        ref.kind.value,
                        ref.name,
                    )
                observed = extract_influence_atoms(
                    tuple(frames),
                    tuple(entries),
                    core,
                )
                required = required_influence_atoms(
                    core,
                    construction,
                    ordinal,
                    tuple(entries),
                    profiles=profiles,
                )
                influence = compare_influence(required, observed)
                if influence.missing:
                    raise ExecutionError(
                        "required transcript influence is missing before challenge"
                    )
                prefix = state
                sample = squeeze_and_sample(
                    state,
                    core,
                    ordinal,
                    occurrence.challenge_domain,
                    construction,
                    profiles=profiles,
                )
                value = sample.value
                state = sample.state
                attempts = sample.attempts
                draw_namespaces = sample.namespaces
        elif occurrence.kind is OccurrenceKind.CHECK:
            assert occurrence.check_predicate is not None
            value = _predicate(occurrence.check_predicate, value_map)
        elif occurrence.kind is OccurrenceKind.TERMINAL:
            value = all(
                entry.value is True
                for entry in entries
                if entry.kind is OccurrenceKind.CHECK and entry.status is EntryStatus.EXECUTED
            )
        elif occurrence.kind is OccurrenceKind.ORACLE_QUERY:
            assert occurrence.oracle_name is not None
            oracle = oracles[occurrence.oracle_name]
            source = dependencies[0]
            if type(source) is not int:
                raise ExecutionError("native oracle query index source must be an integer")
            value = source % len(oracle.cells)
        elif occurrence.kind is OccurrenceKind.ORACLE_ANSWER:
            assert occurrence.oracle_name is not None
            oracle = oracles[occurrence.oracle_name]
            index = dependencies[0]
            if type(index) is not int or not 0 <= index < len(oracle.cells):
                raise ExecutionError("native oracle answer index is out of range")
            value = oracle.cells[index]
        else:  # pragma: no cover - exhaustive Enum guard
            raise ExecutionError("unknown occurrence kind")

        assert value is not None
        _datum(value)
        if is_fs:
            assert state is not None
            for influence_tag in required_influence_kinds(occurrence):
                state = _append_frame(
                    state,
                    frames,
                    influence_tag,
                    k1.encode_datum(
                        k1.DatumRecord(
                            (
                                (0, _symbol(occurrence.name, "occurrence name")),
                                (1, _datum(value)),
                            )
                        )
                    ),
                    occurrence.name,
                )
        entry = RunEntry(
            occurrence.name,
            occurrence.kind,
            EntryStatus.EXECUTED,
            value,
            prefix,
            draw_namespaces,
            attempts,
            influence,
        )
        entries.append(entry)
        value_map[ValueRef.occurrence(occurrence.name)] = value

    record = RunRecord(
        cid,
        tid,
        iid,
        interpretation,
        tuple(entries),
        tuple(frames),
        state,
    )
    if expected_record is not None and record != expected_record:
        raise ReplayError("record differs from the exact derived execution")
    return Completed(record)


def generate(
    core: Core,
    construction: TranscriptConstruction,
    interpretation: ChallengeInterpretation,
    invocation: Invocation,
    strategy: ProverStrategy,
    *,
    fresh_resolver: FreshChallengeResolver | None = None,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> GenerationResult:
    if strategy is None:
        raise ModelError("generation requires a prover strategy")
    return _execute(
        core,
        construction,
        interpretation,
        invocation,
        strategy,
        None,
        fresh_resolver,
        profiles=profiles,
    )


def replay(
    core: Core,
    construction: TranscriptConstruction,
    invocation: Invocation,
    record: RunRecord,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> RunRecord:
    result = _execute(
        core,
        construction,
        record.interpretation,
        invocation,
        None,
        record,
        None,
        profiles=profiles,
    )
    if type(result) is not Completed:  # pragma: no cover - replay has no strategy
        raise ReplayError("replay unexpectedly did not complete")
    return result.record


@dataclass(frozen=True)
class FreshFsPairEvidence:
    core_id: object
    fresh_terminal: bool
    fiat_shamir_terminal: bool
    occurrence_topology: tuple[tuple[str, OccurrenceKind, EntryStatus], ...]


def check_fresh_fs_pair(
    core: Core,
    construction: TranscriptConstruction,
    invocation: Invocation,
    fresh: RunRecord,
    fiat_shamir: RunRecord,
    *,
    profiles: K2SemanticProfiles = K2_SEMANTIC_PROFILES,
) -> FreshFsPairEvidence:
    """Check both runs and their exact same-Core structural relation."""

    expected_construction = construction_id(
        core,
        construction,
        profiles=profiles,
    )
    if fresh.core_id != fiat_shamir.core_id:
        raise ReplayError("Fresh/FS relation requires the same literal Core")
    if fresh.construction_id is not None:
        raise ReplayError("Fresh run must not cite a transcript construction")
    if (
        fresh.transcript_frames
        or fresh.terminal_state is not None
        or any(
            entry.prefix_state is not None
            or entry.draw_namespaces
            or entry.sampling_attempts is not None
            or entry.influence is not None
            for entry in fresh.entries
        )
    ):
        raise ReplayError("Fresh run must not carry Fiat--Shamir transcript state")
    if fiat_shamir.construction_id != expected_construction:
        raise ReplayError("Fiat--Shamir run cites the wrong Core-scoped construction")
    if fresh.invocation_id != fiat_shamir.invocation_id:
        raise ReplayError("Fresh/FS relation requires the same invocation")
    if fresh.interpretation is not ChallengeInterpretation.FRESH or fiat_shamir.interpretation is not ChallengeInterpretation.FIAT_SHAMIR:
        raise ReplayError("Fresh/FS relation axes are reversed or missing")
    fresh_topology = tuple((item.occurrence, item.kind, item.status) for item in fresh.entries)
    fs_topology = tuple((item.occurrence, item.kind, item.status) for item in fiat_shamir.entries)
    if fresh_topology != fs_topology:
        raise ReplayError("Fresh/FS runs disagree on exact occurrence topology")
    namespaces = tuple(
        namespace
        for item in fiat_shamir.entries
        if item.kind is OccurrenceKind.CHALLENGE
        for namespace in item.draw_namespaces
    )
    if len(set(namespaces)) != len(namespaces):
        raise ReplayError("Fiat--Shamir challenge namespaces are not unique")
    replay(core, construction, invocation, fresh, profiles=profiles)
    replay(core, construction, invocation, fiat_shamir, profiles=profiles)
    fresh_terminal = fresh.entries[-1].value is True
    fs_terminal = fiat_shamir.entries[-1].value is True
    return FreshFsPairEvidence(fresh.core_id, fresh_terminal, fs_terminal, fresh_topology)


def mutate_record(record: RunRecord, *, entries: tuple[RunEntry, ...] | None = None, frames: tuple[Frame, ...] | None = None) -> RunRecord:
    """Small explicit mutation helper for negative fixtures."""

    return replace(
        record,
        entries=record.entries if entries is None else entries,
        transcript_frames=record.transcript_frames if frames is None else frames,
    )


# ---------------------------------------------------------------------------
# Reusable bounded fixtures
# ---------------------------------------------------------------------------


class ScriptedStrategy:
    def __init__(self, moves: Mapping[str, Value | Callable[[ProverView], Value]]) -> None:
        self._moves = dict(moves)

    def move(self, occurrence: Occurrence, view: ProverView) -> Value:
        if occurrence.name not in self._moves:
            raise StrategyStopped(f"no move for {occurrence.name}")
        value = self._moves[occurrence.name]
        return value(view) if callable(value) else value


def schnorr_fixture() -> tuple[Core, TranscriptConstruction, Invocation, ProverStrategy]:
    modulus = 23
    order = 11
    generator = 2
    secret = 3
    nonce = 4
    statement = pow(generator, secret, modulus)
    core = Core(
        inputs=(
            InputDecl("g", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("q", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("p", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("statement", InputRole.STATEMENT, value_sort=ValueSort.NAT),
            InputDecl("session", InputRole.PUBLIC_CONTEXT),
        ),
        scopes=(ScopeDecl("root", None, None),),
        schedule=(
            Occurrence(
                "commitment",
                OccurrenceKind.PROVER_MESSAGE,
                prover_value_sort=ValueSort.NAT,
            ),
            Occurrence(
                "challenge",
                OccurrenceKind.CHALLENGE,
                dependencies=(ValueRef.input("statement"),),
                challenge_domain=ChallengeDomain(order),
            ),
            Occurrence(
                "response",
                OccurrenceKind.PROVER_MESSAGE,
                prover_value_sort=ValueSort.NAT,
            ),
            Occurrence(
                "verify",
                OccurrenceKind.CHECK,
                dependencies=(
                    ValueRef.input("g"),
                    ValueRef.input("statement"),
                    ValueRef.occurrence("commitment"),
                    ValueRef.occurrence("challenge"),
                    ValueRef.occurrence("response"),
                    ValueRef.input("p"),
                ),
                check_predicate=Predicate(
                    PredicateKind.SCHNORR,
                    (
                        ValueRef.input("g"),
                        ValueRef.input("statement"),
                        ValueRef.occurrence("commitment"),
                        ValueRef.occurrence("challenge"),
                        ValueRef.occurrence("response"),
                        ValueRef.input("p"),
                    ),
                    (order,),
                ),
            ),
            Occurrence("terminal", OccurrenceKind.TERMINAL),
        ),
        initial_claims=("knowledge",),
        reductions=(
            ReductionDecl(
                "schnorr-reduction",
                "verify",
                "root",
                ("knowledge",),
                (
                    ValueRef.input("g"),
                    ValueRef.input("statement"),
                    ValueRef.occurrence("commitment"),
                    ValueRef.occurrence("challenge"),
                    ValueRef.occurrence("response"),
                    ValueRef.input("p"),
                ),
                ("challenge",),
                (
                    RequiredPublication("commitment", "challenge"),
                    RequiredPublication("response", None),
                ),
                ("checked",),
            ),
        ),
        claim_uses=(
            ClaimConsumerUse("knowledge", "schnorr-reduction"),
            ClaimConsumerUse("checked", "terminal"),
        ),
    )
    def response(view: ProverView) -> Value:
        challenge = view.read_occurrence("challenge")
        assert type(challenge) is int
        return (nonce + challenge * secret) % order

    strategy = ScriptedStrategy(
        {
            "commitment": pow(generator, nonce, modulus),
            "response": response,
        }
    )
    construction = TranscriptConstruction(b"zkc/k2/schnorr/v0")
    invocation = Invocation(
        MappingProxyType(
            {
                "g": generator,
                "q": order,
                "p": modulus,
                "statement": statement,
                "session": b"fixture-session",
            }
        )
    )
    return core, construction, invocation, strategy


def oracle_fixture() -> tuple[Core, TranscriptConstruction, Invocation, ProverStrategy]:
    core = Core(
        inputs=(
            InputDecl("statement", InputRole.STATEMENT),
            InputDecl("session", InputRole.PUBLIC_CONTEXT),
        ),
        scopes=(ScopeDecl("root", None, None),),
        schedule=(
            Occurrence("oracle", OccurrenceKind.ORACLE_PUBLISH, oracle_name="f"),
            Occurrence("query_coin", OccurrenceKind.CHALLENGE, challenge_domain=ChallengeDomain(17)),
            Occurrence(
                "query",
                OccurrenceKind.ORACLE_QUERY,
                dependencies=(ValueRef.occurrence("query_coin"),),
                oracle_name="f",
            ),
            Occurrence(
                "answer",
                OccurrenceKind.ORACLE_ANSWER,
                dependencies=(ValueRef.occurrence("query"),),
                oracle_name="f",
            ),
            Occurrence("fold_coin", OccurrenceKind.CHALLENGE, challenge_domain=ChallengeDomain(19)),
            Occurrence(
                "answer_nonempty",
                OccurrenceKind.CHECK,
                dependencies=(ValueRef.occurrence("answer"), ValueRef.input("statement")),
                check_predicate=Predicate(
                    PredicateKind.BYTES_EQUAL,
                    (ValueRef.occurrence("answer"), ValueRef.input("statement")),
                ),
            ),
            Occurrence("terminal", OccurrenceKind.TERMINAL),
        ),
        extensions=("native-oracle-v0",),
        initial_claims=("oracle-claim",),
        reductions=(
            ReductionDecl(
                "oracle-reduction",
                "answer_nonempty",
                "root",
                ("oracle-claim",),
                (
                    ValueRef.occurrence("answer"),
                    ValueRef.input("statement"),
                ),
                ("query_coin", "fold_coin"),
                (RequiredPublication("oracle", "query_coin"),),
                ("queried",),
            ),
        ),
        claim_uses=(
            ClaimConsumerUse("oracle-claim", "oracle-reduction"),
            ClaimConsumerUse("queried", "terminal"),
        ),
    )
    cells = (b"statement", b"statement", b"statement")
    strategy = ScriptedStrategy({"oracle": OracleObject(cells)})
    invocation = Invocation(
        MappingProxyType({"statement": b"statement", "session": b"oracle-session"})
    )
    return core, TranscriptConstruction(b"zkc/k2/oracle/v0"), invocation, strategy
