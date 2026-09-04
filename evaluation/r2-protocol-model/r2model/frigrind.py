"""Closed FRI-Grind-1 subjects, constructions, and execution requests.

This module owns finite semantic terms. Evaluation lives in ``execution``;
Relations must consume replay-qualified executions rather than these terms
alone.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, Mapping

from .terms import CheckResult, OutcomeClass, affirmative, semantic_id


BASE_FIXTURE = Path("test/Family/Inputs/frigrind.json")
BOUND_FIXTURE = Path("test/Soundness/Inputs/frigrind-bound.json")
INVOCATION_FILE = Path("evaluation/r2-protocol-model/cases/frigrind-invocation.json")
EXTERNAL_FRESH_FILE = Path(
    "evaluation/r2-protocol-model/cases/frigrind-external-fresh.json"
)
BASE_HASH = "cf2e4effc006cae253a77a9f8e0a0d0a3fe024bf3d6af99a75801d4b4765426a"
BOUND_HASH = "317258c54a4b8dad0308f552adc2bf0f8ec4fc72ecc5dc765f4ad206c9503858"
INVOCATION_HASH = "f61a560d3671b924c76031de2b50b5d1f0a1dc65dfef83d45fc9b4f1a643269a"
EXTERNAL_FRESH_HASH = "297f5d518d516f12b6994684f66b263a0db5ec5e3d49d9319fc416e2f9de7425"

BASE_KEYS = frozenset(
    {"family", "name", "k", "field", "query_log2", "ell", "grinding_bits",
     "analysis", "kappa", "anchors", "johnson"}
)
KAPPA_KEYS = frozenset({"sponge", "iv", "codecs"})
CODEC_KEYS = frozenset({"pow_value", "query_index", "rs", "ext_field"})
MAX_CORE_ACTIONS = 64
MAX_PROFILE_CHALLENGE_VALUES = 1024


def _freeze(value: Any) -> Any:
    if isinstance(value, Mapping):
        return (
            "Map",
            tuple((str(key), _freeze(value[key])) for key in sorted(value)),
        )
    if isinstance(value, list):
        return ("List", tuple(_freeze(item) for item in value))
    return value


def _thaw(value: Any) -> Any:
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "Map":
        return {key: _thaw(item) for key, item in value[1]}
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "List":
        return [_thaw(item) for item in value[1]]
    return value


class Provenance(str, Enum):
    INPUT_BUNDLE = "InputBundle"
    PUBLIC_COIN_TAPE = "PublicCoinTape"
    TRANSCRIPT_CONSTRUCTION = "TranscriptConstruction"
    PROVER_STRATEGY = "ProverStrategy"
    DETERMINISTIC_VERIFIER = "DeterministicVerifier"
    WITNESS_LOCAL_MODEL = "WitnessLocalModel"


class TerminalKind(str, Enum):
    SOURCE_RESIDUAL = "SourceResidual"
    REJECT = "Reject"
    ABORT = "Abort"


class ResidualKind(str, Enum):
    FRI_TERMINAL_NOT_MODELED = "FriTerminalNotModeled"


class Interpretation(str, Enum):
    FRESH = "Fresh"
    FS = "FiatShamir"


class ActionKind(str, Enum):
    STATEMENT = "Statement"
    CHALLENGE = "Challenge"
    MESSAGE = "Message"
    CHECK = "Check"
    ROUTE = "Route"
    RESIDUAL = "Residual"


class Actor(str, Enum):
    APPLICATION = "Application"
    PROVER = "Prover"
    VERIFIER = "Verifier"
    SOURCE_BOUNDARY = "SourceBoundary"


class ValueSort(str, Enum):
    RS = "rs"
    EXT_FIELD = "ext_field"
    NONCE = "nonce"
    POW_VALUE = "pow_value"
    QUERY_INDEX = "query_index"
    BOOL = "bool"
    RESIDUAL = "residual"


class CoinSource(str, Enum):
    UNIFORM_FINITE = "UniformFinite"


class Visibility(str, Enum):
    PUBLIC = "PublicEnvironment"
    PRIVATE = "VerifierPrivate"


class PredicateKind(str, Enum):
    POW_ZERO = "PowEqualsZero"
    ROOT_EQUALS_G1 = "StatementEqualsG1"


class FailureEffect(str, Enum):
    REJECT_IMMEDIATELY = "RejectImmediately"
    CONTINUE = "Continue"


class RouteFormula(str, Enum):
    ROOT_CHECK = "RootCheck"
    ROOT_AND_POW = "RootCheckAndPowCheck"


class StrategyKind(str, Enum):
    COPY_STATEMENT = "CopyStatement"
    FIXED_BEFORE_FRESH_COIN = "FixedBeforeFreshCoin"
    SEARCH_POW_ZERO = "SearchPowZero"


class FreshTapeOrigin(str, Enum):
    """Tape provenance; ``EXTERNAL_FIXTURE`` is not an independence claim."""

    EXTERNAL_FIXTURE = "ExternalFixture"
    DERIVED_EXECUTION = "DerivedExecution"


class CoreDerivationKind(str, Enum):
    FIXTURE_GRINDING_CORE = "FixtureGrindingCore"
    DROP_GRINDING_PROJECTION = "DropGrindingProjection"


class Mutation(str, Enum):
    BASE = "base"
    OMIT_STATEMENT = "omit_statement"
    DELAY_STATEMENT = "delay_statement"
    DUPLICATE_STATEMENT = "duplicate_statement"
    WRONG_STATEMENT_CODEC = "wrong_statement_codec"
    WRONG_STATEMENT_VALUE = "wrong_statement_value"
    G1_WIRE_ONLY = "g1_wire_only"
    NONCE_WIRE_ONLY = "nonce_wire_only"
    NAMESPACE_COLLISION = "namespace_collision"
    VERIFIER_PRIVATE_DEPENDENCY = "verifier_private_dependency"
    G1_FUTURE_POW = "g1_future_pow"
    G1_FUTURE_QUERY = "g1_future_query"
    ROUTE_ORDER = "route_order"
    POST_GRIND_ABSORB = "post_grind_absorb"
    CONTINUE_AFTER_FAILED_POW = "continue_after_failed_pow"
    MISSING_SAMPLER_CONTRACT = "missing_sampler_contract"
    UNSUPPORTED_SAMPLER = "unsupported_sampler"


@dataclass(frozen=True)
class FixturePartitions:
    interaction: Any
    construction_refs: Any
    binding_refs: Any
    analysis_goal: Any

    def identities(self) -> dict[str, str]:
        return {
            name: semantic_id(f"r2.fixture.{name.replace('_', '-')}", value)
            for name, value in (
                ("interaction", self.interaction),
                ("construction_refs", self.construction_refs),
                ("binding_refs", self.binding_refs),
                ("analysis_goal", self.analysis_goal),
            )
        }


@dataclass(frozen=True)
class FrozenFixture:
    relative_path: str
    sha256: str
    payload_term: Any
    partitions: FixturePartitions
    relation_projection_occurrences: int

    @property
    def payload(self) -> Mapping[str, Any]:
        value = _thaw(self.payload_term)
        assert isinstance(value, dict)
        return value

    def summary(self) -> dict[str, Any]:
        payload = self.payload
        return {
            "path": self.relative_path,
            "sha256": self.sha256,
            "name": payload["name"],
            "partitions": self.partitions.identities(),
            "relation_projection_occurrences": self.relation_projection_occurrences,
        }


@dataclass(frozen=True)
class CoreAction:
    occurrence: str
    kind: ActionKind
    label: str
    actor: Actor
    value_sort: ValueSort
    cardinality: int | None = None
    count: int = 1
    namespace: str | None = None
    coin_source: CoinSource | None = None
    visibility: Visibility | None = None
    required_influences: tuple[str, ...] = ()
    predicate: PredicateKind | None = None
    failure_effect: FailureEffect | None = None
    route_formula: RouteFormula | None = None
    residual: ResidualKind | None = None

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "label": self.label,
            "actor": self.actor.value,
            "sort": self.value_sort.value,
            "cardinality": self.cardinality,
            "count": self.count,
            "namespace": self.namespace,
            "coin_source": self.coin_source.value if self.coin_source else None,
            "visibility": self.visibility.value if self.visibility else None,
            "required_influences": list(self.required_influences),
            "predicate": self.predicate.value if self.predicate else None,
            "failure_effect": self.failure_effect.value if self.failure_effect else None,
            "route_formula": self.route_formula.value if self.route_formula else None,
            "residual": self.residual.value if self.residual else None,
        }


@dataclass(frozen=True)
class ProtocolCore:
    field: int
    query_space: int
    query_count: int
    grinding_space: int | None
    actions: tuple[CoreAction, ...]

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.protocol-core.v3",
            {
                "field": self.field,
                "query_space": self.query_space,
                "query_count": self.query_count,
                "grinding_space": self.grinding_space,
                "actions": [action.term() for action in self.actions],
            },
        )

    @property
    def includes_grinding(self) -> bool:
        return self.grinding_space is not None

    @property
    def schedule(self) -> tuple[str, ...]:
        return tuple(action.occurrence for action in self.actions)

    @property
    def challenge_actions(self) -> tuple[CoreAction, ...]:
        return tuple(action for action in self.actions if action.kind is ActionKind.CHALLENGE)

    @property
    def transcript_actions(self) -> tuple[CoreAction, ...]:
        return tuple(
            action for action in self.actions
            if action.kind in {ActionKind.STATEMENT, ActionKind.MESSAGE, ActionKind.CHALLENGE}
        )

    def action(self, occurrence: str) -> CoreAction:
        matches = tuple(action for action in self.actions if action.occurrence == occurrence)
        if len(matches) != 1:
            raise KeyError(occurrence)
        return matches[0]


@dataclass(frozen=True)
class CanonicalCodec:
    name: str
    value_sort: ValueSort
    width: int
    domain_cardinality: int

    @property
    def is_total(self) -> bool:
        return (
            not isinstance(self.width, bool) and isinstance(self.width, int) and self.width > 0
            and not isinstance(self.domain_cardinality, bool)
            and isinstance(self.domain_cardinality, int)
            and self.domain_cardinality > 0
            and self.domain_cardinality <= 1 << (8 * self.width)
        )

    def encode(self, value: int) -> bytes:
        if (
            isinstance(value, bool) or not isinstance(value, int) or value < 0
            or value >= self.domain_cardinality or not self.is_total
        ):
            raise ValueError(f"{self.name} value is outside its canonical domain")
        return value.to_bytes(self.width, "big")

    @property
    def identity(self) -> str:
        return semantic_id("r2.canonical-codec.v3", self.term())

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "sort": self.value_sort.value,
            "width": self.width,
            "domain_cardinality": self.domain_cardinality,
        }


@dataclass(frozen=True)
class CodecBinding:
    occurrence: str
    codec: CanonicalCodec

    def term(self) -> dict[str, Any]:
        return {"occurrence": self.occurrence, "codec_id": self.codec.identity}


@dataclass(frozen=True)
class TranscriptConstruction:
    transcript_algorithm: str
    sampler_algorithm: str | None
    codec_bindings: tuple[CodecBinding, ...]
    absorb_order: tuple[str, ...]

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.transcript-construction.v3",
            {
                "transcript_algorithm": self.transcript_algorithm,
                "sampler_algorithm": self.sampler_algorithm,
                "codec_bindings": [binding.term() for binding in self.codec_bindings],
                "absorb_order": list(self.absorb_order),
            },
        )

    def codec_for(self, occurrence: str) -> CanonicalCodec:
        matches = tuple(
            binding.codec for binding in self.codec_bindings
            if binding.occurrence == occurrence
        )
        if len(matches) != 1:
            raise KeyError(occurrence)
        return matches[0]


@dataclass(frozen=True)
class PublicCoinSlot:
    occurrence: str
    cardinality: int
    count: int

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "cardinality": self.cardinality,
            "count": self.count,
        }


@dataclass(frozen=True)
class FreshCoinConstruction:
    """Declared coin-environment law; a tape checks only one support point."""

    name: str
    coin_slots: tuple[PublicCoinSlot, ...]
    reveal_law: str
    distribution_law: str
    strategy_access_law: str

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.fresh-coin-construction.v3",
            {
                "name": self.name,
                "coin_slots": [slot.term() for slot in self.coin_slots],
                "reveal_law": self.reveal_law,
                "distribution_law": self.distribution_law,
                "strategy_access_law": self.strategy_access_law,
            },
        )


@dataclass(frozen=True)
class StrategyContract:
    """Fixed witness-local access declaration, not an adversary class."""

    output_occurrence: str
    kind: StrategyKind
    reads: tuple[str, ...]
    previews: tuple[str, ...] = ()

    def term(self) -> dict[str, Any]:
        return {
            "output": self.output_occurrence,
            "kind": self.kind.value,
            "reads": list(self.reads),
            "previews": list(self.previews),
        }


@dataclass(frozen=True)
class ScenarioVariant:
    core: ProtocolCore
    interpretation: Interpretation
    strategies: tuple[StrategyContract, ...]
    construction: TranscriptConstruction | FreshCoinConstruction

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.protocol-scenario.v3",
            {
                "core": self.core.identity,
                "interpretation": self.interpretation.value,
                "strategies": [strategy.term() for strategy in self.strategies],
                "construction": self.construction.identity,
            },
        )

    @property
    def field(self) -> int:
        return self.core.field

    @property
    def query_space(self) -> int:
        return self.core.query_space

    @property
    def query_count(self) -> int:
        return self.core.query_count

    @property
    def grinding_space(self) -> int:
        return self.core.grinding_space or 0

    @property
    def includes_grinding(self) -> bool:
        return self.core.includes_grinding


@dataclass(frozen=True)
class InputBundle:
    statement_value: int
    base_prover_input: StrategyKind = StrategyKind.COPY_STATEMENT

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.input-bundle.v3",
            {"statement": self.statement_value, "base_prover_input": self.base_prover_input.value},
        )


@dataclass(frozen=True)
class ApplicationContext:
    """Semantic FS initialization context; changes intentionally rotate coins."""

    domain: str
    session: str

    @property
    def identity(self) -> str:
        return semantic_id("r2.application-context.v3", {"domain": self.domain, "session": self.session})


@dataclass(frozen=True)
class NonceSearchPlan:
    start: int
    limit: int

    def term(self) -> dict[str, int]:
        return {"start": self.start, "limit": self.limit}


@dataclass(frozen=True)
class FixedNoncePlan:
    nonce: int

    def term(self) -> dict[str, int]:
        return {"nonce": self.nonce}


@dataclass(frozen=True)
class CoinVector:
    challenge_occurrence: str
    values: tuple[int, ...]

    def term(self) -> dict[str, Any]:
        return {"challenge": self.challenge_occurrence, "values": list(self.values)}


@dataclass(frozen=True)
class FreshCoinTape:
    origin: FreshTapeOrigin
    vectors: tuple[CoinVector, ...]
    source_id: str
    dependency_execution_id: str | None = None

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.fresh-coin-tape.v3",
            {
                "origin": self.origin.value,
                "vectors": [vector.term() for vector in self.vectors],
                "source_id": self.source_id,
                "dependency_execution_id": self.dependency_execution_id,
            },
        )

    def values_for(self, occurrence: str) -> tuple[int, ...]:
        matches = tuple(vector.values for vector in self.vectors if vector.challenge_occurrence == occurrence)
        if len(matches) != 1:
            raise KeyError(occurrence)
        return matches[0]


@dataclass(frozen=True)
class ResourcePlan:
    max_nonce_candidates: int
    max_transcript_events: int
    max_trace_events: int
    max_challenge_values: int
    max_sampler_retries_per_value: int
    max_hash_queries: int

    def term(self) -> dict[str, int]:
        return {
            "max_nonce_candidates": self.max_nonce_candidates,
            "max_transcript_events": self.max_transcript_events,
            "max_trace_events": self.max_trace_events,
            "max_challenge_values": self.max_challenge_values,
            "max_sampler_retries_per_value": self.max_sampler_retries_per_value,
            "max_hash_queries": self.max_hash_queries,
        }


MAX_EVALUATOR_CAPS = ResourcePlan(1_000_000, 64, 64, 1024, 1024, 2_100_000)
DEFAULT_RESOURCE_PLAN = MAX_EVALUATOR_CAPS


@dataclass(frozen=True)
class QualificationCaps:
    max_dependency_executions: int
    max_total_nonce_candidates: int
    max_total_transcript_events: int
    max_total_trace_events: int
    max_total_challenge_values: int
    max_total_sampler_attempts: int
    max_total_hash_queries: int

    def term(self) -> dict[str, int]:
        return {
            "max_dependency_executions": self.max_dependency_executions,
            "max_total_nonce_candidates": self.max_total_nonce_candidates,
            "max_total_transcript_events": self.max_total_transcript_events,
            "max_total_trace_events": self.max_total_trace_events,
            "max_total_challenge_values": self.max_total_challenge_values,
            "max_total_sampler_attempts": self.max_total_sampler_attempts,
            "max_total_hash_queries": self.max_total_hash_queries,
        }


MAX_QUALIFICATION_CAPS = QualificationCaps(
    1,
    1_000_000,
    128,
    128,
    2048,
    2_100_000,
    2_100_000,
)


@dataclass(frozen=True)
class EvaluatorSource:
    relative_path: str
    sha256: str

    def term(self) -> dict[str, str]:
        return {"path": self.relative_path, "sha256": self.sha256}


@dataclass(frozen=True)
class EvaluatorBasis:
    qualification_law: str
    supported_construction_ids: tuple[str, ...]
    source_digests: tuple[EvaluatorSource, ...]
    hard_caps: ResourcePlan
    qualification_caps: QualificationCaps

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.evaluator-basis.v3",
            {
                "qualification_law": self.qualification_law,
                "supported_constructions": list(self.supported_construction_ids),
                "source_digests": [source.term() for source in self.source_digests],
                "hard_caps": self.hard_caps.term(),
                "qualification_caps": self.qualification_caps.term(),
            },
        )


@dataclass(frozen=True)
class ExecutionRequest:
    scenario: ScenarioVariant
    inputs: InputBundle
    application_context: ApplicationContext
    evaluator_basis_id: str
    resources: ResourcePlan
    core_derivation: CoreDerivationKind
    source_fixture_id: str
    source_package_id: str
    nonce_search: NonceSearchPlan | None = None
    fixed_nonce: FixedNoncePlan | None = None
    coin_tape: FreshCoinTape | None = None

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.execution-request.v3",
            {
                "scenario": self.scenario.identity,
                "inputs": self.inputs.identity,
                "application_context": self.application_context.identity,
                "evaluator_basis": self.evaluator_basis_id,
                "resources": self.resources.term(),
                "core_derivation": self.core_derivation.value,
                "source_fixture": self.source_fixture_id,
                "source_package": self.source_package_id,
                "nonce_search": self.nonce_search.term() if self.nonce_search else None,
                "fixed_nonce": self.fixed_nonce.term() if self.fixed_nonce else None,
                "coin_tape": self.coin_tape.identity if self.coin_tape else None,
            },
        )


@dataclass(frozen=True)
class InvocationPackage:
    input_bundle: InputBundle
    default_search: NonceSearchPlan
    source_fixture_id: str
    source_document_id: str

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.invocation-package.v3",
            {
                "input_bundle": self.input_bundle.identity,
                "default_search": self.default_search.term(),
                "source_fixture": self.source_fixture_id,
                "source_document": self.source_document_id,
            },
        )

    @property
    def statement_value(self) -> int:
        return self.input_bundle.statement_value


Invocation = InvocationPackage


def _exact(value: Mapping[str, Any], keys: frozenset[str], where: str) -> None:
    if set(value) != keys:
        raise ValueError(f"{where} keys differ: {sorted(value)}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_json(path: Path, expected_hash: str) -> tuple[bytes, Mapping[str, Any]]:
    if path.stat().st_size > 1 << 20:
        raise ValueError(f"frozen input exceeds the one-megabyte bound: {path}")
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_hash:
        raise ValueError(f"frozen content hash mismatch: {path}")
    value = json.loads(raw, object_pairs_hook=_unique_object)
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain one object")
    return raw, value


def load_fixture(repo_root: Path, companion: bool = False) -> FrozenFixture:
    rel, digest = (BOUND_FIXTURE, BOUND_HASH) if companion else (BASE_FIXTURE, BASE_HASH)
    _, payload = _load_json(repo_root / rel, digest)
    _exact(payload, BASE_KEYS | ({"preamble"} if companion else set()), str(rel))
    if payload["family"] != "fri" or payload["k"] != 1 or payload["analysis"] != "johnson":
        raise ValueError("fixture selector differs from FRI-Grind-1")
    for key in ("query_log2", "ell", "grinding_bits"):
        if isinstance(payload[key], bool) or not isinstance(payload[key], int) or payload[key] <= 0:
            raise ValueError(f"{key} must be a positive integer")
    field = int(payload["field"])
    if field <= 1 or not isinstance(payload["kappa"], dict):
        raise ValueError("invalid field or kappa")
    _exact(payload["kappa"], KAPPA_KEYS, "kappa")
    if not isinstance(payload["kappa"]["codecs"], dict):
        raise ValueError("kappa.codecs must be an object")
    _exact(payload["kappa"]["codecs"], CODEC_KEYS, "kappa.codecs")
    if not isinstance(payload["anchors"], dict) or set(payload["anchors"]) != {"contract", "statement"}:
        raise ValueError("anchors schema differs")
    if not isinstance(payload["johnson"], dict) or set(payload["johnson"]) != {"m", "eta", "delta"}:
        raise ValueError("johnson schema differs")
    occurrences = 0
    if companion:
        if payload["preamble"] != [{"label": "air_id", "class": "rs", "anchor": "contract"}]:
            raise ValueError("companion preamble differs")
        occurrences = 1
    partitions = FixturePartitions(
        _freeze({key: payload[key] for key in ("family", "k", "field", "query_log2", "ell", "grinding_bits")}),
        _freeze(dict(payload["kappa"])),
        _freeze({"anchors": dict(payload["anchors"]), "preamble": list(payload.get("preamble", []))}),
        _freeze({"selector": payload["analysis"], "parameters": dict(payload["johnson"])}),
    )
    return FrozenFixture(str(rel), digest, _freeze(payload), partitions, occurrences)


def load_invocation(repo_root: Path) -> InvocationPackage:
    raw, payload = _load_json(repo_root / INVOCATION_FILE, INVOCATION_HASH)
    keys = frozenset({"schema", "source_fixture_sha256", "statement_value", "g1_strategy",
                      "nonce_search_start", "nonce_search_limit"})
    _exact(payload, keys, str(INVOCATION_FILE))
    if payload["schema"] != "zkc.r2.frigrind-invocation.v2":
        raise ValueError("invocation schema differs")
    numbers = (payload["statement_value"], payload["nonce_search_start"], payload["nonce_search_limit"])
    if any(isinstance(value, bool) or not isinstance(value, int) or value < 0 for value in numbers):
        raise ValueError("invocation finite values are malformed")
    if payload["nonce_search_limit"] <= payload["nonce_search_start"]:
        raise ValueError("nonce interval is empty")
    if payload["g1_strategy"] != "copy_statement" or payload["source_fixture_sha256"] != BASE_HASH:
        raise ValueError("invocation binding differs")
    return InvocationPackage(
        InputBundle(payload["statement_value"]),
        NonceSearchPlan(payload["nonce_search_start"], payload["nonce_search_limit"]),
        f"sha256:{payload['source_fixture_sha256']}",
        f"sha256:{hashlib.sha256(raw).hexdigest()}",
    )


def load_external_fresh(
    repo_root: Path,
    core: ProtocolCore,
) -> tuple[FreshCoinTape, FixedNoncePlan]:
    raw, payload = _load_json(repo_root / EXTERNAL_FRESH_FILE, EXTERNAL_FRESH_HASH)
    _exact(
        payload,
        frozenset({"schema", "source_fixture_sha256", "fixed_nonce", "coin_vectors"}),
        str(EXTERNAL_FRESH_FILE),
    )
    if (
        payload["schema"] != "zkc.r2.frigrind-external-fresh.v1"
        or payload["source_fixture_sha256"] != BASE_HASH
        or not isinstance(payload["coin_vectors"], dict)
    ):
        raise ValueError("external Fresh support-point binding differs")
    nonce = payload["fixed_nonce"]
    if isinstance(nonce, bool) or not isinstance(nonce, int) or nonce < 0 or nonce >= 1 << 64:
        raise ValueError("external Fresh support-point nonce is malformed")
    expected = tuple(action.occurrence for action in core.challenge_actions)
    if tuple(payload["coin_vectors"]) != expected:
        raise ValueError("external Fresh support-point challenge order differs")
    vectors: list[CoinVector] = []
    for action in core.challenge_actions:
        values = payload["coin_vectors"][action.occurrence]
        if not isinstance(values, list) or len(values) != action.count or any(
            isinstance(value, bool)
            or not isinstance(value, int)
            or value < 0
            or action.cardinality is None
            or value >= action.cardinality
            for value in values
        ):
            raise ValueError(
                f"external Fresh support-point values for {action.occurrence} differ"
            )
        vectors.append(CoinVector(action.occurrence, tuple(values)))
    return (
        FreshCoinTape(
            FreshTapeOrigin.EXTERNAL_FIXTURE,
            tuple(vectors),
            f"sha256:{hashlib.sha256(raw).hexdigest()}",
        ),
        FixedNoncePlan(nonce),
    )


def build_evaluator_basis(
    repo_root: Path,
    supported_construction_ids: Iterable[str],
    hard_caps: ResourcePlan = DEFAULT_RESOURCE_PLAN,
    qualification_caps: QualificationCaps = MAX_QUALIFICATION_CAPS,
) -> EvaluatorBasis:
    paths = (
        Path("evaluation/r2-protocol-model/r2model/frigrind.py"),
        Path("evaluation/r2-protocol-model/r2model/execution.py"),
        Path("evaluation/r2-protocol-model/r2model/terms.py"),
    )
    sources = tuple(
        EvaluatorSource(str(path), hashlib.sha256((repo_root / path).read_bytes()).hexdigest())
        for path in paths
    )
    return EvaluatorBasis(
        "r2.exact-request-reexecution.v1",
        tuple(sorted(set(supported_construction_ids))),
        sources,
        hard_caps,
        qualification_caps,
    )


def _statement(field: int) -> CoreAction:
    return CoreAction("statement:f_root", ActionKind.STATEMENT, "f_root", Actor.APPLICATION, ValueSort.RS, field)


def _challenge(
    occurrence: str,
    label: str,
    sort: ValueSort,
    cardinality: int,
    count: int,
    namespace: str,
    required: tuple[str, ...],
) -> CoreAction:
    return CoreAction(
        occurrence, ActionKind.CHALLENGE, label, Actor.VERIFIER, sort,
        cardinality, count, namespace, CoinSource.UNIFORM_FINITE,
        Visibility.PUBLIC, required,
    )


def _message(occurrence: str, label: str, sort: ValueSort, cardinality: int) -> CoreAction:
    return CoreAction(occurrence, ActionKind.MESSAGE, label, Actor.PROVER, sort, cardinality)


def _check(
    occurrence: str,
    label: str,
    predicate: PredicateKind,
    failure: FailureEffect | None,
) -> CoreAction:
    return CoreAction(
        occurrence, ActionKind.CHECK, label, Actor.VERIFIER, ValueSort.BOOL,
        2, predicate=predicate, failure_effect=failure,
    )


def _route(occurrence: str, label: str, formula: RouteFormula) -> CoreAction:
    return CoreAction(
        occurrence, ActionKind.ROUTE, label, Actor.VERIFIER, ValueSort.BOOL,
        2, route_formula=formula,
    )


def _residual() -> CoreAction:
    return CoreAction(
        "residual:fri-terminal-not-modeled", ActionKind.RESIDUAL,
        "fri-terminal-not-modeled", Actor.SOURCE_BOUNDARY, ValueSort.RESIDUAL,
        residual=ResidualKind.FRI_TERMINAL_NOT_MODELED,
    )


def _grinding_actions(
    field: int,
    query_space: int,
    query_count: int,
    grinding_space: int,
) -> tuple[CoreAction, ...]:
    statement = "statement:f_root"
    fold = "challenge:fold1"
    g1 = "message:g1"
    nonce = "message:nonce"
    pow_challenge = "challenge:pow"
    return (
        _statement(field),
        _challenge(fold, "fold1", ValueSort.EXT_FIELD, field, 1, "fri/fold/1", (statement,)),
        _message(g1, "g1", ValueSort.RS, field),
        _message(nonce, "nonce", ValueSort.NONCE, 1 << 64),
        _challenge(
            pow_challenge, "pow", ValueSort.POW_VALUE, grinding_space, 1,
            "fri/grind/pow", (statement, fold, g1, nonce),
        ),
        _check("check:pow_zero", "pow_zero", PredicateKind.POW_ZERO, FailureEffect.REJECT_IMMEDIATELY),
        _challenge(
            "challenge:query", "query", ValueSort.QUERY_INDEX, query_space,
            query_count, "fri/query", (statement, fold, g1, nonce, pow_challenge),
        ),
        _check("check:toy_root_consistency", "toy_root_consistency", PredicateKind.ROOT_EQUALS_G1, None),
        _route("route:fri", "fri", RouteFormula.ROOT_CHECK),
        _route("route:grinding", "grinding", RouteFormula.ROOT_AND_POW),
        _residual(),
    )


def _fri_actions(field: int, query_space: int, query_count: int) -> tuple[CoreAction, ...]:
    statement = "statement:f_root"
    fold = "challenge:fold1"
    g1 = "message:g1"
    return (
        _statement(field),
        _challenge(fold, "fold1", ValueSort.EXT_FIELD, field, 1, "fri/fold/1", (statement,)),
        _message(g1, "g1", ValueSort.RS, field),
        _challenge(
            "challenge:query", "query", ValueSort.QUERY_INDEX, query_space,
            query_count, "fri/query", (statement, fold, g1),
        ),
        _check("check:toy_root_consistency", "toy_root_consistency", PredicateKind.ROOT_EQUALS_G1, None),
        _route("route:fri", "fri", RouteFormula.ROOT_CHECK),
        _residual(),
    )


def base_core(fixture: FrozenFixture) -> ProtocolCore:
    payload = fixture.payload
    field = int(payload["field"])
    query_space = 1 << int(payload["query_log2"])
    query_count = int(payload["ell"])
    grinding_space = 1 << int(payload["grinding_bits"])
    return ProtocolCore(
        field, query_space, query_count, grinding_space,
        _grinding_actions(field, query_space, query_count, grinding_space),
    )


def _fresh_strategies(core: ProtocolCore) -> tuple[StrategyContract, ...]:
    result: list[StrategyContract] = []
    for action in core.actions:
        if action.kind is not ActionKind.MESSAGE:
            continue
        if action.occurrence in {"message:g1", "message:post_grind"}:
            result.append(
                StrategyContract(
                    action.occurrence,
                    StrategyKind.COPY_STATEMENT,
                    ("statement:f_root",),
                )
            )
        elif action.occurrence == "message:nonce":
            result.append(
                StrategyContract(
                    action.occurrence,
                    StrategyKind.FIXED_BEFORE_FRESH_COIN,
                    ("statement:f_root", "challenge:fold1", "message:g1"),
                )
            )
    return tuple(result)


def _fs_strategies(core: ProtocolCore) -> tuple[StrategyContract, ...]:
    result = list(_fresh_strategies(core))
    if core.includes_grinding:
        index = next(
            index for index, strategy in enumerate(result)
            if strategy.output_occurrence == "message:nonce"
        )
        result[index] = StrategyContract(
            "message:nonce",
            StrategyKind.SEARCH_POW_ZERO,
            ("statement:f_root", "challenge:fold1", "message:g1"),
            ("challenge:pow",),
        )
    return tuple(result)


def _codec(action: CoreAction) -> CanonicalCodec:
    assert action.cardinality is not None
    widths = {
        ValueSort.RS: 16,
        ValueSort.EXT_FIELD: 16,
        ValueSort.NONCE: 8,
        ValueSort.POW_VALUE: 8,
        ValueSort.QUERY_INDEX: 8,
    }
    return CanonicalCodec(
        f"r2.{action.value_sort.value}.be{widths[action.value_sort]}.v3",
        action.value_sort,
        widths[action.value_sort],
        action.cardinality,
    )


def _transcript_construction(core: ProtocolCore) -> TranscriptConstruction:
    actions = core.transcript_actions
    return TranscriptConstruction(
        "r2.sha256-chained-transcript.v3",
        "r2.sha256-rejection-sampler.v3",
        tuple(CodecBinding(action.occurrence, _codec(action)) for action in actions),
        tuple(action.occurrence for action in actions),
    )


def _fresh_construction(core: ProtocolCore) -> FreshCoinConstruction:
    return FreshCoinConstruction(
        "r2.uniform-finite-public-coins.v2",
        tuple(
            PublicCoinSlot(
                action.occurrence,
                action.cardinality or 0,
                action.count,
            )
            for action in core.challenge_actions
        ),
        "r2.core-order-sequential-reveal.v1",
        "r2.conditionally-uniform-finite-slot.v1",
        "r2.no-future-coin-reads.v1",
    )


def fs_grinding_scenario(core: ProtocolCore) -> ScenarioVariant:
    if not core.includes_grinding:
        raise ValueError("FS grinding requires a grinding core")
    return ScenarioVariant(core, Interpretation.FS, _fs_strategies(core), _transcript_construction(core))


def fresh_grinding_scenario(core_or_scenario: ProtocolCore | ScenarioVariant) -> ScenarioVariant:
    core = core_or_scenario.core if isinstance(core_or_scenario, ScenarioVariant) else core_or_scenario
    if not core.includes_grinding:
        raise ValueError("Fresh grinding requires a grinding core")
    return ScenarioVariant(core, Interpretation.FRESH, _fresh_strategies(core), _fresh_construction(core))


def fresh_fri_scenario(core_or_scenario: ProtocolCore | ScenarioVariant) -> ScenarioVariant:
    source = core_or_scenario.core if isinstance(core_or_scenario, ScenarioVariant) else core_or_scenario
    core = ProtocolCore(
        source.field, source.query_space, source.query_count, None,
        _fri_actions(source.field, source.query_space, source.query_count),
    )
    return ScenarioVariant(core, Interpretation.FRESH, _fresh_strategies(core), _fresh_construction(core))


def base_scenario(fixture: FrozenFixture) -> ScenarioVariant:
    return fs_grinding_scenario(base_core(fixture))


def _replace_action(core: ProtocolCore, occurrence: str, **changes: Any) -> ProtocolCore:
    actions = tuple(
        replace(action, **changes) if action.occurrence == occurrence else action
        for action in core.actions
    )
    if actions == core.actions:
        raise ValueError(f"missing action {occurrence}")
    return replace(core, actions=actions)


def mutate(base: ScenarioVariant, mutation: Mutation) -> ScenarioVariant:
    if not isinstance(base, ScenarioVariant) or not isinstance(mutation, Mutation):
        raise ValueError("mutation requires a scenario and a closed mutation tag")
    if mutation is Mutation.BASE:
        return base
    if base.interpretation is not Interpretation.FS:
        raise ValueError("the mutation portfolio targets the FS witness")
    construction = base.construction
    if not isinstance(construction, TranscriptConstruction):
        raise ValueError("the mutation portfolio requires an FS transcript construction")
    if mutation in {Mutation.OMIT_STATEMENT, Mutation.DELAY_STATEMENT, Mutation.DUPLICATE_STATEMENT}:
        order = list(construction.absorb_order)
        order.remove("statement:f_root")
        if mutation is Mutation.DELAY_STATEMENT:
            order.insert(order.index("challenge:fold1") + 1, "statement:f_root")
        elif mutation is Mutation.DUPLICATE_STATEMENT:
            index = order.index("challenge:fold1")
            order[index:index] = ["statement:f_root", "statement:f_root"]
        return replace(base, construction=replace(construction, absorb_order=tuple(order)))
    if mutation is Mutation.WRONG_STATEMENT_CODEC:
        bindings = tuple(
            replace(binding, codec=CanonicalCodec("r2.rs.be1.hostile", ValueSort.RS, 1, base.field))
            if binding.occurrence == "statement:f_root" else binding
            for binding in construction.codec_bindings
        )
        return replace(base, construction=replace(construction, codec_bindings=bindings))
    if mutation is Mutation.WRONG_STATEMENT_VALUE:
        raise ValueError("wrong statement value belongs to an independently grounded bridge operand")
    if mutation in {Mutation.G1_WIRE_ONLY, Mutation.NONCE_WIRE_ONLY}:
        occurrence = "message:g1" if mutation is Mutation.G1_WIRE_ONLY else "message:nonce"
        return replace(
            base,
            construction=replace(
                construction,
                absorb_order=tuple(item for item in construction.absorb_order if item != occurrence),
            ),
        )
    if mutation is Mutation.NAMESPACE_COLLISION:
        fold_namespace = base.core.action("challenge:fold1").namespace
        return replace(base, core=_replace_action(base.core, "challenge:query", namespace=fold_namespace))
    if mutation is Mutation.VERIFIER_PRIVATE_DEPENDENCY:
        return replace(base, core=_replace_action(base.core, "challenge:fold1", visibility=Visibility.PRIVATE))
    if mutation in {Mutation.G1_FUTURE_POW, Mutation.G1_FUTURE_QUERY}:
        future = "challenge:pow" if mutation is Mutation.G1_FUTURE_POW else "challenge:query"
        strategies = tuple(
            replace(strategy, reads=strategy.reads + (future,))
            if strategy.output_occurrence == "message:g1" else strategy
            for strategy in base.strategies
        )
        return replace(base, strategies=strategies)
    if mutation is Mutation.ROUTE_ORDER:
        actions = list(base.core.actions)
        left = base.core.schedule.index("route:fri")
        right = base.core.schedule.index("route:grinding")
        actions[left], actions[right] = actions[right], actions[left]
        return replace(base, core=replace(base.core, actions=tuple(actions)))
    if mutation is Mutation.POST_GRIND_ABSORB:
        post = _message("message:post_grind", "post_grind", ValueSort.RS, base.field)
        actions = list(base.core.actions)
        actions.insert(base.core.schedule.index("challenge:query"), post)
        query_index = next(
            index for index, action in enumerate(actions)
            if action.occurrence == "challenge:query"
        )
        actions[query_index] = replace(
            actions[query_index],
            required_influences=actions[query_index].required_influences + (post.occurrence,),
        )
        core = replace(base.core, actions=tuple(actions))
        order = list(construction.absorb_order)
        order.insert(order.index("challenge:query"), post.occurrence)
        bindings = list(construction.codec_bindings)
        bindings.insert(
            next(index for index, binding in enumerate(bindings) if binding.occurrence == "challenge:query"),
            CodecBinding(post.occurrence, _codec(post)),
        )
        return replace(
            base,
            core=core,
            strategies=_fs_strategies(core),
            construction=replace(
                construction,
                absorb_order=tuple(order),
                codec_bindings=tuple(bindings),
            ),
        )
    if mutation is Mutation.CONTINUE_AFTER_FAILED_POW:
        return replace(base, core=_replace_action(base.core, "check:pow_zero", failure_effect=FailureEffect.CONTINUE))
    if mutation is Mutation.MISSING_SAMPLER_CONTRACT:
        return replace(base, construction=replace(construction, sampler_algorithm=None))
    if mutation is Mutation.UNSUPPORTED_SAMPLER:
        return replace(base, construction=replace(construction, sampler_algorithm="r2.unsupported-sampler.v1"))
    raise ValueError(f"unhandled mutation {mutation.value}")


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome, boundary, code, detail)


def _bounded_text(value: Any, limit: int = 256) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


def _admit_core(core: ProtocolCore) -> CheckResult | None:
    if not isinstance(core, ProtocolCore) or not isinstance(core.actions, tuple):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-001", "core has the wrong type")
    numbers = (core.field, core.query_space, core.query_count)
    if any(isinstance(value, bool) or not isinstance(value, int) or value <= 0 for value in numbers):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-001", "core domains are not positive finite integers")
    if core.field > 1 << 128 or core.query_space > 1 << 64:
        return _result(OutcomeClass.UNSUPPORTED, "closed-core", "R2-CORE-012", "core domains exceed the witness profile")
    if core.grinding_space is not None and (
        isinstance(core.grinding_space, bool) or not isinstance(core.grinding_space, int) or core.grinding_space <= 0
    ):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-002", "grinding domain is malformed")
    if core.grinding_space is not None and core.grinding_space > 1 << 64:
        return _result(OutcomeClass.UNSUPPORTED, "closed-core", "R2-CORE-025", "grinding domain exceeds the witness profile")
    if not core.actions or len(core.actions) > MAX_CORE_ACTIONS:
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "closed-core", "R2-CORE-003", "core action bound differs")
    if any(not isinstance(action, CoreAction) for action in core.actions):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-004", "core action has the wrong type")
    if any(
        not _bounded_text(action.occurrence)
        or not _bounded_text(action.label)
        for action in core.actions
    ):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-005", "core occurrence or label is malformed")
    occurrences = core.schedule
    if len(occurrences) != len(set(occurrences)):
        return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-005", "core occurrence is duplicated")
    if core.actions[-1].kind is not ActionKind.RESIDUAL or core.actions[-1].residual is not ResidualKind.FRI_TERMINAL_NOT_MODELED:
        return _result(OutcomeClass.MISMATCH, "source-boundary", "R2-CORE-006", "core residual differs")
    challenge_values = 0
    namespaces: list[str] = []
    kind_prefixes = {
        ActionKind.STATEMENT: "statement:",
        ActionKind.CHALLENGE: "challenge:",
        ActionKind.MESSAGE: "message:",
        ActionKind.CHECK: "check:",
        ActionKind.ROUTE: "route:",
        ActionKind.RESIDUAL: "residual:",
    }
    for index, action in enumerate(core.actions):
        if not isinstance(action.kind, ActionKind) or not isinstance(action.actor, Actor) or not isinstance(action.value_sort, ValueSort):
            return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-007", "core action vocabulary is open")
        if not action.occurrence.startswith(kind_prefixes[action.kind]):
            return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-013", "action occurrence kind prefix differs")
        if action.label != action.occurrence.split(":", 1)[1]:
            return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-029", "semantic action label differs from its occurrence")
        if isinstance(action.count, bool) or not isinstance(action.count, int) or action.count <= 0:
            return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-008", "action multiplicity is malformed")
        if action.cardinality is not None and (
            isinstance(action.cardinality, bool) or not isinstance(action.cardinality, int) or action.cardinality <= 0
        ):
            return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-009", "action domain is malformed")
        sort_bounds = {
            ValueSort.RS: 1 << 128,
            ValueSort.EXT_FIELD: 1 << 128,
            ValueSort.NONCE: 1 << 64,
            ValueSort.POW_VALUE: 1 << 64,
            ValueSort.QUERY_INDEX: 1 << 64,
            ValueSort.BOOL: 2,
        }
        if (
            action.value_sort in sort_bounds
            and action.cardinality is not None
            and action.cardinality > sort_bounds[action.value_sort]
        ):
            return _result(OutcomeClass.UNSUPPORTED, "closed-core", "R2-CORE-026", "action domain exceeds its canonical codec profile")
        if not isinstance(action.required_influences, tuple) or any(
            not isinstance(influence, str) for influence in action.required_influences
        ):
            return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-010", "challenge influence list is malformed")
        if action.kind is ActionKind.STATEMENT:
            if (
                action.actor is not Actor.APPLICATION
                or action.value_sort is not ValueSort.RS
                or action.cardinality != core.field
                or action.count != 1
                or any(
                    value is not None
                    for value in (
                        action.namespace,
                        action.coin_source,
                        action.visibility,
                        action.predicate,
                        action.failure_effect,
                        action.route_formula,
                        action.residual,
                    )
                )
                or action.required_influences
            ):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-014", "Statement action shape differs")
        elif action.kind is ActionKind.CHALLENGE:
            challenge_values += action.count
            if (
                action.actor is not Actor.VERIFIER
                or action.value_sort not in {ValueSort.EXT_FIELD, ValueSort.POW_VALUE, ValueSort.QUERY_INDEX}
                or action.cardinality is None
                or action.coin_source is not CoinSource.UNIFORM_FINITE
                or action.visibility is not Visibility.PUBLIC
                or any(
                    value is not None
                    for value in (action.predicate, action.failure_effect, action.route_formula, action.residual)
                )
            ):
                return _result(OutcomeClass.MISMATCH, "public-coin-eligibility", "R2-PC-001", "a verifier coin source is not public uniform finite")
            if not _bounded_text(action.namespace):
                return _result(OutcomeClass.MALFORMED, "squeeze-sample-admission", "R2-NS-002", "challenge namespace is malformed")
            namespaces.append(action.namespace)
            if len(action.required_influences) != len(set(action.required_influences)):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-010", "challenge influence is duplicated")
            if any(influence not in occurrences[:index] for influence in action.required_influences):
                return _result(OutcomeClass.MISMATCH, f"transcript-prefix:{action.label}", "R2-FS-009", "challenge requires absent or future influence")
            expected_influences = tuple(
                predecessor.occurrence
                for predecessor in core.actions[:index]
                if predecessor.kind in {ActionKind.STATEMENT, ActionKind.MESSAGE, ActionKind.CHALLENGE}
            )
            if action.required_influences != expected_influences:
                return _result(OutcomeClass.MISMATCH, f"transcript-prefix:{action.label}", "R2-FS-010", "protected influence set is not the complete prior transcript prefix")
        elif action.kind is ActionKind.MESSAGE:
            if (
                action.actor is not Actor.PROVER
                or action.value_sort not in {ValueSort.RS, ValueSort.NONCE}
                or action.cardinality is None
                or action.count != 1
                or any(
                    value is not None
                    for value in (
                        action.namespace,
                        action.coin_source,
                        action.visibility,
                        action.predicate,
                        action.failure_effect,
                        action.route_formula,
                        action.residual,
                    )
                )
                or action.required_influences
            ):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-015", "message action shape differs")
        elif action.kind is ActionKind.CHECK:
            if (
                action.actor is not Actor.VERIFIER
                or action.value_sort is not ValueSort.BOOL
                or action.cardinality != 2
                or action.count != 1
                or not isinstance(action.predicate, PredicateKind)
                or action.failure_effect is not None
                and not isinstance(action.failure_effect, FailureEffect)
                or any(
                    value is not None
                    for value in (action.namespace, action.coin_source, action.visibility, action.route_formula, action.residual)
                )
                or action.required_influences
            ):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-016", "check action shape differs")
        elif action.kind is ActionKind.ROUTE:
            if (
                action.actor is not Actor.VERIFIER
                or action.value_sort is not ValueSort.BOOL
                or action.cardinality != 2
                or action.count != 1
                or not isinstance(action.route_formula, RouteFormula)
                or any(
                    value is not None
                    for value in (action.namespace, action.coin_source, action.visibility, action.predicate, action.failure_effect, action.residual)
                )
                or action.required_influences
            ):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-017", "route action shape differs")
        else:
            if (
                action.actor is not Actor.SOURCE_BOUNDARY
                or action.value_sort is not ValueSort.RESIDUAL
                or action.cardinality is not None
                or action.count != 1
                or not isinstance(action.residual, ResidualKind)
                or any(
                    value is not None
                    for value in (action.namespace, action.coin_source, action.visibility, action.predicate, action.failure_effect, action.route_formula)
                )
                or action.required_influences
            ):
                return _result(OutcomeClass.MALFORMED, "closed-core", "R2-CORE-018", "residual action shape differs")
    if challenge_values > MAX_PROFILE_CHALLENGE_VALUES:
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "closed-core", "R2-CORE-011", "aggregate challenge-value bound exceeded")
    if len(namespaces) != len(set(namespaces)):
        return _result(OutcomeClass.MISMATCH, "squeeze-sample-admission", "R2-NS-001", "challenge namespace is reused")
    routes = tuple(action.occurrence for action in core.actions if action.kind is ActionKind.ROUTE)
    expected_routes = ("route:fri", "route:grinding") if core.includes_grinding else ("route:fri",)
    if routes != expected_routes:
        return _result(OutcomeClass.MISMATCH, "typed-routing", "R2-ROUTE-001", "route order differs")
    if sum(action.kind is ActionKind.RESIDUAL for action in core.actions) != 1:
        return _result(OutcomeClass.MISMATCH, "source-boundary", "R2-CORE-027", "Core must contain exactly one residual")
    by_occurrence = {action.occurrence: action for action in core.actions}
    common = {
        "statement:f_root",
        "challenge:fold1",
        "message:g1",
        "challenge:query",
        "check:toy_root_consistency",
        "route:fri",
        "residual:fri-terminal-not-modeled",
    }
    grinding = {"message:nonce", "challenge:pow", "check:pow_zero", "route:grinding"}
    optional = {"message:post_grind"} if core.includes_grinding else set()
    expected_occurrences = common | (grinding if core.includes_grinding else set())
    if (
        not common.issubset(by_occurrence)
        or (set(by_occurrence) & grinding not in (set(), grinding))
        or core.includes_grinding != grinding.issubset(by_occurrence)
        or not set(by_occurrence).issubset(expected_occurrences | optional)
    ):
        return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-019", "required FRI-Grind action set differs")
    named_shapes = (
        ("statement:f_root", ActionKind.STATEMENT, ValueSort.RS, core.field, 1),
        ("challenge:fold1", ActionKind.CHALLENGE, ValueSort.EXT_FIELD, core.field, 1),
        ("message:g1", ActionKind.MESSAGE, ValueSort.RS, core.field, 1),
        ("challenge:query", ActionKind.CHALLENGE, ValueSort.QUERY_INDEX, core.query_space, core.query_count),
    )
    if any(
        (
            by_occurrence[name].kind,
            by_occurrence[name].value_sort,
            by_occurrence[name].cardinality,
            by_occurrence[name].count,
        )
        != (kind, value_sort, cardinality, count)
        for name, kind, value_sort, cardinality, count in named_shapes
    ):
        return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-020", "named FRI action domain differs")
    if core.includes_grinding:
        assert core.grinding_space is not None
        grinding_shapes = (
            ("message:nonce", ActionKind.MESSAGE, ValueSort.NONCE, 1 << 64, 1),
            ("challenge:pow", ActionKind.CHALLENGE, ValueSort.POW_VALUE, core.grinding_space, 1),
        )
        if any(
            (
                by_occurrence[name].kind,
                by_occurrence[name].value_sort,
                by_occurrence[name].cardinality,
                by_occurrence[name].count,
            )
            != (kind, value_sort, cardinality, count)
            for name, kind, value_sort, cardinality, count in grinding_shapes
        ):
            return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-021", "named grinding action domain differs")
        if "message:post_grind" in by_occurrence:
            post = by_occurrence["message:post_grind"]
            if (
                post.kind is not ActionKind.MESSAGE
                or post.value_sort is not ValueSort.RS
                or post.cardinality != core.field
                or post.count != 1
            ):
                return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-028", "post-grinding message domain differs")
        if (
            by_occurrence["check:pow_zero"].predicate is not PredicateKind.POW_ZERO
            or by_occurrence["check:pow_zero"].failure_effect
            not in {FailureEffect.REJECT_IMMEDIATELY, FailureEffect.CONTINUE}
            or by_occurrence["route:grinding"].route_formula is not RouteFormula.ROOT_AND_POW
        ):
            return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-022", "grinding verifier law differs")
    if (
        by_occurrence["check:toy_root_consistency"].predicate is not PredicateKind.ROOT_EQUALS_G1
        or by_occurrence["check:toy_root_consistency"].failure_effect is not None
        or by_occurrence["route:fri"].route_formula is not RouteFormula.ROOT_CHECK
        or by_occurrence["residual:fri-terminal-not-modeled"].residual
        is not ResidualKind.FRI_TERMINAL_NOT_MODELED
    ):
        return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-023", "FRI verifier law differs")
    if core.includes_grinding:
        canonical_schedule = (
            "statement:f_root",
            "challenge:fold1",
            "message:g1",
            "message:nonce",
            "challenge:pow",
            "check:pow_zero",
            *(('message:post_grind',) if 'message:post_grind' in by_occurrence else ()),
            "challenge:query",
            "check:toy_root_consistency",
            "route:fri",
            "route:grinding",
            "residual:fri-terminal-not-modeled",
        )
    else:
        canonical_schedule = (
            "statement:f_root",
            "challenge:fold1",
            "message:g1",
            "challenge:query",
            "check:toy_root_consistency",
            "route:fri",
            "residual:fri-terminal-not-modeled",
        )
    if core.schedule != canonical_schedule:
        return _result(OutcomeClass.MISMATCH, "closed-core", "R2-CORE-024", "FRI-Grind action order differs")
    return None


def _admit_strategies(scenario: ScenarioVariant) -> CheckResult | None:
    if (
        not isinstance(scenario.strategies, tuple)
        or len(scenario.strategies) > MAX_CORE_ACTIONS
        or any(not isinstance(item, StrategyContract) for item in scenario.strategies)
    ):
        return _result(OutcomeClass.MALFORMED, "strategy-closure", "R2-CAUSAL-003", "strategy set is malformed")
    schedule = scenario.core.schedule
    message_occurrences = tuple(
        action.occurrence
        for action in scenario.core.actions
        if action.kind is ActionKind.MESSAGE
    )
    if tuple(strategy.output_occurrence for strategy in scenario.strategies) != message_occurrences:
        return _result(
            OutcomeClass.MISMATCH,
            "strategy-closure",
            "R2-CAUSAL-005",
            "strategy outputs do not exactly cover Core messages in order",
        )
    for strategy in scenario.strategies:
        if (
            not _bounded_text(strategy.output_occurrence)
            or not isinstance(strategy.kind, StrategyKind)
            or not isinstance(strategy.reads, tuple)
            or not isinstance(strategy.previews, tuple)
            or len(strategy.reads) > MAX_CORE_ACTIONS
            or len(strategy.previews) > MAX_CORE_ACTIONS
            or any(not _bounded_text(value) for value in strategy.reads + strategy.previews)
        ):
            return _result(OutcomeClass.MALFORMED, "strategy-closure", "R2-CAUSAL-006", "strategy contract vocabulary is malformed")
        if strategy.output_occurrence not in schedule:
            return _result(OutcomeClass.MALFORMED, "strategy-closure", "R2-CAUSAL-003", "strategy output is absent")
        output_index = schedule.index(strategy.output_occurrence)
        if any(read not in schedule[:output_index] for read in strategy.reads):
            return _result(OutcomeClass.MISMATCH, f"strategy-causality:{strategy.output_occurrence}", "R2-CAUSAL-001", "strategy reads future state")
        if any(preview not in schedule[output_index + 1:] for preview in strategy.previews):
            return _result(OutcomeClass.MISMATCH, f"strategy-causality:{strategy.output_occurrence}", "R2-CAUSAL-002", "strategy preview is not prospective")
    expected = _fs_strategies(scenario.core) if scenario.interpretation is Interpretation.FS else _fresh_strategies(scenario.core)
    if scenario.strategies != expected:
        return _result(OutcomeClass.MISMATCH, "strategy-closure", "R2-CAUSAL-004", "strategy contracts differ from the realization")
    return None


def _admit_fs_construction(scenario: ScenarioVariant) -> CheckResult | None:
    construction = scenario.construction
    if not isinstance(construction, TranscriptConstruction):
        return _result(OutcomeClass.MALFORMED, "construction-closure", "R2-ADM-004", "FS construction is absent")
    if construction.transcript_algorithm != "r2.sha256-chained-transcript.v3":
        return _result(OutcomeClass.UNSUPPORTED, "algorithm-support", "R2-ALG-005", "transcript construction is unsupported")
    if construction.sampler_algorithm is None:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "algorithm-closure", "R2-ALG-001", "sampler construction is missing")
    if construction.sampler_algorithm != "r2.sha256-rejection-sampler.v3":
        return _result(OutcomeClass.UNSUPPORTED, "algorithm-support", "R2-ALG-005", "sampler construction is unsupported")
    actions = scenario.core.transcript_actions
    occurrences = tuple(action.occurrence for action in actions)
    bindings = construction.codec_bindings
    if (
        not isinstance(bindings, tuple)
        or len(bindings) != len(actions)
        or any(not isinstance(binding, CodecBinding) for binding in bindings)
    ):
        return _result(OutcomeClass.MALFORMED, "framing", "R2-FRM-001", "codec bindings are malformed")
    if tuple(binding.occurrence for binding in bindings) != occurrences:
        return _result(OutcomeClass.MISMATCH, "framing", "R2-FRM-006", "codec binding set or order differs")
    for action, binding in zip(actions, bindings, strict=True):
        codec = binding.codec
        if not isinstance(codec, CanonicalCodec) or codec != _codec(action) or not codec.is_total:
            code = "R2-FRM-002" if action.kind is ActionKind.STATEMENT else "R2-SAMPLE-004"
            return _result(OutcomeClass.MALFORMED, "framing", code, f"{action.occurrence} codec is not total for its domain")
    order = construction.absorb_order
    if (
        not isinstance(order, tuple)
        or len(order) > MAX_CORE_ACTIONS
        or any(not isinstance(item, str) for item in order)
    ):
        return _result(OutcomeClass.MALFORMED, "transcript-prefix", "R2-FS-008", "absorb order is malformed")
    fold_index = order.index("challenge:fold1") if "challenge:fold1" in order else len(order)
    before = order[:fold_index].count("statement:f_root")
    total = order.count("statement:f_root")
    if before != 1:
        code = "R2-FS-003" if before > 1 else ("R2-FS-002" if total else "R2-FS-001")
        return _result(OutcomeClass.MISMATCH, "transcript-prefix:fold1", code, "Statement multiplicity before fold challenge differs")
    if order != occurrences:
        missing_protected = None
        for action in scenario.core.challenge_actions:
            if action.occurrence not in order:
                missing_protected = action.label
                break
            prefix = order[:order.index(action.occurrence)]
            if any(prefix.count(required) != 1 for required in action.required_influences):
                missing_protected = action.label
                break
        if missing_protected is not None:
            return _result(OutcomeClass.MISMATCH, f"transcript-prefix:{missing_protected}", "R2-FS-005", "protected influence is absent, duplicated, or late")
        return _result(OutcomeClass.MISMATCH, "transcript-prefix", "R2-FS-006", "absorb order differs from the complete Core")
    for action in scenario.core.challenge_actions:
        prefix = order[:order.index(action.occurrence)]
        if any(prefix.count(required) != 1 for required in action.required_influences):
            return _result(OutcomeClass.MISMATCH, f"transcript-prefix:{action.label}", "R2-FS-005", "protected influence is absent, duplicated, or late")
    return None


def admit_scenario(
    scenario: ScenarioVariant,
    interpretation: Interpretation | str | None = None,
) -> CheckResult:
    if not isinstance(scenario, ScenarioVariant) or not isinstance(scenario.interpretation, Interpretation):
        return _result(OutcomeClass.MALFORMED, "protocol-admission", "R2-ADM-003", "scenario has the wrong type")
    if interpretation is not None:
        try:
            selected = Interpretation(interpretation)
        except (TypeError, ValueError):
            return _result(OutcomeClass.UNSUPPORTED, "interpretation-closure", "R2-ADM-001", "unknown interpretation")
        if selected is not scenario.interpretation:
            return _result(OutcomeClass.MISMATCH, "interpretation-closure", "R2-ADM-002", "scenario has a different interpretation")
    core_failure = _admit_core(scenario.core)
    if core_failure:
        return core_failure
    strategy_failure = _admit_strategies(scenario)
    if strategy_failure:
        return strategy_failure
    if scenario.interpretation is Interpretation.FRESH:
        if not isinstance(scenario.construction, FreshCoinConstruction):
            return _result(OutcomeClass.MALFORMED, "construction-closure", "R2-ADM-004", "Fresh carries FS-only construction state")
        if scenario.construction != _fresh_construction(scenario.core):
            return _result(OutcomeClass.UNSUPPORTED, "construction-support", "R2-ADM-005", "Fresh construction is unsupported")
    else:
        construction_failure = _admit_fs_construction(scenario)
        if construction_failure:
            return construction_failure
    return affirmative(
        "protocol-admission", "R2-ADM-000", "closed protocol realization admitted",
        scenario_id=scenario.identity, core_id=scenario.core.identity,
    )


def grinding_applicability(scenario: ScenarioVariant) -> CheckResult:
    admitted = admit_scenario(scenario)
    if admitted.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "analysis-applicability", "R2-GRIND-000", "grinding applicability requires admission")
    if not scenario.includes_grinding:
        return _result(OutcomeClass.NOT_EXERCISED, "analysis-applicability:grinding-shape", "R2-GRIND-003", "scenario has no grinding round")
    pow_check = scenario.core.action("check:pow_zero")
    if pow_check.failure_effect is not FailureEffect.REJECT_IMMEDIATELY:
        return _result(OutcomeClass.MISMATCH, "analysis-applicability:grinding-failure", "R2-GRIND-004", "failed grinding does not reject immediately")
    left = scenario.core.schedule.index("check:pow_zero")
    right = scenario.core.schedule.index("challenge:query")
    if any(action.kind is ActionKind.MESSAGE for action in scenario.core.actions[left + 1:right]):
        return _result(
            OutcomeClass.CANNOT_ANSWER,
            "analysis-applicability:grinding-adjacency",
            "R2-GRIND-001",
            "post-grinding prover influence invalidates the witness-local placement precondition",
        )
    return affirmative(
        "analysis-applicability:grinding-shape",
        "R2-GRIND-002",
        "witness-local grinding placement preconditions are present; theorem and quantitative Analysis applicability are not decided",
    )
