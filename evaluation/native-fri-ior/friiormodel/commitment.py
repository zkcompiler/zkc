"""Salted SHA-256 Merkle caps over ordered antipodal evaluation pairs.

For a domain of order ``2n``, leaf ``i`` commits to the ordered values at
indices ``i`` and ``i+n`` plus exactly sixteen caller-supplied salt bytes.
The tree stops at a two-node cap.  Query occurrences and proof-material
deduplication are intentionally outside this primitive: an opening proves one
pair position and does not claim how often that position was drawn.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import hmac
from typing import Any

from .field import Fp2
from .profile import (
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
    MERKLE_CAP_SIZE,
    MERKLE_SALT_BYTES,
    EvaluationDomain,
)
from .terms import (
    CheckResult,
    ModelFailure,
    ResourceCounter,
    SemanticId,
    affirmative,
    checker_failure,
    malformed,
    refusal,
    refused,
    semantic_id,
    unsupported_failure,
)


DIGEST_BYTES = hashlib.sha256().digest_size
MAX_AUTHENTICATION_DEPTH = 2
LEAF_HASH_DOMAIN = b"zkc.fri-ior.antipodal-leaf.v1\x00"
NODE_HASH_DOMAIN = b"zkc.fri-ior.merkle-node.v1\x00"


def _validate_digest(digest: Any, boundary: str) -> None:
    if not isinstance(digest, bytes) or len(digest) != DIGEST_BYTES:
        raise malformed(
            boundary,
            "FRI-IOR-COMMITMENT-001",
            "a SHA-256 digest must contain exactly 32 bytes",
        )


def _supported_domain(domain: object) -> EvaluationDomain:
    if not isinstance(domain, EvaluationDomain):
        raise malformed(
            "commitment:domain",
            "FRI-IOR-COMMITMENT-002",
            "a commitment requires an EvaluationDomain value",
        )
    for supported in EXACT_PROFILE.domains:
        if domain == supported:
            return supported
    raise unsupported_failure(
        "commitment:domain",
        "FRI-IOR-COMMITMENT-003",
        "the domain is well formed but unsupported by the exact finite profile",
    )


@dataclass(frozen=True, slots=True)
class MerkleCap:
    """The public two-node commitment value."""

    nodes: tuple[bytes, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.nodes, tuple) or len(self.nodes) != MERKLE_CAP_SIZE:
            raise malformed(
                "commitment:cap-formation",
                "FRI-IOR-COMMITMENT-004",
                "the exact commitment profile requires a two-node cap",
            )
        for digest in self.nodes:
            _validate_digest(digest, "commitment:cap-formation")

    def to_term(self) -> dict[str, Any]:
        return {
            "hash": "sha256",
            "cap_size": MERKLE_CAP_SIZE,
            "nodes": [node.hex() for node in self.nodes],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "merkle-cap",
            "fri-ior.merkle-cap.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class PairOpening:
    """One authenticated ordered antipodal pair at a logical leaf index."""

    domain_name: str
    pair_index: int
    positive: Fp2
    negative: Fp2
    salt: bytes
    authentication_path: tuple[bytes, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.domain_name, str) or not self.domain_name:
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-005",
                "an opening requires a non-empty domain name",
            )
        if type(self.pair_index) is not int or self.pair_index < 0:
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-006",
                "an opening pair index must be a non-negative integer",
            )
        if not isinstance(self.positive, Fp2) or not isinstance(self.negative, Fp2):
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-007",
                "an opening must carry two ordered Fp2 values",
            )
        if not isinstance(self.salt, bytes) or len(self.salt) != MERKLE_SALT_BYTES:
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-008",
                "an opening salt must contain exactly sixteen bytes",
            )
        if not isinstance(self.authentication_path, tuple):
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-009",
                "an authentication path must be a canonical sequence",
            )
        if len(self.authentication_path) > MAX_AUTHENTICATION_DEPTH:
            raise malformed(
                "commitment:opening-formation",
                "FRI-IOR-COMMITMENT-010",
                "an authentication path exceeds the finite profile's depth bound",
            )
        for digest in self.authentication_path:
            _validate_digest(digest, "commitment:opening-formation")

    def to_term(self) -> dict[str, Any]:
        return {
            "domain": self.domain_name,
            "pair_index": self.pair_index,
            "positive": self.positive.to_term(),
            "negative": self.negative.to_term(),
            "salt": self.salt.hex(),
            "authentication_path": [item.hex() for item in self.authentication_path],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "antipodal-pair-opening",
            "fri-ior.antipodal-pair-opening.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class CommitmentTree:
    """Private construction material plus its public Merkle cap."""

    domain: EvaluationDomain
    cap: MerkleCap
    _evaluations: tuple[Fp2, ...] = field(repr=False)
    _salts: tuple[bytes, ...] = field(repr=False)
    _levels: tuple[tuple[bytes, ...], ...] = field(repr=False)

    @property
    def pair_count(self) -> int:
        return self.domain.order // 2

    @property
    def authentication_depth(self) -> int:
        return (self.pair_count // MERKLE_CAP_SIZE).bit_length() - 1

    def open_pair(self, pair_index: int) -> PairOpening:
        if type(pair_index) is not int or not 0 <= pair_index < self.pair_count:
            raise refusal(
                "commitment:opening-request",
                "FRI-IOR-COMMITMENT-011",
                "the requested pair index lies outside the committed domain",
            )
        index = pair_index
        path: list[bytes] = []
        for level in self._levels[:-1]:
            path.append(level[index ^ 1])
            index //= 2
        half = self.domain.order // 2
        return PairOpening(
            domain_name=self.domain.name,
            pair_index=pair_index,
            positive=self._evaluations[pair_index],
            negative=self._evaluations[pair_index + half],
            salt=self._salts[pair_index],
            authentication_path=tuple(path),
        )


def _leaf_payload(
    domain: EvaluationDomain,
    pair_index: int,
    positive: Fp2,
    negative: Fp2,
    salt: bytes,
) -> bytes:
    domain_bytes = domain.name.encode("ascii")
    if len(domain_bytes) > 255 or pair_index >= 1 << 16:
        raise malformed(
            "commitment:leaf-codec",
            "FRI-IOR-COMMITMENT-012",
            "the domain name or pair index exceeds the finite leaf codec",
        )
    return (
        bytes((len(domain_bytes),))
        + domain_bytes
        + pair_index.to_bytes(2, "big")
        + positive.to_bytes()
        + negative.to_bytes()
        + salt
    )


def _hash_leaf(
    domain: EvaluationDomain,
    pair_index: int,
    positive: Fp2,
    negative: Fp2,
    salt: bytes,
    resources: ResourceCounter,
) -> bytes:
    payload = LEAF_HASH_DOMAIN + _leaf_payload(
        domain, pair_index, positive, negative, salt
    )
    resources.consume_hash(len(payload), merkle_nodes=1)
    return hashlib.sha256(payload).digest()


def _hash_node(left: bytes, right: bytes, resources: ResourceCounter) -> bytes:
    _validate_digest(left, "commitment:node-hash")
    _validate_digest(right, "commitment:node-hash")
    payload = NODE_HASH_DOMAIN + left + right
    resources.consume_hash(len(payload), merkle_nodes=1)
    return hashlib.sha256(payload).digest()


def _counter_or_default(resources: ResourceCounter | None) -> ResourceCounter:
    if resources is None:
        return ResourceCounter(DEFAULT_VALIDATION_LIMITS)
    if not isinstance(resources, ResourceCounter):
        raise malformed(
            "commitment:resources",
            "FRI-IOR-COMMITMENT-013",
            "commitment evaluation requires a ResourceCounter when metered",
        )
    return resources


def build_commitment(
    domain: EvaluationDomain,
    evaluations: tuple[Fp2, ...],
    salts: tuple[bytes, ...],
    resources: ResourceCounter | None = None,
) -> CommitmentTree:
    """Build the exact cap from canonical evaluation and salt sequences."""

    supported = _supported_domain(domain)
    counter = _counter_or_default(resources)
    if not isinstance(evaluations, tuple) or len(evaluations) != supported.order:
        raise malformed(
            "commitment:input",
            "FRI-IOR-COMMITMENT-014",
            "the evaluation sequence must cover the domain exactly",
        )
    if not all(isinstance(value, Fp2) for value in evaluations):
        raise malformed(
            "commitment:input",
            "FRI-IOR-COMMITMENT-015",
            "every committed evaluation must be an Fp2 element",
        )
    pair_count = supported.order // 2
    if not isinstance(salts, tuple) or len(salts) != pair_count:
        raise malformed(
            "commitment:input",
            "FRI-IOR-COMMITMENT-016",
            "there must be exactly one salt for every antipodal pair leaf",
        )
    if not all(isinstance(salt, bytes) and len(salt) == MERKLE_SALT_BYTES for salt in salts):
        raise malformed(
            "commitment:input",
            "FRI-IOR-COMMITMENT-017",
            "every antipodal pair leaf requires exactly sixteen salt bytes",
        )
    if pair_count < MERKLE_CAP_SIZE or pair_count & (pair_count - 1):
        raise malformed(
            "commitment:input",
            "FRI-IOR-COMMITMENT-018",
            "the pair-leaf count must be a power of two covering the cap",
        )

    half = supported.order // 2
    leaves = tuple(
        _hash_leaf(
            supported,
            index,
            evaluations[index],
            evaluations[index + half],
            salts[index],
            counter,
        )
        for index in range(pair_count)
    )
    levels: list[tuple[bytes, ...]] = [leaves]
    current = leaves
    while len(current) > MERKLE_CAP_SIZE:
        current = tuple(
            _hash_node(current[index], current[index + 1], counter)
            for index in range(0, len(current), 2)
        )
        levels.append(current)
    return CommitmentTree(
        domain=supported,
        cap=MerkleCap(current),
        _evaluations=evaluations,
        _salts=salts,
        _levels=tuple(levels),
    )


def verify_pair_opening(
    domain: object,
    cap: object,
    opening: object,
    resources: ResourceCounter | None = None,
) -> CheckResult:
    """Authenticate one pair opening under the exact commitment profile."""

    boundary = "commitment:opening-verification"
    try:
        supported = _supported_domain(domain)
        if not isinstance(cap, MerkleCap):
            raise malformed(
                boundary,
                "FRI-IOR-COMMITMENT-019",
                "opening verification requires a MerkleCap value",
            )
        if not isinstance(opening, PairOpening):
            raise malformed(
                boundary,
                "FRI-IOR-COMMITMENT-020",
                "opening verification requires a PairOpening value",
            )
        counter = _counter_or_default(resources)
        if opening.domain_name != supported.name:
            return refused(
                boundary,
                "FRI-IOR-COMMITMENT-021",
                "the opening names a different evaluation domain",
            )
        pair_count = supported.order // 2
        if opening.pair_index >= pair_count:
            return refused(
                boundary,
                "FRI-IOR-COMMITMENT-022",
                "the opening pair index lies outside the committed domain",
            )
        expected_depth = (pair_count // MERKLE_CAP_SIZE).bit_length() - 1
        if len(opening.authentication_path) != expected_depth:
            return refused(
                boundary,
                "FRI-IOR-COMMITMENT-023",
                "the authentication path does not reach the two-node cap",
            )

        running = _hash_leaf(
            supported,
            opening.pair_index,
            opening.positive,
            opening.negative,
            opening.salt,
            counter,
        )
        index = opening.pair_index
        for sibling in opening.authentication_path:
            left, right = (running, sibling) if index % 2 == 0 else (sibling, running)
            running = _hash_node(left, right, counter)
            index //= 2
        if index >= MERKLE_CAP_SIZE:
            return refused(
                boundary,
                "FRI-IOR-COMMITMENT-024",
                "the authentication path terminates outside the published cap",
            )
        if not hmac.compare_digest(running, cap.nodes[index]):
            return refused(
                boundary,
                "FRI-IOR-COMMITMENT-025",
                "the opening does not authenticate to the selected cap node",
            )
        return affirmative(
            boundary,
            "FRI-IOR-COMMITMENT-100",
            "the ordered antipodal pair authenticates to the published cap",
            subject=cap.identity,
            opening=opening.identity,
            pair_index=opening.pair_index,
            cap_index=index,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - exercised with fault injection
        return checker_failure(
            boundary,
            f"unexpected opening-checker failure: {type(error).__name__}",
        )
