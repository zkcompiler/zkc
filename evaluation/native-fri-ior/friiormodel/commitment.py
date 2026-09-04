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
    EXACT_ALGEBRA_PROFILE,
    EvaluationDomain,
    SemanticLaw,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
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
COMMITMENT_PROFILE_NAME = "zkc.fri-ior.salted-antipodal-merkle-cap.v1"
MERKLE_HASH = "sha256"
MERKLE_SALT_BYTES = 16
MERKLE_CAP_SIZE = 2
LEAF_HASH_DOMAIN = b"zkc.fri-ior.antipodal-leaf.v1\x00"
NODE_HASH_DOMAIN = b"zkc.fri-ior.merkle-node.v1\x00"


ANTIPODAL_LEAF_HASH_LAW = SemanticLaw(
    name="antipodal-pair-leaf-hash",
    version=1,
    parameters=(
        ("hash", MERKLE_HASH),
        ("domain-separator-hex", LEAF_HASH_DOMAIN.hex()),
        ("domain-name-codec", "u8-length-then-ascii"),
        ("pair-index-codec", "u16be"),
        ("fp-codec", "canonical-u8-less-than-97"),
        ("fp2-codec", "real-u8-then-imag-u8"),
        ("salt-bytes", MERKLE_SALT_BYTES),
        ("digest-bytes", DIGEST_BYTES),
    ),
    clauses=(
        "leaf-index-i-selects-evaluations-i-then-i-plus-half-domain-order",
        "leaf-payload-is-domain-name-then-index-then-positive-then-negative-then-salt",
        "leaf-digest-is-hash-of-domain-separator-concatenated-with-leaf-payload",
    ),
)

MERKLE_NODE_HASH_LAW = SemanticLaw(
    name="ordered-binary-merkle-node-hash",
    version=1,
    parameters=(
        ("hash", MERKLE_HASH),
        ("domain-separator-hex", NODE_HASH_DOMAIN.hex()),
        ("child-codec", "exactly-32-digest-bytes"),
        ("digest-bytes", DIGEST_BYTES),
    ),
    clauses=(
        "node-payload-is-left-child-then-right-child",
        "node-digest-is-hash-of-domain-separator-concatenated-with-node-payload",
        "left-and-right-child-order-is-semantic",
    ),
)

MERKLE_TREE_CAP_PATH_LAW = SemanticLaw(
    name="binary-merkle-tree-cap-and-path",
    version=1,
    parameters=(
        ("cap-size", MERKLE_CAP_SIZE),
        ("leaf-count", "domain-order-divided-by-two"),
        ("parent-pairing", "adjacent-even-left-odd-right"),
        ("path-order", "leaf-to-cap"),
    ),
    clauses=(
        "tree-reduction-stops-when-the-ordered-level-has-exactly-two-nodes",
        "path-sibling-at-each-level-is-index-xor-one",
        "even-running-index-is-left-and-odd-running-index-is-right",
        "running-index-is-floor-divided-by-two-after-each-node-hash",
        "opening-accepts-exactly-when-final-digest-equals-cap-at-running-index",
    ),
)

EXACT_COMMITMENT_LAWS = (
    ANTIPODAL_LEAF_HASH_LAW,
    MERKLE_NODE_HASH_LAW,
    MERKLE_TREE_CAP_PATH_LAW,
)


@dataclass(frozen=True, slots=True)
class FriCommitmentProfile:
    """The exact encoding, tree, cap, and opening-path semantic owner."""

    name: str
    algebra_profile_id: SemanticId
    hash_name: str
    digest_bytes: int
    salt_bytes: int
    cap_size: int
    semantic_laws: tuple[SemanticLaw, ...]

    def __post_init__(self) -> None:
        if (
            not isinstance(self.name, str)
            or not self.name
            or len(self.name) > 192
            or any(
                character not in "abcdefghijklmnopqrstuvwxyz0123456789.-_"
                for character in self.name
            )
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-026",
                "a commitment profile requires a bounded lower-case ASCII name",
            )
        if (
            not isinstance(self.algebra_profile_id, SemanticId)
            or self.algebra_profile_id.subject_kind != "fri-algebra-profile"
        ):
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-027",
                "a commitment profile must bind one FriAlgebraProfile identity",
            )
        if (
            not isinstance(self.hash_name, str)
            or not self.hash_name
            or len(self.hash_name) > 64
            or any(
                character not in "abcdefghijklmnopqrstuvwxyz0123456789.-_"
                for character in self.hash_name
            )
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-028",
                "a commitment hash name must be a bounded lower-case ASCII identifier",
            )
        if (
            type(self.digest_bytes) is not int
            or self.digest_bytes <= 0
            or type(self.salt_bytes) is not int
            or not 1 <= self.salt_bytes <= 1024
            or type(self.cap_size) is not int
            or self.cap_size < 1
            or self.cap_size & (self.cap_size - 1)
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-029",
                "commitment widths must be positive, bounded, and the cap a power of two",
            )
        if any(
            domain.order // 2 < self.cap_size
            or (domain.order // 2) % self.cap_size
            for domain in EXACT_ALGEBRA_PROFILE.domains
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-030",
                "the commitment cap must divide every antipodal-pair leaf count",
            )
        if (
            type(self.semantic_laws) is not tuple
            or not self.semantic_laws
            or any(type(law) is not SemanticLaw for law in self.semantic_laws)
            or len({law.name for law in self.semantic_laws})
            != len(self.semantic_laws)
            or tuple(law.name for law in self.semantic_laws)
            != tuple(law.name for law in EXACT_COMMITMENT_LAWS)
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-031",
                "a commitment profile requires every exact semantic-law role once and in order",
            )
        leaf_parameters = dict(self.semantic_laws[0].parameters)
        node_parameters = dict(self.semantic_laws[1].parameters)
        tree_parameters = dict(self.semantic_laws[2].parameters)
        if (
            leaf_parameters.get("hash") != self.hash_name
            or leaf_parameters.get("salt-bytes") != self.salt_bytes
            or leaf_parameters.get("digest-bytes") != self.digest_bytes
            or node_parameters.get("hash") != self.hash_name
            or node_parameters.get("digest-bytes") != self.digest_bytes
            or tree_parameters.get("cap-size") != self.cap_size
        ):
            raise malformed(
                "commitment:profile-formation",
                "FRI-IOR-COMMITMENT-032",
                "commitment-law parameters contradict their profile fields",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "algebra_profile_id": self.algebra_profile_id.to_term(),
            "hash": self.hash_name,
            "digest_bytes": self.digest_bytes,
            "salt_bytes": self.salt_bytes,
            "cap_size": self.cap_size,
            "leaf_layout": "ordered-antipodal-evaluation-pair",
            "semantic_law_ids": [law.identity.to_term() for law in self.semantic_laws],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-commitment-profile",
            "fri-ior.commitment-profile.v1",
            self.to_term(),
        )


EXACT_COMMITMENT_PROFILE = FriCommitmentProfile(
    name=COMMITMENT_PROFILE_NAME,
    algebra_profile_id=EXACT_ALGEBRA_PROFILE.identity,
    hash_name=MERKLE_HASH,
    digest_bytes=DIGEST_BYTES,
    salt_bytes=MERKLE_SALT_BYTES,
    cap_size=MERKLE_CAP_SIZE,
    semantic_laws=EXACT_COMMITMENT_LAWS,
)


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
    for supported in EXACT_ALGEBRA_PROFILE.domains:
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
            "commitment_profile_id": EXACT_COMMITMENT_PROFILE.identity.to_term(),
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
            "commitment_profile_id": EXACT_COMMITMENT_PROFILE.identity.to_term(),
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
