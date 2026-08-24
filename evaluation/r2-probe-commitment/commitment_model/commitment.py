"""Commitment constructions, committed-value profiles, and openings.

The witness's FRI scenario carries a committed root as an opaque element and
nothing opens it, which is why its execution ends at the source residual.  This
module supplies the missing half under one design claim:

    a commitment is not an element of the class its content is drawn from, so
    it satisfies no operand slot; an *opening* is a third typed thing that
    does.

The claim that follows, and that this module exists to falsify, is that **no
new action kind is needed**: an opening is a prover message carrying an
``Opening`` value plus a verifier check that consumes it.  If that holds, the
commitment subject is a construction plus a typing discipline, not a widening
of the closed action vocabulary.

What grounds a declared arity is the *construction*, never the schedule.  A
prover who commits to more elements than it declares answers every query in the
declared range honestly, so no arrangement of transcript events detects it.
The honest form is therefore a named hypothesis discharged at the construction,
which :func:`verify_opening` attaches to every affirmative result rather than
pretending the check established it.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Any, Mapping

from .terms import CheckResult, OutcomeClass, semantic_id


# Bounded so that building a root stays far below the evaluator's hash-query
# budget: an arity-20 commitment would cost ~2.1M digests, comparable to the
# whole per-execution cap.  The real FRI fixture draws its queries from 2^10.
MAX_ARITY_LOG2 = 12
MAX_AUTH_PATH = MAX_ARITY_LOG2
MAX_OPENINGS = 64

LEAF_TAG = b"\x00"
NODE_TAG = b"\x01"

#: The assumption every affirmative opening carries, named the way the
#: projection-loss judgment names its own (``required_assumption`` at
#: ``relations.py``).  A length-indexed opening makes an *overstated* arity
#: infeasible to answer; understatement stays undetectable by construction, so
#: the binding property is assumed at the construction rather than established
#: here.
BINDING_ASSUMPTION = "CommitmentBindsDeclaredArity"


class CommitmentError(ValueError):
    """A malformed commitment construction, profile, or opening."""


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome=outcome, boundary=boundary, code=code, detail=detail)


@dataclass(frozen=True)
class CommitmentConstruction:
    """What realizes a commitment, stated the way a sponge states its rate.

    ``auth_depth`` is not free: it is fixed by ``arity_log2``, which is what
    makes an out-of-range query unanswerable rather than merely rejected by
    convention.  ``domain_separation`` records that leaves and internal nodes
    are tagged apart, so an internal node cannot be presented as a leaf.
    """

    name: str
    element_sort: str
    arity_log2: int
    query_sort: str
    domain_separation: str
    binding_game: str

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise CommitmentError("a construction needs a name")
        if not isinstance(self.arity_log2, int):
            raise CommitmentError("arity_log2 must be an integer")
        if not 0 < self.arity_log2 <= MAX_ARITY_LOG2:
            raise CommitmentError("arity_log2 is outside the declared profile")
        for field_name in ("element_sort", "query_sort", "domain_separation", "binding_game"):
            value = getattr(self, field_name)
            if not isinstance(value, str) or not value:
                raise CommitmentError(f"{field_name} must be non-empty text")

    @property
    def auth_depth(self) -> int:
        """Authentication length, fixed by the declared arity."""

        return self.arity_log2

    @property
    def cardinality(self) -> int:
        return 1 << self.arity_log2

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "element_sort": self.element_sort,
            "arity_log2": self.arity_log2,
            "query_sort": self.query_sort,
            "auth_depth": self.auth_depth,
            "domain_separation": self.domain_separation,
            "binding_game": self.binding_game,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.commitment-construction.v1", self.term())


@dataclass(frozen=True)
class CommittedValueProfile:
    """A committed value's declaration, including the opening discipline.

    ``construction`` is a reference resolved against the construction table,
    not a free string: an unresolved route is a missing dependency rather than
    a value the checker carries without evaluating.  ``opens_at`` is the field
    the publication side alone cannot supply — which occurrences open this
    value, and therefore what an opening of it answers.
    """

    name: str
    construction: str
    origin: str
    arity_log2: int
    element_sort: str
    opens_at: tuple[str, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise CommitmentError("a profile needs a name")
        if not isinstance(self.opens_at, tuple) or not self.opens_at:
            raise CommitmentError("a committed value profile declares where it opens")
        if len(self.opens_at) > MAX_OPENINGS:
            raise CommitmentError("opening occurrences exceed the declared bound")
        if len(set(self.opens_at)) != len(self.opens_at):
            raise CommitmentError("opening occurrences repeat")
        if not isinstance(self.arity_log2, int) or not 0 < self.arity_log2 <= MAX_ARITY_LOG2:
            raise CommitmentError("arity_log2 is outside the declared profile")
        if self.origin not in {"prover_message", "relation_derived", "preprocessed"}:
            raise CommitmentError("unknown committed-value origin")

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "construction": self.construction,
            "origin": self.origin,
            "arity_log2": self.arity_log2,
            "element_sort": self.element_sort,
            "opens_at": list(self.opens_at),
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.committed-value-profile.v1", self.term())


@dataclass(frozen=True)
class Opening:
    """Neither the commitment nor an element of its content class.

    An opening carries the commitment it claims to come from, the query it
    answers, the answer, and the authentication that ties the two.  It is the
    operand a check consumes; the commitment itself is not.
    """

    commitment_occurrence: str
    query: int
    answer: str
    auth_path: tuple[str, ...]
    leaf_tagged: bool = True

    def __post_init__(self) -> None:
        if not isinstance(self.commitment_occurrence, str) or not self.commitment_occurrence:
            raise CommitmentError("an opening names the commitment it opens")
        if not isinstance(self.query, int) or self.query < 0:
            raise CommitmentError("an opening query is a non-negative index")
        if not isinstance(self.auth_path, tuple):
            raise CommitmentError("an authentication path is a canonical sequence")
        if len(self.auth_path) > MAX_AUTH_PATH:
            raise CommitmentError("authentication path exceeds the declared bound")

    def term(self) -> dict[str, Any]:
        return {
            "commitment": self.commitment_occurrence,
            "query": self.query,
            "answer": self.answer,
            "auth_path": list(self.auth_path),
            "leaf_tagged": self.leaf_tagged,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.opening.v1", self.term())


def _digest(tag: bytes, payload: bytes) -> str:
    return hashlib.sha256(tag + payload).hexdigest()


def commitment_root(
    construction: CommitmentConstruction,
    leaves: tuple[str, ...],
) -> str:
    """A domain-separated binary commitment over exactly the declared leaves.

    The construction fixes how many leaves a commitment covers, so a prover
    holding more than it declares does not build a malformed tree — it builds a
    well-formed tree over fewer elements and keeps the rest outside the
    subject entirely.  That is why understatement is invisible here and why an
    affirmative opening carries :data:`BINDING_ASSUMPTION`.
    """

    if not isinstance(leaves, tuple) or not leaves:
        raise CommitmentError("a commitment covers at least one leaf")
    if len(leaves) != construction.cardinality:
        raise CommitmentError(
            "a commitment covers exactly the cardinality its construction declares"
        )
    level = [_digest(LEAF_TAG, leaf.encode("utf-8")) for leaf in leaves]
    while len(level) > 1:
        if len(level) % 2:
            level.append(level[-1])
        level = [
            _digest(NODE_TAG, bytes.fromhex(level[i]) + bytes.fromhex(level[i + 1]))
            for i in range(0, len(level), 2)
        ]
    return level[0]


def authentication_path(
    construction: CommitmentConstruction,
    leaves: tuple[str, ...],
    query: int,
) -> tuple[str, ...]:
    """The sibling path for ``query``, whose length is the declared depth."""

    if len(leaves) != construction.cardinality:
        raise CommitmentError(
            "an authentication path is drawn against the declared cardinality"
        )
    if not 0 <= query < len(leaves):
        raise CommitmentError("query outside the realized leaf range")
    level = [_digest(LEAF_TAG, leaf.encode("utf-8")) for leaf in leaves]
    index = query
    path: list[str] = []
    while len(level) > 1:
        if len(level) % 2:
            level.append(level[-1])
        sibling = index ^ 1
        path.append(level[sibling])
        level = [
            _digest(NODE_TAG, bytes.fromhex(level[i]) + bytes.fromhex(level[i + 1]))
            for i in range(0, len(level), 2)
        ]
        index //= 2
    return tuple(path)


def verify_opening(
    construction: CommitmentConstruction,
    profile: CommittedValueProfile,
    commitment_value: str,
    opening: Opening,
) -> CheckResult:
    """Check one opening against the commitment its profile declares.

    The four refusals are the ones a length-indexed, domain-separated opening
    can actually make.  The affirmative result carries
    :data:`BINDING_ASSUMPTION` because an understated arity is answered
    honestly within its declared range and is therefore invisible here.
    """

    boundary = "commitment:opening"
    if profile.construction != construction.name:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "commitment:binding-route",
            "R2-CMT-000",
            "the profile's binding route does not resolve to this construction",
        )
    if profile.arity_log2 != construction.arity_log2:
        return _result(
            OutcomeClass.MISMATCH,
            "commitment:binding-route",
            "R2-CMT-004",
            "the profile's declared arity disagrees with its construction",
        )
    if opening.commitment_occurrence not in profile.opens_at:
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-CMT-001",
            "the opening names a commitment this profile does not open",
        )
    if not 0 <= opening.query < construction.cardinality:
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-CMT-002",
            "the opening query lies outside the declared arity",
        )
    if len(opening.auth_path) != construction.auth_depth:
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-CMT-003",
            "the authentication length is not the construction's declared depth",
        )
    if not opening.leaf_tagged:
        return _result(
            OutcomeClass.MISMATCH,
            "commitment:domain-separation",
            "R2-CMT-005",
            "an internal node was presented where a leaf is required",
        )

    running = _digest(LEAF_TAG, opening.answer.encode("utf-8"))
    index = opening.query
    for sibling in opening.auth_path:
        left, right = (running, sibling) if index % 2 == 0 else (sibling, running)
        running = _digest(NODE_TAG, bytes.fromhex(left) + bytes.fromhex(right))
        index //= 2
    if running != commitment_value:
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-CMT-006",
            "the authenticated opening does not reconstruct the commitment",
        )
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary=boundary,
        code="R2-CMT-100",
        detail=(
            "the opening authenticates under the declared construction; this "
            "establishes neither that the declared arity is the realized one "
            f"nor any bound that reads it, which rest on {BINDING_ASSUMPTION}"
        ),
        subject=profile.identity,
        evidence={
            "construction": construction.identity,
            "opening": opening.identity,
            "required_assumption": BINDING_ASSUMPTION,
        },
    )


#: The construction table.  A sponge states its rate and capacity, a codec its
#: squeeze; a commitment states the relation an opening of it satisfies.
CONSTRUCTIONS: Mapping[str, CommitmentConstruction] = {
    # A vector commitment: an opening is a length-indexed authentication path.
    "r2.commit.binary-merkle.v1": CommitmentConstruction(
        name="r2.commit.binary-merkle.v1",
        element_sort="rs",
        arity_log2=10,
        query_sort="query_index",
        domain_separation="leaf-and-node-tagged",
        binding_game="r2.game.merkle-collision",
    ),
    # An anchor preimage.  The shipped registry resolves `binding_route` to
    # more than one construction: committed columns name a vector commitment
    # while a preprocessed table names `zkc.anchor.preimage`, whose opening is
    # the preimage itself rather than a path.  A design assuming one shape per
    # route would have missed that the *depth* is zero here, so the
    # length-indexed argument that catches an overstated arity does not apply
    # and the whole declared content is revealed instead.
    "r2.anchor.preimage.v1": CommitmentConstruction(
        name="r2.anchor.preimage.v1",
        element_sort="rs",
        arity_log2=8,
        query_sort="whole_preimage",
        domain_separation="preimage-tagged",
        binding_game="r2.game.sha256-preimage",
    ),
}


def resolve_construction(route: Any) -> CommitmentConstruction | CheckResult:
    """Resolve a binding route, or refuse it as a missing dependency."""

    if not isinstance(route, str) or route not in CONSTRUCTIONS:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "commitment:binding-route",
            "R2-CMT-000",
            "the binding route resolves against no admitted construction",
        )
    return CONSTRUCTIONS[route]


def construction_table_id() -> str:
    """One identity over the admitted construction table."""

    return semantic_id(
        "r2.commitment-construction-table.v1",
        {name: value.term() for name, value in sorted(CONSTRUCTIONS.items())},
    )


__all__ = [
    "BINDING_ASSUMPTION",
    "CONSTRUCTIONS",
    "CommitmentConstruction",
    "CommitmentError",
    "CommittedValueProfile",
    "Opening",
    "authentication_path",
    "commitment_root",
    "construction_table_id",
    "resolve_construction",
    "verify_opening",
]
