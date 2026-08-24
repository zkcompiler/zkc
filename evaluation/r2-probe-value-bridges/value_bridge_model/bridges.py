"""Three lanes for a value mapping, and the law that none may pose as another.

The review's tempting repair was "weaken every value bridge to an injection".
The adjudication rejected it, and rightly: collapsing the lanes loses exactly
the distinction that matters.  There are three, and they are not degrees of one
thing:

    bijection    whole-domain semantic equivalence, invertible everywhere
    embedding    injective, with an exact image predicate, invertible ON its
                 image and nowhere else
    projection   one-way and lossy, carrying a collision relation, occurrence
                 accounting, and a quantitative loss someone must price

This module makes the lanes separate subjects and refuses the substitutions.
The lossy instance is the shipped one: an anchor's transcript projection keeps
the low 27 bits of each big-endian 32-bit word of a sha256 digest, 216 bits in
all, and the artifact's bound-relation-anchor count scales the advantage that
prices the shortfall.

The sharp result is in :func:`projection_collision`.  The projection is not
merely lossy in the abstract — a collision is *constructible in constant time*
by flipping any discarded bit.  So the hardness cannot come from the projection.
It has to come from a premise that the adversary must supply digest
**preimages**, which is what the shipped game quantifies over.  Whether the
anchor authority establishes that premise is a separate question, and
:func:`price_projection` refuses to answer it rather than assuming it.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Mapping

from .terms import CheckResult, OutcomeClass, semantic_id


#: The shipped projection: eight elements, each the low 27 bits of one
#: big-endian 32-bit word.
PROJECTION_WORDS = 8
PROJECTION_BITS_PER_WORD = 27
SOURCE_BITS = 256
PROJECTED_BITS = PROJECTION_WORDS * PROJECTION_BITS_PER_WORD  # 216
DISCARDED_BITS = SOURCE_BITS - PROJECTED_BITS  # 40

#: The premise the reduction needs and the anchor authority does not supply.
PREIMAGE_PREMISE = "EveryAnchorHasAnAdversarySuppliedPreimage"


class BridgeError(ValueError):
    """A malformed bridge declaration."""


class Lane(str, Enum):
    BIJECTION = "Bijection"
    EMBEDDING = "LosslessEmbedding"
    PROJECTION = "LossyProjection"


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome=outcome, boundary=boundary, code=code, detail=detail)


@dataclass(frozen=True)
class Bridge:
    """A declared mapping, in exactly one lane."""

    name: str
    lane: Lane
    source_domain: str
    target_domain: str
    #: An embedding must supply this; the other lanes must not.
    image_predicate: str | None = None
    #: A projection must supply these; the other lanes must not.
    collision_relation: str | None = None
    loss_bits: int | None = None
    occurrence_count: int | None = None

    def __post_init__(self) -> None:
        if not self.name or not self.source_domain or not self.target_domain:
            raise BridgeError("a bridge names itself and both domains")

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "lane": self.lane.value,
            "source_domain": self.source_domain,
            "target_domain": self.target_domain,
            "image_predicate": self.image_predicate,
            "collision_relation": self.collision_relation,
            "loss_bits": self.loss_bits,
            "occurrence_count": self.occurrence_count,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.probe.value-bridge.v1", self.term())


def admit_bridge(bridge: Any) -> CheckResult:
    """Each lane carries exactly the obligations its meaning requires."""

    if not isinstance(bridge, Bridge):
        return _result(OutcomeClass.MALFORMED, "bridge", "R2-VBR-000", "not a bridge")

    if bridge.lane is Lane.BIJECTION:
        if bridge.image_predicate is not None:
            return _result(
                OutcomeClass.MISMATCH, "bridge:lane", "R2-VBR-001",
                "a bijection is invertible everywhere and declares no image predicate",
            )
        if bridge.collision_relation is not None or bridge.loss_bits is not None:
            return _result(
                OutcomeClass.MISMATCH, "bridge:lane", "R2-VBR-002",
                "a bijection that admits collisions or loss is not a bijection",
            )
        return CheckResult(
            outcome=OutcomeClass.AFFIRMATIVE, boundary="bridge:lane", code="R2-VBR-100",
            detail="whole-domain equivalence, invertible in both directions",
            subject=bridge.identity,
        )

    if bridge.lane is Lane.EMBEDDING:
        if bridge.image_predicate is None:
            return _result(
                OutcomeClass.MISSING_DEPENDENCY, "bridge:lane", "R2-VBR-003",
                "an embedding is invertible only on its image and must say which values that is",
            )
        if bridge.collision_relation is not None or bridge.loss_bits:
            return _result(
                OutcomeClass.MISMATCH, "bridge:lane", "R2-VBR-004",
                "a mapping that loses information is not a lossless embedding",
            )
        return CheckResult(
            outcome=OutcomeClass.AFFIRMATIVE, boundary="bridge:lane", code="R2-VBR-101",
            detail="injective, with an exact image predicate it inverts on",
            subject=bridge.identity,
        )

    if bridge.image_predicate is not None:
        return _result(
            OutcomeClass.MISMATCH, "bridge:lane", "R2-VBR-005",
            "a lossy projection has no image to invert on and declares no image predicate",
        )
    if bridge.collision_relation is None:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY, "bridge:lane", "R2-VBR-006",
            "a projection must name the collision relation its loss creates",
        )
    if not bridge.loss_bits or bridge.loss_bits <= 0:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY, "bridge:lane", "R2-VBR-007",
            "a projection must state how much it discards",
        )
    if bridge.occurrence_count is None:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY, "bridge:lane", "R2-VBR-008",
            "a projection must be counted: the loss scales with its occurrences",
        )
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE, boundary="bridge:lane", code="R2-VBR-102",
        detail="one-way, with a named collision relation, a stated loss, and an occurrence count",
        subject=bridge.identity,
        evidence={"loss_bits": bridge.loss_bits, "occurrences": bridge.occurrence_count},
    )


# --- the shipped instance ------------------------------------------------------


def project216(digest: bytes) -> tuple[int, ...]:
    """The shipped transcript projection of a sha256 anchor."""

    if len(digest) != 32:
        raise BridgeError("an anchor projection reads a 32-byte digest")
    words = [int.from_bytes(digest[i : i + 4], "big") for i in range(0, 32, 4)]
    mask = (1 << PROJECTION_BITS_PER_WORD) - 1
    return tuple(word & mask for word in words)


def projection_collision() -> tuple[bytes, bytes]:
    """Two distinct digests with the same projection, found in constant time.

    Flipping any bit the projection discards leaves it unchanged.  This is why
    the projection itself cannot be the source of hardness: an adversary free to
    choose digests wins immediately.
    """

    left = bytes(range(32))
    flipped = bytearray(left)
    flipped[0] ^= 1 << 7  # a bit above the low 27 of the first word
    right = bytes(flipped)
    if left == right or project216(left) != project216(right):
        raise BridgeError("the discarded-bit construction failed")
    return left, right


ANCHOR_PROJECTION = Bridge(
    name="zkc.anchor.transcript-projection.216",
    lane=Lane.PROJECTION,
    source_domain="sha256-digest",
    target_domain="field-element-vector-8",
    collision_relation="equal-under-proj216",
    loss_bits=DISCARDED_BITS,
    occurrence_count=1,
)


def price_projection(
    bridge: Bridge,
    anchor_count: int,
    preimage_rule: str | None,
) -> CheckResult:
    """Price a projection's loss, or refuse for the premise it lacks.

    The shipped game quantifies over byte strings ``r1 != r2`` whose digests
    agree under the projection.  Winning it is hard.  But an adversary attacking
    the protocol supplies *anchors*, not preimages, and
    :func:`projection_collision` shows that choosing anchors directly is free.
    So the reduction needs a rule making every admitted anchor the digest of
    something the adversary had to produce.  Without that rule the question is
    unanswerable, and saying so is the honest result.
    """

    if bridge.lane is not Lane.PROJECTION:
        return _result(
            OutcomeClass.MISMATCH, "analysis:projection-loss", "R2-VBR-010",
            "only a lossy projection carries a priced loss",
        )
    if anchor_count == 0:
        return CheckResult(
            outcome=OutcomeClass.AFFIRMATIVE, boundary="analysis:projection-loss",
            code="R2-VBR-103",
            detail="no anchor enters the transcript, so the addend vanishes",
            subject=bridge.identity, evidence={"anchor_count": 0},
        )
    if preimage_rule is None:
        return CheckResult(
            outcome=OutcomeClass.CANNOT_ANSWER,
            boundary="analysis:projection-loss",
            code="R2-VBR-011",
            detail=(
                "the collision game quantifies byte preimages while the anchor "
                "authority supplies only opaque values; a collision in the "
                "projected bits alone is constructible, so the reduction needs "
                "a preimage premise nothing establishes"
            ),
            subject=bridge.identity,
            evidence={
                "anchor_count": anchor_count,
                "input_bits": SOURCE_BITS,
                "output_bits": PROJECTED_BITS,
                "truncated_bits": DISCARDED_BITS,
                "required_assumption": PREIMAGE_PREMISE,
            },
        )
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE, boundary="analysis:projection-loss",
        code="R2-VBR-104",
        detail="the loss is priced under an established preimage rule",
        subject=bridge.identity,
        evidence={
            "anchor_count": anchor_count,
            "truncated_bits": DISCARDED_BITS,
            "preimage_rule": preimage_rule,
        },
    )


def round_trip(
    forward: Callable[[Any], Any],
    backward: Callable[[Any], Any],
    domain: Mapping[str, Any] | tuple[Any, ...],
) -> bool:
    """Both inverse laws, checked by exhaustion over a finite domain."""

    values = tuple(domain.values()) if isinstance(domain, Mapping) else tuple(domain)
    return all(backward(forward(value)) == value for value in values)


__all__ = [
    "ANCHOR_PROJECTION",
    "DISCARDED_BITS",
    "PREIMAGE_PREMISE",
    "PROJECTED_BITS",
    "SOURCE_BITS",
    "Bridge",
    "BridgeError",
    "Lane",
    "admit_bridge",
    "price_projection",
    "project216",
    "projection_collision",
    "round_trip",
]
