"""Is a canonical guard cheap? Measured, not assumed.

The redesign puts path conditions in the identity preimage as reduced ordered
decision diagrams over a regime-fixed variable order, and the review recorded
the resulting worry as ``COST-1``: fixed ordering buys canonicity, not
compactness, so a stored diagram can be exponential in the number of atoms and
identity work becomes unbounded.

The worry is answerable rather than arguable.  The textbook separating example
is the *hidden weighted-bit*-style pairing function

    (x1 AND y1) OR (x2 AND y2) OR ... OR (xn AND yn)

whose reduced diagram is linear in ``n`` under the interleaved order
``x1,y1,x2,y2,...`` and exponential under the separated order
``x1,...,xn,y1,...,yn``.  Both orders are legitimate fixed orders, so a regime
that fixes the wrong one pays exponentially for a formula an author had every
reason to write.

:func:`robdd_size` builds the reduced diagram and returns its node count, so
the question is settled by running it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from .terms import CheckResult, OutcomeClass, semantic_id


#: A guard whose diagram exceeds this is refused rather than stored: identity
#: work must be bounded by something the checker declares, not by hope.
MAX_GUARD_NODES = 512


@dataclass(frozen=True)
class GuardProfile:
    """The declared cost envelope for guard representation."""

    name: str
    max_nodes: int = MAX_GUARD_NODES

    def term(self) -> dict[str, object]:
        return {"name": self.name, "max_nodes": self.max_nodes}

    @property
    def identity(self) -> str:
        return semantic_id("r2.p05.guard-profile.v1", self.term())


def robdd_size(
    predicate: Callable[[dict[str, bool]], bool],
    order: Sequence[str],
) -> int:
    """Node count of the reduced ordered decision diagram under ``order``.

    Built by memoising each node on the function it denotes, which is exactly
    what reduction does: two subtrees deciding the same function are one node.
    """

    memo: dict[tuple, int] = {}
    nodes: dict[int, object] = {}

    def build(index: int, assigned: dict[str, bool]) -> int:
        if index == len(order):
            leaf = predicate(assigned)
            key = ("leaf", leaf)
            if key not in memo:
                memo[key] = len(nodes)
                nodes[memo[key]] = key
            return memo[key]
        low = build(index + 1, {**assigned, order[index]: False})
        high = build(index + 1, {**assigned, order[index]: True})
        if low == high:
            return low  # reduction: the variable does not matter here
        key = ("node", order[index], low, high)
        if key not in memo:
            memo[key] = len(nodes)
            nodes[memo[key]] = key
        return memo[key]

    build(0, {})
    return len(nodes)


def pairing_predicate(n: int) -> Callable[[dict[str, bool]], bool]:
    """``(x1 AND y1) OR ... OR (xn AND yn)`` — the separating example."""

    def predicate(assignment: dict[str, bool]) -> bool:
        return any(assignment[f"x{i}"] and assignment[f"y{i}"] for i in range(n))

    return predicate


def interleaved_order(n: int) -> tuple[str, ...]:
    return tuple(name for i in range(n) for name in (f"x{i}", f"y{i}"))


def separated_order(n: int) -> tuple[str, ...]:
    return tuple(f"x{i}" for i in range(n)) + tuple(f"y{i}" for i in range(n))


def admit_guard(
    profile: GuardProfile,
    predicate: Callable[[dict[str, bool]], bool],
    order: Sequence[str],
) -> CheckResult:
    """Refuse a guard whose canonical diagram exceeds the declared envelope.

    The refusal is the point.  A guard that cannot be represented within the
    envelope is a resource fact, not a semantic verdict, so it is reported as
    ``ResourceExceeded`` and no protocol conclusion is drawn from it.
    """

    size = robdd_size(predicate, order)
    if size > profile.max_nodes:
        return CheckResult(
            outcome=OutcomeClass.RESOURCE_EXCEEDED,
            boundary="guard:representation",
            code="P05-001",
            detail=(
                f"the canonical diagram needs {size} nodes under this order, "
                f"beyond the declared {profile.max_nodes}"
            ),
            subject=profile.identity,
            evidence={"nodes": size, "variables": len(order)},
        )
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary="guard:representation",
        code="P05-100",
        detail="the canonical diagram fits the declared envelope",
        subject=profile.identity,
        evidence={"nodes": size, "variables": len(order)},
    )


__all__ = [
    "MAX_GUARD_NODES",
    "GuardProfile",
    "admit_guard",
    "interleaved_order",
    "pairing_predicate",
    "robdd_size",
    "separated_order",
]
