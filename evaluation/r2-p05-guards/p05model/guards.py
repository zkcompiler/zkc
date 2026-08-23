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

**Size is not work, and an earlier version of this module measured only size.**
It walked every assignment and memoised each node on the function it denotes.
That returns the correct reduced node count, but it visits ``2^|order|`` leaves
whatever the diagram looks like, so the interleaved and separated orders cost
exactly the same to build: 65536 predicate evaluations each at ``n=8``, for
diagrams of 18 and 512 nodes.  A cost model whose cost does not vary with the
representation cannot say anything about the representation.

So the diagram is built the way a real implementation builds one: from the
guard *syntax*, by ``apply`` over a unique table, with memoisation on operand
node pairs.  Then the work counters below track the structure rather than the
input width, and the two orders separate in work as well as in size.

What this module still does not do: inhabit the other two representations the
decision is choosing among.  Canonical-syntax-plus-certificates and a derived
ROBDD witness have no code here, so these measurements price one lane rather
than choosing among three.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping, Sequence

from .terms import CheckResult, OutcomeClass, semantic_id


#: A guard whose diagram exceeds this is refused rather than stored: identity
#: work must be bounded by something the checker declares, not by hope.
#:
#: The value has to be one the adversarial case actually crosses, or the
#: refusal path is never exercised by the envelope it claims to enforce.  The
#: separated order needs 512 nodes at ``n = 8`` and the interleaved order needs
#: 18, so a bound of 256 admits the good order and refuses the bad one at the
#: width the tests measure.  A previous value of 512 sat exactly on the
#: adversarial case and, against a ``>`` comparison, refused nothing.
MAX_GUARD_NODES = 256

#: Work is bounded separately from size.  A guard can stay under the node bound
#: while costing far more to build than storing it suggests, so the envelope
#: declares both and the checker reports both.
MAX_GUARD_WORK = 4096

FALSE = 0
TRUE = 1


@dataclass(frozen=True)
class GuardProfile:
    """The declared cost envelope for guard representation."""

    name: str
    max_nodes: int = MAX_GUARD_NODES
    max_work: int = MAX_GUARD_WORK

    def term(self) -> dict[str, object]:
        return {
            "name": self.name,
            "max_nodes": self.max_nodes,
            "max_work": self.max_work,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.p05.guard-profile.v1", self.term())


class GuardError(ValueError):
    """A malformed guard declaration."""


# --- guard syntax -------------------------------------------------------------
#
# The corpus contract admits exactly two atom kinds:
#
#     GuardAtom = BooleanAtom(BooleanValueRef)
#               | FiniteValueEquals(ValueRef, CanonicalSemanticValue)
#
# Both are modelled, because the finite-domain atom is the one whose encoding
# changes the variable count and therefore both the order and the node count.


@dataclass(frozen=True)
class BooleanAtom:
    """An earlier Boolean value that is not another guard decision."""

    ref: str

    @property
    def key(self) -> str:
        return f"bool:{self.ref}"


@dataclass(frozen=True)
class FiniteValueEquals:
    """Equality of a finite-domain value against one canonical member."""

    ref: str
    value: str

    @property
    def key(self) -> str:
        return f"eq:{self.ref}={self.value}"


Atom = BooleanAtom | FiniteValueEquals


@dataclass(frozen=True)
class Not:
    operand: Any


@dataclass(frozen=True)
class And:
    operands: tuple[Any, ...]


@dataclass(frozen=True)
class Or:
    operands: tuple[Any, ...]


Formula = Atom | Not | And | Or


def atom_keys(formula: Any) -> tuple[str, ...]:
    """Every distinct atom key in ``formula``, in first-occurrence order."""

    seen: dict[str, None] = {}

    def walk(node: Any) -> None:
        if isinstance(node, (BooleanAtom, FiniteValueEquals)):
            seen.setdefault(node.key, None)
        elif isinstance(node, Not):
            walk(node.operand)
        elif isinstance(node, (And, Or)):
            for operand in node.operands:
                walk(operand)
        else:
            raise GuardError(f"not a guard formula node: {node!r}")

    walk(formula)
    return tuple(seen)


# --- the diagram --------------------------------------------------------------


@dataclass
class GuardCost:
    """What building one canonical diagram cost.

    ``nodes`` is what gets stored and enters identity.  ``expansions`` is what
    the build actually did: the number of ``apply`` calls that missed the memo
    and had to recurse.  The two are reported separately because a bound on one
    does not bound the other.
    """

    nodes: int
    expansions: int
    calls: int
    variables: int

    def term(self) -> dict[str, int]:
        return {
            "nodes": self.nodes,
            "expansions": self.expansions,
            "calls": self.calls,
            "variables": self.variables,
        }


@dataclass
class Robdd:
    """A reduced ordered decision diagram over a fixed variable order."""

    order: tuple[str, ...]
    #: (var_index, low, high) -> node id.  Reduction is this table plus the
    #: low == high collapse in `mk`; nothing else is needed for canonicity.
    unique: dict[tuple[int, int, int], int] = field(default_factory=dict)
    #: node id -> (var_index, low, high); terminals are 0 and 1 and absent here.
    nodes: dict[int, tuple[int, int, int]] = field(default_factory=dict)
    memo: dict[tuple[str, int, int], int] = field(default_factory=dict)
    calls: int = 0
    expansions: int = 0

    def __post_init__(self) -> None:
        if len(set(self.order)) != len(self.order):
            raise GuardError("a variable order repeats a variable")
        self._index = {name: i for i, name in enumerate(self.order)}
        self._next = 2

    def _var_index(self, node: int) -> int:
        if node in (FALSE, TRUE):
            return len(self.order)
        return self.nodes[node][0]

    def mk(self, var_index: int, low: int, high: int) -> int:
        if low == high:
            return low  # reduction: the variable does not matter here
        key = (var_index, low, high)
        node = self.unique.get(key)
        if node is None:
            node = self._next
            self._next += 1
            self.nodes[node] = key
            self.unique[key] = node
        return node

    def variable(self, name: str) -> int:
        if name not in self._index:
            raise GuardError(f"variable is outside the declared order: {name}")
        return self.mk(self._index[name], FALSE, TRUE)

    def negate(self, node: int) -> int:
        return self.apply("nand", node, TRUE)

    def apply(self, op: str, left: int, right: int) -> int:
        """Structural apply with memoisation on the operand pair.

        Every call is counted; every call that misses the memo and recurses is
        counted separately.  The second number is the one that tracks diagram
        structure, which is the whole point of building this way.
        """

        self.calls += 1
        terminal = _terminal(op, left, right)
        if terminal is not None:
            return terminal
        key = (op, left, right)
        hit = self.memo.get(key)
        if hit is not None:
            return hit
        self.expansions += 1
        top = min(self._var_index(left), self._var_index(right))
        low = self.apply(op, _low(self, left, top), _low(self, right, top))
        high = self.apply(op, _high(self, left, top), _high(self, right, top))
        node = self.mk(top, low, high)
        self.memo[key] = node
        return node

    def build(self, formula: Any) -> int:
        if isinstance(formula, (BooleanAtom, FiniteValueEquals)):
            return self.variable(formula.key)
        if isinstance(formula, Not):
            return self.negate(self.build(formula.operand))
        if isinstance(formula, And):
            node = TRUE
            for operand in formula.operands:
                node = self.apply("and", node, self.build(operand))
            return node
        if isinstance(formula, Or):
            node = FALSE
            for operand in formula.operands:
                node = self.apply("or", node, self.build(operand))
            return node
        raise GuardError(f"not a guard formula node: {formula!r}")

    def reachable(self, root: int) -> int:
        """Nodes reachable from ``root``, terminals included.

        The unique table can hold nodes an intermediate result created and the
        final diagram no longer uses, so what enters identity is the reachable
        count, not the table size.
        """

        seen: set[int] = set()
        stack = [root]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            if node not in (FALSE, TRUE):
                _, low, high = self.nodes[node]
                stack.extend((low, high))
        return len(seen)


def _terminal(op: str, left: int, right: int) -> int | None:
    if op == "and":
        if left == FALSE or right == FALSE:
            return FALSE
        if left == TRUE:
            return right
        if right == TRUE:
            return left
        return None
    if op == "or":
        if left == TRUE or right == TRUE:
            return TRUE
        if left == FALSE:
            return right
        if right == FALSE:
            return left
        return None
    if op == "nand":
        if left == FALSE or right == FALSE:
            return TRUE
        if left == TRUE and right == TRUE:
            return FALSE
        return None
    raise GuardError(f"unknown operator: {op}")


def _low(diagram: Robdd, node: int, top: int) -> int:
    if node in (FALSE, TRUE) or diagram.nodes[node][0] != top:
        return node
    return diagram.nodes[node][1]


def _high(diagram: Robdd, node: int, top: int) -> int:
    if node in (FALSE, TRUE) or diagram.nodes[node][0] != top:
        return node
    return diagram.nodes[node][2]


def robdd_cost(formula: Any, order: Sequence[str]) -> GuardCost:
    """Build the canonical diagram and report both size and work."""

    diagram = Robdd(tuple(order))
    root = diagram.build(formula)
    return GuardCost(
        nodes=diagram.reachable(root),
        expansions=diagram.expansions,
        calls=diagram.calls,
        variables=len(order),
    )


def robdd_size(formula: Any, order: Sequence[str]) -> int:
    """Node count of the reduced ordered decision diagram under ``order``."""

    return robdd_cost(formula, order).nodes


# --- the separating example ---------------------------------------------------


def pairing_formula(n: int) -> Or:
    """``(x0 AND y0) OR ... OR (xn AND yn)`` — the separating example."""

    return Or(
        tuple(
            And((BooleanAtom(f"x{i}"), BooleanAtom(f"y{i}")))
            for i in range(n)
        )
    )


def pairing_predicate(n: int) -> Callable[[Mapping[str, bool]], bool]:
    """The same function as a predicate, for checking the diagram is right."""

    def predicate(assignment: Mapping[str, bool]) -> bool:
        return any(assignment[f"x{i}"] and assignment[f"y{i}"] for i in range(n))

    return predicate


def interleaved_order(n: int) -> tuple[str, ...]:
    return tuple(f"bool:{name}" for i in range(n) for name in (f"x{i}", f"y{i}"))


def separated_order(n: int) -> tuple[str, ...]:
    return tuple(f"bool:x{i}" for i in range(n)) + tuple(f"bool:y{i}" for i in range(n))


def finite_domain_formula(ref: str, members: Sequence[str]) -> Or:
    """``ref = m0 OR ref = m1 OR ...`` over one declared finite domain.

    The finite atom is modelled because its encoding is what makes a guard's
    variable count depend on domain size rather than on the number of values
    the author mentioned.
    """

    if not members:
        raise GuardError("a finite domain has at least one member")
    return Or(tuple(FiniteValueEquals(ref, member) for member in members))


# --- admission ----------------------------------------------------------------


def admit_guard(
    profile: GuardProfile,
    formula: Any,
    order: Sequence[str],
) -> CheckResult:
    """Refuse a guard whose canonical diagram or build exceeds the envelope.

    The refusal is the point.  A guard that cannot be represented within the
    envelope is a resource fact, not a semantic verdict, so it is reported as
    ``ResourceExceeded`` and no protocol conclusion is drawn from it.
    """

    try:
        cost = robdd_cost(formula, order)
    except GuardError as error:
        return CheckResult(
            outcome=OutcomeClass.MALFORMED,
            boundary="guard:representation",
            code="P05-000",
            detail=str(error),
            subject=profile.identity,
        )
    if cost.nodes > profile.max_nodes:
        return CheckResult(
            outcome=OutcomeClass.RESOURCE_EXCEEDED,
            boundary="guard:representation",
            code="P05-001",
            detail=(
                f"the canonical diagram needs {cost.nodes} nodes under this "
                f"order, beyond the declared {profile.max_nodes}"
            ),
            subject=profile.identity,
            evidence=cost.term(),
        )
    if cost.expansions > profile.max_work:
        return CheckResult(
            outcome=OutcomeClass.RESOURCE_EXCEEDED,
            boundary="guard:work",
            code="P05-002",
            detail=(
                f"building the canonical diagram took {cost.expansions} "
                f"expansions, beyond the declared {profile.max_work}"
            ),
            subject=profile.identity,
            evidence=cost.term(),
        )
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary="guard:representation",
        code="P05-100",
        detail="the canonical diagram fits the declared envelope",
        subject=profile.identity,
        evidence=cost.term(),
    )


__all__ = [
    "FALSE",
    "MAX_GUARD_NODES",
    "MAX_GUARD_WORK",
    "TRUE",
    "And",
    "Atom",
    "BooleanAtom",
    "FiniteValueEquals",
    "Formula",
    "GuardCost",
    "GuardError",
    "GuardProfile",
    "Not",
    "Or",
    "Robdd",
    "admit_guard",
    "atom_keys",
    "finite_domain_formula",
    "interleaved_order",
    "pairing_formula",
    "pairing_predicate",
    "robdd_cost",
    "robdd_size",
    "separated_order",
]
