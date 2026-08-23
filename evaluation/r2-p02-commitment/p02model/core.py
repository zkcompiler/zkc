"""A minimal commitment-and-opening protocol, in the closed action vocabulary.

This witness exists to falsify one claim:

    an opening needs no new action kind — it is a prover **message** carrying an
    ``Opening`` value plus a verifier **check** that consumes it.

The test is only honest if the shape law is the one the FRI witness already
enforces rather than one written to accommodate the answer.  The per-kind rules
below are therefore ported from ``r2model/frigrind.py``'s ``_admit_core``
without relaxation: the occurrence-prefix rule, the label-equals-suffix rule,
the multiplicity and domain shapes, the per-sort domain bounds, the actor
assignment per kind, and the challenge-influence discipline.  Every place this
module had to *add* a rule rather than reuse one is marked ``ADDED``; every
place it had to *weaken* one would be a falsification and is marked ``RELAXED``.

At the time of writing there are no ``RELAXED`` marks.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Any

from .commitment import (
    BINDING_ASSUMPTION,
    CommitmentConstruction,
    CommittedValueProfile,
    Opening,
    authentication_path,
    commitment_root,
    resolve_construction,
    verify_opening,
)
from .terms import CheckResult, OutcomeClass, semantic_id


MAX_CORE_ACTIONS = 64


class ActionKind(str, Enum):
    """Unchanged from the FRI witness.  The claim is that this need not grow."""

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
    QUERY_INDEX = "query_index"
    BOOL = "bool"
    RESIDUAL = "residual"
    #: ADDED.  A value sort, not an action kind — which is precisely the claim.
    OPENING = "opening"


class PredicateKind(str, Enum):
    #: ADDED.  A check contract, not an action kind.
    OPENING_AUTHENTICATES = "OpeningAuthenticatesUnderConstruction"


class RouteFormula(str, Enum):
    OPENING_ONLY = "OpeningCheck"


class ResidualKind(str, Enum):
    COMMITMENT_TERMINAL_NOT_MODELED = "CommitmentTerminalNotModeled"


class CoinSource(str, Enum):
    UNIFORM_FINITE = "UniformFinite"


class Visibility(str, Enum):
    PUBLIC = "Public"


class Mutation(str, Enum):
    BASE = "base"
    FOREIGN_COMMITMENT = "foreign_commitment"
    QUERY_OUT_OF_RANGE = "query_out_of_range"
    SHORT_AUTHENTICATION = "short_authentication"
    NODE_POSED_AS_LEAF = "node_posed_as_leaf"
    UNDERSTATED_ARITY = "understated_arity"
    #: Structural mutations, testing the shape law rather than the opening.
    OPENING_WITHOUT_CHECK = "opening_without_check"
    COMMITMENT_AS_CHECK_OPERAND = "commitment_as_check_operand"


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome=outcome, boundary=boundary, code=code, detail=detail)


@dataclass(frozen=True)
class CoreAction:
    """The FRI witness's action record, plus one optional field.

    ``profile`` is emitted into the identity term **only when present**, so an
    unprofiled action encodes exactly as it did before the commitment subject
    existed.  That is the same discipline the shipped system chose when it
    added value profiles: a profiled value is a new encoder family rather than
    a rotation of every artifact.
    """

    occurrence: str
    kind: ActionKind
    label: str
    actor: Actor
    value_sort: ValueSort
    cardinality: int | None = None
    count: int = 1
    coin_source: CoinSource | None = None
    visibility: Visibility | None = None
    required_influences: tuple[str, ...] = ()
    predicate: PredicateKind | None = None
    route_formula: RouteFormula | None = None
    residual: ResidualKind | None = None
    profile: str | None = None  # ADDED

    def term(self) -> dict[str, Any]:
        body: dict[str, Any] = {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "label": self.label,
            "actor": self.actor.value,
            "sort": self.value_sort.value,
            "cardinality": self.cardinality,
            "count": self.count,
            "coin_source": self.coin_source.value if self.coin_source else None,
            "visibility": self.visibility.value if self.visibility else None,
            "required_influences": list(self.required_influences),
            "predicate": self.predicate.value if self.predicate else None,
            "route_formula": self.route_formula.value if self.route_formula else None,
            "residual": self.residual.value if self.residual else None,
        }
        if self.profile is not None:
            body["profile"] = self.profile
        return body

    @property
    def operand_sort(self) -> ValueSort | None:
        """The sort this value satisfies an operand slot with.

        A profiled value carries a commitment, not an element of the class its
        content is drawn from, so it satisfies no operand slot.  This mirrors
        ``bareClass()`` returning empty for a profiled value in the shipped
        carrier, and it is what keeps a commitment and an element from standing
        in for one another.
        """

        return None if self.profile is not None else self.value_sort


@dataclass(frozen=True)
class CommitmentCore:
    actions: tuple[CoreAction, ...]
    construction: CommitmentConstruction
    profile: CommittedValueProfile

    @property
    def schedule(self) -> tuple[str, ...]:
        return tuple(action.occurrence for action in self.actions)

    def term(self) -> dict[str, Any]:
        return {
            "actions": [action.term() for action in self.actions],
            "schedule": list(self.schedule),
            "construction": self.construction.term(),
            "profile": self.profile.term(),
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.p02.commitment-core.v1", self.term())


COMMITMENT = "statement:root"
QUERY = "challenge:query"
OPENING = "message:opening"
CHECK = "check:opening_authentic"
ROUTE = "route:accept"
RESIDUAL = "residual:commitment-terminal-not-modeled"


def build_core(construction: CommitmentConstruction) -> CommitmentCore:
    """Six actions, every one of them an existing kind."""

    profile = CommittedValueProfile(
        name="r2.p02.profile.committed-vector",
        construction=construction.name,
        origin="prover_message",
        arity_log2=construction.arity_log2,
        element_sort=construction.element_sort,
        opens_at=(COMMITMENT,),
    )
    actions = (
        CoreAction(
            COMMITMENT, ActionKind.STATEMENT, "root", Actor.APPLICATION,
            ValueSort.RS, 1 << 128, profile=profile.name,
        ),
        CoreAction(
            QUERY, ActionKind.CHALLENGE, "query", Actor.VERIFIER,
            ValueSort.QUERY_INDEX, construction.cardinality, 1,
            CoinSource.UNIFORM_FINITE, Visibility.PUBLIC, (COMMITMENT,),
        ),
        CoreAction(
            OPENING, ActionKind.MESSAGE, "opening", Actor.PROVER,
            ValueSort.OPENING, 1,
        ),
        CoreAction(
            CHECK, ActionKind.CHECK, "opening_authentic", Actor.VERIFIER,
            ValueSort.BOOL, 2, predicate=PredicateKind.OPENING_AUTHENTICATES,
        ),
        CoreAction(
            ROUTE, ActionKind.ROUTE, "accept", Actor.VERIFIER,
            ValueSort.BOOL, 2, route_formula=RouteFormula.OPENING_ONLY,
        ),
        CoreAction(
            RESIDUAL, ActionKind.RESIDUAL, "commitment-terminal-not-modeled",
            Actor.SOURCE_BOUNDARY, ValueSort.RESIDUAL,
            residual=ResidualKind.COMMITMENT_TERMINAL_NOT_MODELED,
        ),
    )
    return CommitmentCore(actions, construction, profile)


_KIND_PREFIX = {
    ActionKind.STATEMENT: "statement:",
    ActionKind.CHALLENGE: "challenge:",
    ActionKind.MESSAGE: "message:",
    ActionKind.CHECK: "check:",
    ActionKind.ROUTE: "route:",
    ActionKind.RESIDUAL: "residual:",
}

_KIND_ACTOR = {
    ActionKind.STATEMENT: Actor.APPLICATION,
    ActionKind.CHALLENGE: Actor.VERIFIER,
    ActionKind.MESSAGE: Actor.PROVER,
    ActionKind.CHECK: Actor.VERIFIER,
    ActionKind.ROUTE: Actor.VERIFIER,
    ActionKind.RESIDUAL: Actor.SOURCE_BOUNDARY,
}

_SORT_BOUND = {
    ValueSort.RS: 1 << 128,
    ValueSort.QUERY_INDEX: 1 << 64,
    ValueSort.BOOL: 2,
}


def admit_core(core: Any) -> CheckResult:
    """The FRI witness's shape law, ported without relaxation."""

    if not isinstance(core, CommitmentCore):
        return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-000", "not a core")
    actions = core.actions
    if not actions or len(actions) > MAX_CORE_ACTIONS:
        return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-001", "core size is outside the bound")
    if len(set(core.schedule)) != len(core.schedule):
        return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-002", "core occurrence is duplicated")
    if actions[-1].kind is not ActionKind.RESIDUAL:
        return _result(OutcomeClass.MISMATCH, "source-boundary", "P02-CORE-003", "core does not end at its declared residual")

    for action in actions:
        if not isinstance(action.kind, ActionKind) or not isinstance(action.actor, Actor) or not isinstance(action.value_sort, ValueSort):
            return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-004", "core action vocabulary is open")
        if not action.occurrence.startswith(_KIND_PREFIX[action.kind]):
            return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-005", "action occurrence kind prefix differs")
        if action.label != action.occurrence.split(":", 1)[1]:
            return _result(OutcomeClass.MISMATCH, "closed-core", "P02-CORE-006", "action label differs from its occurrence")
        if action.actor is not _KIND_ACTOR[action.kind]:
            return _result(OutcomeClass.MISMATCH, "closed-core", "P02-CORE-007", "action actor differs from its kind")
        if isinstance(action.count, bool) or not isinstance(action.count, int) or action.count <= 0:
            return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-008", "action multiplicity is malformed")
        if action.cardinality is not None and (
            isinstance(action.cardinality, bool) or not isinstance(action.cardinality, int) or action.cardinality <= 0
        ):
            return _result(OutcomeClass.MALFORMED, "closed-core", "P02-CORE-009", "action domain is malformed")
        bound = _SORT_BOUND.get(action.value_sort)
        if bound is not None and action.cardinality is not None and action.cardinality > bound:
            return _result(OutcomeClass.UNSUPPORTED, "closed-core", "P02-CORE-010", "action domain exceeds its canonical codec profile")
        if action.kind is ActionKind.MESSAGE and action.count != 1:
            return _result(OutcomeClass.MISMATCH, "closed-core", "P02-CORE-011", "a prover message has multiplicity one")
        if action.kind is ActionKind.CHALLENGE and not action.required_influences:
            return _result(OutcomeClass.MISMATCH, "closed-core", "P02-CORE-012", "a challenge declares what it binds")

    # ADDED: the opening discipline.  A commitment is published by a profiled
    # action, and the profile's binding route must resolve to a construction.
    profiled = [action for action in actions if action.profile is not None]
    if len(profiled) != 1:
        return _result(OutcomeClass.MISMATCH, "commitment:publication", "P02-CORE-013", "exactly one action publishes the commitment")
    if profiled[0].occurrence not in core.profile.opens_at:
        return _result(OutcomeClass.MISMATCH, "commitment:publication", "P02-CORE-014", "the profile does not open the action that publishes it")
    resolved = resolve_construction(core.profile.construction)
    if isinstance(resolved, CheckResult):
        return resolved

    openings = [a for a in actions if a.value_sort is ValueSort.OPENING]
    if len(openings) != 1 or openings[0].kind is not ActionKind.MESSAGE:
        return _result(OutcomeClass.MISMATCH, "commitment:opening", "P02-CORE-015", "an opening is carried by exactly one prover message")
    consumers = [
        a for a in actions
        if a.kind is ActionKind.CHECK and a.predicate is PredicateKind.OPENING_AUTHENTICATES
    ]
    if len(consumers) != 1:
        return _result(OutcomeClass.MISMATCH, "commitment:opening", "P02-CORE-016", "an opening is consumed by exactly one check")
    if core.schedule.index(openings[0].occurrence) > core.schedule.index(consumers[0].occurrence):
        return _result(OutcomeClass.MISMATCH, "commitment:opening", "P02-CORE-017", "the opening follows the check that consumes it")

    # The operand rule is deliberately NOT a check here.  ``operand_sort``
    # returns nothing exactly when a profile is present, so a commitment cannot
    # reach an operand slot at all; a rule testing that would restate its own
    # derivation and could never fail.  Construction-enforced is stronger than
    # check-enforced, and saying so is more honest than shipping a rule that
    # always passes.  What *is* checkable is that the publication stays
    # profiled, which P02-CORE-013 above already enforces.

    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary="closed-core",
        code="P02-CORE-100",
        detail="the commitment core admits under the ported shape law with no new action kind",
        subject=core.identity,
        evidence={"construction": resolved.identity, "profile": core.profile.identity},
    )


def honest_leaves(construction: CommitmentConstruction) -> tuple[str, ...]:
    return tuple(f"e{index}" for index in range(construction.cardinality))


def run_opening(
    core: CommitmentCore,
    leaves: tuple[str, ...],
    query: int,
    mutation: Mutation = Mutation.BASE,
) -> CheckResult:
    """Execute the check action against one opening, under a mutation."""

    construction = core.construction
    root = commitment_root(construction, leaves)
    path = authentication_path(construction, leaves, query)
    opening = Opening(
        commitment_occurrence=COMMITMENT, query=query, answer=leaves[query], auth_path=path
    )
    if mutation is Mutation.FOREIGN_COMMITMENT:
        opening = replace(opening, commitment_occurrence="message:other")
    elif mutation is Mutation.QUERY_OUT_OF_RANGE:
        opening = replace(opening, query=construction.cardinality)
    elif mutation is Mutation.SHORT_AUTHENTICATION:
        opening = replace(opening, auth_path=path[:-1])
    elif mutation is Mutation.NODE_POSED_AS_LEAF:
        opening = replace(opening, leaf_tagged=False)
    return verify_opening(construction, core.profile, root, opening)


def mutate_core(core: CommitmentCore, mutation: Mutation) -> CommitmentCore:
    """Structural mutations, which the shape law rather than the opening judges."""

    if mutation is Mutation.OPENING_WITHOUT_CHECK:
        return replace(core, actions=tuple(a for a in core.actions if a.occurrence != CHECK))
    if mutation is Mutation.COMMITMENT_AS_CHECK_OPERAND:
        return replace(
            core,
            actions=tuple(
                replace(a, profile=None) if a.occurrence == COMMITMENT else a
                for a in core.actions
            ),
        )
    return core


__all__ = [
    "BINDING_ASSUMPTION",
    "CHECK",
    "COMMITMENT",
    "ActionKind",
    "CommitmentCore",
    "CoreAction",
    "Mutation",
    "OPENING",
    "QUERY",
    "ValueSort",
    "admit_core",
    "build_core",
    "honest_leaves",
    "mutate_core",
    "run_opening",
]
