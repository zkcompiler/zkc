"""The logarithmic-derivative lookup family, as a clean-room semantic model.

This witness exists because of what the other two cannot reach.  The FRI
witness ends at ``fri-terminal-not-modeled`` before any claim is produced, and
the Schnorr witness has a single implicit claim flow.  Logup is the first
family in the corpus whose whole content is a **claim graph**: an inclusion
claim instantiated from anchors, consumed once by a reduction at a sampled
point, producing an identity claim that leaves undischarged through a named
residual.

So the subjects under test here are the ones no scenario in the redesign has
ever exercised:

    claim production      an input claim carries the anchors it rests on
    claim linearity       a linear claim has exactly one consumer
    terminal closure      no live claim survives the end of the protocol
    role discipline       a role declares exactly one arity; two is refusal
    material identity     a claim's anchors match the material actually bound
    origin/seat agreement a profile's origin and the event carrying it agree

Reconstructed from the shipped family (chunk 3), not copied from it: the model
parses the two pinned fixtures for their facts and declares its own scenario,
whose correspondence to those facts is checked.  Nothing here imports the MLIR
dialect, the seal battery, the canonical encoder, or the conformance twin.

The two negative fixtures the shipped suite already authors are reproduced as
named mutations, together with their boundaries:

    logup-role-widened        -> "declares more than one arity"
    logup-unanchored-inclusion -> an admitted material-identity constraint
                                  does not hold

Four further mutations exercise laws the shipped fixtures do not isolate:
double consumption, an unrouted claim at the terminal, a challenge drawn
before the material it must bind, and a preprocessed profile carried by a
prover message.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import re
from pathlib import Path
from typing import Any, Mapping

from .terms import CheckResult, OutcomeClass, semantic_id


#: 2^61 - 1, the Mersenne prime the shipped fixtures sample the bus challenge
#: from.  The characteristic matters: the lemma's hypothesis fails outright in
#: characteristic two, and overflowing multiplicities are the known soundness
#: failure of the approach.
BUS_CHALLENGE_SPACE = 2305843009213693951

ROLES = ("table", "queries", "multiplicities")

#: Recovered from `registry/protocol-vocabulary.json`.  Arity is per profile,
#: not per family: `logup_queries` declares 10 where the others declare 8, so
#: different roles legitimately carry different arities.  Only two occupants of
#: the SAME role with disagreeing arities is a refusal.  The preprocessed table
#: also names a different binding route from the committed columns.
PROFILES: Mapping[str, Mapping[str, Any]] = {
    "logup_committed_column": {"arity_log2": 8, "origin": "prover_message", "route": "zkc.commit.toy-vector"},
    "logup_multiplicities": {"arity_log2": 8, "origin": "prover_message", "route": "zkc.commit.toy-vector"},
    "logup_queries": {"arity_log2": 10, "origin": "prover_message", "route": "zkc.commit.toy-vector"},
    "logup_table": {"arity_log2": 8, "origin": "preprocessed", "route": "zkc.anchor.preimage"},
}

MAX_ACTIONS = 64
MAX_CLAIMS = 32
MAX_ANCHOR_ROLES = 8

_ANCHOR = re.compile(r"sha256:[0-9a-f]{64}\Z")


class LogupError(ValueError):
    """A malformed logup scenario."""


class Origin(str, Enum):
    PROVER_MESSAGE = "prover_message"
    PREPROCESSED = "preprocessed"
    RELATION_DERIVED = "relation_derived"


class Seat(str, Enum):
    """The event that carries a committed value.

    A profile's origin and its seat are one fact with two spellings.  Keeping
    both variants is what makes the agreement testable in the direction that
    matters: a family with only one seat could not tell whether admission
    checks the agreement or merely the spelling it happens to see.
    """

    PROVER_SLOT = "slot"
    SEAL_BINDING = "bind"


_ORIGIN_SEAT = {
    Origin.PROVER_MESSAGE: Seat.PROVER_SLOT,
    Origin.PREPROCESSED: Seat.SEAL_BINDING,
}


class ClaimContract(str, Enum):
    INCLUSION = "logup_inclusion"
    IDENTITY = "logup_identity"


class Disposition(str, Enum):
    LINEAR = "Linear"


class ActionKind(str, Enum):
    COMMITMENT = "Commitment"
    CHALLENGE = "Challenge"
    REDUCTION = "Reduction"
    RESIDUAL = "Residual"


class Variant(str, Enum):
    BUS = "logup_bus"
    RANGE_CHECK = "logup_range_check"


class Mutation(str, Enum):
    BASE = "base"
    #: Reproduced from the shipped negative fixtures.
    ROLE_WIDENED = "role_widened"
    UNANCHORED_INCLUSION = "unanchored_inclusion"
    #: Laws the shipped fixtures do not isolate.
    CLAIM_CONSUMED_TWICE = "claim_consumed_twice"
    CLAIM_UNROUTED_AT_TERMINAL = "claim_unrouted_at_terminal"
    CHALLENGE_BEFORE_MATERIAL = "challenge_before_material"
    CHALLENGE_UNBOUND_MATERIAL = "challenge_unbound_material"
    CLAIM_ANCHORS_UNBOUND_ROLE = "claim_anchors_unbound_role"
    ORIGIN_SEAT_MISMATCH = "origin_seat_mismatch"
    MULTI_ROUND_CONTRACT = "multi_round_contract"
    REDUNDANT_TABLE_BINDING = "redundant_table_binding"
    AUTHORED_ANCHOR_DIVERGES = "authored_anchor_diverges"
    CLAIM_BOUND_EXCEEDED = "claim_bound_exceeded"
    REDUCTION_CONSUMES_UNDECLARED = "reduction_consumes_undeclared"


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome=outcome, boundary=boundary, code=code, detail=detail)


@dataclass(frozen=True)
class CommittedColumn:
    """One committed column: a role, a declared arity, an origin, and a seat."""

    role: str
    profile: str
    origin: Origin
    seat: Seat
    arity_log2: int
    anchor: str
    binding_route: str = "zkc.commit.toy-vector"
    occurrence_index: int = 0

    def __post_init__(self) -> None:
        if self.role not in ROLES:
            raise LogupError(f"unknown logup role: {self.role}")
        if not _ANCHOR.match(self.anchor):
            raise LogupError("a committed column names a sha256 anchor")
        if not isinstance(self.arity_log2, int) or not 0 < self.arity_log2 <= 32:
            raise LogupError("declared arity is outside the profile")

    def term(self) -> dict[str, Any]:
        return {
            "role": self.role,
            "profile": self.profile,
            "origin": self.origin.value,
            "seat": self.seat.value,
            "arity_log2": self.arity_log2,
            "anchor": self.anchor,
            "binding_route": self.binding_route,
            "index": self.occurrence_index,
        }


@dataclass(frozen=True)
class Claim:
    """A typed resource, produced once and consumed at most once."""

    name: str
    contract: ClaimContract
    anchors: Mapping[str, str]
    produced_by: str
    disposition: Disposition = Disposition.LINEAR

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "contract": self.contract.value,
            "anchors": dict(sorted(self.anchors.items())),
            "produced_by": self.produced_by,
            "disposition": self.disposition.value,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.p03.claim.v1", self.term())


@dataclass(frozen=True)
class Reduction:
    """Consumes claims at a sampled point and produces others."""

    name: str
    contract: str
    rounds: int
    consumes: tuple[str, ...]
    produces: tuple[str, ...]
    deps: tuple[str, ...]
    anchors: Mapping[str, str]

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "contract": self.contract,
            "rounds": self.rounds,
            "consumes": list(self.consumes),
            "produces": list(self.produces),
            "deps": list(self.deps),
            "anchors": dict(sorted(self.anchors.items())),
        }


@dataclass(frozen=True)
class Residual:
    """A claim that leaves undischarged, by a named route."""

    claim: str
    route: str

    def term(self) -> dict[str, Any]:
        return {"claim": self.claim, "route": self.route}


@dataclass(frozen=True)
class Challenge:
    label: str
    domain: str
    space: int
    binds: tuple[str, ...]

    def term(self) -> dict[str, Any]:
        return {
            "label": self.label,
            "domain": self.domain,
            "space": self.space,
            "binds": list(self.binds),
        }


@dataclass(frozen=True)
class LogupCore:
    variant: Variant
    columns: tuple[CommittedColumn, ...]
    challenge: Challenge
    claims: tuple[Claim, ...]
    reductions: tuple[Reduction, ...]
    residuals: tuple[Residual, ...]
    material_bindings: Mapping[str, str]
    #: The spine order, authored rather than derived.  Deriving it would make
    #: the ordering law unfalsifiable: a rule checking that every column
    #: precedes the challenge cannot fire if the schedule is built that way by
    #: construction.  The real protocol's order is the spine, so the model
    #: carries it as data a mutation can move.
    schedule: tuple[str, ...] = ()

    def canonical_schedule(self) -> tuple[str, ...]:
        order = [f"commitment:{c.role}:{c.occurrence_index}" for c in self.columns]
        order.append(f"challenge:{self.challenge.label}")
        order.extend(f"reduction:{r.name}" for r in self.reductions)
        order.extend(f"residual:{r.claim}" for r in self.residuals)
        return tuple(order)

    def term(self) -> dict[str, Any]:
        return {
            "variant": self.variant.value,
            "columns": [c.term() for c in self.columns],
            "challenge": self.challenge.term(),
            "claims": [c.term() for c in self.claims],
            "reductions": [r.term() for r in self.reductions],
            "residuals": [r.term() for r in self.residuals],
            "material_bindings": dict(sorted(self.material_bindings.items())),
            "schedule": list(self.schedule),
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.p03.logup-core.v1", self.term())


# --- fixture facts -----------------------------------------------------------

TABLE_ANCHOR = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"
QUERIES_ANCHOR = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528"
MULT_ANCHOR = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60"

ANCHORS = {
    "table": TABLE_ANCHOR,
    "queries": QUERIES_ANCHOR,
    "multiplicities": MULT_ANCHOR,
}


@dataclass(frozen=True)
class FrozenFixture:
    name: str
    path: str
    sha256: str
    roles: tuple[str, ...]
    challenge_space: int

    def term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "path": self.path,
            "sha256": self.sha256,
            "roles": list(self.roles),
            "challenge_space": self.challenge_space,
        }


def load_fixture(repo_root: Path, name: str, expected_sha256: str) -> FrozenFixture:
    """Read one pinned fixture and recover the facts the model needs.

    The fixture is read for facts, not imported for behaviour: the roles and
    the challenge space are recovered by reading the authored text, and the
    scenario the model builds is declared independently and then checked
    against them.
    """

    import json

    cases = json.loads((Path(__file__).resolve().parents[1] / "cases" / "fixtures.json").read_text())
    if name not in cases:
        raise LogupError(f"unknown fixture: {name}")
    rel = cases[name]["path"]
    path = repo_root / rel
    if path.stat().st_size > 1 << 20:
        raise LogupError("frozen fixture exceeds the one-megabyte bound")
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected_sha256 or digest != cases[name]["sha256"]:
        raise LogupError(f"frozen fixture hash mismatch: {rel}")
    text = raw.decode("utf-8")
    roles = tuple(sorted(set(re.findall(r'as "(table|queries|multiplicities)"', text))))
    spaces = set(re.findall(r'space "(\d+)"', text))
    if len(spaces) != 1:
        raise LogupError("fixture does not declare exactly one challenge space")
    return FrozenFixture(name, rel, digest, roles, int(spaces.pop()))


# --- scenario construction ---------------------------------------------------


def build_core(variant: Variant) -> LogupCore:
    """Declare the scenario independently of the fixture."""

    if variant is Variant.BUS:
        named = dict.fromkeys(ROLES, "logup_committed_column")
    else:
        named = {
            "table": "logup_table",
            "queries": "logup_queries",
            "multiplicities": "logup_multiplicities",
        }

    columns = tuple(
        CommittedColumn(
            role=role,
            profile=named[role],
            origin=Origin(PROFILES[named[role]]["origin"]),
            seat=(
                Seat.SEAL_BINDING
                if PROFILES[named[role]]["origin"] == "preprocessed"
                else Seat.PROVER_SLOT
            ),
            arity_log2=int(PROFILES[named[role]]["arity_log2"]),
            anchor=ANCHORS[role],
            binding_route=str(PROFILES[named[role]]["route"]),
        )
        for role in ROLES
    )
    challenge = Challenge(
        label="beta",
        domain="logup.beta",
        space=BUS_CHALLENGE_SPACE,
        binds=tuple(f"commitment:{c.role}:{c.occurrence_index}" for c in columns),
    )
    inclusion = Claim("inclusion", ClaimContract.INCLUSION, dict(ANCHORS), "instantiate")
    identity = Claim("identity", ClaimContract.IDENTITY, dict(ANCHORS), "reduction:bus")
    reduction = Reduction(
        name="bus",
        contract=variant.value,
        rounds=1,
        consumes=("inclusion",),
        produces=("identity",),
        deps=("beta",),
        anchors=dict(ANCHORS),
    )
    # A seal-stage binding absorbs its digest, so it carries its own reference
    # and a material binding on it would be that fact spelled twice.
    bindings = {
        c.role: c.anchor for c in columns if c.seat is Seat.PROVER_SLOT
    }
    core = LogupCore(
        variant=variant,
        columns=columns,
        challenge=challenge,
        claims=(inclusion, identity),
        reductions=(reduction,),
        residuals=(Residual("identity", "logup-identity-discharge-not-modeled"),),
        material_bindings=bindings,
    )
    return replace(core, schedule=core.canonical_schedule())


# --- admission ---------------------------------------------------------------


def admit_core(core: Any) -> CheckResult:
    """The laws this family is the first to exercise."""

    if not isinstance(core, LogupCore):
        return _result(OutcomeClass.MALFORMED, "closed-core", "P03-000", "not a logup core")
    if len(core.schedule) > MAX_ACTIONS or len(core.claims) > MAX_CLAIMS:
        return _result(OutcomeClass.MALFORMED, "closed-core", "P03-001", "core exceeds its declared bound")

    # -- role discipline: one role, one arity.  Two is refusal, not a choice.
    by_role: dict[str, list[CommittedColumn]] = {}
    for column in core.columns:
        by_role.setdefault(column.role, []).append(column)
    if set(by_role) != set(ROLES):
        return _result(OutcomeClass.MISMATCH, "logup:roles", "P03-002", "the family fills exactly three roles")
    for role, occupants in by_role.items():
        arities = {occupant.arity_log2 for occupant in occupants}
        if len(arities) > 1:
            return _result(
                OutcomeClass.REFUSED,
                "apply.parameters.lookups",
                "P03-003",
                f"role {role} declares more than one arity",
            )

    # -- origin and seat are one fact with two spellings.
    for column in core.columns:
        expected = _ORIGIN_SEAT.get(column.origin)
        if expected is not None and column.seat is not expected:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:origin-seat",
                "P03-004",
                f"role {column.role} declares origin {column.origin.value} on a {column.seat.value} seat",
            )

    # -- the challenge binds every committed column that precedes it.  A column
    #    sampled after the challenge is the weak Fiat-Shamir shape.
    if set(core.schedule) != set(core.canonical_schedule()):
        return _result(OutcomeClass.MALFORMED, "closed-core", "P03-015", "the schedule does not cover exactly the declared occurrences")
    if len(set(core.schedule)) != len(core.schedule):
        return _result(OutcomeClass.MALFORMED, "closed-core", "P03-016", "an occurrence is scheduled twice")
    positions = {occurrence: index for index, occurrence in enumerate(core.schedule)}
    challenge_at = positions[f"challenge:{core.challenge.label}"]
    for column in core.columns:
        occurrence = f"commitment:{column.role}:{column.occurrence_index}"
        if positions[occurrence] > challenge_at:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:transcript-prefix",
                "P03-005",
                f"{column.role} is committed after the challenge that must bind it",
            )
        if occurrence not in core.challenge.binds:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:transcript-prefix",
                "P03-006",
                f"the challenge does not bind {column.role}",
            )

    # -- material identity: a claim's anchors match the material actually bound.
    bound = dict(core.material_bindings)
    for column in core.columns:
        if column.seat is Seat.SEAL_BINDING:
            bound.setdefault(column.role, column.anchor)
    for claim in core.claims:
        for role, anchor in claim.anchors.items():
            if role not in bound:
                return _result(
                    OutcomeClass.MISMATCH,
                    "logup:material-identity",
                    "P03-007",
                    f"claim {claim.name} anchors {role} to material nothing binds",
                )
            if bound[role] != anchor:
                return _result(
                    OutcomeClass.MISMATCH,
                    "logup:material-identity",
                    "P03-008",
                    "an admitted material-identity constraint does not hold",
                )

    # -- the contract declares exactly one round.  The shipped rule asserts
    #    this as a machine condition; a family that widened it would price a
    #    round structure no rule states.
    for reduction in core.reductions:
        if reduction.rounds != 1:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:round-structure",
                "P03-017",
                f"contract {reduction.contract} declares {reduction.rounds} rounds",
            )

    # -- a seal-stage binding is its own material reference, so a separate
    #    material binding on it is that fact spelled twice and is refused as
    #    unconsumed rather than accepted as harmless redundancy.
    for column in core.columns:
        if column.seat is Seat.SEAL_BINDING and column.role in core.material_bindings:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:material-identity",
                "P03-018",
                f"{column.role} is seal-bound and carries a redundant material binding",
            )

    # -- the produced claim's anchors are DERIVED from the material filling each
    #    role, not authored freely.  An authored anchor that diverges from the
    #    derived one is refused rather than preferred.
    derived = {c.role: c.anchor for c in core.columns}
    for reduction in core.reductions:
        for role, anchor in reduction.anchors.items():
            if role in derived and derived[role] != anchor:
                return _result(
                    OutcomeClass.MISMATCH,
                    "logup:derived-anchors",
                    "P03-019",
                    f"the authored anchor for {role} diverges from the material it names",
                )

    # -- claim linearity: exactly one consumer for every linear claim.
    names = {claim.name for claim in core.claims}
    if len(names) != len(core.claims):
        return _result(OutcomeClass.MALFORMED, "logup:claims", "P03-009", "claim name is duplicated")
    consumed: dict[str, int] = {name: 0 for name in names}
    for reduction in core.reductions:
        for name in reduction.consumes:
            if name not in names:
                return _result(OutcomeClass.MISMATCH, "logup:claims", "P03-010", "a reduction consumes an undeclared claim")
            consumed[name] += 1
        for name in reduction.produces:
            if name not in names:
                return _result(OutcomeClass.MISMATCH, "logup:claims", "P03-011", "a reduction produces an undeclared claim")
    for name, count in consumed.items():
        if count > 1:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:claim-linearity",
                "P03-012",
                f"linear claim {name} reaches more than one consumer",
            )

    # -- terminal closure: no live claim survives the end of the protocol.
    routed = {residual.claim for residual in core.residuals}
    for claim in core.claims:
        if consumed[claim.name] == 0 and claim.name not in routed:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:terminal-closure",
                "P03-013",
                f"claim {claim.name} is live at the terminal and no route carries it",
            )
        if consumed[claim.name] and claim.name in routed:
            return _result(
                OutcomeClass.MISMATCH,
                "logup:terminal-closure",
                "P03-014",
                f"claim {claim.name} is both consumed and routed out",
            )

    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary="closed-core",
        code="P03-100",
        detail=(
            "the logup core admits: roles single-valued, origins seated, the "
            "challenge bound to its material, claims linear, and the identity "
            "claim routed to its declared residual rather than discharged"
        ),
        subject=core.identity,
        evidence={
            "residual": core.residuals[0].route,
            "required_assumption": "LogupIdentityDischargeNotModeled",
        },
    )


def correspondence(core: LogupCore, fixture: FrozenFixture) -> CheckResult:
    """Check the independently declared scenario against the pinned fixture."""

    if tuple(sorted(c.role for c in core.columns)) != fixture.roles:
        return _result(OutcomeClass.MISMATCH, "logup:correspondence", "P03-020", "declared roles differ from the fixture")
    if core.challenge.space != fixture.challenge_space:
        return _result(OutcomeClass.MISMATCH, "logup:correspondence", "P03-021", "declared challenge space differs from the fixture")
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary="logup:correspondence",
        code="P03-120",
        detail="the declared scenario corresponds to the pinned fixture on roles and challenge space",
        subject=core.identity,
        evidence={"fixture": fixture.sha256},
    )


def mutate(core: LogupCore, mutation: Mutation) -> LogupCore:
    if mutation is Mutation.BASE:
        return core
    if mutation is Mutation.ROLE_WIDENED:
        widened = CommittedColumn(
            role="queries", profile="logup_queries", origin=Origin.PROVER_MESSAGE,
            seat=Seat.PROVER_SLOT, arity_log2=core.columns[0].arity_log2 + 1,
            anchor=QUERIES_ANCHOR, occurrence_index=1,
        )
        columns = core.columns + (widened,)
        binds = core.challenge.binds + ("commitment:queries:1",)
        widened_core = replace(core, columns=columns, challenge=replace(core.challenge, binds=binds))
        return replace(widened_core, schedule=widened_core.canonical_schedule())
    if mutation is Mutation.UNANCHORED_INCLUSION:
        loose = {role: f"sha256:{'00ff':<4}{index:060x}" for index, role in enumerate(ROLES)}
        claims = tuple(
            replace(claim, anchors=loose) if claim.name == "inclusion" else claim
            for claim in core.claims
        )
        return replace(core, claims=claims)
    if mutation is Mutation.CLAIM_CONSUMED_TWICE:
        second = Reduction(
            name="bus_again", contract=core.variant.value, rounds=1,
            consumes=("inclusion",), produces=(), deps=("beta",),
            anchors=dict(ANCHORS),
        )
        doubled = replace(core, reductions=core.reductions + (second,))
        return replace(doubled, schedule=doubled.canonical_schedule())
    if mutation is Mutation.CLAIM_UNROUTED_AT_TERMINAL:
        unrouted = replace(core, residuals=())
        return replace(unrouted, schedule=unrouted.canonical_schedule())
    if mutation is Mutation.CHALLENGE_BEFORE_MATERIAL:
        # The weak Fiat-Shamir shape: the table is committed *after* the
        # challenge that must bind it.  This moves the occurrence in the spine
        # rather than merely dropping it from the binds list, so the ordering
        # law is what refuses it.
        table = "commitment:table:0"
        beta = f"challenge:{core.challenge.label}"
        order = [o for o in core.schedule if o != table]
        order.insert(order.index(beta) + 1, table)
        return replace(core, schedule=tuple(order))
    if mutation is Mutation.CHALLENGE_UNBOUND_MATERIAL:
        return replace(core, challenge=replace(core.challenge, binds=tuple(
            b for b in core.challenge.binds if not b.endswith(":table:0")
        )))
    if mutation is Mutation.CLAIM_ANCHORS_UNBOUND_ROLE:
        widened = dict(ANCHORS)
        widened["helper"] = TABLE_ANCHOR
        claims = tuple(
            replace(claim, anchors=widened) if claim.name == "inclusion" else claim
            for claim in core.claims
        )
        return replace(core, claims=claims)
    if mutation is Mutation.CLAIM_BOUND_EXCEEDED:
        filler = tuple(
            replace(core.claims[0], name=f"filler{index}")
            for index in range(MAX_CLAIMS + 1)
        )
        return replace(core, claims=core.claims + filler)
    if mutation is Mutation.REDUCTION_CONSUMES_UNDECLARED:
        ghosted = replace(core.reductions[0], consumes=("inclusion", "ghost"))
        return replace(core, reductions=(ghosted,) + core.reductions[1:])
    if mutation is Mutation.MULTI_ROUND_CONTRACT:
        return replace(core, reductions=tuple(
            replace(r, rounds=2) for r in core.reductions
        ))
    if mutation is Mutation.REDUNDANT_TABLE_BINDING:
        bindings = dict(core.material_bindings)
        bindings["table"] = ANCHORS["table"]
        return replace(core, material_bindings=bindings)
    if mutation is Mutation.AUTHORED_ANCHOR_DIVERGES:
        skewed = dict(ANCHORS)
        skewed["queries"] = MULT_ANCHOR
        return replace(core, reductions=tuple(
            replace(r, anchors=skewed) for r in core.reductions
        ))
    if mutation is Mutation.ORIGIN_SEAT_MISMATCH:
        columns = tuple(
            replace(column, origin=Origin.PREPROCESSED)
            if column.role == "queries" else column
            for column in core.columns
        )
        return replace(core, columns=columns)
    raise LogupError(f"unhandled mutation: {mutation}")


__all__ = [
    "ANCHORS",
    "BUS_CHALLENGE_SPACE",
    "ROLES",
    "Claim",
    "ClaimContract",
    "CommittedColumn",
    "Disposition",
    "FrozenFixture",
    "LogupCore",
    "LogupError",
    "Mutation",
    "Origin",
    "Reduction",
    "Residual",
    "Seat",
    "Variant",
    "admit_core",
    "build_core",
    "correspondence",
    "load_fixture",
    "mutate",
]
