"""Compact structural path analysis for the F0-V2B2C1B5A terminal slice.

This is temporary research code.  It gives exact meaning to one deliberately
small fragment of InteractiveCore claim flow: guards are either ``Always`` or
one opaque, structurally identified Boolean atom; reductions are scheduled;
and execution stops at the first active terminal.  The analyzer never
enumerates Boolean assignments.  It does not define required-check truth or
the phrase "required reduction" from the target prose.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any


MAX_ITEMS = 1 << 14


class PathFailure(ValueError):
    """Stable fail-closed result from the bounded path analyzer."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


class ClaimUsage(Enum):
    LINEAR = "Linear"
    REUSABLE = "Reusable"


class TerminalVerdict(Enum):
    ACCEPT = "Accept"
    REJECT = "Reject"
    ABORT = "Abort"


class ClaimDisposition(Enum):
    CONSUME = "Consume"
    DISCHARGE = "Discharge"


@dataclass(frozen=True)
class InitialSource:
    pass


@dataclass(frozen=True)
class ReductionOutputSource:
    reduction: int
    output_ordinal: int


@dataclass(frozen=True)
class ClaimDecl:
    usage: ClaimUsage
    source: InitialSource | ReductionOutputSource


@dataclass(frozen=True)
class ReductionDecl:
    inputs: tuple[int, ...]
    outputs: tuple[int, ...]


@dataclass(frozen=True)
class CheckDecl:
    label: str


@dataclass(frozen=True)
class DispositionEntry:
    claim: int
    disposition: ClaimDisposition


@dataclass(frozen=True)
class TerminalDecl:
    verdict: TerminalVerdict
    public_outputs: tuple[str, ...]
    required_true_checks: tuple[int, ...]
    dispositions: tuple[DispositionEntry, ...]


@dataclass(frozen=True)
class CheckEffect:
    check: int


@dataclass(frozen=True)
class ReductionEffect:
    reduction: int


@dataclass(frozen=True)
class TerminalEffect:
    terminal: int


@dataclass(frozen=True)
class Occurrence:
    guard: str | None
    effect: CheckEffect | ReductionEffect | TerminalEffect


@dataclass(frozen=True)
class Program:
    claims: tuple[ClaimDecl, ...]
    reductions: tuple[ReductionDecl, ...]
    checks: tuple[CheckDecl, ...]
    terminals: tuple[TerminalDecl, ...]
    occurrences: tuple[Occurrence, ...]


@dataclass(frozen=True)
class Cube:
    """A conjunction of positive and negative opaque guard atoms."""

    positive: frozenset[str] = frozenset()
    negative: frozenset[str] = frozenset()
    impossible: bool = False

    def normalized(self) -> Cube:
        return Cube(
            self.positive,
            self.negative,
            self.impossible or bool(self.positive & self.negative),
        )

    def require_true(self, atom: str | None) -> Cube:
        if self.impossible:
            return self
        if atom is None:
            return self
        return Cube(self.positive | {atom}, self.negative).normalized()

    def require_false(self, atom: str | None) -> Cube:
        if self.impossible or atom is None:
            return Cube(impossible=True)
        return Cube(self.positive, self.negative | {atom}).normalized()

    def value(self) -> dict[str, Any]:
        return {
            "positive": sorted(self.positive),
            "negative": sorted(self.negative),
            "impossible": self.impossible,
        }


class ClaimState(Enum):
    LIVE = "Live"
    DEAD = "Dead"
    UNKNOWN = "Unknown"


@dataclass(frozen=True)
class Analysis:
    outcome: str
    code: str
    active_regions: tuple[Cube, ...]
    terminal_live_claims: tuple[tuple[int, ...], ...]
    unresolved_check_truth: tuple[tuple[int, int], ...]
    operations: int

    def value(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome,
            "code": self.code,
            "active_regions": [item.value() for item in self.active_regions],
            "terminal_live_claims": [
                list(items) for items in self.terminal_live_claims
            ],
            "unresolved_check_truth": [
                list(item) for item in self.unresolved_check_truth
            ],
            "operations": self.operations,
        }


def _fail(code: str, detail: str, outcome: str = "Refused") -> None:
    raise PathFailure(outcome, code, detail)


def _strict_dict(value: object, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        _fail("F0V2B2C1B5A-M-SHAPE", f"{label} has another exact shape", "Malformed")
    return value


def _seq(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not list or len(value) > MAX_ITEMS:
        _fail(
            "F0V2B2C1B5A-M-SEQUENCE",
            f"{label} is not one bounded sequence",
            "Malformed",
        )
    return tuple(value)


def _ref(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        _fail(
            "F0V2B2C1B5A-M-REFERENCE",
            f"{label} is not one natural reference",
            "Malformed",
        )
    return value


def _guard(value: object) -> str | None:
    if value is None:
        return None
    if type(value) is not str or not value or len(value) > 128:
        _fail(
            "F0V2B2C1B5A-M-GUARD",
            "guard is not Always or one bounded atom",
            "Malformed",
        )
    return value


def _symbol(value: object, label: str) -> str:
    if type(value) is not str or not value or len(value) > 128:
        _fail("F0V2B2C1B5A-M-SYMBOL", f"{label} is not one bounded symbol", "Malformed")
    return value


def _parse(program: object) -> Program:
    root = _strict_dict(
        program,
        {"claims", "reductions", "checks", "terminals", "occurrences"},
        "program",
    )
    claims: list[ClaimDecl] = []
    for item in _seq(root["claims"], "claims"):
        row = _strict_dict(item, {"usage", "source"}, "claim")
        try:
            usage = ClaimUsage(row["usage"])
        except (TypeError, ValueError):
            _fail(
                "F0V2B2C1B5A-M-CLAIM-USAGE",
                "claim usage is outside the closed sum",
                "Malformed",
            )
        source = _strict_dict(
            row["source"], {"kind", "reduction", "output"}, "claim source"
        )
        if source["kind"] == "Initial":
            if source["reduction"] is not None or source["output"] is not None:
                _fail(
                    "F0V2B2C1B5A-M-CLAIM-SOURCE",
                    "Initial source carries reduction fields",
                    "Malformed",
                )
            parsed_source: InitialSource | ReductionOutputSource = InitialSource()
        elif source["kind"] == "ReductionOutput":
            parsed_source = ReductionOutputSource(
                _ref(source["reduction"], "source reduction"),
                _ref(source["output"], "source output"),
            )
        else:
            _fail(
                "F0V2B2C1B5A-M-CLAIM-SOURCE",
                "claim source is outside the closed sum",
                "Malformed",
            )
        claims.append(ClaimDecl(usage, parsed_source))

    reductions: list[ReductionDecl] = []
    for item in _seq(root["reductions"], "reductions"):
        row = _strict_dict(item, {"inputs", "outputs"}, "reduction")
        reductions.append(
            ReductionDecl(
                tuple(
                    _ref(value, "reduction input")
                    for value in _seq(row["inputs"], "reduction inputs")
                ),
                tuple(
                    _ref(value, "reduction output")
                    for value in _seq(row["outputs"], "reduction outputs")
                ),
            )
        )

    checks: list[CheckDecl] = []
    for item in _seq(root["checks"], "checks"):
        row = _strict_dict(item, {"label"}, "check")
        checks.append(CheckDecl(_symbol(row["label"], "check label")))

    terminals: list[TerminalDecl] = []
    for item in _seq(root["terminals"], "terminals"):
        row = _strict_dict(
            item,
            {"verdict", "public_outputs", "required_true_checks", "dispositions"},
            "terminal",
        )
        try:
            verdict = TerminalVerdict(row["verdict"])
        except (TypeError, ValueError):
            _fail(
                "F0V2B2C1B5A-M-VERDICT",
                "terminal verdict is outside the closed sum",
                "Malformed",
            )
        entries: list[DispositionEntry] = []
        for value in _seq(row["dispositions"], "terminal dispositions"):
            pair = _seq(value, "claim disposition")
            if len(pair) != 2:
                _fail(
                    "F0V2B2C1B5A-M-DISPOSITION",
                    "claim disposition is not a pair",
                    "Malformed",
                )
            try:
                disposition = ClaimDisposition(pair[1])
            except (TypeError, ValueError):
                _fail(
                    "F0V2B2C1B5A-M-DISPOSITION",
                    "claim disposition is outside the closed sum",
                    "Malformed",
                )
            entries.append(
                DispositionEntry(_ref(pair[0], "disposed claim"), disposition)
            )
        terminals.append(
            TerminalDecl(
                verdict,
                tuple(
                    _symbol(value, "public output")
                    for value in _seq(row["public_outputs"], "public outputs")
                ),
                tuple(
                    _ref(value, "required check")
                    for value in _seq(row["required_true_checks"], "required checks")
                ),
                tuple(entries),
            )
        )

    occurrences: list[Occurrence] = []
    for item in _seq(root["occurrences"], "occurrences"):
        row = _strict_dict(item, {"guard", "effect"}, "occurrence")
        effect = _strict_dict(row["effect"], {"kind", "ref"}, "effect")
        reference = _ref(effect["ref"], "effect reference")
        if effect["kind"] == "Check":
            parsed_effect: CheckEffect | ReductionEffect | TerminalEffect = CheckEffect(
                reference
            )
        elif effect["kind"] == "Reduction":
            parsed_effect = ReductionEffect(reference)
        elif effect["kind"] == "Terminal":
            parsed_effect = TerminalEffect(reference)
        else:
            _fail(
                "F0V2B2C1B5A-U-EFFECT",
                "effect is outside the bounded terminal fragment",
                "Unsupported",
            )
        occurrences.append(Occurrence(_guard(row["guard"]), parsed_effect))

    if not terminals or not occurrences:
        _fail(
            "F0V2B2C1B5A-R-NONEMPTY", "terminal and occurrence tables must be nonempty"
        )
    return Program(
        tuple(claims),
        tuple(reductions),
        tuple(checks),
        tuple(terminals),
        tuple(occurrences),
    )


def cube_implies(left: Cube, right: Cube) -> bool:
    """Return exact implication for two conjunctions of independent literals."""

    left = left.normalized()
    right = right.normalized()
    if left.impossible:
        return True
    if right.impossible:
        return False
    return right.positive <= left.positive and right.negative <= left.negative


def cubes_disjoint(left: Cube, right: Cube) -> bool:
    """Return exact disjointness for two conjunctions of independent literals."""

    left = left.normalized()
    right = right.normalized()
    return (
        left.impossible
        or right.impossible
        or bool(left.positive & right.negative)
        or bool(right.positive & left.negative)
    )


def _positions(
    program: Program,
) -> tuple[dict[int, int], dict[int, int], dict[int, int]]:
    check_positions = {index: [] for index in range(len(program.checks))}
    reduction_positions = {index: [] for index in range(len(program.reductions))}
    terminal_positions = {index: [] for index in range(len(program.terminals))}
    for position, occurrence in enumerate(program.occurrences):
        effect = occurrence.effect
        if type(effect) is CheckEffect:
            table = check_positions
            reference = effect.check
        elif type(effect) is ReductionEffect:
            table = reduction_positions
            reference = effect.reduction
        else:
            assert type(effect) is TerminalEffect
            table = terminal_positions
            reference = effect.terminal
        if reference not in table:
            _fail("F0V2B2C1B5A-R-EFFECT-REFERENCE", "effect reference is absent")
        table[reference].append(position)
    for table, label in (
        (check_positions, "Check"),
        (reduction_positions, "Reduction"),
        (terminal_positions, "Terminal"),
    ):
        if any(len(values) != 1 for values in table.values()):
            _fail("F0V2B2C1B5A-R-BACKLINK", f"{label} backlink is not one-to-one")
    return (
        {key: values[0] for key, values in check_positions.items()},
        {key: values[0] for key, values in reduction_positions.items()},
        {key: values[0] for key, values in terminal_positions.items()},
    )


def _active_regions(program: Program) -> tuple[Cube, ...]:
    live = Cube()
    regions: list[Cube] = []
    for occurrence in program.occurrences:
        active = live.require_true(occurrence.guard)
        regions.append(active)
        if type(occurrence.effect) is TerminalEffect:
            live = live.require_false(occurrence.guard)
    return tuple(regions)


def _claim_state(
    program: Program,
    claim_ref: int,
    region: Cube,
    before_position: int,
    reduction_positions: dict[int, int],
    regions: tuple[Cube, ...],
) -> ClaimState:
    claim = program.claims[claim_ref]
    if type(claim.source) is InitialSource:
        source_position = -1
        source_region = Cube()
    else:
        source_position = reduction_positions[claim.source.reduction]
        source_region = regions[source_position]
    if source_position >= before_position or cubes_disjoint(region, source_region):
        return ClaimState.DEAD
    if not cube_implies(region, source_region):
        return ClaimState.UNKNOWN
    if claim.usage is ClaimUsage.REUSABLE:
        return ClaimState.LIVE
    for reduction_ref, reduction in enumerate(program.reductions):
        position = reduction_positions[reduction_ref]
        if position >= before_position or claim_ref not in reduction.inputs:
            continue
        consumer_region = regions[position]
        if cube_implies(region, consumer_region):
            return ClaimState.DEAD
        if not cubes_disjoint(region, consumer_region):
            return ClaimState.UNKNOWN
    return ClaimState.LIVE


def analyze(program_value: object) -> Analysis:
    """Analyze one bounded program without enumerating guard assignments."""

    program = _parse(program_value)
    operations = len(program.occurrences)
    check_positions, reduction_positions, terminal_positions = _positions(program)
    final = program.occurrences[-1]
    if final.guard is not None or type(final.effect) is not TerminalEffect:
        _fail(
            "F0V2B2C1B5A-R-FINAL-FALLBACK",
            "final occurrence is not an unconditional terminal",
        )

    output_coordinates: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(program.claims):
        if type(claim.source) is not ReductionOutputSource:
            continue
        coordinate = (claim.source.reduction, claim.source.output_ordinal)
        if claim.source.reduction >= len(program.reductions):
            _fail(
                "F0V2B2C1B5A-R-CLAIM-SOURCE", "claim names an absent source reduction"
            )
        reduction = program.reductions[claim.source.reduction]
        if (
            claim.source.output_ordinal >= len(reduction.outputs)
            or reduction.outputs[claim.source.output_ordinal] != claim_ref
        ):
            _fail(
                "F0V2B2C1B5A-R-CLAIM-SOURCE",
                "claim source and reduction output coordinate disagree",
            )
        if coordinate in output_coordinates:
            _fail(
                "F0V2B2C1B5A-R-CLAIM-SSA",
                "two claims share one reduction output coordinate",
            )
        output_coordinates[coordinate] = claim_ref
    expected_outputs = {
        (reduction_ref, ordinal): claim_ref
        for reduction_ref, reduction in enumerate(program.reductions)
        for ordinal, claim_ref in enumerate(reduction.outputs)
    }
    if output_coordinates != expected_outputs:
        _fail(
            "F0V2B2C1B5A-R-CLAIM-OUTPUT-CLOSURE",
            "reduction outputs and claim sources are not one exact bijection",
        )

    for reduction in program.reductions:
        if not reduction.inputs or len(set(reduction.inputs)) != len(reduction.inputs):
            _fail(
                "F0V2B2C1B5A-R-REDUCTION-INPUTS",
                "reduction inputs are empty or repeated",
            )
        if len(set(reduction.outputs)) != len(reduction.outputs):
            _fail("F0V2B2C1B5A-R-REDUCTION-OUTPUTS", "reduction outputs repeat")
        if any(
            reference >= len(program.claims)
            for reference in (*reduction.inputs, *reduction.outputs)
        ):
            _fail("F0V2B2C1B5A-R-CLAIM-REFERENCE", "reduction names an absent claim")

    regions = _active_regions(program)
    operations += len(regions)

    for claim_ref, claim in enumerate(program.claims):
        if claim.usage is not ClaimUsage.LINEAR:
            continue
        consumers = [
            regions[reduction_positions[reduction_ref]]
            for reduction_ref, reduction in enumerate(program.reductions)
            if claim_ref in reduction.inputs
        ]
        for left_index, left in enumerate(consumers):
            for right in consumers[left_index + 1 :]:
                operations += 1
                if not cubes_disjoint(left, right):
                    _fail(
                        "F0V2B2C1B5A-R-LINEAR-PATH-OVERLAP",
                        "two linear-claim consumers can occur on one path",
                    )

    for reduction_ref, reduction in enumerate(program.reductions):
        position = reduction_positions[reduction_ref]
        region = regions[position]
        if region.impossible:
            continue
        for claim_ref in reduction.inputs:
            operations += 1
            state = _claim_state(
                program, claim_ref, region, position, reduction_positions, regions
            )
            if state is not ClaimState.LIVE:
                _fail(
                    "F0V2B2C1B5A-R-REDUCTION-LIVENESS",
                    f"reduction {reduction_ref} input {claim_ref} is {state.value}",
                )

    terminal_live_claims: list[tuple[int, ...]] = [() for _ in program.terminals]
    unresolved_checks: list[tuple[int, int]] = []
    for terminal_ref, terminal in enumerate(program.terminals):
        position = terminal_positions[terminal_ref]
        region = regions[position]
        disposition_refs = tuple(entry.claim for entry in terminal.dispositions)
        if any(reference >= len(program.claims) for reference in disposition_refs):
            _fail(
                "F0V2B2C1B5A-R-DISPOSITION-REFERENCE", "terminal names an absent claim"
            )
        if len(set(disposition_refs)) != len(disposition_refs):
            _fail(
                "F0V2B2C1B5A-R-DISPOSITION-UNIQUE",
                "terminal repeats one claim disposition",
            )
        for check_ref in terminal.required_true_checks:
            if check_ref >= len(program.checks):
                _fail(
                    "F0V2B2C1B5A-R-CHECK-REFERENCE",
                    "terminal names an absent required Check",
                )
            check_position = check_positions[check_ref]
            if check_position >= position or not cube_implies(
                region, regions[check_position]
            ):
                _fail(
                    "F0V2B2C1B5A-R-CHECK-OCCURRENCE",
                    "terminal activity does not guarantee the required Check occurred",
                )
            if not region.impossible:
                unresolved_checks.append((terminal_ref, check_ref))
        if region.impossible:
            continue
        live: list[int] = []
        for claim_ref in range(len(program.claims)):
            operations += 1
            state = _claim_state(
                program, claim_ref, region, position, reduction_positions, regions
            )
            if state is ClaimState.UNKNOWN:
                _fail(
                    "F0V2B2C1B5A-R-PATH-AMBIGUITY",
                    f"terminal {terminal_ref} cannot decide claim {claim_ref} liveness in the closed guard fragment",
                )
            if state is ClaimState.LIVE:
                live.append(claim_ref)
        terminal_live_claims[terminal_ref] = tuple(live)
        if tuple(sorted(disposition_refs)) != tuple(live):
            _fail(
                "F0V2B2C1B5A-R-TERMINAL-CLOSURE",
                f"terminal {terminal_ref} dispositions do not equal its path-live claims",
            )

    if unresolved_checks:
        return Analysis(
            "CannotAnswer",
            "F0V2B2C1B5A-C-REQUIRED-CHECK-TRUTH",
            regions,
            tuple(terminal_live_claims),
            tuple(unresolved_checks),
            operations,
        )
    return Analysis(
        "Affirmative",
        "F0V2B2C1B5A-A-COMPACT-PATH-ANALYSIS",
        regions,
        tuple(terminal_live_claims),
        (),
        operations,
    )
