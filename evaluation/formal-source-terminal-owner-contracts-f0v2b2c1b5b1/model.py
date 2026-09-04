"""Candidate Terminal owner contracts for F0-V2B2C1B5B1.

This disposable research model extends the B5A first-active path fragment with
three candidate owner rules:

* a Terminal Guard must structurally entail each required Check result;
* a Terminal names every Reduction whose application it requires; and
* terminal Claim disposition is derived from the verdict instead of carried
  as an otherwise unconstrained identity-bearing tag.

The Boolean analysis is a sound, deliberately incomplete must-literal
abstraction over the Foundation structural fragment Literal, Variable, Let,
and Conditional. PrimitiveCall is opaque; other Foundation constructors are
outside this bounded carrier. Failure to derive a fact refuses the Core; it is
not evidence that the mathematical implication is false.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
import json
from typing import Any


MAX_ITEMS = 1 << 14
MAX_TERM_NODES = 4096
MAX_TERM_DEPTH = 48


class ContractFailure(ValueError):
    """Stable fail-closed result from the bounded candidate analyzer."""

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


class DerivedClaimDisposition(Enum):
    CONSUME = "Consume"
    DISCHARGE = "Discharge"


@dataclass(frozen=True, order=True)
class InputLiteral:
    input_ordinal: int
    positive: bool

    def value(self) -> list[object]:
        return [self.input_ordinal, self.positive]


@dataclass(frozen=True)
class OutcomeFacts:
    possible: bool
    literals: frozenset[InputLiteral] = frozenset()

    def value(self) -> dict[str, object]:
        return {
            "possible": self.possible,
            "literals": [item.value() for item in sorted(self.literals)],
        }


@dataclass(frozen=True)
class BooleanFacts:
    when_true: OutcomeFacts
    when_false: OutcomeFacts

    @staticmethod
    def unknown() -> BooleanFacts:
        return BooleanFacts(OutcomeFacts(True), OutcomeFacts(True))

    @staticmethod
    def literal(value: bool) -> BooleanFacts:
        return BooleanFacts(
            OutcomeFacts(value),
            OutcomeFacts(not value),
        )

    @staticmethod
    def variable(input_ordinal: int) -> BooleanFacts:
        return BooleanFacts(
            OutcomeFacts(True, frozenset({InputLiteral(input_ordinal, True)})),
            OutcomeFacts(True, frozenset({InputLiteral(input_ordinal, False)})),
        )

    def value(self) -> dict[str, object]:
        return {
            "when_true": self.when_true.value(),
            "when_false": self.when_false.value(),
        }


def _contradictory(literals: frozenset[InputLiteral]) -> bool:
    positive = {item.input_ordinal for item in literals if item.positive}
    negative = {item.input_ordinal for item in literals if not item.positive}
    return bool(positive & negative)


def _conjoin(left: OutcomeFacts, right: OutcomeFacts) -> OutcomeFacts:
    if not left.possible or not right.possible:
        return OutcomeFacts(False)
    literals = left.literals | right.literals
    if _contradictory(literals):
        return OutcomeFacts(False)
    return OutcomeFacts(True, literals)


def _alternatives(*items: OutcomeFacts) -> OutcomeFacts:
    possible = [item for item in items if item.possible]
    if not possible:
        return OutcomeFacts(False)
    literals = set(possible[0].literals)
    for item in possible[1:]:
        literals.intersection_update(item.literals)
    return OutcomeFacts(True, frozenset(literals))


def _fail(code: str, detail: str, outcome: str = "Refused") -> None:
    raise ContractFailure(outcome, code, detail)


def _strict_dict(value: object, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        _fail("F0V2B2C1B5B1-M-SHAPE", f"{label} has another exact shape", "Malformed")
    return value


def _seq(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not list or len(value) > MAX_ITEMS:
        _fail(
            "F0V2B2C1B5B1-M-SEQUENCE",
            f"{label} is not one bounded sequence",
            "Malformed",
        )
    return tuple(value)


def _ref(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        _fail(
            "F0V2B2C1B5B1-M-REFERENCE",
            f"{label} is not one natural reference",
            "Malformed",
        )
    return value


def _symbol(value: object, label: str) -> str:
    if type(value) is not str or not value or len(value) > 128:
        _fail(
            "F0V2B2C1B5B1-M-SYMBOL", f"{label} is not one bounded symbol", "Malformed"
        )
    return value


def _canonical_refs(value: object, label: str) -> tuple[int, ...]:
    result = tuple(_ref(item, label) for item in _seq(value, label))
    if result != tuple(sorted(set(result))):
        _fail(
            "F0V2B2C1B5B1-R-CANONICAL-SET",
            f"{label} is not ascending and unique",
        )
    return result


def _term_facts(
    value: object,
    environment: tuple[BooleanFacts, ...],
    counter: list[int],
    depth: int,
) -> BooleanFacts:
    counter[0] += 1
    if counter[0] > MAX_TERM_NODES or depth > MAX_TERM_DEPTH:
        _fail(
            "F0V2B2C1B5B1-M-TERM-BOUND",
            "Boolean term crosses the Foundation node or depth bound",
            "Malformed",
        )
    if type(value) is not dict or type(value.get("tag")) is not str:
        _fail("F0V2B2C1B5B1-M-TERM", "Boolean term has no exact tag", "Malformed")
    tag = value["tag"]
    if tag == "Literal":
        item = _strict_dict(value, {"tag", "value"}, "Literal")
        if type(item["value"]) is not bool:
            _fail("F0V2B2C1B5B1-M-TERM", "Boolean literal is not Boolean", "Malformed")
        return BooleanFacts.literal(item["value"])
    if tag == "Variable":
        item = _strict_dict(value, {"tag", "index"}, "Variable")
        index = _ref(item["index"], "variable index")
        if index >= len(environment):
            _fail(
                "F0V2B2C1B5B1-M-TERM",
                "variable is outside its environment",
                "Malformed",
            )
        return environment[index]
    if tag == "Let":
        item = _strict_dict(value, {"tag", "bound", "body"}, "Let")
        bound = _term_facts(item["bound"], environment, counter, depth + 1)
        return _term_facts(item["body"], (bound, *environment), counter, depth + 1)
    if tag == "Conditional":
        item = _strict_dict(
            value,
            {"tag", "condition", "when_true", "when_false"},
            "Conditional",
        )
        condition = _term_facts(item["condition"], environment, counter, depth + 1)
        when_true = _term_facts(item["when_true"], environment, counter, depth + 1)
        when_false = _term_facts(item["when_false"], environment, counter, depth + 1)
        return BooleanFacts(
            _alternatives(
                _conjoin(condition.when_true, when_true.when_true),
                _conjoin(condition.when_false, when_false.when_true),
            ),
            _alternatives(
                _conjoin(condition.when_true, when_true.when_false),
                _conjoin(condition.when_false, when_false.when_false),
            ),
        )
    if tag == "PrimitiveCall":
        item = _strict_dict(value, {"tag", "primitive", "arguments"}, "PrimitiveCall")
        _symbol(item["primitive"], "primitive coordinate")
        for argument in _seq(item["arguments"], "primitive arguments"):
            _term_facts(argument, environment, counter, depth + 1)
        # Foundation owns the primitive denotation.  The base PIR terminal
        # checker deliberately imports no primitive-specific implication law.
        return BooleanFacts.unknown()
    _fail(
        "F0V2B2C1B5B1-M-TERM",
        "term tag is outside the selected Foundation Boolean fragment",
        "Malformed",
    )


def analyze_boolean_algorithm(value: object) -> tuple[BooleanFacts, int]:
    """Return sound must-facts over exact Boolean input ordinals."""

    algorithm = _strict_dict(
        value, {"algorithm_kind", "ordered_inputs", "term"}, "algorithm"
    )
    _symbol(algorithm["algorithm_kind"], "algorithm kind")
    input_count = _ref(algorithm["ordered_inputs"], "ordered input count")
    if input_count > MAX_ITEMS:
        _fail(
            "F0V2B2C1B5B1-M-SEQUENCE",
            "algorithm input count exceeds the bound",
            "Malformed",
        )
    counter = [0]
    facts = _term_facts(
        algorithm["term"],
        tuple(BooleanFacts.variable(index) for index in range(input_count)),
        counter,
        0,
    )
    return facts, counter[0]


@dataclass(frozen=True)
class PublicBooleanInput:
    reference: int


@dataclass(frozen=True)
class CheckOutputInput:
    check: int


GuardInput = PublicBooleanInput | CheckOutputInput


@dataclass(frozen=True)
class Guard:
    key: str
    inputs: tuple[GuardInput, ...]
    facts: BooleanFacts
    term_nodes: int

    @property
    def always_true(self) -> bool:
        return not self.facts.when_false.possible

    @property
    def always_false(self) -> bool:
        return not self.facts.when_true.possible


def _guard(value: object) -> Guard | None:
    if value is None:
        return None
    item = _strict_dict(value, {"algorithm", "evaluation_contract", "inputs"}, "guard")
    _symbol(item["evaluation_contract"], "evaluation contract")
    raw_inputs = _seq(item["inputs"], "guard inputs")
    algorithm = _strict_dict(
        item["algorithm"],
        {"algorithm_kind", "ordered_inputs", "term"},
        "guard algorithm",
    )
    if algorithm["ordered_inputs"] != len(raw_inputs):
        _fail(
            "F0V2B2C1B5B1-R-GUARD-ABI",
            "guard input count differs from its algorithm ABI",
        )
    inputs: list[GuardInput] = []
    for raw in raw_inputs:
        source = _strict_dict(raw, {"kind", "ref"}, "guard input")
        reference = _ref(source["ref"], "guard input reference")
        if source["kind"] == "PublicBoolean":
            inputs.append(PublicBooleanInput(reference))
        elif source["kind"] == "CheckOutput":
            inputs.append(CheckOutputInput(reference))
        else:
            _fail(
                "F0V2B2C1B5B1-M-GUARD-INPUT",
                "guard input kind is outside the closed sum",
                "Malformed",
            )
    facts, term_nodes = analyze_boolean_algorithm(algorithm)
    canonical = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return Guard(
        hashlib.sha256(canonical).hexdigest(), tuple(inputs), facts, term_nodes
    )


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
class TerminalDecl:
    verdict: TerminalVerdict
    public_outputs: tuple[str, ...]
    required_true_checks: tuple[int, ...]
    required_applied_reductions: tuple[int, ...]
    terminal_claims: tuple[int, ...]


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
    guard: Guard | None
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
    positive: frozenset[str] = frozenset()
    negative: frozenset[str] = frozenset()
    impossible: bool = False

    def normalized(self) -> Cube:
        return Cube(
            self.positive,
            self.negative,
            self.impossible or bool(self.positive & self.negative),
        )

    def require_true(self, guard: Guard | None) -> Cube:
        if self.impossible:
            return self
        if guard is None or guard.always_true:
            return self
        if guard.always_false:
            return Cube(impossible=True)
        return Cube(self.positive | {guard.key}, self.negative).normalized()

    def require_false(self, guard: Guard | None) -> Cube:
        if (
            self.impossible
            or guard is None
            or (guard is not None and guard.always_true)
        ):
            return Cube(impossible=True)
        if guard.always_false:
            return self
        return Cube(self.positive, self.negative | {guard.key}).normalized()

    def value(self) -> dict[str, object]:
        return {
            "positive": sorted(self.positive),
            "negative": sorted(self.negative),
            "impossible": self.impossible,
        }


def cube_implies(left: Cube, right: Cube) -> bool:
    left = left.normalized()
    right = right.normalized()
    if left.impossible:
        return True
    if right.impossible:
        return False
    return right.positive <= left.positive and right.negative <= left.negative


def cubes_disjoint(left: Cube, right: Cube) -> bool:
    left = left.normalized()
    right = right.normalized()
    return (
        left.impossible
        or right.impossible
        or bool(left.positive & right.negative)
        or bool(right.positive & left.negative)
    )


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
    terminal_dispositions: tuple[tuple[tuple[int, str], ...], ...]
    check_entailments: tuple[tuple[int, int, int], ...]
    reduction_requirements: tuple[tuple[int, int], ...]
    operations: int

    def value(self) -> dict[str, object]:
        return {
            "outcome": self.outcome,
            "code": self.code,
            "active_regions": [item.value() for item in self.active_regions],
            "terminal_live_claims": [
                list(items) for items in self.terminal_live_claims
            ],
            "terminal_dispositions": [
                [list(item) for item in entries]
                for entries in self.terminal_dispositions
            ],
            "check_entailments": [list(item) for item in self.check_entailments],
            "reduction_requirements": [
                list(item) for item in self.reduction_requirements
            ],
            "operations": self.operations,
        }


def _parse(program: object) -> Program:
    root = _strict_dict(
        program,
        {"claims", "reductions", "checks", "terminals", "occurrences"},
        "program",
    )
    claims: list[ClaimDecl] = []
    for raw in _seq(root["claims"], "claims"):
        item = _strict_dict(raw, {"usage", "source"}, "claim")
        try:
            usage = ClaimUsage(item["usage"])
        except (TypeError, ValueError):
            _fail(
                "F0V2B2C1B5B1-M-CLAIM-USAGE",
                "claim usage is outside the closed sum",
                "Malformed",
            )
        source = _strict_dict(
            item["source"], {"kind", "reduction", "output"}, "claim source"
        )
        if source["kind"] == "Initial":
            if source["reduction"] is not None or source["output"] is not None:
                _fail(
                    "F0V2B2C1B5B1-M-CLAIM-SOURCE",
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
                "F0V2B2C1B5B1-M-CLAIM-SOURCE",
                "claim source is outside the closed sum",
                "Malformed",
            )
        claims.append(ClaimDecl(usage, parsed_source))

    reductions: list[ReductionDecl] = []
    for raw in _seq(root["reductions"], "reductions"):
        item = _strict_dict(raw, {"inputs", "outputs"}, "reduction")
        reductions.append(
            ReductionDecl(
                tuple(
                    _ref(value, "reduction input")
                    for value in _seq(item["inputs"], "reduction inputs")
                ),
                tuple(
                    _ref(value, "reduction output")
                    for value in _seq(item["outputs"], "reduction outputs")
                ),
            )
        )

    checks: list[CheckDecl] = []
    for raw in _seq(root["checks"], "checks"):
        item = _strict_dict(raw, {"label"}, "check")
        checks.append(CheckDecl(_symbol(item["label"], "check label")))

    terminals: list[TerminalDecl] = []
    for raw in _seq(root["terminals"], "terminals"):
        item = _strict_dict(
            raw,
            {
                "verdict",
                "public_outputs",
                "required_true_checks",
                "required_applied_reductions",
                "terminal_claims",
            },
            "terminal",
        )
        try:
            verdict = TerminalVerdict(item["verdict"])
        except (TypeError, ValueError):
            _fail(
                "F0V2B2C1B5B1-M-VERDICT",
                "terminal verdict is outside the closed sum",
                "Malformed",
            )
        terminals.append(
            TerminalDecl(
                verdict,
                tuple(
                    _symbol(value, "public output")
                    for value in _seq(item["public_outputs"], "public outputs")
                ),
                _canonical_refs(item["required_true_checks"], "required Check set"),
                _canonical_refs(
                    item["required_applied_reductions"], "required Reduction set"
                ),
                _canonical_refs(item["terminal_claims"], "terminal Claim set"),
            )
        )

    occurrences: list[Occurrence] = []
    for raw in _seq(root["occurrences"], "occurrences"):
        item = _strict_dict(raw, {"guard", "effect"}, "occurrence")
        effect = _strict_dict(item["effect"], {"kind", "ref"}, "effect")
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
                "F0V2B2C1B5B1-U-EFFECT",
                "effect is outside the bounded Terminal fragment",
                "Unsupported",
            )
        occurrences.append(Occurrence(_guard(item["guard"]), parsed_effect))
    if not terminals or not occurrences:
        _fail(
            "F0V2B2C1B5B1-R-NONEMPTY", "terminal and occurrence tables must be nonempty"
        )
    return Program(
        tuple(claims),
        tuple(reductions),
        tuple(checks),
        tuple(terminals),
        tuple(occurrences),
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
            table, reference = check_positions, effect.check
        elif type(effect) is ReductionEffect:
            table, reference = reduction_positions, effect.reduction
        else:
            assert type(effect) is TerminalEffect
            table, reference = terminal_positions, effect.terminal
        if reference not in table:
            _fail("F0V2B2C1B5B1-R-EFFECT-REFERENCE", "effect reference is absent")
        table[reference].append(position)
    for table, label in (
        (check_positions, "Check"),
        (reduction_positions, "Reduction"),
        (terminal_positions, "Terminal"),
    ):
        if any(len(values) != 1 for values in table.values()):
            _fail("F0V2B2C1B5B1-R-BACKLINK", f"{label} backlink is not one-to-one")
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
    """Analyze one bounded candidate without assignment enumeration."""

    program = _parse(program_value)
    operations = len(program.occurrences)
    check_positions, reduction_positions, terminal_positions = _positions(program)
    final = program.occurrences[-1]
    if final.guard is not None or type(final.effect) is not TerminalEffect:
        _fail(
            "F0V2B2C1B5B1-R-FINAL-FALLBACK",
            "final occurrence is not an unconditional terminal",
        )

    output_coordinates: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(program.claims):
        if type(claim.source) is not ReductionOutputSource:
            continue
        coordinate = (claim.source.reduction, claim.source.output_ordinal)
        if claim.source.reduction >= len(program.reductions):
            _fail(
                "F0V2B2C1B5B1-R-CLAIM-SOURCE", "claim names an absent source Reduction"
            )
        reduction = program.reductions[claim.source.reduction]
        if (
            claim.source.output_ordinal >= len(reduction.outputs)
            or reduction.outputs[claim.source.output_ordinal] != claim_ref
        ):
            _fail(
                "F0V2B2C1B5B1-R-CLAIM-SOURCE",
                "claim source and Reduction output disagree",
            )
        if coordinate in output_coordinates:
            _fail("F0V2B2C1B5B1-R-CLAIM-SSA", "two Claims share one Reduction output")
        output_coordinates[coordinate] = claim_ref
    expected_outputs = {
        (reduction_ref, ordinal): claim_ref
        for reduction_ref, reduction in enumerate(program.reductions)
        for ordinal, claim_ref in enumerate(reduction.outputs)
    }
    if output_coordinates != expected_outputs:
        _fail(
            "F0V2B2C1B5B1-R-CLAIM-OUTPUT-CLOSURE",
            "Reduction outputs and Claim sources differ",
        )
    for reduction in program.reductions:
        if not reduction.inputs or len(set(reduction.inputs)) != len(reduction.inputs):
            _fail(
                "F0V2B2C1B5B1-R-REDUCTION-INPUTS",
                "Reduction inputs are empty or repeated",
            )
        if len(set(reduction.outputs)) != len(reduction.outputs):
            _fail("F0V2B2C1B5B1-R-REDUCTION-OUTPUTS", "Reduction outputs repeat")
        if any(
            reference >= len(program.claims)
            for reference in (*reduction.inputs, *reduction.outputs)
        ):
            _fail("F0V2B2C1B5B1-R-CLAIM-REFERENCE", "Reduction names an absent Claim")

    regions = _active_regions(program)
    operations += len(regions)
    for position, occurrence in enumerate(program.occurrences):
        if occurrence.guard is None:
            continue
        operations += occurrence.guard.term_nodes
        for source in occurrence.guard.inputs:
            if type(source) is not CheckOutputInput:
                continue
            if source.check >= len(program.checks):
                _fail(
                    "F0V2B2C1B5B1-R-GUARD-INPUT", "guard names an absent Check output"
                )
            source_position = check_positions[source.check]
            if source_position >= position or not cube_implies(
                regions[position], regions[source_position]
            ):
                _fail(
                    "F0V2B2C1B5B1-R-GUARD-INPUT",
                    "guard does not guarantee its Check output exists",
                )

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
                        "F0V2B2C1B5B1-R-LINEAR-PATH-OVERLAP",
                        "two linear-Claim consumers overlap",
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
                    "F0V2B2C1B5B1-R-REDUCTION-LIVENESS",
                    f"Reduction {reduction_ref} input {claim_ref} is {state.value}",
                )

    terminal_live_claims: list[tuple[int, ...]] = [() for _ in program.terminals]
    terminal_dispositions: list[tuple[tuple[int, str], ...]] = [
        () for _ in program.terminals
    ]
    check_entailments: list[tuple[int, int, int]] = []
    reduction_requirements: list[tuple[int, int]] = []
    for terminal_ref, terminal in enumerate(program.terminals):
        position = terminal_positions[terminal_ref]
        region = regions[position]
        if any(
            reference >= len(program.claims) for reference in terminal.terminal_claims
        ):
            _fail("F0V2B2C1B5B1-R-TERMINAL-CLAIM", "Terminal names an absent Claim")
        for check_ref in terminal.required_true_checks:
            if check_ref >= len(program.checks):
                _fail(
                    "F0V2B2C1B5B1-R-CHECK-REFERENCE",
                    "Terminal names an absent required Check",
                )
            check_position = check_positions[check_ref]
            if check_position >= position or not cube_implies(
                region, regions[check_position]
            ):
                _fail(
                    "F0V2B2C1B5B1-R-CHECK-OCCURRENCE",
                    "Terminal does not guarantee the required Check occurred",
                )
            guard = program.occurrences[position].guard
            if region.impossible:
                continue
            if guard is None:
                _fail(
                    "F0V2B2C1B5B1-R-CHECK-ENTAILMENT",
                    "Always cannot entail a runtime Check result",
                )
            positive_inputs = {
                literal.input_ordinal
                for literal in guard.facts.when_true.literals
                if literal.positive
            }
            witnesses = [
                input_ordinal
                for input_ordinal, source in enumerate(guard.inputs)
                if type(source) is CheckOutputInput
                and source.check == check_ref
                and input_ordinal in positive_inputs
            ]
            if not witnesses:
                _fail(
                    "F0V2B2C1B5B1-R-CHECK-ENTAILMENT",
                    "Terminal Guard does not structurally entail required Check truth",
                )
            check_entailments.append((terminal_ref, check_ref, witnesses[0]))
        for reduction_ref in terminal.required_applied_reductions:
            if reduction_ref >= len(program.reductions):
                _fail(
                    "F0V2B2C1B5B1-R-REQUIRED-REDUCTION",
                    "Terminal names an absent required Reduction",
                )
            reduction_position = reduction_positions[reduction_ref]
            if reduction_position >= position or not cube_implies(
                region, regions[reduction_position]
            ):
                _fail(
                    "F0V2B2C1B5B1-R-REQUIRED-REDUCTION",
                    "Terminal activity does not guarantee required Reduction application",
                )
            if not region.impossible:
                reduction_requirements.append((terminal_ref, reduction_ref))
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
                    "F0V2B2C1B5B1-R-PATH-AMBIGUITY",
                    f"Terminal {terminal_ref} cannot decide Claim {claim_ref} liveness",
                )
            if state is ClaimState.LIVE:
                live.append(claim_ref)
        terminal_live_claims[terminal_ref] = tuple(live)
        if terminal.terminal_claims != tuple(live):
            _fail(
                "F0V2B2C1B5B1-R-TERMINAL-CLOSURE",
                f"Terminal {terminal_ref} Claim set differs from its live set",
            )
        disposition = (
            DerivedClaimDisposition.CONSUME
            if terminal.verdict is TerminalVerdict.ACCEPT
            else DerivedClaimDisposition.DISCHARGE
        )
        terminal_dispositions[terminal_ref] = tuple(
            (claim_ref, disposition.value) for claim_ref in terminal.terminal_claims
        )

    return Analysis(
        "Affirmative",
        "F0V2B2C1B5B1-A-TERMINAL-OWNER-CONTRACTS",
        regions,
        tuple(terminal_live_claims),
        tuple(terminal_dispositions),
        tuple(check_entailments),
        tuple(reduction_requirements),
        operations,
    )
