"""Bounded reference model for verifier-derived query-plan elaboration.

This instrument models the selected architectural seam, not the complete PIR
carrier.  Logical derived-word reads are separately identified and then
statically erased into guarded ordinary source reads and pure computations.
Runtime execution never allocates an occurrence or consults a host callback.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import json
from types import MappingProxyType
from typing import Any, Mapping, Sequence


class OutcomeClass(str, Enum):
    MALFORMED = "Malformed"
    MISSING_DEPENDENCY = "MissingDependency"
    KIND_MISMATCH = "KindMismatch"
    UNSUPPORTED = "Unsupported"
    REFUSED = "Refused"
    SEMANTIC_FAILURE = "SemanticFailure"
    NONCOMPLETION = "DeterministicNoncompletion"


class PlanError(ValueError):
    def __init__(self, outcome: OutcomeClass, boundary: str, code: str, message: str):
        super().__init__(message)
        self.outcome = outcome
        self.boundary = boundary
        self.code = code


def _fail(
    outcome: OutcomeClass, boundary: str, code: str, message: str
) -> PlanError:
    return PlanError(outcome, boundary, code, message)


class Visibility(str, Enum):
    PUBLIC = "Public"
    VERIFIER_ONLY = "VerifierOnly"


@dataclass(frozen=True)
class OraclePort:
    name: str
    visibility: Visibility = Visibility.PUBLIC


@dataclass(frozen=True)
class PureStep:
    name: str
    algorithm: str
    inputs: tuple[str, ...]


@dataclass(frozen=True)
class ReadStep:
    name: str
    source_port: str
    index: str


@dataclass(frozen=True)
class CallStep:
    name: str
    program: str
    index: str
    arguments: tuple[tuple[str, str], ...]
    oracle_bindings: tuple[tuple[str, str], ...]


Step = PureStep | ReadStep | CallStep


@dataclass(frozen=True)
class ProgramCase:
    tag: str
    steps: tuple[Step, ...]
    result: str | None = None
    terminal: str | None = None


@dataclass(frozen=True)
class DerivedWordProgram:
    name: str
    modulus: int
    arguments: tuple[str, ...]
    oracle_ports: tuple[OraclePort, ...]
    route_algorithm: str
    route_inputs: tuple[str, ...]
    cases: tuple[ProgramCase, ...]
    output_visibility: Visibility
    maximum_elaboration_depth: int
    maximum_leaf_reads: int


@dataclass(frozen=True)
class PlanSite:
    name: str
    program: str
    index_input: str
    arguments: tuple[tuple[str, str], ...]
    oracle_bindings: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class QueryPlan:
    name: str
    inputs: tuple[str, ...]
    source_oracles: tuple[str, ...]
    sites: tuple[PlanSite, ...]


@dataclass(frozen=True)
class StaticEvent:
    kind: str
    path: tuple[str, ...]
    guard_path: tuple[str, ...]
    details: tuple[tuple[str, Any], ...]

    def body(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "path": list(self.path),
            "guard_path": list(self.guard_path),
            "details": {key: value for key, value in self.details},
        }


@dataclass(frozen=True)
class QueryTrace:
    path: tuple[str, ...]
    source_oracle: str
    index: int
    visibility: Visibility


@dataclass(frozen=True)
class ExecutionResult:
    value: int | None
    terminal: str | None
    queries: tuple[QueryTrace, ...]


@dataclass(frozen=True)
class Elaboration:
    plan_id: str
    target_core_id: str
    events: tuple[StaticEvent, ...]
    logical_to_source_events: tuple[tuple[str, tuple[int, ...]], ...]


@dataclass(frozen=True)
class CheckedElaboration:
    plan_id: str
    target_core_id: str
    event_count: int


_ROUTE_CASES: Mapping[str, tuple[str, ...]] = MappingProxyType(
    {
        "always": ("only",),
        "collision-membership": ("collision", "regular"),
        "set-membership": ("member", "outside"),
    }
)

_PURE_ALGORITHMS = frozenset(
    {
        "field-add",
        "field-negate",
        "identity",
        "lagrange-quotient",
        "weighted-sum-three",
        "binary-fold",
        "four-point-multilinear-fold",
    }
)


def _strict_names(values: Sequence[str], label: str) -> tuple[str, ...]:
    if any(type(value) is not str or not value for value in values):
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:names",
            "VDQP-FORM-001",
            f"{label} contains an invalid name",
        )
    result = tuple(values)
    if len(result) != len(set(result)):
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:names",
            "VDQP-FORM-002",
            f"{label} repeats a name",
        )
    return result


def _step_name(step: Step) -> str:
    return step.name


def _pairs_to_map(
    pairs: Sequence[tuple[str, str]], label: str
) -> Mapping[str, str]:
    result: dict[str, str] = {}
    for key, value in pairs:
        if type(key) is not str or not key or type(value) is not str or not value:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:bindings",
                "VDQP-FORM-003",
                f"{label} contains an invalid binding",
            )
        if key in result:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:bindings",
                "VDQP-FORM-004",
                f"{label} repeats {key!r}",
            )
        result[key] = value
    return MappingProxyType(result)


def _route(
    algorithm: str, values: Sequence[Any]
) -> str:
    if algorithm == "always":
        if values:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-001",
                "the always route accepts no operands",
            )
        return "only"
    if algorithm in ("collision-membership", "set-membership"):
        if len(values) != 2 or type(values[0]) is not int:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-002",
                "membership routing expects an integer and a finite point sequence",
            )
        points = values[1]
        if not isinstance(points, tuple) or any(type(item) is not int for item in points):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-003",
                "membership points must be an immutable integer sequence",
            )
        member = values[0] in points
        if algorithm == "collision-membership":
            return "collision" if member else "regular"
        return "member" if member else "outside"
    raise _fail(
        OutcomeClass.UNSUPPORTED,
        "execution:route",
        "VDQP-EXEC-004",
        f"unsupported route algorithm {algorithm!r}",
    )


def _inverse(value: int, modulus: int) -> int:
    value %= modulus
    if value == 0:
        raise _fail(
            OutcomeClass.SEMANTIC_FAILURE,
            "execution:field",
            "VDQP-EXEC-005",
            "division denominator is zero",
        )
    return pow(value, -1, modulus)


def _lagrange_value(
    x: int, points: tuple[int, ...], answers: tuple[int, ...], modulus: int
) -> int:
    if not points or len(points) != len(answers) or len(points) != len(set(points)):
        raise _fail(
            OutcomeClass.SEMANTIC_FAILURE,
            "execution:interpolation",
            "VDQP-EXEC-006",
            "interpolation points must be nonempty and unique",
        )
    total = 0
    for ordinal, point in enumerate(points):
        numerator = 1
        denominator = 1
        for other_ordinal, other in enumerate(points):
            if other_ordinal == ordinal:
                continue
            numerator = numerator * (x - other) % modulus
            denominator = denominator * (point - other) % modulus
        total += answers[ordinal] * numerator * _inverse(denominator, modulus)
    return total % modulus


def _pure(algorithm: str, values: Sequence[Any], modulus: int) -> int:
    if algorithm not in _PURE_ALGORITHMS:
        raise _fail(
            OutcomeClass.UNSUPPORTED,
            "execution:pure",
            "VDQP-EXEC-007",
            f"unsupported pure algorithm {algorithm!r}",
        )
    if algorithm == "identity":
        if len(values) != 1 or type(values[0]) is not int:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-008",
                "identity expects one integer",
            )
        return values[0] % modulus
    if algorithm == "field-add":
        if len(values) != 2 or any(type(value) is not int for value in values):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-009",
                "field addition expects two integers",
            )
        return (values[0] + values[1]) % modulus
    if algorithm == "field-negate":
        if len(values) != 1 or type(values[0]) is not int:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-010",
                "field negation expects one integer",
            )
        return (-values[0]) % modulus
    if algorithm == "lagrange-quotient":
        if (
            len(values) != 4
            or type(values[0]) is not int
            or type(values[1]) is not int
            or not isinstance(values[2], tuple)
            or not isinstance(values[3], tuple)
        ):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-011",
                "quotient expects source value, index, points, and answers",
            )
        source_value, x, points, answers = values
        interpolation = _lagrange_value(x, points, answers, modulus)
        vanishing = 1
        for point in points:
            vanishing = vanishing * (x - point) % modulus
        return (source_value - interpolation) * _inverse(vanishing, modulus) % modulus
    if algorithm == "weighted-sum-three":
        if len(values) != 4 or any(type(value) is not int for value in values):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-012",
                "three-word batching expects three values and one coefficient",
            )
        a, b, c, coefficient = values
        return (a + coefficient * b + coefficient * coefficient * c) % modulus
    if algorithm == "binary-fold":
        if len(values) != 4 or any(type(value) is not int for value in values):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-013",
                "binary folding expects two values, one index, and one challenge",
            )
        positive, negative, x, challenge = values
        even = (positive + negative) * _inverse(2, modulus) % modulus
        odd = (positive - negative) * _inverse(2 * x, modulus) % modulus
        return (even + challenge * odd) % modulus
    if algorithm == "four-point-multilinear-fold":
        if len(values) != 6 or any(type(value) is not int for value in values):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:pure",
                "VDQP-EXEC-014",
                "four-point folding expects four values and two challenges",
            )
        v00, v01, v10, v11, alpha0, alpha1 = values
        low = (v00 * (1 - alpha0) + v01 * alpha0) % modulus
        high = (v10 * (1 - alpha0) + v11 * alpha0) % modulus
        return (low * (1 - alpha1) + high * alpha1) % modulus
    raise AssertionError("closed pure dispatch exhausted")


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _step_body(step: Step) -> dict[str, Any]:
    if isinstance(step, PureStep):
        return {
            "kind": "pure",
            "name": step.name,
            "algorithm": step.algorithm,
            "inputs": list(step.inputs),
        }
    if isinstance(step, ReadStep):
        return {
            "kind": "read",
            "name": step.name,
            "source_port": step.source_port,
            "index": step.index,
        }
    return {
        "kind": "call",
        "name": step.name,
        "program": step.program,
        "index": step.index,
        "arguments": {key: value for key, value in step.arguments},
        "oracle_bindings": {key: value for key, value in step.oracle_bindings},
    }


def program_body(program: DerivedWordProgram) -> dict[str, Any]:
    return {
        "name": program.name,
        "modulus": program.modulus,
        "arguments": list(program.arguments),
        "oracle_ports": [
            {"name": port.name, "visibility": port.visibility.value}
            for port in program.oracle_ports
        ],
        "route_algorithm": program.route_algorithm,
        "route_inputs": list(program.route_inputs),
        "cases": [
            {
                "tag": case.tag,
                "steps": [_step_body(step) for step in case.steps],
                "result": case.result,
                "terminal": case.terminal,
            }
            for case in program.cases
        ],
        "output_visibility": program.output_visibility.value,
        "maximum_elaboration_depth": program.maximum_elaboration_depth,
        "maximum_leaf_reads": program.maximum_leaf_reads,
    }


def program_id(program: DerivedWordProgram) -> str:
    return hashlib.sha256(
        b"zkc.pir.verifier-derived-word-program\x00"
        + _canonical_bytes(program_body(program))
    ).hexdigest()


def plan_body(plan: QueryPlan, programs: Mapping[str, DerivedWordProgram]) -> dict[str, Any]:
    return {
        "name": plan.name,
        "inputs": list(plan.inputs),
        "source_oracles": list(plan.source_oracles),
        "sites": [
            {
                "name": site.name,
                "program_id": program_id(programs[site.program]),
                "index_input": site.index_input,
                "arguments": {key: value for key, value in site.arguments},
                "oracle_bindings": {
                    key: value for key, value in site.oracle_bindings
                },
            }
            for site in plan.sites
        ],
    }


def plan_id(plan: QueryPlan, programs: Mapping[str, DerivedWordProgram]) -> str:
    return hashlib.sha256(
        b"zkc.pir.verifier-derived-query-plan\x00"
        + _canonical_bytes(plan_body(plan, programs))
    ).hexdigest()


def _program_metrics(
    name: str,
    programs: Mapping[str, DerivedWordProgram],
    visiting: tuple[str, ...] = (),
) -> tuple[int, int]:
    if name in visiting:
        raise _fail(
            OutcomeClass.REFUSED,
            "formation:program-graph",
            "VDQP-FORM-005",
            "derived-word program graph is cyclic",
        )
    program = programs.get(name)
    if program is None:
        raise _fail(
            OutcomeClass.MISSING_DEPENDENCY,
            "formation:program-graph",
            "VDQP-FORM-006",
            f"missing derived-word program {name!r}",
        )
    case_metrics: list[tuple[int, int]] = []
    for case in program.cases:
        depth = 1
        leaves = 0
        for step in case.steps:
            if isinstance(step, ReadStep):
                leaves += 1
            elif isinstance(step, CallStep):
                child_depth, child_leaves = _program_metrics(
                    step.program, programs, visiting + (name,)
                )
                depth = max(depth, 1 + child_depth)
                leaves += child_leaves
        case_metrics.append((depth, leaves))
    return max(case_metrics, default=(1, 0))


def validate_programs(
    programs: Mapping[str, DerivedWordProgram]
) -> Mapping[str, DerivedWordProgram]:
    if not programs:
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:programs",
            "VDQP-FORM-007",
            "the program catalog is empty",
        )
    sealed: dict[str, DerivedWordProgram] = {}
    for name, program in programs.items():
        if type(name) is not str or not name or name != program.name:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:programs",
                "VDQP-FORM-008",
                "program key and declared name disagree",
            )
        if type(program.modulus) is not int or program.modulus <= 2:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:programs",
                "VDQP-FORM-009",
                "program modulus must be an integer greater than two",
            )
        arguments = _strict_names(program.arguments, f"{name} arguments")
        ports = _strict_names(
            tuple(port.name for port in program.oracle_ports), f"{name} oracle ports"
        )
        if program.route_algorithm not in _ROUTE_CASES:
            raise _fail(
                OutcomeClass.UNSUPPORTED,
                "formation:route",
                "VDQP-FORM-010",
                f"unsupported route algorithm {program.route_algorithm!r}",
            )
        initial_refs = frozenset(("index",) + arguments)
        if any(ref not in initial_refs for ref in program.route_inputs):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:route",
                "VDQP-FORM-011",
                "routing may depend only on the requested index and prior public arguments",
            )
        tags = tuple(case.tag for case in program.cases)
        if tags != tuple(sorted(set(tags))):
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:cases",
                "VDQP-FORM-012",
                "program cases must be sorted and unique",
            )
        if frozenset(tags) != frozenset(_ROUTE_CASES[program.route_algorithm]):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:cases",
                "VDQP-FORM-013",
                "program cases do not exhaust the route result type",
            )
        if program.output_visibility is Visibility.PUBLIC and any(
            port.visibility is Visibility.VERIFIER_ONLY for port in program.oracle_ports
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:visibility",
                "VDQP-FORM-014",
                "a public derived result cannot declassify a verifier-only source",
            )
        for case in program.cases:
            if (case.result is None) == (case.terminal is None):
                raise _fail(
                    OutcomeClass.MALFORMED,
                    "formation:cases",
                    "VDQP-FORM-015",
                    "each case must return a result or reach one explicit terminal",
                )
            available = set(initial_refs)
            answer_dependent: set[str] = set()
            step_names = _strict_names(
                tuple(_step_name(step) for step in case.steps),
                f"{name}/{case.tag} step names",
            )
            del step_names
            for step in case.steps:
                if isinstance(step, PureStep):
                    if step.algorithm not in _PURE_ALGORITHMS:
                        raise _fail(
                            OutcomeClass.UNSUPPORTED,
                            "formation:pure",
                            "VDQP-FORM-016",
                            f"unsupported pure algorithm {step.algorithm!r}",
                        )
                    if any(ref not in available for ref in step.inputs):
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:pure",
                            "VDQP-FORM-017",
                            "a pure step reads an unavailable local value",
                        )
                    if any(ref in answer_dependent for ref in step.inputs):
                        answer_dependent.add(step.name)
                elif isinstance(step, ReadStep):
                    if step.source_port not in ports:
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:read",
                            "VDQP-FORM-018",
                            "a read names an absent source port",
                        )
                    if step.index not in available:
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:read",
                            "VDQP-FORM-019",
                            "a read index is unavailable",
                        )
                    if step.index in answer_dependent:
                        raise _fail(
                            OutcomeClass.REFUSED,
                            "formation:read",
                            "VDQP-FORM-020",
                            "source-query routing may not depend on a source answer",
                        )
                    answer_dependent.add(step.name)
                else:
                    if step.program not in programs:
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:call",
                            "VDQP-FORM-021",
                            "a call names an absent program",
                        )
                    child = programs[step.program]
                    arguments_map = _pairs_to_map(step.arguments, "call arguments")
                    oracle_map = _pairs_to_map(step.oracle_bindings, "call oracles")
                    if frozenset(arguments_map) != frozenset(child.arguments):
                        raise _fail(
                            OutcomeClass.KIND_MISMATCH,
                            "formation:call",
                            "VDQP-FORM-022",
                            "call argument bindings are not total",
                        )
                    if frozenset(oracle_map) != frozenset(
                        port.name for port in child.oracle_ports
                    ):
                        raise _fail(
                            OutcomeClass.KIND_MISMATCH,
                            "formation:call",
                            "VDQP-FORM-023",
                            "call oracle bindings are not total",
                        )
                    refs = (step.index,) + tuple(arguments_map.values())
                    if any(ref not in available for ref in refs):
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:call",
                            "VDQP-FORM-024",
                            "call input is unavailable",
                        )
                    if any(ref in answer_dependent for ref in refs):
                        raise _fail(
                            OutcomeClass.REFUSED,
                            "formation:call",
                            "VDQP-FORM-025",
                            "nested query routing may not depend on a source answer",
                        )
                    if any(source not in ports for source in oracle_map.values()):
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:call",
                            "VDQP-FORM-026",
                            "call maps to an absent parent source port",
                        )
                    answer_dependent.add(step.name)
                available.add(step.name)
            if case.result is not None and case.result not in available:
                raise _fail(
                    OutcomeClass.MISSING_DEPENDENCY,
                    "formation:cases",
                    "VDQP-FORM-027",
                    "case result is unavailable",
                )
        sealed[name] = replace(program)
    frozen = MappingProxyType(sealed)
    for name, program in frozen.items():
        depth, leaves = _program_metrics(name, frozen)
        if (
            program.maximum_elaboration_depth != depth
            or program.maximum_leaf_reads != leaves
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:bounds",
                "VDQP-FORM-028",
                "declared elaboration bounds do not equal the exact program graph",
            )
    return frozen


def validate_plan(
    plan: QueryPlan, programs: Mapping[str, DerivedWordProgram]
) -> QueryPlan:
    _strict_names(plan.inputs, "plan inputs")
    _strict_names(plan.source_oracles, "plan source oracles")
    site_names = _strict_names(tuple(site.name for site in plan.sites), "plan sites")
    if site_names != tuple(sorted(site_names)):
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:plan",
            "VDQP-FORM-029",
            "plan sites must be in canonical name order",
        )
    for site in plan.sites:
        program = programs.get(site.program)
        if program is None:
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-030",
                "plan site names an absent program",
            )
        if site.index_input not in plan.inputs:
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-031",
                "plan site index input is absent",
            )
        arguments = _pairs_to_map(site.arguments, "site arguments")
        oracles = _pairs_to_map(site.oracle_bindings, "site oracle bindings")
        if frozenset(arguments) != frozenset(program.arguments):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "formation:plan",
                "VDQP-FORM-032",
                "site argument bindings are not total",
            )
        if any(source not in plan.inputs for source in arguments.values()):
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-033",
                "site argument names an absent plan input",
            )
        if frozenset(oracles) != frozenset(
            port.name for port in program.oracle_ports
        ):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "formation:plan",
                "VDQP-FORM-034",
                "site oracle bindings are not total",
            )
        if any(source not in plan.source_oracles for source in oracles.values()):
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-035",
                "site maps to an absent plan source oracle",
            )
    return replace(plan)


def _symbolic_ref(ref: str, environment: Mapping[str, str]) -> str:
    try:
        return environment[ref]
    except KeyError as error:
        raise _fail(
            OutcomeClass.MISSING_DEPENDENCY,
            "elaboration:symbolic-reference",
            "VDQP-ELAB-001",
            f"missing symbolic reference {ref!r}",
        ) from error


def _static_program_events(
    *,
    program_name: str,
    programs: Mapping[str, DerivedWordProgram],
    path: tuple[str, ...],
    guard_path: tuple[str, ...],
    index_symbol: str,
    arguments: Mapping[str, str],
    oracle_bindings: Mapping[str, str],
) -> list[StaticEvent]:
    program = programs[program_name]
    environment: dict[str, str] = {"index": index_symbol, **arguments}
    events = [
        StaticEvent(
            "Route",
            path,
            guard_path,
            (
                ("algorithm", program.route_algorithm),
                (
                    "inputs",
                    tuple(_symbolic_ref(ref, environment) for ref in program.route_inputs),
                ),
            ),
        )
    ]
    for case in program.cases:
        case_environment = dict(environment)
        case_guard = guard_path + (f"{program.name}:{case.tag}",)
        case_path = path + (case.tag,)
        for step in case.steps:
            step_path = case_path + (step.name,)
            output_symbol = "/".join(step_path)
            if isinstance(step, PureStep):
                events.append(
                    StaticEvent(
                        "DerivedValue",
                        step_path,
                        case_guard,
                        (
                            ("algorithm", step.algorithm),
                            (
                                "inputs",
                                tuple(
                                    _symbolic_ref(ref, case_environment)
                                    for ref in step.inputs
                                ),
                            ),
                            ("output", output_symbol),
                        ),
                    )
                )
            elif isinstance(step, ReadStep):
                source = oracle_bindings[step.source_port]
                index = _symbolic_ref(step.index, case_environment)
                events.extend(
                    (
                        StaticEvent(
                            "QueryOracle",
                            step_path + ("query",),
                            case_guard,
                            (("source_oracle", source), ("index", index)),
                        ),
                        StaticEvent(
                            "AnswerOracle",
                            step_path + ("answer",),
                            case_guard,
                            (
                                ("source_oracle", source),
                                ("query_path", "/".join(step_path + ("query",))),
                                ("output", output_symbol),
                            ),
                        ),
                    )
                )
            else:
                call_arguments = _pairs_to_map(step.arguments, "static call arguments")
                call_oracles = _pairs_to_map(
                    step.oracle_bindings, "static call oracle bindings"
                )
                child_arguments = {
                    key: _symbolic_ref(value, case_environment)
                    for key, value in call_arguments.items()
                }
                child_oracles = {
                    key: oracle_bindings[value] for key, value in call_oracles.items()
                }
                events.extend(
                    _static_program_events(
                        program_name=step.program,
                        programs=programs,
                        path=step_path,
                        guard_path=case_guard,
                        index_symbol=_symbolic_ref(step.index, case_environment),
                        arguments=child_arguments,
                        oracle_bindings=child_oracles,
                    )
                )
                events.append(
                    StaticEvent(
                        "BindNestedResult",
                        step_path + ("result",),
                        case_guard,
                        (("output", output_symbol),),
                    )
                )
            case_environment[step.name] = output_symbol
        if case.result is not None:
            events.append(
                StaticEvent(
                    "ReturnDerivedValue",
                    case_path + ("return",),
                    case_guard,
                    (("value", _symbolic_ref(case.result, case_environment)),),
                )
            )
        else:
            events.append(
                StaticEvent(
                    "ReachSemanticTerminal",
                    case_path + ("terminal",),
                    case_guard,
                    (("terminal", case.terminal),),
                )
            )
    return events


def elaborate(
    plan: QueryPlan, programs: Mapping[str, DerivedWordProgram]
) -> Elaboration:
    programs = validate_programs(programs)
    plan = validate_plan(plan, programs)
    all_events: list[StaticEvent] = []
    logical_map: list[tuple[str, tuple[int, ...]]] = []
    for site in plan.sites:
        program = programs[site.program]
        arguments = {
            key: f"plan-input:{value}"
            for key, value in _pairs_to_map(site.arguments, "site arguments").items()
        }
        oracles = dict(_pairs_to_map(site.oracle_bindings, "site oracles"))
        start = len(all_events)
        site_events = _static_program_events(
            program_name=program.name,
            programs=programs,
            path=(site.name,),
            guard_path=(),
            index_symbol=f"plan-input:{site.index_input}",
            arguments=arguments,
            oracle_bindings=oracles,
        )
        all_events.extend(site_events)
        source_ordinals = tuple(
            start + ordinal
            for ordinal, event in enumerate(site_events)
            if event.kind == "QueryOracle"
        )
        logical_map.append((site.name, source_ordinals))
    event_body = [event.body() for event in all_events]
    target_core_id = hashlib.sha256(
        b"zkc.pir.flattened-query-core\x00" + _canonical_bytes(event_body)
    ).hexdigest()
    return Elaboration(
        plan_id=plan_id(plan, programs),
        target_core_id=target_core_id,
        events=tuple(all_events),
        logical_to_source_events=tuple(logical_map),
    )


def check_elaboration(
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    candidate: Elaboration,
) -> CheckedElaboration:
    expected = elaborate(plan, programs)
    if candidate.plan_id != expected.plan_id:
        raise _fail(
            OutcomeClass.KIND_MISMATCH,
            "checking:identity",
            "VDQP-CHECK-001",
            "candidate plan identity does not match",
        )
    if candidate.target_core_id != expected.target_core_id:
        raise _fail(
            OutcomeClass.KIND_MISMATCH,
            "checking:target-core",
            "VDQP-CHECK-002",
            "candidate target Core identity does not match",
        )
    forbidden = {"PublishDerivedOracle", "AbsorbDerivedDeclaration", "RuntimeEmit"}
    if any(event.kind in forbidden for event in candidate.events):
        raise _fail(
            OutcomeClass.REFUSED,
            "checking:authority",
            "VDQP-CHECK-005",
            "the flattened Core contains an invented derived-word event",
        )
    if candidate.events != expected.events:
        raise _fail(
            OutcomeClass.REFUSED,
            "checking:event-map",
            "VDQP-CHECK-003",
            "candidate static event sequence is incomplete or altered",
        )
    if candidate.logical_to_source_events != expected.logical_to_source_events:
        raise _fail(
            OutcomeClass.REFUSED,
            "checking:logical-map",
            "VDQP-CHECK-004",
            "candidate logical-to-source map loses multiplicity or correlation",
        )
    return CheckedElaboration(
        candidate.plan_id, candidate.target_core_id, len(candidate.events)
    )


@dataclass
class _Budget:
    remaining: int

    def charge(self, amount: int = 1) -> None:
        if type(self.remaining) is not int or self.remaining < amount:
            raise _fail(
                OutcomeClass.NONCOMPLETION,
                "execution:budget",
                "VDQP-EXEC-015",
                "independent evaluator work limit exhausted",
            )
        self.remaining -= amount


def freeze_oracles(
    oracles: Mapping[str, Mapping[int, int]]
) -> Mapping[str, Mapping[int, int]]:
    frozen: dict[str, Mapping[int, int]] = {}
    for name, values in oracles.items():
        if type(name) is not str or not name or not isinstance(values, Mapping):
            raise _fail(
                OutcomeClass.MALFORMED,
                "execution:oracles",
                "VDQP-EXEC-016",
                "oracle catalog is malformed",
            )
        snapshot: dict[int, int] = {}
        for index, value in values.items():
            if type(index) is not int or type(value) is not int or index in snapshot:
                raise _fail(
                    OutcomeClass.MALFORMED,
                    "execution:oracles",
                    "VDQP-EXEC-017",
                    "oracle entries must be unique integer pairs",
                )
            snapshot[index] = value
        frozen[name] = MappingProxyType(snapshot)
    return MappingProxyType(frozen)


def _resolve_runtime(ref: str, environment: Mapping[str, Any]) -> Any:
    try:
        return environment[ref]
    except KeyError as error:
        raise _fail(
            OutcomeClass.MISSING_DEPENDENCY,
            "execution:local-reference",
            "VDQP-EXEC-018",
            f"missing runtime value {ref!r}",
        ) from error


def _execute_program(
    *,
    program_name: str,
    programs: Mapping[str, DerivedWordProgram],
    index: int,
    arguments: Mapping[str, Any],
    oracle_bindings: Mapping[str, str],
    oracles: Mapping[str, Mapping[int, int]],
    budget: _Budget,
    path: tuple[str, ...],
) -> ExecutionResult:
    program = programs[program_name]
    environment: dict[str, Any] = {"index": index, **arguments}
    budget.charge()
    tag = _route(
        program.route_algorithm,
        tuple(_resolve_runtime(ref, environment) for ref in program.route_inputs),
    )
    case = next(case for case in program.cases if case.tag == tag)
    queries: list[QueryTrace] = []
    case_path = path + (case.tag,)
    for step in case.steps:
        step_path = case_path + (step.name,)
        if isinstance(step, PureStep):
            budget.charge()
            environment[step.name] = _pure(
                step.algorithm,
                tuple(_resolve_runtime(ref, environment) for ref in step.inputs),
                program.modulus,
            )
        elif isinstance(step, ReadStep):
            budget.charge(2)
            source_name = oracle_bindings[step.source_port]
            source = oracles.get(source_name)
            if source is None:
                raise _fail(
                    OutcomeClass.MISSING_DEPENDENCY,
                    "execution:read",
                    "VDQP-EXEC-019",
                    f"missing source oracle {source_name!r}",
                )
            query_index = _resolve_runtime(step.index, environment)
            if type(query_index) is not int:
                raise _fail(
                    OutcomeClass.KIND_MISMATCH,
                    "execution:read",
                    "VDQP-EXEC-020",
                    "source query index is not an integer",
                )
            if query_index not in source:
                raise _fail(
                    OutcomeClass.SEMANTIC_FAILURE,
                    "execution:read",
                    "VDQP-EXEC-021",
                    "source query is outside the admitted finite oracle",
                )
            port = next(port for port in program.oracle_ports if port.name == step.source_port)
            queries.append(
                QueryTrace(step_path, source_name, query_index, port.visibility)
            )
            environment[step.name] = source[query_index] % program.modulus
        else:
            budget.charge()
            child_arguments_map = _pairs_to_map(step.arguments, "runtime call arguments")
            child_oracle_map = _pairs_to_map(
                step.oracle_bindings, "runtime call oracle bindings"
            )
            child = _execute_program(
                program_name=step.program,
                programs=programs,
                index=_resolve_runtime(step.index, environment),
                arguments={
                    key: _resolve_runtime(value, environment)
                    for key, value in child_arguments_map.items()
                },
                oracle_bindings={
                    key: oracle_bindings[value]
                    for key, value in child_oracle_map.items()
                },
                oracles=oracles,
                budget=budget,
                path=step_path,
            )
            queries.extend(child.queries)
            if child.terminal is not None:
                return ExecutionResult(None, child.terminal, tuple(queries))
            environment[step.name] = child.value
    if case.terminal is not None:
        return ExecutionResult(None, case.terminal, tuple(queries))
    return ExecutionResult(
        _resolve_runtime(case.result or "", environment), None, tuple(queries)
    )


def execute_site(
    *,
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    site_name: str,
    inputs: Mapping[str, Any],
    oracles: Mapping[str, Mapping[int, int]],
    work_limit: int = 10_000,
) -> ExecutionResult:
    programs = validate_programs(programs)
    plan = validate_plan(plan, programs)
    if type(work_limit) is not int or work_limit < 0:
        raise _fail(
            OutcomeClass.MALFORMED,
            "execution:budget",
            "VDQP-EXEC-022",
            "work limit must be a nonnegative integer",
        )
    if frozenset(inputs) != frozenset(plan.inputs):
        raise _fail(
            OutcomeClass.MISSING_DEPENDENCY,
            "execution:inputs",
            "VDQP-EXEC-023",
            "runtime plan inputs are not exact",
        )
    site = next((site for site in plan.sites if site.name == site_name), None)
    if site is None:
        raise _fail(
            OutcomeClass.MISSING_DEPENDENCY,
            "execution:site",
            "VDQP-EXEC-024",
            f"unknown logical site {site_name!r}",
        )
    arguments = {
        key: inputs[value]
        for key, value in _pairs_to_map(site.arguments, "site arguments").items()
    }
    oracle_bindings = dict(_pairs_to_map(site.oracle_bindings, "site oracles"))
    return _execute_program(
        program_name=site.program,
        programs=programs,
        index=inputs[site.index_input],
        arguments=arguments,
        oracle_bindings=oracle_bindings,
        oracles=oracles,
        budget=_Budget(work_limit),
        path=(site.name,),
    )


def representative_programs() -> Mapping[str, DerivedWordProgram]:
    programs = {
        "circle-batched-word": DerivedWordProgram(
            name="circle-batched-word",
            modulus=17,
            arguments=("coefficient",),
            oracle_ports=(OraclePort("first"), OraclePort("second"), OraclePort("third")),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                ProgramCase(
                    "only",
                    (
                        ReadStep("first-value", "first", "index"),
                        ReadStep("second-value", "second", "index"),
                        ReadStep("third-value", "third", "index"),
                        PureStep(
                            "combined",
                            "weighted-sum-three",
                            ("first-value", "second-value", "third-value", "coefficient"),
                        ),
                    ),
                    result="combined",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=3,
        ),
        "four-point-folded-word": DerivedWordProgram(
            name="four-point-folded-word",
            modulus=17,
            arguments=("alpha0", "alpha1", "one", "two", "three"),
            oracle_ports=(OraclePort("source"),),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                ProgramCase(
                    "only",
                    (
                        PureStep("index-one", "field-add", ("index", "one")),
                        PureStep("index-two", "field-add", ("index", "two")),
                        PureStep("index-three", "field-add", ("index", "three")),
                        ReadStep("value-zero", "source", "index"),
                        ReadStep("value-one", "source", "index-one"),
                        ReadStep("value-two", "source", "index-two"),
                        ReadStep("value-three", "source", "index-three"),
                        PureStep(
                            "folded",
                            "four-point-multilinear-fold",
                            (
                                "value-zero",
                                "value-one",
                                "value-two",
                                "value-three",
                                "alpha0",
                                "alpha1",
                            ),
                        ),
                    ),
                    result="folded",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=4,
        ),
        "multipoint-quotient-word": DerivedWordProgram(
            name="multipoint-quotient-word",
            modulus=17,
            arguments=("answers", "points"),
            oracle_ports=(OraclePort("source"),),
            route_algorithm="collision-membership",
            route_inputs=("index", "points"),
            cases=(
                ProgramCase("collision", (), terminal="UndefinedQuotient"),
                ProgramCase(
                    "regular",
                    (
                        ReadStep("source-value", "source", "index"),
                        PureStep(
                            "quotient",
                            "lagrange-quotient",
                            ("source-value", "index", "points", "answers"),
                        ),
                    ),
                    result="quotient",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
        "stir-quotient-word": DerivedWordProgram(
            name="stir-quotient-word",
            modulus=17,
            arguments=("answers", "points"),
            oracle_ports=(OraclePort("fill"), OraclePort("source")),
            route_algorithm="set-membership",
            route_inputs=("index", "points"),
            cases=(
                ProgramCase(
                    "member",
                    (ReadStep("fill-value", "fill", "index"),),
                    result="fill-value",
                ),
                ProgramCase(
                    "outside",
                    (
                        ReadStep("source-value", "source", "index"),
                        PureStep(
                            "quotient",
                            "lagrange-quotient",
                            ("source-value", "index", "points", "answers"),
                        ),
                    ),
                    result="quotient",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
        "stir-folded-word": DerivedWordProgram(
            name="stir-folded-word",
            modulus=17,
            arguments=("answers", "challenge", "points"),
            oracle_ports=(OraclePort("fill"), OraclePort("source")),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                ProgramCase(
                    "only",
                    (
                        PureStep("negative-index", "field-negate", ("index",)),
                        CallStep(
                            "positive-quotient",
                            "stir-quotient-word",
                            "index",
                            (("answers", "answers"), ("points", "points")),
                            (("fill", "fill"), ("source", "source")),
                        ),
                        CallStep(
                            "negative-quotient",
                            "stir-quotient-word",
                            "negative-index",
                            (("answers", "answers"), ("points", "points")),
                            (("fill", "fill"), ("source", "source")),
                        ),
                        PureStep(
                            "folded",
                            "binary-fold",
                            (
                                "positive-quotient",
                                "negative-quotient",
                                "index",
                                "challenge",
                            ),
                        ),
                    ),
                    result="folded",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            maximum_elaboration_depth=2,
            maximum_leaf_reads=2,
        ),
    }
    return validate_programs(programs)


def representative_plan() -> QueryPlan:
    inputs = (
        "circle-coefficient",
        "circle-index",
        "deep-answers-first",
        "deep-answers-second",
        "deep-index",
        "deep-points-first",
        "deep-points-second",
        "offset-one",
        "offset-three",
        "offset-two",
        "stir-answers",
        "stir-challenge",
        "stir-index",
        "stir-points",
        "whir-alpha-zero",
        "whir-alpha-one",
        "whir-index",
    )
    plan = QueryPlan(
        name="representative-verifier-derived-reads",
        inputs=inputs,
        source_oracles=(
            "circle-first",
            "circle-second",
            "circle-third",
            "deep-first",
            "deep-second",
            "stir-fill",
            "stir-source",
            "whir-source",
        ),
        sites=(
            PlanSite(
                "circle-batch",
                "circle-batched-word",
                "circle-index",
                (("coefficient", "circle-coefficient"),),
                (
                    ("first", "circle-first"),
                    ("second", "circle-second"),
                    ("third", "circle-third"),
                ),
            ),
            PlanSite(
                "deep-first-quotient",
                "multipoint-quotient-word",
                "deep-index",
                (
                    ("answers", "deep-answers-first"),
                    ("points", "deep-points-first"),
                ),
                (("source", "deep-first"),),
            ),
            PlanSite(
                "deep-second-quotient",
                "multipoint-quotient-word",
                "deep-index",
                (
                    ("answers", "deep-answers-second"),
                    ("points", "deep-points-second"),
                ),
                (("source", "deep-second"),),
            ),
            PlanSite(
                "stir-fold",
                "stir-folded-word",
                "stir-index",
                (
                    ("answers", "stir-answers"),
                    ("challenge", "stir-challenge"),
                    ("points", "stir-points"),
                ),
                (("fill", "stir-fill"), ("source", "stir-source")),
            ),
            PlanSite(
                "whir-grouped-fold",
                "four-point-folded-word",
                "whir-index",
                (
                    ("alpha0", "whir-alpha-zero"),
                    ("alpha1", "whir-alpha-one"),
                    ("one", "offset-one"),
                    ("three", "offset-three"),
                    ("two", "offset-two"),
                ),
                (("source", "whir-source"),),
            ),
        ),
    )
    return validate_plan(plan, representative_programs())
