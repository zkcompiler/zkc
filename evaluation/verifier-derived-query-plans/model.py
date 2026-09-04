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
    UNSUPPORTED = "Unsupported"
    MISSING_DEPENDENCY = "MissingDependency"
    CANNOT_ANSWER = "CannotAnswer"
    KIND_MISMATCH = "KindMismatch"
    MALFORMED = "Malformed"
    REFUSED = "Refused"
    DETERMINISTIC_LIMIT_EXCEEDED = "DeterministicLimitExceeded"
    CHECKER_FAILURE = "CheckerFailure"


class PlanError(Exception):
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


class AlgebraProfile(str, Enum):
    PRIME_FIELD = "PrimeFieldV0"


class PlanValueRefKind(str, Enum):
    PLAN_INPUT = "PlanInput"
    PRIOR_LOGICAL_RESULT = "PriorLogicalResult"


@dataclass(frozen=True)
class PlanValueRef:
    kind: PlanValueRefKind
    name: str


def plan_input(name: str) -> PlanValueRef:
    return PlanValueRef(PlanValueRefKind.PLAN_INPUT, name)


def prior_logical_result(name: str) -> PlanValueRef:
    return PlanValueRef(PlanValueRefKind.PRIOR_LOGICAL_RESULT, name)


@dataclass(frozen=True)
class PlanInput:
    name: str
    visibility: Visibility = Visibility.PUBLIC
    is_boolean: bool = False


@dataclass(frozen=True)
class PlanOracle:
    name: str
    visibility: Visibility = Visibility.PUBLIC


@dataclass(frozen=True)
class LogicalActivation:
    condition: PlanValueRef | None = None


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
    algebra_profile: AlgebraProfile
    arguments: tuple[str, ...]
    oracle_ports: tuple[OraclePort, ...]
    route_algorithm: str
    route_inputs: tuple[str, ...]
    cases: tuple[ProgramCase, ...]
    output_visibility: Visibility
    output_is_boolean: bool
    maximum_elaboration_depth: int
    maximum_leaf_reads: int


@dataclass(frozen=True)
class PlanSite:
    name: str
    program: str
    activation: LogicalActivation
    requested_index: PlanValueRef
    arguments: tuple[tuple[str, PlanValueRef], ...]
    oracle_bindings: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class QueryPlan:
    name: str
    inputs: tuple[PlanInput, ...]
    source_oracles: tuple[PlanOracle, ...]
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
    active: bool = True


@dataclass(frozen=True)
class Elaboration:
    plan_id: str
    target_core_id: str
    events: tuple[StaticEvent, ...]
    occurrence_map: tuple[tuple[tuple[str, ...], int], ...]
    logical_to_source_events: tuple[tuple[str, tuple[int, ...]], ...]


@dataclass(frozen=True)
class CheckedElaboration:
    plan_id: str
    target_core_id: str
    event_count: int


@dataclass(frozen=True)
class AdmittedFlatCore:
    core_id: str
    events: tuple[StaticEvent, ...]


@dataclass(frozen=True)
class ProgramEffectSummary:
    control_parameters: frozenset[str]
    result_parameters: frozenset[str]
    result_oracle_ports: frozenset[str]
    may_reach_terminal: bool


_ROUTE_CASES: Mapping[str, tuple[str, ...]] = MappingProxyType(
    {
        "always": ("only",),
        "collision-membership": ("collision", "regular"),
        "quotient-domain": ("collision", "invalid", "regular"),
        "set-membership": ("member", "outside"),
        "stir-quotient-domain": ("invalid", "member", "outside"),
        "zero-vs-nonzero": ("nonzero", "zero"),
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


def _value_bindings_to_map(
    pairs: Sequence[tuple[str, PlanValueRef]], label: str
) -> Mapping[str, PlanValueRef]:
    result: dict[str, PlanValueRef] = {}
    for key, value in pairs:
        if type(key) is not str or not key or type(value) is not PlanValueRef:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:bindings",
                "VDQP-FORM-036",
                f"{label} contains an invalid binding",
            )
        if key in result:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:bindings",
                "VDQP-FORM-037",
                f"{label} repeats {key!r}",
            )
        result[key] = value
    return MappingProxyType(result)


def _is_prime(value: int) -> bool:
    if type(value) is not int or value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def _route(
    algorithm: str, values: Sequence[Any], modulus: int
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
        residues = tuple(item % modulus for item in points)
        member = values[0] % modulus in residues
        if algorithm == "collision-membership":
            return "collision" if member else "regular"
        return "member" if member else "outside"
    if algorithm in ("quotient-domain", "stir-quotient-domain"):
        if len(values) != 3 or type(values[0]) is not int:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-002",
                "quotient routing expects an index, points, and answers",
            )
        points, answers = values[1], values[2]
        if (
            not isinstance(points, tuple)
            or not isinstance(answers, tuple)
            or any(type(item) is not int for item in points + answers)
        ):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-003",
                "quotient points and answers must be immutable integer sequences",
            )
        residues = tuple(item % modulus for item in points)
        if (
            not residues
            or len(residues) != len(set(residues))
            or len(answers) != len(points)
        ):
            return "invalid"
        member = values[0] % modulus in residues
        if algorithm == "quotient-domain":
            return "collision" if member else "regular"
        return "member" if member else "outside"
    if algorithm == "zero-vs-nonzero":
        if len(values) != 1 or type(values[0]) is not int:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:route",
                "VDQP-EXEC-025",
                "zero routing expects one integer",
            )
        return "zero" if values[0] % modulus == 0 else "nonzero"
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
            OutcomeClass.CHECKER_FAILURE,
            "execution:field",
            "VDQP-EXEC-005",
            "a supposedly total field operation reached a zero denominator",
        )
    try:
        return pow(value, -1, modulus)
    except ValueError as error:
        raise _fail(
            OutcomeClass.CHECKER_FAILURE,
            "execution:field",
            "VDQP-EXEC-026",
            "the selected algebra provider could not invert a nonzero value",
        ) from error


def _lagrange_value(
    x: int, points: tuple[int, ...], answers: tuple[int, ...], modulus: int
) -> int:
    if not points or len(points) != len(answers) or len(points) != len(set(points)):
        raise _fail(
            OutcomeClass.CHECKER_FAILURE,
            "execution:interpolation",
            "VDQP-EXEC-006",
            "a routed interpolation operation received an invalid point domain",
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
        "algebra_profile": program.algebra_profile.value,
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
        "output_is_boolean": program.output_is_boolean,
        "maximum_elaboration_depth": program.maximum_elaboration_depth,
        "maximum_leaf_reads": program.maximum_leaf_reads,
    }


def program_id(program: DerivedWordProgram) -> str:
    return hashlib.sha256(
        b"zkc.pir.verifier-derived-word-program\x00"
        + _canonical_bytes(program_body(program))
    ).hexdigest()


def _plan_value_ref_body(reference: PlanValueRef) -> dict[str, str]:
    return {"kind": reference.kind.value, "name": reference.name}


def plan_body(plan: QueryPlan, programs: Mapping[str, DerivedWordProgram]) -> dict[str, Any]:
    return {
        "name": plan.name,
        "inputs": [
            {
                "name": item.name,
                "visibility": item.visibility.value,
                "is_boolean": item.is_boolean,
            }
            for item in plan.inputs
        ],
        "source_oracles": [
            {"name": item.name, "visibility": item.visibility.value}
            for item in plan.source_oracles
        ],
        "sites": [
            {
                "name": site.name,
                "program_id": program_id(programs[site.program]),
                "activation": (
                    None
                    if site.activation.condition is None
                    else _plan_value_ref_body(site.activation.condition)
                ),
                "requested_index": _plan_value_ref_body(site.requested_index),
                "arguments": {
                    key: _plan_value_ref_body(value) for key, value in site.arguments
                },
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
    if not case_metrics:
        return (1, 0)
    return (
        max(item[0] for item in case_metrics),
        max(item[1] for item in case_metrics),
    )


@dataclass(frozen=True)
class _Flow:
    parameters: frozenset[str] = frozenset()
    oracle_ports: frozenset[str] = frozenset()
    answer_tainted: bool = False


def _join_flows(values: Sequence[_Flow]) -> _Flow:
    return _Flow(
        frozenset().union(*(item.parameters for item in values)),
        frozenset().union(*(item.oracle_ports for item in values)),
        any(item.answer_tainted for item in values),
    )


def _program_effect_summary(
    name: str,
    programs: Mapping[str, DerivedWordProgram],
    cache: dict[str, ProgramEffectSummary],
    visiting: tuple[str, ...] = (),
) -> ProgramEffectSummary:
    cached = cache.get(name)
    if cached is not None:
        return cached
    if name in visiting:
        raise _fail(
            OutcomeClass.REFUSED,
            "formation:program-graph",
            "VDQP-FORM-038",
            "derived-word effect graph is cyclic",
        )
    program = programs[name]
    control_parameters: set[str] = set()
    result_parameters: set[str] = set()
    result_oracles: set[str] = set()
    may_reach_terminal = False
    initial = {
        "index": _Flow(),
        **{
            argument: _Flow(parameters=frozenset((argument,)))
            for argument in program.arguments
        },
    }
    for ref in program.route_inputs:
        control_parameters.update(initial[ref].parameters)
    for case in program.cases:
        environment = dict(initial)
        if case.terminal is not None:
            may_reach_terminal = True
        for step in case.steps:
            if isinstance(step, PureStep):
                flow = _join_flows(tuple(environment[ref] for ref in step.inputs))
            elif isinstance(step, ReadStep):
                index_flow = environment[step.index]
                if index_flow.answer_tainted:
                    raise _fail(
                        OutcomeClass.REFUSED,
                        "formation:read",
                        "VDQP-FORM-020",
                        "source-query routing may not depend on a source answer",
                    )
                control_parameters.update(index_flow.parameters)
                flow = _Flow(
                    index_flow.parameters,
                    index_flow.oracle_ports | frozenset((step.source_port,)),
                    True,
                )
            else:
                child = _program_effect_summary(
                    step.program, programs, cache, visiting + (name,)
                )
                arguments = _pairs_to_map(step.arguments, "effect call arguments")
                oracles = _pairs_to_map(step.oracle_bindings, "effect call oracles")
                index_flow = environment[step.index]
                if index_flow.answer_tainted:
                    raise _fail(
                        OutcomeClass.REFUSED,
                        "formation:call",
                        "VDQP-FORM-025",
                        "nested requested-index control may not depend on a source answer",
                    )
                control_parameters.update(index_flow.parameters)
                for child_parameter in child.control_parameters:
                    bound_flow = environment[arguments[child_parameter]]
                    if bound_flow.answer_tainted:
                        raise _fail(
                            OutcomeClass.REFUSED,
                            "formation:call",
                            "VDQP-FORM-039",
                            "a nested control-relevant argument depends on a source answer",
                        )
                    control_parameters.update(bound_flow.parameters)
                result_flows = tuple(
                    environment[arguments[child_parameter]]
                    for child_parameter in child.result_parameters
                )
                argument_flow = _join_flows(result_flows)
                mapped_oracles = frozenset(
                    oracles[child_port] for child_port in child.result_oracle_ports
                )
                flow = _Flow(
                    argument_flow.parameters,
                    argument_flow.oracle_ports | mapped_oracles,
                    argument_flow.answer_tainted or bool(mapped_oracles),
                )
                may_reach_terminal = may_reach_terminal or child.may_reach_terminal
            environment[step.name] = flow
        if case.result is not None:
            result = environment[case.result]
            result_parameters.update(result.parameters)
            result_oracles.update(result.oracle_ports)
    summary = ProgramEffectSummary(
        frozenset(control_parameters),
        frozenset(result_parameters),
        frozenset(result_oracles),
        may_reach_terminal,
    )
    cache[name] = summary
    return summary


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
        if type(program.algebra_profile) is not AlgebraProfile:
            raise _fail(
                OutcomeClass.UNSUPPORTED,
                "formation:algebra",
                "VDQP-FORM-040",
                "the algebra profile has no selected interpretation",
            )
        if type(program.modulus) is not int or program.modulus <= 2:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:programs",
                "VDQP-FORM-009",
                "program modulus must be an integer greater than two",
            )
        if (
            program.algebra_profile is AlgebraProfile.PRIME_FIELD
            and not _is_prime(program.modulus)
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:algebra",
                "VDQP-FORM-041",
                "PrimeFieldV0 requires an exact prime modulus",
            )
        if type(program.output_is_boolean) is not bool:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:programs",
                "VDQP-FORM-042",
                "program output boolean metadata is malformed",
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
        for case in program.cases:
            if (case.result is None) == (case.terminal is None):
                raise _fail(
                    OutcomeClass.MALFORMED,
                    "formation:cases",
                    "VDQP-FORM-015",
                    "each case must return a result or reach one explicit terminal",
                )
            available = set(initial_refs)
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
                    if any(source not in ports for source in oracle_map.values()):
                        raise _fail(
                            OutcomeClass.MISSING_DEPENDENCY,
                            "formation:call",
                            "VDQP-FORM-026",
                            "call maps to an absent parent source port",
                        )
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
    effect_cache: dict[str, ProgramEffectSummary] = {}
    for name, program in frozen.items():
        summary = _program_effect_summary(name, frozen, effect_cache)
        port_visibility = {port.name: port.visibility for port in program.oracle_ports}
        if program.output_visibility is Visibility.PUBLIC and any(
            port_visibility[port] is Visibility.VERIFIER_ONLY
            for port in summary.result_oracle_ports
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:visibility",
                "VDQP-FORM-014",
                "a public result transitively depends on a verifier-only source",
            )
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
    input_names = _strict_names(tuple(item.name for item in plan.inputs), "plan inputs")
    oracle_names = _strict_names(
        tuple(item.name for item in plan.source_oracles), "plan source oracles"
    )
    if input_names != tuple(sorted(input_names)) or oracle_names != tuple(
        sorted(oracle_names)
    ):
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:plan",
            "VDQP-FORM-043",
            "plan input and Oracle declarations must be in canonical name order",
        )
    if any(
        type(item) is not PlanInput
        or type(item.visibility) is not Visibility
        or type(item.is_boolean) is not bool
        for item in plan.inputs
    ) or any(
        type(item) is not PlanOracle or type(item.visibility) is not Visibility
        for item in plan.source_oracles
    ):
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:plan",
            "VDQP-FORM-044",
            "plan declarations are malformed",
        )
    site_names = _strict_names(tuple(site.name for site in plan.sites), "plan sites")
    if not site_names:
        raise _fail(
            OutcomeClass.MALFORMED,
            "formation:plan",
            "VDQP-FORM-029",
            "a query plan must contain at least one logical use",
        )
    inputs_by_name = {item.name: item for item in plan.inputs}
    oracles_by_name = {item.name: item for item in plan.source_oracles}
    effect_cache: dict[str, ProgramEffectSummary] = {}
    summaries = {
        name: _program_effect_summary(name, programs, effect_cache)
        for name in programs
    }
    prior: dict[
        str,
        tuple[
            PlanSite,
            DerivedWordProgram,
            ProgramEffectSummary,
            Mapping[str, tuple[Visibility, bool, bool]],
        ],
    ] = {}

    def resolve(reference: PlanValueRef) -> tuple[Visibility, bool, bool]:
        if (
            type(reference) is not PlanValueRef
            or type(reference.name) is not str
            or not reference.name
        ):
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:plan-reference",
                "VDQP-FORM-045",
                "a plan value reference is malformed",
            )
        if reference.kind is PlanValueRefKind.PLAN_INPUT:
            declaration = inputs_by_name.get(reference.name)
            if declaration is None:
                raise _fail(
                    OutcomeClass.MISSING_DEPENDENCY,
                    "formation:plan-reference",
                    "VDQP-FORM-046",
                    "a plan value reference names an absent input",
                )
            return declaration.visibility, declaration.is_boolean, False
        if reference.kind is not PlanValueRefKind.PRIOR_LOGICAL_RESULT:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:plan-reference",
                "VDQP-FORM-047",
                "a plan value reference has an unknown constructor",
            )
        resolved = prior.get(reference.name)
        if resolved is None and reference.name in site_names:
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:plan-reference",
                "VDQP-FORM-057",
                "a plan value reference points to a causally future logical use",
            )
        if resolved is None:
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan-reference",
                "VDQP-FORM-048",
                "a prior logical result is absent or not causally earlier",
            )
        producer_site, producer, summary, producer_arguments = resolved
        return_case_count = sum(
            case.result is not None for case in producer.cases
        )
        if (
            producer_site.activation.condition is not None
            or summary.may_reach_terminal
            or return_case_count != 1
        ):
            raise _fail(
                OutcomeClass.UNSUPPORTED,
                "formation:plan-reference",
                "VDQP-FORM-049",
                "this bounded profile exposes a prior result only from one "
                "unconditional total-return branch",
            )
        return (
            producer.output_visibility,
            producer.output_is_boolean,
            bool(summary.result_oracle_ports)
            or any(
                producer_arguments[name][2]
                for name in summary.result_parameters
            ),
        )

    for site in plan.sites:
        if type(site.activation) is not LogicalActivation:
            raise _fail(
                OutcomeClass.MALFORMED,
                "formation:activation",
                "VDQP-FORM-050",
                "logical-use activation is malformed",
            )
        program = programs.get(site.program)
        if program is None:
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-030",
                "plan site names an absent program",
            )
        summary = summaries[program.name]
        if site.activation.condition is not None:
            activation_visibility, activation_boolean, activation_tainted = resolve(
                site.activation.condition
            )
            if not activation_boolean:
                raise _fail(
                    OutcomeClass.KIND_MISMATCH,
                    "formation:activation",
                    "VDQP-FORM-051",
                    "logical-use activation is not a Boolean value",
                )
            if activation_visibility is not Visibility.PUBLIC:
                raise _fail(
                    OutcomeClass.REFUSED,
                    "formation:activation",
                    "VDQP-FORM-052",
                    "logical-use activation must be public",
                )
            if activation_tainted:
                raise _fail(
                    OutcomeClass.REFUSED,
                    "formation:activation",
                    "VDQP-FORM-053",
                    "logical-use activation may not depend on a source answer",
                )
        _, _, index_tainted = resolve(site.requested_index)
        if index_tainted:
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:plan-reference",
                "VDQP-FORM-031",
                "logical requested-index control may not depend on a source answer",
            )
        arguments = _value_bindings_to_map(site.arguments, "site arguments")
        oracles = _pairs_to_map(site.oracle_bindings, "site oracle bindings")
        if frozenset(arguments) != frozenset(program.arguments):
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "formation:plan",
                "VDQP-FORM-032",
                "site argument bindings are not total",
            )
        argument_properties = {
            name: resolve(reference) for name, reference in arguments.items()
        }
        if any(
            argument_properties[name][2] for name in summary.control_parameters
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "formation:plan-reference",
                "VDQP-FORM-054",
                "a control-relevant logical argument depends on a source answer",
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
        if any(source not in oracles_by_name for source in oracles.values()):
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "formation:plan",
                "VDQP-FORM-035",
                "site maps to an absent plan source oracle",
            )
        port_visibility = {port.name: port.visibility for port in program.oracle_ports}
        for port_name, source_name in oracles.items():
            if port_visibility[port_name] is not oracles_by_name[source_name].visibility:
                raise _fail(
                    OutcomeClass.KIND_MISMATCH,
                    "formation:visibility",
                    "VDQP-FORM-055",
                    "a source Oracle binding changes declared visibility",
                )
        if program.output_visibility is Visibility.PUBLIC:
            if any(
                argument_properties[name][0] is Visibility.VERIFIER_ONLY
                for name in summary.result_parameters
            ) or any(
                oracles_by_name[oracles[name]].visibility is Visibility.VERIFIER_ONLY
                for name in summary.result_oracle_ports
            ):
                raise _fail(
                    OutcomeClass.REFUSED,
                    "formation:visibility",
                    "VDQP-FORM-056",
                    "a public logical result transitively declassifies a verifier-only value",
                )
        prior[site.name] = (
            site,
            program,
            summary,
            MappingProxyType(argument_properties),
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


def _symbolic_plan_ref(
    reference: PlanValueRef,
    prior_symbols: Mapping[str, str],
) -> str:
    if reference.kind is PlanValueRefKind.PLAN_INPUT:
        return f"plan-input:{reference.name}"
    if reference.kind is PlanValueRefKind.PRIOR_LOGICAL_RESULT:
        try:
            return prior_symbols[reference.name]
        except KeyError as error:
            raise _fail(
                OutcomeClass.MISSING_DEPENDENCY,
                "elaboration:plan-reference",
                "VDQP-ELAB-003",
                "a prior logical result has no causally earlier static value",
            ) from error
    raise _fail(
        OutcomeClass.MALFORMED,
        "elaboration:plan-reference",
        "VDQP-ELAB-002",
        "plan value reference has an unknown constructor",
    )


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


def derive_static_template(
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    *,
    maximum_static_events: int = 10_000,
) -> tuple[tuple[StaticEvent, ...], tuple[tuple[str, tuple[int, ...]], ...]]:
    if type(maximum_static_events) is not int or maximum_static_events < 0:
        raise _fail(
            OutcomeClass.MALFORMED,
            "elaboration:budget",
            "VDQP-ELAB-006",
            "the static elaboration limit must be a nonnegative integer",
        )
    programs = validate_programs(programs)
    plan = validate_plan(plan, programs)
    effect_cache: dict[str, ProgramEffectSummary] = {}
    all_events: list[StaticEvent] = []
    logical_map: list[tuple[str, tuple[int, ...]]] = []
    prior_symbols: dict[str, str] = {}
    for site in plan.sites:
        program = programs[site.program]
        arguments = {
            key: _symbolic_plan_ref(value, prior_symbols)
            for key, value in _value_bindings_to_map(
                site.arguments, "site arguments"
            ).items()
        }
        oracles = dict(_pairs_to_map(site.oracle_bindings, "site oracles"))
        activation_guard = (
            ()
            if site.activation.condition is None
            else (
                "activation:"
                f"{_symbolic_plan_ref(site.activation.condition, prior_symbols)}",
            )
        )
        start = len(all_events)
        site_events = _static_program_events(
            program_name=program.name,
            programs=programs,
            path=(site.name,),
            guard_path=activation_guard,
            index_symbol=_symbolic_plan_ref(
                site.requested_index,
                prior_symbols,
            ),
            arguments=arguments,
            oracle_bindings=oracles,
        )
        summary = _program_effect_summary(
            program.name, programs, effect_cache
        )
        if not summary.may_reach_terminal:
            return_symbols = tuple(
                dict(event.details)["value"]
                for event in site_events
                if event.kind == "ReturnDerivedValue"
            )
            if len(return_symbols) == 1 and not activation_guard:
                prior_symbols[site.name] = return_symbols[0]
        all_events.extend(site_events)
        if len(all_events) > maximum_static_events:
            raise _fail(
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                "elaboration:budget",
                "VDQP-ELAB-007",
                "the external static elaboration limit was exhausted",
            )
        source_ordinals = tuple(
            start + ordinal
            for ordinal, event in enumerate(site_events)
            if event.kind == "QueryOracle"
        )
        logical_map.append((site.name, source_ordinals))
    return tuple(all_events), tuple(logical_map)


_ALLOWED_FLAT_CORE_EVENTS = frozenset(
    {
        "AnswerOracle",
        "BindNestedResult",
        "DerivedValue",
        "QueryOracle",
        "ReachSemanticTerminal",
        "ReturnDerivedValue",
        "Route",
    }
)


def admit_flat_core(events: tuple[StaticEvent, ...]) -> AdmittedFlatCore:
    if type(events) is not tuple or not events:
        raise _fail(
            OutcomeClass.MALFORMED,
            "core-admission:carrier",
            "VDQP-CORE-001",
            "flat Core events must be one nonempty immutable sequence",
        )
    seen_paths: set[tuple[str, ...]] = set()
    query_paths: set[str] = set()
    route_paths: set[tuple[str, ...]] = set()
    return_paths: set[tuple[str, ...]] = set()
    available_values: set[str] = set()
    stopped_paths: set[tuple[str, ...]] = set()
    for event in events:
        if type(event) is not StaticEvent or event.kind not in _ALLOWED_FLAT_CORE_EVENTS:
            raise _fail(
                OutcomeClass.REFUSED,
                "core-admission:event",
                "VDQP-CORE-002",
                "flat Core contains an unsupported or invented event",
            )
        if (
            type(event.path) is not tuple
            or not event.path
            or any(type(item) is not str or not item for item in event.path)
            or event.path in seen_paths
        ):
            raise _fail(
                OutcomeClass.MALFORMED,
                "core-admission:path",
                "VDQP-CORE-003",
                "flat Core event paths are malformed or repeated",
            )
        if type(event.guard_path) is not tuple or any(
            type(item) is not str or not item for item in event.guard_path
        ):
            raise _fail(
                OutcomeClass.MALFORMED,
                "core-admission:guard",
                "VDQP-CORE-004",
                "flat Core guard path is malformed",
            )
        detail_keys = tuple(key for key, _ in event.details)
        if len(detail_keys) != len(set(detail_keys)):
            raise _fail(
                OutcomeClass.MALFORMED,
                "core-admission:details",
                "VDQP-CORE-005",
                "flat Core event details repeat a field",
            )
        details = dict(event.details)
        value_references: tuple[object, ...] = ()
        if event.kind in {"DerivedValue", "Route"}:
            inputs = details.get("inputs")
            if type(inputs) is not tuple:
                raise _fail(
                    OutcomeClass.MALFORMED,
                    "core-admission:details",
                    "VDQP-CORE-005",
                    "flat Core value inputs are malformed",
                )
            value_references = inputs
        elif event.kind == "QueryOracle":
            value_references = (details.get("index"),)
        elif event.kind == "ReturnDerivedValue":
            value_references = (details.get("value"),)
        if any(type(item) is not str or not item for item in value_references):
            raise _fail(
                OutcomeClass.MALFORMED,
                "core-admission:details",
                "VDQP-CORE-005",
                "flat Core value references are malformed",
            )
        activation_references = tuple(
            guard.removeprefix("activation:")
            for guard in event.guard_path
            if guard.startswith("activation:")
        )
        if any(not item for item in activation_references):
            raise _fail(
                OutcomeClass.MALFORMED,
                "core-admission:guard",
                "VDQP-CORE-004",
                "flat Core activation guard is malformed",
            )
        route_guard_count = sum(
            not guard.startswith("activation:") for guard in event.guard_path
        )
        available_route_count = sum(
            len(path) < len(event.path) and event.path[: len(path)] == path
            for path in route_paths
        )
        missing_values = tuple(
            value
            for value in (*value_references, *activation_references)
            if not value.startswith("plan-input:") and value not in available_values
        )
        if (
            missing_values
            or route_guard_count > available_route_count
            or any(
                len(path) < len(event.path) and event.path[: len(path)] == path
                for path in stopped_paths
            )
        ):
            raise _fail(
                OutcomeClass.REFUSED,
                "core-admission:causality",
                "VDQP-CORE-007",
                "a flat Core event precedes one of its value, route, or guard "
                "dependencies",
            )
        seen_paths.add(event.path)
        if event.kind == "QueryOracle":
            query_paths.add("/".join(event.path))
        elif event.kind == "AnswerOracle":
            query_path = details.get("query_path")
            if type(query_path) is not str or query_path not in query_paths:
                raise _fail(
                    OutcomeClass.REFUSED,
                    "core-admission:causality",
                    "VDQP-CORE-006",
                    "an Oracle answer does not follow its exact earlier query",
                )
        elif event.kind == "BindNestedResult":
            child_path = event.path[:-1]
            if not any(
                len(child_path) < len(path)
                and path[: len(child_path)] == child_path
                for path in return_paths
            ):
                raise _fail(
                    OutcomeClass.REFUSED,
                    "core-admission:causality",
                    "VDQP-CORE-007",
                    "a nested result binding precedes every returning child branch",
                )
        if event.kind == "Route":
            route_paths.add(event.path)
        if event.kind == "ReturnDerivedValue":
            return_paths.add(event.path)
        if event.kind == "ReachSemanticTerminal":
            stopped_paths.add(event.path[:-1])
        if event.kind in {"AnswerOracle", "BindNestedResult", "DerivedValue"}:
            output = details.get("output")
            if (
                type(output) is not str
                or not output
                or output.startswith("plan-input:")
                or output in available_values
            ):
                raise _fail(
                    OutcomeClass.MALFORMED,
                    "core-admission:details",
                    "VDQP-CORE-005",
                    "flat Core output is malformed or aliased",
                )
            available_values.add(output)
    core_id = hashlib.sha256(
        b"zkc.pir.flattened-query-core\x00"
        + _canonical_bytes([event.body() for event in events])
    ).hexdigest()
    return AdmittedFlatCore(core_id, tuple(events))


def elaborate(
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    target_core: AdmittedFlatCore,
    *,
    maximum_static_events: int = 10_000,
) -> Elaboration:
    expected_events, logical_map = derive_static_template(
        plan,
        programs,
        maximum_static_events=maximum_static_events,
    )
    if type(target_core) is not AdmittedFlatCore:
        raise _fail(
            OutcomeClass.KIND_MISMATCH,
            "elaboration:target-core",
            "VDQP-ELAB-003",
            "target Core is not an admitted flat-Core handle",
        )
    readmitted = admit_flat_core(target_core.events)
    if readmitted != target_core:
        raise _fail(
            OutcomeClass.KIND_MISMATCH,
            "elaboration:target-core",
            "VDQP-ELAB-004",
            "target Core identity does not authenticate its supplied body",
        )
    expected_by_path = {event.path: event for event in expected_events}
    target_ordinals = {
        event.path: ordinal for ordinal, event in enumerate(target_core.events)
    }
    if set(target_ordinals) != set(expected_by_path) or any(
        target_core.events[target_ordinals[path]] != expected
        for path, expected in expected_by_path.items()
    ):
        raise _fail(
            OutcomeClass.REFUSED,
            "elaboration:target-core",
            "VDQP-ELAB-005",
            "the independently admitted target Core is not the complete expected image",
        )
    occurrence_map = tuple(
        (event.path, target_ordinals[event.path]) for event in expected_events
    )
    mapped_logical_queries = tuple(
        (
            site,
            tuple(
                target_ordinals[expected_events[ordinal].path]
                for ordinal in ordinals
            ),
        )
        for site, ordinals in logical_map
    )
    return Elaboration(
        plan_id=plan_id(plan, programs),
        target_core_id=target_core.core_id,
        events=target_core.events,
        occurrence_map=occurrence_map,
        logical_to_source_events=mapped_logical_queries,
    )


def check_elaboration(
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    target_core: AdmittedFlatCore,
    candidate: Elaboration,
    *,
    maximum_static_events: int = 10_000,
) -> CheckedElaboration:
    expected = elaborate(
        plan,
        programs,
        target_core,
        maximum_static_events=maximum_static_events,
    )
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
    if candidate.occurrence_map != expected.occurrence_map:
        raise _fail(
            OutcomeClass.REFUSED,
            "checking:occurrence-map",
            "VDQP-CHECK-006",
            "candidate path-to-occurrence map is incomplete, aliased, or altered",
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
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
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
        program.modulus,
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
                    OutcomeClass.CANNOT_ANSWER,
                    "execution:read",
                    "VDQP-EXEC-021",
                    "the required live source read is unavailable",
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
    prior_results: Mapping[str, int] | None = None,
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
    input_names = frozenset(item.name for item in plan.inputs)
    if frozenset(inputs) != input_names:
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

    available_prior = {} if prior_results is None else dict(prior_results)

    def resolve(reference: PlanValueRef) -> Any:
        if reference.kind is PlanValueRefKind.PLAN_INPUT:
            return inputs[reference.name]
        if reference.kind is PlanValueRefKind.PRIOR_LOGICAL_RESULT:
            if reference.name not in available_prior:
                raise _fail(
                    OutcomeClass.CANNOT_ANSWER,
                    "execution:prior-result",
                    "VDQP-EXEC-027",
                    "a required prior logical result is unavailable on this path",
                )
            return available_prior[reference.name]
        raise _fail(
            OutcomeClass.MALFORMED,
            "execution:prior-result",
            "VDQP-EXEC-028",
            "a runtime plan reference has an unknown constructor",
        )

    if site.activation.condition is not None:
        activation = resolve(site.activation.condition)
        if type(activation) is not bool:
            raise _fail(
                OutcomeClass.KIND_MISMATCH,
                "execution:activation",
                "VDQP-EXEC-029",
                "logical-use activation is not a Boolean value",
            )
        if not activation:
            return ExecutionResult(None, None, (), False)
    arguments = {
        key: resolve(value)
        for key, value in _value_bindings_to_map(
            site.arguments, "site arguments"
        ).items()
    }
    oracle_bindings = dict(_pairs_to_map(site.oracle_bindings, "site oracles"))
    return _execute_program(
        program_name=site.program,
        programs=programs,
        index=resolve(site.requested_index),
        arguments=arguments,
        oracle_bindings=oracle_bindings,
        oracles=oracles,
        budget=_Budget(work_limit),
        path=(site.name,),
    )


def execute_plan(
    *,
    plan: QueryPlan,
    programs: Mapping[str, DerivedWordProgram],
    inputs: Mapping[str, Any],
    oracles: Mapping[str, Mapping[int, int]],
    work_limit_per_site: int = 10_000,
) -> Mapping[str, ExecutionResult]:
    programs = validate_programs(programs)
    plan = validate_plan(plan, programs)
    results: dict[str, ExecutionResult] = {}
    prior_values: dict[str, int] = {}
    for site in plan.sites:
        result = execute_site(
            plan=plan,
            programs=programs,
            site_name=site.name,
            inputs=inputs,
            oracles=oracles,
            prior_results=prior_values,
            work_limit=work_limit_per_site,
        )
        results[site.name] = result
        if result.active and result.terminal is None and result.value is not None:
            prior_values[site.name] = result.value
    return MappingProxyType(results)


def representative_programs() -> Mapping[str, DerivedWordProgram]:
    programs = {
        "circle-batched-word": DerivedWordProgram(
            name="circle-batched-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
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
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=3,
        ),
        "four-point-folded-word": DerivedWordProgram(
            name="four-point-folded-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
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
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=4,
        ),
        "multipoint-quotient-word": DerivedWordProgram(
            name="multipoint-quotient-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
            arguments=("answers", "points"),
            oracle_ports=(OraclePort("source"),),
            route_algorithm="quotient-domain",
            route_inputs=("index", "points", "answers"),
            cases=(
                ProgramCase("collision", (), terminal="UndefinedQuotient"),
                ProgramCase("invalid", (), terminal="InvalidQuotientDomain"),
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
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
        "stir-quotient-word": DerivedWordProgram(
            name="stir-quotient-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
            arguments=("answers", "points"),
            oracle_ports=(OraclePort("fill"), OraclePort("source")),
            route_algorithm="stir-quotient-domain",
            route_inputs=("index", "points", "answers"),
            cases=(
                ProgramCase("invalid", (), terminal="InvalidQuotientDomain"),
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
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
        "stir-folded-word": DerivedWordProgram(
            name="stir-folded-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
            arguments=("answers", "challenge", "points"),
            oracle_ports=(OraclePort("fill"), OraclePort("source")),
            route_algorithm="zero-vs-nonzero",
            route_inputs=("index",),
            cases=(
                ProgramCase(
                    "nonzero",
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
                ProgramCase("zero", (), terminal="UndefinedFold"),
            ),
            output_visibility=Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=2,
            maximum_leaf_reads=2,
        ),
    }
    return validate_programs(programs)


def representative_plan() -> QueryPlan:
    inputs = tuple(
        PlanInput(name)
        for name in (
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
            "whir-alpha-one",
            "whir-alpha-zero",
            "whir-index",
        )
    )
    plan = QueryPlan(
        name="representative-verifier-derived-reads",
        inputs=inputs,
        source_oracles=tuple(
            PlanOracle(name)
            for name in (
                "circle-first",
                "circle-second",
                "circle-third",
                "deep-first",
                "deep-second",
                "stir-fill",
                "stir-source",
                "whir-source",
            )
        ),
        sites=(
            PlanSite(
                "circle-batch",
                "circle-batched-word",
                LogicalActivation(),
                plan_input("circle-index"),
                (("coefficient", plan_input("circle-coefficient")),),
                (
                    ("first", "circle-first"),
                    ("second", "circle-second"),
                    ("third", "circle-third"),
                ),
            ),
            PlanSite(
                "deep-first-quotient",
                "multipoint-quotient-word",
                LogicalActivation(),
                plan_input("deep-index"),
                (
                    ("answers", plan_input("deep-answers-first")),
                    ("points", plan_input("deep-points-first")),
                ),
                (("source", "deep-first"),),
            ),
            PlanSite(
                "deep-second-quotient",
                "multipoint-quotient-word",
                LogicalActivation(),
                plan_input("deep-index"),
                (
                    ("answers", plan_input("deep-answers-second")),
                    ("points", plan_input("deep-points-second")),
                ),
                (("source", "deep-second"),),
            ),
            PlanSite(
                "stir-fold",
                "stir-folded-word",
                LogicalActivation(),
                plan_input("stir-index"),
                (
                    ("answers", plan_input("stir-answers")),
                    ("challenge", plan_input("stir-challenge")),
                    ("points", plan_input("stir-points")),
                ),
                (("fill", "stir-fill"), ("source", "stir-source")),
            ),
            PlanSite(
                "whir-grouped-fold",
                "four-point-folded-word",
                LogicalActivation(),
                plan_input("whir-index"),
                (
                    ("alpha0", plan_input("whir-alpha-zero")),
                    ("alpha1", plan_input("whir-alpha-one")),
                    ("one", plan_input("offset-one")),
                    ("three", plan_input("offset-three")),
                    ("two", plan_input("offset-two")),
                ),
                (("source", "whir-source"),),
            ),
        ),
    )
    return validate_plan(plan, representative_programs())


def activation_and_prior_result_programs() -> Mapping[str, DerivedWordProgram]:
    programs = {
        "read-word": DerivedWordProgram(
            name="read-word",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
            arguments=(),
            oracle_ports=(OraclePort("source"),),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                ProgramCase(
                    "only",
                    (ReadStep("source-value", "source", "index"),),
                    result="source-value",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
        "value-only-combination": DerivedWordProgram(
            name="value-only-combination",
            modulus=17,
            algebra_profile=AlgebraProfile.PRIME_FIELD,
            arguments=("prior",),
            oracle_ports=(OraclePort("source"),),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                ProgramCase(
                    "only",
                    (
                        ReadStep("source-value", "source", "index"),
                        PureStep(
                            "combined",
                            "field-add",
                            ("source-value", "prior"),
                        ),
                    ),
                    result="combined",
                ),
            ),
            output_visibility=Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        ),
    }
    return validate_programs(programs)


def activation_and_prior_result_plan() -> QueryPlan:
    programs = activation_and_prior_result_programs()
    plan = QueryPlan(
        name="activation-and-prior-result-value-flow",
        inputs=(
            PlanInput("active", is_boolean=True),
            PlanInput("first-index"),
            PlanInput("second-index"),
        ),
        source_oracles=(PlanOracle("first-source"), PlanOracle("second-source")),
        sites=(
            PlanSite(
                "first-read",
                "read-word",
                LogicalActivation(),
                plan_input("first-index"),
                (),
                (("source", "first-source"),),
            ),
            PlanSite(
                "second-combination",
                "value-only-combination",
                LogicalActivation(plan_input("active")),
                plan_input("second-index"),
                (("prior", prior_logical_result("first-read")),),
                (("source", "second-source"),),
            ),
        ),
    )
    return validate_plan(plan, programs)
