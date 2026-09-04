"""Finite family/member measurements over the retained indexed-Core instrument.

This module deliberately imports the existing bounded authoring model.  It does
not add a Core constructor or a second admission authority.  Its graph is the
documented retained-fixture projection, not the complete target ``PCGraph``.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, fields, is_dataclass
from enum import Enum
import importlib.util
import json
from pathlib import Path
import statistics
import sys
import time
from types import ModuleType
from typing import Callable


ROOT = Path(__file__).resolve().parents[2]
INDEXED_MODEL_PATH = ROOT / "evaluation/indexed-core-elaboration/reference_model.py"
ADMISSION_REPETITIONS = 21
ADMISSION_TIME_LIMIT_NS = 250_000_000


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


indexed = _load("_zkc_indexed_core_for_family_instance_probe", INDEXED_MODEL_PATH)
protocol = indexed.protocol


@dataclass(frozen=True)
class Measurement:
    family: str
    parameter_name: str
    parameter: int
    body_bytes: int
    core_id: str
    admission_wall_time_ns: int
    pcgraph_nodes: int
    pcgraph_edges: int
    declarations: int
    declarations_different_from_previous: int
    varying_body_fields_from_previous: tuple[str, ...]

    def frozen_value(self) -> dict[str, object]:
        value = asdict(self)
        del value["admission_wall_time_ns"]
        value["admission_wall_time_class"] = (
            f"at-most-{ADMISSION_TIME_LIMIT_NS}-ns"
        )
        value["varying_body_fields_from_previous"] = list(
            self.varying_body_fields_from_previous
        )
        return value

    def report_value(self) -> dict[str, object]:
        value = self.frozen_value()
        value["admission_wall_time_ns"] = self.admission_wall_time_ns
        return value


@dataclass(frozen=True)
class RegularLaw:
    family: str
    metric: str
    intercept: int
    slope: int

    def value(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True)
class NonAffineObservation:
    family: str
    metric: str
    parameters: tuple[int, ...]
    observed_values: tuple[int, ...]
    successive_changes: tuple[tuple[int, int], ...]

    def value(self) -> dict[str, object]:
        value = asdict(self)
        value["parameters"] = list(self.parameters)
        value["observed_values"] = list(self.observed_values)
        value["successive_changes"] = [
            {"parameter_delta": delta, "value_delta": change}
            for delta, change in self.successive_changes
        ]
        return value


def _plain(value: object) -> object:
    if isinstance(value, Enum):
        return value.value
    if is_dataclass(value) and not isinstance(value, type):
        return {
            item.name: _plain(getattr(value, item.name)) for item in fields(value)
        }
    if type(value) is tuple:
        return [_plain(item) for item in value]
    if type(value) is list:
        return [_plain(item) for item in value]
    if type(value) is dict:
        return {str(key): _plain(item) for key, item in value.items()}
    if value is None or type(value) in {str, int, bool}:
        return value
    internal_reference = getattr(value, "internal_reference", None)
    if callable(internal_reference):
        reference = internal_reference()
        return reference.hex() if type(reference) is bytes else reference
    raise TypeError(f"unsupported canonical measurement value: {type(value)!r}")


def _canonical(value: object) -> str:
    return json.dumps(_plain(value), sort_keys=True, separators=(",", ":"))


def declaration_map(core: object) -> dict[str, str]:
    """Key declarations by semantic name, not by their enclosing sequence slot."""

    rows: dict[str, str] = {}

    def add(key: str, value: object) -> None:
        if key in rows:
            raise ValueError(f"duplicate declaration measurement key: {key}")
        rows[key] = _canonical(value)

    for item in core.inputs:
        add(f"input:{item.name}", item)
    for item in core.scopes:
        add(f"scope:{item.name}", item)
    for item in core.schedule:
        add(f"occurrence:{item.name}", item)
    for item in core.extensions:
        add(f"extension:{item}", item)
    for item in core.initial_claims:
        add(f"initial-claim:{item}", item)
    for item in core.reductions:
        add(f"reduction:{item.name}", item)
    for item in core.claim_uses:
        add(f"claim-use:{item.consumer}", item)
    return rows


def declaration_difference(left: object, right: object) -> int:
    before = declaration_map(left)
    after = declaration_map(right)
    return sum(
        before.get(key) != after.get(key) for key in set(before).union(after)
    )


def varying_body_fields(left: object, right: object) -> tuple[str, ...]:
    return tuple(
        item.name
        for item in fields(left)
        if getattr(left, item.name) != getattr(right, item.name)
    )


def _producer(ref: object) -> tuple[str, str]:
    if ref.kind is protocol.RefKind.INPUT:
        return ("input", ref.name)
    return ("output", ref.name)


def fixture_pcgraph_counts(core: object) -> tuple[int, int]:
    """Count the complete graph representable by the simplified retained carrier.

    The adapter follows the target Section 11 node and edge categories where
    the fixture has coordinates.  Initial claims have no binding source here,
    and schedule-anchored reductions are not first-class occurrences.  The
    result therefore must not be represented as target-graph equivalence.
    """

    protocol.admit_core(core)
    nodes: set[tuple[object, ...]] = set()
    edges: set[tuple[tuple[object, ...], tuple[object, ...]]] = set()

    def edge(source: tuple[object, ...], target: tuple[object, ...]) -> None:
        nodes.add(source)
        nodes.add(target)
        edges.add((source, target))

    for item in core.inputs:
        input_node = (
            "private-input" if item.role is protocol.InputRole.VERIFIER_PRIVATE else "public-input",
            item.name,
        )
        binding = ("binding", item.name)
        scope = ("scope", item.scope)
        nodes.update((input_node, binding, scope))
        edge(input_node, binding)
        edge(scope, binding)

    for item in core.scopes:
        opening = ("scope", item.name)
        nodes.add(opening)
        if item.parent is not None:
            edge(("scope", item.parent), opening)

    occurrence_by_name = {item.name: item for item in core.schedule}
    publication_by_oracle: dict[str, str] = {}
    earlier_terminals: list[str] = []
    for item in core.schedule:
        activity = ("activity", item.name)
        effect = ("effect", item.name)
        output = ("output", item.name)
        nodes.update((activity, effect, output))
        edge(("scope", item.scope), activity)
        for ref in item.guard.refs:
            edge(_producer(ref), activity)
        for terminal in earlier_terminals:
            edge(("terminal", terminal), activity)
        edge(activity, effect)
        for ref in item.dependencies:
            edge(_producer(ref), effect)
        if item.check_predicate is not None:
            for ref in item.check_predicate.refs:
                edge(_producer(ref), effect)
        if item.kind is protocol.OccurrenceKind.ORACLE_PUBLISH:
            assert item.oracle_name is not None
            publication_by_oracle[item.oracle_name] = item.name
        if item.kind in {
            protocol.OccurrenceKind.ORACLE_QUERY,
            protocol.OccurrenceKind.ORACLE_ANSWER,
        }:
            assert item.oracle_name is not None
            publication = publication_by_oracle[item.oracle_name]
            edge(("effect", publication), effect)
        edge(effect, output)
        if item.kind is protocol.OccurrenceKind.TERMINAL:
            terminal = ("terminal", item.name)
            edge(effect, terminal)
            earlier_terminals.append(item.name)

    claims = set(core.initial_claims)
    claims.update(
        claim for reduction in core.reductions for claim in reduction.output_claims
    )
    nodes.update(("claim", claim) for claim in claims)

    reduction_names = {item.name for item in core.reductions}
    for use in core.claim_uses:
        if use.consumer in occurrence_by_name:
            target = ("effect", use.consumer)
        elif use.consumer in reduction_names:
            target = ("reduction", use.consumer)
        else:
            raise ValueError("claim-use consumer is absent from the schedule and reductions")
        edge(("claim", use.claim), target)

    for item in core.reductions:
        reduction = ("reduction", item.name)
        nodes.add(reduction)
        edge(("effect", item.at_occurrence), reduction)
        for claim in item.input_claims:
            edge(("claim", claim), reduction)
        for ref in item.side_inputs:
            edge(_producer(ref), reduction)
        for challenge in item.required_challenges:
            edge(("output", challenge), reduction)
        for publication in item.required_publications:
            edge(("effect", publication.publication), reduction)
        for claim in item.output_claims:
            edge(reduction, ("claim", claim))

    return len(nodes), len(edges)


def _median_admission_time(core: object) -> int:
    protocol.admit_core(core)
    samples: list[int] = []
    for _ in range(ADMISSION_REPETITIONS):
        start = time.perf_counter_ns()
        protocol.admit_core(core)
        samples.append(time.perf_counter_ns() - start)
    return int(statistics.median(samples))


def _measure_family(
    family: str,
    parameter_name: str,
    parameters: tuple[int, ...],
    build: Callable[[int], object],
) -> tuple[Measurement, ...]:
    result: list[Measurement] = []
    previous: object | None = None
    for parameter in parameters:
        checked = build(parameter)
        core = checked.core
        body = protocol.core_body(core)
        nodes, edges = fixture_pcgraph_counts(core)
        measurement = Measurement(
            family=family,
            parameter_name=parameter_name,
            parameter=parameter,
            body_bytes=len(body),
            core_id=(
                f"{checked.core_id.subject_kind}@{checked.core_id.digest.hex()}"
            ),
            admission_wall_time_ns=_median_admission_time(core),
            pcgraph_nodes=nodes,
            pcgraph_edges=edges,
            declarations=len(declaration_map(core)),
            declarations_different_from_previous=(
                0 if previous is None else declaration_difference(previous, core)
            ),
            varying_body_fields_from_previous=(
                () if previous is None else varying_body_fields(previous, core)
            ),
        )
        result.append(measurement)
        previous = core
    return tuple(result)


def measure() -> dict[str, tuple[Measurement, ...]]:
    fri_parameters = (2, 3, 4)
    fri_schema = indexed.fri_schema(
        fold_depths=fri_parameters,
        query_counts=(1,),
    )
    sumcheck_parameters = (1, 2, 4)
    sumcheck_schema = indexed.sumcheck_schema(round_counts=sumcheck_parameters)
    return {
        "fri-like-folding": _measure_family(
            "fri-like-folding",
            "fold_count",
            fri_parameters,
            lambda parameter: indexed.check_core_elaboration_at(
                fri_schema,
                indexed.SemanticIndex(
                    (("fold_depth", parameter), ("query_count", 1))
                ),
            ),
        ),
        "sumcheck-like-rounds": _measure_family(
            "sumcheck-like-rounds",
            "variable_count",
            sumcheck_parameters,
            lambda parameter: indexed.check_core_elaboration_at(
                sumcheck_schema,
                indexed.SemanticIndex((("round_count", parameter),)),
            ),
        ),
    }


def finite_variation(
    measurements: dict[str, tuple[Measurement, ...]],
) -> tuple[tuple[RegularLaw, ...], tuple[NonAffineObservation, ...]]:
    laws: list[RegularLaw] = []
    non_affine: list[NonAffineObservation] = []
    for family, rows in measurements.items():
        for metric in ("body_bytes", "pcgraph_nodes", "pcgraph_edges", "declarations"):
            first, second = rows[0], rows[1]
            delta_parameter = second.parameter - first.parameter
            delta_value = getattr(second, metric) - getattr(first, metric)
            if delta_parameter > 0 and delta_value % delta_parameter == 0:
                slope = delta_value // delta_parameter
                intercept = getattr(first, metric) - slope * first.parameter
                if all(
                    getattr(row, metric) == intercept + slope * row.parameter
                    for row in rows
                ):
                    laws.append(RegularLaw(family, metric, intercept, slope))
                    continue
            non_affine.append(
                NonAffineObservation(
                    family,
                    metric,
                    tuple(row.parameter for row in rows),
                    tuple(getattr(row, metric) for row in rows),
                    tuple(
                        (
                            right.parameter - left.parameter,
                            getattr(right, metric) - getattr(left, metric),
                        )
                        for left, right in zip(rows, rows[1:])
                    ),
                )
            )
    return tuple(laws), tuple(non_affine)


def adjacent_identity_substitutions_refused(
    measurements: dict[str, tuple[Measurement, ...]],
) -> bool:
    for rows in measurements.values():
        for left, right in zip(rows, rows[1:]):
            if left.core_id == right.core_id:
                return False
    return True


SUMCHECK_THEOREM_BINDINGS = {
    "theorem_source": "sumcheck-soundness-family-source",
    "quantifiers": ["variable_count", "degree_bound", "field_cardinality"],
    "bound": "degree_bound * variable_count / field_cardinality",
    "applicability_coordinates": [
        "theorem_schema_id",
        "family_definition_id",
        "family_read_manifest_schema_ids",
        "family_experiment_profile_ids",
        "source_and_target_subject_roles",
        "exact_role_and_parameter_substitution",
        "side_condition_schemas",
        "typed_bound_transform",
        "hypothesis_context_id",
        "support_and_validation_basis_ids",
    ],
    "pointwise_coordinates": [
        "family_definition_id",
        "logical_variable_count_literal_id",
        "concrete_core_id",
        "concrete_protocol_id",
        "relation_instance_and_binding_ids",
        "statement_and_witness_role_coordinates",
        "challenge_model_coordinate",
        "round_count_equals_variable_count",
        "degree_bound_coordinate",
        "field_cardinality_coordinate",
        "family_instance_correspondence_judgment_id",
    ],
    "design_evidence": {
        "instances-only": [
            "one family applicability judgment",
            "one pointwise correspondence and specialization per concrete Core",
        ],
        "template-core": [
            "one family applicability judgment",
            "one admitted template identity and total bounded unfolding law",
            "one unfolding equality and concrete Core admission per member",
            "one pointwise correspondence and specialization per concrete Core",
        ],
        "family-semantic-profile": [
            "one family applicability judgment",
            "one family-profile publication and parameter-fixing import per member",
            "one unfolding equality and concrete Core admission per member",
            "one pointwise correspondence and specialization per concrete Core",
        ],
    },
}


def theorem_source_is_reused() -> bool:
    evidence = SUMCHECK_THEOREM_BINDINGS["design_evidence"]
    return (
        len(evidence) == 3
        and all(
            rows[0] == "one family applicability judgment"
            for rows in evidence.values()
        )
        and "variable_count" in SUMCHECK_THEOREM_BINDINGS["quantifiers"]
        and "logical_variable_count_literal_id"
        in SUMCHECK_THEOREM_BINDINGS["pointwise_coordinates"]
    )
