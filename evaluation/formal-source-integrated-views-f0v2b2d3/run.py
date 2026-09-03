#!/usr/bin/env python3
"""Run the F0-V2B2D3 integrated six-owner-view closure gate."""

from __future__ import annotations

import argparse
from collections import Counter
import copy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
F2O1_LEDGER = HERE / "f2o1-six-view-ledger.json"
F2O1 = ROOT / "evaluation/formal-provider-observables-f2o1"
F2O1_GENERATOR = F2O1 / "generator.py"
F2O1_CHECKER = F2O1 / "checker.py"
F2O1_FROZEN_LEDGER = F2O1 / "generated/ledger.json"
F2O1_FROZEN_LEAN = F2O1 / "generated/Integrated.lean"

AGGREGATE = "F0V2B2D3-A-INTEGRATED-SIX-VIEWS"
CANNOT_ANSWER = "F0V2B2D3-C-INTEGRATED-SIX-VIEWS"
BASELINE = "integrated-baseline"
CONTROL_NAMES = (
    "private-verifier-output-sink",
    "invalid-module-control-sink",
    "history-challenge-condition",
    "logical-reject-preemption",
)


class GateFailure(RuntimeError):
    """The package detected drift, disagreement, or an accepted mutation."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _algorithm_preimages(model: ModuleType, fixture: object) -> tuple[Any, ...]:
    return tuple(
        sorted(
            (
                item.identity.internal_reference(),
                model.k1.algorithm_preimage(item),
            )
            for item in fixture.algorithms
        )
    )


def _cold_project(
    model: ModuleType, independent: ModuleType, fixture: object
) -> tuple[dict[str, Any], dict[str, Any]]:
    return independent.project(
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
        model.d1.raw_module_sources(fixture.environment),
        _algorithm_preimages(model, fixture),
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        _require(value is None, "unit leaf has another carrier")
        return {"kind": "unit"}
    if kind == "natural":
        _require(
            type(value) is int and 0 <= value <= atom["max"],
            "natural leaf is outside its bound",
        )
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        _require(type(value) is bool, "meta-boolean leaf has another carrier")
        return {"kind": "meta-boolean"}
    if kind == "canonical-body":
        _require(
            type(value) is dict
            and set(value) == {"compiler", "body"}
            and value["compiler"] == atom["compiler"],
            "canonical-body leaf has another compiler",
        )
        bytes.fromhex(value["body"])
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "exact-profile-law":
        _require(
            type(value) is dict and value.get("name") == atom["law"],
            "profile-law leaf names another law",
        )
        return {"kind": "exact-profile-law", "law": atom["law"]}
    if kind == "admitted-module-effect":
        _require(
            type(value) is dict
            and set(value) == {"module_body", "declaration_body", "payload_body"},
            "admitted module-effect leaf has another carrier",
        )
        for body in value.values():
            bytes.fromhex(body)
        return {"kind": "admitted-module-effect"}
    raise GateFailure(f"unknown schema atom {kind}")


def _enumerate_leaves(
    view: str, schema: dict[str, Any], value: Any
) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []

    def walk(node: dict[str, Any], current: Any, path: list[dict[str, int]]) -> None:
        kind = node["node"]
        if kind == "atom":
            leaves.append(
                {
                    "view": view,
                    "path": copy.deepcopy(path),
                    "boundary": _boundary(node["atom"], current),
                }
            )
            return
        if kind == "record":
            ordinals = [ordinal for ordinal, _child in node["fields"]]
            _require(
                type(current) is dict and list(current) == ordinals,
                "record differs from compiled schema",
            )
            for ordinal, child in node["fields"]:
                walk(
                    child,
                    current[ordinal],
                    [*path, {"step": "field", "ordinal": ordinal}],
                )
            return
        if kind == "variant":
            _require(
                type(current) is dict and set(current) == {"case", "value"},
                "variant differs from compiled schema",
            )
            cases = dict(node["cases"])
            _require(current["case"] in cases, "variant selects an absent case")
            walk(
                cases[current["case"]],
                current["value"],
                [*path, {"step": "variant", "ordinal": current["case"]}],
            )
            return
        if kind == "sequence":
            _require(
                type(current) is list and len(current) <= node["max"],
                "sequence differs from compiled schema",
            )
            for ordinal, child_value in enumerate(current):
                walk(
                    node["element"],
                    child_value,
                    [*path, {"step": "sequence", "ordinal": ordinal}],
                )
            return
        raise GateFailure(f"unknown schema node {kind}")

    walk(schema, value, [])
    return leaves


def _path_key(coordinate: Mapping[str, Any]) -> tuple[tuple[str, int], ...]:
    return tuple((item["step"], item["ordinal"]) for item in coordinate["path"])


def _parse_path(spec: str) -> tuple[tuple[str, int], ...]:
    names = {"f": "field", "s": "sequence", "v": "variant"}
    return tuple((names[token[0]], int(token[1:])) for token in spec.split())


def _source_coordinates() -> dict[str, tuple[str, str, str]]:
    result: dict[str, tuple[str, str, str]] = {
        "subject.protocol": (BASELINE, "ExecutionView", "f0"),
        "module.0.decision-class": (BASELINE, "EffectView", "f7 s0 f1"),
        "module.1.decision-class": (
            BASELINE,
            "StrategyDecisionView",
            "f1 s1 f4 v2 f0",
        ),
        "module.2.decision-class": (
            BASELINE,
            "StrategyDecisionView",
            "f1 s2 f4 v2 f0",
        ),
    }
    mode_paths = (
        "f4 s0 f1 f5 v0",
        "f4 s1 f1 f5 v1 f0",
        "f4 s2 f1 f5 v2",
    )
    for oracle_ref, path in enumerate(mode_paths):
        result[f"oracle.{oracle_ref}.mode"] = (BASELINE, "EffectView", path)
    for occurrence_ref, visibility in ((6, 0), (9, 1), (12, 0)):
        result[f"query.{occurrence_ref}.visibility"] = (
            BASELINE,
            "EffectView",
            f"f1 s{occurrence_ref} f3 v6 v1 f2 v{visibility}",
        )
    for occurrence_ref in (*range(14), *range(17, 23)):
        result[f"occurrence.{occurrence_ref}"] = (
            BASELINE,
            "EffectView",
            f"f1 s{occurrence_ref} f0",
        )
    for claim_ref in range(3):
        result[f"claim.{claim_ref}.declaration"] = (
            BASELINE,
            "ClaimReductionView",
            f"f1 s{claim_ref} f1",
        )
    for reduction_ref in range(2):
        result[f"reduction.{reduction_ref}.declaration"] = (
            BASELINE,
            "ClaimReductionView",
            f"f2 s{reduction_ref} f1",
        )
    for terminal_ref in range(3):
        result[f"terminal.{terminal_ref}.declaration"] = (
            BASELINE,
            "EffectView",
            f"f6 s{terminal_ref} f0",
        )
    result["terminal.22.preemption"] = (
        BASELINE,
        "EffectView",
        "f6 s2 f6",
    )
    result["control.logical-reject-preemption.terminal.22.preemption"] = (
        "logical-reject-preemption",
        "EffectView",
        "f6 s2 f6",
    )
    _require(len(result) == 40, "owner-view source table is not the forty F2-O1 gaps")
    return result


def _adapt_coordinate(
    carrier_index: int,
    view_index: int,
    carrier: str,
    view: str,
    coordinate: dict[str, Any],
) -> dict[str, Any]:
    owner_path = copy.deepcopy(coordinate["path"])
    return {
        # Compatibility discriminator required by the unchanged F2-O1 checker.
        "view": "PublicCoinView",
        "path": [
            {"step": "field", "ordinal": carrier_index},
            {"step": "field", "ordinal": view_index},
            *owner_path,
        ],
        "boundary": copy.deepcopy(coordinate["boundary"]),
        "carrier": carrier,
        "owner_view": view,
        "owner_path": owner_path,
    }


def _manifest_table(
    view_values: Mapping[str, Mapping[str, Any]],
    schemas: Mapping[str, dict[str, Any]],
    carrier_order: tuple[str, ...],
    view_order: tuple[str, ...],
) -> tuple[list[dict[str, Any]], dict[tuple[str, str, tuple[Any, ...]], dict[str, Any]]]:
    manifest: list[dict[str, Any]] = []
    table: dict[tuple[str, str, tuple[Any, ...]], dict[str, Any]] = {}
    for carrier_index, carrier in enumerate(carrier_order):
        for view_index, view in enumerate(view_order):
            for coordinate in _enumerate_leaves(
                view, schemas[view], view_values[carrier][view]
            ):
                adapted = _adapt_coordinate(
                    carrier_index, view_index, carrier, view, coordinate
                )
                key = (carrier, view, _path_key(coordinate))
                _require(key not in table, "owner leaf coordinate is duplicated")
                table[key] = adapted
                manifest.append(adapted)
    return manifest, table


def _f2_gap_counts(result: Mapping[str, Any]) -> dict[str, int]:
    counts = Counter(item["class"] for item in result["gaps"])
    return {name: counts.get(name, 0) for name in sorted(result["gap_classes"])}


def _adapt_f2o1(
    generator: ModuleType,
    checker: ModuleType,
    lean_text: str,
    original_ledger: dict[str, Any],
    facts: dict[str, Any],
    typed_values: Mapping[str, Mapping[str, Any]],
    cold_values: Mapping[str, Mapping[str, Any]],
    schemas: Mapping[str, dict[str, Any]],
    carrier_order: tuple[str, ...],
    view_order: tuple[str, ...],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, int]]:
    typed_manifest, typed_table = _manifest_table(
        typed_values, schemas, carrier_order, view_order
    )
    cold_manifest, _cold_table = _manifest_table(
        cold_values, schemas, carrier_order, view_order
    )
    _require(
        {_canonical(item) for item in typed_manifest}
        == {_canonical(item) for item in cold_manifest},
        "typed and cold six-view leaf universes disagree",
    )

    ledger = copy.deepcopy(original_ledger)
    original_paths = checker._source_paths()
    expected_paths: dict[str, tuple[tuple[str, int], ...]] = {}
    for construct_id, owner_path in original_paths.items():
        coordinate = typed_table[(BASELINE, "PublicCoinView", owner_path)]
        expected_paths[construct_id] = _path_key(coordinate)
    added = _source_coordinates()
    for construct_id, (carrier, view, path_spec) in added.items():
        coordinate = typed_table[(carrier, view, _parse_path(path_spec))]
        expected_paths[construct_id] = _path_key(coordinate)

    for construct in ledger["constructs"]:
        construct_id = construct["id"]
        source = construct["source"]
        if "coordinate" in source:
            owner_path = _path_key(source["coordinate"])
            source["coordinate"] = copy.deepcopy(
                typed_table[(BASELINE, "PublicCoinView", owner_path)]
            )
        elif construct_id in added:
            carrier, view, path_spec = added[construct_id]
            source.clear()
            source["coordinate"] = copy.deepcopy(
                typed_table[(carrier, view, _parse_path(path_spec))]
            )
        else:
            gap = source["no_source_coordinate"]
            gap["named_by"] = [
                copy.deepcopy(
                    typed_table[
                        (BASELINE, "PublicCoinView", _path_key(coordinate))
                    ]
                )
                for coordinate in gap["named_by"]
            ]
    ledger["gaps"] = sorted(
        (
            {
                "construct": construct["id"],
                "class": construct["source"]["no_source_coordinate"]["class"],
                "needed_for": construct["source"]["no_source_coordinate"][
                    "needed_for"
                ],
            }
            for construct in ledger["constructs"]
            if "no_source_coordinate" in construct["source"]
        ),
        key=lambda item: item["construct"],
    )
    baseline_counts = {
        view: sum(
            1
            for coordinate in typed_manifest
            if coordinate["carrier"] == BASELINE
            and coordinate["owner_view"] == view
        )
        for view in view_order
    }
    ledger["subject"]["view_status"] = {
        view: {
            "status": "realized-by-f0v2b2d3-research-gate",
            "leaf_count": baseline_counts[view],
            "implementation": (
                "evaluation/formal-source-integrated-views-f0v2b2d3/"
                "model.py"
            ),
        }
        for view in view_order
    }
    ledger["premises"][1]["statement"] = (
        "F0-V2B2D3 supplies research-gate bodies for all six normalized views; "
        "this adapted ledger does not publish target owner authority."
    )
    ledger["six_view_adapter"] = {
        "format": "zkc.f0v2b2d3.f2o1-six-view-adapter.v0",
        "carrier_order": list(carrier_order),
        "view_order": list(view_order),
        "leaf_count": len(typed_manifest),
        "closed_gap_class": "operational-owner-view",
        "checker_compatibility": (
            "virtual paths prefix carrier and owner-view ordinals; the preserved "
            "PublicCoinView discriminator is required by the unchanged F2-O1 checker, "
            "while carrier, owner_view, and owner_path retain the actual source."
        ),
    }

    adapted_facts = copy.deepcopy(facts)
    adapted_facts["manifest"] = cold_manifest
    adapted_facts["universe"] = {_canonical(item) for item in cold_manifest}
    adapted_facts["gap_classes"] = checker.GAP_CLASSES
    prior_source_paths = checker._source_paths
    checker._source_paths = lambda: expected_paths
    try:
        result = checker.check(ledger, lean_text, adapted_facts)
    finally:
        checker._source_paths = prior_source_paths
    leaf_counts = {
        f"{carrier}/{view}": sum(
            1
            for coordinate in typed_manifest
            if coordinate["carrier"] == carrier
            and coordinate["owner_view"] == view
        )
        for carrier in carrier_order
        for view in view_order
    }
    return ledger, result, leaf_counts


def _substitutions(model: ModuleType, views: dict[str, Any]) -> dict[str, bytes]:
    substitutions: dict[str, dict[str, Any]] = {}
    changed = copy.deepcopy(views["PublicBindingView"])
    changed[2][0][2] = model.foundation._v(
        (changed[2][0][2]["case"] + 1) % 3
    )
    substitutions["PublicBindingView"] = changed
    changed = copy.deepcopy(views["StrategyDecisionView"])
    changed[1][0][4] = copy.deepcopy(changed[1][1][4])
    substitutions["StrategyDecisionView"] = changed
    changed = copy.deepcopy(views["PublicCoinView"])
    changed[2] = not changed[2]
    substitutions["PublicCoinView"] = changed
    changed = copy.deepcopy(views["EffectView"])
    changed[6][0][1] = model.foundation._v(
        (changed[6][0][1]["case"] + 1) % 3
    )
    substitutions["EffectView"] = changed
    changed = copy.deepcopy(views["ClaimReductionView"])
    changed[1][0][3] = model.foundation._v(
        1 - changed[1][0][3]["case"]
    )
    substitutions["ClaimReductionView"] = changed
    changed = copy.deepcopy(views["ExecutionView"])
    changed[6][3][0][2] = model.foundation._v(
        (changed[6][3][0][2]["case"] + 1) % 3
    )
    substitutions["ExecutionView"] = changed
    return {
        view: model.codec.encode_value(model.VIEW_SCHEMAS[view], value)
        for view, value in substitutions.items()
    }


def evaluate() -> tuple[list[Finding], dict[str, Any], dict[str, Any]]:
    model = _load("_zkc_f0v2b2d3_model", MODEL)
    independent = _load("_zkc_f0v2b2d3_independent", INDEPENDENT)
    generator = _load("_zkc_f0v2b2d3_f2o1_generator", F2O1_GENERATOR)
    checker = _load("_zkc_f0v2b2d3_f2o1_checker", F2O1_CHECKER)
    profile = model.d1.profile_evidence()
    independent.configure(
        profile["candidate_interaction_digest"],
        profile["candidate_interaction_body_sha256"],
    )
    _require(model.VIEW_SCHEMAS == independent.VIEW_SCHEMAS, "schemas disagree")

    findings = [
        _finding(
            "predecessor-source-pins",
            "Affirmative",
            "F0V2B2D3-A-PREDECESSOR-PINS",
        ),
        _finding(
            "candidate-profile-and-schema",
            "Affirmative",
            "F0V2B2D3-A-PROFILE-SCHEMA",
        ),
    ]
    carrier_order = tuple(model.d1.SCENARIOS)
    view_order = tuple(model.VIEW_ORDER)
    _require(len(carrier_order) == 5 and len(view_order) == 6, "matrix shape drifted")
    typed_values: dict[str, dict[str, Any]] = {}
    cold_values: dict[str, dict[str, Any]] = {}
    body_matrix: dict[str, dict[str, Any]] = {}
    disagreements: list[str] = []
    control_eligibility: dict[str, bool] = {}
    coverage: dict[str, Any] = {}
    for carrier, fixture in model.d1.fixtures().items():
        core_result = model.d1.admit_core(fixture.candidate, fixture.environment)
        _require(
            core_result.outcome == "Affirmative" and core_result.handle is not None,
            f"{carrier} Core did not admit",
        )
        protocol_result = model.d1.admit_fresh_protocol(
            core_result.handle, fixture.protocol_candidate, fixture.environment
        )
        _require(
            protocol_result.outcome == "Affirmative"
            and protocol_result.handle is not None,
            f"{carrier} Fresh Protocol did not admit",
        )
        typed = model.project_views(core_result.handle, protocol_result.handle)
        cold_view, cold_evidence = _cold_project(model, independent, fixture)
        typed_bodies = model.encode_views(typed)
        cold_bodies = independent.encode_views(cold_view)
        typed_values[carrier] = typed
        cold_values[carrier] = cold_view
        coverage[carrier] = {
            "decisions": cold_evidence["decisions"],
            "oracle_modes": list(cold_evidence["oracle_modes"]),
            "oracle_visibilities": list(cold_evidence["oracle_visibilities"]),
            "module_decisions": list(cold_evidence["module_decisions"]),
        }
        control_eligibility[carrier] = cold_evidence["pc_graph"]["eligible"]
        body_matrix[carrier] = {}
        for view in view_order:
            if typed_bodies[view] != cold_bodies[view]:
                disagreements.append(f"{carrier}/{view}:typed-cold")
            decoded = model.k1.decode_datum(typed_bodies[view])
            if model.k1.encode_datum(decoded) != typed_bodies[view]:
                disagreements.append(f"{carrier}/{view}:round-trip")
            leaves = _enumerate_leaves(
                view, model.VIEW_SCHEMAS[view], typed[view]
            )
            body_matrix[carrier][view] = {
                "sha256": hashlib.sha256(typed_bodies[view]).hexdigest(),
                "bytes": len(typed_bodies[view]),
                "leaves": len(leaves),
            }
    _require(not disagreements, f"CannotAnswer/{CANNOT_ANSWER}: {disagreements}")
    _require(
        control_eligibility[BASELINE]
        and all(not control_eligibility[name] for name in CONTROL_NAMES),
        "D1 control outcomes drifted",
    )
    expected_coverage = {
        "decisions": 4,
        "oracle_modes": [0, 1, 2],
        "oracle_visibilities": [0, 1, 0],
        "module_decisions": [0, 1, 2],
    }
    _require(
        all(item == expected_coverage for item in coverage.values()),
        "constructor branch coverage drifted",
    )
    findings.extend(
        (
            _finding(
                "five-d1-core-and-protocol-admissions",
                "Affirmative",
                "F0V2B2D3-A-FIVE-CARRIERS",
            ),
            _finding(
                "thirty-typed-projections",
                "Affirmative",
                "F0V2B2D3-A-THIRTY-TYPED",
            ),
            _finding(
                "thirty-cold-byte-agreements",
                "Affirmative",
                "F0V2B2D3-A-THIRTY-COLD",
            ),
            _finding(
                "thirty-canonical-round-trips",
                "Affirmative",
                "F0V2B2D3-A-THIRTY-ROUNDTRIP",
            ),
            _finding(
                "oracle-module-challenge-terminal-coverage",
                "Affirmative",
                "F0V2B2D3-A-CONSTRUCTOR-COVERAGE",
            ),
            _finding(
                "four-d1-neighbour-controls",
                "Refused",
                "F0V2B2D3-R-D1-CONTROLS",
            ),
        )
    )

    baseline_bodies = model.encode_views(typed_values[BASELINE])
    substituted = _substitutions(model, typed_values[BASELINE])
    _require(
        set(substituted) == set(view_order)
        and all(substituted[view] != baseline_bodies[view] for view in view_order),
        "schema-valid owner substitution was not byte-distinct",
    )
    findings.append(
        _finding(
            "six-schema-valid-owner-substitutions",
            "Refused",
            "F0V2B2D3-R-SIX-OWNER-SUBSTITUTIONS",
        )
    )

    lean_text, original_ledger = generator.build()
    _require(
        lean_text == F2O1_FROZEN_LEAN.read_text(encoding="utf-8")
        and original_ledger
        == json.loads(F2O1_FROZEN_LEDGER.read_text(encoding="utf-8")),
        "unchanged F2-O1 generator no longer reproduces its fixtures",
    )
    facts = checker.owner_facts()
    facts["gap_classes"] = checker.GAP_CLASSES
    before = checker.check(original_ledger, lean_text, facts)
    _require(
        before["outcome"] == "Affirmative"
        and before["code"] == checker.PASS_CODE,
        f"unchanged F2-O1 checker rejected the frozen ledger: {before}",
    )
    before["gap_classes"] = checker.GAP_CLASSES
    before_counts = _f2_gap_counts(before)
    adapted_ledger, after, leaf_counts = _adapt_f2o1(
        generator,
        checker,
        lean_text,
        original_ledger,
        facts,
        typed_values,
        cold_values,
        model.VIEW_SCHEMAS,
        carrier_order,
        view_order,
    )
    _require(
        after["outcome"] == "Affirmative" and after["code"] == checker.PASS_CODE,
        f"unchanged F2-O1 checker rejected six-view ledger: {after}",
    )
    after["gap_classes"] = checker.GAP_CLASSES
    after_counts = _f2_gap_counts(after)
    _require(
        before_counts["operational-owner-view"] == 40
        and after_counts["operational-owner-view"] == 0,
        "F2-O1 owner-view gap delta differs",
    )
    _require(
        after["sourced"] - before["sourced"] == 40
        and len(before["gaps"]) - len(after["gaps"]) == 40,
        "F2-O1 source and gap totals do not close exactly forty",
    )
    findings.extend(
        (
            _finding(
                "unchanged-f2o1-generator-and-checker",
                "Affirmative",
                "F0V2B2D3-A-F2O1-UNCHANGED",
            ),
            _finding(
                "five-carrier-six-view-leaf-universe",
                "Affirmative",
                "F0V2B2D3-A-COMPLETE-LEAF-UNIVERSE",
            ),
            _finding(
                "f2o1-owner-view-gaps-40-to-0",
                "Affirmative",
                "F0V2B2D3-A-F2O1-OWNER-VIEW-40-TO-0",
            ),
        )
    )
    outcomes = {
        "operational-owner-view": (
            "Affirmative",
            "F0V2B2D3-A-GAP-OWNER-VIEW-40-TO-0",
        ),
        "operational-distribution": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-DISTRIBUTION-3-TO-3",
        ),
        "operational-denotation": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-DENOTATION-6-TO-6",
        ),
        "module-effect-denotation": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-MODULE-DENOTATION-3-TO-3",
        ),
        "oracle-carrier-representation": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-ORACLE-CARRIER-3-TO-3",
        ),
        "operational-outcome-map": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-OUTCOME-MAP-1-TO-1",
        ),
        "property-premise": (
            "CannotAnswer",
            "F0V2B2D3-C-GAP-PREMISE-5-TO-5",
        ),
    }
    for gap_class in sorted(outcomes):
        outcome, code = outcomes[gap_class]
        findings.append(
            _finding(
                f"f2o1-gap-{gap_class}-{before_counts[gap_class]}-to-{after_counts[gap_class]}",
                outcome,
                code,
            )
        )
    findings.extend(
        (
            _finding(
                "remaining-sixteen-operational-semantic-gaps",
                "CannotAnswer",
                "F0V2B2D3-C-REMAINING-OPERATIONAL-SEMANTICS",
            ),
            _finding(
                "remaining-five-property-premises",
                "CannotAnswer",
                "F0V2B2D3-C-REMAINING-PREMISES",
            ),
            _finding(
                "target-owner-authority-untouched",
                "Affirmative",
                "F0V2B2D3-A-NONPUBLICATION",
            ),
            _finding(
                "proof-security-and-provider-correspondence",
                "CannotAnswer",
                "F0V2B2D3-C-NONCLAIMS",
            ),
            _finding(
                "integrated-six-view-closure",
                "Affirmative",
                AGGREGATE,
            ),
        )
    )

    payload = [finding.value() for finding in findings]
    findings_sha256 = hashlib.sha256(
        _canonical(payload).encode("utf-8")
    ).hexdigest()
    source_paths = (
        ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py",
        ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/independent.py",
        ROOT
        / "evaluation/formal-source-owner-projections-f0v2b2c1b1/model.py",
        ROOT
        / "evaluation/formal-source-owner-projections-f0v2b2c1b1/independent.py",
        ROOT
        / "evaluation/formal-source-oracle-owner-projections-f0v2b2c1b2/model.py",
        ROOT
        / "evaluation/formal-source-oracle-owner-projections-f0v2b2c1b2/independent.py",
        ROOT
        / "evaluation/formal-source-claim-reduction-owner-projections-f0v2b2c1b3/model.py",
        ROOT
        / "evaluation/formal-source-claim-reduction-owner-projections-f0v2b2c1b3/independent.py",
        ROOT
        / "evaluation/formal-source-module-owner-projections-f0v2b2c1b4/model.py",
        ROOT
        / "evaluation/formal-source-module-owner-projections-f0v2b2c1b4/independent.py",
        ROOT
        / "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/model.py",
        ROOT
        / "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/independent.py",
        F2O1_GENERATOR,
        F2O1_CHECKER,
        F2O1 / "expected-findings.json",
    )
    source_pins = {
        str(path.relative_to(ROOT)): _sha256(path) for path in source_paths
    }
    ledger_bytes = (_canonical(adapted_ledger) + "\n").encode("utf-8")
    metrics = {
        "findings": len(findings),
        "findings_sha256": findings_sha256,
        "carrier_count": len(carrier_order),
        "view_count": len(view_order),
        "body_count": sum(len(item) for item in body_matrix.values()),
        "disagreements": disagreements,
        "body_matrix": body_matrix,
        "leaf_counts": leaf_counts,
        "complete_leaf_universe": sum(leaf_counts.values()),
        "coverage": coverage,
        "control_eligibility": control_eligibility,
        "owner_substitutions": len(substituted),
        "f2o1": {
            "before": {
                "constructs": before["constructs"],
                "sourced": before["sourced"],
                "gaps": len(before["gaps"]),
                "by_class": before_counts,
            },
            "after": {
                "constructs": after["constructs"],
                "sourced": after["sourced"],
                "gaps": len(after["gaps"]),
                "by_class": after_counts,
                "missing_operational_observables": after["aggregate"][
                    "missing_operational_observables"
                ],
            },
            "owner_view_gaps_closed": 40,
        },
        "source_pins": source_pins,
        "f2o1_ledger_sha256": hashlib.sha256(ledger_bytes).hexdigest(),
    }
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": findings_sha256,
        "finding_codes": payload,
        "body_matrix": body_matrix,
        "f2o1_gap_counts": {
            "before": before_counts,
            "after": after_counts,
        },
        "source_pins": source_pins,
        "f2o1_ledger_sha256": metrics["f2o1_ledger_sha256"],
    }
    return findings, metrics, {"observed": observed, "ledger": adapted_ledger}


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot load frozen findings") from error
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--refresh", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        findings, metrics, artifacts = evaluate()
    except (GateFailure, ValueError, KeyError, TypeError) as error:
        print(
            json.dumps(
                {"aggregate": CANNOT_ANSWER, "disagreements": [str(error)]},
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    observed = artifacts["observed"]
    ledger_text = json.dumps(artifacts["ledger"], indent=2, sort_keys=True) + "\n"
    if args.refresh:
        EXPECTED.write_text(json.dumps(observed, indent=2, sort_keys=True) + "\n")
        F2O1_LEDGER.write_text(ledger_text, encoding="utf-8")
    if args.check:
        if observed != _load_expected():
            print(
                json.dumps(
                    {"expected": _load_expected(), "observed": observed},
                    indent=2,
                    sort_keys=True,
                )
            )
            return 1
        try:
            frozen_ledger = F2O1_LEDGER.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as error:
            print(json.dumps({"ledger_error": str(error)}, indent=2))
            return 1
        if frozen_ledger != ledger_text:
            print(json.dumps({"ledger_error": "six-view ledger drifted"}, indent=2))
            return 1
    outcomes = Counter(finding.outcome for finding in findings)
    output: dict[str, Any] = {
        "aggregate": AGGREGATE,
        "outcomes": dict(sorted(outcomes.items())),
        "metrics": metrics,
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
