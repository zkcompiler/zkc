#!/usr/bin/env python3
"""Check the frozen structural expressibility-axis matrix."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PACKAGE = Path(__file__).resolve().parent

AXES_PATH = PACKAGE / "axes.json"
CASES_PATH = PACKAGE / "cases.json"
EXPECTED_PATH = PACKAGE / "expected-findings.json"

EXPECTED_AXES = {
    "party_structure",
    "oracle_publishers",
    "verifier_input_privacy",
    "query_privacy",
    "verifier_randomness_privacy",
    "challenge_source",
    "challenge_interpretation",
    "round_structure",
    "statement_timing",
    "oracle_kinds",
    "oracle_access_modes",
    "commitment_relation",
    "setup_kind",
    "setup_trust",
    "composition_modes",
    "termination_modes",
    "randomness_sources",
    "statement_adaptivity",
    "query_adaptivity",
    "communication_kind",
}

OWNER_PINS = {
    "docs-next/pir/interactive-core.md":
        "9ef8181f88c3145319c4608c599f51b409157cfe9fdab7c1821fbb57f9da4bce",
    "docs-next/pir/fiat-shamir.md":
        "f3a8b2a13f16528101cf4894262c187bcb89ace695f9ca290b29bab63c7f3c0f",
    "docs-next/pir/interfaces-and-plans.md":
        "e3888d7d2ba6c84ceafdf457255a02079b13d95af4f94fce8a6d3c7e8ae6041c",
    "docs-next/pir/verifier-derived-query-plans.md":
        "9c27ad452e83b264bf63c2b744f5ab29e5d8d72488c7a4a93e77598a2759d651",
    (
        "docs-next/notes/semantic-revalidation-and-redesign/"
        "post-freeze-research-program/README.md"
    ): "efc7d1df95808dd1ea91db02710a2b54fa0c1e1c89fba50d6da2a470c798eb67",
}

PRIVATE_PEER_REVIEW_PIN = (
    "f188af14e170ff98d6cce45cca5b5f1b8019b65c9ecb699c136845ab0df35c2d"
)
KINDS = {"constructor", "reopening_condition", "explicit_boundary"}
CARDINALITIES = {"one", "one_or_more"}
VERDICTS = {"fits", "bends", "breaks"}


class MatrixError(ValueError):
    """The frozen matrix is malformed or incomplete."""


def _reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise MatrixError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicates
        )
    except (OSError, json.JSONDecodeError, MatrixError) as exc:
        raise MatrixError(f"cannot load {path.relative_to(ROOT)}: {exc}") from exc
    if not isinstance(value, dict):
        raise MatrixError(f"{path.relative_to(ROOT)}: top level must be an object")
    return value


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest_path(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return digest_bytes(encoded)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise MatrixError(message)


def validate_axes(axes_doc: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    _require(axes_doc.get("schema_version") == 1, "axes: unsupported schema_version")
    _require(isinstance(axes_doc.get("question"), str), "axes: missing exact question")
    _require(set(axes_doc.get("verdicts", [])) == VERDICTS, "axes: verdict set drift")

    destinations_raw = axes_doc.get("destinations")
    axes_raw = axes_doc.get("axes")
    _require(isinstance(destinations_raw, list), "axes: destinations must be a list")
    _require(isinstance(axes_raw, list), "axes: axes must be a list")

    destinations: dict[str, Any] = {}
    for destination in destinations_raw:
        _require(isinstance(destination, dict), "axes: destination must be an object")
        identifier = destination.get("id")
        _require(isinstance(identifier, str) and identifier, "axes: destination id missing")
        _require(identifier not in destinations, f"axes: duplicate destination {identifier}")
        _require(destination.get("kind") in KINDS, f"axes: bad kind for {identifier}")
        for field in ("page", "section", "summary"):
            _require(
                isinstance(destination.get(field), str) and destination[field],
                f"axes: {identifier} missing {field}",
            )
        page = ROOT / destination["page"]
        _require(page.is_file(), f"axes: {identifier} page does not exist")
        section_match = re.search(r"\b(\d+(?:\.\d+)?)\b", destination["section"])
        _require(section_match is not None, f"axes: {identifier} section has no number")
        heading = re.compile(
            rf"^#{{2,6}}\s+{re.escape(section_match.group(1))}(?:\.|\s)", re.MULTILINE
        )
        _require(
            heading.search(page.read_text(encoding="utf-8")) is not None,
            f"axes: {identifier} section is not present in {destination['page']}",
        )
        destinations[identifier] = destination

    axes: dict[str, Any] = {}
    for axis in axes_raw:
        _require(isinstance(axis, dict), "axes: axis must be an object")
        identifier = axis.get("id")
        _require(isinstance(identifier, str) and identifier, "axes: axis id missing")
        _require(identifier not in axes, f"axes: duplicate axis {identifier}")
        _require(axis.get("cardinality") in CARDINALITIES, f"axes: bad cardinality {identifier}")
        _require(isinstance(axis.get("title"), str), f"axes: {identifier} title missing")
        values_raw = axis.get("values")
        _require(isinstance(values_raw, list) and values_raw, f"axes: {identifier} values missing")
        values: dict[str, str] = {}
        for value in values_raw:
            _require(isinstance(value, dict), f"axes: {identifier} value must be object")
            value_id = value.get("id")
            destination_id = value.get("destination")
            _require(isinstance(value_id, str) and value_id, f"axes: {identifier} value id missing")
            _require(value_id not in values, f"axes: duplicate value {identifier}.{value_id}")
            _require(
                isinstance(destination_id, str) and destination_id in destinations,
                f"axes: {identifier}.{value_id} has unknown destination",
            )
            _require(
                isinstance(value.get("meaning"), str) and value["meaning"],
                f"axes: {identifier}.{value_id} meaning missing",
            )
            values[value_id] = destination_id
        axes[identifier] = {
            "cardinality": axis["cardinality"],
            "values": values,
        }

    _require(set(axes) == EXPECTED_AXES, "axes: required structural axis set drift")
    return destinations, axes


def validate_source_sets(cases_doc: dict[str, Any]) -> None:
    source_sets = cases_doc.get("source_sets")
    _require(isinstance(source_sets, dict), "cases: source_sets missing")
    for source_id in ("portfolio", "holdout_adjudication"):
        source = source_sets.get(source_id)
        _require(isinstance(source, dict), f"cases: source set {source_id} missing")
        path = ROOT / str(source.get("path", ""))
        _require(path.is_file(), f"cases: source set {source_id} path missing")
        _require(
            source.get("sha256") == digest_path(path),
            f"cases: source set {source_id} digest drift",
        )

    peer = source_sets.get("peer_review_map")
    _require(isinstance(peer, dict), "cases: peer review source set missing")
    _require(peer.get("distributed") is False, "cases: private peer map must be marked undistributed")
    _require(
        peer.get("sha256") == PRIVATE_PEER_REVIEW_PIN,
        "cases: private peer review extraction pin drift",
    )
    _require(
        isinstance(peer.get("frozen_extract"), str) and peer["frozen_extract"],
        "cases: private peer review frozen-extract description missing",
    )


def validate_owner_pins() -> None:
    for relative, expected in OWNER_PINS.items():
        path = ROOT / relative
        _require(path.is_file(), f"owner pin missing: {relative}")
        _require(digest_path(path) == expected, f"owner pin drift: {relative}")


def derive_case(
    case: dict[str, Any],
    axis_order: list[str],
    axes: dict[str, Any],
    destinations: dict[str, Any],
) -> tuple[str, list[str]]:
    vector = case.get("feature_vector")
    _require(isinstance(vector, list), f"{case.get('id')}: feature_vector missing")
    _require(len(vector) == len(axis_order), f"{case.get('id')}: feature_vector length drift")

    selected_destinations: set[str] = set()
    for axis_id, selected in zip(axis_order, vector, strict=True):
        axis = axes[axis_id]
        if axis["cardinality"] == "one":
            _require(isinstance(selected, str), f"{case.get('id')}: {axis_id} must select one value")
            values = [selected]
        else:
            _require(
                isinstance(selected, list) and selected,
                f"{case.get('id')}: {axis_id} must select one or more values",
            )
            _require(
                all(isinstance(value, str) for value in selected),
                f"{case.get('id')}: {axis_id} contains a non-string value",
            )
            _require(
                selected == sorted(set(selected)),
                f"{case.get('id')}: {axis_id} values are not canonical",
            )
            values = selected
        for value in values:
            _require(value in axis["values"], f"{case.get('id')}: unknown {axis_id}.{value}")
            selected_destinations.add(axis["values"][value])

    boundaries = sorted(
        destination_id
        for destination_id in selected_destinations
        if destinations[destination_id]["kind"] == "explicit_boundary"
    )
    reopenings = sorted(
        destination_id
        for destination_id in selected_destinations
        if destinations[destination_id]["kind"] == "reopening_condition"
    )
    if boundaries:
        return "breaks", boundaries
    if reopenings:
        return "bends", reopenings
    return "fits", []


def validate_cases(
    cases_doc: dict[str, Any],
    axes: dict[str, Any],
    destinations: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, tuple[str, list[str]]]]:
    _require(cases_doc.get("schema_version") == 1, "cases: unsupported schema_version")
    validate_source_sets(cases_doc)
    axis_order = cases_doc.get("axis_order")
    _require(isinstance(axis_order, list), "cases: axis_order missing")
    _require(axis_order == list(axes), "cases: axis_order must equal axes.json order")

    cases = cases_doc.get("cases")
    _require(isinstance(cases, list) and cases, "cases: case list missing")
    seen: set[str] = set()
    derived: dict[str, tuple[str, list[str]]] = {}
    portfolio_ids: set[str] = set()
    peer_rows: set[str] = set()
    unseen_classes: set[str] = set()

    for case in cases:
        _require(isinstance(case, dict), "cases: case must be an object")
        case_id = case.get("id")
        _require(isinstance(case_id, str) and case_id, "cases: case id missing")
        _require(case_id not in seen, f"cases: duplicate case {case_id}")
        seen.add(case_id)
        _require(isinstance(case.get("name"), str) and case["name"], f"{case_id}: name missing")
        coverage = case.get("coverage")
        _require(
            isinstance(coverage, list) and coverage == sorted(set(coverage)),
            f"{case_id}: coverage is not canonical",
        )
        source_refs = case.get("source_refs")
        _require(isinstance(source_refs, list) and source_refs, f"{case_id}: source_refs missing")
        for source_ref in source_refs:
            _require(isinstance(source_ref, dict), f"{case_id}: bad source ref")
            if source_ref.get("kind") == "primary":
                _require(
                    isinstance(source_ref.get("url"), str)
                    and source_ref["url"].startswith("https://")
                    and isinstance(source_ref.get("coordinate"), str)
                    and source_ref["coordinate"],
                    f"{case_id}: incomplete primary source ref",
                )
            else:
                _require(
                    source_ref.get("set") in cases_doc["source_sets"]
                    and isinstance(source_ref.get("coordinate"), str)
                    and source_ref["coordinate"],
                    f"{case_id}: incomplete repository source ref",
                )

        if "unconsidered" in coverage:
            _require(
                any(ref.get("kind") == "primary" for ref in source_refs),
                f"{case_id}: unconsidered case lacks a primary source",
            )
        portfolio_id = case.get("portfolio_id")
        if portfolio_id is not None:
            _require(isinstance(portfolio_id, str), f"{case_id}: bad portfolio_id")
            portfolio_ids.add(portfolio_id)
        for row in case.get("peer_review_rows", []):
            _require(isinstance(row, str), f"{case_id}: bad peer review row")
            peer_rows.add(row)
        for unseen in case.get("unconsidered_classes", []):
            _require(isinstance(unseen, str), f"{case_id}: bad unconsidered class")
            unseen_classes.add(unseen)

        derived[case_id] = derive_case(case, axis_order, axes, destinations)

        predicted = case.get("predicted_verdict")
        predicted_destinations = case.get("predicted_destinations")
        _require(predicted in VERDICTS, f"{case_id}: bad predicted verdict")
        _require(
            isinstance(predicted_destinations, list)
            and predicted_destinations == sorted(set(predicted_destinations)),
            f"{case_id}: predicted destinations are not canonical",
        )
        for recorded in case.get("recorded_verdicts", []):
            _require(isinstance(recorded, dict), f"{case_id}: bad recorded verdict")
            _require(
                recorded.get("set") in {"holdout_adjudication", "peer_review_map"},
                f"{case_id}: bad recorded-verdict source",
            )
            _require(
                isinstance(recorded.get("recorded"), str) and recorded["recorded"],
                f"{case_id}: recorded label missing",
            )
            _require(
                recorded.get("projected_verdict") in VERDICTS,
                f"{case_id}: bad recorded projection",
            )
            required = recorded.get("required_destinations")
            _require(
                isinstance(required, list) and required == sorted(set(required)),
                f"{case_id}: recorded destinations are not canonical",
            )

    required = cases_doc.get("required_coverage")
    _require(isinstance(required, dict), "cases: required_coverage missing")
    _require(
        portfolio_ids == set(required.get("portfolio_ids", [])),
        "cases: portfolio census mismatch",
    )
    _require(
        peer_rows == set(required.get("peer_review_rows", [])),
        "cases: peer review census mismatch",
    )
    _require(
        unseen_classes == set(required.get("unconsidered_classes", [])),
        "cases: unconsidered-class census mismatch",
    )
    return cases, derived


def disagreements(
    cases: list[dict[str, Any]],
    derived: dict[str, tuple[str, list[str]]],
) -> tuple[list[str], list[str], list[str]]:
    predictions: list[str] = []
    holdouts: list[str] = []
    peers: list[str] = []
    for case in cases:
        case_id = case["id"]
        verdict, destination_ids = derived[case_id]
        if (
            case["predicted_verdict"] != verdict
            or case["predicted_destinations"] != destination_ids
        ):
            predictions.append(
                f"{case_id}: frozen={case['predicted_verdict']}/{case['predicted_destinations']} "
                f"derived={verdict}/{destination_ids}"
            )
        for recorded in case.get("recorded_verdicts", []):
            if (
                recorded["projected_verdict"] != verdict
                or recorded["required_destinations"] != destination_ids
            ):
                message = (
                    f"{case_id}: recorded={recorded['recorded']} projected="
                    f"{recorded['projected_verdict']}/{recorded['required_destinations']} "
                    f"derived={verdict}/{destination_ids}"
                )
                if recorded["set"] == "holdout_adjudication":
                    holdouts.append(message)
                else:
                    peers.append(message)
    return predictions, holdouts, peers


def expect_rejected(
    axes_doc: dict[str, Any], cases_doc: dict[str, Any], mutation: str
) -> None:
    try:
        destinations, axes = validate_axes(axes_doc)
        validate_cases(cases_doc, axes, destinations)
    except MatrixError:
        return
    raise MatrixError(f"mutation was accepted: {mutation}")


def run_mutation_checks(axes_doc: dict[str, Any], cases_doc: dict[str, Any]) -> int:
    count = 0

    mutated = copy.deepcopy(axes_doc)
    mutated["axes"][0]["values"][0]["destination"] = "C-DOES-NOT-EXIST"
    expect_rejected(mutated, cases_doc, "unknown destination")
    count += 1

    mutated = copy.deepcopy(cases_doc)
    mutated["cases"][0]["feature_vector"].pop()
    expect_rejected(axes_doc, mutated, "short feature vector")
    count += 1

    mutated = copy.deepcopy(cases_doc)
    mutated["cases"][0]["feature_vector"][0] = "unknown_party_shape"
    expect_rejected(axes_doc, mutated, "unknown axis value")
    count += 1

    mutated = copy.deepcopy(cases_doc)
    mutated["cases"][4]["feature_vector"][16] = ["setup_generator", "public_environment"]
    expect_rejected(axes_doc, mutated, "noncanonical multivalue order")
    count += 1

    destinations, axes = validate_axes(axes_doc)
    mutated = copy.deepcopy(cases_doc)
    mutated["cases"][0]["predicted_verdict"] = "breaks"
    cases, derived = validate_cases(mutated, axes, destinations)
    prediction_errors, _, _ = disagreements(cases, derived)
    _require(bool(prediction_errors), "mutation was accepted: predicted verdict substitution")
    count += 1

    mutated = copy.deepcopy(cases_doc)
    recorded_case = next(case for case in mutated["cases"] if case.get("recorded_verdicts"))
    recorded_case["recorded_verdicts"][0]["projected_verdict"] = "breaks"
    cases, derived = validate_cases(mutated, axes, destinations)
    _, holdout_errors, peer_errors = disagreements(cases, derived)
    _require(
        bool(holdout_errors or peer_errors),
        "mutation was accepted: recorded-verdict substitution",
    )
    count += 1
    return count


def finding(name: str, outcome: str, code: str, detail: Any) -> dict[str, Any]:
    return {"name": name, "outcome": outcome, "code": code, "detail": detail}


def evaluate(axes_doc: dict[str, Any], cases_doc: dict[str, Any]) -> dict[str, Any]:
    validate_owner_pins()
    destinations, axes = validate_axes(axes_doc)
    cases, derived = validate_cases(cases_doc, axes, destinations)
    mutation_count = run_mutation_checks(axes_doc, cases_doc)
    prediction_errors, holdout_errors, peer_errors = disagreements(cases, derived)

    boundary_destinations = sorted(
        destination_id
        for destination_id, destination in destinations.items()
        if destination["kind"] == "explicit_boundary"
    )
    reopening_destinations = sorted(
        destination_id
        for destination_id, destination in destinations.items()
        if destination["kind"] == "reopening_condition"
    )
    portfolio_ids = sorted({case["portfolio_id"] for case in cases if "portfolio_id" in case})
    peer_rows = sorted(
        {row for case in cases for row in case.get("peer_review_rows", [])}
    )
    unseen = sorted(
        {item for case in cases for item in case.get("unconsidered_classes", [])}
    )
    primary_case_count = sum(
        1
        for case in cases
        if "unconsidered" in case["coverage"]
        and any(ref.get("kind") == "primary" for ref in case["source_refs"])
    )
    holdout_record_count = sum(
        record.get("set") == "holdout_adjudication"
        for case in cases
        for record in case.get("recorded_verdicts", [])
    )
    peer_record_count = sum(
        record.get("set") == "peer_review_map"
        for case in cases
        for record in case.get("recorded_verdicts", [])
    )

    findings = [
        finding(
            "axis-schema-closure",
            "Affirmative",
            "RA-A-AXIS-SCHEMA-CLOSED",
            {"axes": len(axes), "values": sum(len(axis["values"]) for axis in axes.values())},
        ),
        finding(
            "destination-totality",
            "Affirmative",
            "RA-A-DESTINATIONS-TOTAL",
            {"destinations": len(destinations), "kinds": sorted(KINDS)},
        ),
        finding(
            "authority-coordinate-resolution",
            "Affirmative",
            "RA-A-AUTHORITY-COORDINATES",
            {"resolved_destinations": len(destinations)},
        ),
        finding(
            "owner-source-pins",
            "Affirmative",
            "RA-A-OWNER-SOURCE-PINS",
            {"pins": len(OWNER_PINS)},
        ),
        finding(
            "case-matrix-totality",
            "Affirmative",
            "RA-A-CASE-MATRIX-TOTAL",
            {"cases": len(cases), "cells": len(cases) * len(axes)},
        ),
        finding(
            "portfolio-census",
            "Affirmative",
            "RA-A-PORTFOLIO-CENSUS",
            {"portfolio_ids": portfolio_ids},
        ),
        finding(
            "peer-map-census",
            "Affirmative",
            "RA-A-PEER-MAP-CENSUS",
            {"rows": peer_rows, "records": peer_record_count},
        ),
        finding(
            "unconsidered-class-census",
            "Affirmative",
            "RA-A-UNCONSIDERED-CENSUS",
            {"classes": unseen, "cases_with_primary_sources": primary_case_count},
        ),
        finding(
            "primary-source-citations",
            "Affirmative",
            "RA-A-PRIMARY-SOURCES-PINNED",
            {"cited_unconsidered_cases": primary_case_count},
        ),
        finding(
            "derived-prediction-agreement",
            "Affirmative" if not prediction_errors else "CannotAnswer",
            "RA-A-DERIVED-PREDICTIONS" if not prediction_errors else "RA-C-DERIVED-PREDICTION-DISAGREEMENT",
            {"disagreements": prediction_errors},
        ),
        finding(
            "recorded-holdout-agreement",
            "Affirmative" if not holdout_errors else "CannotAnswer",
            "RA-A-HOLDOUT-ADJUDICATION" if not holdout_errors else "RA-C-HOLDOUT-ADJUDICATION-DISAGREEMENT",
            {"records": holdout_record_count, "disagreements": holdout_errors},
        ),
        finding(
            "recorded-peer-review-agreement",
            "Affirmative" if not peer_errors else "CannotAnswer",
            "RA-A-PEER-REVIEW-MAP" if not peer_errors else "RA-C-PEER-REVIEW-DISAGREEMENT",
            {"records": peer_record_count, "disagreements": peer_errors},
        ),
        finding(
            "mutation-refusals",
            "Affirmative",
            "RA-A-MUTATIONS-REFUSED",
            {"mutations": mutation_count},
        ),
        finding(
            "boundary-destination-census",
            "Affirmative",
            "RA-A-BOUNDARIES-ENUMERATED",
            {
                "explicit_boundaries": boundary_destinations,
                "reopening_conditions": reopening_destinations,
            },
        ),
        finding(
            "universal-expressibility",
            "CannotAnswer",
            "RA-C-UNIVERSAL-EXPRESSIBILITY",
            "A closed authored vocabulary and finite cited case set do not prove completeness for every protocol.",
        ),
        finding(
            "source-protocol-correspondence",
            "CannotAnswer",
            "RA-C-SOURCE-CORRESPONDENCE",
            "Feature vectors are reviewed source readings, not machine-checked paper-to-PIR correspondence.",
        ),
        finding(
            "cryptographic-properties",
            "CannotAnswer",
            "RA-C-CRYPTOGRAPHIC-PROPERTIES",
            "Structural placement does not establish soundness, knowledge, zero knowledge, Fiat-Shamir security, or implementation support.",
        ),
    ]

    disagreement_count = len(prediction_errors) + len(holdout_errors) + len(peer_errors)
    if disagreement_count:
        aggregate = "RA-C-RECORDED-VERDICT-DISAGREEMENT"
        aggregate_outcome = "CannotAnswer"
    else:
        aggregate = "RA-A-AXES-CLOSED-AND-DERIVED"
        aggregate_outcome = "Affirmative"
    findings.append(
        finding(
            "expressibility-axes",
            aggregate_outcome,
            aggregate,
            {
                "cases": len(cases),
                "disagreements": disagreement_count,
                "rule": "boundary > reopening condition > constructor",
            },
        )
    )
    return {
        "aggregate": aggregate,
        "question": axes_doc["question"],
        "findings": findings,
        "findings_sha256": canonical_digest(findings),
    }


def expected_projection(report: dict[str, Any]) -> dict[str, Any]:
    return {
        "aggregate": report["aggregate"],
        "findings_sha256": report["findings_sha256"],
        "finding_codes": [
            [item["name"], item["outcome"], item["code"]]
            for item in report["findings"]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare with frozen findings")
    parser.add_argument("--json", action="store_true", help="emit the complete JSON report")
    args = parser.parse_args()

    try:
        report = evaluate(load_json(AXES_PATH), load_json(CASES_PATH))
    except MatrixError as exc:
        print(f"CannotAnswer/RA-C-MALFORMED-MATRIX: {exc}", file=sys.stderr)
        return 1

    if args.check:
        try:
            expected = load_json(EXPECTED_PATH)
        except MatrixError as exc:
            print(f"CannotAnswer/RA-C-EXPECTED-FINDINGS: {exc}", file=sys.stderr)
            return 1
        observed = expected_projection(report)
        if observed != expected:
            print("CannotAnswer/RA-C-FROZEN-FINDINGS-MISMATCH", file=sys.stderr)
            print(json.dumps({"expected": expected, "observed": observed}, indent=2), file=sys.stderr)
            return 1

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(f"{report['aggregate']} ({len(report['findings'])} findings)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
