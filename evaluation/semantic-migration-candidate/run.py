#!/usr/bin/env python3
"""Run or inspect the non-publishing semantic migration candidate."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import sys
from typing import Any

import independent
import model


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"


class GateError(RuntimeError):
    """The candidate no longer matches its frozen bounded findings."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> dict[str, str]:
        return {"name": self.name, "outcome": self.outcome, "code": self.code}


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise GateError(message)


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    report = model.build_report()
    cold = independent.verify(report)
    rotation = report["rotation"]
    gates = report["f1_gates"]
    alternatives = report["open_alternatives"]
    owner_variants = (
        "algorithm-read-in-owner-view",
        "public-coin-denotation-in-pir",
        "outcome-map-in-owner",
    )
    package_variants = (
        "algorithm-preimage-in-source-package",
        "public-coin-binding-in-analysis",
        "outcome-map-per-analysis-provider",
    )

    checks: list[tuple[str, bool, str]] = [
        ("baseline-publication-agreement", report["compiler_agreement"]["baseline"], "MIGRATION-A-BASELINE-COMPILERS"),
        ("candidate-publication-agreement", report["compiler_agreement"]["candidate"], "MIGRATION-A-CANDIDATE-COMPILERS"),
        ("interaction-rotation-cone", set(rotation["rotated"]) == set(model.COMMON_ROTATION), "MIGRATION-A-ROTATION-16"),
        ("stable-independent-roots", set(rotation["stable"]) == set(model.FOUNDATION_STABLE), "MIGRATION-A-STABLE-2"),
        ("foundation-common-basis", not rotation["foundation_changed"], "MIGRATION-A-FOUNDATION-STABLE"),
        ("exact-owner-page-changes", cold["owner_pages"] == 6, "MIGRATION-A-OWNER-PAGES"),
        ("exact-manifest-changes", cold["manifest_overrides"] == 7, "MIGRATION-A-MANIFESTS"),
        ("old-rotated-profile-refusal", report["old_profile_refusal"]["rotated_rows_are_unequal"], "MIGRATION-R-OLD-PROFILES"),
        ("old-stable-profile-control", report["old_profile_refusal"]["stable_rows_are_equal"], "MIGRATION-A-STABLE-CONTROL"),
        ("published-table-not-written", report["old_profile_refusal"]["published_identity_file_unchanged"], "MIGRATION-A-NO-PUBLICATION-WRITE"),
        ("endpoint-terminal-projection", cold["endpoint_terminal_controls"] == 4, "MIGRATION-A-ENDPOINT-TERMINAL"),
        ("migrated-r1a", gates["r1a"]["outcome"] == "Affirmative", "MIGRATION-A-R1A"),
        ("migrated-r1b-core", gates["r1b"]["core"]["outcome"] == "Affirmative", "MIGRATION-A-R1B-CORE"),
        ("migrated-r1b-protocol", gates["r1b"]["protocol"]["outcome"] == "Affirmative", "MIGRATION-A-R1B-PROTOCOL"),
        ("old-terminal-carrier-refusal", gates["r1b"]["old_terminal_bytes_refused"], "MIGRATION-R-OLD-TERMINAL"),
        ("migrated-r1c0-catalog", len(gates["r1c0"]["schema_catalog_entries"]) == 6, "MIGRATION-A-R1C0-CATALOG"),
        ("migrated-r1c0-authority-routes", len(gates["r1c0"]["split_source_routes"]) == 6, "MIGRATION-A-R1C0-ROUTES"),
        ("owner-alternative-identities", len({alternatives[key]["interaction_digest"] for key in owner_variants}) == 3, "MIGRATION-A-OWNER-ALTERNATIVES"),
        ("package-alternatives-preserve-pir", all(not alternatives[key]["target_profile_rotation"] for key in package_variants), "MIGRATION-A-PACKAGE-ALTERNATIVES"),
        ("active-lane-slots", cold["integration_slots"] == 5, "MIGRATION-A-INTEGRATION-SLOTS"),
    ]
    for name, condition, code in checks:
        _require(condition, f"{name} failed")

    findings = [Finding(name, "Affirmative", code) for name, _condition, code in checks]
    findings.extend(
        (
            Finding("foundation-byte-bound-selection", "CannotAnswer", "MIGRATION-C-M1-BOUNDARY"),
            Finding("provider-observable-ownership", "CannotAnswer", "MIGRATION-C-PROVIDER-OWNERSHIP"),
            Finding("target-publication", "Hold", "MIGRATION-H-NO-PUBLICATION"),
        )
    )
    metrics = {
        "findings": len(findings),
        "profiles": len(report["candidate_identity_table"]["profiles"]),
        "rotated_profiles": rotation["count"],
        "stable_profiles": len(rotation["stable"]),
        "owner_pages": cold["owner_pages"],
        "manifest_overrides": cold["manifest_overrides"],
        "open_alternatives": cold["alternatives"],
        "integration_slots": cold["integration_slots"],
        "endpoint_terminal_controls": cold["endpoint_terminal_controls"],
        "interaction_digest": report["candidate_identity_table"]["profiles"]["interaction"]["profile_digest"],
        "aggregate": "MIGRATION-H-NO-PUBLICATION",
    }
    return findings, {"metrics": metrics, "report": report, "independent": cold}


def _expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateError(f"cannot read expected findings: {error}") from error
    if not isinstance(value, dict):
        raise GateError("expected findings have another carrier")
    return value


def check() -> dict[str, Any]:
    findings, evidence = evaluate()
    expected = _expected()
    observed = [item.value() for item in findings]
    _require(observed == expected["cases"], "finding classification drifted")
    for key, value in expected["metrics"].items():
        _require(evidence["metrics"].get(key) == value, f"metric {key} drifted")
    return {"findings": observed, **evidence}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--print-patches", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.check:
            result = check()
        else:
            findings, evidence = evaluate()
            result = {"findings": [item.value() for item in findings], **evidence}
    except (GateError, model.CandidateError, independent.IndependentError) as error:
        print(f"semantic migration candidate failed: {error}", file=sys.stderr)
        return 1
    if args.print_patches:
        changes = result["report"]["exact_changes"]
        for row in (*changes["pages"], *changes["manifests"]):
            print(row["unified_diff"], end="")
        return 0
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    metrics = result["metrics"]
    print(
        "Semantic migration candidate: "
        f"{len(result['findings'])}/{len(result['findings'])} findings matched; "
        f"{metrics['rotated_profiles']} profiles rotate; disposition Hold"
    )
    print(f"  candidate Interaction digest: {metrics['interaction_digest']}")
    print("  publication: not performed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
