#!/usr/bin/env python3
"""Run the direct, non-publishing semantic refreeze rehearsal."""

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
    """The direct-source rehearsal differs from its frozen observations."""


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
    publication = report["publication"]
    gates = report["prerequisite_gates"]
    owner_aggregate = gates["owner_views"]["aggregate"]

    checks: list[tuple[str, bool, str]] = [
        (
            "direct-owner-source-pins",
            cold["owner_pages"] == 6 and cold["profile_manifests"] == 8,
            "MIGRATION-A-DIRECT-SOURCES",
        ),
        (
            "current-publication-compiler-agreement",
            publication["compiler_agreement"],
            "MIGRATION-A-CURRENT-COMPILERS",
        ),
        (
            "seventeen-profile-rotation",
            cold["migration_rotated_profiles"] == 17,
            "MIGRATION-A-ROTATION-17",
        ),
        (
            "analysis-kernel-stability-control",
            publication["migration_stable_profiles"] == ["analysis-kernel"],
            "MIGRATION-A-STABLE-CONTROL",
        ),
        (
            "legacy-profile-refusal-controls",
            all(publication["legacy_profile_refusals"].values()),
            "MIGRATION-R-LEGACY-PROFILES",
        ),
        (
            "published-table-not-written",
            report["published_identity_sha256_before"]
            == report["published_identity_sha256_after"],
            "MIGRATION-A-NO-PUBLICATION-WRITE",
        ),
        (
            "target-basis-prerequisite",
            gates["target_basis"]["results"] > 0,
            "MIGRATION-A-TARGET-BASIS",
        ),
        (
            "target-core-prerequisite",
            gates["target_core"]["passed"] == gates["target_core"]["total"],
            "MIGRATION-A-TARGET-CORE",
        ),
        (
            "owner-view-prerequisite-executed",
            gates["owner_views"]["passed"] == gates["owner_views"]["total"],
            "MIGRATION-A-OWNER-VIEW-GATE",
        ),
        (
            "migrated-terminal-contract",
            gates["terminal_contract"]["findings"] == 58,
            "MIGRATION-A-TERMINAL-CONTRACT",
        ),
    ]
    for name, condition, _code in checks:
        _require(condition, f"{name} failed")

    _require(
        owner_aggregate
        == {
            "outcome": "Affirmative",
            "code": "F1R1C-A-SOURCE-DETERMINACY",
        },
        "owner-view source determinacy did not close",
    )

    findings = [Finding(name, "Affirmative", code) for name, _condition, code in checks]
    _require(
        gates["terminal_contract"]["hidden_gating_counterexample"]["violation"]
        == "linear-claim-consumed-twice",
        "hidden-terminal-gating failed",
    )
    findings.append(
        Finding(
            "hidden-terminal-gating",
            "Refused",
            "MIGRATION-R-HIDDEN-GATING",
        )
    )
    findings.append(
        Finding(
            "exact-owner-view-law-binding",
            owner_aggregate["outcome"],
            owner_aggregate["code"],
        )
    )
    findings.append(Finding("identity-publication", "Hold", "MIGRATION-H-NO-PUBLICATION"))
    metrics = {
        "findings": len(findings),
        "profiles": cold["indexed_profiles"],
        "rotated_profiles": cold["rotated_profiles"],
        "stable_profiles": cold["stable_profiles"],
        "migration_rotated_profiles": cold["migration_rotated_profiles"],
        "migration_stable_profiles": cold["migration_stable_profiles"],
        "analysis_branch_rotated_profiles": cold[
            "analysis_branch_rotated_profiles"
        ],
        "owner_pages": cold["owner_pages"],
        "profile_manifests": cold["profile_manifests"],
        "legacy_profile_controls": cold["legacy_profile_controls"],
        "target_core_cases": gates["target_core"]["total"],
        "owner_view_cases": gates["owner_views"]["total"],
        "interaction_digest": publication["candidate_identity_table"]["profiles"][
            "interaction"
        ]["profile_digest"],
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
    args = parser.parse_args(argv)
    try:
        if args.check:
            result = check()
        else:
            findings, evidence = evaluate()
            result = {"findings": [item.value() for item in findings], **evidence}
    except (GateError, model.CandidateError, independent.IndependentError) as error:
        print(f"semantic refreeze rehearsal failed: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    metrics = result["metrics"]
    print(
        "Semantic refreeze rehearsal: "
        f"{len(result['findings'])}/{len(result['findings'])} observations matched; "
        f"{metrics['rotated_profiles']} profiles rotate; publication remains Hold"
    )
    print(f"  candidate Interaction digest: {metrics['interaction_digest']}")
    print("  publication: not performed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
