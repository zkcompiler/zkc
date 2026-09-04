#!/usr/bin/env python3
"""Run the migrated owner-view publication-topology gate."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"


class GateFailure(RuntimeError):
    pass


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise GateFailure(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


model = _load("_zkc_f0v_candidate", HERE / "model.py")
cold = _load("_zkc_f0v_independent", HERE / "independent.py")


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _expect_reference_rejection(candidate: object) -> str:
    try:
        model.observe(candidate)
    except (model.TopologyError, model.publication.PublicationError) as error:
        return f"{type(error).__name__}: {error}"
    except Exception as error:  # pragma: no cover - unexpected implementation bug
        raise GateFailure(
            f"reference path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("reference path accepted a forbidden F0-V1 mutation")


def _expect_cold_rejection(candidate: object) -> str:
    try:
        cold.observe(candidate)
    except (cold.TopologyError, cold.cold.ColdError) as error:
        return f"{type(error).__name__}: {error}"
    except Exception as error:  # pragma: no cover - unexpected implementation bug
        raise GateFailure(
            f"cold path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("cold path accepted a forbidden F0-V1 mutation")


MUTATIONS: tuple[tuple[str, str, str, str], ...] = (
    (
        "missing-schema",
        "missing-owner-schema",
        "F0V1-R-MISSING-SCHEMA",
        "removing one owner schema and its root edge is rejected",
    ),
    (
        "extra-schema",
        "extra-owner-schema",
        "F0V1-R-EXTRA-SCHEMA",
        "adding a seventh reachable owner schema is rejected",
    ),
    (
        "wrong-owner",
        "schema-owner-substitution",
        "F0V1-R-SCHEMA-OWNER",
        "changing a Core view to a Protocol-owned selector is rejected",
    ),
    (
        "wrong-law",
        "schema-law-substitution",
        "F0V1-R-SCHEMA-LAW",
        "changing the PublicCoin derivation dependency is rejected",
    ),
    (
        "common-role-cross-kind",
        "common-role-as-family-body",
        "F0V1-R-CROSS-KIND-COMPILER",
        "a common consumer-role compiler cannot compile a binding payload",
    ),
    (
        "unreachable-extension",
        "unreachable-schema-declaration",
        "F0V1-R-UNREACHABLE-SCHEMA",
        "an authenticated but unreachable schema declaration is rejected",
    ),
    (
        "absent-selector",
        "absent-owner-source-selector",
        "F0V1-R-ABSENT-SELECTOR",
        "a declaration selector absent from authenticated source is rejected",
    ),
    (
        "retained-revision",
        "retained-revision-after-source-change",
        "F0V1-R-RETAINED-REVISION",
        "a locally changed synthetic profile retaining revision zero is rejected",
    ),
    (
        "imported-family-compiler",
        "dependent-family-body-import",
        "F0V1-R-IMPORTED-FAMILY-BODY",
        "a dependent profile cannot import a common role compiler for its payload",
    ),
    (
        "swapped-common-role",
        "consumer-purpose-role-swap",
        "F0V1-R-ROLE-SWAP",
        "consumer and purpose role-body compilers are non-substitutable",
    ),
)


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read frozen F0-V1 findings") from error
    if type(value) is not dict:
        raise GateFailure("frozen F0-V1 findings have the wrong shape")
    return value


def run_gate() -> dict[str, Any]:
    reference_evidence = model.observe()
    cold_evidence = cold.observe()
    if reference_evidence != cold_evidence:
        raise GateFailure(
            "independent publication paths disagree:\n"
            + json.dumps(
                {"reference": reference_evidence, "cold": cold_evidence},
                indent=2,
                sort_keys=True,
            )
        )

    findings = [
        _finding(
            "independent-publication-agreement",
            "Affirmative",
            "F0V1-A-INDEPENDENT-PUBLICATION",
            "two independent compilers agree on all eighteen candidate profiles",
        ),
        _finding(
            "six-entry-owner-schema-catalog",
            "Affirmative",
            "F0V1-A-SCHEMA-CATALOG",
            "Interaction publishes exactly five Core schemas and one Protocol schema",
        ),
        _finding(
            "common-role-local-family-routing",
            "Affirmative",
            "F0V1-A-SOURCE-ROUTING",
            "six repaired profiles share only consumer/purpose and own four family bodies",
        ),
        _finding(
            "exact-rotation-cone",
            "Affirmative",
            "F0V1-A-ROTATION-CONE",
            "the migrated and Analysis text rotates all eighteen indexed profiles",
        ),
        _finding(
            "outside-cone-stability",
            "Affirmative",
            "F0V1-A-OUTSIDE-STABLE",
            "the Analysis-head comparison has no stable profile outside the rotation cone",
        ),
        _finding(
            "changed-profile-revisions",
            "Affirmative",
            "F0V1-A-REVISION-DISCIPLINE",
            "all six locally changed profiles advance their syntax revision",
        ),
        _finding(
            "canonical-view-body-grammar",
            "CannotAnswer",
            "F0V1-C-CANONICAL-GRAMMAR",
            "this topology gate does not re-derive the complete canonical grammar",
        ),
        _finding(
            "proper-subset-read-closure",
            "CannotAnswer",
            "F0V1-C-PARTIAL-CLOSURE",
            "the exact constructor dependency graph remains an F1-R1C2 obligation",
        ),
    ]

    mutation_diagnostics: dict[str, dict[str, str]] = {}
    for mutation, finding_name, code, detail in MUTATIONS:
        mutated = model.mutated_candidate(mutation)
        mutation_diagnostics[mutation] = {
            "reference": _expect_reference_rejection(mutated),
            "cold": _expect_cold_rejection(mutated),
        }
        findings.append(_finding(finding_name, "Refused", code, detail))

    expected = _load_expected()
    observed_cases = [
        {"name": row.name, "outcome": row.outcome, "code": row.code} for row in findings
    ]
    if observed_cases != expected.get("cases"):
        raise GateFailure(
            "F0-V1 finding classification drifted:\n"
            + json.dumps(
                {"expected": expected.get("cases"), "observed": observed_cases},
                indent=2,
            )
        )
    aggregate = {
        "outcome": "Affirmative",
        "code": "F0V1-A-PUBLICATION-TOPOLOGY",
    }
    if aggregate != expected.get("aggregate"):
        raise GateFailure("F0-V1 aggregate disposition drifted")
    frozen_identity = expected.get("interaction_profile_digests")
    observed_identity = {
        "before": reference_evidence["interaction_before"],
        "after": reference_evidence["interaction_after"],
    }
    if observed_identity != frozen_identity:
        raise GateFailure("F0-V1 Interaction profile identity control drifted")

    return {
        "format": "zkc.formal-source-owner-view-repair-f0v1.v0",
        "aggregate": aggregate,
        "cases": [
            {
                "name": row.name,
                "outcome": row.outcome,
                "code": row.code,
                "detail": row.detail,
            }
            for row in findings
        ],
        "evidence": reference_evidence,
        "mutation_diagnostics": mutation_diagnostics,
        "passed": len(findings),
        "total": len(expected["cases"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    try:
        report = run_gate()
    except GateFailure as error:
        print(f"F0-V1 gate failed: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        aggregate = report["aggregate"]
        print(
            f"F0-V1 owner-view repair topology: {report['passed']}/"
            f"{report['total']} findings matched"
        )
        print(f"  aggregate: {aggregate['outcome']}/{aggregate['code']}")
        for row in report["cases"]:
            print(f"  {row['name']}: {row['outcome']}/{row['code']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
