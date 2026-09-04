#!/usr/bin/env python3
"""Frozen gate for the Q3-A formalization-receipt assurance audit."""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any

from independent import run_mutations
from model import AuditFailure, HERE, canonical_digest, direct_findings, read_json


EXPECTED = HERE / "expected-findings.json"
AGGREGATE = "Q3A-C-OBSERVATION-NOT-AUTHENTICATED-RESULT"


def report() -> dict[str, Any]:
    direct, measurements = direct_findings()
    mutation_results = run_mutations()
    findings = [*direct, *(result.finding for result in mutation_results)]
    finding_codes = [finding.value() for finding in findings]
    outcomes: dict[str, int] = {}
    for finding in findings:
        outcomes[finding.outcome] = outcomes.get(finding.outcome, 0) + 1
    return {
        "aggregate": AGGREGATE,
        "findings_sha256": canonical_digest(finding_codes),
        "finding_codes": finding_codes,
        "measurements": {
            **measurements,
            "black_box_cases": len(mutation_results),
            "accepted_cases": sum(result.accepted for result in mutation_results),
            "refused_cases": sum(not result.accepted for result in mutation_results),
            "outcomes": dict(sorted(outcomes.items())),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with frozen findings")
    parser.add_argument("--json", action="store_true", help="print the complete report")
    args = parser.parse_args()
    try:
        current = report()
        if args.check:
            expected = read_json(EXPECTED)
            if current != expected:
                raise AuditFailure(
                    "frozen findings drift\nexpected: "
                    + json.dumps(expected, sort_keys=True)
                    + "\ncurrent:  "
                    + json.dumps(current, sort_keys=True)
                )
    except AuditFailure as error:
        print(f"formalization-receipt assurance audit failed: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(current, indent=2, sort_keys=True))
    else:
        counts = current["measurements"]["outcomes"]
        print(
            f"{current['aggregate']}: {len(current['finding_codes'])} findings "
            f"({counts.get('Affirmative', 0)} affirmative, "
            f"{counts.get('Refused', 0)} refused, "
            f"{counts.get('CannotAnswer', 0)} cannot-answer)"
        )
        print(
            "bounded result: the pinned reading is reproducible, but the current "
            "path does not mint an independently authenticated Q3 result"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
