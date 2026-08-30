#!/usr/bin/env python3
"""Run the bounded Plan continuation semantic evaluator."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import unittest

from fixtures import family_cases
import reference_model as m


ROOT = Path(__file__).resolve().parent


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="run the focused semantic gate")
    parser.parse_args(argv)
    suite = unittest.TestLoader().discover(str(ROOT / "tests"), top_level_dir=str(ROOT / "tests"))
    count = suite.countTestCases()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    matrix = [
        {
            "family": case.name,
            "evidence_depth": case.evidence_depth,
            "continuation_arm": list(case.expected_arm),
            "confidential_source_requirement": case.expected_requirement.value,
            "plan_id": case.plan.identity,
            "continuation_oir_id": m.derive_endpoint_graph(
                case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
            ).identity,
        }
        for case in family_cases()
    ]
    print(json.dumps({"cases": matrix, "tests": count}, sort_keys=True, indent=2))
    if result.wasSuccessful():
        print(f"Plan continuation semantic validation: {count}/{count} tests passed")
        return 0
    print("Plan continuation semantic validation: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
