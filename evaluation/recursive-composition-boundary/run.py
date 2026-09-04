#!/usr/bin/env python3
"""Run the bounded recursive-composition boundary gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import unittest

import reference_model as model


ROOT = Path(__file__).resolve().parent


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="run the focused gate")
    parser.parse_args(argv)

    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"),
        top_level_dir=str(ROOT / "tests"),
    )
    count = suite.countTestCases()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    boundary_matrix = json.loads(
        (ROOT / "cases" / "expected-boundaries.json").read_text(encoding="utf-8")
    )
    report = {
        "boundary_case_count": len(boundary_matrix["cases"]),
        "boundary_case_ids": sorted(item["id"] for item in boundary_matrix["cases"]),
        "canonical_two_run_grounding_equation_id": (
            model.canonical_two_run_recurrence_equation().identity
        ),
        "tests": count,
    }
    print(json.dumps(report, sort_keys=True, indent=2))
    if result.wasSuccessful():
        print(f"Recursive composition boundary validation: {count}/{count} tests passed")
        return 0
    print("Recursive composition boundary validation: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
