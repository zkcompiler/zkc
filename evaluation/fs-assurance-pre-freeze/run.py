#!/usr/bin/env python3
"""Run the bounded pre-freeze Fiat--Shamir assurance pressure gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parent


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="run the focused gate")
    parser.parse_args(argv)

    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    count = suite.countTestCases()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    matrix = json.loads(
        (ROOT / "cases" / "attack-matrix.json").read_text(encoding="utf-8")
    )
    print(
        json.dumps(
            {
                "assurance_layers": len(matrix["assurance_layers"]),
                "attack_cases": len(matrix["cases"]),
                "tests": count,
            },
            sort_keys=True,
        )
    )
    if result.wasSuccessful():
        print(f"FS assurance pre-freeze: {count}/{count} tests passed")
        return 0
    print("FS assurance pre-freeze: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
