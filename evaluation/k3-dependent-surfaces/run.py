#!/usr/bin/env python3
"""Run the bounded dependent-surface research gate."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parent


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the frozen bounded gate (also the default operation)",
    )
    parser.parse_args(argv)
    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    count = suite.countTestCases()
    print(f"Dependent Interface, Plan, and Relations surfaces: {count} tests")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if result.wasSuccessful():
        print(
            "Dependent Interface, Plan, and Relations surfaces: "
            f"{count}/{count} tests passed"
        )
        return 0
    print("Dependent Interface, Plan, and Relations surfaces: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
