#!/usr/bin/env python3
"""Run the bounded executable-foundation and independent-oracle gates."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parent


def run_suite(path: Path, label: str) -> tuple[int, bool]:
    # A TestLoader retains its first discovery root.  Use a fresh loader and
    # make each non-package test directory its own import root so the second
    # suite cannot inherit the first suite's topology.
    suite = unittest.TestLoader().discover(str(path), top_level_dir=str(path))
    count = suite.countTestCases()
    print(f"Executable foundations {label}: {count} tests")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return count, result.wasSuccessful()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the frozen executable-foundation gate (also the default operation)",
    )
    parser.parse_args(argv)

    reference_count, reference_ok = run_suite(ROOT / "tests", "reference")
    oracle_count, oracle_ok = run_suite(ROOT / "oracle" / "tests", "oracle")
    total = reference_count + oracle_count
    if reference_ok and oracle_ok:
        print(f"Executable foundations: {total}/{total} tests passed")
        return 0
    print("Executable foundations: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
