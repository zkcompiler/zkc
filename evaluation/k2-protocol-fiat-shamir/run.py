#!/usr/bin/env python3
"""Run the bounded interactive-protocol and Fiat--Shamir reference gate."""

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
        help="run the frozen protocol and Fiat--Shamir gate (also the default operation)",
    )
    parser.parse_args(argv)
    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    count = suite.countTestCases()
    print(f"Interactive protocol and Fiat-Shamir: {count} tests")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if result.wasSuccessful():
        print(f"Interactive protocol and Fiat-Shamir: {count}/{count} tests passed")
        return 0
    print("Interactive protocol and Fiat-Shamir: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
