#!/usr/bin/env python3
"""Run the checked finite-cover Analysis gate."""

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
        help="run the bounded gate (also the default operation)",
    )
    parser.parse_args(argv)
    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    count = suite.countTestCases()
    print(f"Checked finite-cover Analysis: {count} tests")
    successful = unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful()
    if successful:
        print(f"Checked finite-cover Analysis: {count}/{count} tests passed")
        return 0
    print("Checked finite-cover Analysis: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
