#!/usr/bin/env python3
"""Run the bounded K3-E integrated-closure research gate."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import time
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
    print(f"K3-E integrated closure: {count} tests")
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    elapsed = time.perf_counter() - started
    if result.wasSuccessful():
        print(
            f"K3-E integrated closure: {count}/{count} tests passed in {elapsed:.3f}s"
        )
        return 0
    print(f"K3-E integrated closure: FAILED after {elapsed:.3f}s", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
