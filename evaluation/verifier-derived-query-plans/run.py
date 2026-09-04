#!/usr/bin/env python3
"""Run the verifier-derived query-plan witness and falsification suite."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import unittest

import independent_oracle


HERE = Path(__file__).resolve().parent


def run_tests() -> bool:
    suite = unittest.defaultTestLoader.discover(
        str(HERE / "tests"), pattern="test_*.py", top_level_dir=str(HERE)
    )
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return result.wasSuccessful()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-independent", action="store_true")
    args = parser.parse_args(argv)
    if args.print_independent:
        print(json.dumps(independent_oracle.evaluate(), indent=2, sort_keys=True))
    if args.check and not run_tests():
        return 1
    if not args.print_independent:
        print("Verifier-derived query plans: checked finite elaboration witness complete")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
