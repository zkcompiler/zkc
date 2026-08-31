#!/usr/bin/env python3
"""Run or inspect the stable PIR semantic-profile publication gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import unittest

import independent
import reference_model


HERE = Path(__file__).resolve().parent


def run_tests() -> bool:
    suite = unittest.defaultTestLoader.discover(
        str(HERE / "tests"),
        pattern="test_*.py",
        top_level_dir=str(HERE),
    )
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return result.wasSuccessful()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-identities", action="store_true")
    args = parser.parse_args(argv)

    reference = reference_model.compile_repository()
    cold = independent.compile_repository()
    reference_table = reference_model.identity_table(reference)
    cold_table = independent.identity_table(cold)
    if reference_table != cold_table:
        print("independent publication compilers disagree", file=sys.stderr)
        return 1
    if args.print_identities:
        print(json.dumps(reference_table, indent=2, sort_keys=False))
        return 0
    if args.check and not run_tests():
        return 1
    print(
        "Semantic profile publication: "
        f"{len(reference.profiles)}/{len(reference_model.PROFILE_KEYS)} profiles "
        "reconstructed by two independent compilers"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
