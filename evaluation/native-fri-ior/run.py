#!/usr/bin/env python3
"""Build, verify, and optionally compare the frozen public FRI/IOR report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

from friiormodel.fixtures import load_fixture, parse_expected_projection
from friiormodel.report import (
    build_public_report,
    canonical_pretty_json,
    expected_projection,
    verify_public_report,
)
from friiormodel.terms import ModelFailure


DEFAULT_ROOT = Path(__file__).resolve().parents[2]
EXPECTED_PATH = "evaluation/native-fri-ior/cases/expected-results.json"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_public_report(args.root)
        if not verify_public_report(args.root, report):
            raise RuntimeError("public report verification failed")
        if args.check:
            frozen = parse_expected_projection(
                load_fixture(args.root, EXPECTED_PATH, "expected_results").value
            )
            if expected_projection(report) != frozen["projection"]:
                raise RuntimeError(
                    "verified report differs from the expected projection"
                )
        encoded = canonical_pretty_json(report)
        if args.output is None:
            sys.stdout.buffer.write(encoded)
        else:
            args.output.write_bytes(encoded)
        return 0
    except (ModelFailure, OSError, RuntimeError) as error:
        sys.stderr.write(f"public FRI/IOR report failed: {error}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
