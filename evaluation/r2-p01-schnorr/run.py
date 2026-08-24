#!/usr/bin/env python3
"""Build, verify, and compare P01's public-only Phase B evidence artifact."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any

from p01model.provenance import (
    ProvenanceError,
    canonical_json_text,
    load_public_fixture,
)
from p01model.report import build_report, expected_projection, verify_report


ERROR_SCHEMA = "zkc.r2.p01.runner-error.v2"
_EXPECTED_PATH = "evaluation/r2-p01-schnorr/cases/expected-results.json"


def _render(value: Any) -> str:
    return canonical_json_text(value, pretty=True)


def _emit_error(kind: str, detail: Any) -> None:
    print(
        _render({"schema": ERROR_SCHEMA, "error": {"kind": kind, "detail": detail}}),
        file=sys.stderr,
        end="",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="must be the checkout that loaded this runner",
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "retained for suite symmetry; public rebuild, structural verification, "
            "and post-build frozen-projection comparison always run"
        ),
    )
    args = parser.parse_args()

    try:
        # Complete construction before opening expected results, so the oracle
        # cannot influence case selection, evidence, or report identity.
        report = build_report(args.repo_root)
        errors = verify_report(report, args.repo_root)
        expected_binding = load_public_fixture(
            args.repo_root,
            path=_EXPECTED_PATH,
            role="p01-expected-public-projection",
        )
        expected = expected_binding.value
        actual = expected_projection(report)
        if expected != actual:
            errors.append("post-build expected projection differs")
    except (OSError, ProvenanceError, RuntimeError, TypeError, ValueError) as error:
        _emit_error("runner-failure", str(error))
        return 1

    rendered = _render(report)
    try:
        if args.output is None:
            print(rendered, end="")
        else:
            args.output.write_text(rendered, encoding="utf-8")
    except OSError as error:
        _emit_error("output-failure", str(error))
        return 1

    if errors:
        _emit_error("verification-failure", errors)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
