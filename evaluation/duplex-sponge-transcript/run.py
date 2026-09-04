#!/usr/bin/env python3
"""Build, verify, and compare the public duplex-transition report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

from duplexmodel.diagnostics import DuplexModelError
from duplexmodel.provenance import load_fixture
from duplexmodel.report import (
    EXPECTED_PATH,
    build_report,
    expected_projection,
    verify_report,
)
from duplexmodel.terms import canonical_json_text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parents[2]
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "strictly rebuild and compare the separately frozen projection; "
            "plain mode only builds and emits"
        ),
    )
    args = parser.parse_args()
    try:
        report = build_report(args.repo_root)
        errors: list[str] = []
        if args.check:
            # The expected projection is deliberately unopened until the
            # public report has been constructed and strictly rebuilt.
            errors = verify_report(report, args.repo_root)
            expected = load_fixture(
                args.repo_root,
                EXPECTED_PATH,
                role="post-build-expected-public-projection",
            ).value
            if expected != expected_projection(report):
                errors.append("post-build expected projection differs")
    except (DuplexModelError, OSError, TypeError, ValueError) as error:
        print(f"duplex transcript runner failure: {error}", file=sys.stderr)
        return 1
    rendered = canonical_json_text(report, pretty=True)
    try:
        if args.output is None:
            print(rendered, end="")
        else:
            args.output.write_text(rendered, encoding="utf-8")
    except OSError as error:
        print(f"duplex transcript output failure: {error}", file=sys.stderr)
        return 1
    if errors:
        for error in errors:
            print(f"duplex transcript verification failure: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
