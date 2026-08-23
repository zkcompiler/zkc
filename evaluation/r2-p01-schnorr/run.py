#!/usr/bin/env python3
"""Build and independently verify the frozen finite P01 Schnorr report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

from p01model.report import build_report, verify_report


MAX_JSON_INPUT_BYTES = 1 << 20
ERROR_SCHEMA = "zkc.r2.p01.runner-error.v1"
_LOADED_EVALUATION_ROOT = Path(__file__).resolve().parent


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load_json(path: Path) -> Any:
    """Load one bounded JSON value while rejecting duplicate object keys."""

    size = path.stat().st_size
    if size > MAX_JSON_INPUT_BYTES:
        raise ValueError(f"JSON input exceeds the one-megabyte bound: {path}")
    return json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_unique_object,
    )


def _render(value: Any) -> str:
    return json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n"


def _emit_error(kind: str, detail: Any) -> None:
    print(
        _render(
            {
                "schema": ERROR_SCHEMA,
                "error": {"kind": kind, "detail": detail},
            }
        ),
        file=sys.stderr,
        end="",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--check",
        action="store_true",
        help="retained for check-runner symmetry; replay is always checked",
    )
    args = parser.parse_args()

    expectation_path = _LOADED_EVALUATION_ROOT / "cases" / "expected-results.json"
    try:
        expectations = load_json(expectation_path)
        report = build_report(args.repo_root, expectations)
        errors = verify_report(report, args.repo_root, expectations)
    except (OSError, ValueError, RuntimeError, TypeError, KeyError) as error:
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

    if errors or report.get("overall_pass") is not True:
        _emit_error(
            "verification-failure",
            errors or ["not every frozen case expectation matched"],
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
