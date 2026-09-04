#!/usr/bin/env python3
"""Build and verify the canonical repaired R2 FRI-Grind report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

from r2model.report import EXECUTION_ROLES, RELATION_NAMES, build_report, verify_report


EXPECTED_SCHEMA = "zkc.r2.expected-results.v4"


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load(path: Path) -> Any:
    if path.stat().st_size > 1 << 20:
        raise ValueError(f"JSON input exceeds the one-megabyte bound: {path}")
    return json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_unique_object,
    )


def expected_projection(report: dict[str, Any]) -> dict[str, Any]:
    definitions = report["relations"]["definitions"]
    runs = report["relations"]["runs"]
    return {
        "schema": EXPECTED_SCHEMA,
        "semantic_regime_id": report["semantic_regime_id"],
        "replay_basis": report["replay_basis"],
        "semantic_roots": report["semantic_roots"],
        "executions": {
            role: {
                key: report["executions"][role][key]
                for key in (
                    "manifest_id",
                    "request_id",
                    "record_id",
                    "qualification_id",
                )
            }
            for role in EXECUTION_ROLES
        },
        "relations": {
            name: {
                "shape_id": definitions[name]["shape"]["shape_id"],
                "validation_profile_id": definitions[name]["validation_profile"][
                    "profile_id"
                ],
                "run_evidence_id": runs[name]["run_evidence"]["run_evidence_id"],
                "hybrid_factorization_id": runs[name]["hybrid_factorization_id"],
            }
            for name in RELATION_NAMES
        },
        "cases": report["cases"],
        "root_ids": report["root_ids"],
        "report_id": report["report_id"],
    }


def _check_expected(report: dict[str, Any], expected: Any) -> list[str]:
    required = {
        "schema",
        "semantic_regime_id",
        "replay_basis",
        "semantic_roots",
        "executions",
        "relations",
        "cases",
        "root_ids",
        "report_id",
    }
    if not isinstance(expected, dict) or set(expected) != required:
        return ["expected-results keys differ"]
    actual = expected_projection(report)
    errors: list[str] = []
    if expected.get("schema") != EXPECTED_SCHEMA:
        errors.append("expected-results schema differs")
    for key in (
        "semantic_regime_id",
        "replay_basis",
        "semantic_roots",
        "executions",
        "relations",
        "cases",
        "root_ids",
        "report_id",
    ):
        if expected.get(key) != actual[key]:
            errors.append(f"expected-results {key.replace('_', ' ')} differ")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        report = build_report(args.repo_root)
        errors = verify_report(report, args.repo_root)
        if args.check:
            expected = _load(
                Path(__file__).resolve().parent / "cases" / "expected-results.json"
            )
            errors.extend(_check_expected(report, expected))
    except (OSError, ValueError, RuntimeError, TypeError, KeyError) as error:
        print(f"R2 runner failure: {error}", file=sys.stderr)
        return 1
    if errors:
        for error in errors:
            print(f"R2 verification failure: {error}", file=sys.stderr)
        return 1
    rendered = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    if args.check:
        print("R2 expected semantic identities and classifications reproduced", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
