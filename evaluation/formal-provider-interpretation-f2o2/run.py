#!/usr/bin/env python3
"""Frozen gate for the finite Schnorr VCVio interpretation."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
GENERATOR = HERE / "generator.py"
CHECKER = HERE / "checker.py"
EXPECTED = HERE / "expected-findings.json"


class GateError(RuntimeError):
    """Generation, independent checking, or frozen comparison failed."""


def _run(path: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-B", str(path), *arguments],
        cwd=HERE.parents[1],
        check=False,
        capture_output=True,
        text=True,
    )


def _digest(value: Any) -> str:
    body = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(body).hexdigest()


def report() -> dict[str, Any]:
    generated = _run(GENERATOR, "--check")
    if generated.returncode != 0:
        raise GateError(f"untrusted generation drifted: {generated.stdout}{generated.stderr}")
    checked = _run(CHECKER)
    if checked.returncode != 0:
        raise GateError(f"independent checker failed: {checked.stdout}{checked.stderr}")
    try:
        result = json.loads(checked.stdout)
    except json.JSONDecodeError as error:
        raise GateError("independent checker returned non-JSON output") from error
    result["findings_sha256"] = _digest(result["finding_codes"])
    return result


def frozen_view(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "aggregate": result["aggregate"],
        "finding_codes": result["finding_codes"],
        "findings_sha256": result["findings_sha256"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare frozen findings")
    parser.add_argument("--json", action="store_true", help="print the full report")
    parser.add_argument("--emit-expected", action="store_true", help="print the frozen view")
    args = parser.parse_args()
    try:
        result = report()
        observed = frozen_view(result)
        if args.check:
            expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
            if observed != expected:
                raise GateError(
                    "frozen findings drift\nexpected: "
                    + json.dumps(expected, sort_keys=True)
                    + "\nobserved: "
                    + json.dumps(observed, sort_keys=True)
                )
    except (GateError, OSError, KeyError, json.JSONDecodeError) as error:
        print(f"provider interpretation gate failed: {error}", file=sys.stderr)
        return 1
    if args.emit_expected:
        print(json.dumps(observed, indent=2, sort_keys=True))
    elif args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        outcomes: dict[str, int] = {}
        for _name, outcome, _code in result["finding_codes"]:
            outcomes[outcome] = outcomes.get(outcome, 0) + 1
        print(
            f"{result['aggregate']}: {len(result['finding_codes'])} findings "
            f"({outcomes.get('Affirmative', 0)} affirmative, "
            f"{outcomes.get('CannotAnswer', 0)} cannot-answer)"
        )
        print(
            "all five correspondence clauses agree on their complete finite "
            "domains; the provider map remains a package input until Analysis "
            "publishes its declaration"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
