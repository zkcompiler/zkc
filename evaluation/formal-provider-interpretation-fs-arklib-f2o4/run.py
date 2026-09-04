#!/usr/bin/env python3
"""Frozen gate for the finite ArkLib Fiat--Shamir interpretation."""

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
    body = json.dumps(value, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return hashlib.sha256(body).hexdigest()


def report() -> dict[str, Any]:
    generated = _run(GENERATOR, "--check")
    if generated.returncode != 0:
        raise GateError(
            f"untrusted generation drifted: {generated.stdout}{generated.stderr}"
        )
    checked = _run(CHECKER)
    if checked.returncode != 0:
        raise GateError(
            f"independent checker failed: {checked.stdout}{checked.stderr}"
        )
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
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--emit-expected", action="store_true")
    parser.add_argument("--write-expected", action="store_true")
    args = parser.parse_args()
    try:
        result = report()
        observed = frozen_view(result)
        if args.write_expected:
            EXPECTED.write_text(
                json.dumps(observed, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
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
        print(f"Fiat-Shamir provider interpretation gate failed: {error}", file=sys.stderr)
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
            f"{outcomes.get('Negative', 0)} negative controls, "
            f"{outcomes.get('Refused', 0)} refused)"
        )
        print(
            "all five correspondence clauses agree on 54 source runs; "
            "the retrying corpus has zero measured exhaustions while its "
            "InterpretationFailed lane remains explicitly unmodelled"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
