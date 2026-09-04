#!/usr/bin/env python3
"""Audit the diversity of evidence methods declared by repository checks.

The audit is intentionally structural.  It can detect an inventory that relies
on one style of evidence for a whole class of claims; it cannot decide whether
an individual test is well designed or whether its claim is true.
"""

from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Mapping, Sequence
import json
from pathlib import Path
from typing import Any

from checks import run


METHOD_LENSES: Mapping[str, frozenset[str]] = {
    "policy": frozenset(("governance",)),
    "static-analysis": frozenset(("governance",)),
    "unit": frozenset(("example",)),
    "known-answer": frozenset(("example", "relational")),
    "negative": frozenset(("adversarial",)),
    "roundtrip": frozenset(("example", "relational")),
    "differential": frozenset(("relational",)),
    "property": frozenset(("generative",)),
    "metamorphic": frozenset(("relational", "generative")),
    "mutation": frozenset(("adversarial", "generative")),
    "bounded-exhaustive": frozenset(("generative",)),
    "translation-validation": frozenset(("relational",)),
    "fuzz": frozenset(("adversarial", "generative")),
    "sanitizer": frozenset(("adversarial",)),
    "upstream-replay": frozenset(("relational",)),
    "formal-reading": frozenset(("external",)),
    "diagnostic": frozenset(("governance",)),
}

# Each tuple member is an alternative set: at least one lens in each member
# must be present.  These are intentionally low floors, not quality grades.
CLASSIFICATION_FLOORS: Mapping[str, tuple[frozenset[str], ...]] = {
    "control-plane": (
        frozenset(("example",)),
        frozenset(("adversarial",)),
    ),
    "repository-policy": (
        frozenset(("governance",)),
        frozenset(("adversarial",)),
    ),
    "static-quality": (frozenset(("governance",)),),
    "durable-conformance": (
        frozenset(("example",)),
        frozenset(("adversarial",)),
    ),
    "implementation-regression": (
        frozenset(("example",)),
        frozenset(("adversarial",)),
    ),
    "research-falsifier": (
        frozenset(("adversarial",)),
        frozenset(("example", "relational", "generative")),
    ),
    "external-correspondence": (frozenset(("external",)),),
    "diagnostic": (frozenset(("governance",)),),
}


def _lenses(methods: Sequence[str]) -> frozenset[str]:
    return frozenset(
        lens for method in methods for lens in METHOD_LENSES.get(method, ())
    )


def audit(manifest: run.Manifest) -> dict[str, Any]:
    """Return a deterministic, machine-readable portfolio audit."""

    findings: list[dict[str, Any]] = []
    checks: list[dict[str, Any]] = []
    method_counts: Counter[str] = Counter()
    lens_counts: Counter[str] = Counter()

    vocabulary_gap = sorted(set(run.METHODS) ^ set(METHOD_LENSES))
    if vocabulary_gap:
        findings.append(
            {
                "kind": "method-vocabulary-drift",
                "items": vocabulary_gap,
                "message": "runner methods and portfolio lenses disagree",
            }
        )

    floor_gap = sorted(set(run.CLASSIFICATIONS) ^ set(CLASSIFICATION_FLOORS))
    if floor_gap:
        findings.append(
            {
                "kind": "classification-vocabulary-drift",
                "items": floor_gap,
                "message": "runner classifications and portfolio floors disagree",
            }
        )

    for check in manifest.checks:
        methods = tuple(check["methods"])
        lenses = _lenses(methods)
        method_counts.update(methods)
        lens_counts.update(lenses)
        missing = [
            sorted(alternatives)
            for alternatives in CLASSIFICATION_FLOORS[check["classification"]]
            if not alternatives.intersection(lenses)
        ]
        if missing:
            findings.append(
                {
                    "kind": "insufficient-method-diversity",
                    "check": check["id"],
                    "classification": check["classification"],
                    "missing_lens_alternatives": missing,
                    "message": "declared methods do not meet the classification floor",
                }
            )
        checks.append(
            {
                "id": check["id"],
                "classification": check["classification"],
                "methods": list(methods),
                "lenses": sorted(lenses),
            }
        )

    unused = sorted(set(run.METHODS) - set(method_counts))
    return {
        "schema_version": 1,
        "manifest_sha256": manifest.digest,
        "outcome": "pass" if not findings else "fail",
        "summary": {
            "checks": len(checks),
            "declared_methods": len(method_counts),
            "available_methods": len(run.METHODS),
            "unused_methods": unused,
            "findings": len(findings),
        },
        "method_counts": dict(sorted(method_counts.items())),
        "lens_counts": dict(sorted(lens_counts.items())),
        "checks": checks,
        "findings": findings,
    }


def _write_json(path: Path, report: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _parse_arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=run.DEFAULT_MANIFEST)
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--check",
        action="store_true",
        help="return nonzero when the declared portfolio misses a policy floor",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parse_arguments(argv)
    try:
        manifest = run.load_manifest(arguments.manifest)
    except run.ManifestError as error:
        print(f"method portfolio error: {error}")
        return 2
    report = audit(manifest)
    if arguments.output:
        _write_json(arguments.output.resolve(), report)
    summary = report["summary"]
    print(
        "Method portfolio: "
        f"{summary['checks']} checks, "
        f"{summary['declared_methods']}/{summary['available_methods']} methods used, "
        f"{summary['findings']} policy findings"
    )
    if summary["unused_methods"]:
        print("Unused methods: " + ", ".join(summary["unused_methods"]))
    if arguments.output:
        print(f"Report: {arguments.output.resolve()}")
    if arguments.check and report["outcome"] != "pass":
        for finding in report["findings"]:
            print(f"FAIL {finding['kind']}: {finding['message']}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
