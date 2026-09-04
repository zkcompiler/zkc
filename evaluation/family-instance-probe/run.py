#!/usr/bin/env python3
"""Run the finite family/member measurement probe."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"
SOURCE_FILES = (
    ROOT / "docs-next/pir/interactive-core.md",
    ROOT / "docs-next/pir/fiat-shamir.md",
    ROOT / "docs-next/analysis/cryptographic-properties.md",
    ROOT / "docs-next/relations/relation-model.md",
    ROOT / "evaluation/indexed-core-elaboration/reference_model.py",
    ROOT / "evaluation/k2-protocol-fiat-shamir/reference_model.py",
)
AGGREGATE = "FAMILYINSTANCE-A-INSTANCES-OUTSIDE-CORE"


class ProbeFailure(RuntimeError):
    """The package found drift or a failed bounded assertion."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


FINDINGS = (
    Finding("six-finite-core-admissions", "Affirmative", "FAMILYINSTANCE-A-SIX-CORES"),
    Finding("parameter-rotates-core-identity", "Affirmative", "FAMILYINSTANCE-A-CORE-ROTATION"),
    Finding("fri-instance-measurements", "Affirmative", "FAMILYINSTANCE-A-FRI-MEASUREMENTS"),
    Finding("sumcheck-instance-measurements", "Affirmative", "FAMILYINSTANCE-A-SUMCHECK-MEASUREMENTS"),
    Finding(
        "regular-finite-variation",
        "Negative",
        "FAMILYINSTANCE-N-FRI-BODY-BYTES-NON-AFFINE",
    ),
    Finding("bounded-admission-time", "Affirmative", "FAMILYINSTANCE-A-ADMISSION-TIME"),
    Finding("adjacent-identity-substitution", "Refused", "FAMILYINSTANCE-R-ADJACENT-IDENTITY"),
    Finding("fixture-graph-measurements", "Affirmative", "FAMILYINSTANCE-A-FIXTURE-GRAPH"),
    Finding("target-pcgraph-equivalence", "CannotAnswer", "FAMILYINSTANCE-C-TARGET-PCGRAPH"),
    Finding("family-theorem-source-reuse", "Affirmative", "FAMILYINSTANCE-A-THEOREM-REUSE"),
    Finding("internal-template-necessity", "CannotAnswer", "FAMILYINSTANCE-C-TEMPLATE-NECESSITY"),
    Finding("family-profile-attachment", "CannotAnswer", "FAMILYINSTANCE-C-PROFILE-ATTACHMENT"),
    Finding("theorem-proof-or-soundness", "CannotAnswer", "FAMILYINSTANCE-C-THEOREM-OR-SOUNDNESS"),
    Finding("target-design-adoption", "CannotAnswer", "FAMILYINSTANCE-C-DESIGN-ADOPTION"),
    Finding("family-instance-recommendation", "Affirmative", AGGREGATE),
)


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ProbeFailure(detail)


def _source_hashes() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in SOURCE_FILES
    }


def _findings_hash(findings: list[list[str]]) -> str:
    body = json.dumps(findings, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(body).hexdigest()


def evaluate() -> dict[str, object]:
    model = _load("_zkc_family_instance_probe_model", HERE / "model.py")
    measurements = model.measure()
    flat = [row for rows in measurements.values() for row in rows]
    _require(len(flat) == 6, "expected exactly six measured concrete Cores")
    _require(
        len({row.core_id for row in flat}) == 6,
        "every selected family member must have a distinct Core identity",
    )
    _require(
        all(row.admission_wall_time_ns <= model.ADMISSION_TIME_LIMIT_NS for row in flat),
        "a bare finite Core admission exceeded the frozen wall-time ceiling",
    )
    _require(
        model.adjacent_identity_substitutions_refused(measurements),
        "an adjacent parameter substitution preserved Core identity",
    )
    regularity, non_affine = model.finite_variation(measurements)
    _require(len(regularity) == 7, "expected seven affine finite measurements")
    _require(
        tuple((row.family, row.metric) for row in non_affine)
        == (("fri-like-folding", "body_bytes"),),
        "the finite non-affine measurement set drifted",
    )
    _require(
        all(row.pcgraph_nodes > 0 and row.pcgraph_edges > 0 for row in flat),
        "fixture graph measurements must be nonempty",
    )
    _require(
        model.theorem_source_is_reused(),
        "the three design evidence ledgers do not share one family theorem source",
    )

    finding_values = [item.value() for item in FINDINGS]
    return {
        "aggregate": AGGREGATE,
        "findings_sha256": _findings_hash(finding_values),
        "finding_codes": finding_values,
        "source_sha256": _source_hashes(),
        "measurements": {
            family: [row.frozen_value() for row in rows]
            for family, rows in measurements.items()
        },
        "admission_wall_time_ns": {
            family: [
                {"parameter": row.parameter, "median": row.admission_wall_time_ns}
                for row in rows
            ]
            for family, rows in measurements.items()
        },
        "admission_wall_time_limit_ns": model.ADMISSION_TIME_LIMIT_NS,
        "admission_repetitions_per_instance": model.ADMISSION_REPETITIONS,
        "regularity": [item.value() for item in regularity],
        "non_affine": [item.value() for item in non_affine],
        "theorem_binding": model.SUMCHECK_THEOREM_BINDINGS,
    }


def _check_expected(report: dict[str, object]) -> None:
    expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
    stable_report = {
        key: value
        for key, value in report.items()
        if key != "admission_wall_time_ns"
    }
    _require(stable_report == expected, "frozen family/instance findings drifted")


def _print_summary(report: dict[str, object]) -> None:
    print(
        f"family-instance-probe: {report['aggregate']} "
        f"({len(report['finding_codes'])} findings)"
    )
    for family, rows in report["measurements"].items():
        timings = {
            item["parameter"]: item["median"]
            for item in report["admission_wall_time_ns"][family]
        }
        for row in rows:
            print(
                f"  {family} {row['parameter_name']}={row['parameter']}: "
                f"body={row['body_bytes']} bytes, nodes={row['pcgraph_nodes']}, "
                f"edges={row['pcgraph_edges']}, declarations={row['declarations']}, "
                f"changed={row['declarations_different_from_previous']}, "
                f"admission-median={timings[row['parameter']]} ns"
            )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with frozen findings")
    parser.add_argument("--json", action="store_true", help="emit the complete report")
    args = parser.parse_args(argv)
    try:
        report = evaluate()
        if args.check:
            _check_expected(report)
    except (OSError, ValueError, ProbeFailure) as error:
        print(f"family-instance-probe: FAIL: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_summary(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
