#!/usr/bin/env python3
"""Run the F1-R1C owner-view source-determinacy audit."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"


class GateFailure(RuntimeError):
    pass


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise GateFailure(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


audit = _load("_zkc_f1r1c_audit", HERE / "audit_model.py")
cold = _load("_zkc_f1r1c_inventory", HERE / "independent.py")


def run_gate() -> dict[str, object]:
    findings, evidence = audit.evaluate()
    try:
        expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read frozen F1-R1C findings") from error

    observed_cases = [
        {"name": item.name, "outcome": item.outcome, "code": item.code}
        for item in findings
    ]
    if observed_cases != expected["cases"]:
        raise GateFailure(
            "F1-R1C finding classification drifted:\n"
            + json.dumps(
                {"expected": expected["cases"], "observed": observed_cases},
                indent=2,
            )
        )
    if evidence["aggregate"] != expected["aggregate"]:
        raise GateFailure("F1-R1C aggregate disposition drifted")

    inventory = cold.inventory()
    for key in (
        "view_bodies",
        "extension_catalogs",
        "selected_view_body_declarations",
        "canonical_view_body_grammars",
        "static_fragment_body_functions",
        "source_subject_compilers",
    ):
        if inventory[key] != evidence[key]:
            raise GateFailure(f"independent raw-source inventory disagrees on {key}")

    if evidence["target_profile_digest"] != expected["target_profile_digest"]:
        raise GateFailure("the frozen target profile digest changed")
    return {
        "aggregate": evidence["aggregate"],
        "cases": [
            {
                "name": item.name,
                "outcome": item.outcome,
                "code": item.code,
                "detail": item.detail,
            }
            for item in findings
        ],
        "evidence": evidence,
        "independent_inventory": inventory,
        "passed": len(findings),
        "total": len(expected["cases"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    try:
        report = run_gate()
    except (GateFailure, audit.AuditError, cold.InventoryError) as error:
        print(f"F1-R1C audit failed: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        aggregate = report["aggregate"]
        print(
            f"F1-R1C owner-view determinacy: {report['passed']}/{report['total']} "
            f"observations matched"
        )
        print(f"  aggregate: {aggregate['outcome']}/{aggregate['code']}")
        for row in report["cases"]:
            print(f"  {row['name']}: {row['outcome']}/{row['code']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
