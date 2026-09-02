#!/usr/bin/env python3
"""Run the F2-O1 integrated provider-observable audit.

``--check`` is checkout-free: it regenerates the artifacts, invokes the
independent checker, runs all named mutations, verifies the frozen findings,
and checks the digest-bound elaboration receipt.  ``--elaborate`` additionally
runs the generated file under the pinned VCVio checkout and rewrites that
receipt before performing the ordinary check.
"""

from __future__ import annotations

import argparse
import ast
import copy
from dataclasses import dataclass
from datetime import UTC, datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
GENERATOR = HERE / "generator.py"
CHECKER = HERE / "checker.py"
EXPECTED = HERE / "expected-findings.json"
RECEIPT = HERE / "elaboration-receipt.json"
GENERATED_LEAN = HERE / "generated" / "Integrated.lean"
GENERATED_LEDGER = HERE / "generated" / "ledger.json"
D1_EXPECTED = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/expected-findings.json"
B5B2_EXPECTED = ROOT / "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/expected-findings.json"
F2O0_EXPECTED = ROOT / "evaluation/formal-provider-observables-f2o0/expected-findings.json"
TARGET_SOURCE = ROOT / "docs-next/pir/interactive-core.md"

DEFAULT_CHECKOUT = Path(os.environ.get("ZKC_F2O1_VCVIO_CHECKOUT", "/tmp/zkc-f0-sources.b66lUO/VCVio"))
ELAN_BIN = Path.home() / ".elan" / "bin"
AGGREGATE_OUTCOME = "CannotAnswer"
AGGREGATE_CODE = "F2O1-C-MISSING-OPERATIONAL-OBSERVABLE"
RECEIPT_FORMAT = "zkc.formal-provider-observables-f2o1.elaboration-receipt.v0"
PROVIDER_REVISION = "de0a3108140e3e04a7ebf0075aa110b459ee6e8a"
PROVIDER_TOOLCHAIN = "leanprover/lean4:v4.33.1"
PROVIDER_MODULE = "VCVio.OracleComp.ProbComp"
PRINTED_DECLARATIONS = ("ZkcF2O1.interaction",)
AXIOM_LINE = re.compile(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*)\])$")

MUTATION_CODES = {
    "duplicate-shared-challenge-equal-draws": "F2O1-R-SHARED-CHALLENGE-DUPLICATED",
    "reorder-interleaved-occurrences": "F2O1-R-SCHEDULE-ORDER",
    "drop-reduction-required-challenge-backlink": "F2O1-R-REDUCTION-CHALLENGE-BACKLINK",
    "logical-oracle-as-committed-table": "F2O1-R-ORACLE-MODE-MISMATCH",
    "verifier-only-query-to-public": "F2O1-R-QUERY-VISIBILITY",
    "omit-fallback-terminal-preemption": "F2O1-R-TERMINAL-PREEMPTION",
}


class GateFailure(RuntimeError):
    """The package detected drift, disagreement, or an accepted mutation."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _read_json(path: Path, label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure(f"cannot load {label}") from error


def _entry(ledger: dict[str, Any], construct_id: str) -> dict[str, Any]:
    for item in ledger["constructs"]:
        if item["id"] == construct_id:
            return item
    raise GateFailure(f"ledger lacks {construct_id}")


def _lake_environment() -> dict[str, str]:
    environment = os.environ.copy()
    if ELAN_BIN.is_dir():
        environment["PATH"] = f"{ELAN_BIN}{os.pathsep}{environment.get('PATH', '')}"
    return environment


def _lake_available(checkout: Path) -> bool:
    environment = _lake_environment()
    return (
        checkout.is_dir()
        and (checkout / "lean-toolchain").is_file()
        and (checkout / "lake-manifest.json").is_file()
        and shutil.which("lake", path=environment["PATH"]) is not None
    )


def _parse_axioms(stdout: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for line in stdout.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if match:
            axioms = match.group(3)
            result[match.group(1)] = [] if axioms is None else [item.strip() for item in axioms.split(",") if item.strip()]
    return result


def elaborate(checkout: Path) -> dict[str, Any]:
    environment = _lake_environment()

    def run(command: list[str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(command, cwd=checkout, env=environment, capture_output=True, text=True, check=False)

    revision = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    toolchain = (checkout / "lean-toolchain").read_text(encoding="utf-8").strip()
    lean_version = run(["lean", "--version"]).stdout.strip()
    command = ["lake", "env", "lean", str(GENERATED_LEAN)]
    started = time.perf_counter()
    completed = run(command)
    return {
        "format": RECEIPT_FORMAT,
        "classification": "environment fact only: elaboration of untrusted generated syntax; no correspondence, property, proof, or security claim",
        "provider": {
            "name": "VCVio",
            "checkout": str(checkout),
            "revision": revision,
            "toolchain": toolchain,
            "lean_version": lean_version,
            "lake_manifest_sha256": _sha256((checkout / "lake-manifest.json").read_bytes()),
            "imported_module": PROVIDER_MODULE,
        },
        "generated_file": GENERATED_LEAN.relative_to(HERE).as_posix(),
        "generated_sha256": _sha256(GENERATED_LEAN.read_bytes()),
        "ledger_file": GENERATED_LEDGER.relative_to(HERE).as_posix(),
        "ledger_sha256": _sha256(GENERATED_LEDGER.read_bytes()),
        "command": command,
        "exit_status": completed.returncode,
        "wall_seconds": round(time.perf_counter() - started, 3),
        "axioms": _parse_axioms(completed.stdout),
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "observed_at": datetime.now(UTC).isoformat(timespec="seconds"),
    }


def _mutate(name: str, lean_text: str, ledger: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    text = lean_text
    value = copy.deepcopy(ledger)
    if name == "duplicate-shared-challenge-equal-draws":
        item = _entry(value, "occurrence.14")
        item["realizes"]["sample_count"] = 2
        needle = "  let challenge0 ← ops.sampleChallenge 0 []  -- [f2o1:occurrence.14]"
        replacement = needle + "\n  let challenge0Again ← ops.sampleChallenge 0 []"
        _require(needle in text, "shared challenge line absent")
        text = text.replace(needle, replacement, 1)
        text = text.replace(
            "ops.applyReduction 1 [challenge0, challenge2]",
            "ops.applyReduction 1 [challenge0Again, challenge2]",
            1,
        )
    elif name == "reorder-interleaved-occurrences":
        lines = text.splitlines()
        first = next(index for index, line in enumerate(lines) if "[f2o1:occurrence.6]" in line)
        second = next(index for index, line in enumerate(lines) if "[f2o1:occurrence.7]" in line)
        lines[first], lines[second] = lines[second], lines[first]
        text = "\n".join(lines) + "\n"
    elif name == "drop-reduction-required-challenge-backlink":
        _entry(value, "reduction.0.declaration")["realizes"]["required_challenges"] = [0]
    elif name == "logical-oracle-as-committed-table":
        _entry(value, "oracle.2.mode")["realizes"]["mode"] = "FullCanonical"
    elif name == "verifier-only-query-to-public":
        _entry(value, "query.9.visibility")["realizes"]["visibility"] = "Public"
    elif name == "omit-fallback-terminal-preemption":
        _entry(
            value, "control.logical-reject-preemption.terminal.22.preemption"
        )["realizes"]["preempted_by"] = [20]
    else:
        raise GateFailure(f"unknown mutation {name}")
    return text, value


def evaluate(checkout: Path) -> tuple[list[Finding], dict[str, Any]]:
    findings: list[Finding] = []
    d1 = _read_json(D1_EXPECTED, "D1 frozen findings")
    b5b2 = _read_json(B5B2_EXPECTED, "B5B2 frozen findings")
    f2o0 = _read_json(F2O0_EXPECTED, "F2-O0 frozen findings")
    _require(
        d1.get("aggregate") == "F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE"
        and b5b2.get("aggregate") == "F0V2B2C1B5B2-A-EXACT-TERMINAL-OWNER-PROJECTIONS"
        and f2o0.get("aggregate") == "F2O0-C-MISSING-OPERATIONAL-OBSERVABLE",
        "D1, B5B2, or F2-O0 predecessor pin drifted",
    )
    findings.append(Finding("predecessor-pins", "Affirmative", "F2O1-A-PREDECESSOR-PINS"))

    generator = _load("_zkc_f2o1_generator", GENERATOR)
    checker = _load("_zkc_f2o1_checker", CHECKER)
    generator_source = GENERATOR.read_text(encoding="utf-8")
    checker_source = CHECKER.read_text(encoding="utf-8")
    def imports(source: str) -> set[str]:
        names: set[str] = set()
        for node in ast.walk(ast.parse(source)):
            if isinstance(node, ast.Import):
                names.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                names.add(node.module)
        return names

    generator_imports = imports(generator_source)
    checker_imports = imports(checker_source)
    _require(
        "generator" not in checker_imports
        and "checker" not in generator_imports
        and generator is not checker,
        "generator and checker code are not independent",
    )
    findings.append(Finding("generator-checker-separation", "Affirmative", "F2O1-A-CODE-SEPARATION"))

    lean_text, ledger = generator.build()
    facts = checker.owner_facts()
    _require(
        ledger["subject"]["core_id"] == facts["core_id"]
        and ledger["subject"]["protocol_id"] == facts["protocol_id"],
        "generator and cold checker identify different subjects",
    )
    findings.append(Finding("cold-subject-authentication", "Affirmative", "F2O1-A-SUBJECT-AUTHENTICATED"))
    _require(
        lean_text.encode() == GENERATED_LEAN.read_bytes()
        and (json.dumps(ledger, indent=2, sort_keys=True) + "\n").encode() == GENERATED_LEDGER.read_bytes(),
        "generated Lean or ledger is not byte-reproducible",
    )
    findings.append(Finding("generated-fixtures-reproduced", "Affirmative", "F2O1-A-GENERATED-FIXTURES"))

    view_status = ledger["subject"]["view_status"]
    _require(view_status["PublicCoinView"]["status"] == "realized" and view_status["PublicCoinView"]["leaf_count"] == len(facts["manifest"]), "PublicCoinView realization drifted")
    _require(sum(item["status"] == "no_integrated_projection" for item in view_status.values()) == 5, "integrated view issuance boundary drifted")
    findings.extend(
        (
            Finding("integrated-public-coin-view", "Affirmative", "F2O1-A-PUBLIC-COIN-VIEW"),
            Finding("five-integrated-owner-views-unissued", "CannotAnswer", "F2O1-C-INTEGRATED-VIEW-PROJECTIONS"),
        )
    )

    report = checker.check(copy.deepcopy(ledger), lean_text, facts)
    _require(report["outcome"] == "Affirmative" and report["code"] == checker.PASS_CODE, "independent checker refused baseline: " + json.dumps(report["failures"]))
    _require(report["constructs"] == len(ledger["constructs"]) and report["sourced"] == len(generator._source_paths()), "construct totality or source count drifted")
    _require(len([item for item in ledger["constructs"] if item["id"].startswith("occurrence.")]) == 23, "occurrence totality drifted")
    findings.extend(
        (
            Finding("ledger-total-over-occurrences", "Affirmative", "F2O1-A-SCHEDULE-TOTAL"),
            Finding("ledger-coordinate-injectivity", "Affirmative", "F2O1-A-COORDINATE-INJECTIVE"),
            Finding("ledger-coordinate-validity", "Affirmative", "F2O1-A-COORDINATES-VALID"),
            Finding("ledger-gap-enumeration", "Affirmative", "F2O1-A-GAPS-ENUMERATED"),
            Finding("integrated-discriminators-rendered", "Affirmative", "F2O1-A-INTEGRATED-DISCRIMINATORS"),
        )
    )
    _require(
        set(facts["controls"])
        == {
            "private-verifier-output-sink",
            "invalid-module-control-sink",
            "history-challenge-condition",
            "logical-reject-preemption",
        }
        and all(not item["eligible"] for item in facts["controls"].values())
        and facts["controls"]["logical-reject-preemption"]["fallback_verdict"] == 0,
        "D1 neighbour controls drifted",
    )
    findings.append(
        Finding("four-d1-neighbour-controls", "Refused", "F2O1-R-D1-NEIGHBOURS")
    )

    mutation_failures: dict[str, list[str]] = {}
    for name, code in MUTATION_CODES.items():
        mutated_text, mutated_ledger = _mutate(name, lean_text, ledger)
        mutated = checker.check(mutated_ledger, mutated_text, facts)
        _require(mutated["outcome"] == "Refused" and mutated["code"] == code, f"{name}: expected Refused/{code}, got {mutated['outcome']}/{mutated['code']}")
        mutation_failures[name] = [item["code"] for item in mutated["failures"]]
        findings.append(Finding(name, "Refused", code))

    operational = report["aggregate"]["missing_operational_observables"]
    _require(report["aggregate"]["outcome"] == AGGREGATE_OUTCOME and report["aggregate"]["code"] == AGGREGATE_CODE and operational, "aggregate did not fail closed over operational gaps")
    property_gaps = sorted(item["construct"] for item in report["gaps"] if item["class"] == "property-premise")
    findings.extend(
        (
            Finding("operational-observable-list", "CannotAnswer", AGGREGATE_CODE),
            Finding("property-premise-list", "CannotAnswer", "F2O1-C-PROPERTY-PREMISES"),
        )
    )

    receipt = _read_json(RECEIPT, "elaboration receipt")
    _require(
        receipt.get("format") == RECEIPT_FORMAT
        and receipt.get("generated_sha256") == _sha256(GENERATED_LEAN.read_bytes())
        and receipt.get("ledger_sha256") == _sha256(GENERATED_LEDGER.read_bytes())
        and receipt.get("provider", {}).get("revision") == PROVIDER_REVISION
        and receipt.get("provider", {}).get("toolchain") == PROVIDER_TOOLCHAIN
        and receipt.get("provider", {}).get("imported_module") == PROVIDER_MODULE,
        "elaboration receipt is not bound to generated artifacts and provider pins",
    )
    findings.append(Finding("elaboration-receipt-bound", "Affirmative", "F2O1-A-RECEIPT-BOUND"))
    if receipt.get("exit_status") == 0 and set(receipt.get("axioms", {})) == set(PRINTED_DECLARATIONS) and all(receipt["axioms"][name] == [] for name in PRINTED_DECLARATIONS):
        findings.append(Finding("elaboration-recorded", "Affirmative", "F2O1-A-ELABORATION-RECORDED"))
    else:
        findings.append(Finding("elaboration-recorded", "Refused", "F2O1-R-ELABORATION-FAILED"))

    target = TARGET_SOURCE.read_text(encoding="utf-8")
    _require("F2O1" not in target, "target owner page names this package")
    findings.extend(
        (
            Finding("target-authority-untouched", "Affirmative", "F2O1-A-NONPUBLICATION"),
            Finding("provider-correspondence", "CannotAnswer", "F2O1-C-PROVIDER-CORRESPONDENCE"),
            Finding("property-proof-or-security", "CannotAnswer", "F2O1-C-PROPERTY"),
            Finding("provider-observable-audit-integrated", AGGREGATE_OUTCOME, AGGREGATE_CODE),
        )
    )
    payload = [item.value() for item in findings]
    metrics = {
        "findings": len(findings),
        "findings_sha256": _sha256(json.dumps(payload, separators=(",", ":")).encode()),
        "constructs": report["constructs"],
        "sourced_constructs": report["sourced"],
        "public_coin_leaf_count": len(facts["manifest"]),
        "operational_gaps": operational,
        "property_premise_gaps": property_gaps,
        "mutations": len(MUTATION_CODES),
        "mutation_failure_codes": mutation_failures,
        "generated_lean_sha256": _sha256(GENERATED_LEAN.read_bytes()),
        "ledger_sha256": _sha256(GENERATED_LEDGER.read_bytes()),
        "receipt": {key: receipt.get(key) for key in ("exit_status", "wall_seconds", "observed_at")},
        "live_elaboration": "available" if _lake_available(checkout) else "Unsupported/F2O1-U-PROVIDER-ENVIRONMENT",
    }
    return findings, metrics


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--elaborate", action="store_true")
    parser.add_argument("--emit-expected", action="store_true")
    parser.add_argument("--checkout", type=Path, default=DEFAULT_CHECKOUT)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    if args.elaborate:
        if not _lake_available(checkout):
            print(json.dumps({"outcome": "Unsupported", "code": "F2O1-U-PROVIDER-ENVIRONMENT", "checkout": str(checkout)}, indent=2))
            return 2
        generator = _load("_zkc_f2o1_elaboration_generator", GENERATOR)
        generator.write()
        receipt = elaborate(checkout)
        RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[formal-provider-observables-f2o1] elaboration exit {receipt['exit_status']} in {receipt['wall_seconds']}s")
        if receipt["exit_status"] != 0:
            print(receipt["stdout"])
            print(receipt["stderr"], file=sys.stderr)
    try:
        findings, metrics = evaluate(checkout)
    except GateFailure as error:
        print(f"F2-O1 gate failed: {error}", file=sys.stderr)
        return 1
    observed = {
        "aggregate": {
            "outcome": AGGREGATE_OUTCOME,
            "code": AGGREGATE_CODE,
            "missing_operational_observables": metrics["operational_gaps"],
        },
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [item.value() for item in findings],
    }
    if args.emit_expected:
        print(json.dumps(observed, indent=2))
        return 0
    if args.check and observed != _read_json(EXPECTED, "frozen findings"):
        print(json.dumps({"expected": _read_json(EXPECTED, "frozen findings"), "observed": observed}, indent=2, sort_keys=True))
        return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    output: dict[str, Any] = {"aggregate": observed["aggregate"], "outcomes": dict(sorted(counts.items())), "metrics": metrics}
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
