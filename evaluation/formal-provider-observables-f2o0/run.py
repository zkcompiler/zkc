#!/usr/bin/env python3
"""Run the F2-O0 provider-observable audit gate.

``--check`` reruns the Python parts (generation, independent checking, and
every mutation), verifies that the committed generated file and ledger are
reproduced byte for byte, verifies that the committed elaboration receipt is
bound to the committed generated file by digest, and compares the findings
with the frozen list.  It never needs the provider checkout.

``--elaborate`` additionally runs ``lake env lean`` on the generated file
inside the pinned VCVio checkout and rewrites ``elaboration-receipt.json``
before the ordinary check.  A missing checkout is classified as
``Unsupported/F2O0-U-PROVIDER-ENVIRONMENT`` and is never a silent pass.
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
GENERATED_LEAN = HERE / "generated" / "Schnorr.lean"
GENERATED_LEDGER = HERE / "generated" / "ledger.json"
B1_EXPECTED = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/expected-findings.json"
R1B_IDENTITIES = ROOT / "evaluation/formal-source-target-core-f1r1b/expected-identities.json"
TARGET_SOURCE = ROOT / "docs-next/pir/interactive-core.md"
DEFAULT_CHECKOUT = Path(
    os.environ.get("ZKC_F2O0_VCVIO_CHECKOUT", "/tmp/zkc-f0-sources.b66lUO/VCVio")
)
ELAN_BIN = Path.home() / ".elan" / "bin"

AGGREGATE = "F2O0-C-MISSING-OPERATIONAL-OBSERVABLE"
RECEIPT_FORMAT = "zkc.formal-provider-observables-f2o0.elaboration-receipt.v0"
PROVIDER_REVISION = "de0a3108140e3e04a7ebf0075aa110b459ee6e8a"
PROVIDER_TOOLCHAIN = "leanprover/lean4:v4.33.1"
PROVIDER_MODULE = "VCVio.CryptoFoundations.SigmaProtocol"
PRINTED_DECLARATIONS = ("ZkcF2O0.interaction", "ZkcF2O0.providerShape")
B1_AGGREGATE = "F0V2B1-A-BOUNDED-NORMALIZED-DERIVATION"
B1_LEAF_COUNT = 329
OPERATIONAL_GAPS = {
    "challenge.0.law": ("operational-distribution", "F2O0-C-CHALLENGE-LAW"),
    "check.0.denotation": ("operational-denotation", "F2O0-C-CHECK-DENOTATION"),
    "guard.4.denotation": ("operational-denotation", "F2O0-C-GUARD-DENOTATION"),
    "provider.verify": ("operational-outcome-map", "F2O0-C-OUTCOME-MAP"),
}
PROPERTY_GAPS = {
    "provider.relation": "F2O0-C-RELATION",
    "provider.witness-type": "F2O0-C-WITNESS-TYPE",
    "provider.prover-state-type": "F2O0-C-PROVER-STATE",
    "provider.commit": "F2O0-C-HONEST-COMMIT",
    "provider.respond": "F2O0-C-HONEST-RESPOND",
}
GAP_FINDING_NAMES = {
    "challenge.0.law": "challenge-sampling-law",
    "check.0.denotation": "check-denotation",
    "guard.4.denotation": "guard-denotation",
    "provider.verify": "outcome-partition-map",
    "provider.relation": "relation-predicate",
    "provider.witness-type": "witness-type",
    "provider.prover-state-type": "prover-private-state",
    "provider.commit": "honest-commit",
    "provider.respond": "honest-respond",
}
MUTATION_CODES = {
    "alias-equal-valued-read-coordinates": "F2O0-R-COORDINATE-ALIAS",
    "drop-response-producer": "F2O0-R-OCCURRENCE-UNCOVERED",
    "strip-response-producer-coordinate": "F2O0-R-CONSTRUCT-UNSOURCED",
    "constant-fresh-challenge": "F2O0-R-CHALLENGE-NOT-FRESH",
    "omit-reject-terminal": "F2O0-R-TERMINAL-UNCOVERED",
    "unknown-coordinate-ordinal": "F2O0-R-COORDINATE-UNKNOWN",
    "cross-view-coordinate-replay": "F2O0-R-COORDINATE-UNKNOWN",
    "invent-check-denotation": "F2O0-R-INVENTED-OBSERVABLE",
    "unledgered-lean-marker": "F2O0-R-MARKER-UNLEDGERED",
    "reorder-challenge-after-response": "F2O0-R-SCHEDULE-ORDER",
    "untyped-gap-entry": "F2O0-R-GAP-UNTYPED",
    "duplicate-lean-marker": "F2O0-R-MARKER-DUPLICATE",
    "verdict-swap": "F2O0-R-VERDICT-MISMATCH",
    "effect-kind-mismatch": "F2O0-R-EFFECT-MISMATCH",
}
SOURCED_TYPE_CONSTRUCTS = ("type.z3", "type.bool")
PROVIDER_TYPE_CONSTRUCTS = (
    "provider.statement-type",
    "provider.commit-type",
    "provider.challenge-type",
    "provider.response-type",
)
AXIOM_LINE = re.compile(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*)\])$")


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
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical_digest(value: Any) -> str:
    return _sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
            "ascii"
        )
    )


def _read_json(path: Path, label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure(f"cannot load {label}") from error


def _string_constants(source: str) -> set[str]:
    """String constants of a module, excluding module and function docstrings."""

    tree = ast.parse(source)
    docstrings: set[int] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.ClassDef)):
            body = node.body
            if (
                body
                and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)
            ):
                docstrings.add(id(body[0].value))
    return {
        node.value
        for node in ast.walk(tree)
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and id(node) not in docstrings
    }


def _imports(source: str) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Import):
            names.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module)
    return names


def _construct(ledger: dict[str, Any], construct_id: str) -> dict[str, Any]:
    for entry in ledger["constructs"]:
        if entry["id"] == construct_id:
            return entry
    raise GateFailure(f"ledger lacks construct {construct_id}")


def _compiler(entry: dict[str, Any]) -> str | None:
    coordinate = entry["source"].get("coordinate")
    if coordinate is None:
        return None
    return coordinate["boundary"].get("compiler")


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
    closures: dict[str, list[str]] = {}
    for line in stdout.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if match is None:
            continue
        axioms = match.group(3)
        closures[match.group(1)] = (
            [] if axioms is None else [item.strip() for item in axioms.split(",") if item]
        )
    return closures


def elaborate(checkout: Path) -> dict[str, Any]:
    """Run the pinned provider environment on the generated file; record facts."""

    environment = _lake_environment()

    def run(command: list[str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            command, cwd=checkout, env=environment, capture_output=True, text=True, check=False
        )

    revision = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    toolchain = (checkout / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_sha = _sha256((checkout / "lake-manifest.json").read_bytes())
    lean_version = run(["lean", "--version"]).stdout.strip()
    command = ["lake", "env", "lean", str(GENERATED_LEAN)]
    started = time.perf_counter()
    completed = run(command)
    wall = round(time.perf_counter() - started, 3)
    return {
        "format": RECEIPT_FORMAT,
        "classification": (
            "environment fact only: the pinned toolchain elaborated the untrusted "
            "generated file; no correspondence, applicability, property, or security "
            "claim"
        ),
        "provider": {
            "name": "VCVio",
            "checkout": str(checkout),
            "revision": revision,
            "toolchain": toolchain,
            "lean_version": lean_version,
            "lake_manifest_sha256": manifest_sha,
            "imported_module": PROVIDER_MODULE,
        },
        "generated_file": GENERATED_LEAN.relative_to(HERE).as_posix(),
        "generated_sha256": _sha256(GENERATED_LEAN.read_bytes()),
        "ledger_file": GENERATED_LEDGER.relative_to(HERE).as_posix(),
        "ledger_sha256": _sha256(GENERATED_LEDGER.read_bytes()),
        "command": command,
        "exit_status": completed.returncode,
        "wall_seconds": wall,
        "axioms": _parse_axioms(completed.stdout),
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "observed_at": datetime.now(UTC).isoformat(timespec="seconds"),
    }


def evaluate(checkout: Path) -> tuple[list[Finding], dict[str, Any]]:
    findings: list[Finding] = []
    metrics: dict[str, Any] = {}

    # Predecessor pins: the B1 frozen view universe and the F1-R1B identities.
    b1_expected = _read_json(B1_EXPECTED, "B1 frozen findings")
    identities = _read_json(R1B_IDENTITIES, "F1-R1B frozen identities")
    _require(
        b1_expected["aggregate"]["code"] == B1_AGGREGATE
        and b1_expected["evidence_control"]["total_leaf_count"] == B1_LEAF_COUNT,
        "B1 predecessor result drifted",
    )
    b1_manifest_digests = {
        view: item["manifest_digest"]
        for view, item in b1_expected["evidence_control"]["views"].items()
    }
    findings.append(_finding("predecessor-pins", "Affirmative", "F2O0-A-PREDECESSOR-PIN"))

    # Load the untrusted generator and the independent checker.
    generator = _load("_zkc_f2o0_generator", GENERATOR)
    checker = _load("_zkc_f2o0_checker", CHECKER)
    subject = generator.load_subject()
    facts = checker.owner_facts()
    _require(
        subject["core_id"] == identities["core_id"]
        and subject["protocol_id"] == identities["fresh_protocol_id"]
        and facts["core_id"] == identities["core_id"]
        and facts["protocol_id"] == identities["fresh_protocol_id"],
        "admitted subject identities drifted from the F1-R1B pins",
    )
    findings.append(_finding("subject-admitted", "Affirmative", "F2O0-A-SUBJECT-ADMITTED"))

    _require(
        subject["manifests"] == facts["manifests"]
        and facts["leaf_count"] == B1_LEAF_COUNT
        and {
            view: _canonical_digest(coordinates)
            for view, coordinates in subject["manifests"].items()
        }
        == b1_manifest_digests,
        "generator and checker view universes disagree or drifted from B1",
    )
    findings.append(_finding("view-universe-agreement", "Affirmative", "F2O0-A-VIEW-UNIVERSE"))

    generator_source = GENERATOR.read_text(encoding="utf-8")
    checker_source = CHECKER.read_text(encoding="utf-8")
    generator_constants = _string_constants(generator_source)
    checker_constants = _string_constants(checker_source)
    _require(
        not any("checker" in name or "generator" in name for name in _imports(generator_source))
        and not any(
            "checker" in name or "generator" in name for name in _imports(checker_source)
        )
        and not any("checker" in value for value in generator_constants)
        and not any("generator" in value for value in checker_constants)
        and any(value.endswith("model.py") for value in generator_constants)
        and not any(value.endswith("independent.py") for value in generator_constants)
        and any(value.endswith("independent.py") for value in checker_constants)
        and not any(value.endswith("model.py") for value in checker_constants)
        and generator.owner is not sys.modules["_zkc_f0v2b1_independent_owner"]
        and generator is not checker,
        "generator and checker are not separated",
    )
    findings.append(
        _finding("generator-checker-separation", "Affirmative", "F2O0-A-CODE-SEPARATION")
    )

    # Reproduce the committed generated artifacts byte for byte.
    lean_text, ledger = generator.generate(None, subject)
    committed_lean = GENERATED_LEAN.read_bytes()
    committed_ledger = GENERATED_LEDGER.read_bytes()
    _require(
        lean_text.encode("utf-8") == committed_lean
        and generator.ledger_bytes(ledger) == committed_ledger,
        "regenerated Lean file or ledger differs from the committed fixtures",
    )
    findings.append(
        _finding("generated-fixtures-reproduced", "Affirmative", "F2O0-A-GENERATED-FIXTURES")
    )

    # Independent check of the baseline ledger.
    report = checker.check(copy.deepcopy(ledger), lean_text, facts)
    _require(
        report["outcome"] == "Affirmative" and report["code"] == checker.PASS_CODE,
        "independent checker refused the baseline ledger: " + json.dumps(report["failures"]),
    )
    coverage = report["coverage"]
    _require(
        coverage["occurrences"] == 6
        and coverage["occurrences_with_steps"] == 6
        and coverage["terminals"] == 2
        and coverage["terminals_with_verdicts"] == 2,
        "schedule coverage drifted",
    )
    _require(
        coverage["claimed_coordinates"] == report["sourced"]
        and coverage["view_leaves"] == B1_LEAF_COUNT,
        "coordinate injectivity or universe drifted",
    )
    challenge_step = _construct(ledger, "occurrence.1")
    _require(
        challenge_step["realizes"]["realization"] == "sample"
        and challenge_step["realizes"]["samples_from"] == "challenge.0.law"
        and _compiler(_construct(ledger, "challenge.0.interpretation"))
        is None
        and _construct(ledger, "challenge.0.interpretation")["source"]["coordinate"]["view"]
        == "ExecutionView",
        "Fresh challenge realization drifted",
    )
    _require(
        _construct(ledger, "terminal.0.verdict")["realizes"]["verdict"] == "accept"
        and _construct(ledger, "terminal.1.verdict")["realizes"]["verdict"] == "reject"
        and _construct(ledger, "occurrence.4")["realizes"]["realization"]
        == "guarded-terminal"
        and _construct(ledger, "occurrence.5")["realizes"]["realization"]
        == "fallback-terminal",
        "terminal realization drifted",
    )
    findings.extend(
        (
            _finding("ledger-total-over-schedule", "Affirmative", "F2O0-A-SCHEDULE-TOTAL"),
            _finding(
                "ledger-injective-over-coordinates",
                "Affirmative",
                "F2O0-A-COORDINATE-INJECTIVE",
            ),
            _finding("ledger-coordinates-valid", "Affirmative", "F2O0-A-COORDINATES-VALID"),
            _finding("lean-ledger-markers-consistent", "Affirmative", "F2O0-A-MARKERS"),
            _finding("fresh-challenge-sampled", "Affirmative", "F2O0-A-FRESH-SAMPLE"),
            _finding("both-terminals-realized", "Affirmative", "F2O0-A-TERMINALS"),
        )
    )

    # Which candidate observables turned out to be present.
    _require(
        all(
            _compiler(_construct(ledger, name)) == "value-type-body-v0"
            for name in SOURCED_TYPE_CONSTRUCTS
        )
        and all(
            _compiler(_construct(ledger, name)) in ("value-type-body-v0", None)
            and "coordinate" in _construct(ledger, name)["source"]
            for name in PROVIDER_TYPE_CONSTRUCTS
        ),
        "value-type observables are no longer sourced",
    )
    findings.append(
        _finding("value-types-sourced", "Affirmative", "F2O0-A-VALUE-TYPES-SOURCED")
    )
    reads = [entry for entry in ledger["constructs"] if entry["kind"] == "prover-read"]
    decisions = [entry for entry in ledger["constructs"] if entry["kind"] == "prover-decision"]
    _require(
        len(reads) == facts["reads"] == 7
        and len(decisions) == facts["decisions"] == 2
        and all("coordinate" in entry["source"] for entry in reads + decisions)
        and "coordinate" in _construct(ledger, "strategy.parameter")["source"],
        "prover interface sourcing drifted",
    )
    findings.append(_finding("prover-interface-sourced", "Affirmative", "F2O0-A-PROVER-INTERFACE"))
    findings.append(
        _finding("provider-type-parameters-sourced", "Affirmative", "F2O0-A-PROVIDER-TYPES")
    )

    # The audit result: exact enumeration of every missing observable.
    gaps = {gap["construct"]: gap for gap in report["gaps"]}
    _require(
        set(gaps) == set(OPERATIONAL_GAPS) | set(PROPERTY_GAPS)
        and all(gaps[name]["class"] == item[0] for name, item in OPERATIONAL_GAPS.items())
        and all(gaps[name]["class"] == "property-premise" for name in PROPERTY_GAPS)
        and report["audit"]["outcome"] == "CannotAnswer"
        and report["audit"]["code"] == AGGREGATE
        and all(gap["reason"] and gap["needed_for"] and gap["lives_in"] for gap in gaps.values()),
        "the enumerated gap set drifted: " + json.dumps(sorted(gaps)),
    )
    for name, (_gap_class, code) in OPERATIONAL_GAPS.items():
        findings.append(_finding(GAP_FINDING_NAMES[name], "CannotAnswer", code))
    for name, code in PROPERTY_GAPS.items():
        findings.append(_finding(GAP_FINDING_NAMES[name], "CannotAnswer", code))

    # Mutations: each must produce its named checker failure.
    _require(tuple(MUTATION_CODES) == tuple(generator.MUTATIONS), "mutation catalog drifted")
    mutation_reports: dict[str, list[str]] = {}
    for mutation, code in MUTATION_CODES.items():
        mutated_text, mutated_ledger = generator.generate(mutation, subject)
        _require(
            mutated_text != lean_text or mutated_ledger != ledger,
            f"{mutation} did not mutate",
        )
        mutated = checker.check(copy.deepcopy(mutated_ledger), mutated_text, facts)
        _require(
            mutated["outcome"] == "Refused" and mutated["code"] == code,
            f"{mutation}: expected Refused/{code}, got {mutated['outcome']}/{mutated['code']}",
        )
        mutation_reports[mutation] = sorted({item["code"] for item in mutated["failures"]})
        findings.append(_finding(mutation, "Refused", code))

    # The committed elaboration receipt is bound to the committed generated file.
    receipt = _read_json(RECEIPT, "elaboration receipt")
    _require(
        receipt.get("format") == RECEIPT_FORMAT
        and receipt.get("generated_sha256") == _sha256(committed_lean)
        and receipt.get("ledger_sha256") == _sha256(committed_ledger)
        and receipt.get("provider", {}).get("revision") == PROVIDER_REVISION
        and receipt.get("provider", {}).get("toolchain") == PROVIDER_TOOLCHAIN
        and receipt.get("provider", {}).get("imported_module") == PROVIDER_MODULE,
        "elaboration receipt is not bound to the committed generated file and pins",
    )
    findings.append(_finding("elaboration-receipt-bound", "Affirmative", "F2O0-A-RECEIPT-BOUND"))
    axioms = receipt.get("axioms", {})
    if (
        receipt.get("exit_status") == 0
        and set(axioms) == set(PRINTED_DECLARATIONS)
        and all(axioms[name] == [] for name in PRINTED_DECLARATIONS)
    ):
        findings.append(
            _finding("elaboration-recorded", "Affirmative", "F2O0-A-ELABORATION-RECORDED")
        )
    else:
        findings.append(
            _finding("elaboration-recorded", "Refused", "F2O0-R-ELABORATION-FAILED")
        )

    target = TARGET_SOURCE.read_text(encoding="utf-8")
    _require("F2O0" not in target, "target text names this package")
    findings.append(
        _finding("target-authority-untouched", "Affirmative", "F2O0-A-NONPUBLICATION")
    )
    findings.extend(
        (
            _finding("q2-correspondence", "CannotAnswer", "F2O0-C-Q2-CORRESPONDENCE"),
            _finding("theorem-applicability", "CannotAnswer", "F2O0-C-APPLICABILITY"),
            _finding("property-or-security", "CannotAnswer", "F2O0-C-PROPERTY"),
            _finding(
                "shared-challenge-discriminator", "CannotAnswer", "F2O0-C-SHARED-CHALLENGE"
            ),
            _finding("provider-observable-audit", "CannotAnswer", AGGREGATE),
        )
    )

    payload = [finding.value() for finding in findings]
    metrics.update(
        {
            "findings": len(findings),
            "findings_sha256": _sha256(
                json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
            ),
            "constructs": report["constructs"],
            "sourced_constructs": report["sourced"],
            "claimed_coordinates": coverage["claimed_coordinates"],
            "view_leaves": coverage["view_leaves"],
            "operational_gaps": report["audit"]["operational_gaps"],
            "property_premise_gaps": report["audit"]["property_premise_gaps"],
            "mutations": len(MUTATION_CODES),
            "mutation_failure_codes": mutation_reports,
            "generated_lean_lines": lean_text.count("\n"),
            "generated_lean_sha256": _sha256(committed_lean),
            "ledger_sha256": _sha256(committed_ledger),
            "receipt": {
                "exit_status": receipt.get("exit_status"),
                "wall_seconds": receipt.get("wall_seconds"),
                "axioms": axioms,
                "revision": receipt.get("provider", {}).get("revision"),
                "toolchain": receipt.get("provider", {}).get("toolchain"),
                "observed_at": receipt.get("observed_at"),
            },
            "live_elaboration": (
                "available"
                if _lake_available(checkout)
                else "Unsupported/F2O0-U-PROVIDER-ENVIRONMENT"
            ),
        }
    )
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    value = _read_json(EXPECTED, "frozen findings")
    _require(type(value) is dict, "expected findings root differs")
    return value


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
            print(
                json.dumps(
                    {
                        "outcome": "Unsupported",
                        "code": "F2O0-U-PROVIDER-ENVIRONMENT",
                        "detail": f"no pinned VCVio checkout with lake at {checkout}",
                    },
                    indent=2,
                )
            )
            return 2
        receipt = elaborate(checkout)
        RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", "utf-8")
        print(
            f"[formal-provider-observables-f2o0] elaborated {receipt['generated_file']} "
            f"in {receipt['wall_seconds']}s, exit {receipt['exit_status']}, "
            f"axioms {json.dumps(receipt['axioms'], sort_keys=True)}"
        )
        if receipt["exit_status"] != 0:
            print(receipt["stdout"])
            print(receipt["stderr"], file=sys.stderr)
    try:
        findings, metrics = evaluate(checkout)
    except GateFailure as error:
        print(f"F2-O0 gate failed: {error}", file=sys.stderr)
        return 1
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.emit_expected:
        print(json.dumps(observed, indent=2))
        return 0
    if args.check and observed != _load_expected():
        print(
            json.dumps(
                {"expected": _load_expected(), "observed": observed},
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    output: dict[str, Any] = {
        "aggregate": AGGREGATE,
        "outcomes": dict(sorted(counts.items())),
        "metrics": metrics,
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
