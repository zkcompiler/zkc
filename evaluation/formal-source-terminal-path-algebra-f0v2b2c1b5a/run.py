#!/usr/bin/env python3
"""Run the F0-V2B2C1B5A terminal path-algebra research gate."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
AGGREGATE = "F0V2B2C1B5A-C-TERMINAL-CONTRACT-INCOMPLETE"


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
        raise AssertionError(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


def _source(
    kind: str, reduction: int | None = None, output: int | None = None
) -> dict[str, Any]:
    return {"kind": kind, "reduction": reduction, "output": output}


def _effect(kind: str, reference: int) -> dict[str, Any]:
    return {"kind": kind, "ref": reference}


def _occurrence(guard: str | None, kind: str, reference: int) -> dict[str, Any]:
    return {"guard": guard, "effect": _effect(kind, reference)}


def safe_program() -> dict[str, Any]:
    """One branch-complete Accept/Abort/Reject pressure carrier.

    ``g`` selects the first reduction and Accept.  If that terminal is not
    selected, its false outcome makes the second, unconditional reduction's
    active region exactly ``not g``.  ``h`` then selects Abort versus the
    unconditional Reject fallback.  The two reductions are therefore
    disjoint consumers of the same linear initial claim.
    """

    return {
        "claims": [
            {"usage": "Linear", "source": _source("Initial")},
            {
                "usage": "Reusable",
                "source": _source("ReductionOutput", 0, 0),
            },
            {
                "usage": "Reusable",
                "source": _source("ReductionOutput", 1, 0),
            },
        ],
        "reductions": [
            {"inputs": [0], "outputs": [1]},
            {"inputs": [0], "outputs": [2]},
        ],
        "checks": [{"label": "bounded-check-0"}],
        "terminals": [
            {
                "verdict": "Accept",
                "public_outputs": ["check-output-0"],
                "required_true_checks": [],
                "dispositions": [[1, "Consume"]],
            },
            {
                "verdict": "Abort",
                "public_outputs": ["abort-code"],
                "required_true_checks": [],
                "dispositions": [[2, "Discharge"]],
            },
            {
                "verdict": "Reject",
                "public_outputs": ["reject-code"],
                "required_true_checks": [],
                "dispositions": [[2, "Discharge"]],
            },
        ],
        "occurrences": [
            _occurrence(None, "Check", 0),
            _occurrence("g", "Reduction", 0),
            _occurrence("g", "Terminal", 0),
            _occurrence(None, "Reduction", 1),
            _occurrence("h", "Terminal", 1),
            _occurrence(None, "Terminal", 2),
        ],
    }


def _mutate(name: str) -> dict[str, Any]:
    program = deepcopy(safe_program())
    if name == "final-fallback-guarded":
        program["occurrences"][-1]["guard"] = "z"
    elif name == "terminal-backlink-duplicate":
        program["occurrences"][-1]["effect"]["ref"] = 1
    elif name == "terminal-reference-absent":
        program["occurrences"][-1]["effect"]["ref"] = 9
    elif name == "claim-output-source":
        program["claims"][2]["source"]["reduction"] = 0
    elif name == "claim-output-closure":
        program["reductions"][1]["outputs"] = []
    elif name == "reduction-empty-input":
        program["reductions"][1]["inputs"] = []
    elif name == "reduction-claim-reference":
        program["reductions"][1]["inputs"] = [9]
    elif name == "linear-consumer-overlap":
        second = program["occurrences"].pop(3)
        program["occurrences"].insert(2, second)
    elif name == "reduction-input-dead":
        program["reductions"][1]["inputs"] = [1]
    elif name == "accept-disposes-dead":
        program["terminals"][0]["dispositions"] = [[0, "Consume"]]
    elif name == "accept-omits-live":
        program["terminals"][0]["dispositions"] = []
    elif name == "abort-disposes-absent":
        program["terminals"][1]["dispositions"] = [[1, "Discharge"]]
    elif name == "abort-omits-live":
        program["terminals"][1]["dispositions"] = []
    elif name == "reject-omits-live":
        program["terminals"][2]["dispositions"] = []
    elif name == "disposition-duplicate":
        program["terminals"][0]["dispositions"] = [
            [1, "Consume"],
            [1, "Discharge"],
        ]
    elif name == "disposition-reference":
        program["terminals"][0]["dispositions"] = [[9, "Consume"]]
    elif name == "path-ambiguous-consumer":
        program["occurrences"][3]["guard"] = "x"
    elif name == "required-check-after-terminal":
        program["terminals"][0]["required_true_checks"] = [0]
        check = program["occurrences"].pop(0)
        program["occurrences"].insert(3, check)
    elif name == "required-check-guard-not-implied":
        program["terminals"][0]["required_true_checks"] = [0]
        program["occurrences"][0]["guard"] = "k"
    elif name == "malformed-verdict":
        program["terminals"][0]["verdict"] = "Success"
    elif name == "unsupported-effect":
        program["occurrences"][0]["effect"]["kind"] = "Message"
    else:  # pragma: no cover - test table is closed
        raise KeyError(name)
    return program


MUTATIONS: tuple[tuple[str, str, str], ...] = (
    ("final-fallback-guarded", "Refused", "F0V2B2C1B5A-R-FINAL-FALLBACK"),
    ("terminal-backlink-duplicate", "Refused", "F0V2B2C1B5A-R-BACKLINK"),
    ("terminal-reference-absent", "Refused", "F0V2B2C1B5A-R-EFFECT-REFERENCE"),
    ("claim-output-source", "Refused", "F0V2B2C1B5A-R-CLAIM-SOURCE"),
    ("claim-output-closure", "Refused", "F0V2B2C1B5A-R-CLAIM-SOURCE"),
    ("reduction-empty-input", "Refused", "F0V2B2C1B5A-R-REDUCTION-INPUTS"),
    ("reduction-claim-reference", "Refused", "F0V2B2C1B5A-R-CLAIM-REFERENCE"),
    ("linear-consumer-overlap", "Refused", "F0V2B2C1B5A-R-LINEAR-PATH-OVERLAP"),
    ("reduction-input-dead", "Refused", "F0V2B2C1B5A-R-REDUCTION-LIVENESS"),
    ("accept-disposes-dead", "Refused", "F0V2B2C1B5A-R-TERMINAL-CLOSURE"),
    ("accept-omits-live", "Refused", "F0V2B2C1B5A-R-TERMINAL-CLOSURE"),
    ("abort-disposes-absent", "Refused", "F0V2B2C1B5A-R-TERMINAL-CLOSURE"),
    ("abort-omits-live", "Refused", "F0V2B2C1B5A-R-TERMINAL-CLOSURE"),
    ("reject-omits-live", "Refused", "F0V2B2C1B5A-R-TERMINAL-CLOSURE"),
    ("disposition-duplicate", "Refused", "F0V2B2C1B5A-R-DISPOSITION-UNIQUE"),
    ("disposition-reference", "Refused", "F0V2B2C1B5A-R-DISPOSITION-REFERENCE"),
    ("path-ambiguous-consumer", "Refused", "F0V2B2C1B5A-R-PATH-AMBIGUITY"),
    ("required-check-after-terminal", "Refused", "F0V2B2C1B5A-R-CHECK-OCCURRENCE"),
    ("required-check-guard-not-implied", "Refused", "F0V2B2C1B5A-R-CHECK-OCCURRENCE"),
    ("malformed-verdict", "Malformed", "F0V2B2C1B5A-M-VERDICT"),
    ("unsupported-effect", "Unsupported", "F0V2B2C1B5A-U-EFFECT"),
)


def _candidate(model: ModuleType, program: object) -> tuple[str, str, object | None]:
    try:
        result = model.analyze(program)
        return result.outcome, result.code, result
    except model.PathFailure as error:
        return error.outcome, error.code, None


def _expect(
    operation: Callable[[], tuple[str, str, object | None]],
    outcome: str,
    code: str,
    label: str,
) -> object | None:
    observed_outcome, observed_code, result = operation()
    _require(
        observed_outcome == outcome,
        f"{label}: expected {outcome}, got {observed_outcome}",
    )
    _require(observed_code == code, f"{label}: expected {code}, got {observed_code}")
    return result


def _inventory_family() -> dict[str, Any]:
    value = json.loads(INVENTORY.read_text(encoding="utf-8"))
    families = [
        item
        for item in value["required_pressure_families"]
        if item["id"] == "terminal-abort-consume-discharge"
    ]
    _require(len(families) == 1, "terminal family is absent or duplicated in B2A")
    return families[0]


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b5a_model", MODEL)
    independent = _load("_zkc_f0v2b2c1b5a_independent", INDEPENDENT)
    findings: list[Finding] = []

    family = _inventory_family()
    _require(family["stage"] == "B2C", "terminal pressure family moved stages")
    _require(
        set(family["views"])
        == {"PublicCoinView", "EffectView", "ClaimReductionView", "ExecutionView"},
        "terminal pressure view set drifted",
    )
    findings.append(
        _finding(
            "predecessor-and-family-pin", "Affirmative", "F0V2B2C1B5A-A-PREDECESSOR-PIN"
        )
    )

    model_source = MODEL.read_text(encoding="utf-8")
    cold_source = INDEPENDENT.read_text(encoding="utf-8")
    _require(
        "itertools" not in model_source and "product(" not in model_source,
        "candidate path analyzer enumerates assignments",
    )
    _require(
        "import model" not in cold_source
        and "from model" not in cold_source
        and "_zkc_f0v2b2c1b5a_model" not in cold_source,
        "independent oracle imports the candidate",
    )
    findings.append(
        _finding(
            "candidate-and-oracle-separation",
            "Affirmative",
            "F0V2B2C1B5A-A-ORACLE-SEPARATION",
        )
    )

    program = safe_program()
    result = _expect(
        lambda: _candidate(model, program),
        "Affirmative",
        "F0V2B2C1B5A-A-COMPACT-PATH-ANALYSIS",
        "safe terminal carrier",
    )
    assert result is not None
    oracle = independent.evaluate_all(program)
    _require(oracle["valid"], f"independent oracle rejected positive carrier: {oracle}")
    _require(
        oracle["assignments"] == 4, "positive oracle did not cover both guard atoms"
    )
    _require(
        oracle["terminal_counts"] == {"Abort": 1, "Accept": 2, "Reject": 1},
        "first-active terminal counts differ",
    )
    findings.append(
        _finding(
            "branch-complete-terminal-carrier",
            "Affirmative",
            "F0V2B2C1B5A-A-TERMINAL-CARRIER",
        )
    )

    expected_regions = [
        {"positive": [], "negative": [], "impossible": False},
        {"positive": ["g"], "negative": [], "impossible": False},
        {"positive": ["g"], "negative": [], "impossible": False},
        {"positive": [], "negative": ["g"], "impossible": False},
        {"positive": ["h"], "negative": ["g"], "impossible": False},
        {"positive": [], "negative": ["g", "h"], "impossible": False},
    ]
    _require(
        [item.value() for item in result.active_regions] == expected_regions,
        "active-region derivation differs",
    )
    _require(
        result.terminal_live_claims == ((1,), (2,), (2,)),
        "terminal live-claim sets differ",
    )
    findings.append(
        _finding(
            "first-active-terminal-regions",
            "Affirmative",
            "F0V2B2C1B5A-A-FIRST-ACTIVE-REGIONS",
        )
    )
    findings.append(
        _finding(
            "path-sensitive-claim-closure",
            "Affirmative",
            "F0V2B2C1B5A-A-PATH-CLAIM-CLOSURE",
        )
    )

    _require(
        result.operations < 128, "bounded carrier crossed the compact operation budget"
    )
    findings.append(
        _finding(
            "compact-no-assignment-analysis",
            "Affirmative",
            "F0V2B2C1B5A-A-COMPACT-BOUND",
        )
    )

    mutation_agreement = 0
    for name, outcome, code in MUTATIONS:
        mutated = _mutate(name)
        _expect(lambda value=mutated: _candidate(model, value), outcome, code, name)
        oracle_result = independent.evaluate_all(mutated)
        _require(
            not oracle_result["valid"], f"independent oracle accepted mutation {name}"
        )
        findings.append(_finding(name, outcome, code))
        mutation_agreement += 1
    findings.append(
        _finding(
            "mutation-oracle-agreement",
            "Affirmative",
            "F0V2B2C1B5A-A-MUTATION-AGREEMENT",
        )
    )

    required_check = deepcopy(program)
    required_check["terminals"][0]["required_true_checks"] = [0]
    check_result = _expect(
        lambda: _candidate(model, required_check),
        "CannotAnswer",
        "F0V2B2C1B5A-C-REQUIRED-CHECK-TRUTH",
        "required Check truth",
    )
    assert check_result is not None
    check_oracle = independent.evaluate_all(required_check)
    _require(
        not check_oracle["valid"], "opaque required Check truth unexpectedly closed"
    )
    _require(
        "required-check-not-true" in check_oracle["violations"],
        "oracle did not expose false required Check",
    )
    findings.append(
        _finding(
            "required-check-truth-law",
            "CannotAnswer",
            "F0V2B2C1B5A-C-REQUIRED-CHECK-TRUTH",
        )
    )

    _require(
        set(program["terminals"][0])
        == {"verdict", "public_outputs", "required_true_checks", "dispositions"},
        "terminal source shape drifted",
    )
    findings.append(
        _finding(
            "required-reduction-selector",
            "CannotAnswer",
            "F0V2B2C1B5A-C-REQUIRED-REDUCTION",
        )
    )
    findings.append(
        _finding(
            "full-terminal-owner-projection",
            "CannotAnswer",
            "F0V2B2C1B5A-C-FULL-TERMINAL-PROJECTION",
        )
    )
    findings.append(
        _finding(
            "general-guard-implication",
            "CannotAnswer",
            "F0V2B2C1B5A-C-GENERAL-GUARD-IMPLICATION",
        )
    )
    findings.append(
        _finding(
            "target-publication", "CannotAnswer", "F0V2B2C1B5A-C-TARGET-PUBLICATION"
        )
    )
    findings.append(
        _finding(
            "live-implementation-correspondence",
            "CannotAnswer",
            "F0V2B2C1B5A-C-LIVE-CORRESPONDENCE",
        )
    )
    findings.append(
        _finding("formal-proof", "CannotAnswer", "F0V2B2C1B5A-C-FORMAL-PROOF")
    )
    findings.append(
        _finding("cryptographic-security", "CannotAnswer", "F0V2B2C1B5A-C-SECURITY")
    )
    findings.append(_finding("q1-correspondence", "CannotAnswer", "F0V2B2C1B5A-C-Q1"))
    findings.append(_finding("terminal-contract-aggregate", "CannotAnswer", AGGREGATE))

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    metrics = {
        "findings": len(findings),
        "findings_sha256": checksum,
        "candidate_operations": result.operations,
        "positive_assignments": oracle["assignments"],
        "positive_terminal_counts": oracle["terminal_counts"],
        "mutations": mutation_agreement,
        "required_check_assignments": check_oracle["assignments"],
        "required_check_counterexample": check_oracle["first_counterexample"],
    }
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    findings, metrics = evaluate()
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.check:
        expected = _load_expected()
        if observed != expected:
            print(
                json.dumps(
                    {"expected": expected, "observed": observed},
                    indent=2,
                    sort_keys=True,
                )
            )
            return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    print(
        json.dumps(
            {
                "aggregate": AGGREGATE,
                "outcomes": dict(sorted(counts.items())),
                "metrics": metrics,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
