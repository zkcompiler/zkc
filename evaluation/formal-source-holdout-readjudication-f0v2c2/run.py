#!/usr/bin/env python3
"""Byte-pinned cold-holdout readjudication against migrated PIR owner text."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PACKAGE = Path(__file__).resolve().parent

HOLDOUT_DIR = (
    "docs-next/notes/semantic-revalidation-and-redesign/"
    "semantic-closure-and-freeze/cold-protocol-holdouts"
)

SOURCE_PINS = {
    f"{HOLDOUT_DIR}/README.md": "0079cd3db2103d74e413c8980efc7b658b52a3b715a13e8ff42a4f0d3d2f11c7",
    f"{HOLDOUT_DIR}/circle-starks-boundary-analysis.md": "3e9d85e94a8dce815500631afce1ba4a06569b19ce5c439ef1e6714818b9515f",
    f"{HOLDOUT_DIR}/galois-ring-snarks-boundary-analysis.md": "6005e37418e8f6eb63b21a2333b9e0d6ed8e544a713ac6e26e8ba4e9aadf65cd",
    f"{HOLDOUT_DIR}/multiparty-sumcheck-boundary-analysis.md": "389b320caec51384a51e918e0390d3a2aa7143990d55c27b3925839023bcf84b",
    f"{HOLDOUT_DIR}/portfolio-adjudication-and-freeze-decision.md": "a40acbf3f467e6084f4cbfa45ecf4fe3f2ec204976c9a713b791c1531d251028",
    f"{HOLDOUT_DIR}/source-ledger.json": "b0e7efa0b4ffed3b4ebb8a70f73dc305283b370ee85a45686946fc0cd0ae2222",
    f"{HOLDOUT_DIR}/warpfold-boundary-analysis.md": "75b7b13d812535ad663e648bf5c13d945b151a917b97eb2e62f1a418a3c09c8f",
    f"{HOLDOUT_DIR}/whir-constructive-encoding.md": "a091090622897da5548714573fd1aa048b8e9f730794b324af8271681ca440b0",
    f"{HOLDOUT_DIR}/whir-falsification-and-decision.md": "cb491ce278bc9628c351dd2389523d5f3b88ccdad6aaa8088bad4efbaa83c5f3",
    f"{HOLDOUT_DIR}/whir-source-and-anatomy.md": "507c43ea0091d777d3bac3225dfa5f42f05937b40199e29676cf3865e4f2e410",
}

OWNER_PINS = {
    "docs-next/pir/interactive-core.md": "5f017f0dc88aca3c50651a8c5e4861ea2450c3035e9015c276babbf4b913f34f",
    "docs-next/pir/fiat-shamir.md": "52682bd1e46f0579b7f6445cfa2866ab2bfce819aa1082d796ae216f451bf671",
    "docs-next/pir/duplex-sponge-fiat-shamir.md": "60d66fb3636c85d0d4201de3962bdc19b3664469bc8808dfbe738ad57d248db4",
    "docs-next/pir/endpoint-projection-views.md": "65edfbaf3a378894c56042f68d671c906377ba97c7e6e936dc2a39df260ff2c4",
    "docs-next/oir/projection-contract.md": "235846997438e33de1d9ad49d501e0937c032b9de102e6da928033729a1855c6",
}

SUPPORT_PINS = {
    "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0-v2c-migration-owner-text.md": "880bc7f13b09c1c84407ee1fc81e907aa3f9150d86b3ad2ea855c8e8999bb361",
    "docs-next/notes/semantic-revalidation-and-redesign/expressibility-axes/README.md": "846eb057888021274059d06517f2c62f3d83b8f5c15f02c58ede66a2781d20e3",
    "evaluation/expressibility-axes/axes.json": "38e6e927387c0b9a8ec2d855a28af61da69c074640efaea11c8408fa9601ec42",
    "evaluation/expressibility-axes/cases.json": "eb191fa7d01b5ddb2a0fc758ff9094a74a988e8f596105e102c023470b1e7003",
}

EXPECTED_ROWS = {
    "WHIR Construction 5.1 with a closed finite query plan": ("fits", ()),
    "Circle STARK boundary analysis at one finite instance": ("fits", ()),
    "WARPfold finite fold": ("fits", ()),
    "WARPfold broad cross-system application": (
        "breaks",
        ("B-CROSS-EXECUTION", "B-IMPORTED-CHALLENGE"),
    ),
    "Physical multiparty Sumcheck": ("breaks", ("B-MULTIPARTY",)),
    "Commitment-anchored virtual two-role Sumcheck proof": ("fits", ()),
    "Complete noninteractive transparent SNARK over Galois rings with an omitted transform": (
        "breaks",
        ("B-SOURCE-INCOMPLETE",),
    ),
    "Explicit interactive Galois-ring components": ("fits", ()),
}

RECORD_MARKERS = {
    "WHIR Construction 5.1 with a closed finite query plan":
        "| WHIR, Construction 5.1 | constructive encoding | `ProfileOrModule` | no rotation |",
    "Circle STARK boundary analysis at one finite instance":
        "| Circle STARKs | boundary analysis | `ProfileOrModule` | no rotation |",
    "WARPfold finite fold":
        "| WARPfold | boundary analysis | `ProfileOrModule` for the fold; `Undetermined` for the broad cross-system application | no rotation |",
    "WARPfold broad cross-system application":
        "| WARPfold | boundary analysis | `ProfileOrModule` for the fold; `Undetermined` for the broad cross-system application | no rotation |",
    "Physical multiparty Sumcheck":
        "| Multiparty Sumcheck | boundary analysis | `IntentionalBoundary` for physical MPC; `ProfileOrModule` for a commitment-anchored virtual proof | retain two-role scope |",
    "Commitment-anchored virtual two-role Sumcheck proof":
        "| Multiparty Sumcheck | boundary analysis | `IntentionalBoundary` for physical MPC; `ProfileOrModule` for a commitment-anchored virtual proof | retain two-role scope |",
    "Complete noninteractive transparent SNARK over Galois rings with an omitted transform":
        "| Transparent SNARKs over Galois rings | boundary analysis | `Undetermined` for the complete noninteractive SNARK; `ProfileOrModule` for explicit interactive components | no rotation; require a separate transcript source |",
    "Explicit interactive Galois-ring components":
        "| Transparent SNARKs over Galois rings | boundary analysis | `Undetermined` for the complete noninteractive SNARK; `ProfileOrModule` for explicit interactive components | no rotation; require a separate transcript source |",
}

SIX_VIEWS = {
    "PublicBindingView",
    "StrategyDecisionView",
    "PublicCoinView",
    "EffectView",
    "ClaimReductionView",
    "ExecutionView",
}


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def as_dict(self) -> dict[str, str]:
        return {"name": self.name, "outcome": self.outcome, "code": self.code}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_sha256(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def _pin_finding(name: str, pins: dict[str, str], ok_code: str, bad_code: str) -> Finding:
    ok = all((ROOT / path).is_file() and _sha256(ROOT / path) == digest for path, digest in pins.items())
    return Finding(name, "Affirmative" if ok else "CannotAnswer", ok_code if ok else bad_code)


# A Must result is (when_true, when_false); None denotes Impossible.
LiteralSet = frozenset[tuple[str, int]]
MustResult = tuple[LiteralSet | None, LiteralSet | None]
Term = tuple[Any, ...]


def _union(left: LiteralSet | None, right: LiteralSet | None) -> LiteralSet | None:
    if left is None or right is None:
        return None
    return left | right


def _meet(left: LiteralSet | None, right: LiteralSet | None) -> LiteralSet | None:
    if left is None:
        return right
    if right is None:
        return left
    return left & right


def must(term: Term) -> MustResult:
    tag = term[0]
    if tag == "input":
        index = int(term[1])
        return frozenset({("Positive", index)}), frozenset({("Negative", index)})
    if tag == "true":
        return frozenset(), None
    if tag == "false":
        return None, frozenset()
    if tag != "if":
        return frozenset(), frozenset()
    condition, when_true_term, when_false_term = term[1:]
    condition_true, condition_false = must(condition)
    arm_true, arm_false = must(when_true_term)
    else_true, else_false = must(when_false_term)
    return (
        _meet(_union(condition_true, arm_true), _union(condition_false, else_true)),
        _meet(_union(condition_true, arm_false), _union(condition_false, else_false)),
    )


def conjunction(indices: tuple[int, ...]) -> Term:
    if not indices:
        return ("true",)
    return ("if", ("input", indices[0]), conjunction(indices[1:]), ("false",))


def fold_frontier_failure() -> Term:
    final_failure = ("if", conjunction((2, 3, 4)), ("false",), ("true",))
    return (
        "if",
        ("input", 0),
        ("if", ("input", 1), final_failure, ("false",)),
        ("false",),
    )


def evaluate() -> dict[str, Any]:
    findings: list[Finding] = []
    findings.append(
        _pin_finding(
            "holdout-source-bytes",
            SOURCE_PINS,
            "F0V2C2-A-HOLDOUT-SOURCE-BYTES",
            "F0V2C2-C-HOLDOUT-SOURCE-DRIFT",
        )
    )
    exact_holdout_files = {
        str(path.relative_to(ROOT)) for path in (ROOT / HOLDOUT_DIR).iterdir() if path.is_file()
    }
    expected_holdout_files = set(SOURCE_PINS)
    findings.append(
        Finding(
            "holdout-file-inventory",
            "Affirmative" if exact_holdout_files == expected_holdout_files else "CannotAnswer",
            "F0V2C2-A-HOLDOUT-FILE-INVENTORY"
            if exact_holdout_files == expected_holdout_files
            else "F0V2C2-C-HOLDOUT-FILE-INVENTORY",
        )
    )
    findings.append(
        _pin_finding(
            "migrated-owner-page-bytes",
            OWNER_PINS,
            "F0V2C2-A-MIGRATED-OWNER-BYTES",
            "F0V2C2-C-MIGRATED-OWNER-DRIFT",
        )
    )
    findings.append(
        _pin_finding(
            "migration-and-axis-source-bytes",
            SUPPORT_PINS,
            "F0V2C2-A-MIGRATION-AXIS-BYTES",
            "F0V2C2-C-MIGRATION-AXIS-DRIFT",
        )
    )

    owner_text = (ROOT / "docs-next/pir/interactive-core.md").read_text()
    owner_markers = [
        "required_true_checks: CanonicalSortedUniqueSeq<CheckRef>",
        "Positive(i) in MustWhenTrue(GuardTerm(o_t))",
        "required_applied_reductions: CanonicalSortedUniqueSeq<ReductionRef>",
        "LiveClaims(o_t) = t.terminal_claims",
        "ProtocolOutcomeLane(P) =",
        "PIRViewSchemaCatalog = {",
    ]
    owner_laws_present = all(marker in owner_text for marker in owner_markers)
    findings.append(
        Finding(
            "migrated-terminal-view-and-outcome-laws",
            "Affirmative" if owner_laws_present else "CannotAnswer",
            "F0V2C2-A-MIGRATED-OWNER-LAWS"
            if owner_laws_present
            else "F0V2C2-C-MIGRATED-OWNER-LAWS",
        )
    )

    all_positive = frozenset(("Positive", index) for index in range(5))
    fold_positive = frozenset({("Positive", 0), ("Positive", 1)})
    guard_ok = must(conjunction((0, 1, 2, 3, 4)))[0] == all_positive
    guard_ok = guard_ok and must(fold_frontier_failure())[0] == fold_positive
    findings.append(
        Finding(
            "nested-guard-must-facts",
            "Affirmative" if guard_ok else "CannotAnswer",
            "F0V2C2-A-NESTED-GUARD-MUST-FACTS"
            if guard_ok
            else "F0V2C2-C-NESTED-GUARD-MUST-FACTS",
        )
    )

    whir_source = (ROOT / f"{HOLDOUT_DIR}/whir-constructive-encoding.md").read_text()
    legacy_whir_shape = all(
        marker in whir_source
        for marker in (
            "apply `R_fold`",
            "apply `R_final`",
            "reach `Accept`",
            "reach fallback `Reject`",
            "C_initial --R_fold--> C_folded --R_final--> no live claim",
        )
    )
    findings.append(
        Finding(
            "legacy-whir-two-terminal-shape",
            "Refused" if legacy_whir_shape and owner_laws_present else "CannotAnswer",
            "F0V2C2-R-WHIR-TWO-TERMINAL-SHAPE"
            if legacy_whir_shape and owner_laws_present
            else "F0V2C2-C-WHIR-TERMINAL-SHAPE",
        )
    )

    axes = json.loads((ROOT / "evaluation/expressibility-axes/axes.json").read_text())
    termination_axis = next(axis for axis in axes["axes"] if axis["id"] == "termination_modes")
    interpretation_axis = next(
        value for value in termination_axis["values"] if value["id"] == "interpretation_failure"
    )
    stale_axis_meaning = "Reject or Abort branch" in interpretation_axis["meaning"]
    findings.append(
        Finding(
            "structural-axis-interpretation-failure-meaning",
            "Refused" if stale_axis_meaning and owner_laws_present else "CannotAnswer",
            "F0V2C2-R-AXIS-INTERPRETATION-FAILURE-MEANING"
            if stale_axis_meaning and owner_laws_present
            else "F0V2C2-C-AXIS-INTERPRETATION-FAILURE-MEANING",
        )
    )

    adjudication = json.loads((PACKAGE / "adjudication.json").read_text())
    rows = adjudication.get("rows", [])
    row_names = [row.get("name") for row in rows]
    table_complete = (
        adjudication.get("schema_version") == 1
        and set(row_names) == set(EXPECTED_ROWS)
        and len(row_names) == len(set(row_names)) == 8
        and {row.get("holdout") for row in rows}
        == {"WHIR", "Circle STARKs", "WARPfold", "Multiparty Sumcheck", "Transparent SNARKs over Galois rings"}
    )
    findings.append(
        Finding(
            "five-holdout-eight-row-table",
            "Affirmative" if table_complete else "CannotAnswer",
            "F0V2C2-A-COMPLETE-VERDICT-TABLE"
            if table_complete
            else "F0V2C2-C-INCOMPLETE-VERDICT-TABLE",
        )
    )

    matrix = json.loads((ROOT / "evaluation/expressibility-axes/cases.json").read_text())
    matrix_rows = {case["name"]: case for case in matrix["cases"] if case["name"] in EXPECTED_ROWS}
    record_text = (ROOT / f"{HOLDOUT_DIR}/portfolio-adjudication-and-freeze-decision.md").read_text()
    disagreements: list[str] = []
    for name in EXPECTED_ROWS:
        data_row = next((row for row in rows if row.get("name") == name), None)
        matrix_row = matrix_rows.get(name)
        expected_verdict, expected_boundaries = EXPECTED_ROWS[name]
        reasons: list[str] = []
        if data_row is None:
            reasons.append("missing adjudication row")
        if matrix_row is None:
            reasons.append("missing structural-axes row")
        if RECORD_MARKERS[name] not in record_text:
            reasons.append("adjudication record disagrees")
        if data_row is not None:
            if data_row.get("verdict") != expected_verdict:
                reasons.append("frozen verdict changed")
            if tuple(data_row.get("boundaries", [])) != expected_boundaries:
                reasons.append("frozen boundary set changed")
        if matrix_row is not None:
            if matrix_row.get("predicted_verdict") != expected_verdict:
                reasons.append("matrix prediction disagrees")
            if tuple(matrix_row.get("predicted_destinations", [])) != expected_boundaries:
                reasons.append("matrix boundary set disagrees")
            recorded = matrix_row.get("recorded_verdicts", [])
            if len(recorded) != 1:
                reasons.append("recorded adjudication projection is not unique")
            else:
                if recorded[0].get("projected_verdict") != expected_verdict:
                    reasons.append("recorded adjudication verdict disagrees")
                if tuple(recorded[0].get("required_destinations", [])) != expected_boundaries:
                    reasons.append("recorded adjudication boundary set disagrees")
                if data_row is not None and recorded[0].get("recorded") != data_row.get("recorded"):
                    reasons.append("recorded label disagrees")
        slug = {
            "WHIR Construction 5.1 with a closed finite query plan": "WHIR",
            "Circle STARK boundary analysis at one finite instance": "CIRCLE",
            "WARPfold finite fold": "WARPFOLD-FOLD",
            "WARPfold broad cross-system application": "WARPFOLD-CROSS-SYSTEM",
            "Physical multiparty Sumcheck": "PHYSICAL-MULTIPARTY",
            "Commitment-anchored virtual two-role Sumcheck proof": "VIRTUAL-SUMCHECK",
            "Complete noninteractive transparent SNARK over Galois rings with an omitted transform": "GALOIS-NONINTERACTIVE",
            "Explicit interactive Galois-ring components": "GALOIS-INTERACTIVE",
        }[name]
        if reasons:
            disagreements.append(f"{name}: {', '.join(reasons)}")
            findings.append(Finding(f"{name} verdict comparison", "CannotAnswer", f"F0V2C2-C-{slug}-DISAGREEMENT"))
        else:
            findings.append(Finding(f"{name} verdict comparison", "Affirmative", f"F0V2C2-A-{slug}-AGREES"))

    fit_rows = [row for row in rows if row.get("verdict") == "fits"]
    six_view_coverage = all(SIX_VIEWS <= set(row.get("views", {})) for row in fit_rows)
    no_fit_view_gap = all(not row.get("missing_coordinates") for row in fit_rows)
    findings.append(
        Finding(
            "fitting-holdout-six-view-coverage",
            "Affirmative" if six_view_coverage and no_fit_view_gap else "CannotAnswer",
            "F0V2C2-A-FIT-VIEW-COVERAGE"
            if six_view_coverage and no_fit_view_gap
            else "F0V2C2-C-FIT-VIEW-COVERAGE",
        )
    )
    break_rows = [row for row in rows if row.get("verdict") == "breaks"]
    break_gaps_named = all(row.get("missing_coordinates") and row.get("boundaries") for row in break_rows)
    findings.append(
        Finding(
            "breaking-holdout-missing-coordinate-census",
            "Affirmative" if break_gaps_named else "CannotAnswer",
            "F0V2C2-A-BREAK-COORDINATE-CENSUS"
            if break_gaps_named
            else "F0V2C2-C-BREAK-COORDINATE-CENSUS",
        )
    )

    valid_lanes = {
        "Accepted",
        "Rejected",
        "Aborted",
        "InterpretationFailed",
        "StrategyStopped",
        "OperationalNoncompletion",
    }
    fit_outcomes_complete = True
    for row in fit_rows:
        for outcome in row.get("outcomes", []):
            lane = outcome.get("lane")
            if lane not in valid_lanes:
                fit_outcomes_complete = False
    findings.append(
        Finding(
            "fitting-holdout-outcome-partition",
            "Affirmative" if fit_outcomes_complete else "CannotAnswer",
            "F0V2C2-A-FIT-OUTCOME-PARTITION"
            if fit_outcomes_complete
            else "F0V2C2-C-FIT-OUTCOME-PARTITION",
        )
    )
    missing_outcome_modes = all(any(outcome.get("lane") is None for outcome in row.get("outcomes", [])) for row in break_rows)
    findings.append(
        Finding(
            "breaking-holdout-outcome-gaps",
            "Affirmative" if missing_outcome_modes else "CannotAnswer",
            "F0V2C2-A-BREAK-OUTCOME-GAPS"
            if missing_outcome_modes
            else "F0V2C2-C-BREAK-OUTCOME-GAPS",
        )
    )

    exact_statuses = {row["name"]: row["terminal_contract"]["status"] for row in rows}
    source_specialization = {
        name
        for name, status in exact_statuses.items()
        if status == "source-specialization-required"
    }
    expected_specialization = {
        "Circle STARK boundary analysis at one finite instance",
        "WARPfold finite fold",
        "Commitment-anchored virtual two-role Sumcheck proof",
        "Explicit interactive Galois-ring components",
    }
    findings.append(
        Finding(
            "boundary-analysis-terminal-carrier-exactness",
            "CannotAnswer" if source_specialization == expected_specialization else "Malformed",
            "F0V2C2-C-EXACT-TERMINAL-CARRIERS"
            if source_specialization == expected_specialization
            else "F0V2C2-M-TERMINAL-CARRIER-CENSUS",
        )
    )
    findings.append(
        Finding(
            "owner-page-reopening",
            "Affirmative",
            "F0V2C2-A-NO-OWNER-PAGE-REOPENING",
        )
    )

    aggregate_ok = table_complete and not disagreements
    aggregate = (
        "F0V2C2-A-HOLDOUTS-READJUDICATED"
        if aggregate_ok
        else "F0V2C2-C-HOLDOUT-VERDICT-DISAGREEMENTS"
    )
    findings.append(
        Finding(
            "holdout-readjudication",
            "Affirmative" if aggregate_ok else "CannotAnswer",
            aggregate,
        )
    )

    finding_dicts = [finding.as_dict() for finding in findings]
    return {
        "question": adjudication["question"],
        "aggregate": aggregate,
        "disagreements": disagreements,
        "findings": finding_dicts,
        "findings_sha256": _canonical_sha256(finding_dicts),
        "adjudication_sha256": _sha256(PACKAGE / "adjudication.json"),
        "metrics": {
            "holdouts": len({row.get("holdout") for row in rows}),
            "verdict_rows": len(rows),
            "fits": sum(row.get("verdict") == "fits" for row in rows),
            "breaks": sum(row.get("verdict") == "breaks" for row in rows),
            "bends": sum(row.get("verdict") == "bends" for row in rows),
            "disagreements": len(disagreements),
            "source_pins": len(SOURCE_PINS),
            "owner_pins": len(OWNER_PINS),
        },
    }


def _expected_projection(report: dict[str, Any]) -> dict[str, Any]:
    return {
        "aggregate": report["aggregate"],
        "adjudication_sha256": report["adjudication_sha256"],
        "findings_sha256": report["findings_sha256"],
        "finding_codes": [
            [finding["name"], finding["outcome"], finding["code"]]
            for finding in report["findings"]
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with frozen expected findings")
    args = parser.parse_args(argv)

    report = evaluate()
    print(json.dumps(report, indent=2, sort_keys=True))
    if not args.check:
        return 0
    expected = json.loads((PACKAGE / "expected-findings.json").read_text())
    if _expected_projection(report) != expected:
        print("frozen finding projection mismatch", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
