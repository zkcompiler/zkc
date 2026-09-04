#!/usr/bin/env python3
"""Frozen gate for the F2-P0 Schnorr Relations--Plan coupling audit."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

from independent import IndependentFailure, reconstruct as reconstruct_independent
from model import AuditFailure, reconstruct as reconstruct_direct


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"
AGGREGATE = "F2P0-C-EXACT-COUPLING-UNDERDETERMINED"


def _digest(value: Any) -> str:
    body = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(body).hexdigest()


def _finding(subject: str, outcome: str, code: str) -> list[str]:
    return [subject, outcome, code]


def report() -> dict[str, Any]:
    direct = reconstruct_direct()
    independent = reconstruct_independent()
    if direct["path"] == independent["path"]:
        raise AuditFailure("the two reconstruction paths have the same identity")
    if direct["agreement"] != independent["agreement"]:
        raise AuditFailure(
            "typed and cold reconstructions disagree\n"
            + json.dumps(
                {"direct": direct["agreement"], "independent": independent["agreement"]},
                indent=2,
                sort_keys=True,
            )
        )
    if direct["basis"] != independent["basis"]:
        raise AuditFailure("typed and cold source-pin audits disagree")
    direct_source = (HERE / "model.py").read_text(encoding="utf-8")
    independent_source = (HERE / "independent.py").read_text(encoding="utf-8")
    if "import independent" in direct_source or "import model" in independent_source:
        raise AuditFailure("reconstruction paths import one another")

    findings = [
        _finding("exact-cutoff-and-source-pins", "Affirmative", "F2P0-A-SOURCE-PINS"),
        _finding("f1-core-and-protocol-reconstructed", "Affirmative", "F2P0-A-SUBJECT"),
        _finding("six-view-cold-reconstruction", "Affirmative", "F2P0-A-COLD-VIEWS"),
        _finding("f2o0-five-gap-inventory", "Affirmative", "F2P0-A-GAP-INVENTORY"),
        _finding("statement-binding-role-site", "Affirmative", "F2P0-A-STATEMENT-SITE"),
        _finding("commit-and-respond-role-sites", "Affirmative", "F2P0-A-DECISION-SITES"),
        _finding("forward-contract-construction-route", "Affirmative", "F2P0-A-CONSTRUCTION-ROUTE"),
        _finding("acyclic-independent-attachment-routes", "Affirmative", "F2P0-A-ACYCLIC-ATTACHMENTS"),
        _finding("conditional-owner-coordinate-matrix", "Affirmative", "F2P0-A-CONDITIONAL-COORDINATES"),
        _finding("knowledge-shaped-finite-completion", "Affirmative", "F2P0-A-AMBIGUITY-WITNESS-A"),
        _finding("statement-only-finite-completion", "Affirmative", "F2P0-A-AMBIGUITY-WITNESS-B"),
        _finding("plus-one-response-controls", "Refused", "F2P0-R-BAD-RESPONSE"),
        _finding("verifier-check-implies-relation", "Refused", "F2P0-R-CHECK-AS-RELATION"),
        _finding("decision-site-implies-honest-algorithm", "Refused", "F2P0-R-ROLE-AS-ALGORITHM"),
        _finding("plan-realizes-implies-honesty", "Refused", "F2P0-R-REALIZES-AS-HONESTY"),
        _finding("finite-completion-selection", "Refused", "F2P0-R-COMPLETION-SELECTION"),
        _finding("two-path-exact-agreement", "Affirmative", "F2P0-A-PATH-AGREEMENT"),
        _finding("exact-relation-definition", "CannotAnswer", "F2P0-C-RELATION-DEFINITION"),
        _finding("exact-relation-semantic-model", "CannotAnswer", "F2P0-C-RELATION-MODEL"),
        _finding("definition-model-correspondence", "CannotAnswer", "F2P0-C-DEFINITION-MODEL"),
        _finding("concrete-relation-instance", "CannotAnswer", "F2P0-C-RELATION-INSTANCE"),
        _finding("current-relation-predicate", "CannotAnswer", "F2P0-C-RELATION"),
        _finding("current-witness-type", "CannotAnswer", "F2P0-C-WITNESS-TYPE"),
        _finding("current-prover-private-state", "CannotAnswer", "F2P0-C-PROVER-STATE"),
        _finding("current-honest-commit", "CannotAnswer", "F2P0-C-HONEST-COMMIT"),
        _finding("current-honest-respond", "CannotAnswer", "F2P0-C-HONEST-RESPOND"),
        _finding("provider-total-relation-translation", "CannotAnswer", "F2P0-C-PROVIDER-RELATION"),
        _finding("provider-private-state-translation", "CannotAnswer", "F2P0-C-PROVIDER-STATE"),
        _finding("relation-relative-plan-honesty", "CannotAnswer", "F2P0-C-HONESTY-JOIN"),
        _finding("exact-relations-plan-coupling", "CannotAnswer", AGGREGATE),
    ]
    outcomes: dict[str, int] = {}
    for _name, outcome, _code in findings:
        outcomes[outcome] = outcomes.get(outcome, 0) + 1
    agreement = direct["agreement"]
    return {
        "aggregate": f"CannotAnswer/{AGGREGATE}",
        "finding_codes": findings,
        "findings_sha256": _digest(findings),
        "measurements": {
            **direct["basis"],
            "reconstruction_paths": 2,
            "verifier_cases_per_path": agreement["subject"]["verifier_cases"],
            "finite_completions": len(agreement["ambiguity_witnesses"]),
            "accepted_honest_runs": sum(
                item["accepted_honest_runs"] for item in agreement["ambiguity_witnesses"]
            ),
            "rejected_plus_one_controls": sum(
                item["rejected_plus_one_controls"] for item in agreement["ambiguity_witnesses"]
            ),
            "premises": len(agreement["premises"]),
            "current_premise_coordinates": sum(
                item["current_premise_coordinate"] is not None
                for item in agreement["premises"].values()
            ),
            "conditional_owner_coordinate_families": sum(
                bool(item["conditional_owner_coordinates"])
                for item in agreement["premises"].values()
            ),
            "outcomes": dict(sorted(outcomes.items())),
            "agreement_sha256": direct["agreement_sha256"],
        },
        "premise_matrix": agreement["premises"],
        "ambiguity_witnesses": agreement["ambiguity_witnesses"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with frozen findings")
    parser.add_argument("--json", action="store_true", help="print the complete report")
    args = parser.parse_args()
    try:
        current = report()
        if args.check:
            expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
            if current != expected:
                raise AuditFailure(
                    "frozen findings drift\nexpected: "
                    + json.dumps(expected, sort_keys=True)
                    + "\ncurrent:  "
                    + json.dumps(current, sort_keys=True)
                )
    except (AuditFailure, IndependentFailure, OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        print(f"F2-P0 coupling audit failed: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(current, indent=2, sort_keys=True))
    else:
        counts = current["measurements"]["outcomes"]
        print(
            f"{current['aggregate']}: {len(current['finding_codes'])} findings "
            f"({counts.get('Affirmative', 0)} affirmative, "
            f"{counts.get('Refused', 0)} refused, "
            f"{counts.get('CannotAnswer', 0)} cannot-answer)"
        )
        print(
            "bounded result: the contracts provide an acyclic attachment grammar, "
            "but the current target does not select an exact relation, Plan, or provider premise"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
