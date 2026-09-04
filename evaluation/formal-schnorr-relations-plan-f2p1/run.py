#!/usr/bin/env python3
"""Frozen gate for the F2-P1 exact Schnorr relation and Plan candidates."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

from independent import IndependentFailure, reconstruct as reconstruct_independent
from model import CandidateFailure, reconstruct as reconstruct_direct


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"
AGGREGATE = "F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE"


def _digest(value: Any) -> str:
    body = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(body).hexdigest()


def _finding(subject: str, outcome: str, code: str) -> list[str]:
    return [subject, outcome, code]


def report() -> dict[str, Any]:
    direct = reconstruct_direct()
    independent = reconstruct_independent()
    if direct["path"] == independent["path"]:
        raise CandidateFailure(
            "CheckerFailure",
            "F2P1-X-PATH-SEPARATION",
            "the two reconstruction paths have the same identity",
        )
    if direct["basis"] != independent["basis"]:
        raise CandidateFailure(
            "CheckerFailure",
            "F2P1-X-SOURCE-AGREEMENT",
            "the two source-pin audits disagree",
        )
    if direct["agreement"] != independent["agreement"]:
        raise CandidateFailure(
            "CheckerFailure",
            "F2P1-X-BODY-AGREEMENT",
            "typed and cold candidate reconstructions disagree\n"
            + json.dumps(
                {"direct": direct["agreement"], "independent": independent["agreement"]},
                indent=2,
                sort_keys=True,
            ),
        )
    if direct["agreement_sha256"] != independent["agreement_sha256"]:
        raise CandidateFailure(
            "CheckerFailure",
            "F2P1-X-IDENTITY-AGREEMENT",
            "the two agreement digests differ",
        )
    direct_source = (HERE / "model.py").read_text(encoding="utf-8")
    independent_source = (HERE / "independent.py").read_text(encoding="utf-8")
    if "import independent" in direct_source or "import model" in independent_source:
        raise CandidateFailure(
            "CheckerFailure",
            "F2P1-X-PATH-IMPORT",
            "candidate reconstruction paths import one another",
        )

    findings = [
        _finding("exact-cutoff-and-source-pins", "Affirmative", "F2P1-A-SOURCE-PINS"),
        _finding("f1r1b-fresh-protocol-subject", "Affirmative", "F2P1-A-SUBJECT"),
        _finding("finite-additive-z3-algebra", "Affirmative", "F2P1-A-ADDITIVE-ALGEBRA"),
        _finding("exact-relation-definition-candidate", "Affirmative", "F2P1-A-RELATION-DEFINITION"),
        _finding("four-interface-role-candidates", "Affirmative", "F2P1-A-INTERFACE-ROLES"),
        _finding("exact-semantic-model-candidate", "Affirmative", "F2P1-A-RELATION-MODEL"),
        _finding("definition-model-finite-correspondence", "Affirmative", "F2P1-A-DEFINITION-MODEL"),
        _finding("exact-relation-instance-family", "Affirmative", "F2P1-A-RELATION-INSTANCES"),
        _finding("representative-public-instance", "Affirmative", "F2P1-A-PUBLIC-INSTANCE"),
        _finding("protocol-statement-edge", "Affirmative", "F2P1-A-STATEMENT-EDGE"),
        _finding("protocol-challenge-response-phase-edges", "Affirmative", "F2P1-A-PHASE-EDGES"),
        _finding("protocol-relation-binding-candidate", "Affirmative", "F2P1-A-PROTOCOL-BINDING"),
        _finding("initial-claim-meaning", "CannotAnswer", "F2P1-C-INITIAL-CLAIM-ABSENT"),
        _finding("prover-plan-candidate", "Affirmative", "F2P1-A-PROVER-PLAN"),
        _finding("plan-realizes-candidate", "Affirmative", "F2P1-A-PLAN-REALIZES"),
        _finding("honest-commit-recipe", "Affirmative", "F2P1-A-HONEST-COMMIT"),
        _finding("honest-respond-recipe", "Affirmative", "F2P1-A-HONEST-RESPOND"),
        _finding("nonce-persistent-state", "Affirmative", "F2P1-A-NONCE-STATE"),
        _finding("plan-witness-surface", "Affirmative", "F2P1-A-WITNESS-SURFACE"),
        _finding("plan-witness-binding", "Affirmative", "F2P1-A-WITNESS-BINDING"),
        _finding("relation-predicate-premise-coordinate", "Affirmative", "F2P1-A-PREMISE-RELATION"),
        _finding("witness-type-premise-coordinate", "Affirmative", "F2P1-A-PREMISE-WITNESS"),
        _finding("prover-state-premise-coordinate", "Affirmative", "F2P1-A-PREMISE-STATE"),
        _finding("honest-commit-premise-coordinate", "Affirmative", "F2P1-A-PREMISE-COMMIT"),
        _finding("honest-respond-premise-coordinate", "Affirmative", "F2P1-A-PREMISE-RESPOND"),
        _finding("all-valid-pairs-bound-plan-accept", "Affirmative", "F2P1-A-HONEST-RUNS"),
        _finding("plus-one-response-controls", "Refused", "F2P1-R-PLUS-ONE"),
        _finding("independent-path-separation", "Affirmative", "F2P1-A-PATH-SEPARATION"),
        _finding("two-path-body-agreement", "Affirmative", "F2P1-A-BODY-AGREEMENT"),
        _finding("two-path-identity-agreement", "Affirmative", "F2P1-A-IDENTITY-AGREEMENT"),
        _finding("wrong-statement-edge-mutation", "Refused", "F2P1-R-STATEMENT-EDGE"),
        _finding("swapped-phase-role-mutation", "Refused", "F2P1-R-PHASE-ROLE-SWAP"),
        _finding("different-witness-type-mutation", "Refused", "F2P1-R-WITNESS-TYPE"),
        _finding("unguaranteed-plan-read-mutation", "Negative", "F2P1-N-PLAN-READ"),
        _finding("wrong-protocol-id-mutation", "Refused", "F2P1-R-WRONG-PROTOCOL"),
        _finding("pinned-theorem-applicability", "CannotAnswer", "F2P1-C-THEOREM-APPLICABILITY"),
        _finding("schnorr-property-claim", "CannotAnswer", "F2P1-C-PROPERTY"),
        _finding("schnorr-security-claim", "CannotAnswer", "F2P1-C-SECURITY"),
        _finding("complete-requested-candidate-binding", "CannotAnswer", AGGREGATE),
    ]
    outcomes: dict[str, int] = {}
    for _name, outcome, _code in findings:
        outcomes[outcome] = outcomes.get(outcome, 0) + 1

    agreement = direct["agreement"]
    measurements = agreement["measurements"]
    return {
        "aggregate": f"CannotAnswer/{AGGREGATE}",
        "finding_codes": findings,
        "findings_sha256": _digest(findings),
        "measurements": {
            **direct["basis"],
            **measurements,
            "reconstruction_paths": 2,
            "premises": len(agreement["premises"]),
            "mutations": len(agreement["mutations"]),
            "blockers": len(agreement["blockers"]),
            "outcomes": dict(sorted(outcomes.items())),
            "agreement_sha256": direct["agreement_sha256"],
        },
        "candidate_identities": agreement["identities"],
        "premise_table": agreement["premises"],
        "mutation_outcomes": agreement["mutations"],
        "blockers": agreement["blockers"],
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
                raise CandidateFailure(
                    "Refused",
                    "F2P1-R-FROZEN-DRIFT",
                    "frozen findings drift\nexpected: "
                    + json.dumps(expected, sort_keys=True)
                    + "\ncurrent:  "
                    + json.dumps(current, sort_keys=True),
                )
    except (
        CandidateFailure,
        IndependentFailure,
        OSError,
        UnicodeDecodeError,
        json.JSONDecodeError,
    ) as error:
        if isinstance(error, CandidateFailure):
            prefix = f"{error.outcome}/{error.code}: "
        else:
            prefix = ""
        print(f"F2-P1 candidate gate failed: {prefix}{error}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(current, indent=2, sort_keys=True))
    else:
        counts = current["measurements"]["outcomes"]
        print(
            f"{current['aggregate']}: {len(current['finding_codes'])} findings "
            f"({counts.get('Affirmative', 0)} affirmative, "
            f"{counts.get('Refused', 0)} refused, "
            f"{counts.get('Negative', 0)} negative, "
            f"{counts.get('CannotAnswer', 0)} cannot-answer)"
        )
        print(
            "bounded result: exact finite-additive relation and honest-Plan candidates "
            "bind and reconstruct, but the admitted Protocol has no initial ClaimRef"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
