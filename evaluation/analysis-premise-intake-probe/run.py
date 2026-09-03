from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import independent
import model


ROOT = Path(__file__).resolve().parent
FIXTURE = ROOT / "fixture.json"
EXPECTED = ROOT / "expected-findings.json"


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def build_report() -> dict[str, Any]:
    typed = model.evaluate(FIXTURE)
    cold = independent.evaluate(FIXTURE)
    if typed != cold:
        raise RuntimeError("API-R-INDEPENDENT-DISAGREEMENT")

    complete = typed["complete"]
    alternate = typed["alternate_provider"]
    fresh = typed["fresh"]
    fiat_shamir = typed["fiat_shamir"]
    extra_key = typed["extra_key"]
    scope_mismatches = typed["scope_mismatches"]
    if complete["outcome"] != "Affirmative" or complete["named_premise_ids"] != complete["hypothesis_set"]:
        raise RuntimeError("API-R-HYPOTHESIS-SET")
    if any(value != "CannotAnswer/API-C-MISSING-PREMISE" for value in typed["omissions"].values()):
        raise RuntimeError("API-R-OMISSION-DID-NOT-FAIL-CLOSED")
    if typed["wrong_coordinate"] != {
        "outcome": "Refused", "code": "API-R-PREMISE-COORDINATE", "slot": "challenge-law"
    }:
        raise RuntimeError("API-R-WRONG-COORDINATE-ACCEPTED")
    if extra_key != {
        "outcome": "Malformed", "code": "API-M-EXTRA-PREMISE", "extra": ["unexpected"]
    }:
        raise RuntimeError("API-R-EXTRA-PREMISE-NOT-MALFORMED")
    if set(scope_mismatches) != {
        "FreshChallengeOnly", "OracleModelOnly", "ExactSubjectsOnly", "RebindRequired"
    } or any(
        result["outcome"] != "Refused" or result["code"] != "API-R-MODEL-SCOPE"
        for result in scope_mismatches.values()
    ):
        raise RuntimeError("API-R-MODEL-SCOPE-DID-NOT-REFUSE")
    if fresh["outcome"] != "Affirmative" or fiat_shamir["outcome"] != "Affirmative":
        raise RuntimeError("API-R-CHALLENGE-INTAKE")
    if set(fresh["named_premise_ids"]) & set(fiat_shamir["named_premise_ids"]):
        raise RuntimeError("API-R-FRESH-FS-PREMISE-ALIAS")
    if complete["judgment_id"] == alternate["judgment_id"]:
        raise RuntimeError("API-R-PROVIDER-MAP-IDENTITY-ALIAS")

    finding_codes = [
        ["closed-named-premise-schema", "Affirmative", "API-A-CLOSED-SCHEMA"],
        ["current-subject-premise-catalog", "Affirmative", "API-A-CATALOG"],
        ["complete-schnorr-fresh-intake", "Affirmative", "API-A-COMPLETE-INTAKE"],
        ["premises-retained-in-hypothesis-set", "Affirmative", "API-A-HYPOTHESIS-SET"],
        ["every-single-premise-omission", "CannotAnswer", "API-C-MISSING-PREMISE"],
        ["different-coordinate-substitution", "Refused", "API-R-PREMISE-COORDINATE"],
        ["extra-premise-key", "Malformed", "API-M-EXTRA-PREMISE"],
        ["all-model-scope-mismatches", "Refused", "API-R-MODEL-SCOPE"],
        ["fresh-and-fiat-shamir-premise-separation", "Affirmative", "API-A-REGIME-SEPARATION"],
        ["provider-map-identity-separation", "Affirmative", "API-A-PROVIDER-MAP-IDENTITY"],
        ["independent-reconstruction", "Affirmative", "API-A-INDEPENDENT-RECONSTRUCTION"],
        ["profile-qualified-outcome-partition", "Affirmative", "API-A-OUTCOME-PARTITION-TYPED"],
        ["theorem-result", "CannotAnswer", "API-C-NO-THEOREM"],
        ["property-result", "CannotAnswer", "API-C-NO-PROPERTY"],
        ["owner-adoption", "CannotAnswer", "API-C-NO-OWNER-ADOPTION"],
    ]
    findings_sha256 = hashlib.sha256(_canonical(finding_codes)).hexdigest()
    return {
        "aggregate": "Affirmative/API-A-FINITE-PREMISE-INTAKE",
        "finding_codes": finding_codes,
        "findings_sha256": findings_sha256,
        "catalog": {
            "premises": len(typed["premise_ids"]),
            "premise_ids": typed["premise_ids"],
            "catalog_digest": typed["catalog_digest"],
            "evidence_depths": typed["depth_counts"],
            "kinds": 9,
            "outcome_lanes": 6,
            "subject_outcome_lanes": 5,
        },
        "intake": {
            "complete_judgment_id": complete["judgment_id"],
            "alternate_provider_judgment_id": alternate["judgment_id"],
            "complete_premises": len(complete["named_premise_ids"]),
            "omission_outcomes": typed["omissions"],
            "wrong_coordinate": typed["wrong_coordinate"],
            "extra_key": extra_key,
            "scope_mismatches": scope_mismatches,
            "fresh_premise_ids": fresh["named_premise_ids"],
            "fiat_shamir_premise_ids": fiat_shamir["named_premise_ids"],
            "same_core": True,
        },
        "outcome_partition_coordinate": {
            "outcome": "Affirmative",
            "code": "API-A-OUTCOME-PARTITION-TYPED",
            "coordinate": "ProtocolOutcomeLane(subject.fresh_protocol_id)",
            "reason": "the fixture keys each total provider map by the exact five-lane partition of its selected Fresh Protocol"
        },
        "measurements": {
            "reconstruction_paths": 2,
            "complete_intakes": 4,
            "single_premise_omissions": len(typed["omissions"]),
            "coordinate_substitutions": 1,
            "extra_key_mutations": 1,
            "model_scope_variants_refused": len(scope_mismatches),
            "distinct_provider_maps": 2,
        },
        "nonclaims": [
            "No theorem is proved.",
            "No protocol or cryptographic property is established.",
            "No Analysis or PIR owner text or profile is adopted or published."
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--dump", action="store_true")
    args = parser.parse_args()
    report = build_report()
    if args.dump:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    if args.check:
        expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
        if report != expected:
            print(json.dumps({"outcome": "Refused", "code": "API-R-EXPECTED-FINDINGS", "actual": report}, indent=2, sort_keys=True))
            return 1
        print(json.dumps({"outcome": "pass", "aggregate": report["aggregate"], "findings_sha256": report["findings_sha256"]}, sort_keys=True))
        return 0
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
