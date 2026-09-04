#!/usr/bin/env python3
"""Run the bounded F0-V2A canonical view-schema feasibility gate."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import independent as cold
import model


ROOT = Path(__file__).resolve().parent
EXPECTED = ROOT / "expected-findings.json"


class GateFailure(RuntimeError):
    """The executable gate or its frozen classification drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name=name, outcome=outcome, code=code, detail=detail)


MUTATIONS: tuple[tuple[str, str, str, str], ...] = (
    (
        "unknown-node",
        "host-reflection-node",
        "F0V2A-R-HOST-REFLECTION",
        "a reflection/callback node is outside the closed description universe",
    ),
    (
        "unsorted-fields",
        "noncanonical-field-order",
        "F0V2A-R-FIELD-ORDER",
        "record field ordinals must remain strict canonical order",
    ),
    (
        "duplicate-field",
        "duplicate-field-ordinal",
        "F0V2A-R-DUPLICATE-FIELD",
        "two schema children cannot share one field coordinate",
    ),
    (
        "empty-variant",
        "empty-variant-schema",
        "F0V2A-R-EMPTY-VARIANT",
        "a closed variant must declare at least one case",
    ),
    (
        "unknown-atom",
        "unknown-atom-kind",
        "F0V2A-R-UNKNOWN-ATOM",
        "a host-object atom cannot become semantic view material",
    ),
    (
        "unknown-compiler",
        "unknown-leaf-body-compiler",
        "F0V2A-R-UNKNOWN-COMPILER",
        "a semantic atom must select one exact authenticated body compiler",
    ),
    (
        "module-payload-decomposition",
        "module-payload-generic-descent",
        "F0V2A-R-MODULE-DESCENT",
        "replacing the opaque effect atom rotates the authenticated schema",
    ),
    (
        "missing-value-field",
        "missing-record-field",
        "F0V2A-R-MISSING-FIELD",
        "a concrete view must contain every schema field",
    ),
    (
        "extra-value-field",
        "extra-record-field",
        "F0V2A-R-EXTRA-FIELD",
        "a concrete view cannot contain an undeclared field",
    ),
    (
        "inactive-variant-case",
        "absent-variant-case",
        "F0V2A-R-VARIANT-CASE",
        "a concrete variant must select one declared active case",
    ),
    (
        "sequence-overflow",
        "sequence-bound-overflow",
        "F0V2A-R-SEQUENCE-BOUND",
        "concrete sequence length cannot exceed the schema maximum",
    ),
    (
        "law-substitution",
        "exact-profile-law-substitution",
        "F0V2A-R-LAW-SUBSTITUTION",
        "another well-formed law reference cannot inhabit a fixed law atom",
    ),
    (
        "leaf-compiler-substitution",
        "canonical-body-compiler-substitution",
        "F0V2A-R-COMPILER-SUBSTITUTION",
        "same-shaped reference bytes under another compiler do not form",
    ),
    (
        "unadmitted-canonical-value",
        "unadmitted-canonical-value",
        "F0V2A-R-CANONICAL-VALUE",
        "a canonical-value atom requires exact prior value admission",
    ),
    (
        "unsupported-module-effect",
        "unsupported-module-effect",
        "F0V2A-R-MODULE-UNSUPPORTED",
        "an unsupported exact effect cannot become an admitted view atom",
    ),
    (
        "invalid-module-payload",
        "invalid-module-payload",
        "F0V2A-R-MODULE-PAYLOAD",
        "a module payload must pass its authenticated owner schema",
    ),
    (
        "module-owner-substitution",
        "module-effect-owner-substitution",
        "F0V2A-R-MODULE-OWNER",
        "effect module and declaration owner must be identical",
    ),
    (
        "boolean-as-natural",
        "boolean-natural-alias",
        "F0V2A-R-BOOLEAN-TYPE",
        "Python integer aliasing cannot make a natural into MetaBoolean",
    ),
    (
        "missing-manifest-leaf",
        "missing-complete-manifest-leaf",
        "F0V2A-R-MANIFEST-OMISSION",
        "the complete manifest cannot omit one active atomic leaf",
    ),
    (
        "duplicate-manifest-leaf",
        "duplicate-manifest-coordinate",
        "F0V2A-R-MANIFEST-DUPLICATE",
        "the manifest must be coordinate-unique",
    ),
    (
        "reordered-manifest",
        "reordered-complete-manifest",
        "F0V2A-R-MANIFEST-ORDER",
        "the manifest must remain in canonical coordinate order",
    ),
    (
        "wrong-boundary",
        "wrong-atomic-boundary",
        "F0V2A-R-WRONG-BOUNDARY",
        "a valid path under another atomic boundary does not resolve",
    ),
    (
        "interior-path",
        "interior-or-empty-path",
        "F0V2A-R-INTERIOR-PATH",
        "a coordinate must use a nonempty path ending exactly at an atom",
    ),
    (
        "text-path-step",
        "textual-field-path",
        "F0V2A-R-TEXT-PATH",
        "field names and text lookup are outside the coordinate grammar",
    ),
    (
        "out-of-range-sequence-path",
        "absent-sequence-element",
        "F0V2A-R-SEQUENCE-PATH",
        "a coordinate cannot select an absent concrete sequence element",
    ),
    (
        "cross-view-coordinate",
        "cross-view-coordinate",
        "F0V2A-R-CROSS-VIEW",
        "a field coordinate cannot be replayed under another view schema",
    ),
    (
        "equal-value-coordinate-alias",
        "equal-value-coordinate-alias",
        "F0V2A-R-EQUAL-VALUE-ALIAS",
        "equal semantic leaf values at distinct paths retain distinct coordinates",
    ),
)


def _reference_rejection(candidate: object) -> str:
    try:
        model.observe(candidate)
    except model.SchemaError as error:
        return f"SchemaError: {error}"
    except Exception as error:  # pragma: no cover - implementation defect
        raise GateFailure(
            f"reference path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("reference path accepted a forbidden F0-V2A mutation")


def _cold_rejection(candidate: object) -> str:
    try:
        cold.observe(candidate)
    except cold.ColdError as error:
        return f"ColdError: {error}"
    except Exception as error:  # pragma: no cover - implementation defect
        raise GateFailure(
            f"cold path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("cold path accepted a forbidden F0-V2A mutation")


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read frozen F0-V2A findings") from error
    if type(value) is not dict:
        raise GateFailure("frozen F0-V2A findings have the wrong shape")
    return value


def run_gate() -> dict[str, Any]:
    candidate = model.build_candidate()
    reference_evidence = model.observe(candidate)
    cold_evidence = cold.observe(candidate)
    if reference_evidence != cold_evidence:
        raise GateFailure(
            "recursive and iterative schema paths disagree:\n"
            + json.dumps(
                {"recursive": reference_evidence, "iterative": cold_evidence},
                indent=2,
                sort_keys=True,
            )
        )

    findings = [
        _finding(
            "six-view-representative-catalog",
            "Affirmative",
            "F0V2A-A-SIX-VIEWS",
            "one representative conforming schema/value pair forms for all six Interaction views",
        ),
        _finding(
            "finite-structural-universe",
            "Affirmative",
            "F0V2A-A-STRUCTURAL-UNIVERSE",
            "record, variant, and sequence are the only non-atomic nodes",
        ),
        _finding(
            "closed-semantic-atom-universe",
            "Affirmative",
            "F0V2A-A-ATOM-UNIVERSE",
            "all nine selected semantic atom classes are exercised",
        ),
        _finding(
            "recursive-iterative-agreement",
            "Affirmative",
            "F0V2A-A-INDEPENDENT-AGREEMENT",
            "independent recursive and iterative paths derive identical evidence",
        ),
        _finding(
            "enumeration-resolution-inverse",
            "Affirmative",
            "F0V2A-A-RESOLVER-INVERSE",
            "both paths resolve every enumerated coordinate to its exact leaf value",
        ),
        _finding(
            "exact-complete-manifests",
            "Affirmative",
            "F0V2A-A-COMPLETE-MANIFEST",
            "each requested manifest equals the complete sorted-unique active-leaf set",
        ),
        _finding(
            "fixed-law-atoms",
            "Affirmative",
            "F0V2A-A-FIXED-LAWS",
            "law identity is embedded in the atom schema and boundary",
        ),
        _finding(
            "opaque-module-effect-boundary",
            "Affirmative",
            "F0V2A-A-OPAQUE-MODULE",
            "the complete admitted module effect is one leaf and its payload is not reflected",
        ),
        _finding(
            "equal-values-distinct-coordinates",
            "Affirmative",
            "F0V2A-A-NO-VALUE-ALIAS",
            "three equal ValueRef leaves retain three distinct structural coordinates",
        ),
        _finding(
            "exact-six-target-body-grammars",
            "CannotAnswer",
            "F0V2A-C-EXACT-TARGET-GRAMMAR",
            "representative schemas do not fill the prose placeholders in all six target bodies",
        ),
        _finding(
            "complete-owner-view-derivation",
            "CannotAnswer",
            "F0V2A-C-OWNER-DERIVATION",
            "fixture values are not derived from the exact admitted F1-R1B owner handles",
        ),
        _finding(
            "target-profile-publication-and-migration",
            "CannotAnswer",
            "F0V2A-C-TARGET-MIGRATION",
            "no target source, profile revision, or semantic identity changes in this gate",
        ),
        _finding(
            "proper-subset-read-closure",
            "CannotAnswer",
            "F0V2A-C-PARTIAL-CLOSURE",
            "constructor-specific dependency closure remains an F1-R1C2 obligation",
        ),
    ]

    mutation_diagnostics: dict[str, dict[str, str]] = {}
    for mutation, finding_name, code, detail in MUTATIONS:
        mutated = model.mutated_candidate(mutation)
        mutation_diagnostics[mutation] = {
            "recursive": _reference_rejection(mutated),
            "iterative": _cold_rejection(mutated),
        }
        findings.append(_finding(finding_name, "Refused", code, detail))

    observed_cases = [
        {"name": row.name, "outcome": row.outcome, "code": row.code} for row in findings
    ]
    expected = _load_expected()
    if observed_cases != expected.get("cases"):
        raise GateFailure(
            "F0-V2A finding classification drifted:\n"
            + json.dumps(
                {"expected": expected.get("cases"), "observed": observed_cases},
                indent=2,
            )
        )
    aggregate = {
        "outcome": "Affirmative",
        "code": "F0V2A-A-SCHEMA-ALGEBRA-FEASIBLE",
    }
    if aggregate != expected.get("aggregate"):
        raise GateFailure("F0-V2A aggregate disposition drifted")
    evidence_control = {
        "views": reference_evidence["views"],
        "total_leaf_count": reference_evidence["total_leaf_count"],
    }
    if evidence_control != expected.get("evidence_control"):
        raise GateFailure(
            "F0-V2A schema or manifest identity control drifted:\n"
            + json.dumps(
                {
                    "expected": expected.get("evidence_control"),
                    "observed": evidence_control,
                },
                indent=2,
                sort_keys=True,
            )
        )

    return {
        "format": "zkc.formal-source-view-schema-f0v2a.v0",
        "aggregate": aggregate,
        "cases": [asdict(row) for row in findings],
        "evidence": reference_evidence,
        "mutation_diagnostics": mutation_diagnostics,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="print only the frozen gate summary",
    )
    arguments = parser.parse_args()
    result = run_gate()
    if arguments.check:
        print(
            "[formal-source-view-schema-f0v2a] "
            f"{len(result['cases'])}/{len(result['cases'])} findings; "
            f"{result['aggregate']['outcome']}/{result['aggregate']['code']}; "
            f"{result['evidence']['total_leaf_count']} representative leaves"
        )
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
