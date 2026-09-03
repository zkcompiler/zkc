#!/usr/bin/env python3
"""Run the bounded oracle-proof compilation composition probe."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any

import independent
import model


PACKAGE = Path(__file__).resolve().parent
REPOSITORY = PACKAGE.parents[1]
FIXTURE = PACKAGE / "fixture.json"
EXPECTED = PACKAGE / "expected-findings.json"
CANONICAL_FRAMED_CHECKER = (
    REPOSITORY / "evaluation/k2-protocol-fiat-shamir/reference_model.py"
)
INDEXED_ELABORATOR = REPOSITORY / "evaluation/indexed-core-elaboration/reference_model.py"


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("BCS-R-DEPENDENCY-LOAD")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _indexed_authoring_control() -> dict[str, Any]:
    indexed = _load("_bcs_indexed_authoring", INDEXED_ELABORATOR)
    schema = indexed.fri_schema(fold_depths=(2,), query_counts=(2,))
    index = indexed.semantic_index(fold_depth=2, query_count=2)
    checked = indexed.check_core_elaboration_at(schema, index)
    checked = indexed.require_live_result(checked)
    return {
        "outcome": "Affirmative",
        "application": "finite-repeat authoring control only",
        "fold_depth": 2,
        "query_count": 2,
        "output_occurrences": checked.expansion.occurrences,
        "schema_reference_sha256": hashlib.sha256(
            checked.schema_id.internal_reference()
        ).hexdigest(),
        "core_reference_sha256": hashlib.sha256(
            checked.core_id.internal_reference()
        ).hexdigest(),
        "is_compilation_authority": False,
    }


def _canonical_framed_evidence(typed: dict[str, Any]) -> dict[str, Any]:
    checker = _load("_bcs_canonical_framed_checker", CANONICAL_FRAMED_CHECKER)
    legacy_core, construction, _, _ = checker.oracle_fixture()
    control = checker.check_fs_construction(legacy_core, legacy_core, construction)
    if control.kind.value != "affirmative":
        raise RuntimeError("BCS-R-CANONICAL-FRAMED-CONTROL")
    view_kinds = (
        checker.StaticViewKind.TRANSCRIPT_DECLARATION,
        checker.StaticViewKind.REQUIRED_INFLUENCE,
        checker.StaticViewKind.CHALLENGE_TRANSITION,
    )
    issued_views: list[str] = []
    for kind in view_kinds:
        issued = checker.issue_construction_static_view(
            legacy_core, construction, kind, checker._VIEW_FIELDS[kind]
        )
        if issued.kind.value != "affirmative":
            raise RuntimeError("BCS-R-CANONICAL-FRAMED-VIEW")
        issued_views.append(kind.value)

    raw = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = model._parse_core(raw["source_core"], raw["interaction_profile"])
    target, _ = model.elaborate(source, raw["commitment_profile"])
    exact_target_attempt = checker.check_fs_construction(
        target,
        target,
        checker.TranscriptConstruction(b"zkc/bcs-compilation-probe/v0"),
    )
    if exact_target_attempt.kind.value != "malformed":
        raise RuntimeError("BCS-R-EXACT-TARGET-CARRIER-BOUNDARY")
    if typed["target"]["core_id"] != target.identity:
        raise RuntimeError("BCS-R-EXACT-TARGET-IDENTITY")
    return {
        "legacy_control_outcome": "Affirmative",
        "legacy_control_views": issued_views,
        "legacy_control_core_occurrences": len(legacy_core.schedule),
        "exact_target_outcome": "Malformed",
        "exact_target_core_id": target.identity,
        "reason": "the existing executable checker admits its bounded legacy carrier, not the migrated target Core carrier",
    }


def build_report() -> dict[str, Any]:
    typed = model.evaluate(FIXTURE)
    cold = independent.evaluate(FIXTURE)
    if typed != cold:
        raise RuntimeError("BCS-R-INDEPENDENT-DISAGREEMENT")
    indexed = _indexed_authoring_control()
    canonical_framed = _canonical_framed_evidence(typed)
    missing_premises = [
        *typed["premises"]["missing_coordinates"],
        *typed["premises"]["provisional_family_coordinates"],
    ]
    blockers = ["canonical-framed-checker-exact-target-carrier", *missing_premises]
    findings = [
        {
            "name": "source-core-and-six-views",
            "outcome": "Affirmative",
            "code": "BCS-A-SOURCE-CORE-AND-VIEWS",
        },
        {
            "name": "commitment-opening-transition",
            "outcome": "Affirmative",
            "code": "BCS-A-COMMITMENT-OPENING-TRANSITION",
        },
        {
            "name": "canonical-framed-on-exact-target",
            "outcome": "CannotAnswer",
            "code": "BCS-C-CANONICAL-FRAMED-EXACT-TARGET",
        },
        {
            "name": "identity-and-influence-cone",
            "outcome": "Affirmative",
            "code": "BCS-A-IDENTITY-AND-INFLUENCE-CONE",
        },
        {
            "name": "soundness-premise-coordinates",
            "outcome": "CannotAnswer",
            "code": "BCS-C-SOUNDNESS-PREMISE-COORDINATES",
        },
    ]
    findings_sha256 = hashlib.sha256(_canonical(findings)).hexdigest()
    return {
        "aggregate": {
            "outcome": "CannotAnswer",
            "code": "BCS-C-COMPOSITION-INCOMPLETE",
            "verdict": "bends",
            "blocking_items": blockers,
        },
        "question": json.loads(FIXTURE.read_text(encoding="utf-8"))["question"],
        "findings": findings,
        "findings_sha256": findings_sha256,
        "source": typed["source"],
        "commitment_transition": {
            "source_core_id": typed["transition"]["source_core_id"],
            "target_core_id": typed["transition"]["target_core_id"],
            "target_readmitted": typed["transition"]["target_readmitted"],
            "compiler_role": typed["transition"]["compiler_role"],
            "compiler_activation_claimed": typed["transition"]["compiler_activation_claimed"],
            "mapped_occurrences": len(typed["transition"]["occurrence_map"]),
            "mapped_answers": len(typed["transition"]["answer_map"]),
            "inserted_target_effects": len(typed["transition"]["inserted_target_effects"]),
            "source_target_view_relations": typed["transition"]["view_relations"],
            "view_relation_digest": typed["transition"]["view_relation_digest"],
        },
        "target": {
            "core_id": typed["target"]["core_id"],
            "public_binding_oracles": typed["target"]["public_binding_oracles"],
            "occurrences": typed["target"]["occurrences"],
        },
        "indexed_authoring_control": indexed,
        "canonical_framed": canonical_framed,
        "identity_cone": typed["identity_cone"],
        "theorem_coordinates": typed["premises"],
        "independent_reconstruction": {
            "outcome": "Affirmative",
            "paths": 2,
            "complete_report_digest": hashlib.sha256(_canonical(typed)).hexdigest(),
        },
        "nonclaims": [
            "The probe does not prove source soundness, state restoration, or round-by-round soundness.",
            "The probe does not establish commitment binding, hiding, correctness, or extraction.",
            "The probe does not establish a random-oracle property, Fiat-Shamir theorem, quantitative loss, or security result.",
            "The probe does not activate Compiler authority or establish implementation, backend, or deployment correspondence.",
            "The package-local admissions and identities are bounded research evidence, not owner-issued authority.",
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
        projection = {
            "aggregate": report["aggregate"],
            "findings": report["findings"],
            "findings_sha256": report["findings_sha256"],
        }
        if projection != expected:
            print(
                json.dumps(
                    {
                        "outcome": "Refused",
                        "code": "BCS-R-EXPECTED-FINDINGS",
                        "actual": projection,
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 1
        print(
            json.dumps(
                {
                    "outcome": "pass",
                    "aggregate": report["aggregate"],
                    "findings_sha256": report["findings_sha256"],
                },
                sort_keys=True,
            )
        )
        return 0
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
