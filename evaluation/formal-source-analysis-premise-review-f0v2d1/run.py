#!/usr/bin/env python3
"""Independently review the Analysis named-premise owner text."""

from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"
BASE_COMMIT = "7a63432"

ANALYSIS_PAGES = (
    "docs-next/analysis/README.md",
    "docs-next/analysis/analysis-model.md",
    "docs-next/analysis/cryptographic-properties.md",
    "docs-next/analysis/incremental-composition.md",
    "docs-next/analysis/profile-publication.md",
    "docs-next/analysis/semantic-relations.md",
    "docs-next/analysis/transport-composition-and-replay.md",
)
CHANGED_PAGES = (
    "docs-next/analysis/analysis-model.md",
    "docs-next/analysis/cryptographic-properties.md",
    "docs-next/analysis/profile-publication.md",
)
MIGRATED_MANIFESTS = (
    "docs-next/analysis/profiles/kernel.json",
    "docs-next/analysis/profiles/cryptographic-property.json",
    "docs-next/analysis/profiles/afk-transport.json",
)
NAME_SCOPE_DIRECTORIES = (
    "docs-next/analysis",
    "docs-next/relations",
    "docs-next/pir",
    "docs-next/foundation",
)
SOURCE_PINS = (
    *ANALYSIS_PAGES,
    *MIGRATED_MANIFESTS,
    "docs-next/relations/relation-model.md",
    "docs-next/pir/interfaces-and-plans.md",
    "evaluation/analysis-premise-intake-probe/model.py",
    "evaluation/analysis-premise-intake-probe/independent.py",
    "evaluation/k3-analysis-closure/reference_model.py",
    "evaluation/k3-analysis-closure/tests/test_reference_model.py",
)

UNRESOLVED_LAW_NAMES = (
    "ProviderDeclaration",
    "ClosedProviderCarrier",
    "ExactModelBindingLaw",
    "ExactNamedHypothesis",
    "FreshSamplingHypothesis",
    "SamplerAdequacyHypothesis",
    "OracleProcessHypothesis",
)


class ReviewError(RuntimeError):
    """The frozen source or one of the review observations drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ReviewError(detail)


def _read(relative: str) -> str:
    try:
        return (ROOT / relative).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise ReviewError(f"cannot read {relative}") from error


def _json(relative: str) -> Any:
    try:
        return json.loads(_read(relative))
    except json.JSONDecodeError as error:
        raise ReviewError(f"cannot decode {relative}") from error


def _source_hashes() -> dict[str, str]:
    return {
        relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        for relative in SOURCE_PINS
    }


def _definition_surface() -> str:
    paths: list[Path] = []
    for relative in NAME_SCOPE_DIRECTORIES:
        paths.extend((ROOT / relative).rglob("*.md"))
    return "\n".join(path.read_text(encoding="utf-8") for path in sorted(paths))


def _definition_count(text: str, symbol: str) -> int:
    return len(
        re.findall(
            rf"^[ \t]*{re.escape(symbol)}(?:<[^\n=]+>)?(?:\([^\n]*\))?[ \t]*(?::=|=)",
            text,
            flags=re.MULTILINE,
        )
    )


def _record_block(text: str, selector: str) -> str:
    start = text.find(selector)
    _require(start >= 0, f"selector is absent: {selector}")
    brace = text.find("{", start)
    _require(brace >= 0, f"selector has no record body: {selector}")
    depth = 0
    for index in range(brace, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start : index + 1]
    raise ReviewError(f"selector has an unclosed record body: {selector}")


def _name_review(pages: dict[str, str]) -> dict[str, Any]:
    surface = _definition_surface()
    unresolved = {
        name: _definition_count(surface, name) for name in UNRESOLVED_LAW_NAMES
    }
    _require(
        unresolved == {name: 0 for name in UNRESOLVED_LAW_NAMES},
        "the frozen unresolved law-name set drifted",
    )

    resolved = (
        "AnalysisProfileLawRef",
        "AnalysisDistributionProfileId",
        "AnalysisAsymptoticProtocolFamilyDefinitionId",
        "RelationSemanticModelId",
        "RelationInterfaceId",
        "PlanWitnessBindingId",
        "ProverPlanId",
        "ProtocolOutcomeLane",
        "AFKClassicalRandomOracleProfileId",
    )
    counts = {name: _definition_count(surface, name) for name in resolved}
    _require(all(count > 0 for count in counts.values()), "a frozen resolved name disappeared")

    model = pages["docs-next/analysis/analysis-model.md"]
    coordinate_names = (
        "PIRPublicCoinLawCoordinate",
        "AnalysisFamilyPremiseCoordinate",
        "PIRProtocolOutcomePartitionCoordinate",
        "RelationsModelEvaluatorCoordinate",
        "RelationsWitnessPlanJoinCoordinate",
        "PIRPlanStateCoordinate",
        "PIRPlanRecipeCoordinate",
    )
    coordinate_block = _record_block(model, "AnalysisPremiseCoordinate =")
    _require(
        all(name in coordinate_block for name in coordinate_names),
        "the premise-coordinate constructor set drifted",
    )

    property_page = pages["docs-next/analysis/cryptographic-properties.md"]
    subject = _record_block(property_page, "AnalysisSubjectTuple S =")
    subject_fields = (
        "fresh_protocol_id",
        "challenge_ref",
        "relation_semantic_model_id",
        "relation_interface_id",
        "plan_witness_binding_id",
    )
    _require(
        all(field in subject for field in subject_fields),
        "a named-premise subject-tuple field disappeared",
    )

    unqualified = (
        "AnalysisProfileLawRef<ProviderDeclaration>",
        "AnalysisProfileLawRef<ClosedProviderCarrier>",
        "AnalysisLawTerm<ExactModelBindingLaw<K>>",
        "AnalysisLawTerm<ExactNamedHypothesis<K>>",
    )
    _require(
        all(item in model for item in unqualified),
        "the frozen profile-parameter omission set drifted",
    )
    return {
        "resolved_requested_names": len(resolved),
        "resolved_coordinate_constructors": len(coordinate_names),
        "resolved_subject_tuple_fields": len(subject_fields),
        "unresolved_law_names": list(UNRESOLVED_LAW_NAMES),
        "unqualified_profile_law_uses": len(unqualified),
    }


def _constructor_blocks(text: str, expression: str) -> list[tuple[int, str]]:
    pattern = re.compile(expression)
    result: list[tuple[int, str]] = []
    for match in pattern.finditer(text):
        brace = text.find("{", match.start(), match.end() + 1)
        _require(brace >= 0, "constructor match has no opening brace")
        depth = 0
        for index in range(brace, len(text)):
            if text[index] == "{":
                depth += 1
            elif text[index] == "}":
                depth -= 1
                if depth == 0:
                    result.append((text.count("\n", 0, match.start()) + 1, text[match.start() : index + 1]))
                    break
        else:
            raise ReviewError("constructor display has an unclosed body")
    return result


def _constructor_review(pages: dict[str, str]) -> dict[str, Any]:
    specifications = (
        ("AnalysisQuestionBody", r"(?<![A-Za-z0-9_])AnalysisQuestionBody\s*\{", "named_premise_requirements", 11),
        ("AnalysisGoalBody", r"(?<![A-Za-z0-9_])AnalysisGoalBody\s*\{", "named_premise_bindings", 12),
        ("AnalysisHypothesisContextBody", r"(?<![A-Za-z0-9_])AnalysisHypothesisContextBody\s*\{", "exact_named_premise_ids", 6),
        ("AnalysisSupportInstantiationBody", r"(?<![A-Za-z0-9_])AnalysisSupportInstantiationBody\s*\{", "exact_named_premise_ids", 5),
        ("AnalysisJudgmentRecordBody", r"(?<![A-Za-z0-9_])AnalysisJudgmentRecordBody\s*\{", "exact_named_premise_ids", 1),
        ("AnalysisNamedPremiseBody", r"AnalysisNamedPremiseBody<[^>]+>\s*\{", "kind", 4),
    )
    metrics: dict[str, Any] = {}
    missing_total = 0
    for name, expression, field, expected_count in specifications:
        rows: list[tuple[str, int, bool]] = []
        for relative, text in pages.items():
            for line, block in _constructor_blocks(text, expression):
                rows.append((relative, line, field in block))
        _require(len(rows) == expected_count, f"the {name} constructor census drifted")
        _require(not any(row[2] for row in rows), f"a frozen incomplete {name} constructor became complete")
        missing_total += len(rows)
        metrics[name] = {
            "constructors": len(rows),
            "field_complete": 0,
            "locations": [f"{relative}:{line}" for relative, line, _complete in rows],
        }

    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    context_blocks = _constructor_blocks(
        crypto, r"(?<![A-Za-z0-9_])AnalysisHypothesisContextBody\s*\{"
    )
    node_count = sum(
        len(re.findall(r"^\s*\{\s*\d+\s*,", block, flags=re.MULTILINE))
        for _line, block in context_blocks
    )
    _require(node_count == 30, "the anonymous hypothesis-node census drifted")
    _require(
        "An `AnalysisGoalBody` contains only `question_id`." in pages["docs-next/analysis/analysis-model.md"],
        "the stale goal-body sentence drifted",
    )
    _require(
        "set roots to OutwardFrontier(the rewritten nodes)" in pages["docs-next/analysis/analysis-model.md"]
        and "set each rewritten node's exact_named_premise_ids" not in pages["docs-next/analysis/analysis-model.md"],
        "the frozen DAG-union omission drifted",
    )
    return {
        "body_constructors": metrics,
        "incomplete_body_constructors": missing_total,
        "anonymous_hypothesis_nodes_without_new_field": node_count,
        "derived_helper_omissions": [
            "affirmative judgment constructor",
            "canonical goal DAG union",
        ],
        "stale_goal_body_sentence": True,
    }


def _intake_review(pages: dict[str, str]) -> dict[str, Any]:
    model = pages["docs-next/analysis/analysis-model.md"]
    block = model.split("IntakeAnalysisNamedPremises(", 1)[1].split("```", 1)[0]
    required = (
        "return CannotAnswer for a missing key or an absent premise source",
        "return Refused when a supplied premise is well formed but its kind or\n     coordinate differs",
        "return Malformed for an extra, duplicate, noncanonical, or\n     caller-ordered key",
        "FreshChallengeOnly premise only for a question over a Fresh Protocol",
        "OracleModelOnly premise only for a question whose experiment uses\n     exactly that distribution profile",
        "ExactSubjectsOnly premise only for\n     a question over exactly those subjects",
        "RebindRequired admits no\n     question",
        "binding map has the required\n     key set and no other key",
    )
    _require(all(snippet in block for snippet in required), "the intake disposition or scope text drifted")

    cases: dict[str, str | None] = {
        "missing-key": "CannotAnswer",
        "absent-source": "CannotAnswer",
        "kind-mismatch": "Refused",
        "coordinate-mismatch": "Refused",
        "extra-key": "Malformed",
        "duplicate-key": "Malformed",
        "noncanonical-key": "Malformed",
        "caller-ordered-key": "Malformed",
        "fresh-scope-mismatch": None,
        "oracle-model-mismatch": "Refused",
        "subject-scope-mismatch": None,
        "rebind-required": None,
    }
    _require(len(cases) == 12, "the intake branch census drifted")
    return {
        "classified_branches": cases,
        "cannot_answer_branches": 2,
        "refused_branches": 3,
        "malformed_branches": 4,
        "unclassified_scope_branches": 3,
        "default_branches": 0,
    }


def _decision_review(pages: dict[str, str]) -> dict[str, Any]:
    model = pages["docs-next/analysis/analysis-model.md"]
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    positive_intent = (
        "FreshChallengeOnly" in model,
        "OracleModelOnly(AnalysisDistributionProfileId)" in model,
        "five lanes for a Fresh or duplex-sponge Protocol, six for a\ncanonical-framed one" in crypto,
        "A question over a Fiat--Shamir Protocol\nselects no such premise" in crypto,
        "AFKClassicalRandomOracleProfileId(S)" in crypto,
    )
    _require(all(positive_intent), "the selected decision-intent clauses drifted")
    defects = (
        "CanonicalMap<ProtocolOutcomeLane, CanonicalValue<provider_carrier>>" in model,
        "BoundHypothesis(sampling_hypothesis, which binds law_coordinate" in crypto,
        "BoundHypothesis(adequacy_hypothesis, which names one adequacy form" in crypto,
    )
    _require(all(defects), "the frozen decision-fidelity defects drifted")
    return {
        "intent_clauses_present": len(positive_intent),
        "unclosed_exactness_points": [
            "outcome-lane family is used without its Protocol parameter",
            "Fresh sampling binding is prose rather than law-term arguments",
            "sampler adequacy form is prose rather than law-term arguments",
        ],
    }


def _schnorr_review(pages: dict[str, str]) -> dict[str, Any]:
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    requirements = crypto.split("SchnorrNamedPremiseRequirements(", 1)[1].split("```", 1)[0]
    slots = re.findall(r'slot: "([a-z-]+)"', requirements)
    _require(
        slots
        == [
            "fresh-coin",
            "provider-outcome",
            "relation",
            "witness",
            "prover-state",
            "commit",
            "respond",
        ],
        "the seven-premise slot sequence drifted",
    )

    relation_model = _read("docs-next/relations/relation-model.md")
    binding = _record_block(relation_model, "PlanWitnessBinding =")
    _require("ProverPlanId" not in binding, "PlanWitnessBinding unexpectedly names a ProverPlan")
    _require(
        "the ProverPlanId named by\n  S.relation_axis_ingress.fresh.plan_witness_binding_id" in crypto,
        "the frozen PlanOf derivation drifted",
    )

    plan_page = _read("docs-next/pir/interfaces-and-plans.md")
    _require("CanonicalMap<ProverDecisionPointRef, DecisionRecipe>" in plan_page, "Plan decision-key type drifted")
    _require("persistent_state: CanonicalSeq<StrategyStateSlot>" in plan_page, "Plan state carrier drifted")
    candidate_expected = _json(
        "evaluation/formal-schnorr-relations-plan-f2p1/expected-findings.json"
    )
    encoded = json.dumps(candidate_expected, sort_keys=True)
    for coordinate in (
        "ProverPlan.decision_recipes[0].nodes[0]",
        "ProverPlan.decision_recipes[2].nodes[0]",
        ").persistent_state[0]",
        ").private_witness[0].value_type + PlanWitnessBinding.witness_edges[0]",
    ):
        _require(coordinate in encoded, "a selected Schnorr candidate coordinate drifted")
    return {
        "requirements": len(slots),
        "subject_tuple_fields_resolve": True,
        "candidate_ordinals": {
            "private_witness": 0,
            "witness_edge": 0,
            "persistent_state": 0,
            "commit_decision": 0,
            "commit_recipe_node": 0,
            "respond_decision": 2,
            "respond_recipe_node": 0,
        },
        "plan_id_recoverable_from_plan_witness_binding": False,
        "coordinate_key_type_mismatches": 2,
    }


def _catalog(text: str, name: str) -> list[str]:
    block = _record_block(text, f"{name} =")
    return re.findall(r'"(analysis\.[a-z0-9-]+)"', block)


def _old_bytes(relative: str) -> bytes:
    try:
        return subprocess.run(
            ["git", "show", f"{BASE_COMMIT}:{relative}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReviewError(f"cannot reconstruct the review base for {relative}") from error


def _load_module(name: str, path: Path) -> Any:
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        raise ReviewError(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[name] = module
    specification.loader.exec_module(module)
    return module


def _publication_review(pages: dict[str, str]) -> dict[str, Any]:
    catalog_names = {
        "analysis-kernel": "AnalysisKernelSupportedKinds",
        "analysis-cryptographic-property": "AnalysisCryptographicPropertySupportedKinds",
        "analysis-afk-transport": "AnalysisAFKTransportSupportedKinds",
    }
    manifest_paths = {
        _json(path)["key"]: path for path in MIGRATED_MANIFESTS
    }
    sequence_equal: dict[str, bool] = {}
    set_equal: dict[str, bool] = {}
    model = pages["docs-next/analysis/analysis-model.md"]
    for key, name in catalog_names.items():
        owner = _catalog(model, name)
        manifest = _json(manifest_paths[key])["supported_subject_kinds"]
        sequence_equal[key] = owner == manifest
        set_equal[key] = set(owner) == set(manifest)
    _require(
        sequence_equal
        == {
            "analysis-kernel": True,
            "analysis-cryptographic-property": True,
            "analysis-afk-transport": False,
        },
        "the literal supported-kind comparison drifted",
    )
    _require(all(set_equal.values()), "a supported-kind set no longer matches")

    old_model = _old_bytes("docs-next/analysis/analysis-model.md").decode("utf-8")
    old_transport = json.loads(_old_bytes("docs-next/analysis/profiles/afk-transport.json"))
    preexisting_transport_mismatch = (
        _catalog(old_model, "AnalysisAFKTransportSupportedKinds")
        != old_transport["supported_subject_kinds"]
    )
    _require(preexisting_transport_mismatch, "the preexisting sequence defect disappeared from the review base")

    observed_definition_bumps: dict[str, list[str]] = {}
    for relative in MIGRATED_MANIFESTS:
        old = json.loads(_old_bytes(relative))
        current = _json(relative)
        _require(old["revision"] == 0 and current["revision"] == 1, "a profile revision transition drifted")
        old_definitions = {(row["kind"], row["name"]): row for row in old["definitions"]}
        bumps = [
            row["name"]
            for row in current["definitions"]
            if (row["kind"], row["name"]) in old_definitions
            and row["revision"] != old_definitions[(row["kind"], row["name"])]["revision"]
        ]
        observed_definition_bumps[current["key"]] = bumps
    _require(
        observed_definition_bumps
        == {
            "analysis-kernel": ["common-analysis-domain-v0"],
            "analysis-cryptographic-property": ["cryptographic-property-body-v0"],
            "analysis-afk-transport": ["afk-transport-body-v0"],
        },
        "the declaration revision set drifted",
    )

    publication = ROOT / "evaluation" / "semantic-profile-publication"
    reference = _load_module("_analysis_premise_review_reference", publication / "reference_model.py")
    cold = _load_module("_analysis_premise_review_cold", publication / "independent.py")
    current_reference = reference.identity_table(reference.compile_repository())
    current_cold = cold.identity_table(cold.compile_repository())
    _require(current_reference == current_cold, "publication compilers disagree on current source")

    manifest_overrides = {
        json.loads(_old_bytes(path))["key"]: json.loads(_old_bytes(path))
        for path in MIGRATED_MANIFESTS
    }
    page_overrides = {path: _old_bytes(path) for path in CHANGED_PAGES}
    base_reference = reference.identity_table(
        reference.compile_repository(
            manifest_overrides=manifest_overrides,
            page_overrides=page_overrides,
        )
    )
    base_cold = cold.identity_table(
        cold.compile_repository(
            manifest_overrides=manifest_overrides,
            page_overrides=page_overrides,
        )
    )
    _require(base_reference == base_cold, "publication compilers disagree on review-base source")
    cone = [
        key
        for key, value in current_reference["profiles"].items()
        if base_reference["profiles"][key] != value
    ]
    expected_cone = [
        "analysis-kernel",
        "analysis-cryptographic-property",
        "analysis-afk-transport",
        "analysis-afk-theorem-source-validation",
        "analysis-incremental-composition",
        "analysis-incremental-composition-source-validation",
    ]
    _require(cone == expected_cone, "the Analysis identity-rotation cone drifted")
    return {
        "catalog_sequence_equal": sequence_equal,
        "catalog_set_equal": set_equal,
        "transport_sequence_mismatch_preexisting": preexisting_transport_mismatch,
        "profile_revision_bumps": 3,
        "observed_definition_bumps": observed_definition_bumps,
        "missing_meaning_revision_bumps": ["property-core-v0", "afk-application-v0"],
        "compiler_agreement_current": True,
        "compiler_agreement_base": True,
        "compiled_profiles": len(current_reference["profiles"]),
        "all_declarations_reachable": True,
        "rotation_cone": cone,
    }


def _call_counts(path: Path, selected: Iterable[str]) -> dict[str, int]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    result = {name: 0 for name in selected}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        name = ""
        if isinstance(node.func, ast.Name):
            name = node.func.id
        elif isinstance(node.func, ast.Attribute):
            name = node.func.attr
        if name in result:
            result[name] += 1
    return result


def _class_fields(tree: ast.Module, selected: Iterable[str]) -> dict[str, list[str]]:
    wanted = set(selected)
    result: dict[str, list[str]] = {}
    for node in tree.body:
        if not isinstance(node, ast.ClassDef) or node.name not in wanted:
            continue
        fields: list[str] = []
        for statement in node.body:
            if isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name):
                fields.append(statement.target.id)
        result[node.name] = fields
    return result


def _package_impact_review() -> dict[str, Any]:
    model_path = ROOT / "evaluation/k3-analysis-closure/reference_model.py"
    tests_path = ROOT / "evaluation/k3-analysis-closure/tests/test_reference_model.py"
    selected = (
        "AnalysisQuestionBodyV0",
        "AnalysisGoalBodyV0",
        "AnalysisHypothesisNodeV0",
        "AnalysisHypothesisContextBodyV0",
        "AnalysisSupportInstantiationBodyV0",
        "AnalysisJudgmentRecordBodyV0",
    )
    tree = ast.parse(model_path.read_text(encoding="utf-8"))
    fields = _class_fields(tree, selected)
    required = {
        "AnalysisQuestionBodyV0": "named_premise_requirements",
        "AnalysisGoalBodyV0": "named_premise_bindings",
        "AnalysisHypothesisNodeV0": "exact_named_premise_ids",
        "AnalysisHypothesisContextBodyV0": "exact_named_premise_ids",
        "AnalysisSupportInstantiationBodyV0": "exact_named_premise_ids",
        "AnalysisJudgmentRecordBodyV0": "exact_named_premise_ids",
    }
    _require(set(fields) == set(selected), "the selected Analysis reference classes drifted")
    missing = {
        name: field for name, field in required.items() if field not in fields[name]
    }
    _require(missing == required, "the frozen reference-model field omissions drifted")

    model_calls = _call_counts(model_path, selected)
    test_calls = _call_counts(tests_path, selected)
    expected_calls = {
        "AnalysisQuestionBodyV0": 8,
        "AnalysisGoalBodyV0": 14,
        "AnalysisHypothesisNodeV0": 5,
        "AnalysisHypothesisContextBodyV0": 4,
        "AnalysisSupportInstantiationBodyV0": 1,
        "AnalysisJudgmentRecordBodyV0": 1,
    }
    combined = {name: model_calls[name] + test_calls[name] for name in selected}
    _require(combined == expected_calls, "the affected reference-model call census drifted")

    finite = _read("evaluation/finite-cover-analysis/tests/test_finite_cover.py")
    joined = _read("evaluation/k3-integrated-closure/reference_model.py")
    _require("k3-analysis-closure" in finite and "k3-analysis-closure" in joined, "an Analysis dependent stopped importing the shared model")

    recursive = _read("evaluation/recursive-composition-boundary/reference_model.py")
    _require(
        '"analysis.support-instantiation"' in recursive
        and '"analysis.judgment-record"' in recursive,
        "the incremental-composition surrogate identity path drifted",
    )
    return {
        "reference_body_classes_missing_fields": missing,
        "affected_reference_constructor_calls": combined,
        "direct_model_package": "evaluation/k3-analysis-closure",
        "dependent_model_packages": [
            "evaluation/finite-cover-analysis",
            "evaluation/k3-integrated-closure",
        ],
        "incremental_surrogate_package": "evaluation/recursive-composition-boundary",
        "checks_requiring_refreeze_or_revalidation": [
            "research.property-analysis",
            "research.finite-cover",
            "research.joined-semantic-boundary",
            "research.recursive-composition-boundary",
            "research.profile-publication",
            "research.analysis-premise-intake",
        ],
        "exact_binding_values_determined": False,
    }


def _probe_review() -> dict[str, Any]:
    typed = _read("evaluation/analysis-premise-intake-probe/model.py")
    cold = _read("evaluation/analysis-premise-intake-probe/independent.py")
    _require(
        '"outcome": "Refused", "code": "API-R-EXTRA-PREMISE"' in typed
        and '"outcome": "Refused", "code": "API-R-EXTRA-PREMISE"' in cold,
        "the predecessor probe extra-key behavior drifted",
    )
    _require("model_scope" not in typed and "model_scope" not in cold, "the predecessor probe acquired model-scope checks")
    return {
        "extra_key_matches_owner_text": False,
        "model_scope_checked": False,
        "frozen_expected_finding_for_extra_key": False,
    }


def evaluate() -> dict[str, Any]:
    pages = {relative: _read(relative) for relative in ANALYSIS_PAGES}
    metrics = {
        "source_sha256": _source_hashes(),
        "names": _name_review(pages),
        "constructors": _constructor_review(pages),
        "intake": _intake_review(pages),
        "decision_fidelity": _decision_review(pages),
        "schnorr": _schnorr_review(pages),
        "publication": _publication_review(pages),
        "package_impact": _package_impact_review(),
        "predecessor_probe": _probe_review(),
    }
    findings = [
        Finding("name-closure", "Negative", "F0V2D1-N-NAME-CLOSURE"),
        Finding("constructor-consistency", "Negative", "F0V2D1-N-CONSTRUCTOR-CONSISTENCY"),
        Finding("intake-soundness", "CannotAnswer", "F0V2D1-C-INTAKE-SCOPE-DISPOSITION"),
        Finding("decision-fidelity", "Negative", "F0V2D1-N-DECISION-FIDELITY"),
        Finding("schnorr-coordinate-formation", "Negative", "F0V2D1-N-SCHNORR-COORDINATES"),
        Finding("profile-manifest-closure", "Negative", "F0V2D1-N-PROFILE-MANIFESTS"),
        Finding("existing-package-refreeze", "CannotAnswer", "F0V2D1-C-REFREEZE-INPUTS"),
        Finding("publication-compiler-agreement", "Affirmative", "F0V2D1-A-PUBLICATION-COMPILERS"),
        Finding("identity-rotation-cone", "Affirmative", "F0V2D1-A-ROTATION-CONE"),
        Finding("predecessor-probe-coverage", "Negative", "F0V2D1-N-PROBE-COVERAGE"),
    ]
    return {
        "aggregate": {
            "outcome": "Negative",
            "code": "F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED",
            "blocking_findings": [
                "F0V2D1-N-NAME-CLOSURE",
                "F0V2D1-N-CONSTRUCTOR-CONSISTENCY",
                "F0V2D1-N-DECISION-FIDELITY",
                "F0V2D1-N-SCHNORR-COORDINATES",
                "F0V2D1-N-PROFILE-MANIFESTS",
                "F0V2D1-N-PROBE-COVERAGE",
            ],
            "cannot_answer_findings": [
                "F0V2D1-C-INTAKE-SCOPE-DISPOSITION",
                "F0V2D1-C-REFREEZE-INPUTS",
            ],
        },
        "finding_codes": [finding.value() for finding in findings],
        "metrics": metrics,
        "nonclaims": [
            "The review does not edit or publish Analysis owner semantics.",
            "Static name and constructor checks are not an Analysis implementation or mechanized proof.",
            "Publication compiler agreement is not evidence that the owner text is semantically closed.",
            "The finite Schnorr candidate coordinates establish no relation truth, Plan honesty, theorem, or cryptographic property.",
        ],
    }


def check() -> dict[str, Any]:
    expected = _json(str(EXPECTED.relative_to(ROOT)))
    observed = evaluate()
    _require(
        observed["aggregate"] == expected["aggregate"],
        "the frozen Analysis premise aggregate drifted",
    )
    _require(
        observed["finding_codes"] == expected["finding_codes"],
        "the frozen Analysis premise finding classifications drifted",
    )
    return observed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = check() if args.check else evaluate()
    except ReviewError as error:
        print(f"Analysis premise review failed: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        findings = result["finding_codes"]
        negatives = sum(item[1] == "Negative" for item in findings)
        unanswered = sum(item[1] == "CannotAnswer" for item in findings)
        print(
            "Analysis named-premise owner-text review: "
            f"{len(findings)}/{len(findings)} findings reproduced; "
            f"{negatives} negative, {unanswered} cannot answer; aggregate Negative"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
