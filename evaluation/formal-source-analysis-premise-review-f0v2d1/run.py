#!/usr/bin/env python3
"""Independently rerun the Analysis named-premise owner-text review."""

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
BASE_COMMIT = "27871e7"
FENCE_END = "\n" + chr(96) * 3 + "\n"

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
    "docs-next/analysis/transport-composition-and-replay.md",
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
    "docs-next/pir/fiat-shamir.md",
    "docs-next/pir/interfaces-and-plans.md",
    "docs-next/pir/interactive-core.md",
    "evaluation/analysis-premise-intake-probe/run.py",
    "evaluation/analysis-premise-intake-probe/model.py",
    "evaluation/analysis-premise-intake-probe/independent.py",
    "evaluation/analysis-premise-intake-probe/fixture.json",
    "evaluation/analysis-premise-intake-probe/expected-findings.json",
    "evaluation/k3-analysis-closure/reference_model.py",
    "evaluation/k3-analysis-closure/tests/test_reference_model.py",
    "evaluation/k3-analysis-closure/README.md",
    "evaluation/k2-protocol-fiat-shamir/reference_model.py",
    "evaluation/finite-cover-analysis/tests/test_finite_cover.py",
    "evaluation/k3-integrated-closure/tests/test_reference_model.py",
)

LAW_FAMILY_NAMES = (
    "ProviderDeclaration",
    "ClosedProviderCarrier",
    "ExactModelBindingLaw",
    "ExactNamedHypothesis",
    "FreshSamplingHypothesis",
    "ConstructionSamplerAdequacyHypothesis",
    "ConstructionOracleProcessHypothesis",
    "SamplerAdequacyHypothesis",
    "OracleProcessHypothesis",
    "OperationalCompletionHypothesis",
    "HonestCommitHypothesis",
    "HonestRespondHypothesis",
)


class ReviewError(RuntimeError):
    """The reviewed source or a frozen observation drifted."""


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


def _definition_block(text: str, start_selector: str, end_selector: str) -> str:
    start = text.find(start_selector)
    _require(start >= 0, f"definition is absent: {start_selector}")
    end = text.find(end_selector, start + len(start_selector))
    _require(end > start, f"definition terminator is absent: {end_selector}")
    return text[start:end]


def _name_review(pages: dict[str, str]) -> dict[str, Any]:
    surface = _definition_surface()
    counts = {name: _definition_count(surface, name) for name in LAW_FAMILY_NAMES}
    _require(all(count == 1 for count in counts.values()), "a named law family is not defined exactly once")

    model = pages["docs-next/analysis/analysis-model.md"]
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    _require(
        "ProviderDeclaration =\n  closed schema law family" in model
        and "ClosedProviderCarrier =\n  closed schema law family" in model,
        "a provider family lost its closed-schema statement",
    )
    _require(
        "ExactModelBindingLaw<P,K> =\n  TotalAnalysisLawSignature<P," in model
        and "ExactNamedHypothesis<P,K> =\n  TotalAnalysisLawSignature<P," in model
        and "NamedHypothesisArgumentSchema<P,K>" in model,
        "a generic law family lost its displayed signature",
    )
    bound_value = _definition_block(
        model, "AnalysisNamedPremiseBoundValue<P,K> =", "\n\nAnalysisNamedPremiseSource<P>"
    )
    _require(
        "BoundProviderOutcomeCarrierMap<Protocol: ProtocolId>(" in bound_value
        and "AnalysisProviderOutcomeCarrierMapBody<P,Protocol>" in bound_value,
        "the provider bound-value arm is not an explicit dependent variant",
    )
    goal = _record_block(model, "AnalysisGoalBody =")
    _require(
        "AnalysisNamedPremiseBindingValue" in goal
        and "AnalysisNamedPremiseBindingValue =" in model
        and "AnalysisNamedPremiseId<P,r.kind>" in model,
        "the goal binding carrier no longer fixes the direct profile and requirement kind",
    )
    construction_bindings = _definition_block(
        crypto,
        "FiatShamirConstructionPremiseBindings(\n    S: AnalysisSubjectTuple,",
        FENCE_END,
    )
    _require(
        "ell0: StatementLength(AnalysisStatementType(S))" in construction_bindings
        and "AFKMemberKnowledgeQuestion(S, ell0)" in construction_bindings
        and "FiatShamirConstructionPremiseBindings(S, ell0)" in crypto,
        "the construction binding helper or its caller lost the statement-length binder",
    )
    _require(
        "AnalysisChallengeFreshLawCoordinate(S) =" in crypto
        and "[challenges[S.challenge_ref].fresh_law]" in crypto
        and "SchnorrFreshLawRef(S) =\n  the value of the leaf" in crypto,
        "the fresh-law reference is no longer derived from the authenticated public-coin view",
    )

    return {
        "named_law_families": counts,
        "closed_schema_families": 2,
        "profile_and_kind_binders_closed": True,
        "provider_arm_protocol_binder_closed": True,
        "goal_binding_value_profile_and_kind_closed": True,
        "construction_length_binder_closed": True,
        "fresh_law_owner_leaf_closed": True,
        "remaining_owner_name_gaps": [],
    }


def _constructor_blocks(text: str, expression: str) -> list[tuple[int, str]]:
    result: list[tuple[int, str]] = []
    for match in re.finditer(expression, text):
        brace = text.find("{", match.start(), match.end() + 1)
        _require(brace >= 0, "constructor match has no opening brace")
        depth = 0
        for index in range(brace, len(text)):
            if text[index] == "{":
                depth += 1
            elif text[index] == "}":
                depth -= 1
                if depth == 0:
                    result.append(
                        (
                            text.count("\n", 0, match.start()) + 1,
                            text[match.start() : index + 1],
                        )
                    )
                    break
        else:
            raise ReviewError("constructor display has an unclosed body")
    return result


def _anonymous_nodes(relative: str, text: str) -> list[tuple[str, int, bool]]:
    rows: list[tuple[str, int, bool]] = []
    for _context_line, block in _constructor_blocks(
        text, r"(?<![A-Za-z0-9_])AnalysisHypothesisContextBody\s*\{"
    ):
        for match in re.finditer(r"\{\s*\d+\s*,\s*AnalysisGoalId\(", block):
            end = block.find("}", match.start())
            _require(end >= 0, "hypothesis node has no closing brace")
            body = block[match.start() : end + 1]
            absolute = text.find(block) + match.start()
            rows.append((relative, text.count("\n", 0, absolute) + 1, "premises(goal)" in body))
    return rows


def _constructor_review(pages: dict[str, str]) -> dict[str, Any]:
    specifications = (
        ("AnalysisQuestionBody", r"(?<![A-Za-z0-9_])AnalysisQuestionBody\s*\{", "named_premise_requirements", 11),
        ("AnalysisGoalBody", r"(?<![A-Za-z0-9_])AnalysisGoalBody\s*\{", "named_premise_bindings", 12),
        ("AnalysisHypothesisContextBody", r"(?<![A-Za-z0-9_])AnalysisHypothesisContextBody\s*\{", "exact_named_premise_ids", 6),
        ("AnalysisSupportInstantiationBody", r"(?<![A-Za-z0-9_])AnalysisSupportInstantiationBody\s*\{", "exact_named_premise_ids", 5),
        ("AnalysisJudgmentRecordBody", r"(?<![A-Za-z0-9_])AnalysisJudgmentRecordBody\s*\{", "exact_named_premise_ids", 1),
        ("AnalysisNamedPremiseBody", r"AnalysisNamedPremiseBody<[^>]+>\s*\{", "kind", 12),
    )
    metrics: dict[str, Any] = {}
    for name, expression, field, expected_count in specifications:
        rows: list[tuple[str, int, bool]] = []
        for relative, text in pages.items():
            rows.extend(
                (relative, line, field in block)
                for line, block in _constructor_blocks(text, expression)
            )
        _require(len(rows) == expected_count, f"the {name} constructor census drifted")
        _require(all(row[2] for row in rows), f"an affected {name} display is incomplete")
        metrics[name] = {
            "constructors": len(rows),
            "field_complete": len(rows),
        }

    nodes: list[tuple[str, int, bool]] = []
    for relative, text in pages.items():
        nodes.extend(_anonymous_nodes(relative, text))
    _require(len(nodes) == 31, "the anonymous hypothesis-node census drifted")
    missing = [f"{relative}:{line}" for relative, line, complete in nodes if not complete]
    _require(not missing, "an anonymous hypothesis-node display omits premises(goal)")

    model = pages["docs-next/analysis/analysis-model.md"]
    _require(
        "exact_named_premise_ids: PremiseIdsOfProposition(proposition_id)" in model
        and "carrying\n     each node's exact_named_premise_ids" in model
        and "exact_named_premise_ids to the canonical union" in model,
        "a repaired derivation helper regressed",
    )
    _require(
        "premises(goal)" in model
        and "denotes exactly PremiseIdsOfGoal" in model
        and "ContextPremiseIds(nodes, roots) =" in model,
        "the node/context notation law drifted",
    )
    return {
        "body_constructors": metrics,
        "anonymous_hypothesis_nodes": len(nodes),
        "nodes_with_premises_goal": len(nodes),
        "nodes_missing_premises_goal": missing,
        "judgment_helper_complete": True,
        "dag_union_helper_complete": True,
        "context_premise_ids_matches_schema": True,
    }


def _intake_review(pages: dict[str, str]) -> dict[str, Any]:
    model = pages["docs-next/analysis/analysis-model.md"]
    block = _definition_block(model, "IntakeAnalysisNamedPremises(", FENCE_END)
    required = (
        "return CannotAnswer for a missing key or an absent premise source",
        "return Refused when a supplied premise is well formed but its kind or\n     coordinate differs",
        "return Malformed for an extra, duplicate, noncanonical, or\n     caller-ordered key",
        "FreshChallengeOnly premise only for a question over a Fresh Protocol",
        "OracleModelOnly premise only for a question whose experiment uses\n     exactly that distribution profile",
        "ExactSubjectsOnly premise only for\n     a question over exactly those subjects",
        "RebindRequired admits no\n     question",
        "failure of any of these four checks returns Refused, before\n     any goal is formed",
        "binding map has the required\n     key set and no other key",
    )
    _require(all(snippet in block for snippet in required), "the intake partition drifted")

    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    generic_uses = crypto.count(
        "named_premise_requirements: NamedPremiseRequirementsOf(family, exact_subjects)"
    )
    empty_license = (
        "every other family of this profile and of the transport profile, the source\n"
        "premise families, asymptotic special soundness, theorem truth, theorem\n"
        "applicability, and family-instance correspondence, fixes the empty\n"
        "requirement sequence" in crypto
    )
    _require(generic_uses == 3 and empty_license, "the empty-family requirement license drifted")
    return {
        "classified_branches": {
            "CannotAnswer": ["missing-key", "absent-source"],
            "Refused": [
                "kind-mismatch",
                "coordinate-mismatch",
                "fresh-scope-mismatch",
                "oracle-model-mismatch",
                "subject-scope-mismatch",
                "rebind-required",
            ],
            "Malformed": [
                "extra-key",
                "duplicate-key",
                "noncanonical-key",
                "caller-ordered-key",
            ],
        },
        "default_branches": 0,
        "generic_requirement_constructors": generic_uses,
        "empty_family_sentence_licenses_all_generic_uses": True,
    }


def _decision_review(pages: dict[str, str]) -> dict[str, Any]:
    model = pages["docs-next/analysis/analysis-model.md"]
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    required = (
        "PIRConstructionPremiseCoordinate(" in model,
        "BoundProviderOutcomeCarrierMap<Protocol: ProtocolId>(" in model,
        "CanonicalMap<ProtocolOutcomeLane(Protocol),\n                 AnalysisProviderLaneImage<provider_carrier>>" in model,
        "whose value at a\n      lane is Image(_) exactly when" in model,
        "OperationalCompletion" in model,
        "model_scope: FreshChallengeOnly" in crypto,
        crypto.count("model_scope: OracleModelOnly(oracle_model)") == 4,
        "A question over a Fiat--Shamir Protocol\nselects no such premise" in crypto,
        "ProviderJudgmentRequirements(P: ProtocolId)" in crypto,
        "SchnorrNamedPremiseRequirements(S: AnalysisSubjectTuple)" in crypto,
        "FiatShamirConstructionPremiseRequirements(T, oracle_model)" in crypto,
        "FiatShamirNamedPremiseRequirements(F, oracle_model)" in crypto,
    )
    _require(all(required), "a selected decision representation drifted")
    return {
        "selected_decisions": [
            "Fresh distribution is a FreshChallengeOnly named premise",
            "Fiat-Shamir uses separate construction or family sampler and oracle premises",
            "provider outcome maps use Image or Unmodelled over the exact Protocol partition",
            "whole-partition provider statements add operational completion",
            "provider requirements are separate from the relation-bound Fresh question",
            "scope failure is Refused before goal formation",
        ],
        "selected_decisions_represented": True,
    }


def _schnorr_review(pages: dict[str, str]) -> dict[str, Any]:
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    subject = _record_block(crypto, "AnalysisSubjectTuple S =")
    _require(
        "fresh_prover_plan_id: ProverPlanId" in subject
        and "S.fresh_prover_plan_id names the Plan whose checked\n  realization and checked witness-surface extraction produced the surface" in crypto,
        "the Plan subject coordinate or adequacy clause drifted",
    )

    requirements = _definition_block(
        crypto,
        "SchnorrNamedPremiseRequirements(S: AnalysisSubjectTuple) =",
        "\n\nProviderJudgmentRequirements",
    )
    slots = re.findall(r'slot: "([a-z-]+)"', requirements)
    _require(
        slots == ["fresh-coin", "relation", "witness", "prover-state", "commit", "respond"],
        "the repaired Schnorr requirement sequence drifted",
    )
    _require(
        "PIRPlanStateCoordinate(PlanOf(S), StrategyStateSlotRef 0)" in requirements
        and "PlanOf(S), ProverDecisionPointRef 0, RecipeNodeRef 0" in requirements
        and "PlanOf(S), ProverDecisionPointRef 2, RecipeNodeRef 0" in requirements,
        "a typed Plan coordinate drifted",
    )

    bindings = _definition_block(
        crypto, "SchnorrNamedPremiseBindings(S: AnalysisSubjectTuple) =", "\n\nSchnorrExtractorPremiseBindings"
    )
    expected_constructors = (
        "FreshPublicCoinDistributionPremise(",
        "RelationPredicatePremise(S, SchnorrPremiseScope(S),",
        "WitnessTypePremise(S, SchnorrPremiseScope(S),",
        "ProverPrivateStatePremise(S,",
        "HonestCommitPremise(S,",
        "HonestRespondPremise(S,",
    )
    _require(
        all(snippet in bindings for snippet in expected_constructors)
        and bindings.count('"') >= 12,
        "the relation-bound Schnorr helper no longer spells all six exact premise constructors",
    )

    extractor_bindings = _definition_block(
        crypto,
        "SchnorrExtractorPremiseBindings(S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) =",
        "\n\nFiatShamirConstructionPremiseBindings",
    )
    _require(
        extractor_bindings.count("SchnorrExtractorPremiseScope(S, Ext)") == 2
        and "RelationPredicatePremise" in extractor_bindings
        and "WitnessTypePremise" in extractor_bindings,
        "the extractor question no longer forms its own two exact-subject premise identities",
    )
    extractor_scope = _definition_block(
        crypto,
        "SchnorrExtractorPremiseScope(S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) =",
        "\n\nRelationPredicatePremise",
    )
    _require(
        "SchnorrFixedExtractorWorksQuestion(S, Ext).exact_subjects" in extractor_scope,
        "the extractor premise scope is detached from the consuming question",
    )
    construction_bindings = _definition_block(
        crypto,
        "FiatShamirConstructionPremiseBindings(\n    S: AnalysisSubjectTuple,",
        FENCE_END,
    )
    _require(
        "ell0: StatementLength(AnalysisStatementType(S))" in construction_bindings
        and "AFKMemberKnowledgeQuestion(S, ell0)" in construction_bindings
        and "SamplerAdequacyFormOf(S.transcript_construction_id)" in construction_bindings,
        "the construction helper no longer binds length or derives its sampler form",
    )

    family_bindings = _definition_block(
        crypto, "FiatShamirFamilyPremiseBindings(F) =", FENCE_END
    )
    _require(
        "SamplerAdequacyFormOf(F)" in family_bindings
        and "FiatShamirFamilySamplerPremise" in family_bindings
        and "FiatShamirFamilyOracleProcessPremise" in family_bindings,
        "the family helper no longer spells both exact premise identities",
    )

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
        _require(coordinate in encoded, "a selected finite coordinate drifted")
    return {
        "relation_bound_requirements": len(slots),
        "provider_requirements": 1,
        "subject_plan_id_present": True,
        "subject_plan_adequacy_present": True,
        "typed_plan_coordinates": 3,
        "finite_candidate_ordinals": {
            "private_witness": 0,
            "witness_edge": 0,
            "persistent_state": 0,
            "commit_decision": 0,
            "commit_recipe_node": 0,
            "respond_decision": 2,
            "respond_recipe_node": 0,
        },
        "exact_relation_bound_constructors": len(expected_constructors),
        "extractor_question_owns_scope": True,
        "extractor_exact_premises": 2,
        "construction_helper_binds_length_parameter": True,
        "construction_sampler_form_derived": True,
        "family_sampler_form_derived": True,
        "owner_text_goal_identities_form_exactly": True,
    }


def _hypothesis_schema_review(pages: dict[str, str]) -> dict[str, Any]:
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    property_schema = _definition_block(
        crypto,
        "NamedHypothesisArgumentSchema<AnalysisCryptographicPropertyLanguageProfileId, K> =",
        "\n\nPremiseIdOf",
    )
    transport_schema = _definition_block(
        crypto,
        "NamedHypothesisArgumentSchema<AnalysisAFKTransportLanguageProfileId, K> =",
        "\n\nSamplerAdequacyHypothesis",
    )
    property_rows = {
        "FreshPublicCoinDistribution": (
            "coordinate: PIRPublicCoinLawCoordinate",
            "distribution_model: AnalysisDistributionProfileId",
        ),
        "FiatShamirSamplerAdequacy": (
            "coordinate: PIRConstructionPremiseCoordinate(_, SamplerAdequacy)",
            "oracle_model: AnalysisDistributionProfileId",
            "form: SamplerAdequacyForm",
        ),
        "FiatShamirOracleProcess": (
            "coordinate: PIRConstructionPremiseCoordinate(_, OracleProcess)",
            "oracle_model: AnalysisDistributionProfileId",
        ),
        "OperationalCompletion": (
            "coordinate: PIRProtocolOutcomePartitionCoordinate",
            "provider: AnalysisProviderDeclaration<AnalysisCryptographicPropertyLanguageProfileId>",
        ),
        "HonestCommit or K = HonestRespond": (
            "coordinate: PIRPlanRecipeCoordinate",
        ),
    }
    for kind, fields in property_rows.items():
        marker = property_schema.find(f"when K = {kind}")
        _require(marker >= 0, f"property schema lost its {kind} row")
        row = property_schema[property_schema.rfind("[", 0, marker) : marker]
        positions = [row.find(field) for field in fields]
        _require(
            all(position >= 0 for position in positions)
            and positions == sorted(positions)
            and fields[0].startswith("coordinate:"),
            f"property schema {kind} no longer has coordinate-first exact arguments",
        )
    _require(
        property_schema.count("when K =") == 5,
        "the property hypothesis schema gained an unreviewed row",
    )

    transport_rows = {
        "FiatShamirSamplerAdequacy": (
            "coordinate: AnalysisFamilyPremiseCoordinate(_, SamplerAdequacy)",
            "oracle_model: AnalysisDistributionProfileId",
            "form: SamplerAdequacyForm",
        ),
        "FiatShamirOracleProcess": (
            "coordinate: AnalysisFamilyPremiseCoordinate(_, OracleProcess)",
            "oracle_model: AnalysisDistributionProfileId",
        ),
    }
    for kind, fields in transport_rows.items():
        marker = transport_schema.find(f"when K = {kind}")
        _require(marker >= 0, f"transport schema lost its {kind} row")
        row = transport_schema[transport_schema.rfind("[", 0, marker) : marker]
        positions = [row.find(field) for field in fields]
        _require(
            all(position >= 0 for position in positions)
            and positions == sorted(positions)
            and fields[0].startswith("coordinate:"),
            f"transport schema {kind} no longer has coordinate-first exact arguments",
        )
    _require(
        transport_schema.count("when K =") == 2,
        "the transport hypothesis schema gained an unreviewed row",
    )

    declaration_arities = {
        "FreshSamplingHypothesis": 2,
        "ConstructionSamplerAdequacyHypothesis": 3,
        "ConstructionOracleProcessHypothesis": 2,
        "OperationalCompletionHypothesis": 2,
        "HonestCommitHypothesis": 1,
        "HonestRespondHypothesis": 1,
        "SamplerAdequacyHypothesis": 3,
        "OracleProcessHypothesis": 2,
    }
    declaration_order = tuple(declaration_arities)
    for index, name in enumerate(declaration_order):
        start = crypto.find(f"{name} =")
        _require(start >= 0, f"hypothesis declaration is absent: {name}")
        end = crypto.find("\n\n", start)
        _require(end > start, f"hypothesis declaration is not closed: {name}")
        block = re.sub(r"\s+", " ", crypto[start:end])
        _require(
            "ExactNamedHypothesis<" in block
            and "canonical arguments are [ coordinate:" in block,
            f"{name} is not an exact coordinate-first hypothesis declaration",
        )
    _require(
        crypto.count("ExactNamedHypothesis<Analysis") == len(declaration_arities),
        "the concrete hypothesis declaration census drifted",
    )
    return {
        "property_schema_rows": len(property_rows),
        "transport_schema_rows": len(transport_rows),
        "hypothesis_declarations": len(declaration_arities),
        "argument_arities": declaration_arities,
        "all_coordinate_first": True,
        "free_or_extra_arguments": [],
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
    manifest_paths = {_json(path)["key"]: path for path in MIGRATED_MANIFESTS}
    sequence_equal: dict[str, bool] = {}
    model = pages["docs-next/analysis/analysis-model.md"]
    for key, name in catalog_names.items():
        sequence_equal[key] = (
            _catalog(model, name)
            == _json(manifest_paths[key])["supported_subject_kinds"]
        )
    _require(all(sequence_equal.values()), "an owner catalog and manifest sequence differ")

    observed_definition_bumps: dict[str, list[str]] = {}
    for relative in MIGRATED_MANIFESTS:
        old = json.loads(_old_bytes(relative))
        current = _json(relative)
        _require(
            old["revision"] == 1 and current["revision"] == 1,
            "a profile revision transition drifted",
        )
        old_definitions = {(row["kind"], row["name"]): row for row in old["definitions"]}
        observed_definition_bumps[current["key"]] = [
            row["name"]
            for row in current["definitions"]
            if row["revision"]
            != old_definitions[(row["kind"], row["name"])]["revision"]
        ]
    _require(
        observed_definition_bumps
        == {
            "analysis-kernel": [],
            "analysis-cryptographic-property": [],
            "analysis-afk-transport": [],
        },
        "the profile-law revision set drifted",
    )

    publication = ROOT / "evaluation" / "semantic-profile-publication"
    reference = _load_module(
        "_analysis_premise_round2_reference", publication / "reference_model.py"
    )
    cold = _load_module(
        "_analysis_premise_round2_cold", publication / "independent.py"
    )
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
        "profile_revision_bumps_in_review_range": 0,
        "observed_definition_bumps": observed_definition_bumps,
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
        if isinstance(node.func, ast.Name):
            name = node.func.id
        elif isinstance(node.func, ast.Attribute):
            name = node.func.attr
        else:
            name = ""
        if name in result:
            result[name] += 1
    return result


def _class_fields(tree: ast.Module, selected: Iterable[str]) -> dict[str, list[str]]:
    wanted = set(selected)
    result: dict[str, list[str]] = {}
    for node in tree.body:
        if not isinstance(node, ast.ClassDef) or node.name not in wanted:
            continue
        result[node.name] = [
            statement.target.id
            for statement in node.body
            if isinstance(statement, ast.AnnAssign)
            and isinstance(statement.target, ast.Name)
        ]
    return result


RELATION_GOAL_DIGEST = "79dcc80fff8307a7d2ab79ba523220ce0e17337bef2af0f6ba19fbe6cb17ccb4"
FAMILY_GOAL_DIGEST = "9c49308e1e89c5da7f01b783dd323428fb71470fe3acfd9a31d021d47ca1b2f2"


def _load_migrated_analysis() -> Any:
    package = ROOT / "evaluation/k3-analysis-closure"
    path = package / "reference_model.py"
    sys.path.insert(0, str(package))
    try:
        return _load_module("_analysis_premise_round3_migrated", path)
    finally:
        sys.path.pop(0)


def _independent_id_datum(module: Any, identifier: Any) -> Any:
    return module.k1.BytesValue(identifier.internal_reference())


def _independent_kind_body(module: Any, kind: Any) -> Any:
    ordinal = tuple(module.AnalysisNamedPremiseKind).index(kind)
    return module.k1.DatumVariant(ordinal, module.k1.UNIT)


def _independent_process_body(module: Any, process: Any) -> Any:
    ordinal = tuple(module.AnalysisPremiseProcessKind).index(process)
    return module.k1.DatumVariant(ordinal, module.k1.UNIT)


def _independent_coordinate_body(module: Any, coordinate: Any) -> Any:
    k1 = module.k1
    name = type(coordinate).__name__
    if name == "PIRPublicCoinLawCoordinate":
        return k1.DatumVariant(0, k1.DatumRecord(((0, coordinate.declaration_ref),)))
    if name == "AnalysisFamilyPremiseCoordinate":
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, coordinate.family_definition_id)),
                    (1, _independent_process_body(module, coordinate.process_kind)),
                )
            ),
        )
    if name == "PIRConstructionPremiseCoordinate":
        return k1.DatumVariant(
            2,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, coordinate.transcript_construction_id)),
                    (1, _independent_process_body(module, coordinate.process_kind)),
                )
            ),
        )
    if name == "PIRProtocolOutcomePartitionCoordinate":
        return k1.DatumVariant(
            3,
            k1.DatumRecord(((0, _independent_id_datum(module, coordinate.protocol_id)),)),
        )
    if name == "RelationsModelEvaluatorCoordinate":
        return k1.DatumVariant(
            4,
            k1.DatumRecord(
                ((0, _independent_id_datum(module, coordinate.relation_semantic_model_id)),)
            ),
        )
    if name == "RelationsWitnessPlanJoinCoordinate":
        return k1.DatumVariant(
            5,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, coordinate.relation_interface_id)),
                    (1, k1.Nat(coordinate.private_witness_ordinal)),
                    (2, _independent_id_datum(module, coordinate.plan_witness_binding_id)),
                    (3, k1.Nat(coordinate.witness_edge_ordinal)),
                )
            ),
        )
    if name == "PIRPlanStateCoordinate":
        return k1.DatumVariant(
            6,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, coordinate.prover_plan_id)),
                    (1, k1.Nat(coordinate.strategy_state_slot_ordinal)),
                )
            ),
        )
    if name == "PIRPlanRecipeCoordinate":
        return k1.DatumVariant(
            7,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, coordinate.prover_plan_id)),
                    (1, k1.Nat(coordinate.prover_decision_point_ordinal)),
                    (2, k1.Nat(coordinate.recipe_node_ordinal)),
                )
            ),
        )
    raise ReviewError(f"independent premise encoder does not know {name}")


def _independent_law_term_body(module: Any, term: Any) -> Any:
    return module.k1.DatumRecord(
        (
            (0, term.law_ref),
            (1, module.k1.DatumSeq(tuple(term.canonical_arguments))),
        )
    )


def _independent_bound_body(module: Any, bound: Any) -> Any:
    k1 = module.k1
    name = type(bound).__name__
    if name == "BoundModel":
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (0, _independent_id_datum(module, bound.semantic_subject_ref)),
                    (1, _independent_law_term_body(module, bound.law_term)),
                )
            ),
        )
    if name == "BoundHypothesis":
        return k1.DatumVariant(1, _independent_law_term_body(module, bound.law_term))
    raise ReviewError(f"independent premise encoder does not know {name}")


def _independent_source_body(module: Any, source: Any) -> Any:
    k1 = module.k1
    name = type(source).__name__
    if name == "OwnerSemanticCoordinate":
        return k1.DatumVariant(
            0, _independent_id_datum(module, source.semantic_subject_ref)
        )
    if name == "CandidateOwnerCoordinate":
        return k1.DatumVariant(
            1, _independent_id_datum(module, source.semantic_subject_ref)
        )
    if name == "FamilyHypothesisSource":
        return k1.DatumVariant(2, source.family_coordinate)
    raise ReviewError(f"independent premise encoder does not know {name}")


def _independent_scope_body(module: Any, scope: Any) -> Any:
    k1 = module.k1
    name = type(scope).__name__
    if name == "FreshChallengeOnly":
        return k1.DatumVariant(0, k1.UNIT)
    if name == "OracleModelOnly":
        return k1.DatumVariant(
            1, _independent_id_datum(module, scope.distribution_profile_id)
        )
    if name == "ExactSubjectsOnly":
        return k1.DatumVariant(
            2,
            k1.DatumSeq(
                tuple(_independent_id_datum(module, item) for item in scope.exact_subjects)
            ),
        )
    if name == "RebindRequired":
        return k1.DatumVariant(3, k1.UNIT)
    raise ReviewError(f"independent premise encoder does not know {name}")


def _independent_premise_body(module: Any, body: Any) -> Any:
    k1 = module.k1
    evidence = tuple(module.AnalysisPremiseEvidenceDepth).index(body.evidence_depth)
    return k1.DatumRecord(
        (
            (0, _independent_kind_body(module, body.kind)),
            (1, _independent_coordinate_body(module, body.coordinate)),
            (2, _independent_bound_body(module, body.bound_model_or_hypothesis)),
            (3, _independent_source_body(module, body.source)),
            (4, k1.DatumVariant(evidence, k1.UNIT)),
            (5, _independent_scope_body(module, body.model_scope)),
        )
    )


def _independent_requirement_body(module: Any, requirement: Any) -> Any:
    return module.k1.DatumRecord(
        (
            (0, module.k1.Symbol(requirement.slot)),
            (1, _independent_kind_body(module, requirement.kind)),
            (2, _independent_coordinate_body(module, requirement.coordinate)),
        )
    )


def _independent_profiled_id(
    module: Any, subject_kind: str, profile_id: Any, body: Any
) -> Any:
    return module.k1.profiled_content_id(
        subject_kind,
        profile_id,
        body,
        semantic_regime=module.k1.SEMANTIC_REGIME_ID,
    )


def _registry_body(module: Any, identifier: Any, subject_kind: str) -> Any:
    entry = module._ANALYSIS_FORMATION_REGISTRY.get(identifier.internal_reference())
    _require(entry is not None and entry[0] == subject_kind, f"missing formed {subject_kind} body")
    return entry[2]


def _registry_identifier(module: Any, subject_kind: str, digest: str) -> Any:
    matches = [
        entry[3]
        for entry in module._ANALYSIS_FORMATION_REGISTRY.values()
        if entry[0] == subject_kind and entry[3].digest.hex() == digest
    ]
    _require(len(matches) == 1, f"the frozen {subject_kind} identity is absent or ambiguous")
    return matches[0]


def _independent_goal_reconstruction(
    module: Any, observed_goal_id: Any, profile_id: Any
) -> dict[str, Any]:
    k1 = module.k1
    goal = _registry_body(module, observed_goal_id, "analysis.goal")
    question = _registry_body(module, goal.question_id, "analysis.question")
    question_datum = k1.DatumRecord(
        (
            (0, k1.profile_declaration_ref_datum(question.family)),
            (
                1,
                k1.DatumSeq(
                    tuple(_independent_id_datum(module, item) for item in question.exact_subjects)
                ),
            ),
            (2, question.context),
            (3, question.family_payload),
            (
                4,
                k1.DatumSeq(
                    tuple(
                        _independent_requirement_body(module, item)
                        for item in question.named_premise_requirements
                    )
                ),
            ),
        )
    )
    question_id = _independent_profiled_id(
        module, "analysis.question", profile_id, question_datum
    )
    _require(question_id == goal.question_id, "independent question identity disagrees")

    rebuilt_bindings = []
    premise_digests: dict[str, str] = {}
    for binding in goal.named_premise_bindings:
        premise = _registry_body(module, binding.premise_id, "analysis.named-premise")
        premise_id = _independent_profiled_id(
            module,
            "analysis.named-premise",
            profile_id,
            _independent_premise_body(module, premise),
        )
        _require(premise_id == binding.premise_id, "independent premise identity disagrees")
        premise_digests[binding.requirement.slot] = premise_id.digest.hex()
        rebuilt_bindings.append(
            k1.DatumRecord(
                (
                    (0, _independent_requirement_body(module, binding.requirement)),
                    (1, _independent_id_datum(module, premise_id)),
                )
            )
        )
    goal_datum = k1.DatumRecord(
        (
            (0, _independent_id_datum(module, question_id)),
            (1, k1.DatumSeq(tuple(rebuilt_bindings))),
        )
    )
    rebuilt_goal_id = _independent_profiled_id(
        module, "analysis.goal", profile_id, goal_datum
    )
    _require(rebuilt_goal_id == observed_goal_id, "independent goal identity disagrees")
    return {
        "question_digest": question_id.digest.hex(),
        "goal_digest": rebuilt_goal_id.digest.hex(),
        "premise_digests": premise_digests,
        "used_migrated_identity_former": False,
        "used_migrated_body_encoder": False,
    }


def _package_impact_review() -> dict[str, Any]:
    model_path = ROOT / "evaluation/k3-analysis-closure/reference_model.py"
    tests_path = ROOT / "evaluation/k3-analysis-closure/tests/test_reference_model.py"
    model_text = model_path.read_text(encoding="utf-8")
    tests_text = tests_path.read_text(encoding="utf-8")
    selected = (
        "AnalysisQuestionBodyV0",
        "AnalysisGoalBodyV0",
        "AnalysisHypothesisNodeV0",
        "AnalysisHypothesisContextBodyV0",
        "AnalysisSupportInstantiationBodyV0",
        "AnalysisJudgmentRecordBodyV0",
    )
    fields = _class_fields(ast.parse(model_text), selected)
    required = {
        "AnalysisQuestionBodyV0": "named_premise_requirements",
        "AnalysisGoalBodyV0": "named_premise_bindings",
        "AnalysisHypothesisNodeV0": "exact_named_premise_ids",
        "AnalysisHypothesisContextBodyV0": "exact_named_premise_ids",
        "AnalysisSupportInstantiationBodyV0": "exact_named_premise_ids",
        "AnalysisJudgmentRecordBodyV0": "exact_named_premise_ids",
    }
    _require(set(fields) == set(selected), "the selected Analysis body classes drifted")
    missing = {
        name: field for name, field in required.items() if field not in fields[name]
    }
    _require(not missing, "a migrated Analysis body class is missing its premise field")

    model_calls = _call_counts(model_path, selected)
    test_calls = _call_counts(tests_path, selected)
    combined = {name: model_calls[name] + test_calls[name] for name in selected}
    _require(
        combined
        == {
            "AnalysisQuestionBodyV0": 8,
            "AnalysisGoalBodyV0": 14,
            "AnalysisHypothesisNodeV0": 1,
            "AnalysisHypothesisContextBodyV0": 1,
            "AnalysisSupportInstantiationBodyV0": 1,
            "AnalysisJudgmentRecordBodyV0": 1,
        },
        "the migrated constructor-call census drifted",
    )

    module = _load_migrated_analysis()
    relation_goal = _registry_identifier(module, "analysis.goal", RELATION_GOAL_DIGEST)
    # The family goal is lazy in the migrated instrument.  Invoke its public
    # constructor only to obtain the observed comparison value and populate
    # the body registry; the reconstruction below uses neither that constructor
    # nor the migrated body encoders or identity former.
    family_goal = module.family_goal_id(
        module.SELECTED_AFK_FAMILY, "target-adaptive-knowledge-q-lt-N"
    )
    _require(
        family_goal.digest.hex() == FAMILY_GOAL_DIGEST,
        "the frozen migrated family goal identity drifted",
    )
    relation_reconstruction = _independent_goal_reconstruction(
        module, relation_goal, module.ANALYSIS_PROPERTY_PROFILE_ID
    )
    family_reconstruction = _independent_goal_reconstruction(
        module, family_goal, module.ANALYSIS_TRANSPORT_PROFILE_ID
    )

    k2_tree = ast.parse(_read("evaluation/k2-protocol-fiat-shamir/reference_model.py"))
    k2_fields = _class_fields(
        k2_tree, ("PublicCoinChallengeProjection", "TranscriptConstruction")
    )
    _require(
        k2_fields["PublicCoinChallengeProjection"]
        == ["challenge_coordinate", "domain_coordinate", "challenge_domain"],
        "the imported public-coin projection field set drifted",
    )
    fresh_helper = _definition_block(
        model_text,
        "def _schnorr_public_coin_law_coordinate(",
        "\n\ndef schnorr_named_premise_requirements",
    )
    _require(
        "projection.challenge_coordinate" in fresh_helper
        and "fresh_law" not in fresh_helper,
        "the frozen Fresh coordinate proxy drifted",
    )
    _require(
        "max_attempts" in k2_fields["TranscriptConstruction"]
        and "challenge_rules" not in k2_fields["TranscriptConstruction"]
        and "construction.max_attempts == 1" in model_text,
        "the frozen construction sampler-form proxy drifted",
    )

    property_catalog = _definition_block(
        model_text,
        "ANALYSIS_PROPERTY_DECLARATION_CATALOGS =",
        "\n\nANALYSIS_TRANSPORT_DECLARATION_CATALOGS =",
    )
    _require(
        "operational-completion-hypothesis-v0" not in property_catalog
        and 'k1.Symbol("operational-completion-hypothesis")' in tests_text,
        "the frozen operational-completion declaration gap drifted",
    )

    finite = _read("evaluation/finite-cover-analysis/tests/test_finite_cover.py")
    joined = _read("evaluation/k3-integrated-closure/tests/test_reference_model.py")
    _require(
        "exact_named_premise_ids" in finite
        and "named_premise_bindings" in finite
        and "named_premise_bindings" in joined
        and "intake_analysis_named_premises" in joined
        and "intake_analysis_named_premises" in finite,
        "a dependent migrated premise surface drifted",
    )
    return {
        "reference_body_classes_missing_fields": missing,
        "affected_reference_constructor_calls": combined,
        "independent_relation_goal": relation_reconstruction,
        "independent_family_goal": family_reconstruction,
        "owner_determined_premise_identities": False,
        "owner_determined_family_goal": True,
        "owner_determined_relation_fresh_goal": False,
        "remaining_refreeze_inputs": [
            "the authenticated PublicCoinView fresh_law declaration leaf for the migrated Schnorr Protocol",
            "identity-bearing construction challenge_rules and their per-rule maximum_draws values",
            "published property-profile ProviderDeclaration and ClosedProviderCarrier declarations",
            "an exact property-profile OperationalCompletionHypothesis declaration reference",
        ],
    }


def _lane_and_completion_review(pages: dict[str, str]) -> dict[str, Any]:
    model = pages["docs-next/analysis/analysis-model.md"]
    crypto = pages["docs-next/analysis/cryptographic-properties.md"]
    pir = _read("docs-next/pir/interactive-core.md")
    probe = _json("evaluation/analysis-premise-intake-probe/fixture.json")
    probe_expected = _json("evaluation/analysis-premise-intake-probe/expected-findings.json")
    migrated = _read("evaluation/k3-analysis-closure/reference_model.py")
    migrated_tests = _read("evaluation/k3-analysis-closure/tests/test_reference_model.py")
    lane_names = [
        "Accepted",
        "Rejected",
        "Aborted",
        "InterpretationFailed",
        "StrategyStopped",
        "OperationalNoncompletion",
    ]
    _require(
        "exactly the constructor names of the PIR outcome" in model
        and all(name in pir for name in lane_names)
        and probe["protocol_outcome_lanes"] == lane_names
        and all(f'= "{name}"' in migrated for name in lane_names),
        "the six provider-lane names disagree",
    )
    _require(
        "AnalysisProviderLaneImage<carrier> =\n    Image(CanonicalValue<carrier>)\n  | Unmodelled" in model
        and "Image(_) exactly when" in model
        and "provider lane image disagrees with modelled_lanes" in migrated
        and "API-M-PROVIDER-LANE-IMAGE" in json.dumps(probe_expected),
        "the Image/Unmodelled law is not shared by the reviewed surfaces",
    )
    _require(
        "OperationalCompletionHypothesis =" in crypto
        and "OperationalCompletionPremise(" in crypto
        and "OPERATIONAL_COMPLETION = \"OperationalCompletion\"" in migrated,
        "the tenth kind is absent from an owner or migrated surface",
    )
    property_catalog = _definition_block(
        migrated,
        "ANALYSIS_PROPERTY_DECLARATION_CATALOGS =",
        "\n\nANALYSIS_TRANSPORT_DECLARATION_CATALOGS =",
    )
    exact_declaration_present = "operational-completion-hypothesis-v0" in property_catalog
    arbitrary_test_law = 'k1.Symbol("operational-completion-hypothesis")' in migrated_tests
    _require(not exact_declaration_present and arbitrary_test_law, "the frozen completion-law mismatch drifted")
    return {
        "lane_names": lane_names,
        "lane_image_law_shared": True,
        "tenth_kind_shared": True,
        "migrated_exact_completion_declaration_present": exact_declaration_present,
        "migrated_test_uses_arbitrary_completion_law_symbol": arbitrary_test_law,
        "cross_surface_consistent": False,
    }


def _probe_review() -> dict[str, Any]:
    typed = _read("evaluation/analysis-premise-intake-probe/model.py")
    cold = _read("evaluation/analysis-premise-intake-probe/independent.py")
    run = _read("evaluation/analysis-premise-intake-probe/run.py")
    expected = _json("evaluation/analysis-premise-intake-probe/expected-findings.json")
    encoded = json.dumps(expected, sort_keys=True)
    _require(
        '"outcome": "Malformed", "code": "API-M-EXTRA-PREMISE"' in typed
        and '"outcome": "Malformed", "code": "API-M-EXTRA-PREMISE"' in cold,
        "the two intake evaluators do not classify an extra key as Malformed",
    )
    _require(
        "model_scope" in typed
        and "model_scope" in cold
        and "API-R-MODEL-SCOPE" in typed
        and "API-R-MODEL-SCOPE" in cold,
        "the two intake evaluators do not cover model scope",
    )
    _require(
        "all-model-scope-mismatches" in run
        and "API-M-EXTRA-PREMISE" in encoded
        and "API-R-MODEL-SCOPE" in encoded,
        "the predecessor probe did not freeze the new controls",
    )
    return {
        "extra_key_matches_owner_text": True,
        "model_scope_variants_checked": 4,
        "scope_mismatch_disposition": "Refused",
        "frozen_expected_findings": True,
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
        "hypothesis_argument_schemas": _hypothesis_schema_review(pages),
        "publication": _publication_review(pages),
        "package_impact": _package_impact_review(),
        "lane_and_completion": _lane_and_completion_review(pages),
        "predecessor_probe": _probe_review(),
    }
    review_findings = [
        Finding("name-closure", "Affirmative", "F0V2D1-A-NAME-CLOSURE"),
        Finding(
            "constructor-consistency",
            "Affirmative",
            "F0V2D1-A-CONSTRUCTOR-CONSISTENCY",
        ),
        Finding("intake-soundness", "Affirmative", "F0V2D1-A-INTAKE-SOUNDNESS"),
        Finding("decision-fidelity", "Affirmative", "F0V2D1-A-DECISION-FIDELITY"),
        Finding(
            "schnorr-coordinate-formation",
            "Affirmative",
            "F0V2D1-A-SCHNORR-BINDINGS",
        ),
        Finding(
            "profile-manifest-closure",
            "Affirmative",
            "F0V2D1-A-PROFILE-MANIFESTS",
        ),
        Finding(
            "existing-package-refreeze",
            "Negative",
            "F0V2D1-N-MIGRATED-IDENTITY-INPUTS",
        ),
        Finding(
            "hypothesis-argument-schema-closure",
            "Affirmative",
            "F0V2D1-A-HYPOTHESIS-ARGUMENT-SCHEMAS",
        ),
        Finding(
            "provider-lane-and-completion-consistency",
            "Negative",
            "F0V2D1-N-MIGRATED-COMPLETION-LAW",
        ),
    ]
    supporting = [
        Finding(
            "publication-compiler-agreement",
            "Affirmative",
            "F0V2D1-A-PUBLICATION-COMPILERS",
        ),
        Finding(
            "identity-rotation-cone",
            "Affirmative",
            "F0V2D1-A-ROTATION-CONE",
        ),
        Finding(
            "predecessor-probe-coverage",
            "Affirmative",
            "F0V2D1-A-PROBE-COVERAGE",
        ),
    ]
    unanswered = [
        finding.code for finding in review_findings if finding.outcome == "CannotAnswer"
    ]
    negatives = [
        finding.code for finding in review_findings if finding.outcome == "Negative"
    ]
    if all(finding.outcome == "Affirmative" for finding in review_findings):
        aggregate = {
            "outcome": "Affirmative",
            "code": "F0V2D1-A-ANALYSIS-PREMISE-TEXT-CLOSED",
            "blocking_findings": [],
            "cannot_answer_findings": [],
        }
    elif negatives:
        aggregate = {
            "outcome": "Negative",
            "code": "F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED",
            "blocking_findings": negatives,
            "cannot_answer_findings": unanswered,
        }
    else:
        aggregate = {
            "outcome": "CannotAnswer",
            "code": "F0V2D1-C-ANALYSIS-PREMISE-TEXT-NOT-CLOSED",
            "blocking_findings": [],
            "cannot_answer_findings": unanswered,
        }
    return {
        "aggregate": aggregate,
        "finding_codes": [
            finding.value() for finding in (*review_findings, *supporting)
        ],
        "metrics": metrics,
        "nonclaims": [
            "The review does not edit or publish Analysis owner semantics.",
            "Static name and constructor checks are not an Analysis implementation or mechanized proof.",
            "Publication compiler agreement is not evidence that the owner text is semantically closed.",
            "The finite Schnorr coordinates establish no relation truth, Plan honesty, theorem, or cryptographic property.",
            "Independent identity reconstruction checks canonical formation of the migrated bodies, not that their semantic inputs match the owner text.",
            "The negative migration findings do not imply that an unformed provider premise is false.",
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
        aggregate = result["aggregate"]
        print(
            "Analysis named-premise owner-text review: "
            f"{len(findings)}/{len(findings)} findings reproduced; "
            f"{negatives} negative, {unanswered} cannot answer; "
            f"aggregate {aggregate['outcome']}/{aggregate['code']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
