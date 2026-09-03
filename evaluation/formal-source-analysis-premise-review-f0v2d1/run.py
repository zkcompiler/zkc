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
BASE_COMMIT = "8ae0ee1"
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
    "docs-next/pir/interfaces-and-plans.md",
    "docs-next/pir/interactive-core.md",
    "evaluation/analysis-premise-intake-probe/run.py",
    "evaluation/analysis-premise-intake-probe/model.py",
    "evaluation/analysis-premise-intake-probe/independent.py",
    "evaluation/analysis-premise-intake-probe/fixture.json",
    "evaluation/analysis-premise-intake-probe/expected-findings.json",
    "evaluation/k3-analysis-closure/reference_model.py",
    "evaluation/k3-analysis-closure/tests/test_reference_model.py",
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
        "ExactModelBindingLaw<K> =\n  TotalAnalysisLawSignature<P," in model
        and "ExactNamedHypothesis<K> =\n  TotalAnalysisLawSignature<P," in model,
        "a generic law family lost its displayed signature",
    )

    concrete_signatures = {
        "FreshSamplingHypothesis": 2,
        "ConstructionSamplerAdequacyHypothesis": 3,
        "ConstructionOracleProcessHypothesis": 2,
        "SamplerAdequacyHypothesis": 3,
        "OracleProcessHypothesis": 2,
    }
    for name in concrete_signatures:
        _require(
            f"{name} =" in crypto and f"the profile's {name} declaration" in crypto,
            f"{name} no longer has a declaration and law-term use",
        )

    generic_profile_free = (
        "ExactModelBindingLaw<K> =\n  TotalAnalysisLawSignature<P," in model
        and "ExactNamedHypothesis<K> =\n  TotalAnalysisLawSignature<P," in model
    )
    bound_value = _definition_block(
        model, "AnalysisNamedPremiseBoundValue<P,K> =", "\n\nAnalysisNamedPremiseSource<P>"
    )
    free_protocol_parameter = (
        "AnalysisProviderOutcomeCarrierMapBody<P,Protocol>" in bound_value
        and "<Protocol>" not in bound_value.split("=", 1)[0]
    )
    goal = _record_block(model, "AnalysisGoalBody =")
    bare_named_premise_id = (
        "CanonicalMap<AnalysisNamedPremiseRequirement, AnalysisNamedPremiseId>" in goal
    )
    construction_bindings = _definition_block(
        crypto,
        "FiatShamirConstructionPremiseBindings(S: AnalysisSubjectTuple) =",
        FENCE_END,
    )
    unbound_construction_length = (
        "AFKMemberKnowledgeQuestion(S, ell0)" in construction_bindings
        and "ell0" not in construction_bindings.split("=", 1)[0]
    )
    _require(
        generic_profile_free
        and free_protocol_parameter
        and bare_named_premise_id
        and unbound_construction_length,
        "the frozen round-two name-closure gaps drifted",
    )

    return {
        "named_law_families": counts,
        "closed_schema_families": 2,
        "displayed_signature_families": 7,
        "concrete_hypothesis_argument_arities": concrete_signatures,
        "remaining_gaps": [
            "analysis-model.md:2125-2133 leaves P free in both generic law-family names",
            "analysis-model.md:2145-2150 leaves Protocol free in the provider bound-value arm",
            "analysis-model.md:2241-2245 and 3091-3094 use an unparameterized AnalysisNamedPremiseId carrier",
            "cryptographic-properties.md:2362-2365 uses ell0 without binding it",
            "the five concrete hypothesis declarations carry more canonical arguments than ExactNamedHypothesis<K> admits",
        ],
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
        ("AnalysisNamedPremiseBody", r"AnalysisNamedPremiseBody<[^>]+>\s*\{", "kind", 6),
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
    _require(
        missing
        == [
            "docs-next/analysis/cryptographic-properties.md:5196",
            "docs-next/analysis/cryptographic-properties.md:5364",
            "docs-next/analysis/cryptographic-properties.md:6100",
            "docs-next/analysis/cryptographic-properties.md:6102",
            "docs-next/analysis/cryptographic-properties.md:6109",
            "docs-next/analysis/cryptographic-properties.md:6112",
            "docs-next/analysis/cryptographic-properties.md:6115",
        ],
        "the round-two incomplete-node set drifted",
    )

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
        "nodes_with_premises_goal": len(nodes) - len(missing),
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
        "BoundProviderOutcomeCarrierMap(" in model,
        "CanonicalMap<ProtocolOutcomeLane(Protocol), CanonicalValue<provider_carrier>>" in model,
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
            "provider outcome maps use the exact Protocol-qualified lane partition",
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
    incomplete_slots = [
        slot
        for slot in ("relation", "witness", "prover-state", "commit", "respond")
        if f'"{slot}"' in bindings
    ]
    _require(
        incomplete_slots == ["relation", "witness", "prover-state", "commit", "respond"]
        and "model_scope" not in bindings
        and "AnalysisLawTerm {" not in bindings,
        "the residual Schnorr helper shape drifted",
    )
    construction_bindings = _definition_block(
        crypto,
        "FiatShamirConstructionPremiseBindings(S: AnalysisSubjectTuple) =",
        FENCE_END,
    )
    _require(
        "AFKMemberKnowledgeQuestion(S, ell0)" in construction_bindings,
        "the residual construction helper closure gap drifted",
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
        "bindings_without_exact_premise_bodies": incomplete_slots,
        "construction_helper_binds_length_parameter": False,
        "goal_identities_form_exactly": False,
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
            old["revision"] == 0 and current["revision"] == 1,
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
            "analysis-kernel": ["common-analysis-domain-v0"],
            "analysis-cryptographic-property": [
                "cryptographic-property-body-v0",
                "property-core-v0",
            ],
            "analysis-afk-transport": [
                "afk-transport-body-v0",
                "afk-application-v0",
            ],
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
        "profile_revision_bumps": 3,
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
    fields = _class_fields(ast.parse(model_path.read_text(encoding="utf-8")), selected)
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
    _require(missing == required, "the frozen reference-model field omissions drifted")

    model_calls = _call_counts(model_path, selected)
    test_calls = _call_counts(tests_path, selected)
    combined = {name: model_calls[name] + test_calls[name] for name in selected}
    expected_calls = {
        "AnalysisQuestionBodyV0": 8,
        "AnalysisGoalBodyV0": 14,
        "AnalysisHypothesisNodeV0": 5,
        "AnalysisHypothesisContextBodyV0": 4,
        "AnalysisSupportInstantiationBodyV0": 1,
        "AnalysisJudgmentRecordBodyV0": 1,
    }
    _require(combined == expected_calls, "the affected constructor-call census drifted")

    finite = _read("evaluation/finite-cover-analysis/tests/test_finite_cover.py")
    joined = _read("evaluation/k3-integrated-closure/reference_model.py")
    recursive = _read("evaluation/recursive-composition-boundary/reference_model.py")
    publication = _read("evaluation/semantic-profile-publication/tests/test_publication.py")
    _require(
        "k3-analysis-closure" in finite
        and "k3-analysis-closure" in joined
        and '"analysis.support-instantiation"' in recursive
        and '"analysis.judgment-record"' in recursive
        and "published-identities.json" in publication,
        "a dependent migration surface drifted",
    )
    return {
        "reference_body_classes_missing_fields": missing,
        "affected_reference_constructor_calls": combined,
        "direct_check": "research.property-analysis",
        "dependent_checks": [
            "research.finite-cover",
            "research.joined-semantic-boundary",
            "research.recursive-composition-boundary",
            "research.profile-publication",
        ],
        "encoding_surfaces": [
            "analysis schema descriptors and dispatch",
            "Analysis exact-body dataclasses and encoders",
            "hypothesis node/context premise-ID derivation",
            "constructor-profile predecessor extraction",
            "question, goal, support, and judgment helpers",
        ],
        "exact_binding_values_determined": False,
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
        "publication": _publication_review(pages),
        "package_impact": _package_impact_review(),
        "predecessor_probe": _probe_review(),
    }
    review_findings = [
        Finding("name-closure", "CannotAnswer", "F0V2D1-C-NAME-CLOSURE"),
        Finding(
            "constructor-consistency",
            "CannotAnswer",
            "F0V2D1-C-CONSTRUCTOR-CONSISTENCY",
        ),
        Finding("intake-soundness", "Affirmative", "F0V2D1-A-INTAKE-SOUNDNESS"),
        Finding("decision-fidelity", "Affirmative", "F0V2D1-A-DECISION-FIDELITY"),
        Finding(
            "schnorr-coordinate-formation",
            "CannotAnswer",
            "F0V2D1-C-SCHNORR-BINDINGS",
        ),
        Finding(
            "profile-manifest-closure",
            "Affirmative",
            "F0V2D1-A-PROFILE-MANIFESTS",
        ),
        Finding(
            "existing-package-refreeze",
            "CannotAnswer",
            "F0V2D1-C-REFREEZE-INPUTS",
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
            "The migration inventory does not implement or validate the required Analysis identity rotation.",
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
