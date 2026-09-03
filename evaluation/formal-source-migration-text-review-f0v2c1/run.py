#!/usr/bin/env python3
"""Independently audit the migrated PIR owner text before freeze."""

from __future__ import annotations

import argparse
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
BASE_COMMIT = "b82ce5e"

PAGES = (
    "docs-next/pir/interactive-core.md",
    "docs-next/pir/fiat-shamir.md",
    "docs-next/pir/duplex-sponge-fiat-shamir.md",
    "docs-next/pir/interfaces-and-plans.md",
    "docs-next/pir/endpoint-projection-views.md",
    "docs-next/oir/projection-contract.md",
)
MIGRATED_MANIFESTS = (
    "docs-next/oir/profiles/endpoint-graph.json",
    "docs-next/oir/profiles/projection-relation.json",
    "docs-next/pir/profiles/canonical-framed-fiat-shamir.json",
    "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json",
    "docs-next/pir/profiles/endpoint-source-view.json",
    "docs-next/pir/profiles/interaction.json",
    "docs-next/pir/profiles/interface-plan.json",
    "docs-next/pir/profiles/public-setup.json",
)
FOUNDATION = "docs-next/foundation/executable-foundations.md"
PROFILE_INDEX = "docs-next/foundation/semantic-profile-manifests.json"
PUBLISHED_IDENTITIES = "docs-next/pir/profiles/published-identities.json"


class ReviewError(RuntimeError):
    """The frozen review input or observation drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ReviewError(message)


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
        for relative in (*PAGES, *MIGRATED_MANIFESTS)
    }


def _definition_count(text: str, symbol: str) -> int:
    return len(
        re.findall(
            rf"^[ \t]*{re.escape(symbol)}(?:\([^\n]*\))?[ \t]*(?::=|=)",
            text,
            flags=re.MULTILINE,
        )
    )


def _record_fields(text: str, body: str) -> tuple[str, ...]:
    match = re.search(rf"^{re.escape(body)} = \{{\n", text, flags=re.MULTILINE)
    _require(match is not None, f"body {body} is absent")
    assert match is not None
    lines = text[match.end() :].splitlines()
    fields: list[str] = []
    depth = 1
    for line in lines:
        depth += line.count("{") - line.count("}")
        field = re.match(r"^  ([a-z][a-z0-9_]*)(?::|,|$)", line)
        if depth >= 1 and field:
            fields.append(field.group(1))
        if depth == 0:
            break
    _require(depth == 0, f"body {body} is not closed")
    _require(len(fields) == len(set(fields)), f"body {body} repeats a field")
    return tuple(fields)


VIEW_SCHEMAS: dict[str, tuple[tuple[str, str], ...]] = {
    "docs-next/pir/interactive-core.md": (
        ("PublicBindingView", "PublicBindingViewBody"),
        ("StrategyDecisionView", "StrategyDecisionViewBody"),
        ("PublicCoinView", "PublicCoinViewBody"),
        ("EffectView", "EffectViewBody"),
        ("ClaimReductionView", "ClaimReductionViewBody"),
        ("ExecutionView", "ExecutionViewBody"),
    ),
    "docs-next/pir/fiat-shamir.md": (
        ("TranscriptDeclarationView", "TranscriptDeclarationViewBody"),
        ("RequiredInfluenceView", "RequiredInfluenceViewBody"),
        ("ChallengeTransitionView", "ChallengeTransitionViewBody"),
        ("FSConstructionView", "FSConstructionViewBody"),
        ("ExecutionView", "CanonicalFramedExecutionViewBody"),
    ),
    "docs-next/pir/duplex-sponge-fiat-shamir.md": (
        ("DuplexTranscriptDeclarationView", "DuplexTranscriptDeclarationViewBody"),
        ("DuplexEncodedInputCoverageView", "DuplexEncodedInputCoverageViewBody"),
        ("DuplexChallengeTransitionView", "DuplexChallengeTransitionViewBody"),
        ("DuplexFSConstructionView", "DuplexFSConstructionViewBody"),
        ("ExecutionView", "DuplexExecutionViewBody"),
    ),
}


FS_PROSE_FIELDS: dict[str, tuple[str, ...]] = {
    "TranscriptDeclarationViewBody": (
        "fixed_initial_state_and_derived_initialization_schedule",
        "exact_frame_schedule_coordinates",
    ),
    "RequiredInfluenceViewBody": (
        "scope_binding_requirements",
        "per_challenge_ordered_required_influence_sets",
        "reduction_and_module_additions",
        "exact_prefix_law",
    ),
    "ChallengeTransitionViewBody": (
        "challenge_namespace_derivation",
        "acceptance_abi",
        "decoder_abi",
        "draw_bounds",
        "exact_length_law",
        "state_update_before_decode_law",
        "retry_law",
        "sampling_failure_law",
        "challenge_decoding_coordinates",
    ),
    "FSConstructionViewBody": ("result_schema",),
    "DuplexTranscriptDeclarationViewBody": (
        "state_carrier_and_invariant",
        "binary_instance_carrier_and_bit_convention",
        "exact_instance_binding_projection",
        "fixed_start_absorb_squeeze_laws",
        "exact_edge_case_laws",
        "exact_construction_material_schema",
        "prover_required_schedule",
        "verifier_complete_schedule",
    ),
    "DuplexEncodedInputCoverageViewBody": (
        "exact_instance_binding_sequence",
        "salt_coordinate",
        "per_challenge_ordered_encoded_input_coverage",
        "exact_message_coverage",
        "exact_challenge_coverage",
        "prover_required_prefix_law",
        "verifier_complete_schedule_law",
    ),
    "DuplexChallengeTransitionViewBody": (
        "per_challenge_squeeze_and_decoder_map",
        "decode_after_state_transition_law",
        "prover_execution_domain",
        "verifier_execution_domain",
    ),
    "DuplexFSConstructionViewBody": (
        "result_schema",
        "instance_projection",
        "construction_material_map",
        "prover_schedule_correspondence",
        "verifier_schedule_correspondence",
    ),
}

FS_UNDEFINED_FIELDS: dict[str, tuple[str, ...]] = {
    "DuplexTranscriptDeclarationViewBody": (
        "semantic_argument_shape",
        "exact_operational_resource_projection",
    ),
    "DuplexEncodedInputCoverageViewBody": ("prohibited_additions",),
    "DuplexChallengeTransitionViewBody": (
        "decoder_totality_contracts",
        "exact_squeeze_event_projection",
    ),
}


def _view_closure(pages: dict[str, str]) -> dict[str, Any]:
    schema_count = 0
    body_count = 0
    for relative, rows in VIEW_SCHEMAS.items():
        text = pages[relative]
        for view, expected_body in rows:
            selector = f"StaticViewSchema({view}) = {{"
            _require(text.count(selector) == 1, f"schema selector {view} is not unique")
            tail = text.split(selector, 1)[1].split("\n}", 1)[0]
            body = re.search(r"^  body: ([A-Za-z0-9_]+),$", tail, re.MULTILINE)
            _require(body is not None, f"schema {view} has no exact body field")
            assert body is not None
            _require(body.group(1) == expected_body, f"schema {view} points at another body")
            _require(
                _definition_count(text, expected_body) == 1,
                f"schema body {expected_body} is not defined exactly once on its page",
            )
            schema_count += 1
            body_count += 1

    interaction = pages["docs-next/pir/interactive-core.md"]
    foundation = _read(FOUNDATION)
    definition_surface = "\n".join((*pages.values(), foundation))
    unresolved = {
        symbol: _definition_count(definition_surface, symbol)
        for symbol in (
            "AdmittedModuleEffectAtom",
            "GuardInputs",
            "GuardTerm",
        )
    }
    _require(
        unresolved == {
            "AdmittedModuleEffectAtom": 0,
            "GuardInputs": 0,
            "GuardTerm": 0,
        },
        "the frozen unresolved-name set drifted",
    )
    _require(
        "{ Guard(s) | s a scope opening on o's scope path }" in interaction,
        "the scope-opening guard expression drifted",
    )
    scope = interaction.split("ScopeDecl = {", 1)[1].split("\n}", 1)[0]
    _require("guard" not in scope.lower(), "ScopeDecl unexpectedly acquired a guard")

    fs_pages = {
        **{body: pages["docs-next/pir/fiat-shamir.md"] for body in tuple(FS_PROSE_FIELDS)[:4]},
        **{body: pages["docs-next/pir/duplex-sponge-fiat-shamir.md"] for body in tuple(FS_PROSE_FIELDS)[4:]},
    }
    all_fields: dict[str, tuple[str, ...]] = {}
    for body, text in fs_pages.items():
        all_fields[body] = _record_fields(text, body)
        expected_special = set(FS_PROSE_FIELDS.get(body, ())) | set(
            FS_UNDEFINED_FIELDS.get(body, ())
        )
        _require(
            expected_special <= set(all_fields[body]),
            f"the field classification for {body} no longer selects source fields",
        )
    field_count = sum(map(len, all_fields.values()))
    prose_count = sum(map(len, FS_PROSE_FIELDS.values()))
    undefined_count = sum(map(len, FS_UNDEFINED_FIELDS.values()))
    _require(field_count == 95, "the eight family body displays no longer contain 95 fields")
    _require(prose_count == 40, "the prose-only field census drifted")
    _require(undefined_count == 5, "the undefined field census drifted")
    _require(
        "names such as `IdentityOnEveryOccurrenceRef` are nullary variant tags"
        in interaction,
        "the nullary closed-name rule is absent",
    )
    return {
        "static_view_schemas": schema_count,
        "resolved_schema_body_displays": body_count,
        "owner_unresolved_expressions": [
            "AdmittedModuleEffectAtom",
            "Guard(s) for a scope opening",
            "GuardInputs",
            "GuardTerm",
            "Must let substitution",
        ],
        "fs_body_fields": field_count,
        "fs_exact_fields": field_count - prose_count - undefined_count,
        "fs_prose_fields": prose_count,
        "fs_undefined_fields": undefined_count,
        "fs_unclosed_families": 11,
    }


def _terminal_review(interaction: str) -> dict[str, Any]:
    required = (
        "AttemptGuards(o) :=",
        "{ Guard(o) } union { Guard(s) | s a scope opening on o's scope path }",
        "Must(let x = e1 in e2)   = Must(e2), every reference to x contributing",
        "Positive(i) in MustWhenTrue(GuardTerm(o_t))",
    )
    for snippet in required:
        _require(snippet in interaction, "the frozen Terminal-law source drifted")

    # Exhaust the corrected opaque-guard inclusion law.  If a later occurrence
    # is live and all its guards hold, every included earlier guard holds too.
    atoms = (0, 1)
    implications = 0
    counterexamples = 0
    for earlier_mask in range(1 << len(atoms)):
        earlier = {atom for atom in atoms if earlier_mask & (1 << atom)}
        for later_mask in range(1 << len(atoms)):
            later = {atom for atom in atoms if later_mask & (1 << atom)}
            if not earlier <= later:
                continue
            for valuation in range(1 << len(atoms)):
                later_true = all(valuation & (1 << atom) for atom in later)
                if not later_true:
                    continue
                implications += 1
                if not all(valuation & (1 << atom) for atom in earlier):
                    counterexamples += 1
    _require(implications == 16 and counterexamples == 0, "guard-inclusion oracle drifted")

    # The committed positive predecessor shapes use feasible first-active
    # regions: q and g; otherwise h; otherwise fallback, or l; otherwise h;
    # otherwise fallback.  The omitted impossible-region exemption therefore
    # rejects none of these positive terminal regions, although it changes the
    # treatment of an unreachable authored Terminal.
    baseline = [0, 0, 0]
    for q in (False, True):
        for g in (False, True):
            for h in (False, True):
                if q and g:
                    baseline[0] += 1
                elif h:
                    baseline[1] += 1
                else:
                    baseline[2] += 1
    logical = [0, 0, 0]
    for l in (False, True):
        for h in (False, True):
            if l:
                logical[0] += 1
            elif h:
                logical[1] += 1
            else:
                logical[2] += 1
    _require(baseline == [2, 3, 3], "baseline terminal-region census drifted")
    _require(logical == [2, 1, 1], "logical terminal-region census drifted")
    return {
        "corrected_guard_inclusion_cases": implications,
        "corrected_guard_inclusion_counterexamples": counterexamples,
        "baseline_terminal_region_counts": baseline,
        "logical_terminal_region_counts": logical,
        "positive_impossible_terminal_regions": 0,
        "impossible_region_exemption_present": False,
    }


def _pcgraph_review(interaction: str) -> dict[str, Any]:
    transfer_snippets = (
        "output = Join(activity, producer of each input), after its exact K1 ABI check",
        "effect = Publish(activity); there is no output node",
        "effect = Join(activity, producer of the index);",
        "the publication-effect edge is not part of that join",
        "Failure precedence is lattice priority, `Invalid` above `VerifierPrivate`",
        "the effect node of every Public Query together with the producer node\nof its index",
        "every accepting Terminal state\nnode with the producer nodes of its public outputs",
    )
    for snippet in transfer_snippets:
        _require(snippet in interaction, "a selected graph transfer or sink sentence drifted")
    return {
        "named_transfer_clauses": 5,
        "challenge_precedence": "Invalid then VerifierPrivate then semantic validity",
        "public_query_sink_coordinates": 3,
        "acceptance_sink_families": 5,
    }


def _load_module(name: str, path: Path) -> Any:
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        raise ReviewError(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[name] = module
    specification.loader.exec_module(module)
    return module


def _publication_review() -> dict[str, Any]:
    directory = ROOT / "evaluation" / "semantic-profile-publication"
    reference = _load_module("_migration_review_publication_reference", directory / "reference_model.py")
    cold = _load_module("_migration_review_publication_cold", directory / "independent.py")
    reference_result = reference.compile_repository()
    cold_result = cold.compile_repository()
    reference_table = reference.identity_table(reference_result)
    cold_table = cold.identity_table(cold_result)
    _require(reference_table == cold_table, "independent publication compilers disagree")
    published = _json(PUBLISHED_IDENTITIES)
    current_legacy = reference.legacy_identity_table(reference_result)
    mismatches = [
        key
        for key, row in current_legacy["profiles"].items()
        if published["profiles"].get(key) != row
    ]
    _require(
        mismatches
        == [
            "interaction",
            "canonical-framed-fiat-shamir",
            "duplex-sponge-fiat-shamir",
            "public-setup",
            "commitment-opening",
            "oracle-commitment",
        ],
        "the expected unpublished legacy identity mismatch set drifted",
    )
    return {
        "compiler_agreement": True,
        "compiled_profiles": len(reference_table["profiles"]),
        "published_legacy_mismatches": mismatches,
        "publication_table_written": False,
    }


def _all_manifests() -> dict[str, tuple[str, dict[str, Any]]]:
    index = _json(PROFILE_INDEX)
    result: dict[str, tuple[str, dict[str, Any]]] = {}
    for row in index["manifests"]:
        key = row["key"]
        _require(key not in result, "profile index repeats a key")
        result[key] = (row["source"], _json(row["source"]))
    return result


def _strong_components(
    graph: dict[tuple[str, str, str], set[tuple[str, str, str]]]
) -> list[tuple[tuple[str, str, str], ...]]:
    index = 0
    indices: dict[tuple[str, str, str], int] = {}
    low: dict[tuple[str, str, str], int] = {}
    stack: list[tuple[str, str, str]] = []
    active: set[tuple[str, str, str]] = set()
    result: list[tuple[tuple[str, str, str], ...]] = []

    def visit(node: tuple[str, str, str]) -> None:
        nonlocal index
        indices[node] = index
        low[node] = index
        index += 1
        stack.append(node)
        active.add(node)
        for target in graph[node]:
            if target not in indices:
                visit(target)
                low[node] = min(low[node], low[target])
            elif target in active:
                low[node] = min(low[node], indices[target])
        if low[node] == indices[node]:
            component: list[tuple[str, str, str]] = []
            while True:
                current = stack.pop()
                active.remove(current)
                component.append(current)
                if current == node:
                    break
            result.append(tuple(sorted(component)))

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    return result


def _manifest_review(pages: dict[str, str]) -> dict[str, Any]:
    indexed = _all_manifests()
    definitions: dict[tuple[str, str, str], dict[str, Any]] = {}
    graph: dict[tuple[str, str, str], set[tuple[str, str, str]]] = {}
    migrated_definition_count = 0
    migrated_subject_count = 0
    for key, (_path, manifest) in indexed.items():
        for definition in manifest["definitions"]:
            node = (key, definition["kind"], definition["name"])
            _require(node not in definitions, "a profile repeats a declaration")
            definitions[node] = definition
            graph[node] = set()
        if _path in MIGRATED_MANIFESTS:
            migrated_definition_count += len(manifest["definitions"])
            migrated_subject_count += len(manifest["subjects"])

    for key, (_path, manifest) in indexed.items():
        for definition in manifest["definitions"]:
            node = (key, definition["kind"], definition["name"])
            for dependency in definition.get("dependencies", []):
                profile = key if dependency.get("profile", "self") == "self" else dependency["profile"]
                target = (profile, dependency["kind"], dependency["name"])
                _require(target in definitions, "a declaration dependency is unresolved")
                graph[node].add(target)
        local = {(item["kind"], item["name"]) for item in manifest["definitions"]}
        for subject in manifest["subjects"]:
            compiler = subject["body_compiler"]
            profile = key if compiler.get("profile", "self") == "self" else compiler["profile"]
            _require(
                (profile, compiler["kind"], compiler["name"]) in definitions,
                "a subject body compiler is unresolved",
            )
            for law in subject["laws"]:
                _require(("pir.semantic-law", law) in local or ("oir.semantic-law", law) in local or ("relations.semantic-law", law) in local or ("analysis.semantic-law", law) in local, "a subject law is unresolved")
            _require(any(name == subject["evaluator"] for _kind, name in local), "a subject evaluator is unresolved")
            _require(any(name == subject["failure_schema"] for _kind, name in local), "a subject failure schema is unresolved")

    components = [item for item in _strong_components(graph) if len(item) > 1]
    component_profiles = sorted({node[0] for component in components for node in component})
    component_edges = sum(
        1
        for component in components
        for source in component
        for target in graph[source]
        if target in component
    )
    _require(
        len(components) == 2
        and component_profiles
        == ["canonical-framed-fiat-shamir", "duplex-sponge-fiat-shamir"]
        and sum(map(len, components)) == 12
        and component_edges == 20,
        "the local declaration-reference component census drifted",
    )

    # These are the selected pre-publication revision changes.  They encode the
    # manual meaning audit; new declarations start at revision zero.
    expected_bumps = {
        "docs-next/oir/profiles/endpoint-graph.json": {
            ("oir.body-compiler", "endpoint-graph-body-v0"),
            ("oir.semantic-law", "endpoint-contract-derivation-v0"),
        },
        "docs-next/oir/profiles/projection-relation.json": {
            ("oir.body-compiler", "projection-proposition-body-v0"),
            ("oir.semantic-law", "exact-endpoint-projection-v0"),
        },
        "docs-next/pir/profiles/canonical-framed-fiat-shamir.json": {
            ("pir.semantic-law", "canonical-framed-source-views-v0"),
        },
        "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json": {
            ("pir.semantic-law", "duplex-sponge-source-views-v0"),
        },
        "docs-next/pir/profiles/endpoint-source-view.json": {
            ("pir.body-compiler", "endpoint-source-view-body-v0"),
        },
        "docs-next/pir/profiles/interaction.json": {
            ("pir.body-compiler", "interactive-core-body-v0"),
            ("pir.semantic-law", "core-admission-v0"),
            ("pir.semantic-law", "execution-and-replay-v0"),
            ("pir.semantic-law", "public-coin-eligibility-v0"),
            ("pir.semantic-law", "static-view-issuance-v0"),
        },
        "docs-next/pir/profiles/interface-plan.json": {
            ("pir.semantic-law", "interface-admission-v0"),
        },
        "docs-next/pir/profiles/public-setup.json": {
            ("pir.semantic-law", "public-setup-projection-and-issuance-v0"),
        },
    }
    revision_bumps = 0
    new_definitions = 0
    for relative in MIGRATED_MANIFESTS:
        try:
            old_text = subprocess.run(
                ["git", "show", f"{BASE_COMMIT}:{relative}"],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            ).stdout
            old = json.loads(old_text)
        except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
            raise ReviewError(f"cannot reconstruct the migration base for {relative}") from error
        current = _json(relative)
        _require(old["revision"] == 0 and current["revision"] == 1, "a migrated profile revision differs")
        old_rows = {(row["kind"], row["name"]): row for row in old["definitions"]}
        observed_bumps: set[tuple[str, str]] = set()
        for row in current["definitions"]:
            key = (row["kind"], row["name"])
            if key not in old_rows:
                _require(row["revision"] == 0, "a new declaration does not start at revision zero")
                new_definitions += 1
            elif row["revision"] != old_rows[key]["revision"]:
                _require(
                    old_rows[key]["revision"] == 0 and row["revision"] == 1,
                    "an existing declaration has another revision transition",
                )
                observed_bumps.add(key)
        _require(observed_bumps == expected_bumps[relative], "the selected definition revision set drifted")
        revision_bumps += len(observed_bumps)

    envelope_profiles = {
        "interaction": ("docs-next/pir/interactive-core.md", (2, 2, 1, 2)),
        "public-setup": ("docs-next/pir/interactive-core.md", (1, 1, 1, 1)),
        "canonical-framed-fiat-shamir": ("docs-next/pir/fiat-shamir.md", (2, 2, 2, 2)),
        "duplex-sponge-fiat-shamir": ("docs-next/pir/duplex-sponge-fiat-shamir.md", (2, 2, 2, 2)),
        "interface-plan": ("docs-next/pir/interfaces-and-plans.md", (2, 2, 1, 2)),
        "endpoint-source-view": ("docs-next/pir/endpoint-projection-views.md", (1, 1, 1, 1)),
    }
    prefixes = {
        "interaction": "PIR",
        "public-setup": "PublicSetup",
        "canonical-framed-fiat-shamir": "CanonicalFramed",
        "duplex-sponge-fiat-shamir": "Duplex",
        "interface-plan": "InterfacePlan",
        "endpoint-source-view": "Endpoint",
    }
    arm_counts: dict[str, list[int]] = {}
    suffixes = ("BindingPayload", "CapabilityRequirement", "NoPolicy", "PolicyClosure")
    for profile, (page, expected) in envelope_profiles.items():
        text = pages[page]
        counts: list[int] = []
        for suffix in suffixes:
            name = f"{prefixes[profile]}Source{suffix}Body(x) ="
            _require(text.count(name) == 1, f"source envelope compiler {name} is not unique")
            tail = text.split(name, 1)[1].split("\n```", 1)[0]
            block = re.split(r"\n[A-Za-z][A-Za-z0-9]*Body\(x\) =", tail, maxsplit=1)[0]
            counts.append(len(re.findall(r"^[ \t]*(?:\| )?V\(", block, re.MULTILINE)))
        _require(tuple(counts) == expected, f"source envelope arms differ for {profile}")
        arm_counts[profile] = counts

    return {
        "migrated_manifests": len(MIGRATED_MANIFESTS),
        "migrated_definitions": migrated_definition_count,
        "migrated_subjects": migrated_subject_count,
        "resolved_definition_dependencies": True,
        "resolved_subject_compilers": True,
        "local_reference_components": len(components),
        "local_reference_component_nodes": sum(map(len, components)),
        "local_reference_component_edges": component_edges,
        "local_reference_component_profiles": component_profiles,
        "profile_revision_bumps": len(MIGRATED_MANIFESTS),
        "definition_revision_bumps": revision_bumps,
        "new_revision_zero_definitions": new_definitions,
        "source_envelope_arm_counts": arm_counts,
    }


def _decision_review(pages: dict[str, str], manifest: dict[str, Any]) -> dict[str, Any]:
    interaction = pages["docs-next/pir/interactive-core.md"]
    canonical = pages["docs-next/pir/fiat-shamir.md"]
    duplex = pages["docs-next/pir/duplex-sponge-fiat-shamir.md"]
    applied = [
        "which a consumer of the view must\n  hold and reauthenticate; no view carries a preimage" in interaction,
        "A nominal law declaration is a hook,\nnot a distribution" in interaction,
        "ProtocolOutcomeLane(P) =" in interaction and "StrategyStopped" in interaction,
        all(
            snippet in interaction
            for snippet in (
                "fixation: None",
                "through the active terminal's occurrence inclusive",
                "PartialRunRecord(P) = {",
                "not a completed record",
                "run_record_schema: PIRRuntimeSchema",
            )
        ),
        manifest["local_reference_components"] == 2
        and _pcgraph_review(interaction)["named_transfer_clauses"] == 5,
        False,  # Catalog entries exist, but the selected exact family bodies do not.
        all(_json(path)["revision"] == 1 for path in MIGRATED_MANIFESTS),
        not any(path.startswith("docs-next/analysis/") or path.startswith("docs-next/relations/") or path.startswith("docs-next/foundation/") for path in (*PAGES, *MIGRATED_MANIFESTS)),
    ]
    _require(applied == [True, True, True, True, True, False, True, True], "decision-fidelity census drifted")
    _require("CanonicalFramedViewSchemaCatalog = {" in canonical, "canonical catalog is absent")
    _require("DuplexViewSchemaCatalog = {" in duplex, "duplex catalog is absent")
    return {
        "recorded_decisions": len(applied),
        "fully_applied_decisions": sum(applied),
        "incomplete_decisions": ["exact family view bodies"],
    }


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    pages = {relative: _read(relative) for relative in PAGES}
    view = _view_closure(pages)
    terminal = _terminal_review(pages["docs-next/pir/interactive-core.md"])
    pcgraph = _pcgraph_review(pages["docs-next/pir/interactive-core.md"])
    manifests = _manifest_review(pages)
    publication = _publication_review()
    decisions = _decision_review(pages, manifests)

    findings = [
        Finding("decision-fidelity", "Negative", "F0V2C1-N-DECISION-FIDELITY"),
        Finding("terminal-contract", "Negative", "F0V2C1-N-TERMINAL-CONTRACT"),
        Finding("public-coin-graph", "Affirmative", "F0V2C1-A-PCGRAPH-TRANSFER"),
        Finding("owner-name-closure", "Negative", "F0V2C1-N-OWNER-CLOSURE"),
        Finding("manifest-closure", "Affirmative", "F0V2C1-A-MANIFEST-CLOSURE"),
        Finding("publication-compilers", "Affirmative", "F0V2C1-A-PUBLICATION-COMPILERS"),
        Finding("family-body-closure", "Negative", "F0V2C1-N-FS-BODY-CLOSURE"),
    ]
    metrics = {
        "source_sha256": _source_hashes(),
        "decisions": decisions,
        "terminal": terminal,
        "pcgraph": pcgraph,
        "views": view,
        "manifests": manifests,
        "publication": publication,
    }
    return findings, metrics


def _expected() -> dict[str, Any]:
    value = _json(str(EXPECTED.relative_to(ROOT)))
    _require(type(value) is dict, "expected findings have another carrier")
    return value


def check() -> tuple[list[Finding], dict[str, Any]]:
    findings, metrics = evaluate()
    expected = _expected()
    _require([item.value() for item in findings] == expected["finding_codes"], "finding classifications drifted")
    _require(metrics == expected["metrics"], "review evidence metrics drifted")
    _require(
        expected["aggregate"]
        == {
            "outcome": "Negative",
            "code": "F0V2C1-N-MIGRATION-TEXT-NOT-CLOSED",
            "blocking_findings": [
                "F0V2C1-N-DECISION-FIDELITY",
                "F0V2C1-N-TERMINAL-CONTRACT",
                "F0V2C1-N-OWNER-CLOSURE",
                "F0V2C1-N-FS-BODY-CLOSURE",
            ],
        },
        "aggregate finding drifted",
    )
    return findings, metrics


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        findings, metrics = check() if args.check else evaluate()
    except ReviewError as error:
        print(f"migration text review failed: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(
            json.dumps(
                {
                    "aggregate": {
                        "outcome": "Negative",
                        "code": "F0V2C1-N-MIGRATION-TEXT-NOT-CLOSED",
                    },
                    "finding_codes": [item.value() for item in findings],
                    "metrics": metrics,
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        negatives = sum(item.outcome == "Negative" for item in findings)
        print(
            "Migration text freeze review: "
            f"{len(findings)}/{len(findings)} findings reproduced; "
            f"{negatives} blocking findings; aggregate Negative"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
