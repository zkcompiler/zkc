#!/usr/bin/env python3
"""Structured source-determinacy audit for the F1-R1C owner-view gate."""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
PUBLICATION_DIR = ROOT / "evaluation" / "semantic-profile-publication"
R1B_MODEL = (
    ROOT / "evaluation" / "formal-source-target-core-f1r1b" / "reference_model.py"
)
K2_MODEL = ROOT / "evaluation" / "k2-protocol-fiat-shamir" / "reference_model.py"
PUBLISHED_IDENTITIES = (
    ROOT / "docs-next" / "pir" / "profiles" / "published-identities.json"
)

COMMON_CATALOG_KINDS = frozenset(
    {
        "pir.body-compiler",
        "pir.evaluator-signature",
        "pir.failure-schema",
        "pir.semantic-law",
        "pir.source-fragment",
        "pir.subject-language",
    }
)
VIEW_BODIES = (
    "PublicBindingViewBody",
    "StrategyDecisionViewBody",
    "PublicCoinViewBody",
    "EffectViewBody",
    "ClaimReductionViewBody",
    "ExecutionViewBody",
)
COORDINATE_BODY_GRAMMARS = (
    "PIRStaticViewCoordinateBody",
    "PIRViewPathStepBody",
    "PIRViewAtomicBoundaryBody",
    "PIRStaticViewFieldCoordinateBody",
    "PIRStaticViewReadManifestBody",
)
LAW_FIELDS = (
    "prover_view_formation",
    "visible_history_law",
    "generated_execution_law",
    "replay_qualification_law",
    "relation_run_view_issuance_law",
)
LAW_FIELD_SELECTION = {
    "StrategyDecisionView.prover_view_formation_law": "prover-view-formation-v0",
    "ExecutionView.visible_history_law": "visible-history-v0",
    "ExecutionView.generated_execution_law": "execution-and-replay-v0",
    "ExecutionView.replay_qualification_law": "replay-qualification-v0",
    "ExecutionView.relation_run_view_issuance_law": "run-view-issuance-v0",
}
SOURCE_SUBJECT_KINDS = (
    "pir.source-binding-payload",
    "pir.source-capability-requirement",
    "pir.source-consumer",
    "pir.source-no-policy",
    "pir.source-policy-closure",
    "pir.source-purpose",
)
EXPECTED_STATIC_FRAGMENT_BODY_FUNCTIONS = (
    "PIRProfileLawReferenceBody",
    "PIRReferenceBody",
    "StaticViewBody",
    "PIRSourceConsumerRoleBody",
    "PIRSourcePurposeRoleBody",
    "PIRStaticViewCoordinateBody",
    "PIRStaticViewFieldCoordinateBody",
    "PIRStaticViewReadManifestBody",
    "PIRStaticViewBindingPayloadBody",
    "PIRStaticViewCapabilityRequirementBody",
    "PIRStaticViewNoPolicyBody",
    "PIRStaticViewPolicyClosureBody",
    "PIRSourceBindingPayloadBody",
    "PIRSourceCapabilityRequirementBody",
    "PIRSourceNoPolicyBody",
    "PIRSourcePolicyClosureBody",
)

EXPECTED_SOURCE_COMPILERS = {
    "pir.source-binding-payload": "source-binding-payload-body-v0",
    "pir.source-capability-requirement": "source-capability-requirement-body-v0",
    "pir.source-consumer": "source-consumer-role-body-v0",
    "pir.source-no-policy": "source-no-policy-body-v0",
    "pir.source-policy-closure": "source-policy-closure-body-v0",
    "pir.source-purpose": "source-purpose-role-body-v0",
}


class AuditError(RuntimeError):
    """The migrated owner-view source no longer has the rehearsed shape."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AuditError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise AuditError(detail)


def _definition_map(manifest: Mapping[str, Any]) -> dict[tuple[str, str], Any]:
    return {
        (str(item["kind"]), str(item["name"])): item for item in manifest["definitions"]
    }


def _subject_map(manifest: Mapping[str, Any]) -> dict[str, Any]:
    return {str(item["kind"]): item for item in manifest["subjects"]}


def _body_functions(fragment: bytes) -> tuple[str, ...]:
    try:
        text = fragment.decode("utf-8")
    except UnicodeDecodeError as error:
        raise AuditError("Interaction static-view fragment is not UTF-8") from error
    return tuple(re.findall(r"(?m)^([A-Za-z][A-Za-z0-9]+Body)\([^\n]*\) =", text))


def evaluate() -> tuple[tuple[Finding, ...], Mapping[str, Any]]:
    publication = _load_module(
        "_zkc_f1r1c_publication", PUBLICATION_DIR / "reference_model.py"
    )
    cold = _load_module(
        "_zkc_f1r1c_publication_cold", PUBLICATION_DIR / "independent.py"
    )
    r1b = _load_module("_zkc_f1r1c_r1b", R1B_MODEL)
    k2 = _load_module("_zkc_f1r1c_k2", K2_MODEL)

    reference_repository = publication.compile_repository()
    cold_repository = cold.compile_repository()
    reference_table = publication.identity_table(reference_repository)
    cold_table = cold.identity_table(cold_repository)
    _require(
        reference_table == cold_table,
        "the independent semantic-profile compilers disagree",
    )
    target = reference_repository.profiles["interaction"]
    cold_target = cold_repository.profiles["interaction"]
    _require(
        target.body_bytes == cold_target.body_bytes,
        "the independent Interaction profile bodies disagree",
    )
    _require(
        target.profile_id.internal_reference() == cold_target.identifier.ref(),
        "the independent Interaction profile references disagree",
    )
    findings: list[Finding] = [
        Finding(
            "published-profile-independent-agreement",
            "Affirmative",
            "F1R1C-A-PROFILE",
            "two independent compilers reconstruct the same Interaction profile",
        )
    ]

    try:
        published = json.loads(PUBLISHED_IDENTITIES.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError("cannot read the frozen profile identity table") from error
    _require(
        reference_table["profiles"]["interaction"]
        != published["profiles"]["interaction"],
        "the migrated Interaction profile unexpectedly equals the published row",
    )
    findings.append(
        Finding(
            "candidate-profile-rehearsal-control",
            "Affirmative",
            "F1R1C-A-CANDIDATE-PROFILE",
            "the candidate is reconstructed directly from the migrated manifests and remains unpublished",
        )
    )

    static_fragment = target.source_fragments["interaction-static-views"]
    _require(
        static_fragment == cold_target.source_fragments["interaction-static-views"],
        "the independent compilers extracted different static-view source",
    )
    _require(
        b"`PIRViewSchemaCatalog` in its inline profile-owned declaration catalog"
        in static_fragment,
        "the target no longer makes the inspected schema-catalog claim",
    )
    findings.append(
        Finding(
            "static-view-source-authenticated",
            "Affirmative",
            "F1R1C-A-STATIC-SOURCE",
            "the exact static-view source fragment is authenticated by the profile",
        )
    )

    for body in VIEW_BODIES:
        _require(
            f"{body} = {{".encode("ascii") in static_fragment,
            f"the static source omits {body}",
        )
    findings.append(
        Finding(
            "six-owner-view-surfaces-named",
            "Affirmative",
            "F1R1C-A-VIEW-SURFACE",
            "the source names five Core views and one Protocol ExecutionView",
        )
    )

    fixture = r1b.make_fixture()
    admitted_core = r1b.admit_core(fixture.core_candidate, fixture.environment)
    _require(
        (admitted_core.outcome, admitted_core.code)
        == ("Affirmative", "F1R1B-A-CORE-ADMITTED"),
        "the retained exact-target Core no longer admits",
    )
    admitted_protocol = r1b.admit_fresh_protocol(
        admitted_core.handle, fixture.protocol_candidate, fixture.environment
    )
    _require(
        (admitted_protocol.outcome, admitted_protocol.code)
        == ("Affirmative", "F1R1B-A-FRESH-ADMITTED"),
        "the retained exact-target Fresh Protocol no longer admits",
    )
    findings.append(
        Finding(
            "retained-admitted-owner-subject",
            "Affirmative",
            "F1R1C-A-ADMITTED-SUBJECT",
            "the R1B Core and Fresh Protocol provide exact admitted owner handles",
        )
    )

    manifest = target.manifest
    catalog_kinds = frozenset(kind for kind, _name in target.declaration_index)
    extension_catalogs = tuple(sorted(catalog_kinds - COMMON_CATALOG_KINDS))
    _require(
        extension_catalogs == ("pir.static-view-schema",),
        "the candidate does not expose exactly the static-view schema catalog",
    )
    findings.append(
        Finding(
            "promised-view-schema-catalog",
            "Affirmative",
            "F1R1C-A-SCHEMA-CATALOG",
            "the candidate manifest exposes the profile-owned static-view schema catalog",
        )
    )

    selectors = tuple(str(item["selector"]) for item in manifest["definitions"])
    selected_view_bodies = tuple(
        body
        for body in VIEW_BODIES
        if f"StaticViewSchema({body.removesuffix('Body')}) = {{" in selectors
    )
    _require(
        selected_view_bodies == VIEW_BODIES,
        "one or more owner-view schemas lacks an exact declaration selector",
    )
    findings.append(
        Finding(
            "view-schema-entry-routing",
            "Affirmative",
            "F1R1C-A-SCHEMA-ENTRY",
            "all six owner-view schemas have exact candidate declaration selectors",
        )
    )

    canonical_view_bodies = tuple(
        body
        for body in VIEW_BODIES
        if f"{body} = {{".encode("ascii") in static_fragment
        and b"StaticViewBody(view) =" in static_fragment
    )
    _require(
        canonical_view_bodies == VIEW_BODIES,
        "the generic canonical view-body compiler does not cover all six schemas",
    )
    findings.append(
        Finding(
            "canonical-view-body-grammar",
            "Affirmative",
            "F1R1C-A-VIEW-BODY",
            "the candidate authenticates all six complete bodies and their generic canonical compiler",
        )
    )

    coordinate_bodies = tuple(
        name
        for name in COORDINATE_BODY_GRAMMARS
        if f"{name}(".encode("ascii") in static_fragment
        or f"{name} =".encode("ascii") in static_fragment
    )
    _require(
        coordinate_bodies == COORDINATE_BODY_GRAMMARS,
        "one or more coordinate or read-manifest body grammars is absent",
    )
    findings.append(
        Finding(
            "atomic-coordinate-and-manifest-grammar",
            "Affirmative",
            "F1R1C-A-COORDINATE-BODY",
            "the candidate fixes coordinate, path, boundary, field, and manifest bodies",
        )
    )

    for field in LAW_FIELDS:
        _require(
            field.encode("ascii") in static_fragment,
            f"the inspected law field {field} is absent",
        )
    definitions = _definition_map(manifest)
    static_law = definitions[("pir.semantic-law", "static-view-issuance-v0")]
    _require(
        len(static_law["dependencies"]) == 6
        and all(item["kind"] == "pir.static-view-schema" for item in static_law["dependencies"]),
        "static-view issuance does not reach all six schema declarations",
    )
    selected_laws: dict[str, str] = {}
    for coordinate, declaration in LAW_FIELD_SELECTION.items():
        view, field = coordinate.split(".", 1)
        pattern = re.compile(
            rb"\(" + re.escape(view.encode("ascii")) + rb",\s*"
            + re.escape(field.encode("ascii")) + rb"\)\s*"
            + rb"->\s*the profile's pir\.semantic-law declaration\s*"
            + re.escape(declaration.encode("ascii")) + rb","
        )
        _require(
            pattern.search(static_fragment) is not None,
            f"the exact law-field selection is absent for {coordinate}",
        )
        selected = definitions.get(("pir.semantic-law", declaration))
        _require(
            selected is not None,
            f"the law-field selection names an absent declaration {declaration}",
        )
        schema = (
            "strategy-decision-view-v0"
            if view == "StrategyDecisionView"
            else "execution-view-v0"
        )
        _require(
            {
                "profile": "self",
                "kind": "pir.semantic-law",
                "name": declaration,
            }
            in definitions[("pir.static-view-schema", schema)]["dependencies"],
            f"the selected declaration is not a dependency of {schema}",
        )
        selected_laws[coordinate] = declaration
    _require(
        selected_laws == LAW_FIELD_SELECTION,
        "the exact law-field selection table is incomplete",
    )
    findings.append(
        Finding(
            "view-law-reference-map",
            "Affirmative",
            "F1R1C-A-LAW-MAP",
            "the five law-valued leaves select exact reachable semantic-law declarations",
        )
    )

    body_functions = _body_functions(static_fragment)
    _require(
        body_functions == EXPECTED_STATIC_FRAGMENT_BODY_FUNCTIONS,
        "the static-view fragment body-function inventory changed",
    )
    subjects = _subject_map(manifest)
    source_compilers = {
        kind: subjects[kind]["body_compiler"]["name"] for kind in SOURCE_SUBJECT_KINDS
    }
    _require(
        source_compilers == EXPECTED_SOURCE_COMPILERS,
        "the six source subjects do not use the migrated split compiler routes",
    )
    findings.append(
        Finding(
            "static-view-authority-envelope-bodies",
            "Affirmative",
            "F1R1C-A-AUTHORITY-BODIES",
            "the four authority-envelope bodies and two role bodies have distinct authenticated compiler routes",
        )
    )

    _require(
        target.profile_id != k2.PIR_INTERACTION_PROFILE_ID,
        "the K2 fixture profile unexpectedly equals the published target profile",
    )
    _require(
        hasattr(k2, "StaticViewField") and hasattr(k2, "PIRStaticViewAtomicCoordinate"),
        "the retained K2 view witness no longer has its documented shape",
    )
    _require(
        "path" not in k2.PIRStaticViewAtomicCoordinate.__dataclass_fields__,
        "the K2 fixture now carries the target nonempty path algebra",
    )
    findings.append(
        Finding(
            "fixture-view-substitution",
            "Refused",
            "F1R1C-R-FIXTURE-VIEW",
            "K2 uses a witness-local profile and top-level field coordinates, not the target atomic path schema",
        )
    )

    _require(
        b"PIRStaticViewReadManifestBody(x) =" in static_fragment
        and b"RequiredPIRViewReadClosure(view_coordinate, selected_fields) =" in static_fragment
        and b"manifest = RequiredPIRViewReadClosure(coordinate, manifest)" in static_fragment,
        "the exact read-manifest grammar or fixed-point closure law is absent",
    )
    findings.append(
        Finding(
            "exact-required-read-manifest",
            "Affirmative",
            "F1R1C-A-READ-MANIFEST",
            "the manifest body, atomic resolver, constructor closure, and exact fixed-point rule are authenticated",
        )
    )

    evidence = {
        "format": "zkc.formal-source-owner-views-f1r1c.audit.v0",
        "aggregate": {
            "outcome": "Affirmative",
            "code": "F1R1C-A-SOURCE-DETERMINACY",
        },
        "target_profile_digest": target.profile_id.digest.hex(),
        "view_bodies": list(VIEW_BODIES),
        "extension_catalogs": list(extension_catalogs),
        "selected_view_body_declarations": list(selected_view_bodies),
        "canonical_view_body_grammars": list(canonical_view_bodies),
        "coordinate_body_grammars": list(coordinate_bodies),
        "static_fragment_body_functions": list(body_functions),
        "law_field_selection": selected_laws,
        "static_view_schema_dependencies": {
            name: [
                f"{item['kind']}::{item['name']}"
                for item in definitions[("pir.static-view-schema", name)]["dependencies"]
            ]
            for name in (
                "public-binding-view-v0",
                "strategy-decision-view-v0",
                "public-coin-view-v0",
                "effect-view-v0",
                "claim-reduction-view-v0",
                "execution-view-v0",
            )
        },
        "source_subject_compilers": source_compilers,
        "exact_read_manifest": True,
        "retained_core_id": fixture.core_candidate.asserted_id.carrier(),
        "retained_protocol_id": fixture.protocol_candidate.asserted_id.carrier(),
    }
    return tuple(findings), evidence
