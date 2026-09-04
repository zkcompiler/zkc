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
    "PIRStaticViewOwnerCoordinateBody",
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
    "PIRSourceConsumerRoleBody",
    "PIRSourcePurposeRoleBody",
)


class AuditError(RuntimeError):
    """The repository no longer exhibits the frozen F1-R1C boundary."""


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
        == published["profiles"]["interaction"],
        "the reconstructed Interaction profile differs from the frozen row",
    )
    findings.append(
        Finding(
            "published-profile-frozen-control",
            "Affirmative",
            "F1R1C-A-FROZEN-PROFILE",
            "the independently reconstructed profile matches the frozen v0 row",
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
        not extension_catalogs,
        "the target now publishes an extension catalog; refresh the R1C audit",
    )
    findings.append(
        Finding(
            "promised-view-schema-catalog",
            "CannotAnswer",
            "F1R1C-C-SCHEMA-CATALOG",
            "the source promises a profile-owned view-schema catalog, but the published profile has no extension catalog",
        )
    )

    selectors = tuple(str(item["selector"]) for item in manifest["definitions"])
    selected_view_bodies = tuple(
        body for body in VIEW_BODIES if any(body in selector for selector in selectors)
    )
    _require(
        not selected_view_bodies,
        "one or more view schemas now have declaration selectors; refresh the audit",
    )
    findings.append(
        Finding(
            "view-schema-entry-routing",
            "CannotAnswer",
            "F1R1C-C-SCHEMA-ENTRY",
            "none of the six view schemas has a published declaration entry or selector",
        )
    )

    body_grammar = target.source_fragments["interaction-body-grammar"]
    canonical_view_bodies = tuple(
        body for body in VIEW_BODIES if f"{body}(x) = R".encode("ascii") in body_grammar
    )
    _require(
        not canonical_view_bodies,
        "canonical view-body grammars now exist; refresh the audit",
    )
    findings.append(
        Finding(
            "canonical-view-body-grammar",
            "CannotAnswer",
            "F1R1C-C-VIEW-BODY",
            "the six displayed record shapes have no exact canonical body grammar",
        )
    )

    coordinate_bodies = tuple(
        name
        for name in COORDINATE_BODY_GRAMMARS
        if f"{name}(".encode("ascii") in static_fragment
        or f"{name}(".encode("ascii") in body_grammar
    )
    _require(
        not coordinate_bodies,
        "static-view coordinate body grammars now exist; refresh the audit",
    )
    findings.append(
        Finding(
            "atomic-coordinate-and-manifest-grammar",
            "CannotAnswer",
            "F1R1C-C-COORDINATE-BODY",
            "paths and boundaries are described abstractly but lack exact body compilers for payload commitment",
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
        static_law["dependencies"] == [],
        "static-view issuance now declares dependencies; refresh the audit",
    )
    _require(
        b"PIRStaticViewLawBindings" not in static_fragment,
        "an explicit law-field mapping now exists; refresh the audit",
    )
    findings.append(
        Finding(
            "view-law-reference-map",
            "CannotAnswer",
            "F1R1C-C-LAW-MAP",
            "five law-valued fields have no explicit field-to-declaration map in the source or manifest",
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
        set(source_compilers.values()) == {"source-authority-envelope-body-v0"},
        "source-envelope compiler routing changed; refresh the audit",
    )
    findings.append(
        Finding(
            "static-view-authority-envelope-bodies",
            "CannotAnswer",
            "F1R1C-C-AUTHORITY-BODIES",
            "four static-view payload/requirement/no-policy/closure grammars are absent behind the shared compiler route",
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

    findings.append(
        Finding(
            "exact-required-read-manifest",
            "CannotAnswer",
            "F1R1C-C-READ-MANIFEST",
            "without the exact field resolver and constructor closure table, no target manifest can be formed without guessing",
        )
    )

    evidence = {
        "format": "zkc.formal-source-owner-views-f1r1c.audit.v0",
        "aggregate": {
            "outcome": "CannotAnswer",
            "code": "F1R1C-C-SOURCE-DETERMINACY",
        },
        "target_profile_digest": target.profile_id.digest.hex(),
        "view_bodies": list(VIEW_BODIES),
        "extension_catalogs": list(extension_catalogs),
        "selected_view_body_declarations": list(selected_view_bodies),
        "canonical_view_body_grammars": list(canonical_view_bodies),
        "coordinate_body_grammars": list(coordinate_bodies),
        "static_fragment_body_functions": list(body_functions),
        "law_fields_without_explicit_map": list(LAW_FIELDS),
        "source_subject_compilers": source_compilers,
        "retained_core_id": fixture.core_candidate.asserted_id.carrier(),
        "retained_protocol_id": fixture.protocol_candidate.asserted_id.carrier(),
    }
    return tuple(findings), evidence
