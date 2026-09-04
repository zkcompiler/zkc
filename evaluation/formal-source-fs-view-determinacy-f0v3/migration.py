"""Compose the proposed FS view catalogs over the common migration candidate."""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
from typing import Any

import proposal


ROOT = Path(__file__).resolve().parents[2]
MIGRATION_MODEL = ROOT / "evaluation/semantic-migration-candidate/model.py"


class MigrationError(RuntimeError):
    """The FS overlay or its independently compiled cone disagreed."""


def _load_migration() -> Any:
    name = "_zkc_f0v3b_semantic_migration"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, MIGRATION_MODEL)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError("cannot load the semantic migration candidate")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _dependency(profile: str, kind: str, name: str) -> dict[str, str]:
    return {"profile": profile, "kind": kind, "name": name}


def _definition(
    kind: str,
    name: str,
    fragment: str,
    selector: str,
    dependencies: list[dict[str, str]],
) -> dict[str, Any]:
    return {
        "kind": kind,
        "name": name,
        "revision": 0,
        "fragment": fragment,
        "selector": selector,
        "dependencies": dependencies,
    }


def _find_definition(manifest: dict[str, Any], kind: str, name: str) -> dict[str, Any]:
    found = [
        row
        for row in manifest["definitions"]
        if row["kind"] == kind and row["name"] == name
    ]
    if len(found) != 1:
        raise MigrationError(f"definition {kind}/{name} is not unique")
    return found[0]


def _append_page_source(
    migration: Any,
    candidate: Any,
    family: str,
    fragment: str,
    source: str,
) -> None:
    spec = proposal.FAMILIES[family]
    manifest = candidate.manifests[spec["profile_key"]]
    migration.b5.f0v._append_to_fragment(candidate.pages, manifest, fragment, source)
    page = str(manifest["owner_page"])
    candidate.inserted_sources.setdefault(page, tuple())
    candidate.inserted_sources[page] += (source,)


def _apply_manifest(candidate: Any, family: str) -> None:
    spec = proposal.FAMILIES[family]
    packet = proposal.read_packet(family)
    overlay = proposal.read_overlay(family)
    schema = packet["schema"]
    manifest = candidate.manifests[spec["profile_key"]]
    body_fragment = (
        "canonical-framed-fs-body-grammar"
        if family == "canonical-framed"
        else "duplex-sponge-fs-body-grammar"
    )
    semantics_fragment = (
        "canonical-framed-fs-semantics"
        if family == "canonical-framed"
        else "duplex-sponge-fs-semantics"
    )
    body_compiler = spec["body_compiler"]
    if any(
        row["kind"] == "pir.body-compiler" and row["name"] == body_compiler
        for row in manifest["definitions"]
    ):
        raise MigrationError(f"{family} static-view body compiler already exists")
    expected_additions = [
        _definition(
            "pir.body-compiler",
            body_compiler,
            body_fragment,
            spec["body_selector"],
            [
                _dependency(
                    "interaction", "pir.body-compiler", "static-view-body-v0"
                )
            ],
        )
    ]
    schema_refs: list[dict[str, str]] = []
    for view, (name, tag) in spec["views"].items():
        selector = (
            f"F0V3BStaticViewSchemaV0({name}) = "
            f"Owner({schema['views'][view]['owner_subject_kind']});"
            f"Tag({tag});Body({body_compiler})"
        )
        dependencies = [
            _dependency("self", "pir.body-compiler", body_compiler),
            _dependency("self", "pir.body-compiler", "source-binding-payload-body-v0"),
            _dependency(
                "self", "pir.body-compiler", "source-capability-requirement-body-v0"
            ),
            _dependency("self", "pir.body-compiler", "source-no-policy-body-v0"),
            _dependency(
                "self", "pir.body-compiler", "source-policy-closure-body-v0"
            ),
            _dependency(
                "interaction", "pir.semantic-law", "static-view-schema-resolution-v0"
            ),
        ]
        dependencies.extend(
            _dependency("self", "pir.semantic-law", law)
            for law in proposal.family_laws(schema, schema["views"][view]["schema"])
        )
        expected_additions.append(
            _definition(
                "pir.static-view-schema",
                name,
                semantics_fragment,
                selector,
                dependencies,
            )
        )
        schema_refs.append(_dependency("self", "pir.static-view-schema", name))
    if overlay["definition_additions"] != expected_additions:
        raise MigrationError(f"{family} manifest definitions differ from proposal")
    expected_dependency_additions = [
        {
            "consumer": {
                "kind": "pir.semantic-law",
                "name": spec["source_law"],
            },
            "dependencies": schema_refs,
        }
    ]
    if overlay["dependency_additions"] != expected_dependency_additions:
        raise MigrationError(f"{family} law dependencies differ from proposal")
    manifest["supported_subject_kinds"] = sorted(
        set(manifest["supported_subject_kinds"])
        | set(overlay["supported_subject_kinds_add"])
    )
    manifest["definitions"].extend(copy.deepcopy(expected_additions))
    source_law = _find_definition(
        manifest, "pir.semantic-law", spec["source_law"]
    )
    for reference in schema_refs:
        if reference not in source_law["dependencies"]:
            source_law["dependencies"].append(reference)


def build_fs_view_candidate() -> Any:
    """Return the common candidate plus both proposed family-local catalogs."""

    migration = _load_migration()
    candidate = migration.build_candidate()
    for family in proposal.FAMILIES:
        packet = proposal.read_packet(family)
        _apply_manifest(candidate, family)
        semantics_fragment = (
            "canonical-framed-fs-semantics"
            if family == "canonical-framed"
            else "duplex-sponge-fs-semantics"
        )
        body_fragment = (
            "canonical-framed-fs-body-grammar"
            if family == "canonical-framed"
            else "duplex-sponge-fs-body-grammar"
        )
        _append_page_source(
            migration,
            candidate,
            family,
            semantics_fragment,
            packet["semantic_source"],
        )
        _append_page_source(
            migration,
            candidate,
            family,
            body_fragment,
            packet["body_source"],
        )
    return candidate


def _changed_profiles(before: dict[str, Any], after: dict[str, Any]) -> list[str]:
    return [
        key
        for key in before["profiles"]
        if before["profiles"][key] != after["profiles"][key]
    ]


def measure() -> dict[str, Any]:
    """Compile both publication paths and return the total and incremental cone."""

    migration = _load_migration()
    baseline = migration.baseline_pair()
    common_candidate = migration.build_candidate()
    common = migration.compile_pair(common_candidate)
    candidate_override = build_fs_view_candidate()
    candidate = migration.compile_pair(candidate_override)
    for label, pair in (
        ("baseline", baseline),
        ("common", common),
        ("candidate", candidate),
    ):
        if pair.reference_table != pair.cold_table:
            raise MigrationError(f"publication compilers disagree for {label}")
    total_report = migration.rotation(baseline, candidate)
    incremental_report = migration.rotation(common, candidate)
    total_reference = total_report["rotated"]
    total_cold = _changed_profiles(baseline.cold_table, candidate.cold_table)
    incremental_reference = incremental_report["rotated"]
    incremental_cold = _changed_profiles(common.cold_table, candidate.cold_table)
    if total_reference != total_cold or incremental_reference != incremental_cold:
        raise MigrationError("publication compilers report different rotation cones")
    return {
        "baseline_compiler_agreement": True,
        "common_compiler_agreement": True,
        "candidate_compiler_agreement": True,
        "total_rotation": total_reference,
        "total_stable": total_report["stable"],
        "incremental_fs_rotation": incremental_reference,
        "incremental_fs_stable": incremental_report["stable"],
        "candidate_profiles": {
            key: {
                "revision": row["revision"],
                "profile_digest": row["profile_digest"],
                "body_sha256": row["body_sha256"],
            }
            for key, row in candidate.reference_table["profiles"].items()
        },
        "exact_changes": migration.exact_change_record(candidate_override),
        "published_identity_file_written": False,
    }
