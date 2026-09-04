#!/usr/bin/env python3
"""Audit the migrated FS-family owner views without publishing identities."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any, Callable

import cold_projection
import independent
import model
import typed_projection
from support import law


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"
AUDIT = HERE / "field-audit.json"
SCHEMA = HERE / "schema-source.json"
CANONICAL_PAGE = ROOT / "docs-next/pir/fiat-shamir.md"
DUPLEX_PAGE = ROOT / "docs-next/pir/duplex-sponge-fiat-shamir.md"
CANONICAL_MANIFEST = ROOT / "docs-next/pir/profiles/canonical-framed-fiat-shamir.json"
DUPLEX_MANIFEST = ROOT / "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json"
INTERACTION_MANIFEST = ROOT / "docs-next/pir/profiles/interaction.json"
PUBLISHED_IDENTITIES = ROOT / "docs-next/pir/profiles/published-identities.json"
BASELINE_IDENTITIES = (
    ROOT
    / "evaluation/formal-source-owner-view-repair-f0v/baseline-identities.json"
)
PUBLICATION_MODEL = ROOT / "evaluation/semantic-profile-publication/reference_model.py"
COLD_PUBLICATION_MODEL = ROOT / "evaluation/semantic-profile-publication/independent.py"
K2_MODEL = ROOT / "evaluation/k2-protocol-fiat-shamir/reference_model.py"
DUPLEX_MODEL = ROOT / "evaluation/duplex-sponge-transcript/duplexmodel/construction.py"
DUPLEX_CASE = ROOT / "evaluation/duplex-sponge-transcript/cases/construction.json"


class AuditFailure(RuntimeError):
    """The current source inventory or executable grammar drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AuditFailure(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise AuditFailure(f"cannot read {path.relative_to(ROOT)}") from error


def _json(path: Path) -> Any:
    try:
        return json.loads(_read(path))
    except json.JSONDecodeError as error:
        raise AuditFailure(f"cannot decode {path.relative_to(ROOT)}") from error


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise AuditFailure(f"cannot hash {path.relative_to(ROOT)}") from error


def _record_fields(lines: list[str], selector: str) -> tuple[int, list[str]]:
    matches = [index for index, line in enumerate(lines) if selector in line]
    if len(matches) != 1:
        raise AuditFailure(f"owner selector {selector!r} is not unique")
    start = matches[0]
    depth = lines[start].count("{") - lines[start].count("}")
    fields: list[str] = []
    for line in lines[start + 1 :]:
        if depth == 1:
            match = re.match(r"\s{2}([a-z][a-z0-9_]*):", line)
            if match is not None:
                fields.append(match.group(1))
        depth += line.count("{") - line.count("}")
        if depth == 0:
            break
    if depth != 0 or not fields:
        raise AuditFailure(f"owner body {selector!r} is not one closed record")
    return start + 1, fields


def _field_inventory() -> tuple[dict[str, Any], dict[str, int]]:
    audit = _json(AUDIT)
    if type(audit) is not dict or set(audit) != {"format", "views"}:
        raise AuditFailure("field audit has another outer shape")
    if audit["format"] != "zkc.formal-source-fs-view-determinacy-f0v3.field-audit.v1":
        raise AuditFailure("field audit format drifted")
    expected_views = model.load_source()["view_order"]
    if tuple(audit["views"]) != tuple(expected_views):
        raise AuditFailure("field-audit view order differs from the current grammar")
    page_lines = {
        "docs-next/pir/fiat-shamir.md": _read(CANONICAL_PAGE).splitlines(),
        "docs-next/pir/duplex-sponge-fiat-shamir.md": _read(DUPLEX_PAGE).splitlines(),
    }
    counts: dict[str, int] = {}
    for view, entry in audit["views"].items():
        if type(entry) is not dict or set(entry) != {
            "file",
            "section",
            "body_selector",
            "body_line",
            "fields",
        }:
            raise AuditFailure(f"{view} audit entry has another shape")
        lines = page_lines.get(entry["file"])
        if lines is None:
            raise AuditFailure(f"{view} cites a non-family owner page")
        line, observed = _record_fields(lines, entry["body_selector"])
        if line != entry["body_line"] or observed != entry["fields"]:
            raise AuditFailure(f"{view} no longer has its exact transcribed field body")
        counts[view] = len(observed)
    if sum(counts.values()) != 91:
        raise AuditFailure("the migrated eight-view census is not 91 top-level fields")
    return audit, counts


def _static_definitions(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        row
        for row in manifest["definitions"]
        if row["kind"] == "pir.static-view-schema"
    ]


def _law_field_selections(
    canonical_manifest: dict[str, Any], duplex_manifest: dict[str, Any]
) -> dict[str, Any]:
    expected = {
        "canonical-framed": {
            ("TranscriptDeclarationView", "initialization_schedule_law"): (
                "canonical-framed",
                "canonical-framed-body-grammar-v0",
            ),
            ("TranscriptDeclarationView", "frame_body_law"): (
                "canonical-framed",
                "canonical-framed-body-grammar-v0",
            ),
            ("RequiredInfluenceView", "exact_prefix_law"): (
                "canonical-framed",
                "canonical-framed-prefix-and-domain-v0",
            ),
            ("ChallengeTransitionView", "namespace_derivation_law"): (
                "canonical-framed",
                "canonical-framed-prefix-and-domain-v0",
            ),
            ("ChallengeTransitionView", "exact_length_law"): (
                "canonical-framed",
                "canonical-framed-body-grammar-v0",
            ),
            ("ChallengeTransitionView", "state_update_before_decode_law"): (
                "canonical-framed",
                "canonical-framed-admission-and-execution-v0",
            ),
            ("ChallengeTransitionView", "retry_law"): (
                "canonical-framed",
                "canonical-framed-admission-and-execution-v0",
            ),
            ("ChallengeTransitionView", "sampling_failure_law"): (
                "canonical-framed",
                "canonical-framed-admission-and-execution-v0",
            ),
            ("FSConstructionView", "structural_conclusion.law"): (
                "canonical-framed",
                "canonical-framed-same-core-construction-v0",
            ),
            ("ExecutionView", "visible_history_law"): (
                "interaction",
                "visible-history-v0",
            ),
            ("ExecutionView", "generated_execution_law"): (
                "canonical-framed",
                "canonical-framed-protocol-execution-v0",
            ),
            ("ExecutionView", "replay_qualification_law"): (
                "canonical-framed",
                "canonical-framed-replay-v0",
            ),
            ("ExecutionView", "relation_run_view_issuance_law"): (
                "interaction",
                "run-view-issuance-v0",
            ),
        },
        "duplex-sponge": {
            ("DuplexTranscriptDeclarationView", "state_carrier.invariant_law"): (
                "duplex-sponge",
                "duplex-sponge-state-transition-v0",
            ),
            (
                "DuplexTranscriptDeclarationView",
                "instance_carrier.bit_convention_law",
            ): ("duplex-sponge", "duplex-sponge-body-grammar-v0"),
            (
                "DuplexTranscriptDeclarationView",
                "instance_binding_projection.law",
            ): ("duplex-sponge", "duplex-sponge-source-views-v0"),
            (
                "DuplexTranscriptDeclarationView",
                "fixed_start_absorb_squeeze_law",
            ): ("duplex-sponge", "duplex-sponge-state-transition-v0"),
            ("DuplexTranscriptDeclarationView", "edge_case_law"): (
                "duplex-sponge",
                "duplex-sponge-state-transition-v0",
            ),
            (
                "DuplexEncodedInputCoverageView",
                "prover_required_prefix_law",
            ): ("duplex-sponge", "duplex-sponge-prover-required-prefix-v0"),
            (
                "DuplexEncodedInputCoverageView",
                "verifier_complete_schedule_law",
            ): ("duplex-sponge", "duplex-sponge-state-transition-v0"),
            ("DuplexChallengeTransitionView", "decoder_totality_law"): (
                "duplex-sponge",
                "duplex-sponge-admission-and-execution-v0",
            ),
            (
                "DuplexChallengeTransitionView",
                "decode_after_state_transition_law",
            ): ("duplex-sponge", "duplex-sponge-state-transition-v0"),
            (
                "DuplexFSConstructionView",
                "prover_schedule_correspondence.law",
            ): ("duplex-sponge", "duplex-sponge-downstream-boundary-v0"),
            (
                "DuplexFSConstructionView",
                "verifier_schedule_correspondence.law",
            ): ("duplex-sponge", "duplex-sponge-downstream-boundary-v0"),
            ("DuplexFSConstructionView", "instance_projection.law"): (
                "duplex-sponge",
                "duplex-sponge-same-core-construction-v0",
            ),
            ("DuplexFSConstructionView", "structural_conclusion.law"): (
                "duplex-sponge",
                "duplex-sponge-admission-and-execution-v0",
            ),
            ("ExecutionView", "visible_history_law"): (
                "interaction",
                "visible-history-v0",
            ),
            ("ExecutionView", "generated_execution_law"): (
                "duplex-sponge",
                "duplex-sponge-protocol-execution-v0",
            ),
            ("ExecutionView", "replay_qualification_law"): (
                "duplex-sponge",
                "duplex-sponge-replay-v0",
            ),
            ("ExecutionView", "relation_run_view_issuance_law"): (
                "interaction",
                "run-view-issuance-v0",
            ),
        },
    }
    pages = {
        "canonical-framed": (
            _read(CANONICAL_PAGE),
            "PIRStaticViewLawFieldSelection(CanonicalFramedFiatShamir)",
        ),
        "duplex-sponge": (
            _read(DUPLEX_PAGE),
            "PIRStaticViewLawFieldSelection(DuplexSpongeFiatShamir)",
        ),
    }
    manifests = {
        "canonical-framed": canonical_manifest,
        "duplex-sponge": duplex_manifest,
        "interaction": _json(INTERACTION_MANIFEST),
    }
    static_names = {
        "canonical-framed": {
            "TranscriptDeclarationView": "transcript-declaration-view-v0",
            "RequiredInfluenceView": "required-influence-view-v0",
            "ChallengeTransitionView": "challenge-transition-view-v0",
            "FSConstructionView": "fs-construction-view-v0",
            "ExecutionView": "execution-view-v0",
        },
        "duplex-sponge": {
            "DuplexTranscriptDeclarationView": "duplex-transcript-declaration-view-v0",
            "DuplexEncodedInputCoverageView": "duplex-encoded-input-coverage-view-v0",
            "DuplexChallengeTransitionView": "duplex-challenge-transition-view-v0",
            "DuplexFSConstructionView": "duplex-fs-construction-view-v0",
            "ExecutionView": "execution-view-v0",
        },
    }
    catalogs = {
        family: {
            row["name"]
            for row in manifest["definitions"]
            if row["kind"] == "pir.semantic-law"
        }
        for family, manifest in manifests.items()
    }
    evidence: dict[str, Any] = {}
    pattern = re.compile(
        r"\(\s*([A-Za-z][A-Za-z0-9]*),\s*([a-z][a-z0-9_.]*)\s*\)"
        r"\s*->\s*(?:(interaction)\s+)?([a-z0-9-]+)(?:,\s*imported)?"
    )
    for family, (page, selector) in pages.items():
        marker = selector + " = CanonicalMap ["
        if page.count(marker) != 1:
            raise AuditFailure(f"{family} law-field selection is not unique")
        block = page.split(marker, 1)[1].split("\n]\n```", 1)[0]
        observed: dict[tuple[str, str], tuple[str, str]] = {}
        for view, field, imported, law_name in pattern.findall(block):
            key = (view, field)
            if key in observed:
                raise AuditFailure(f"{family} repeats law-field coordinate {key}")
            observed[key] = ("interaction" if imported else family, law_name)
        if observed != expected[family]:
            raise AuditFailure(f"{family} law-field selection differs")
        static_by_name = {
            row["name"]: row for row in _static_definitions(manifests[family])
        }
        for (view, _field), (law_profile, law_name) in observed.items():
            if law_name not in catalogs[law_profile]:
                raise AuditFailure(
                    f"{family}/{view} selects an undeclared {law_profile} law"
                )
            if law_profile == "interaction":
                dependencies = {
                    (row["profile"], row["kind"], row["name"])
                    for row in static_by_name[static_names[family][view]]["dependencies"]
                }
                if ("interaction", "pir.semantic-law", law_name) not in dependencies:
                    raise AuditFailure(
                        f"{family}/{view} omits imported law {law_name}"
                    )
        encoded = [
            [view, field, law_profile, law_name]
            for (view, field), (law_profile, law_name) in sorted(observed.items())
        ]
        evidence[family] = {
            "entries": len(encoded),
            "sha256": hashlib.sha256(
                json.dumps(encoded, separators=(",", ":")).encode("ascii")
            ).hexdigest(),
        }
    newly_selected = {
        "canonical-framed-protocol-execution-v0",
        "canonical-framed-replay-v0",
        "duplex-sponge-prover-required-prefix-v0",
        "duplex-sponge-same-core-construction-v0",
        "duplex-sponge-protocol-execution-v0",
        "duplex-sponge-replay-v0",
    }
    selected_local = {
        law_name
        for selection in expected.values()
        for law_profile, law_name in selection.values()
        if law_profile != "interaction"
    }
    if not newly_selected <= selected_local:
        raise AuditFailure("the six added family law declarations are not all selected")
    evidence["selected_added_declarations"] = sorted(newly_selected)
    return evidence


def _profile_inventory(source: dict[str, Any]) -> dict[str, Any]:
    reference = _load("_zkc_f0v3_publication", PUBLICATION_MODEL)
    cold = _load("_zkc_f0v3_cold_publication", COLD_PUBLICATION_MODEL)
    reference_table = reference.identity_table(reference.compile_repository())
    cold_table = cold.identity_table(cold.compile_repository())
    if reference_table != cold_table:
        raise AuditFailure("the two publication compilers disagree on current manifests")

    baseline = _json(BASELINE_IDENTITIES)
    published = _json(PUBLISHED_IDENTITIES)
    if set(reference_table["profiles"]) != set(baseline["profiles"]):
        raise AuditFailure("current and pre-migration identity pins have another key set")
    rotated = [
        key
        for key, row in reference_table["profiles"].items()
        if row["profile_digest"] != baseline["profiles"][key]
    ]
    stable = [key for key in reference_table["profiles"] if key not in rotated]
    if len(rotated) != 17 or stable != ["analysis-kernel"]:
        raise AuditFailure("the rehearsal identity rotation is not the expected 17/1 split")
    if not set(published["profiles"]) < set(reference_table["profiles"]):
        raise AuditFailure("the legacy published table is not a strict profile subset")
    if any(
        published["profiles"][key]["profile_digest"]
        == reference_table["profiles"][key]["profile_digest"]
        for key in published["profiles"]
    ):
        raise AuditFailure("one legacy published profile was accepted as current")

    families = {
        "canonical-framed": (
            "canonical-framed-fiat-shamir",
            CANONICAL_MANIFEST,
            CANONICAL_PAGE,
            {
                "transcript-declaration-view-v0",
                "required-influence-view-v0",
                "challenge-transition-view-v0",
                "fs-construction-view-v0",
                "execution-view-v0",
            },
        ),
        "duplex-sponge": (
            "duplex-sponge-fiat-shamir",
            DUPLEX_MANIFEST,
            DUPLEX_PAGE,
            {
                "duplex-transcript-declaration-view-v0",
                "duplex-encoded-input-coverage-view-v0",
                "duplex-challenge-transition-view-v0",
                "duplex-fs-construction-view-v0",
                "execution-view-v0",
            },
        ),
    }
    family_evidence: dict[str, Any] = {}
    for family, (profile_key, path, page, expected_names) in families.items():
        manifest = _json(path)
        row = reference_table["profiles"][profile_key]
        pin = source["owner_profiles"][family]
        if pin != {
            "key": family,
            "revision": row["revision"],
            "profile_digest": row["profile_digest"],
            "profile_body_sha256": row["body_sha256"],
        }:
            raise AuditFailure(f"{family} direct profile pin differs")
        definitions = _static_definitions(manifest)
        if {item["name"] for item in definitions} != expected_names:
            raise AuditFailure(f"{family} static-view catalog differs")
        page_text = _read(page)
        for definition in definitions:
            if page_text.count(definition["selector"]) != 1:
                raise AuditFailure(
                    f"{family}/{definition['name']} selector is not unique in its owner page"
                )
            dependencies = {
                (item["profile"], item["kind"], item["name"])
                for item in definition["dependencies"]
            }
            if (
                "interaction",
                "pir.body-compiler",
                "static-view-body-v0",
            ) not in dependencies:
                raise AuditFailure(f"{family}/{definition['name']} omits the body compiler")
        family_evidence[family] = {
            "manifest_revision": manifest["revision"],
            "profile_digest": row["profile_digest"],
            "profile_body_sha256": row["body_sha256"],
            "static_view_schemas": sorted(expected_names),
        }
    return {
        "compiler_agreement": True,
        "families": family_evidence,
        "law_field_selections": _law_field_selections(
            _json(CANONICAL_MANIFEST), _json(DUPLEX_MANIFEST)
        ),
        "rotated_profiles": rotated,
        "stable_profiles": stable,
        "published_identity_sha256": _sha256(PUBLISHED_IDENTITIES),
    }


def _rejected(action: Callable[[], Any], errors: tuple[type[BaseException], ...]) -> bool:
    try:
        action()
    except errors:
        return True
    return False


def _mutations(
    source: dict[str, Any],
    schemas: dict[str, Any],
    cold_schemas: dict[str, Any],
    sample_value: dict[str, Any],
    sample_result: dict[str, Any],
) -> dict[str, bool]:
    duplicate_ordinal = copy.deepcopy(source)
    duplicate_ordinal["definitions"]["CanonicalFrameCoordinate"]["record"][1][0] = 0
    owner_substitution = copy.deepcopy(source)
    owner_substitution["views"]["CanonicalTranscriptDeclarationView"][
        "owner_subject_kind"
    ] = "pir.protocol"
    law_substitution = copy.deepcopy(sample_value)
    law_substitution[2] = law("canonical-framed", "canonical-framed-source-views-v0")
    compiler_substitution = copy.deepcopy(sample_value)
    compiler_substitution[0]["compiler"] = "core-id-body-v0"
    result_conclusion_bytes = copy.deepcopy(sample_result)
    result_conclusion_bytes[-1] = b"owner-local-result-ref"
    profiles = source["owner_profiles"]
    return {
        "recursive-schema-ordinal": _rejected(
            lambda: model.compile_source(duplicate_ordinal), (model.SchemaError,)
        ),
        "iterative-schema-ordinal": _rejected(
            lambda: independent.compile_source(duplicate_ordinal),
            (independent.IndependentError,),
        ),
        "recursive-owner-substitution": _rejected(
            lambda: model.compile_source(owner_substitution), (model.SchemaError,)
        ),
        "iterative-owner-substitution": _rejected(
            lambda: independent.compile_source(owner_substitution),
            (independent.IndependentError,),
        ),
        "recursive-law-substitution": _rejected(
            lambda: model.validate(
                schemas["CanonicalChallengeTransitionView"], law_substitution, profiles
            ),
            (model.SchemaError,),
        ),
        "iterative-law-substitution": _rejected(
            lambda: independent.validate(
                cold_schemas["CanonicalChallengeTransitionView"],
                law_substitution,
                profiles,
            ),
            (independent.IndependentError,),
        ),
        "recursive-compiler-substitution": _rejected(
            lambda: model.validate(
                schemas["CanonicalChallengeTransitionView"], compiler_substitution, profiles
            ),
            (model.SchemaError,),
        ),
        "iterative-compiler-substitution": _rejected(
            lambda: independent.validate(
                cold_schemas["CanonicalChallengeTransitionView"], compiler_substitution, profiles
            ),
            (independent.IndependentError,),
        ),
        "recursive-wrong-family-view-kind": _rejected(
            lambda: model.validate_view(
                "duplex-sponge",
                "CanonicalChallengeTransitionView",
                schemas,
                sample_value,
                profiles,
            ),
            (model.SchemaError,),
        ),
        "iterative-wrong-family-view-kind": _rejected(
            lambda: independent.validate_view(
                "duplex-sponge",
                "CanonicalChallengeTransitionView",
                cold_schemas,
                sample_value,
                profiles,
            ),
            (independent.IndependentError,),
        ),
        "recursive-result-conclusion-bytes": _rejected(
            lambda: model.validate_view(
                "canonical-framed",
                "CanonicalFSConstructionView",
                schemas,
                result_conclusion_bytes,
                profiles,
            ),
            (model.SchemaError,),
        ),
        "iterative-result-conclusion-bytes": _rejected(
            lambda: independent.validate_view(
                "canonical-framed",
                "CanonicalFSConstructionView",
                cold_schemas,
                result_conclusion_bytes,
                profiles,
            ),
            (independent.IndependentError,),
        ),
    }


def _findings() -> list[Finding]:
    return [
        Finding(
            "direct-fs-family-source-pins",
            "Affirmative",
            "F0V3-A-FS-SOURCE-PINS",
            "both direct manifests compile to the pinned rehearsal identities",
        ),
        Finding(
            "current-eight-view-field-census",
            "Affirmative",
            "F0V3-A-EIGHT-VIEW-CENSUS",
            "all 91 migrated top-level fields are transcribed from exact owner bodies",
        ),
        Finding(
            "published-static-view-schema-catalogs",
            "Affirmative",
            "F0V3-A-PUBLISHED-SCHEMAS",
            "both direct manifests declare five family-local static-view schemas",
        ),
        Finding(
            "family-law-field-selections",
            "Affirmative",
            "F0V3-A-LAW-FIELD-SELECTIONS",
            "both owner tables select declared laws and every imported law is a manifest dependency",
        ),
        Finding(
            "current-finite-view-grammar",
            "Affirmative",
            "F0V3-A-CURRENT-VIEW-GRAMMAR",
            "the eight migrated construction/result bodies compile in the finite grammar",
        ),
        Finding(
            "recursive-iterative-schema-agreement",
            "Affirmative",
            "F0V3-A-DUAL-SCHEMA-COMPILERS",
            "recursive and iterative compilers produce equal expanded schemas",
        ),
        Finding(
            "k2-typed-cold-current-values",
            "Affirmative",
            "F0V3-A-K2-TYPED-COLD-BYTES",
            "typed and cold paths byte-agree on all four canonical-framed views for both carriers",
        ),
        Finding(
            "duplex-typed-cold-current-values",
            "Affirmative",
            "F0V3-A-DUPLEX-TYPED-COLD-BYTES",
            "typed and cold paths byte-agree on three construction-owned duplex views",
        ),
        Finding(
            "checked-duplex-carrier-boundary",
            "Affirmative",
            "F0V3-A-DUPLEX-CARRIER-BOUNDARY",
            "the duplex witness exposes no checked result, so no result value is claimed",
        ),
        Finding(
            "schema-law-owner-mutation-kills",
            "Affirmative",
            "F0V3-A-MUTATION-KILLS",
            "both paths reject schema, law, compiler, owner, family, and result-shape substitutions",
        ),
        Finding(
            "rehearsal-identity-rotation-control",
            "Affirmative",
            "F0V3-A-ROTATION-CONTROL",
            "both publication compilers reproduce the direct 17-profile migration cone without writing identities",
        ),
        Finding(
            "unframed-challenge-position",
            "Affirmative",
            "F0V3-A-TOTAL-SCHEDULE-CHALLENGE-POSITION",
            "every challenge rule names its occurrence's total Core schedule position independently of whether Section 4 emits a frame entry",
        ),
        Finding(
            "witness-as-owner-definition",
            "Refused",
            "F0V3-R-WITNESS-SUBSTITUTION",
            "a witness-local value cannot replace a PIR owner body",
        ),
        Finding(
            "interaction-body-by-label-substitution",
            "Refused",
            "F0V3-R-INTERACTION-LABEL-SUBSTITUTION",
            "an Interaction body is not imported merely because a family field has a similar label",
        ),
    ]


def run_audit() -> dict[str, Any]:
    _audit, field_counts = _field_inventory()
    source = model.load_source()
    publication = _profile_inventory(source)
    schemas, owners, recursive_metrics = model.compile_source(source)
    cold_schemas, cold_owners, iterative_metrics = independent.compile_source(
        copy.deepcopy(source)
    )
    if len(schemas) != 8 or schemas != cold_schemas or owners != cold_owners:
        raise AuditFailure("recursive and iterative current-schema compilers disagree")

    projections: dict[str, dict[str, dict[str, Any]]] = {}
    unavailable: dict[str, list[str]] = {}
    first_transition: dict[str, Any] | None = None
    first_result: dict[str, Any] | None = None
    for name, raw, typed_values in typed_projection.k2_cases():
        cold_values = cold_projection.k2_values(
            json.loads(json.dumps(raw, sort_keys=True, separators=(",", ":")))
        )
        if tuple(typed_values) != tuple(cold_values):
            raise AuditFailure(f"typed and cold K2 {name} view catalogs differ")
        projections["k2-" + name] = {}
        for view, typed_value in typed_values.items():
            cold_value = cold_values[view]
            model.validate_view(
                "canonical-framed", view, schemas, typed_value, source["owner_profiles"]
            )
            independent.validate_view(
                "canonical-framed",
                view,
                cold_schemas,
                cold_value,
                source["owner_profiles"],
            )
            typed_bytes = model.wire(typed_value)
            cold_bytes = independent.wire(cold_value)
            if typed_bytes != cold_bytes:
                raise AuditFailure(f"typed and cold K2 {name}/{view} bytes differ")
            projections["k2-" + name][view] = {
                "body_sha256": hashlib.sha256(typed_bytes).hexdigest(),
                "body_bytes": len(typed_bytes),
                "typed_cold_byte_equal": True,
                "leaf_count": model.value_leaf_count(schemas[view], typed_value),
            }
        missing = sorted(
            {
                "CanonicalTranscriptDeclarationView",
                "CanonicalRequiredInfluenceView",
                "CanonicalChallengeTransitionView",
                "CanonicalFSConstructionView",
            }
            - set(typed_values)
        )
        if missing:
            unavailable["k2-" + name] = missing
        if first_transition is None and "CanonicalChallengeTransitionView" in typed_values:
            first_transition = typed_values["CanonicalChallengeTransitionView"]
            first_result = typed_values["CanonicalFSConstructionView"]

    duplex_raw, duplex_typed = typed_projection.duplex_case()
    duplex_cold = cold_projection.duplex_values(
        json.loads(json.dumps(duplex_raw, sort_keys=True, separators=(",", ":")))
    )
    if tuple(duplex_typed) != tuple(duplex_cold):
        raise AuditFailure("typed and cold duplex view catalogs differ")
    if "CheckedDuplexFSConstruction" in _read(DUPLEX_MODEL):
        raise AuditFailure("duplex witness now appears to expose a checked-result carrier")
    projections["duplex-finite"] = {}
    for view, typed_value in duplex_typed.items():
        cold_value = duplex_cold[view]
        model.validate_view(
            "duplex-sponge", view, schemas, typed_value, source["owner_profiles"]
        )
        independent.validate_view(
            "duplex-sponge", view, cold_schemas, cold_value, source["owner_profiles"]
        )
        typed_bytes = model.wire(typed_value)
        cold_bytes = independent.wire(cold_value)
        if typed_bytes != cold_bytes:
            raise AuditFailure(f"typed and cold duplex {view} bytes differ")
        projections["duplex-finite"][view] = {
            "body_sha256": hashlib.sha256(typed_bytes).hexdigest(),
            "body_bytes": len(typed_bytes),
            "typed_cold_byte_equal": True,
            "leaf_count": model.value_leaf_count(schemas[view], typed_value),
        }

    if first_transition is None or first_result is None:
        raise AuditFailure("no canonical mutation samples were derived")
    mutation_kills = _mutations(
        source, schemas, cold_schemas, first_transition, first_result
    )
    if not all(mutation_kills.values()):
        raise AuditFailure("one schema, law, compiler, owner, or family mutation survived")

    schema_counts = {
        view: {
            "node_count": model.schema_counts(schema)[0],
            "leaf_count": model.schema_counts(schema)[1],
        }
        for view, schema in schemas.items()
    }
    source_paths = (
        CANONICAL_PAGE,
        DUPLEX_PAGE,
        CANONICAL_MANIFEST,
        DUPLEX_MANIFEST,
        INTERACTION_MANIFEST,
        PUBLISHED_IDENTITIES,
        BASELINE_IDENTITIES,
        K2_MODEL,
        DUPLEX_MODEL,
        DUPLEX_CASE,
        AUDIT,
        SCHEMA,
    )
    evidence_control = {
        "source_sha256": {
            str(path.relative_to(ROOT)): _sha256(path) for path in source_paths
        },
        "field_count": sum(field_counts.values()),
        "field_counts": field_counts,
        "profile_publication": publication,
        "current_schema_sha256": model.digest(schemas),
        "cold_current_schema_sha256": independent.digest(cold_schemas),
        "compiled_schema_count": len(schemas),
        "current_schema_counts": schema_counts,
        "recursive_metrics": recursive_metrics,
        "iterative_metrics": iterative_metrics,
        "current_values": projections,
        "underdetermined_values": unavailable,
        "mutation_kills": mutation_kills,
        "duplex_checked_result_witnessed": False,
    }
    findings = _findings()
    aggregate = {
        "outcome": "Affirmative",
        "code": "F0V3-A-MIGRATED-FS-VIEW-DETERMINACY",
    }
    projection = {
        "aggregate": aggregate,
        "evidence_control": evidence_control,
        "cases": [
            {"name": row.name, "outcome": row.outcome, "code": row.code}
            for row in findings
        ],
    }
    return {
        **projection,
        "details": [asdict(row) for row in findings],
        "nonclaims": [
            "publication or finalization of the rehearsed profile identities",
            "transfer of owner facts from a witness or Interaction by label",
            "a checked duplex result where the witness exposes none",
            "implementation conformance or production backend support",
            "Fiat-Shamir soundness, knowledge soundness, zero knowledge, ROM, or QROM security",
            "theorem correspondence, theorem applicability, or theorem truth",
        ],
    }


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditFailure("cannot read frozen FS-family findings") from error
    if type(value) is not dict:
        raise AuditFailure("frozen FS-family findings have another shape")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--refresh", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    try:
        report = run_audit()
        projection = {
            key: report[key] for key in ("aggregate", "evidence_control", "cases")
        }
        if args.refresh:
            EXPECTED.write_text(
                json.dumps(projection, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
        if args.check and projection != _load_expected():
            raise AuditFailure("current FS-family projection differs from frozen findings")
    except (
        AuditFailure,
        cold_projection.ColdProjectionError,
        independent.IndependentError,
        model.SchemaError,
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
    ) as error:
        print(f"FS-family audit failure: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
