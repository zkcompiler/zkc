#!/usr/bin/env python3
"""Audit FS-family view determinacy and test a bounded candidate grammar."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import sys
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
PUBLISHED_IDENTITIES = ROOT / "docs-next/pir/profiles/published-identities.json"
K2_MODEL = ROOT / "evaluation/k2-protocol-fiat-shamir/reference_model.py"
DUPLEX_MODEL = ROOT / "evaluation/duplex-sponge-transcript/duplexmodel/construction.py"
DUPLEX_CASE = ROOT / "evaluation/duplex-sponge-transcript/cases/construction.json"


class AuditFailure(RuntimeError):
    """The frozen source inventory or executable candidate drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


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


def _field_inventory() -> tuple[dict[str, Any], dict[str, int], dict[str, int]]:
    audit = _json(AUDIT)
    if type(audit) is not dict or set(audit) != {
        "format",
        "obligation_order",
        "obligations",
        "views",
    }:
        raise AuditFailure("field audit has another outer shape")
    if audit["format"] != "zkc.formal-source-fs-view-determinacy-f0v3.field-audit.v0":
        raise AuditFailure("field audit format drifted")
    if (
        type(audit["obligation_order"]) is not list
        or len(audit["obligation_order"]) != 11
        or len(set(audit["obligation_order"])) != 11
        or tuple(audit["obligations"]) != tuple(audit["obligation_order"])
    ):
        raise AuditFailure("owner-obligation catalog is malformed")
    expected_views = model.load_source()["view_order"]
    if tuple(audit["views"]) != tuple(expected_views):
        raise AuditFailure("field-audit view order differs from candidate grammar")
    page_lines = {
        "docs-next/pir/fiat-shamir.md": _read(CANONICAL_PAGE).splitlines(),
        "docs-next/pir/duplex-sponge-fiat-shamir.md": _read(DUPLEX_PAGE).splitlines(),
    }
    statuses = {"exact-body": 0, "prose-placeholder": 0, "undefined-symbol": 0}
    nodes = {"atomic": 0, "structural": 0}
    referenced_obligations: set[str] = set()
    seen_lines: set[tuple[str, int]] = set()
    total = 0
    for view, entry in audit["views"].items():
        if type(entry) is not dict or set(entry) != {
            "file",
            "section",
            "body_line",
            "fields",
        }:
            raise AuditFailure(f"{view} audit entry has another shape")
        lines = page_lines.get(entry["file"])
        if lines is None:
            raise AuditFailure(f"{view} cites a non-target owner page")
        body_line = entry["body_line"]
        if type(body_line) is not int or "ViewBody = {" not in lines[body_line - 1]:
            raise AuditFailure(f"{view} body line no longer selects a view display")
        previous = body_line
        for row in entry["fields"]:
            if type(row) is not list or len(row) != 5:
                raise AuditFailure(f"{view} field row is malformed")
            line, field, status, node, obligation = row
            if (
                type(line) is not int
                or line <= previous
                or (entry["file"], line) in seen_lines
                or type(field) is not str
                or field not in lines[line - 1]
            ):
                raise AuditFailure(f"{view}.{field} no longer selects one exact source line")
            previous = line
            seen_lines.add((entry["file"], line))
            if status not in statuses or node not in nodes:
                raise AuditFailure(f"{view}.{field} uses an unknown classification")
            if status == "exact-body":
                if obligation is not None:
                    raise AuditFailure(f"{view}.{field} gives an exact field an obligation")
            elif obligation not in audit["obligations"]:
                raise AuditFailure(f"{view}.{field} lacks an exact owner obligation")
            else:
                referenced_obligations.add(obligation)
            statuses[status] += 1
            nodes[node] += 1
            total += 1
    if total != 97 or statuses != {
        "exact-body": 37,
        "prose-placeholder": 40,
        "undefined-symbol": 20,
    } or nodes != {"atomic": 44, "structural": 53}:
        raise AuditFailure("the exact 97-field classification census drifted")
    if referenced_obligations != set(audit["obligation_order"]) - {
        "F0V3-O-PUBLISHED-SCHEMAS"
    }:
        raise AuditFailure("field rows do not close to the exact owner-obligation set")
    return audit, statuses, nodes


def _profile_inventory(source: dict[str, Any]) -> None:
    published = _json(PUBLISHED_IDENTITIES)["profiles"]
    manifests = {
        "canonical-framed": _json(CANONICAL_MANIFEST),
        "duplex-sponge": _json(DUPLEX_MANIFEST),
    }
    published_keys = {
        "canonical-framed": "canonical-framed-fiat-shamir",
        "duplex-sponge": "duplex-sponge-fiat-shamir",
    }
    for key, manifest in manifests.items():
        pin = source["owner_profiles"][key]
        identity = published[published_keys[key]]
        if pin["profile_digest"] != identity["profile_digest"]:
            raise AuditFailure(f"{key} profile digest pin differs")
        if pin["profile_body_sha256"] != identity["body_sha256"]:
            raise AuditFailure(f"{key} profile-body pin differs")
        serialized = json.dumps(manifest, sort_keys=True, separators=(",", ":"))
        if (
            "pir.static-view-schema" in manifest.get("supported_subject_kinds", [])
            or any(
                type(item) is dict and item.get("kind") == "pir.static-view-schema"
                for item in manifest.get("subjects", [])
            )
            or "pir.static-view-schema" in serialized
        ):
            raise AuditFailure(f"{key} now publishes a static-view schema")


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
) -> dict[str, bool]:
    duplicate_ordinal = copy.deepcopy(source)
    duplicate_ordinal["definitions"]["CanonicalFrameCoordinate"]["record"][1][0] = 0
    owner_substitution = copy.deepcopy(source)
    owner_substitution["views"]["CanonicalTranscriptDeclarationView"][
        "owner_subject_kind"
    ] = "pir.protocol"
    law_substitution = copy.deepcopy(sample_value)
    law_substitution[2] = law(
        "canonical-framed", "canonical-framed-source-views-v0"
    )
    compiler_substitution = copy.deepcopy(sample_value)
    compiler_substitution[0]["compiler"] = "core-id-body-v0"
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
                schemas["CanonicalChallengeTransitionView"],
                law_substitution,
                profiles,
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
                schemas["CanonicalChallengeTransitionView"],
                compiler_substitution,
                profiles,
            ),
            (model.SchemaError,),
        ),
        "iterative-compiler-substitution": _rejected(
            lambda: independent.validate(
                cold_schemas["CanonicalChallengeTransitionView"],
                compiler_substitution,
                profiles,
            ),
            (independent.IndependentError,),
        ),
    }


def _findings(audit: dict[str, Any]) -> list[Finding]:
    affirmative = [
        Finding(
            "authenticated-fs-family-source-pins",
            "Affirmative",
            "F0V3-A-FS-SOURCE-PINS",
            "both profile identities and all four displays per family are pinned",
        ),
        Finding(
            "eight-view-field-census",
            "Affirmative",
            "F0V3-A-EIGHT-VIEW-CENSUS",
            "all 97 displayed fields have one exact line and determinacy classification",
        ),
        Finding(
            "normalized-finite-view-grammar",
            "Affirmative",
            "F0V3-A-FS-VIEW-GRAMMAR-BOUNDED",
            "eight candidate bodies compile in the finite Atom/Record/Variant/Sequence universe",
        ),
        Finding(
            "recursive-iterative-schema-agreement",
            "Affirmative",
            "F0V3-A-DUAL-SCHEMA-COMPILERS",
            "recursive and iterative topological compilers produce equal expanded schemas",
        ),
        Finding(
            "k2-typed-cold-candidate-values",
            "Affirmative",
            "F0V3-A-K2-TYPED-COLD",
            "typed and cold paths agree on four candidate values for two checked K2 carriers",
        ),
        Finding(
            "duplex-typed-cold-candidate-values",
            "Affirmative",
            "F0V3-A-DUPLEX-TYPED-COLD",
            "typed and cold paths agree on three construction-owned duplex candidate values",
        ),
        Finding(
            "checked-duplex-carrier-boundary",
            "Affirmative",
            "F0V3-A-DUPLEX-CARRIER-BOUNDARY",
            "the duplex witness has no checked-result issuer, so no result value is claimed",
        ),
        Finding(
            "schema-law-owner-mutation-kills",
            "Affirmative",
            "F0V3-A-MUTATION-KILLS",
            "both paths reject schema ordinals, law atoms, body compilers, and owner substitutions",
        ),
    ]
    obligation_findings = {
        "F0V3-O-PUBLISHED-SCHEMAS": (
            "published-static-view-schema-catalog",
            "F0V3-C-PUBLISHED-SCHEMAS",
        ),
        "F0V3-O-CANONICAL-FRAME-SCHEDULE": (
            "canonical-frame-schedule-bodies",
            "F0V3-C-CANONICAL-FRAME-SCHEDULE",
        ),
        "F0V3-O-CANONICAL-INFLUENCE": (
            "canonical-influence-view-bodies",
            "F0V3-C-CANONICAL-INFLUENCE",
        ),
        "F0V3-O-CANONICAL-TRANSITION-ABI": (
            "canonical-transition-abi-bodies",
            "F0V3-C-CANONICAL-TRANSITION-ABI",
        ),
        "F0V3-O-CANONICAL-RESULT-BODY": (
            "canonical-checked-result-body",
            "F0V3-C-CANONICAL-RESULT-BODY",
        ),
        "F0V3-O-DUPLEX-STATE-INSTANCE": (
            "duplex-state-instance-bodies",
            "F0V3-C-DUPLEX-STATE-INSTANCE",
        ),
        "F0V3-O-DUPLEX-MATERIAL-SALT": (
            "duplex-material-salt-bodies",
            "F0V3-C-DUPLEX-MATERIAL-SALT",
        ),
        "F0V3-O-DUPLEX-CODEC-ARGUMENTS": (
            "duplex-codec-argument-bodies",
            "F0V3-C-DUPLEX-CODEC-ARGUMENTS",
        ),
        "F0V3-O-DUPLEX-SCHEDULE-COVERAGE": (
            "duplex-schedule-coverage-bodies",
            "F0V3-C-DUPLEX-SCHEDULE-COVERAGE",
        ),
        "F0V3-O-DUPLEX-TRANSITION-ABI": (
            "duplex-transition-abi-bodies",
            "F0V3-C-DUPLEX-TRANSITION-ABI",
        ),
        "F0V3-O-DUPLEX-RESULT-BODY": (
            "duplex-checked-result-body",
            "F0V3-C-DUPLEX-RESULT-BODY",
        ),
    }
    cannot_answer = [
        Finding(
            obligation_findings[key][0],
            "CannotAnswer",
            obligation_findings[key][1],
            audit["obligations"][key],
        )
        for key in audit["obligation_order"]
    ]
    refused = [
        Finding(
            "witness-as-owner-definition",
            "Refused",
            "F0V3-R-WITNESS-SUBSTITUTION",
            "a K2 or duplex witness-local value cannot fill a missing PIR owner body",
        ),
        Finding(
            "interaction-body-by-label-substitution",
            "Refused",
            "F0V3-R-INTERACTION-LABEL-SUBSTITUTION",
            "an Interaction body is not imported merely because an FS field has a similar label",
        ),
    ]
    return affirmative + cannot_answer + refused


def run_audit() -> dict[str, Any]:
    audit, statuses, node_classes = _field_inventory()
    source = model.load_source()
    _profile_inventory(source)
    schemas, owners, recursive_metrics = model.compile_source(source)
    cold_source = independent.load_source()
    cold_schemas, cold_owners, iterative_metrics = independent.compile_source(cold_source)
    if schemas != cold_schemas or owners != cold_owners:
        raise AuditFailure("recursive and iterative candidate compilers disagree")

    projections: dict[str, dict[str, dict[str, Any]]] = {}
    first_transition: dict[str, Any] | None = None
    for name, raw, typed_values in typed_projection.k2_cases():
        cold_values = cold_projection.k2_values(
            json.loads(json.dumps(raw, sort_keys=True, separators=(",", ":")))
        )
        if typed_values != cold_values:
            raise AuditFailure(f"typed and cold K2 {name} projections differ")
        projections["k2-" + name] = {}
        for view, value in typed_values.items():
            model.validate(schemas[view], value, source["owner_profiles"])
            independent.validate(cold_schemas[view], value, source["owner_profiles"])
            projections["k2-" + name][view] = {
                "body_sha256": model.digest(value),
                "leaf_count": model.value_leaf_count(schemas[view], value),
            }
        if first_transition is None:
            first_transition = typed_values["CanonicalChallengeTransitionView"]

    duplex_raw, duplex_typed = typed_projection.duplex_case()
    duplex_cold = cold_projection.duplex_values(
        json.loads(json.dumps(duplex_raw, sort_keys=True, separators=(",", ":")))
    )
    if duplex_typed != duplex_cold:
        raise AuditFailure("typed and cold duplex projections differ")
    if "CheckedDuplexFSConstruction" in _read(DUPLEX_MODEL):
        raise AuditFailure("duplex witness now appears to expose a checked-result carrier")
    projections["duplex-finite"] = {}
    for view, value in duplex_typed.items():
        model.validate(schemas[view], value, source["owner_profiles"])
        independent.validate(cold_schemas[view], value, source["owner_profiles"])
        projections["duplex-finite"][view] = {
            "body_sha256": model.digest(value),
            "leaf_count": model.value_leaf_count(schemas[view], value),
        }
    if first_transition is None:  # pragma: no cover - fixed K2 fixture set
        raise AuditFailure("no canonical transition sample was derived")
    mutation_kills = _mutations(
        source, schemas, cold_schemas, first_transition
    )
    if not all(mutation_kills.values()):
        raise AuditFailure("one schema, law, compiler, or owner mutation survived")

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
        PUBLISHED_IDENTITIES,
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
        "field_count": sum(statuses.values()),
        "field_status_counts": statuses,
        "field_node_counts": node_classes,
        "owner_obligations": audit["obligation_order"],
        "candidate_schema_sha256": model.digest(schemas),
        "candidate_schema_counts": schema_counts,
        "recursive_metrics": recursive_metrics,
        "iterative_metrics": iterative_metrics,
        "candidate_values": projections,
        "mutation_kills": mutation_kills,
        "duplex_checked_result_witnessed": False,
    }
    findings = _findings(audit)
    aggregate = {
        "outcome": "CannotAnswer",
        "code": "F0V3-C-FS-VIEW-DETERMINACY",
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
            "publication or adoption of any candidate body or schema",
            "determinacy of the current eight owner-view displays",
            "transfer of owner facts from K2, duplex, or Interaction by label",
            "implementation conformance or production backend support",
            "Fiat-Shamir soundness, knowledge soundness, zero knowledge, ROM, or QROM security",
            "theorem correspondence, theorem applicability, or theorem truth",
        ],
    }


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditFailure("cannot read frozen F0-V3 findings") from error
    if type(value) is not dict:
        raise AuditFailure("frozen F0-V3 findings have another shape")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = run_audit()
        projection = {
            key: report[key] for key in ("aggregate", "evidence_control", "cases")
        }
        if args.check and projection != _load_expected():
            raise AuditFailure("current F0-V3 projection differs from frozen findings")
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
        print(f"F0-V3 audit failure: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
