"""Reference inspection of the migrated owner-view publication topology.

The positive path reads the authored manifests and owner pages directly.  An
isolated copy is used only for directed negative controls; no profile overlay
is needed to establish the positive result.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PUBLICATION_MODEL = (
    ROOT / "evaluation" / "semantic-profile-publication" / "reference_model.py"
)


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


publication = _load_module("_zkc_f0v_reference_publication", PUBLICATION_MODEL)


class TopologyError(ValueError):
    """The synthetic candidate does not have the selected F0-V1 topology."""


@dataclass
class Candidate:
    manifests: dict[str, dict[str, Any]]
    pages: dict[str, bytes]


INTERACTION = "interaction"
DIRECT_REPAIR_PROFILES = (
    "interaction",
    "canonical-framed-fiat-shamir",
    "duplex-sponge-fiat-shamir",
    "public-setup",
    "interface-plan",
    "endpoint-source-view",
)
DEPENDENT_REPAIR_PROFILES = DIRECT_REPAIR_PROFILES[1:]
EXPECTED_REVISIONS = {
    "interaction": 3,
    "canonical-framed-fiat-shamir": 5,
    "duplex-sponge-fiat-shamir": 4,
    "public-setup": 2,
    "interface-plan": 2,
    "endpoint-source-view": 2,
}
EXPECTED_ROTATION = (
    "analysis-afk-theorem-source-validation",
    "analysis-afk-transport",
    "analysis-cryptographic-property",
    "analysis-incremental-composition",
    "analysis-incremental-composition-source-validation",
    "canonical-framed-fiat-shamir",
    "commitment-opening",
    "duplex-sponge-fiat-shamir",
    "endpoint-source-view",
    "interaction",
    "interface-plan",
    "oir-endpoint-graph",
    "oir-projection-relation",
    "oracle-commitment",
    "public-setup",
    "relations",
    "verifier-derived-query-plan",
)
EXPECTED_STABLE = ("analysis-kernel",)
BASELINE_IDENTITIES = HERE / "baseline-identities.json"

SOURCE_KIND_TO_LOCAL_COMPILER = {
    "pir.source-binding-payload": "source-binding-payload-body-v0",
    "pir.source-capability-requirement": ("source-capability-requirement-body-v0"),
    "pir.source-no-policy": "source-no-policy-body-v0",
    "pir.source-policy-closure": "source-policy-closure-body-v0",
}
SOURCE_KIND_TO_COMMON_COMPILER = {
    "pir.source-consumer": "source-consumer-role-body-v0",
    "pir.source-purpose": "source-purpose-role-body-v0",
}
OLD_SHARED_COMPILER = "source-authority-envelope-body-v0"

SCHEMA_NAMES = (
    "public-binding-view-v0",
    "strategy-decision-view-v0",
    "public-coin-view-v0",
    "effect-view-v0",
    "claim-reduction-view-v0",
    "execution-view-v0",
)
SCHEMA_OWNERS = {
    "public-binding-view-v0": "pir.interactive-core",
    "strategy-decision-view-v0": "pir.interactive-core",
    "public-coin-view-v0": "pir.interactive-core",
    "effect-view-v0": "pir.interactive-core",
    "claim-reduction-view-v0": "pir.interactive-core",
    "execution-view-v0": "pir.protocol",
}
SCHEMA_TAGS = {
    "public-binding-view-v0": "PublicBindingView",
    "strategy-decision-view-v0": "StrategyDecisionView",
    "public-coin-view-v0": "PublicCoinView",
    "effect-view-v0": "EffectView",
    "claim-reduction-view-v0": "ClaimReductionView",
    "execution-view-v0": "ExecutionView",
}
SCHEMA_LAWS = {
    "public-binding-view-v0": ("core-admission-v0",),
    "strategy-decision-view-v0": (
        "core-admission-v0",
        "prover-view-formation-v0",
    ),
    "public-coin-view-v0": (
        "core-admission-v0",
        "public-coin-eligibility-v0",
    ),
    "effect-view-v0": ("core-admission-v0",),
    "claim-reduction-view-v0": ("core-admission-v0",),
    "execution-view-v0": (
        "core-admission-v0",
        "execution-and-replay-v0",
        "protocol-outcome-partition-v0",
        "run-view-issuance-v0",
        "visible-history-v0",
        "replay-qualification-v0",
    ),
}

INTERACTION_FRAGMENT = "interaction-static-views"
DEPENDENT_FRAGMENTS = {
    "canonical-framed-fiat-shamir": "canonical-framed-fs-body-grammar",
    "duplex-sponge-fiat-shamir": "duplex-sponge-fs-body-grammar",
    "public-setup": "public-setup",
    "interface-plan": "interface-plan-semantics",
    "endpoint-source-view": "endpoint-source-view-semantics",
}


def _ref(profile: str, kind: str, name: str) -> dict[str, str]:
    return {"profile": profile, "kind": kind, "name": name}


def _definition(
    kind: str,
    name: str,
    fragment: str,
    selector: str,
    dependencies: list[dict[str, str]] | None = None,
) -> dict[str, Any]:
    return {
        "kind": kind,
        "name": name,
        "revision": 0,
        "fragment": fragment,
        "selector": selector,
        "dependencies": [] if dependencies is None else dependencies,
    }


def _load_manifest(key: str) -> dict[str, Any]:
    path = publication.MANIFEST_FILES[key]
    return json.loads(path.read_text(encoding="utf-8"))


def _fragment(manifest: Mapping[str, Any], name: str) -> Mapping[str, str]:
    rows = [row for row in manifest["fragments"] if row["name"] == name]
    if len(rows) != 1:
        raise TopologyError(f"profile {manifest['key']} does not select {name}")
    return rows[0]


def _owner_page(manifest: Mapping[str, Any], fragment: Mapping[str, str]) -> str:
    if manifest["format"] == publication.LEGACY_SOURCE_FORMAT:
        return str(manifest["owner_page"])
    return str(fragment["owner_page"])


def _append_to_fragment(
    pages: dict[str, bytes],
    manifest: Mapping[str, Any],
    fragment_name: str,
    source: str,
) -> None:
    fragment = _fragment(manifest, fragment_name)
    page_name = _owner_page(manifest, fragment)
    page = pages.get(page_name, (ROOT / page_name).read_bytes())
    end_line = f"<!-- {fragment['end']} -->\n".encode("ascii")
    if page.count(end_line) != 1:
        raise TopologyError(f"profile {manifest['key']} has a nonunique end marker")
    insertion = source.encode("ascii")
    if not insertion or not insertion.endswith(b"\n\n"):
        raise TopologyError("synthetic source must end with one structural blank line")
    pages[page_name] = page.replace(end_line, insertion + end_line)


def _local_source_selector(profile: str, subject_kind: str) -> str:
    prefixes = {
        "interaction": "PIR",
        "canonical-framed-fiat-shamir": "CanonicalFramed",
        "duplex-sponge-fiat-shamir": "Duplex",
        "public-setup": "PublicSetup",
        "interface-plan": "InterfacePlan",
        "endpoint-source-view": "Endpoint",
    }
    suffixes = {
        "pir.source-binding-payload": "SourceBindingPayloadBody(x) =",
        "pir.source-capability-requirement": "SourceCapabilityRequirementBody(x) =",
        "pir.source-no-policy": "SourceNoPolicyBody(x) =",
        "pir.source-policy-closure": "SourcePolicyClosureBody(x) =",
    }
    return prefixes[profile] + suffixes[subject_kind]


def _schema_selector(name: str) -> str:
    return f"StaticViewSchema({SCHEMA_TAGS[name]}) = {{"


def _schema_dependencies(name: str) -> list[dict[str, str]]:
    dependencies = [
        _ref("self", "pir.body-compiler", "static-view-body-v0"),
        _ref(
            "self",
            "pir.semantic-law",
            "static-view-schema-resolution-v0",
        ),
    ]
    dependencies.extend(
        _ref("self", "pir.semantic-law", law) for law in SCHEMA_LAWS[name]
    )
    return dependencies


def _interaction_source_block() -> str:
    lines = [
        "### F0-V1 synthetic publication topology (non-normative override)",
        "",
        "```text",
        "F0VStaticViewBodyTopologyV0(x) = CompleteClosedOwnerViewBody(x)",
        "F0VStaticViewSchemaResolutionLawV0 = ExactAtomicPathsAndCompleteManifestOnly",
    ]
    lines.extend(
        _local_source_selector(INTERACTION, kind)
        for kind in SOURCE_KIND_TO_LOCAL_COMPILER
    )
    lines.extend(_schema_selector(name) for name in SCHEMA_NAMES)
    lines.extend(("```", ""))
    return "\n".join(lines) + "\n"


def _dependent_source_block(profile: str) -> str:
    lines = [
        "### F0-V1 synthetic source-envelope topology (non-normative override)",
        "",
        "```text",
    ]
    lines.extend(
        _local_source_selector(profile, kind) for kind in SOURCE_KIND_TO_LOCAL_COMPILER
    )
    lines.extend(("```", ""))
    return "\n".join(lines) + "\n"


def _replace_subject_routes(manifest: dict[str, Any], profile: str) -> None:
    for subject in manifest["subjects"]:
        kind = subject["kind"]
        if kind in SOURCE_KIND_TO_LOCAL_COMPILER:
            subject["body_compiler"] = _ref(
                "self",
                "pir.body-compiler",
                SOURCE_KIND_TO_LOCAL_COMPILER[kind],
            )
        elif kind in SOURCE_KIND_TO_COMMON_COMPILER:
            subject["body_compiler"] = _ref(
                "self" if profile == INTERACTION else INTERACTION,
                "pir.body-compiler",
                SOURCE_KIND_TO_COMMON_COMPILER[kind],
            )


def _repair_interaction(manifest: dict[str, Any], pages: dict[str, bytes]) -> None:
    manifest["revision"] = 1
    definitions: list[dict[str, Any]] = []
    for source in manifest["definitions"]:
        item = copy.deepcopy(source)
        if item["kind"] == "pir.body-compiler" and item["name"] == OLD_SHARED_COMPILER:
            item["name"] = "source-consumer-role-body-v0"
            item["selector"] = "PIRSourceConsumerRoleBody(x) = R"
        if (
            item["kind"] == "pir.semantic-law"
            and item["name"] == "static-view-issuance-v0"
        ):
            item["dependencies"] = [
                _ref("self", "pir.static-view-schema", name) for name in SCHEMA_NAMES
            ]
        definitions.append(item)

    definitions.append(
        _definition(
            "pir.body-compiler",
            "source-purpose-role-body-v0",
            INTERACTION_FRAGMENT,
            "PIRSourcePurposeRoleBody(x) = R",
        )
    )
    for kind, compiler in SOURCE_KIND_TO_LOCAL_COMPILER.items():
        definitions.append(
            _definition(
                "pir.body-compiler",
                compiler,
                INTERACTION_FRAGMENT,
                _local_source_selector(INTERACTION, kind),
            )
        )
    definitions.extend(
        (
            _definition(
                "pir.body-compiler",
                "static-view-body-v0",
                INTERACTION_FRAGMENT,
                "F0VStaticViewBodyTopologyV0(x) = CompleteClosedOwnerViewBody(x)",
            ),
            _definition(
                "pir.semantic-law",
                "static-view-schema-resolution-v0",
                INTERACTION_FRAGMENT,
                "F0VStaticViewSchemaResolutionLawV0 = "
                "ExactAtomicPathsAndCompleteManifestOnly",
            ),
        )
    )
    definitions.extend(
        _definition(
            "pir.static-view-schema",
            name,
            INTERACTION_FRAGMENT,
            _schema_selector(name),
            _schema_dependencies(name),
        )
        for name in SCHEMA_NAMES
    )
    manifest["definitions"] = definitions
    _replace_subject_routes(manifest, INTERACTION)
    _append_to_fragment(
        pages,
        manifest,
        INTERACTION_FRAGMENT,
        _interaction_source_block(),
    )


def _repair_dependent(
    manifest: dict[str, Any],
    pages: dict[str, bytes],
) -> None:
    profile = str(manifest["key"])
    fragment = DEPENDENT_FRAGMENTS[profile]
    manifest["revision"] = 1
    manifest["definitions"].extend(
        _definition(
            "pir.body-compiler",
            compiler,
            fragment,
            _local_source_selector(profile, kind),
        )
        for kind, compiler in SOURCE_KIND_TO_LOCAL_COMPILER.items()
    )
    _replace_subject_routes(manifest, profile)
    _append_to_fragment(
        pages,
        manifest,
        fragment,
        _dependent_source_block(profile),
    )


def build_candidate() -> Candidate:
    """Copy the authored manifests and pages for mutation-only use."""

    manifests = {key: _load_manifest(key) for key in DIRECT_REPAIR_PROFILES}
    page_names = {
        _owner_page(manifest, fragment)
        for manifest in manifests.values()
        for fragment in manifest["fragments"]
    }
    pages = {name: (ROOT / name).read_bytes() for name in page_names}
    return Candidate(manifests, pages)


def _definitions(
    manifest: Mapping[str, Any],
) -> dict[tuple[str, str], Mapping[str, Any]]:
    return {(item["kind"], item["name"]): item for item in manifest["definitions"]}


def _subject_routes(manifest: Mapping[str, Any]) -> dict[str, tuple[str, str]]:
    return {
        row["kind"]: (
            row["body_compiler"]["profile"],
            row["body_compiler"]["name"],
        )
        for row in manifest["subjects"]
        if row["kind"].startswith("pir.source-")
    }


def _expected_routes(profile: str) -> dict[str, tuple[str, str]]:
    routes = {
        kind: ("self", compiler)
        for kind, compiler in SOURCE_KIND_TO_LOCAL_COMPILER.items()
    }
    routes.update(
        {
            kind: (
                "self" if profile == INTERACTION else INTERACTION,
                compiler,
            )
            for kind, compiler in SOURCE_KIND_TO_COMMON_COMPILER.items()
        }
    )
    return routes


def validate_topology(profiles: Mapping[str, Any]) -> None:
    for key in DIRECT_REPAIR_PROFILES:
        manifest = profiles[key].manifest
        if manifest["revision"] != EXPECTED_REVISIONS[key]:
            raise TopologyError(f"{key} has the wrong migrated revision")
        routes = _subject_routes(manifest)
        if routes != _expected_routes(key):
            raise TopologyError(f"{key} has the wrong source-authority routing")
        definitions = _definitions(manifest)
        for kind, compiler in SOURCE_KIND_TO_LOCAL_COMPILER.items():
            coordinate = ("pir.body-compiler", compiler)
            definition = definitions.get(coordinate)
            if definition is None or definition["selector"] != _local_source_selector(key, kind):
                raise TopologyError(f"{key} omits exact local compiler {compiler}")
        if any(item["name"] == OLD_SHARED_COMPILER for item in manifest["definitions"]):
            raise TopologyError(f"{key} retains the catch-all source compiler")

    interaction = profiles[INTERACTION].manifest
    definitions = _definitions(interaction)
    schema_rows = [
        item
        for item in interaction["definitions"]
        if item["kind"] == "pir.static-view-schema"
    ]
    if tuple(row["name"] for row in schema_rows) != SCHEMA_NAMES:
        raise TopologyError("Interaction has the wrong static-view schema catalog")
    for row in schema_rows:
        name = row["name"]
        if row["selector"] != _schema_selector(name):
            raise TopologyError(f"schema {name} has the wrong owner or selector")
        if row["dependencies"] != _schema_dependencies(name):
            raise TopologyError(f"schema {name} has the wrong exact dependencies")
    source_body = profiles[INTERACTION].body_bytes
    for name in SCHEMA_NAMES:
        tag = SCHEMA_TAGS[name]
        owner = (
            f"ProtocolView(ProtocolId, {tag})"
            if name == "execution-view-v0"
            else f"CoreView(CoreId, {tag})"
        )
        if source_body.count(f"owner: {owner},".encode("ascii")) != 1:
            raise TopologyError(f"schema {name} has the wrong exact owner")
    issuance = definitions[("pir.semantic-law", "static-view-issuance-v0")]
    expected_schema_refs = [
        _ref("self", "pir.static-view-schema", name) for name in SCHEMA_NAMES
    ]
    if issuance["dependencies"] != expected_schema_refs:
        raise TopologyError("static-view issuance does not close over six schemas")
    expected_common = {
        "source-consumer-role-body-v0": "PIRSourceConsumerRoleBody(x) = R",
        "source-purpose-role-body-v0": "PIRSourcePurposeRoleBody(x) = R",
    }
    for name, selector in expected_common.items():
        definition = definitions.get(("pir.body-compiler", name))
        if definition is None or definition["selector"] != selector:
            raise TopologyError(f"Interaction omits exact common role compiler {name}")


def _profile_summary(profile: Any, profile_ref: bytes) -> dict[str, Any]:
    return {
        "body_sha256": hashlib.sha256(profile.body_bytes).hexdigest(),
        "profile_ref_hex": profile_ref.hex(),
        "direct_imports": list(profile.direct_import_keys),
        "declarations": {
            f"{kind}/{name}": ordinal
            for (kind, name), ordinal in sorted(profile.declaration_index.items())
        },
    }


def observe(candidate: Candidate | None = None) -> dict[str, Any]:
    repaired = (
        publication.compile_repository()
        if candidate is None
        else publication.compile_repository(
            manifest_overrides=candidate.manifests,
            page_overrides=candidate.pages,
        )
    )
    validate_topology(repaired.profiles)
    baseline = json.loads(BASELINE_IDENTITIES.read_text(encoding="utf-8"))["profiles"]
    rotated = tuple(
        sorted(
            key
            for key in publication.PROFILE_KEYS
            if baseline[key] != repaired.profiles[key].profile_id.digest.hex()
        )
    )
    stable = tuple(sorted(set(publication.PROFILE_KEYS) - set(rotated)))
    if rotated != EXPECTED_ROTATION:
        raise TopologyError(f"wrong rotation cone: {rotated!r}")
    if stable != EXPECTED_STABLE:
        raise TopologyError(f"wrong stable complement: {stable!r}")

    interaction = repaired.profiles[INTERACTION].manifest
    return {
        "rotated_profiles": list(rotated),
        "stable_profiles": list(stable),
        "schema_entries": [
            row["name"]
            for row in interaction["definitions"]
            if row["kind"] == "pir.static-view-schema"
        ],
        "revisions": {
            key: repaired.profiles[key].manifest["revision"]
            for key in DIRECT_REPAIR_PROFILES
        },
        "source_routes": {
            key: {
                kind: {"profile": route[0], "compiler": route[1]}
                for kind, route in sorted(
                    _subject_routes(repaired.profiles[key].manifest).items()
                )
            }
            for key in DIRECT_REPAIR_PROFILES
        },
        "profiles": {
            key: _profile_summary(
                repaired.profiles[key],
                repaired.profiles[key].profile_id.internal_reference(),
            )
            for key in publication.PROFILE_KEYS
        },
        "interaction_before": baseline[INTERACTION],
        "interaction_after": repaired.profiles[INTERACTION].profile_id.digest.hex(),
    }


def _replace_page_text(candidate: Candidate, old: str, new: str) -> None:
    old_bytes = old.encode("ascii")
    matches = [key for key, page in candidate.pages.items() if old_bytes in page]
    if len(matches) != 1:
        raise TopologyError(f"mutation selector occurs in {len(matches)} pages")
    key = matches[0]
    candidate.pages[key] = candidate.pages[key].replace(
        old_bytes, new.encode("ascii"), 1
    )


def _find_definition(manifest: dict[str, Any], kind: str, name: str) -> dict[str, Any]:
    rows = [
        row
        for row in manifest["definitions"]
        if row["kind"] == kind and row["name"] == name
    ]
    if len(rows) != 1:
        raise TopologyError(f"cannot uniquely mutate {kind}/{name}")
    return rows[0]


def _find_subject(manifest: dict[str, Any], kind: str) -> dict[str, Any]:
    rows = [row for row in manifest["subjects"] if row["kind"] == kind]
    if len(rows) != 1:
        raise TopologyError(f"cannot uniquely mutate subject {kind}")
    return rows[0]


def mutated_candidate(name: str) -> Candidate:
    candidate = build_candidate()
    interaction = candidate.manifests[INTERACTION]
    if name == "missing-schema":
        interaction["definitions"] = [
            row
            for row in interaction["definitions"]
            if not (
                row["kind"] == "pir.static-view-schema"
                and row["name"] == "claim-reduction-view-v0"
            )
        ]
        issuance = _find_definition(
            interaction, "pir.semantic-law", "static-view-issuance-v0"
        )
        issuance["dependencies"] = [
            row
            for row in issuance["dependencies"]
            if row["name"] != "claim-reduction-view-v0"
        ]
    elif name == "extra-schema":
        selector = "StaticViewSchema(ExtraView) = {"
        interaction["definitions"].append(
            _definition(
                "pir.static-view-schema",
                "extra-view-v0",
                INTERACTION_FRAGMENT,
                selector,
                _schema_dependencies("public-binding-view-v0"),
            )
        )
        issuance = _find_definition(
            interaction, "pir.semantic-law", "static-view-issuance-v0"
        )
        issuance["dependencies"].append(
            _ref("self", "pir.static-view-schema", "extra-view-v0")
        )
        _append_to_fragment(
            candidate.pages,
            interaction,
            INTERACTION_FRAGMENT,
            f"```text\n{selector}\n```\n\n",
        )
    elif name == "wrong-owner":
        _replace_page_text(
            candidate,
            "owner: CoreView(CoreId, PublicBindingView),",
            "owner: ProtocolView(ProtocolId, PublicBindingView),",
        )
    elif name == "wrong-law":
        row = _find_definition(
            interaction, "pir.static-view-schema", "public-coin-view-v0"
        )
        for dependency in row["dependencies"]:
            if dependency["name"] == "public-coin-eligibility-v0":
                dependency["name"] = "execution-and-replay-v0"
                break
    elif name == "common-role-cross-kind":
        row = _find_subject(interaction, "pir.source-binding-payload")
        row["body_compiler"] = _ref(
            "self", "pir.body-compiler", "source-consumer-role-body-v0"
        )
    elif name == "unreachable-extension":
        selector = "F0VOrphanStaticViewSchemaV0 = Orphan"
        interaction["definitions"].append(
            _definition(
                "pir.static-view-schema",
                "orphan-view-v0",
                INTERACTION_FRAGMENT,
                selector,
            )
        )
        _append_to_fragment(
            candidate.pages,
            interaction,
            INTERACTION_FRAGMENT,
            f"```text\n{selector}\n```\n\n",
        )
    elif name == "absent-selector":
        row = _find_definition(interaction, "pir.body-compiler", "static-view-body-v0")
        row["selector"] = "F0VAbsentStaticViewBodySelector"
    elif name == "retained-revision":
        interaction["revision"] = 0
    elif name == "imported-family-compiler":
        profile = candidate.manifests["canonical-framed-fiat-shamir"]
        local_name = SOURCE_KIND_TO_LOCAL_COMPILER["pir.source-binding-payload"]
        profile["definitions"] = [
            row
            for row in profile["definitions"]
            if not (row["kind"] == "pir.body-compiler" and row["name"] == local_name)
        ]
        subject = _find_subject(profile, "pir.source-binding-payload")
        subject["body_compiler"] = _ref(
            INTERACTION, "pir.body-compiler", "source-consumer-role-body-v0"
        )
    elif name == "swapped-common-role":
        profile = candidate.manifests["public-setup"]
        subject = _find_subject(profile, "pir.source-purpose")
        subject["body_compiler"] = _ref(
            INTERACTION, "pir.body-compiler", "source-consumer-role-body-v0"
        )
    else:
        raise TopologyError(f"unknown mutation {name!r}")
    return candidate
