"""Read and authenticate the two proposed F0-V3B owner-text packets."""

from __future__ import annotations

import copy
import difflib
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PROPOSED = HERE / "proposed"

FAMILIES = {
    "canonical-framed": {
        "proposal": PROPOSED / "fiat-shamir-section-13.md",
        "overlay": PROPOSED / "canonical-framed-manifest-overlay.json",
        "page": ROOT / "docs-next/pir/fiat-shamir.md",
        "semantic_marker": "<!-- zkc-profile-source:canonical-framed-fs-semantics:end -->\n",
        "body_marker": "<!-- zkc-profile-source:canonical-framed-fs-body-grammar:end -->\n",
        "profile_key": "canonical-framed-fiat-shamir",
        "body_compiler": "canonical-framed-static-view-body-v0",
        "body_selector": "CanonicalFramedStaticViewBodyV0(schema,value) =",
        "source_law": "canonical-framed-source-views-v0",
        "views": {
            "CanonicalTranscriptDeclarationView": (
                "canonical-transcript-declaration-view-v0",
                "TranscriptDeclarationView",
            ),
            "CanonicalRequiredInfluenceView": (
                "canonical-required-influence-view-v0",
                "RequiredInfluenceView",
            ),
            "CanonicalChallengeTransitionView": (
                "canonical-challenge-transition-view-v0",
                "ChallengeTransitionView",
            ),
            "CanonicalFSConstructionView": (
                "canonical-fs-construction-view-v0",
                "FSConstructionView",
            ),
        },
    },
    "duplex-sponge": {
        "proposal": PROPOSED / "duplex-section-11.md",
        "overlay": PROPOSED / "duplex-sponge-manifest-overlay.json",
        "page": ROOT / "docs-next/pir/duplex-sponge-fiat-shamir.md",
        "semantic_marker": "<!-- zkc-profile-source:duplex-sponge-fs-semantics:end -->\n",
        "body_marker": "<!-- zkc-profile-source:duplex-sponge-fs-body-grammar:end -->\n",
        "profile_key": "duplex-sponge-fiat-shamir",
        "body_compiler": "duplex-sponge-static-view-body-v0",
        "body_selector": "DuplexSpongeStaticViewBodyV0(schema,value) =",
        "source_law": "duplex-sponge-source-views-v0",
        "views": {
            "DuplexTranscriptDeclarationView": (
                "duplex-transcript-declaration-view-v0",
                "DuplexTranscriptDeclarationView",
            ),
            "DuplexEncodedInputCoverageView": (
                "duplex-encoded-input-coverage-view-v0",
                "DuplexEncodedInputCoverageView",
            ),
            "DuplexChallengeTransitionView": (
                "duplex-challenge-transition-view-v0",
                "DuplexChallengeTransitionView",
            ),
            "DuplexFSConstructionView": (
                "duplex-fs-construction-view-v0",
                "DuplexFSConstructionView",
            ),
        },
    },
}


class ProposalError(RuntimeError):
    """A proposed owner-text packet is incomplete or no longer exact."""


def _between(text: str, start: str, end: str, label: str) -> str:
    start_marker = f"<!-- f0v3b-{start}:start -->\n"
    end_marker = f"<!-- f0v3b-{end}:end -->\n"
    if text.count(start_marker) != 1 or text.count(end_marker) != 1:
        raise ProposalError(f"{label} has a nonunique {start}/{end} block")
    before, tail = text.split(start_marker, 1)
    del before
    value, after = tail.split(end_marker, 1)
    del after
    if not value:
        raise ProposalError(f"{label} has an empty {start} block")
    return value


def read_packet(family: str) -> dict[str, Any]:
    if family not in FAMILIES:
        raise ProposalError(f"unknown proposal family {family}")
    spec = FAMILIES[family]
    path = spec["proposal"]
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise ProposalError(f"cannot read {path.relative_to(ROOT)}") from error
    diff_start = "<!-- f0v3b-page-diff:start -->\n"
    diff_end = "<!-- f0v3b-page-diff:end -->\n"
    if text.count(diff_start) != 1 or text.count(diff_end) != 1:
        raise ProposalError(f"{family} has a nonunique page-diff block")
    head, diff_tail = text.split(diff_start, 1)
    page_diff, after_diff = diff_tail.split(diff_end, 1)
    if after_diff:
        raise ProposalError(f"{family} has content after its page-diff block")
    semantic_source = _between(
        head, "semantic-source", "semantic-source", family
    )
    body_source = _between(head, "body-source", "body-source", family)
    schema_text = _between(head, "schema-json", "schema-json", family)
    if schema_text.startswith("```json\n") and schema_text.endswith("```\n"):
        schema_text = schema_text[len("```json\n") : -len("```\n")]
    try:
        schema = json.loads(schema_text)
    except json.JSONDecodeError as error:
        raise ProposalError(f"{family} proposed schema JSON is malformed") from error
    expected_keys = {
        "format",
        "family",
        "maximum_sequence_length",
        "body_compilers",
        "laws",
        "definitions",
        "views",
    }
    if type(schema) is not dict or set(schema) != expected_keys:
        raise ProposalError(f"{family} proposed schema has another outer shape")
    if (
        schema["format"] != "zkc.f0v3b.proposed-family-view-schema.v0"
        or schema["family"] != family
        or set(schema["views"]) != set(spec["views"])
    ):
        raise ProposalError(f"{family} proposed schema identity or view order drifted")
    return {
        "text": text,
        "semantic_source": semantic_source,
        "body_source": body_source,
        "schema": schema,
        "page_diff": page_diff,
        "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
    }


def read_overlay(family: str) -> dict[str, Any]:
    """Read the exact profile-manifest overlay paired with one proposal."""

    spec = FAMILIES[family]
    try:
        value = json.loads(spec["overlay"].read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProposalError(f"cannot read {family} manifest overlay") from error
    if type(value) is not dict or set(value) != {
        "format",
        "profile_key",
        "supported_subject_kinds_add",
        "definition_additions",
        "dependency_additions",
    }:
        raise ProposalError(f"{family} manifest overlay has another shape")
    if (
        value["format"] != "zkc.f0v3b.fs-family-manifest-overlay.v0"
        or value["profile_key"] != spec["profile_key"]
        or value["supported_subject_kinds_add"] != []
        or type(value["definition_additions"]) is not list
        or len(value["definition_additions"]) != 5
        or type(value["dependency_additions"]) is not list
        or len(value["dependency_additions"]) != 1
    ):
        raise ProposalError(f"{family} manifest overlay identity drifted")
    return value


def combined_schema_source(template: dict[str, Any]) -> dict[str, Any]:
    """Reconstruct the complete compiler input from the two owner proposals."""

    source = {
        key: copy.deepcopy(value)
        for key, value in template.items()
        if key not in {"body_compilers", "laws", "definitions", "views"}
    }
    compilers: set[str] = set()
    laws: set[str] = set()
    definitions: dict[str, Any] = {}
    views: dict[str, Any] = {}
    for family in FAMILIES:
        packet = read_packet(family)
        schema = packet["schema"]
        if schema["maximum_sequence_length"] != template["maximum_sequence_length"]:
            raise ProposalError(f"{family} proposal uses another sequence bound")
        compilers.update(schema["body_compilers"])
        laws.update(schema["laws"])
        for name, definition in schema["definitions"].items():
            if name in definitions and definitions[name] != definition:
                raise ProposalError(f"shared proposed definition {name} disagrees")
            definitions[name] = copy.deepcopy(definition)
        for name, view in schema["views"].items():
            if name in views:
                raise ProposalError(f"proposed view {name} is duplicated")
            views[name] = copy.deepcopy(view)
    source["body_compilers"] = sorted(compilers)
    source["laws"] = sorted(laws)
    source["definitions"] = dict(sorted(definitions.items()))
    source["views"] = {
        name: views[name]
        for name in template["view_order"]
    }
    return source


def proposed_page_bytes(family: str) -> bytes:
    spec = FAMILIES[family]
    packet = read_packet(family)
    try:
        page = spec["page"].read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise ProposalError(f"cannot read {spec['page'].relative_to(ROOT)}") from error
    for source_key, marker_key in (
        ("semantic_source", "semantic_marker"),
        ("body_source", "body_marker"),
    ):
        marker = spec[marker_key]
        if page.count(marker) != 1:
            raise ProposalError(f"{family} insertion marker is not unique")
        source = packet[source_key]
        if not source.endswith("\n\n"):
            raise ProposalError(f"{family} proposed source lacks a structural blank")
        page = page.replace(marker, source + marker)
    return page.encode("utf-8")


def page_diff(family: str) -> str:
    spec = FAMILIES[family]
    before = spec["page"].read_text(encoding="utf-8")
    after = proposed_page_bytes(family).decode("utf-8")
    path = str(spec["page"].relative_to(ROOT))
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=path,
            tofile=f"proposed/{path}",
        )
    )


def verify_page_diff(family: str) -> None:
    packet = read_packet(family)
    if packet["page_diff"] != page_diff(family):
        raise ProposalError(f"{family} frozen page diff does not match its source blocks")


def family_laws(schema: dict[str, Any], root: Any) -> tuple[str, ...]:
    """Return exact law dependencies reachable from one proposed view root."""

    found: set[str] = set()
    seen: set[str] = set()
    work = [root]
    while work:
        node = work.pop()
        if type(node) is dict:
            if set(node) == {"ref"}:
                name = node["ref"]
                if name not in seen:
                    seen.add(name)
                    work.append(schema["definitions"][name])
            elif "atom" in node and node["atom"].get("kind") == "exact-profile-law":
                found.add(node["atom"]["law"].split(":", 1)[1])
            else:
                work.extend(node.values())
        elif type(node) is list:
            work.extend(node)
    return tuple(sorted(found))
