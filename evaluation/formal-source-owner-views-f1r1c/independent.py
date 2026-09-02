#!/usr/bin/env python3
"""Raw-source inventory independent of the structured F1-R1C audit model."""

from __future__ import annotations

import json
from pathlib import Path
import re
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "docs-next" / "pir" / "profiles" / "interaction.json"
OWNER_PAGE = ROOT / "docs-next" / "pir" / "interactive-core.md"

VIEW_BODIES = (
    "PublicBindingViewBody",
    "StrategyDecisionViewBody",
    "PublicCoinViewBody",
    "EffectViewBody",
    "ClaimReductionViewBody",
    "ExecutionViewBody",
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


class InventoryError(RuntimeError):
    pass


def _object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise InventoryError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _extract(page: bytes, start: str, end: str) -> bytes:
    start_line = f"<!-- {start} -->\n".encode("ascii")
    end_line = f"<!-- {end} -->\n".encode("ascii")
    if page.count(start_line) != 1 or page.count(end_line) != 1:
        raise InventoryError("source markers are not unique")
    left = page.index(start_line) + len(start_line)
    right = page.index(end_line)
    if left >= right:
        raise InventoryError("source marker interval is empty or reversed")
    return page[left:right]


def inventory() -> Mapping[str, Any]:
    try:
        manifest = json.loads(
            MANIFEST.read_text(encoding="utf-8"), object_pairs_hook=_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise InventoryError("cannot read Interaction manifest") from error
    page = OWNER_PAGE.read_bytes()
    fragments = {item["name"]: item for item in manifest["fragments"]}
    static_source = fragments["interaction-static-views"]
    body_source = fragments["interaction-body-grammar"]
    static_fragment = _extract(page, static_source["start"], static_source["end"])
    body_fragment = _extract(page, body_source["start"], body_source["end"])

    explicit_kinds = {item["kind"] for item in manifest["definitions"]}
    all_kinds = explicit_kinds | {"pir.source-fragment", "pir.subject-language"}
    selectors = tuple(item["selector"] for item in manifest["definitions"])
    body_functions = tuple(
        re.findall(rb"(?m)^([A-Za-z][A-Za-z0-9]+Body)\([^\n]*\) =", static_fragment)
    )
    body_functions_text = tuple(item.decode("ascii") for item in body_functions)
    subjects = {item["kind"]: item for item in manifest["subjects"]}
    source_kinds = tuple(
        sorted(kind for kind in subjects if kind.startswith("pir.source-"))
    )
    return {
        "view_bodies": [
            body
            for body in VIEW_BODIES
            if f"{body} = {{".encode("ascii") in static_fragment
        ],
        "extension_catalogs": sorted(all_kinds - COMMON_CATALOG_KINDS),
        "selected_view_body_declarations": [
            body for body in VIEW_BODIES if any(body in item for item in selectors)
        ],
        "canonical_view_body_grammars": [
            body
            for body in VIEW_BODIES
            if f"{body}(x) = R".encode("ascii") in body_fragment
        ],
        "static_fragment_body_functions": list(body_functions_text),
        "source_subject_compilers": {
            kind: subjects[kind]["body_compiler"]["name"] for kind in source_kinds
        },
    }
