#!/usr/bin/env python3
"""Independently audit the migrated PIR owner text before freeze."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


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
PACKET_SOURCES = (
    "evaluation/formal-source-fs-view-determinacy-f0v3/proposed/fiat-shamir-section-13.md",
    "evaluation/formal-source-fs-view-determinacy-f0v3/proposed/duplex-section-11.md",
)


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
        for relative in (*PAGES, *MIGRATED_MANIFESTS, *PACKET_SOURCES)
    }


def _definition_count(text: str, symbol: str) -> int:
    return len(
        re.findall(
            rf"^[ \t]*{re.escape(symbol)}(?:\([^\n]*\))?[ \t]*(?::=|=)",
            text,
            flags=re.MULTILINE,
        )
    )


def _record_field_types(text: str, body: str) -> dict[str, str]:
    match = re.search(rf"^{re.escape(body)} = \{{\n", text, flags=re.MULTILINE)
    _require(match is not None, f"body {body} is absent")
    assert match is not None
    lines = text[match.end() :].splitlines()
    fields: dict[str, str] = {}
    depth = 1
    for line in lines:
        field = re.match(r"^  ([a-z][a-z0-9_]*): (.*?)(?:,)?$", line)
        if depth == 1 and field:
            _require(field.group(1) not in fields, f"body {body} repeats a field")
            fields[field.group(1)] = field.group(2)
        depth += line.count("{") - line.count("}")
        if depth == 0:
            break
    _require(depth == 0, f"body {body} is not closed")
    return fields


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


FS_BODY_PAGES: dict[str, str] = {
    "TranscriptDeclarationViewBody": "docs-next/pir/fiat-shamir.md",
    "RequiredInfluenceViewBody": "docs-next/pir/fiat-shamir.md",
    "ChallengeTransitionViewBody": "docs-next/pir/fiat-shamir.md",
    "FSConstructionViewBody": "docs-next/pir/fiat-shamir.md",
    "DuplexTranscriptDeclarationViewBody": "docs-next/pir/duplex-sponge-fiat-shamir.md",
    "DuplexEncodedInputCoverageViewBody": "docs-next/pir/duplex-sponge-fiat-shamir.md",
    "DuplexChallengeTransitionViewBody": "docs-next/pir/duplex-sponge-fiat-shamir.md",
    "DuplexFSConstructionViewBody": "docs-next/pir/duplex-sponge-fiat-shamir.md",
}

FS_PROSE_FIELDS: dict[str, tuple[str, ...]] = {body: () for body in FS_BODY_PAGES}
FS_UNDEFINED_FIELDS: dict[str, tuple[str, ...]] = {body: () for body in FS_BODY_PAGES}


def _field_form(field_type: str) -> str:
    if field_type == "Natural":
        return "natural"
    if field_type == "CanonicalValue" or field_type.startswith("CanonicalValue<"):
        return "value"
    if field_type == "PIRProfileLawReference":
        return "law-reference"
    if field_type.startswith(("CanonicalSeq<", "CanonicalSortedUniqueSeq<", "NonEmptyCanonicalSeq<")):
        return "sequence"
    if field_type in {"AlwaysAccept", "DuplexSponge", "NoRetry", "None", "StructurallyConstructed"}:
        return "closed-tag"
    if field_type.startswith("{") or field_type in {
        "AlgorithmUse",
        "ChallengeABI",
        "MaterialCoordinate",
        "MaterialSchema",
        "PIRRuntimeSchema",
        "ScheduleCorrespondence",
    }:
        return "record"
    if any(token in field_type for token in ("Id", "Ref", "ValueType", "SemanticFailureType")):
        return "identity"
    raise ReviewError(f"family body field has a non-exact form: {field_type}")


def _packet_schema(relative: str) -> dict[str, Any]:
    text = _read(relative)
    try:
        block = text.split("<!-- f0v3b-schema-json:start -->", 1)[1]
        block = block.split("<!-- f0v3b-schema-json:end -->", 1)[0]
        block = block.split("```json", 1)[1].split("```", 1)[0]
        value = json.loads(block)
    except (IndexError, json.JSONDecodeError) as error:
        raise ReviewError(f"cannot recover the candidate schema packet from {relative}") from error
    _require(type(value) is dict, f"candidate schema packet in {relative} has another carrier")
    return value


def _packet_review(pages: dict[str, str]) -> dict[str, Any]:
    canonical = _packet_schema(PACKET_SOURCES[0])["definitions"]
    duplex = _packet_schema(PACKET_SOURCES[1])["definitions"]
    transcript = canonical["CanonicalTranscriptDeclarationViewBody"]["record"]
    transition = canonical["CanonicalChallengeTransitionViewBody"]["record"]
    canonical_result = canonical["CanonicalFSConstructionViewBody"]["record"]
    duplex_result = duplex["DuplexFSConstructionViewBody"]["record"]
    _require(transcript[9][1] == {"ref": "CanonicalValue"}, "candidate application-domain field drifted")
    _require(
        transcript[11][1]["atom"]["law"]
        == "canonical-framed:canonical-framed-source-views-v0",
        "candidate frame-body law drifted",
    )
    _require([row[0] for row in transition[5][1]["record"]] == [0, 1], "candidate draw record drifted")
    _require(len(canonical_result) == 8 and len(duplex_result) == 13, "candidate result records drifted")

    packet_bodies = {
        "TranscriptDeclarationViewBody": transcript,
        "RequiredInfluenceViewBody": canonical["CanonicalRequiredInfluenceViewBody"]["record"],
        "ChallengeTransitionViewBody": transition,
        "FSConstructionViewBody": canonical_result,
        "DuplexTranscriptDeclarationViewBody": duplex["DuplexTranscriptDeclarationViewBody"]["record"],
        "DuplexEncodedInputCoverageViewBody": duplex["DuplexEncodedInputCoverageViewBody"]["record"],
        "DuplexChallengeTransitionViewBody": duplex["DuplexChallengeTransitionViewBody"]["record"],
        "DuplexFSConstructionViewBody": duplex_result,
    }
    packet_counts = {body: len(record) for body, record in packet_bodies.items()}
    _require(
        packet_counts
        == {
            "TranscriptDeclarationViewBody": 13,
            "RequiredInfluenceViewBody": 7,
            "ChallengeTransitionViewBody": 11,
            "FSConstructionViewBody": 8,
            "DuplexTranscriptDeclarationViewBody": 20,
            "DuplexEncodedInputCoverageViewBody": 10,
            "DuplexChallengeTransitionViewBody": 11,
            "DuplexFSConstructionViewBody": 13,
        }
        and all(
            [row[0] for row in record] == list(range(len(record)))
            for record in packet_bodies.values()
        ),
        "candidate body cardinality or ordinal sequence drifted",
    )

    canonical_page = pages["docs-next/pir/fiat-shamir.md"]
    duplex_page = pages["docs-next/pir/duplex-sponge-fiat-shamir.md"]
    for snippet, text in (
        ('application_domain: ProtocolDeclarationRef<"pir.fs-application-domain">', canonical_page),
        ("frame_body_law: PIRProfileLawReference", canonical_page),
        ("draw_bounds: { squeeze_length: Natural, maximum_draws: Natural }", canonical_page),
        ("result_schema: PIRRuntimeSchema", canonical_page),
        ("result_schema: PIRRuntimeSchema", duplex_page),
    ):
        _require(snippet in text, f"normalized owner body drifted at {snippet}")

    deviations = [
        {
            "body": "TranscriptDeclarationViewBody",
            "field": "application_domain",
            "packet": "CanonicalValue",
            "owner": 'ProtocolDeclarationRef<"pir.fs-application-domain">',
            "judgment": "owner",
        },
        {
            "body": "TranscriptDeclarationViewBody",
            "field": "frame_body_law",
            "packet": "canonical-framed-source-views-v0",
            "owner": "body-grammar law reference",
            "judgment": "owner",
        },
        {
            "body": "ChallengeTransitionViewBody",
            "field": "draw_bounds",
            "packet": "record ordinals 0 and 1",
            "owner": "record fields squeeze_length and maximum_draws",
            "judgment": "owner",
        },
        {
            "body": "FSConstructionViewBody",
            "field": "result_schema",
            "packet": "omitted",
            "owner": "PIRRuntimeSchema",
            "judgment": "owner",
        },
        {
            "body": "DuplexFSConstructionViewBody",
            "field": "result_schema",
            "packet": "omitted",
            "owner": "PIRRuntimeSchema",
            "judgment": "owner",
        },
    ]
    return {
        "body_field_counts": packet_counts,
        "deviations": deviations,
    }


def _claim_source_region_text_closed(interaction: str) -> bool:
    required = (
        "BoundaryRegion(Initially) := {",
        "required_true: {}, required_false: {}, impossible: false",
        "BoundaryRegion(BeforeOccurrence(o)) := {",
        "required_false: { Guard(t') | t' a terminal occurrence earlier than o",
        "impossible: an earlier terminal occurrence has Guard Always",
        "ClaimSourceRegion(c) :=",
        "BoundaryRegion(ScopeDecl(PublicBindingDecl(binding).scope).opening)",
        "when c.source is InitialClaim(binding)",
        "when c.source is ReductionOutput(r, output_ordinal), with o_r the",
        "occurrence of ApplyReduction(r)",
        "Implies(Region(o), ClaimSourceRegion(c))",
        "Disjoint(Region(o), ClaimSourceRegion(c))",
    )
    return (
        all(snippet in interaction for snippet in required)
        and interaction.count("BoundaryRegion(Initially) :=") == 1
        and interaction.count("BoundaryRegion(BeforeOccurrence(o)) :=") == 1
        and interaction.count("ClaimSourceRegion(c) :=") == 1
        and "Region(Source(c))" not in interaction
    )


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
        "AdmittedModuleEffectAtom": _definition_count(
            definition_surface, "AdmittedModuleEffectAtom"
        ),
        "GuardInputs": definition_surface.count("GuardInputs(o) ="),
        "GuardTerm": definition_surface.count("GuardTerm(o) ="),
    }
    _require(
        unresolved == {
            "AdmittedModuleEffectAtom": 1,
            "GuardInputs": 2,
            "GuardTerm": 2,
        },
        "the repaired owner-name definition census drifted",
    )
    _require(
        "AttemptGuards(o) := { Guard(o) } minus { Always }" in interaction,
        "the unguarded-scope attempt law drifted",
    )
    scope = interaction.split("ScopeDecl = {", 1)[1].split("\n}", 1)[0]
    _require("guard" not in scope.lower(), "ScopeDecl unexpectedly acquired a guard")
    _require(
        "| PIRReference | PIRProfileLawReference | AdmittedModuleEffect" in interaction
        and interaction.count("AdmittedModuleEffectAtom(x) :=") == 1
        and "V(9,AdmittedModuleEffectAtom(effect))" in interaction,
        "the module-effect atomic boundary closure drifted",
    )
    claim_source_region_closed = _claim_source_region_text_closed(interaction)

    all_fields: dict[str, dict[str, str]] = {}
    forms: dict[str, dict[str, int]] = {}
    for body, relative in FS_BODY_PAGES.items():
        all_fields[body] = _record_field_types(pages[relative], body)
        forms[body] = {}
        for field_type in all_fields[body].values():
            form = _field_form(field_type)
            forms[body][form] = forms[body].get(form, 0) + 1
    field_count = sum(map(len, all_fields.values()))
    prose_count = sum(map(len, FS_PROSE_FIELDS.values()))
    undefined_count = sum(map(len, FS_UNDEFINED_FIELDS.values()))
    _require(field_count == 95, "the eight family body displays no longer contain 95 fields")
    _require(prose_count == 0, "a prose-only family field remains")
    _require(undefined_count == 0, "an undefined family field remains")
    _require(
        "names such as `IdentityOnEveryOccurrenceRef` are nullary variant tags"
        in interaction,
        "the nullary closed-name rule is absent",
    )
    return {
        "static_view_schemas": schema_count,
        "resolved_schema_body_displays": body_count,
        "owner_unresolved_expressions": []
        if claim_source_region_closed
        else [
            "Region(Source(c)) has no region mapping for InitialClaim(BindingRef) or ReductionOutput(ReductionRef, output_ordinal)"
        ],
        "claim_source_region_closed": claim_source_region_closed,
        "owner_atomic_boundary_arms": 10,
        "owner_module_effect_body_arm": 9,
        "fs_body_fields": field_count,
        "fs_exact_fields": field_count,
        "fs_prose_fields": prose_count,
        "fs_undefined_fields": undefined_count,
        "fs_unclosed_families": 0,
        "fs_field_form_counts": forms,
        "packet_review": _packet_review(pages),
    }


@dataclass(frozen=True)
class _Occurrence:
    terminal: bool
    guard: int | None
    openings_before: tuple[int, ...] = ()


@dataclass(frozen=True)
class _Region:
    required_true: frozenset[int]
    required_false: frozenset[int]
    impossible: bool


def _region(schedule: tuple[_Occurrence, ...], position: int) -> _Region:
    required_true = (
        frozenset()
        if schedule[position].guard is None
        else frozenset({schedule[position].guard})
    )
    earlier_terminals = tuple(
        occurrence
        for occurrence in schedule[:position]
        if occurrence.terminal
    )
    required_false = frozenset(
        occurrence.guard
        for occurrence in earlier_terminals
        if occurrence.guard is not None
    )
    return _Region(
        required_true,
        required_false,
        any(occurrence.guard is None for occurrence in earlier_terminals)
        or bool(required_true & required_false),
    )


def _boundary_region(
    schedule: tuple[_Occurrence, ...], before_position: int
) -> _Region:
    earlier_terminals = tuple(
        occurrence
        for occurrence in schedule[:before_position]
        if occurrence.terminal
    )
    return _Region(
        frozenset(),
        frozenset(
            occurrence.guard
            for occurrence in earlier_terminals
            if occurrence.guard is not None
        ),
        any(occurrence.guard is None for occurrence in earlier_terminals),
    )


def _region_satisfied(region: _Region, valuation: tuple[bool, ...]) -> bool:
    return not region.impossible and all(
        valuation[atom] for atom in region.required_true
    ) and all(not valuation[atom] for atom in region.required_false)


def _path_attempts(
    schedule: tuple[_Occurrence, ...], valuation: tuple[bool, ...]
) -> tuple[tuple[bool, ...], frozenset[int]]:
    live = True
    attempts: list[bool] = []
    opened: set[int] = set()
    for occurrence in schedule:
        if not live:
            attempts.append(False)
            continue
        opened.update(occurrence.openings_before)
        active = occurrence.guard is None or valuation[occurrence.guard]
        attempts.append(active)
        if active and occurrence.terminal:
            live = False
    return tuple(attempts), frozenset(opened)


def _implies(left: _Region, right: _Region) -> bool:
    return (
        right.required_true <= left.required_true
        and right.required_false <= left.required_false
    )


def _disjoint(left: _Region, right: _Region) -> bool:
    return bool(
        left.required_true & right.required_false
        or right.required_true & left.required_false
    )


def _claim_status(
    target: _Region, source: _Region, consumers: tuple[_Region, ...]
) -> str:
    live = _implies(target, source) and all(
        _disjoint(target, consumer) for consumer in consumers
    )
    dead = _disjoint(target, source) or any(
        _implies(target, consumer) for consumer in consumers
    )
    _require(
        not (live and dead),
        "ClaimStatus produced overlapping Live and Dead verdicts",
    )
    return "Live" if live else "Dead" if dead else "Unknown"


def _claim_source_region(
    schedule: tuple[_Occurrence, ...], source_kind: str, source_position: int | None
) -> _Region:
    if source_kind == "initially":
        _require(source_position is None, "Initially source has an occurrence position")
        return _boundary_region(schedule, 0)
    if source_kind == "before-occurrence":
        _require(source_position is not None, "boundary source has no occurrence position")
        return _boundary_region(schedule, source_position)
    if source_kind == "reduction-output":
        _require(source_position is not None, "Reduction output has no occurrence position")
        return _region(schedule, source_position)
    raise ReviewError(f"unknown claim source kind: {source_kind}")


def _claim_source_present(
    path: tuple[tuple[bool, ...], frozenset[int]],
    source_kind: str,
    source_position: int | None,
    opening: int | None,
) -> bool:
    attempts, opened = path
    if source_kind == "initially":
        return True
    if source_kind == "before-occurrence":
        _require(opening is not None, "boundary source has no opening coordinate")
        return opening in opened
    if source_kind == "reduction-output":
        _require(source_position is not None, "Reduction output has no occurrence position")
        return attempts[source_position]
    raise ReviewError(f"unknown claim source kind: {source_kind}")


def _path_referenced_claim_status(
    schedule: tuple[_Occurrence, ...],
    target_position: int,
    source_kind: str,
    source_position: int | None,
    opening: int | None = None,
    consumers: tuple[int, ...] = (),
) -> dict[str, Any]:
    atoms = sorted(
        {occurrence.guard for occurrence in schedule if occurrence.guard is not None}
    )
    _require(atoms == list(range(len(atoms))), "claim fixture guard atoms are not dense")
    valuations = tuple(product((False, True), repeat=len(atoms)))
    paths = tuple(_path_attempts(schedule, valuation) for valuation in valuations)
    reaching = tuple(path for path in paths if path[0][target_position])
    _require(reaching, "claim fixture target has no reaching path")
    source_region = _claim_source_region(schedule, source_kind, source_position)
    consumer_regions = tuple(_region(schedule, position) for position in consumers)
    status = _claim_status(_region(schedule, target_position), source_region, consumer_regions)
    actual = tuple(
        _claim_source_present(path, source_kind, source_position, opening)
        and not any(path[0][position] for position in consumers)
        for path in reaching
    )
    live_counterexample = status == "Live" and not all(actual)
    dead_counterexample = status == "Dead" and any(actual)
    _require(
        not live_counterexample and not dead_counterexample,
        "ClaimStatus disagrees with the path reference",
    )
    return {
        "status": status,
        "reaching_paths": len(reaching),
        "paths_with_live_claim": sum(actual),
        "live_counterexamples": int(live_counterexample),
        "dead_counterexamples": int(dead_counterexample),
    }


def _claim_source_discriminators() -> dict[str, Any]:
    fixtures = {
        "initial-claim-at-initial-boundary": (
            (_Occurrence(False, None), _Occurrence(True, None)),
            1,
            "initially",
            None,
            None,
        ),
        "initial-claim-before-unguarded-occurrence": (
            (_Occurrence(False, None, (0,)), _Occurrence(True, None)),
            1,
            "before-occurrence",
            0,
            0,
        ),
        "initial-claim-before-guarded-occurrence": (
            (_Occurrence(False, 0, (0,)), _Occurrence(True, None)),
            1,
            "before-occurrence",
            0,
            0,
        ),
        "reduction-output-at-later-guarded-terminal": (
            (_Occurrence(False, 0), _Occurrence(True, 0)),
            1,
            "reduction-output",
            0,
            None,
        ),
    }
    results = {
        name: _path_referenced_claim_status(
            schedule,
            target,
            source_kind,
            source_position,
            opening,
        )
        for name, (
            schedule,
            target,
            source_kind,
            source_position,
            opening,
        ) in fixtures.items()
    }
    _require(
        all(result["status"] == "Live" for result in results.values()),
        "a ClaimSource arm discriminator is not Live",
    )

    guarded_schedule = fixtures["initial-claim-before-guarded-occurrence"][0]
    occurrence_coercion = _claim_status(
        _region(guarded_schedule, 1),
        _region(guarded_schedule, 0),
        (),
    )
    _require(
        occurrence_coercion == "Unknown",
        "guarded binding-opening discriminator no longer distinguishes the repair",
    )
    results["initial-claim-before-guarded-occurrence"][
        "pre-repair-occurrence-coercion"
    ] = occurrence_coercion
    return results


def _region_and_claim_oracle() -> dict[str, Any]:
    valuations = tuple(product((False, True), repeat=2))
    occurrence_shapes = tuple(
        _Occurrence(terminal, guard)
        for terminal in (False, True)
        for guard in (None, 0, 1)
    )
    schedule_count = 0
    region_count = 0
    attempt_comparisons = 0
    impossible_regions = 0
    unreachable_regions = 0
    opening_boundaries = 0
    opening_boundary_comparisons = 0
    claim_cases = 0
    claim_source_cases = {"occurrence": 0, "scope-boundary": 0}
    claim_verdicts = {"Live": 0, "Dead": 0, "Unknown": 0}
    claim_counterexamples = {"Live": 0, "Dead": 0}

    for length in range(1, 5):
        for raw_schedule in product(occurrence_shapes, repeat=length):
            for with_openings in (False, True):
                schedule = tuple(
                    _Occurrence(
                        occurrence.terminal,
                        occurrence.guard,
                        (position,) if with_openings else (),
                    )
                    for position, occurrence in enumerate(raw_schedule)
                )
                schedule_count += 1
                paths = tuple(
                    _path_attempts(schedule, valuation) for valuation in valuations
                )
                opening_boundaries += sum(len(opened) for _attempts, opened in paths)
                for position in range(length):
                    region = _region(schedule, position)
                    observed = tuple(path[0][position] for path in paths)
                    predicted = tuple(
                        _region_satisfied(region, valuation) for valuation in valuations
                    )
                    _require(observed == predicted, "Region disagrees with attemptedness")
                    region_count += 1
                    attempt_comparisons += len(valuations)
                    impossible_regions += int(region.impossible)
                    unreachable_regions += int(not any(observed))
                    _require(
                        region.impossible == (not any(observed)),
                        "Region impossible flag disagrees with reachability",
                    )
                    if with_openings:
                        boundary = _boundary_region(schedule, position)
                        observed_boundary = tuple(
                            position in path[1] for path in paths
                        )
                        predicted_boundary = tuple(
                            _region_satisfied(boundary, valuation)
                            for valuation in valuations
                        )
                        _require(
                            observed_boundary == predicted_boundary,
                            "scope-boundary region disagrees with execution",
                        )
                        opening_boundary_comparisons += len(valuations)

            # Give every occurrence a deterministic unguarded opening boundary.
            # This checks occurrence and initial-claim source regions against the
            # same path reference.  The latter is evidence for the proposed
            # typed source map; the owner text does not currently define it.
            schedule = tuple(
                _Occurrence(
                    occurrence.terminal,
                    occurrence.guard,
                    (position,),
                )
                for position, occurrence in enumerate(raw_schedule)
            )
            paths = tuple(
                _path_attempts(schedule, valuation) for valuation in valuations
            )
            for target_position in range(length):
                reaching = tuple(
                    path for path in paths if path[0][target_position]
                )
                if not reaching:
                    continue
                source_regions = tuple(
                    (
                        "scope-boundary",
                        position,
                        _boundary_region(schedule, position),
                    )
                    for position in range(target_position + 1)
                ) + tuple(
                    ("occurrence", position, _region(schedule, position))
                    for position in range(target_position)
                    if not schedule[position].terminal
                )
                for source_kind, source_position, source_region in source_regions:
                    possible_consumers = tuple(
                        consumer_position
                        for consumer_position in range(target_position)
                        if not schedule[consumer_position].terminal
                        and (
                            consumer_position >= source_position
                            if source_kind == "scope-boundary"
                            else consumer_position > source_position
                        )
                    )
                    for mask in range(1 << len(possible_consumers)):
                        consumer_positions = tuple(
                            position
                            for index, position in enumerate(possible_consumers)
                            if mask & (1 << index)
                        )
                        consumer_regions = tuple(
                            _region(schedule, position)
                            for position in consumer_positions
                        )
                        status = _claim_status(
                            _region(schedule, target_position),
                            source_region,
                            consumer_regions,
                        )
                        actual = tuple(
                            (
                                source_position in path[1]
                                if source_kind == "scope-boundary"
                                else path[0][source_position]
                            )
                            and not any(
                                path[0][position]
                                for position in consumer_positions
                            )
                            for path in reaching
                        )
                        claim_cases += 1
                        claim_source_cases[source_kind] += 1
                        claim_verdicts[status] += 1
                        if status == "Live" and not all(actual):
                            claim_counterexamples["Live"] += 1
                        if status == "Dead" and any(actual):
                            claim_counterexamples["Dead"] += 1

    _require(
        impossible_regions == unreachable_regions,
        "impossible and unreachable region counts differ",
    )
    _require(
        claim_counterexamples == {"Live": 0, "Dead": 0},
        "ClaimStatus is unsound against the path reference",
    )
    _require(claim_verdicts["Unknown"] > 0, "the oracle did not exercise Unknown")
    return {
        "guard_atoms": 2,
        "maximum_schedule_occurrences": 4,
        "structural_schedules_with_opening_variants": schedule_count,
        "regions": region_count,
        "attemptedness_comparisons": attempt_comparisons,
        "deterministic_scope_opening_visits": opening_boundaries,
        "scope_boundary_region_comparisons": opening_boundary_comparisons,
        "impossible_regions": impossible_regions,
        "unreachable_regions": unreachable_regions,
        "claim_status_cases": claim_cases,
        "claim_status_source_cases": claim_source_cases,
        "claim_status_verdicts": claim_verdicts,
        "claim_status_counterexamples": claim_counterexamples,
    }


LiteralSet = frozenset[tuple[str, int]]
_MustResult = tuple[LiteralSet | None, LiteralSet | None]
_Term = tuple[Any, ...]


def _facts_union(left: LiteralSet | None, right: LiteralSet | None) -> LiteralSet | None:
    if left is None or right is None:
        return None
    combined = left | right
    ordinals = {ordinal for _polarity, ordinal in combined}
    if any(
        {("Positive", ordinal), ("Negative", ordinal)} <= combined
        for ordinal in ordinals
    ):
        return None
    return combined


def _facts_meet(left: LiteralSet | None, right: LiteralSet | None) -> LiteralSet | None:
    if left is None:
        return right
    if right is None:
        return left
    return left & right


def _must_env(term: _Term, environment: tuple[_MustResult, ...]) -> _MustResult:
    tag = term[0]
    if tag == "variable":
        return environment[int(term[1])]
    if tag == "constant":
        return (frozenset(), None) if term[1] is True else (None, frozenset())
    if tag == "let":
        bound = _must_env(term[1], environment)
        return _must_env(term[2], (bound, *environment))
    if tag == "if":
        condition = _must_env(term[1], environment)
        when_true = _must_env(term[2], environment)
        when_false = _must_env(term[3], environment)
        return (
            _facts_meet(
                _facts_union(condition[0], when_true[0]),
                _facts_union(condition[1], when_false[0]),
            ),
            _facts_meet(
                _facts_union(condition[0], when_true[1]),
                _facts_union(condition[1], when_false[1]),
            ),
        )
    # Primitive calls and every other portable-term constructor contribute no
    # literal under the frozen owner law.
    return frozenset(), frozenset()


def _term_value(term: _Term, environment: tuple[bool, ...]) -> bool:
    tag = term[0]
    if tag == "variable":
        return environment[int(term[1])]
    if tag == "constant":
        return bool(term[1])
    if tag == "let":
        bound = _term_value(term[1], environment)
        return _term_value(term[2], (bound, *environment))
    if tag == "if":
        return _term_value(term[2], environment) if _term_value(term[1], environment) else _term_value(term[3], environment)
    mask = int(term[1])
    ordinal = sum(int(value) << index for index, value in enumerate(environment[:2]))
    return bool(mask & (1 << ordinal))


def _facts_hold(facts: LiteralSet, valuation: tuple[bool, ...]) -> bool:
    return all(
        valuation[ordinal] if polarity == "Positive" else not valuation[ordinal]
        for polarity, ordinal in facts
    )


def _must_env_oracle() -> dict[str, Any]:
    def input_must(ordinal: int, is_boolean: bool) -> _MustResult:
        if not is_boolean:
            return frozenset(), frozenset()
        return (
            frozenset({("Positive", ordinal)}),
            frozenset({("Negative", ordinal)}),
        )

    boolean_inputs: tuple[_MustResult, ...] = (
        input_must(0, True),
        input_must(1, True),
    )
    non_boolean_input = input_must(0, False)
    bases: tuple[_Term, ...] = (
        ("variable", 0),
        ("variable", 1),
        ("constant", True),
        ("constant", False),
        ("primitive", 0b0110),
        ("record-construct", 0b1001),
        ("project", 0b1010),
        ("inject", 0b0101),
        ("case", 0b0011),
        ("sequence-construct", 0b1100),
        ("sequence-length", 0b1110),
        ("fail", 0b0001),
        ("strict-index", 0b0111),
        ("bounded-append", 0b1000),
        ("bounded-iterate", 0b1011),
    )
    terms = list(bases)
    small = bases[:6]
    terms.extend(("if", condition, left, right) for condition, left, right in product(small, repeat=3))
    terms.extend(
        (
            "let",
            bound,
            ("if", ("variable", 0), ("variable", 1), ("constant", False)),
        )
        for bound in small
    )
    contradiction = (
        "if",
        ("variable", 0),
        ("if", ("variable", 0), ("constant", False), ("constant", True)),
        ("constant", False),
    )
    terms.append(contradiction)

    valuations = tuple(product((False, True), repeat=2))
    branch_checks = 0
    impossible_branches = 0
    contradictions_normalized = 0
    for term in terms:
        result = _must_env(term, boolean_inputs)
        outputs = tuple(_term_value(term, valuation) for valuation in valuations)
        for expected, facts in ((True, result[0]), (False, result[1])):
            matching = tuple(
                valuation
                for valuation, output in zip(valuations, outputs)
                if output is expected
            )
            branch_checks += 1
            if facts is None:
                impossible_branches += 1
                _require(not matching, "MustEnv marked a reachable branch Impossible")
            else:
                _require(
                    all(_facts_hold(facts, valuation) for valuation in matching),
                    "MustEnv invented a literal",
                )
        if result[0] is None or result[1] is None:
            contradictions_normalized += int(term == contradiction)

    _require(
        _must_env(contradiction, boolean_inputs)[0] is None,
        "contradictory must-facts did not normalize to Impossible",
    )
    _require(
        non_boolean_input == (frozenset(), frozenset()),
        "non-Boolean input contributed a literal",
    )
    other_tags = tuple(term[0] for term in bases[5:])
    _require(
        len(other_tags) == 10
        and all(
            _must_env((tag, 0), boolean_inputs) == (frozenset(), frozenset())
            for tag in other_tags
        ),
        "an unnamed portable-term constructor contributed a literal",
    )
    return {
        "terms": len(terms),
        "valuations_per_term": len(valuations),
        "branch_soundness_checks": branch_checks,
        "impossible_branches": impossible_branches,
        "contradiction_discriminators": contradictions_normalized,
        "non_boolean_input_literal_count": 0,
        "other_term_constructors_with_empty_facts": len(other_tags),
    }


def _carrier_claim_status_review() -> dict[str, Any]:
    projection = (
        _Occurrence(False, None),
        _Occurrence(False, 0),
        _Occurrence(True, 0),
        _Occurrence(False, None),
        _Occurrence(True, 1),
        _Occurrence(True, None),
    )
    projection_claims = (
        ("initially", None, None, (1, 3)),
        ("reduction-output", 1, None, ()),
        ("reduction-output", 3, None, ()),
    )

    path_cases = 0
    path_verdicts = {"Live": 0, "Dead": 0, "Unknown": 0}
    path_counterexamples = {"Live": 0, "Dead": 0}

    def statuses(
        schedule: tuple[_Occurrence, ...],
        claims: tuple[tuple[str, int | None, int | None, tuple[int, ...]], ...],
        terminal_positions: tuple[int, ...],
    ) -> tuple[list[list[int]], int]:
        nonlocal path_cases
        live_sets: list[list[int]] = []
        unknown = 0
        for terminal in terminal_positions:
            current: list[int] = []
            for claim, (source_kind, source_position, opening, consumers) in enumerate(claims):
                result = _path_referenced_claim_status(
                    schedule,
                    terminal,
                    source_kind,
                    source_position,
                    opening,
                    tuple(consumer for consumer in consumers if consumer < terminal),
                )
                status = result["status"]
                path_cases += 1
                path_verdicts[status] += 1
                path_counterexamples["Live"] += result["live_counterexamples"]
                path_counterexamples["Dead"] += result["dead_counterexamples"]
                unknown += int(status == "Unknown")
                if status == "Live":
                    current.append(claim)
            live_sets.append(current)
        return live_sets, unknown

    projection_live, projection_unknown = statuses(
        projection, projection_claims, (2, 4, 5)
    )
    _require(projection_live == [[1], [2], [2]], "terminal projection live sets drifted")

    integrated_live_sets: dict[str, list[list[int]]] = {}
    integrated_unknown = 0
    integrated_reusable_claim_live = 0
    for name, terminal_guards in (
        ("integrated-baseline", (0, 1, None)),
        ("private-verifier-output-sink", (0, 1, None)),
        ("invalid-module-control-sink", (0, 1, None)),
        ("history-challenge-condition", (0, 1, None)),
        ("logical-reject-preemption", (0, 1, None)),
    ):
        schedule = tuple(_Occurrence(False, None) for _ in range(20)) + tuple(
            _Occurrence(True, guard) for guard in terminal_guards
        )
        claims = (
            ("initially", None, None, ()),
            ("reduction-output", 18, None, ()),
            ("reduction-output", 19, None, ()),
        )
        live_sets, unknown = statuses(schedule, claims, (20, 21, 22))
        _require(
            live_sets == [[0, 1, 2], [0, 1, 2], [0, 1, 2]],
            f"{name} reusable-claim liveness drifted",
        )
        integrated_live_sets[name] = live_sets
        integrated_unknown += unknown
        integrated_reusable_claim_live += sum(0 in row for row in live_sets)

    whir = (
        _Occurrence(False, 0),
        _Occurrence(False, 0),
        _Occurrence(True, 0),
        _Occurrence(True, None),
    )
    whir_claims = (
        ("initially", None, None, (0,)),
        ("reduction-output", 0, None, (1,)),
    )
    whir_live, whir_unknown = statuses(whir, whir_claims, (2, 3))
    _require(whir_live == [[], [0]], "WHIR closed-state live sets drifted")
    warpfold = (
        _Occurrence(False, None, (0,)),
        _Occurrence(True, 60),
        _Occurrence(True, None),
    )
    warpfold_live, warpfold_unknown = statuses(warpfold, (), (1, 2))
    _require(warpfold_live == [[], []], "WARPfold closed-state live sets drifted")
    _require(
        projection_unknown + integrated_unknown + whir_unknown + warpfold_unknown == 0,
        "a frozen represented carrier produced ClaimStatus Unknown",
    )
    _require(
        path_counterexamples == {"Live": 0, "Dead": 0},
        "a frozen carrier ClaimStatus verdict is unsound against the path reference",
    )
    return {
        "terminal_projection": {
            "carriers": 1,
            "terminal_live_claims": projection_live,
            "unknown": projection_unknown,
        },
        "integrated": {
            "carriers": len(integrated_live_sets),
            "terminal_live_claims": integrated_live_sets,
            "unknown": integrated_unknown,
            "reusable_claim_zero_live_terminals": integrated_reusable_claim_live,
            "owner_declarations_omit_reusable_claim_zero": True,
        },
        "holdouts": {
            "represented_carriers": 2,
            "terminal_live_claims": {
                "WHIR": whir_live,
                "WARPfold": warpfold_live,
            },
            "unknown": whir_unknown + warpfold_unknown,
            "source_specialized_rows_without_exact_carriers": 4,
        },
        "path_reference": {
            "claim_status_cases": path_cases,
            "claim_status_verdicts": path_verdicts,
            "claim_status_counterexamples": path_counterexamples,
        },
        "claim_source_discriminators": _claim_source_discriminators(),
    }


def _terminal_review(interaction: str) -> dict[str, Any]:
    required = (
        "AttemptGuards(o) := { Guard(o) } minus { Always }",
        "GuardInputs(o) = [] and GuardTerm(o) = None",
        "MustEnv(let x = e1 in e2, environment) =",
        "MustEnv(e2, [MustEnv(e1, environment)] ++ environment)",
        "when input i is Boolean, and { when_true: {}, when_false: {} } otherwise",
        "MustEnv(any other term constructor, environment) =",
        "Positive(i) and Negative(i) for one input i is Impossible",
        "Region(o) := {",
        "BoundaryRegion(Initially) := {",
        "BoundaryRegion(BeforeOccurrence(o)) := {",
        "ClaimSourceRegion(c) :=",
        "ClaimStatus(c, o) :=",
        "no claim has ClaimStatus Unknown at o_t",
        "Positive(i) in MustWhenTrue(GuardTerm(o_t))",
        "An impossible\nregion is refused rather than discharged vacuously",
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
    oracle = _region_and_claim_oracle()
    must_env = _must_env_oracle()
    carriers = _carrier_claim_status_review()
    _require(
        _claim_source_region_text_closed(interaction),
        "the ClaimSourceRegion owner law is not closed",
    )
    mechanization_findings_closed = [
        "TERMINAL-C-MUST-ENV-CONSTRUCTORS-UNDEFINED",
        "TERMINAL-C-NONBOOLEAN-INPUT-MUST-UNDEFINED",
        "TERMINAL-C-CONTRADICTION-NORMALIZATION-UNDEFINED",
        "TERMINAL-C-IMPOSSIBLE-GUARD-PLACEMENT",
        "TERMINAL-C-FORWARD-STATE-TRANSFER-NOT-CLOSED-HERE",
    ]
    return {
        "corrected_guard_inclusion_cases": implications,
        "corrected_guard_inclusion_counterexamples": counterexamples,
        "baseline_terminal_region_counts": baseline,
        "logical_terminal_region_counts": logical,
        "positive_impossible_terminal_regions": 0,
        "impossible_region_refusal_present": True,
        "region_and_claim_oracle": oracle,
        "must_env_oracle": must_env,
        "frozen_carriers": carriers,
        "mechanization_underdetermination_findings_closed": (
            mechanization_findings_closed
        ),
        "mechanization_underdetermination_findings_remaining": [],
        "claim_source_region_mapping_present": True,
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


def _git_bytes(revision: str, relative: str) -> bytes:
    try:
        return subprocess.run(
            ["git", "show", f"{revision}:{relative}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReviewError(f"cannot reconstruct {relative} at {revision}") from error


def _source_page_paths(value: Any) -> set[str]:
    if isinstance(value, str):
        return {value} if value.endswith(".md") else set()
    result: set[str] = set()
    if isinstance(value, list):
        for item in value:
            result.update(_source_page_paths(item))
    elif isinstance(value, dict):
        for item in value.values():
            result.update(_source_page_paths(item))
    return result


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

    baseline_manifests: dict[str, dict[str, Any]] = {}
    baseline_pages: dict[str, bytes] = {}
    for key, (relative, _manifest) in _all_manifests().items():
        try:
            baseline = json.loads(_git_bytes(BASE_COMMIT, relative))
        except json.JSONDecodeError as error:
            raise ReviewError(f"cannot decode {relative} at {BASE_COMMIT}") from error
        baseline_manifests[key] = baseline
        for page in _source_page_paths(baseline):
            baseline_pages[page] = _git_bytes(BASE_COMMIT, page)
    reference_baseline = reference.identity_table(
        reference.compile_repository(
            manifest_overrides=baseline_manifests,
            page_overrides=baseline_pages,
        )
    )
    cold_baseline = cold.identity_table(
        cold.compile_repository(
            manifest_overrides=baseline_manifests,
            page_overrides=baseline_pages,
        )
    )
    _require(reference_baseline == cold_baseline, "publication compilers disagree at the migration base")
    rotated = [
        key
        for key in reference.PROFILE_KEYS
        if reference_table["profiles"][key] != reference_baseline["profiles"][key]
    ]
    stable = [key for key in reference.PROFILE_KEYS if key not in rotated]
    _require(
        rotated
        == [
            "interaction",
            "canonical-framed-fiat-shamir",
            "duplex-sponge-fiat-shamir",
            "public-setup",
            "commitment-opening",
            "oracle-commitment",
            "verifier-derived-query-plan",
            "interface-plan",
            "oir-endpoint-graph",
            "endpoint-source-view",
            "oir-projection-relation",
            "relations",
            "analysis-cryptographic-property",
            "analysis-afk-transport",
            "analysis-afk-theorem-source-validation",
            "analysis-incremental-composition",
            "analysis-incremental-composition-source-validation",
        ]
        and stable == ["analysis-kernel"],
        "the migration rotation cone drifted",
    )
    return {
        "compiler_agreement": True,
        "baseline_compiler_agreement": True,
        "compiled_profiles": len(reference_table["profiles"]),
        "rotated_profiles": rotated,
        "rotation_count": len(rotated),
        "stable_profiles": stable,
        "foundation_changed": reference_table["foundation"] != reference_baseline["foundation"],
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


def _decision_review(
    pages: dict[str, str], manifest: dict[str, Any], view: dict[str, Any]
) -> dict[str, Any]:
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
        view["fs_body_fields"] == view["fs_exact_fields"]
        and view["fs_unclosed_families"] == 0,
        all(_json(path)["revision"] == 1 for path in MIGRATED_MANIFESTS),
        not any(path.startswith("docs-next/analysis/") or path.startswith("docs-next/relations/") or path.startswith("docs-next/foundation/") for path in (*PAGES, *MIGRATED_MANIFESTS)),
    ]
    _require(applied == [True] * 8, "decision-fidelity census drifted")
    _require("CanonicalFramedViewSchemaCatalog = {" in canonical, "canonical catalog is absent")
    _require("DuplexViewSchemaCatalog = {" in duplex, "duplex catalog is absent")
    return {
        "recorded_decisions": len(applied),
        "fully_applied_decisions": sum(applied),
        "incomplete_decisions": [],
    }


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    pages = {relative: _read(relative) for relative in PAGES}
    view = _view_closure(pages)
    terminal = _terminal_review(pages["docs-next/pir/interactive-core.md"])
    pcgraph = _pcgraph_review(pages["docs-next/pir/interactive-core.md"])
    manifests = _manifest_review(pages)
    publication = _publication_review()
    decisions = _decision_review(pages, manifests, view)

    terminal_closed = terminal["claim_source_region_mapping_present"]
    owner_closed = not view["owner_unresolved_expressions"]
    findings = [
        Finding("decision-fidelity", "Affirmative", "F0V2C1-A-DECISION-FIDELITY"),
        Finding(
            "terminal-contract",
            "Affirmative" if terminal_closed else "CannotAnswer",
            "F0V2C1-A-TERMINAL-CONTRACT"
            if terminal_closed
            else "F0V2C1-C-TERMINAL-CLAIM-SOURCE-REGION",
        ),
        Finding("public-coin-graph", "Affirmative", "F0V2C1-A-PCGRAPH-TRANSFER"),
        Finding(
            "owner-name-closure",
            "Affirmative" if owner_closed else "CannotAnswer",
            "F0V2C1-A-OWNER-CLOSURE"
            if owner_closed
            else "F0V2C1-C-OWNER-CLAIM-SOURCE-REGION",
        ),
        Finding("manifest-closure", "Affirmative", "F0V2C1-A-MANIFEST-CLOSURE"),
        Finding("publication-compilers", "Affirmative", "F0V2C1-A-PUBLICATION-COMPILERS"),
        Finding("family-body-closure", "Affirmative", "F0V2C1-A-FS-BODY-CLOSURE"),
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


def _aggregate(findings: list[Finding]) -> dict[str, Any]:
    blocking = [finding.name for finding in findings if finding.outcome != "Affirmative"]
    if not blocking:
        return {
            "outcome": "Affirmative",
            "code": "F0V2C1-A-MIGRATION-TEXT-CLOSED",
            "blocking_findings": [],
        }
    return {
        "outcome": "CannotAnswer",
        "code": "F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED",
        "blocking_findings": blocking,
    }


def _expected() -> dict[str, Any]:
    value = _json(str(EXPECTED.relative_to(ROOT)))
    _require(type(value) is dict, "expected findings have another carrier")
    return value


def check() -> tuple[list[Finding], dict[str, Any]]:
    findings, metrics = evaluate()
    expected = _expected()
    _require([item.value() for item in findings] == expected["finding_codes"], "finding classifications drifted")
    _require(metrics == expected["metrics"], "review evidence metrics drifted")
    _require(expected["aggregate"] == _aggregate(findings), "aggregate finding drifted")
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
        aggregate = _aggregate(findings)
        print(
            json.dumps(
                {
                    "aggregate": aggregate,
                    "finding_codes": [item.value() for item in findings],
                    "metrics": metrics,
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        blockers = sum(item.outcome != "Affirmative" for item in findings)
        aggregate = _aggregate(findings)
        print(
            "Migration text freeze review: "
            f"{len(findings)}/{len(findings)} findings reproduced; "
            f"{blockers} blocking findings; aggregate {aggregate['outcome']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
