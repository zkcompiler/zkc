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
MIGRATION_BASE_COMMIT = "b82ce5e"
ROUND_SEVEN_COMMIT = "0590fc5f"
ROUND_EIGHT_COMMIT = "16eed00f"

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
ANALYSIS_PAGE = "docs-next/analysis/cryptographic-properties.md"
ANALYSIS_READ_CATALOG_CONTROL = "checks/tests/test_analysis_owner_read_catalog.py"
SOURCE_IDENTITY_CONTROL = "checks/tests/test_pir_source_identity_constructors.py"
PROTOCOL_REFERENCE_MODEL = "evaluation/k2-protocol-fiat-shamir/reference_model.py"
ANALYSIS_REFERENCE_MODEL = "evaluation/k3-analysis-closure/reference_model.py"
PIR_MARKDOWN_PAGES = tuple(
    str(path.relative_to(ROOT))
    for path in sorted((ROOT / "docs-next" / "pir").glob("*.md"))
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
        for relative in dict.fromkeys(
            (
                *PAGES,
                *PIR_MARKDOWN_PAGES,
                FOUNDATION,
                ANALYSIS_PAGE,
                ANALYSIS_READ_CATALOG_CONTROL,
                SOURCE_IDENTITY_CONTROL,
                PROTOCOL_REFERENCE_MODEL,
                ANALYSIS_REFERENCE_MODEL,
                *MIGRATED_MANIFESTS,
                *PACKET_SOURCES,
            )
        )
    }


def _canonical_sha256(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _definition_count(text: str, symbol: str) -> int:
    return len(
        re.findall(
            rf"^[ \t]*{re.escape(symbol)}(?:\([^\n]*\))?[ \t]*(?::=|=)",
            text,
            flags=re.MULTILINE,
        )
    )


def _line_number(text: str, needle: str) -> int:
    position = text.find(needle)
    return 1 if position < 0 else text.count("\n", 0, position) + 1


def _definition_block(text: str, symbol: str) -> tuple[str, int]:
    match = re.search(rf"^{re.escape(symbol)} = \{{", text, flags=re.MULTILINE)
    _require(match is not None, f"body {symbol} is absent")
    assert match is not None
    depth = 0
    end = match.end()
    for position in range(match.end() - 1, len(text)):
        character = text[position]
        depth += character == "{"
        depth -= character == "}"
        if depth == 0:
            end = position + 1
            break
    _require(depth == 0, f"body {symbol} is not closed")
    return text[match.start() : end], text.count("\n", 0, match.start()) + 1


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


CORE_LOCAL_REFERENCE_TYPES = (
    "ScopeRef",
    "OccurrenceRef",
    "ProverDecisionPointRef",
    "ChallengeRef",
    "BindingRef",
    "ClaimRef",
    "ReductionRef",
    "CheckRef",
    "TerminalRef",
    "OracleRef",
    "PublicInputRef",
    "VerifierPrivateInputRef",
    "ConstantRef",
    "DerivedValueRef",
)

LAW_SELECTION_CONFIG: dict[str, dict[str, Any]] = {
    "interaction": {
        "page": "docs-next/pir/interactive-core.md",
        "manifest": "docs-next/pir/profiles/interaction.json",
        "table": "PIRStaticViewLawFieldSelection(Interaction)",
        "ordinal_base": "c32fec65^",
        "new_laws": {
            "visible-history-v0",
            "prover-view-formation-v0",
            "replay-qualification-v0",
        },
        "views": {
            "PublicBindingView": ("PublicBindingViewBody", "public-binding-view-v0"),
            "StrategyDecisionView": ("StrategyDecisionViewBody", "strategy-decision-view-v0"),
            "PublicCoinView": ("PublicCoinViewBody", "public-coin-view-v0"),
            "EffectView": ("EffectViewBody", "effect-view-v0"),
            "ClaimReductionView": ("ClaimReductionViewBody", "claim-reduction-view-v0"),
            "ExecutionView": ("ExecutionViewBody", "execution-view-v0"),
        },
        "fields": (
            ("StrategyDecisionView", "prover_view_formation_law", "interaction", "prover-view-formation-v0"),
            ("ExecutionView", "visible_history_law", "interaction", "visible-history-v0"),
            ("ExecutionView", "generated_execution_law", "interaction", "execution-and-replay-v0"),
            ("ExecutionView", "replay_qualification_law", "interaction", "replay-qualification-v0"),
            ("ExecutionView", "relation_run_view_issuance_law", "interaction", "run-view-issuance-v0"),
        ),
    },
    "canonical-framed-fiat-shamir": {
        "page": "docs-next/pir/fiat-shamir.md",
        "manifest": "docs-next/pir/profiles/canonical-framed-fiat-shamir.json",
        "table": "PIRStaticViewLawFieldSelection(CanonicalFramedFiatShamir)",
        "ordinal_base": "5105247d^",
        "new_laws": {
            "canonical-framed-protocol-execution-v0",
            "canonical-framed-replay-v0",
        },
        "views": {
            "TranscriptDeclarationView": ("TranscriptDeclarationViewBody", "transcript-declaration-view-v0"),
            "RequiredInfluenceView": ("RequiredInfluenceViewBody", "required-influence-view-v0"),
            "ChallengeTransitionView": ("ChallengeTransitionViewBody", "challenge-transition-view-v0"),
            "FSConstructionView": ("FSConstructionViewBody", "fs-construction-view-v0"),
            "ExecutionView": ("CanonicalFramedExecutionViewBody", "execution-view-v0"),
        },
        "fields": (
            ("TranscriptDeclarationView", "initialization_schedule_law", "canonical-framed-fiat-shamir", "canonical-framed-body-grammar-v0"),
            ("TranscriptDeclarationView", "frame_body_law", "canonical-framed-fiat-shamir", "canonical-framed-body-grammar-v0"),
            ("RequiredInfluenceView", "exact_prefix_law", "canonical-framed-fiat-shamir", "canonical-framed-prefix-and-domain-v0"),
            ("ChallengeTransitionView", "namespace_derivation_law", "canonical-framed-fiat-shamir", "canonical-framed-prefix-and-domain-v0"),
            ("ChallengeTransitionView", "exact_length_law", "canonical-framed-fiat-shamir", "canonical-framed-body-grammar-v0"),
            ("ChallengeTransitionView", "state_update_before_decode_law", "canonical-framed-fiat-shamir", "canonical-framed-admission-and-execution-v0"),
            ("ChallengeTransitionView", "retry_law", "canonical-framed-fiat-shamir", "canonical-framed-admission-and-execution-v0"),
            ("ChallengeTransitionView", "sampling_failure_law", "canonical-framed-fiat-shamir", "canonical-framed-admission-and-execution-v0"),
            ("FSConstructionView", "structural_conclusion.law", "canonical-framed-fiat-shamir", "canonical-framed-same-core-construction-v0"),
            ("ExecutionView", "visible_history_law", "interaction", "visible-history-v0"),
            ("ExecutionView", "generated_execution_law", "canonical-framed-fiat-shamir", "canonical-framed-protocol-execution-v0"),
            ("ExecutionView", "replay_qualification_law", "canonical-framed-fiat-shamir", "canonical-framed-replay-v0"),
            ("ExecutionView", "relation_run_view_issuance_law", "interaction", "run-view-issuance-v0"),
        ),
    },
    "duplex-sponge-fiat-shamir": {
        "page": "docs-next/pir/duplex-sponge-fiat-shamir.md",
        "manifest": "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json",
        "table": "PIRStaticViewLawFieldSelection(DuplexSpongeFiatShamir)",
        "ordinal_base": "5105247d^",
        "new_laws": {
            "duplex-sponge-prover-required-prefix-v0",
            "duplex-sponge-same-core-construction-v0",
            "duplex-sponge-protocol-execution-v0",
            "duplex-sponge-replay-v0",
        },
        "views": {
            "DuplexTranscriptDeclarationView": ("DuplexTranscriptDeclarationViewBody", "duplex-transcript-declaration-view-v0"),
            "DuplexEncodedInputCoverageView": ("DuplexEncodedInputCoverageViewBody", "duplex-encoded-input-coverage-view-v0"),
            "DuplexChallengeTransitionView": ("DuplexChallengeTransitionViewBody", "duplex-challenge-transition-view-v0"),
            "DuplexFSConstructionView": ("DuplexFSConstructionViewBody", "duplex-fs-construction-view-v0"),
            "ExecutionView": ("DuplexExecutionViewBody", "execution-view-v0"),
        },
        "fields": (
            ("DuplexTranscriptDeclarationView", "state_carrier.invariant_law", "duplex-sponge-fiat-shamir", "duplex-sponge-state-transition-v0"),
            ("DuplexTranscriptDeclarationView", "instance_carrier.bit_convention_law", "duplex-sponge-fiat-shamir", "duplex-sponge-body-grammar-v0"),
            ("DuplexTranscriptDeclarationView", "instance_binding_projection.law", "duplex-sponge-fiat-shamir", "duplex-sponge-source-views-v0"),
            ("DuplexTranscriptDeclarationView", "fixed_start_absorb_squeeze_law", "duplex-sponge-fiat-shamir", "duplex-sponge-state-transition-v0"),
            ("DuplexTranscriptDeclarationView", "edge_case_law", "duplex-sponge-fiat-shamir", "duplex-sponge-state-transition-v0"),
            ("DuplexEncodedInputCoverageView", "prover_required_prefix_law", "duplex-sponge-fiat-shamir", "duplex-sponge-prover-required-prefix-v0"),
            ("DuplexEncodedInputCoverageView", "verifier_complete_schedule_law", "duplex-sponge-fiat-shamir", "duplex-sponge-state-transition-v0"),
            ("DuplexChallengeTransitionView", "decoder_totality_law", "duplex-sponge-fiat-shamir", "duplex-sponge-admission-and-execution-v0"),
            ("DuplexChallengeTransitionView", "decode_after_state_transition_law", "duplex-sponge-fiat-shamir", "duplex-sponge-state-transition-v0"),
            ("DuplexFSConstructionView", "prover_schedule_correspondence.law", "duplex-sponge-fiat-shamir", "duplex-sponge-downstream-boundary-v0"),
            ("DuplexFSConstructionView", "verifier_schedule_correspondence.law", "duplex-sponge-fiat-shamir", "duplex-sponge-downstream-boundary-v0"),
            ("DuplexFSConstructionView", "instance_projection.law", "duplex-sponge-fiat-shamir", "duplex-sponge-same-core-construction-v0"),
            ("DuplexFSConstructionView", "structural_conclusion.law", "duplex-sponge-fiat-shamir", "duplex-sponge-admission-and-execution-v0"),
            ("ExecutionView", "visible_history_law", "interaction", "visible-history-v0"),
            ("ExecutionView", "generated_execution_law", "duplex-sponge-fiat-shamir", "duplex-sponge-protocol-execution-v0"),
            ("ExecutionView", "replay_qualification_law", "duplex-sponge-fiat-shamir", "duplex-sponge-replay-v0"),
            ("ExecutionView", "relation_run_view_issuance_law", "interaction", "run-view-issuance-v0"),
        ),
    },
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


def _interface_completion_review(pages: dict[str, str]) -> dict[str, Any]:
    """Derive the repaired failure presentation from the owner execution law."""

    interface = pages["docs-next/pir/interfaces-and-plans.md"]
    canonical = pages["docs-next/pir/fiat-shamir.md"]
    interaction = pages["docs-next/pir/interactive-core.md"]
    foundation = _read(FOUNDATION)
    coordinate_block = interface.split("CompletionPayloadCoordinate =", 1)[1].split(
        "CompletionEntry =", 1
    )[0]
    coordinates = re.findall(r"(?:^|\n)\s*(?:\|\s*)?([A-Z][A-Za-z0-9_]+)", coordinate_block)
    expected_coordinates = [
        "TerminalPublicOutput",
        "FSFailureDomainPayload",
        "FSFailureChallenge",
        "FSFailurePrefixReceiptCount",
        "FSFailurePrefixState",
        "FSFailureFinalState",
    ]
    _require(coordinates == expected_coordinates, "completion coordinate list drifted")

    body_tail = interface.split("CompletionPayloadCoordinateBody(x) =", 1)[1].split(
        "CompletionEntryBody(x)", 1
    )[0]
    body_arms = [int(item) for item in re.findall(r"V\((\d+),", body_tail)]
    _require(body_arms == list(range(6)), "completion coordinate body arms drifted")

    for snippet in (
        "Worst(Seq(t,c)) = (",
        "Worst(Record(fields)) = (",
        "Worst(Variant(cases)) = (",
        "bytes<=1048576",
    ):
        _require(snippet in foundation, "Foundation Worst-tuple law drifted")
    _require(
        "17 + MaxDatumBytes(TranscriptStateType) <= 2^20" in canonical,
        "transcript-state completion preflight drifted",
    )

    for snippet in (
        "FSChallengeRefType = ValueType(\n  Root(B.semantic_regime.id,\n"
        '       "foundation.root-value-domain", 2),\n  Nat(2^14 - 1))',
        "FSDrawCountType = ValueType(\n  Root(B.semantic_regime.id,\n"
        '       "foundation.root-value-domain", 2),\n  Nat(2^20))',
        "SamplingExhaustedPayloadType = ValueType(\n"
        "  Root(B.semantic_regime.id,\n"
        '       "foundation.root-value-domain", 7),\n'
        "  Record { 0: FSChallengeRefType, 1: FSDrawCountType })",
    ):
        _require(snippet in canonical, "a fixed failure-coordinate type drifted")

    # Independently evaluate the Appendix A.2 equations instead of accepting
    # the Interface paragraph's admissibility conclusion.
    Schema = tuple[Any, ...]
    Worst = tuple[int, int, int, int]

    def magnitude(value: int) -> int:
        return max(1, (value.bit_length() + 7) // 8)

    def worst(schema: Schema) -> Worst:
        tag = schema[0]
        if tag == "nat":
            return (9 + magnitude(int(schema[1])), 1, 0, 0)
        if tag == "record":
            children = [worst(child) for child in schema[1]]
            return (
                9 + sum(16 + child[0] for child in children),
                1 + sum(child[1] for child in children),
                len(children) + sum(child[2] for child in children),
                0 if not children else 1 + max(child[3] for child in children),
            )
        raise ReviewError(f"completion review has no Worst rule for {tag}")

    challenge_schema: Schema = ("nat", (1 << 14) - 1)
    count_schema: Schema = ("nat", 1 << 20)
    failure_payload_schema: Schema = (
        "record",
        (challenge_schema, count_schema),
    )
    challenge_worst = worst(challenge_schema)
    count_worst = worst(count_schema)
    failure_payload_worst = worst(failure_payload_schema)
    constitutional_bounds = (1 << 20, 1 << 14, 1 << 14, 384)
    _require(
        all(
            measure[index] <= bound
            for measure in (challenge_worst, count_worst, failure_payload_worst)
            for index, bound in enumerate(constitutional_bounds)
        ),
        "a fixed completion coordinate exceeds a Foundation Worst bound",
    )
    state_types_admitted = all(
        snippet in canonical
        for snippet in (
            "17 + MaxDatumBytes(TranscriptStateType) <= 2^20",
            "preflight each exact\n   K1 maximum tagged-completion schema",
        )
    )
    terminal_output_types_admitted = all(
        snippet in text
        for text, snippet in (
            (
                interface,
                "selects the exact canonical value and K2\n"
                "`ValueType` of the `o`th public output",
            ),
            (
                interaction,
                "type constants, inputs, derived values, guards, messages, checks,\n"
                "   challenges, Oracle origins and modes, exact logical-access domain laws,\n"
                "   claims, reductions, terminals, and occurrence outputs",
            ),
        )
    )
    _require(state_types_admitted, "state-coordinate Foundation preflight drifted")
    _require(
        terminal_output_types_admitted,
        "terminal output coordinate no longer inherits an admitted Foundation type",
    )

    sampling_input_block = canonical.split("SamplingInputTypes(c) =", 1)[1].split(
        "ChallengeRule =", 1
    )[0]
    sampling_input_terms = re.findall(
        r"\[(TranscriptBytesType)\]|core\.challenges\[c\]\.(public_conditions)|"
        r"core\.challenges\[c\]\.correlation\.(prior_members)",
        sampling_input_block,
    )
    normalized_sampling_terms = [next(item for item in row if item) for row in sampling_input_terms]
    _require(
        normalized_sampling_terms
        == ["TranscriptBytesType", "public_conditions", "prior_members"],
        "SamplingInputTypes(c) operand order drifted",
    )
    replay_operands = [
        "public_condition_values",
        "prior_joint_member_challenge_values",
    ]
    _require(
        all(
            snippet in interface
            for snippet in (
                "the values of the challenge's `public_conditions` and the accepted values of\n"
                "its `correlation.prior_members`",
                "the operands of the owner's\n`SamplingInputTypes(c)`",
                "Each such operand is a constant that `ProtocolId` fixes, a public\n"
                "input that Section 3.2 binds to a slot, a derived value of those, or an\n"
                "occurrence value with a transport entry of Section 3.4.",
            )
        ),
        "Interface replay-operand statement drifted",
    )

    value_ref_block = interaction.split("ValueRef =", 1)[1].split(
        "TypedValueRef =", 1
    )[0]
    value_ref_arms = re.findall(r"(?:^|\n)\s*(?:\|\s*)?([A-Z][A-Za-z]+)\(", value_ref_block)
    _require(
        value_ref_arms
        == [
            "PublicInput",
            "VerifierPrivateInput",
            "Constant",
            "Derived",
            "OccurrenceOutput",
        ],
        "Core ValueRef arms drifted",
    )
    public_condition_verifier_private_rejected = all(
        snippet in text
        for text, snippet in (
            (
                interaction,
                "Each Challenge has exactly one occurrence and one output. Its public\n"
                "conditions are available and public before that occurrence.",
            ),
            (
                interaction,
                "| VerifierPrivate  else if VerifierPrivate in deps\n"
                "  | Invalid          else if some public_condition class is not StaticPublic",
            ),
            (
                canonical,
                "require `PublicCoinEligible(core) = true",
            ),
            (
                canonical,
                "refuse any missing action, unsupported effect, invalid scope,\n"
                "   verifier-private influence, or bound crossing",
            ),
        )
    )
    _require(
        public_condition_verifier_private_rejected,
        "verifier-private challenge-condition exclusion drifted",
    )

    # Re-run the round-eight countermodel at the repaired Interface boundary.
    # Its public condition is an earlier public occurrence output.  The value is
    # available to the Core, but omission of the ExternalApplication transport
    # makes the interpretation-failure presentation inadmissible at item 6.
    occurrence_replay_operands = {("message", 0)}
    missing_transport: set[tuple[str, int, str]] = set()
    complete_transport = {("message", 0, "ExternalApplication")}

    def replay_transport_admitted(
        operands: set[tuple[str, int]],
        transport: set[tuple[str, int, str]],
    ) -> bool:
        return all((*operand, "ExternalApplication") in transport for operand in operands)

    countermodel_without_transport_refused = not replay_transport_admitted(
        occurrence_replay_operands, missing_transport
    )
    countermodel_with_transport_admitted = replay_transport_admitted(
        occurrence_replay_operands, complete_transport
    )
    _require(
        countermodel_without_transport_refused and countermodel_with_transport_admitted,
        "replay-input transport discriminator drifted",
    )
    _require(
        "for a canonical-framed\n   Protocol the replay-input transport of Section 3.5"
        in interface,
        "Interface admission item 6 no longer enforces replay-input transport",
    )

    presented = {
        "construction",
        "challenge",
        "prefix_receipt_count",
        "prefix_state",
        *replay_operands,
    }
    # This is a dependency derivation from the transition equations.  Leaves
    # not produced by another displayed equation are operation inputs.  The
    # failure target fixes exhaustion, so final_state can be obtained by
    # iterating the state transition to maximum_draws; the receipt still stores
    # every acceptance bit, which must be recomputed during replay.
    dependencies: dict[str, set[str]] = {
        "rule": {"construction", "challenge"},
        "draw_ordinal": {"rule"},
        "namespace": {"construction", "challenge", "draw_ordinal"},
        "draw_bytes": {"rule"},
        "squeezed_bytes": {
            "construction",
            "draw_pre_state",
            "namespace",
            "draw_bytes",
        },
        "draw_post_state": {
            "construction",
            "draw_pre_state",
            "namespace",
            "draw_bytes",
            "squeezed_bytes",
        },
        "accepted": {
            "rule",
            "squeezed_bytes",
            "public_condition_values",
            "prior_joint_member_challenge_values",
        },
        "draw_receipt": {
            "challenge",
            "draw_ordinal",
            "draw_bytes",
            "namespace",
            "draw_pre_state",
            "draw_post_state",
            "squeezed_bytes",
            "accepted",
        },
        "draw_pre_state": {"prefix_state", "earlier_draw_post_states"},
        "earlier_draw_post_states": {
            "construction",
            "challenge",
            "prefix_state",
        },
        "failure_final_state": {
            "construction",
            "challenge",
            "prefix_state",
        },
    }

    def roots(node: str, active: frozenset[str] = frozenset()) -> set[str]:
        _require(node not in active, "completion dependency graph contains a cycle")
        if node not in dependencies:
            return {node}
        result: set[str] = set()
        for child in dependencies[node]:
            result.update(roots(child, active | {node}))
        return result

    draw_roots = roots("draw_receipt")
    final_state_roots = roots("failure_final_state")
    missing_draw_inputs = sorted(draw_roots - presented)
    missing_final_state_inputs = sorted(final_state_roots - presented)
    _require(
        all(
            snippet in canonical
            for snippet in (
                "[draw_pre_state, namespace, rule.draw_bytes]",
                "[draw_pre_state, namespace, rule.draw_bytes, bytes]",
                "++ exact public condition values",
                "++ exact prior joint-member challenge values",
                "FS replay recomputes initialization, every frame, namespace, squeeze-bytes\n"
                "result, exact-length check, state advancement, acceptance result",
            )
        ),
        "the challenge transition inputs drifted",
    )
    return {
        "coordinate_list": coordinates,
        "coordinate_body_arms": body_arms,
        "coordinate_body_matches_list": len(coordinates) == len(body_arms),
        "presented_derivation_inputs": sorted(presented),
        "sampling_input_terms": normalized_sampling_terms,
        "sampling_inputs_without_transcript_bytes": replay_operands,
        "interface_names_exact_trailing_sampling_operands": True,
        "value_ref_arms": value_ref_arms,
        "non_occurrence_operand_classes": ["Constant", "PublicInput", "Derived"],
        "public_input_assignment_is_total": (
            "Domain(invocation_assignment) =" in interface
            and "{ Public(p) | p in core.public_inputs }" in interface
        ),
        "verifier_private_public_condition_admissible": False,
        "verifier_private_public_condition_rejection_lines": {
            "core_public_requirement": _line_number(
                interaction, "conditions are available and public before that occurrence"
            ),
            "core_transfer": _line_number(
                interaction, "| VerifierPrivate  else if VerifierPrivate in deps"
            ),
            "fiat_shamir_public_coin_gate": _line_number(
                canonical, "require `PublicCoinEligible(core) = true"
            ),
            "fiat_shamir_private_influence_refusal": _line_number(
                canonical, "verifier-private influence, or bound crossing"
            ),
        },
        "round_eight_occurrence_countermodel": {
            "operand": "OccurrenceOutput(message,0)",
            "without_external_application_transport": "Refused",
            "with_external_application_transport": "AdmissibleAtReplayInputGate",
            "admission_item": 6,
        },
        "draw_receipt_dependency_roots": sorted(draw_roots),
        "final_state_dependency_roots": sorted(final_state_roots),
        "missing_draw_inputs": missing_draw_inputs,
        "missing_final_state_inputs": missing_final_state_inputs,
        "first_missing_input_line": _line_number(
            canonical, "++ exact public condition values"
        ),
        "second_missing_input_line": _line_number(
            canonical, "++ exact prior joint-member challenge values"
        ),
        "squeeze_output_is_derived": True,
        "state_sequence_is_derived": True,
        "final_state_is_derived": not missing_final_state_inputs,
        "acceptance_evaluation_is_derived": not missing_draw_inputs,
        "fixed_type_worst_tuples": {
            "FSFailureChallenge": challenge_worst,
            "FSFailurePrefixReceiptCount": count_worst,
            "FSFailureDomainPayload": failure_payload_worst,
        },
        "constitutional_worst_bounds": constitutional_bounds,
        "state_coordinates_owner_preflighted": state_types_admitted,
        "terminal_outputs_owner_admitted": terminal_output_types_admitted,
        "all_coordinate_types_foundation_admissible": (
            state_types_admitted and terminal_output_types_admitted
        ),
        "complete": (
            not missing_draw_inputs
            and not missing_final_state_inputs
            and public_condition_verifier_private_rejected
            and countermodel_without_transport_refused
            and countermodel_with_transport_admitted
            and state_types_admitted
            and terminal_output_types_admitted
            and len(coordinates) == len(body_arms)
        ),
    }


def _source_identity_review() -> dict[str, Any]:
    """Check each source subject constructor against its profile-local compiler."""

    kind_suffix = {
        "binding-payload": "BindingPayload",
        "capability-requirement": "CapabilityRequirement",
        "no-policy": "NoPolicy",
        "policy-closure": "PolicyClosure",
    }
    site_pattern = re.compile(
        r'ProfiledSemanticId<"pir\.source-(binding-payload|capability-requirement|'
        r'no-policy|policy-closure)">\('
    )
    direct_pattern = re.compile(r"\s*B,\s*(\w+),\s*(\w+)\(\s*(\w+)\(")
    dispatched_pattern = re.compile(
        r'\s*B,\s*(\w+),\s*SourceSubjectBody\(\1,\s*"pir\.source-([a-z-]+)"\)'
        r"\(\s*(\w+)\("
    )
    compiler_pattern = re.compile(
        r"^(\w*)Source(BindingPayload|CapabilityRequirement|NoPolicy|PolicyClosure)"
        r"Body\(x\) =",
        re.MULTILINE,
    )
    arm_pattern = re.compile(r"if x = (\w+)\(y\)")

    sites = 0
    direct_sites = 0
    dispatched_sites = 0
    compiler_rows: dict[str, dict[str, list[str]]] = {}
    compiler_pages: dict[tuple[str, str], str] = {}
    for relative in PIR_MARKDOWN_PAGES:
        text = _read(relative)
        matches = list(compiler_pattern.finditer(text))
        page_compilers: dict[tuple[str, str], list[str]] = {}
        for match in matches:
            key = (match.group(1), match.group(2))
            _require(key not in page_compilers, f"{relative} repeats source compiler {key}")
            fence_end = text.find("\n```", match.end())
            _require(fence_end >= 0, f"{relative} source compiler is outside a closed fence")
            block = text[match.end() : fence_end]
            next_compiler = compiler_pattern.search(block)
            if next_compiler is not None:
                block = block[: next_compiler.start()]
            arms = arm_pattern.findall(block)
            _require(arms and "Body(x))" not in block, f"{relative} has an untagged compiler arm")
            page_compilers[key] = arms
            _require(
                key not in compiler_pages,
                f"source compiler {key} is physically defined on two PIR pages",
            )
            compiler_pages[key] = relative
            compiler_rows.setdefault(match.group(1), {})[match.group(2)] = arms

        for site in site_pattern.finditer(text):
            sites += 1
            kind = kind_suffix[site.group(1)]
            tail = text[site.end() : site.end() + 300]
            dispatched = dispatched_pattern.match(tail)
            if dispatched is not None:
                _require(site.group(1) == dispatched.group(2), "dispatcher selects another source kind")
                _require(dispatched.group(3) == "StaticView", "dispatcher receives an untagged family")
                dispatched_sites += 1
                continue
            direct = direct_pattern.match(tail)
            _require(direct is not None, f"{relative} constructor bypasses its source compiler")
            assert direct is not None
            _profile, compiler, tag = direct.groups()
            suffix = f"Source{kind}Body"
            _require(compiler.endswith(suffix), f"{relative} constructor selects another source kind")
            key = (compiler[: -len(suffix)], kind)
            _require(key in page_compilers, f"{relative} does not define {compiler}")
            _require(tag in page_compilers[key], f"{relative} compiler has no {tag} arm")
            direct_sites += 1

    _require(sites == 14, "PIR source identity constructor census drifted")
    _require(
        len(compiler_pages) == 24
        and all(set(rows) == set(kind_suffix.values()) for rows in compiler_rows.values()),
        "PIR source compiler census drifted",
    )
    expected_family_arms = {
        "CanonicalFramed": {
            kind: ["StaticView", "CheckedConstruction"] for kind in kind_suffix.values()
        },
        "Duplex": {
            kind: ["StaticView", "CheckedConstruction"] for kind in kind_suffix.values()
        },
    }
    for prefix, expected in expected_family_arms.items():
        _require(compiler_rows.get(prefix) == expected, f"{prefix} compiler arms drifted")

    # Resolve the generic static-view dispatch through each profile manifest.
    # This checks the profile-bound compiler, not merely the prose name of the
    # dispatcher at the call site.
    static_view_profiles = {
        "interaction": (
            "PIR",
            "docs-next/pir/profiles/interaction.json",
        ),
        "canonical-framed-fiat-shamir": (
            "CanonicalFramed",
            "docs-next/pir/profiles/canonical-framed-fiat-shamir.json",
        ),
        "duplex-sponge-fiat-shamir": (
            "Duplex",
            "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json",
        ),
    }
    dispatcher_bindings: dict[str, dict[str, str]] = {}
    for profile, (prefix, manifest_path) in static_view_profiles.items():
        definitions = _json(manifest_path)["definitions"]
        by_name = {
            row["name"]: row
            for row in definitions
            if row["kind"] == "pir.body-compiler"
        }
        bound: dict[str, str] = {}
        for source_kind, suffix in kind_suffix.items():
            declaration = by_name.get(f"source-{source_kind}-body-v0")
            _require(
                declaration is not None,
                f"{profile} does not bind the {source_kind} source compiler",
            )
            expected_selector = f"{prefix}Source{suffix}Body(x) ="
            _require(
                declaration["selector"] == expected_selector,
                f"{profile} binds another {source_kind} source compiler",
            )
            _require(
                "StaticView" in compiler_rows[prefix][suffix],
                f"{profile} source compiler has no StaticView arm",
            )
            bound[source_kind] = expected_selector
        dispatcher_bindings[profile] = bound

    interaction = _read("docs-next/pir/interactive-core.md")
    _require(
        all(
            snippet in interaction
            for snippet in (
                "the pir.body-compiler that owner_profile's catalog binds to the",
                "for a dependent profile that profile's own compilers",
                "constructor selects the owner profile's own bound compiler",
                "Interaction compilers below\nnever form another profile's subject",
            )
        ),
        "generic source-compiler dispatcher contract drifted",
    )

    protocol_model = _read(PROTOCOL_REFERENCE_MODEL)
    analysis_model = _read(ANALYSIS_REFERENCE_MODEL)
    _require(
        all(
            snippet in analysis_model
            for snippet in (
                "fs_execution = _affirmative_pir_view(",
                "k2.issue_execution_view(",
                "k2.ChallengeInterpretation.FIAT_SHAMIR,",
            )
        ),
        "Analysis canonical-framed execution-view call drifted",
    )
    model_selects_transcript_profile = all(
        snippet in protocol_model
        for snippet in (
            "owner_profile = (",
            "profiles.interaction\n        if interpretation is ChallengeInterpretation.FRESH",
            "else profiles.transcript_fs",
            "coordinate.semantic_profile_id == profiles.transcript_fs.identity",
        )
    )
    _require(
        model_selects_transcript_profile,
        "executable execution-view owner-profile selection drifted",
    )
    _require(
        all(
            snippet in protocol_model
            for snippet in (
                "def compile_pir_source_subject_body(",
                "payload_body = compile_pir_source_subject_body(",
                "no_policy_body = compile_pir_source_subject_body(",
                "requirement_body = compile_pir_source_subject_body(",
                "closure_body = compile_pir_source_subject_body(",
            )
        ),
        "executable source-subject compiler dispatch drifted",
    )

    k2 = _load_module(
        "_migration_review_k2",
        ROOT / PROTOCOL_REFERENCE_MODEL,
    )
    publication_model = _load_module(
        "_migration_review_source_publication",
        ROOT / "evaluation/semantic-profile-publication/reference_model.py",
    )
    publication = publication_model.compile_repository()
    k1 = k2.k1

    def encoded(value: object) -> bytes:
        return k1.encode_datum(value)

    def body_observation(value: object) -> dict[str, Any]:
        raw = encoded(value)
        return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

    def source_bundle(
        profile: object,
        owner_compiler: object,
        source_family: object,
        arm: int,
        local_payload: object,
        capability_family: str,
        consumer_id: object,
        purpose_id: object,
        binding: object | None = None,
    ) -> dict[str, Any]:
        family = k1.Symbol(capability_family)
        consumer_role_body = k1.DatumRecord(
            ((0, family), (1, k2._any_content_ref(consumer_id, "review consumer")))
        )
        purpose_role_body = k1.DatumRecord(
            ((0, family), (1, k2._any_content_ref(purpose_id, "review purpose")))
        )
        consumer_role_id = k2._authority_id(
            profile, "pir.source-consumer", consumer_role_body
        )
        purpose_role_id = k2._authority_id(
            profile, "pir.source-purpose", purpose_role_body
        )
        payload_body = k1.DatumVariant(arm, local_payload)
        no_policy_body = k1.DatumVariant(
            arm,
            k1.DatumRecord(
                ((0, k2._any_content_ref(profile.identity, "review owner profile")),)
            ),
        )
        requirement_body = k1.DatumVariant(
            arm,
            k1.DatumRecord(
                (
                    (0, k2._any_content_ref(consumer_role_id, "review consumer role")),
                    (1, k2._any_content_ref(purpose_role_id, "review purpose role")),
                )
            ),
        )
        payload_id = k2._authority_id(
            profile, "pir.source-binding-payload", payload_body
        )
        no_policy_id = k2._authority_id(
            profile, "pir.source-no-policy", no_policy_body
        )
        requirement_id = k2._authority_id(
            profile, "pir.source-capability-requirement", requirement_body
        )
        closure_body = k1.DatumVariant(
            arm,
            k1.DatumRecord(
                (
                    (0, k2._any_content_ref(payload_id, "review payload")),
                    (1, k2._any_content_ref(no_policy_id, "review no-policy")),
                    (2, k2._any_content_ref(requirement_id, "review requirement")),
                )
            ),
        )
        closure_id = k2._authority_id(
            profile, "pir.source-policy-closure", closure_body
        )
        expected_bodies = {
            k2.PIRSourceSubjectKind.BINDING_PAYLOAD: payload_body,
            k2.PIRSourceSubjectKind.CAPABILITY_REQUIREMENT: requirement_body,
            k2.PIRSourceSubjectKind.NO_POLICY: no_policy_body,
            k2.PIRSourceSubjectKind.POLICY_CLOSURE: closure_body,
        }
        for subject_kind, expected_body in expected_bodies.items():
            observed_body = k2.compile_pir_source_subject_body(
                owner_compiler,
                subject_kind,
                source_family,
                expected_body.payload,
            )
            _require(
                encoded(observed_body) == encoded(expected_body),
                f"{owner_compiler.value} {source_family.value} {subject_kind.value} "
                "differs from the owner equation",
            )
        if binding is not None:
            _require(
                binding.owner_binding_payload == payload_id
                and binding.operation_policy.owner_no_policy_declaration == no_policy_id
                and binding.capability_requirement.owner_requirement == requirement_id
                and binding.owner_policy_closure == closure_id,
                f"{owner_compiler.value} issued source-authority identities drifted",
            )
        return {
            "owner_compiler": owner_compiler.value,
            "family": source_family.value,
            "arm": arm,
            "subjects": {
                subject_kind.value: {
                    **body_observation(body),
                    "identity": {
                        k2.PIRSourceSubjectKind.BINDING_PAYLOAD: payload_id,
                        k2.PIRSourceSubjectKind.CAPABILITY_REQUIREMENT: requirement_id,
                        k2.PIRSourceSubjectKind.NO_POLICY: no_policy_id,
                        k2.PIRSourceSubjectKind.POLICY_CLOSURE: closure_id,
                    }[subject_kind].carrier(),
                    "byte_equal": True,
                }
                for subject_kind, body in expected_bodies.items()
            },
            "issued_binding_checked": binding is not None,
            "issued_binding_matches_expected": True if binding is not None else None,
        }

    checker_declarations = {
        "canonical-framed-fiat-shamir": (
            k2.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
            (
                ("pir.evaluator-signature", "canonical-framed-construction-check-v0"),
                ("pir.semantic-law", "canonical-framed-same-core-construction-v0"),
                ("pir.failure-schema", "canonical-framed-construction-defects-v0"),
            ),
            (1, 3, 1),
            k2._checked_fs_result_schema_body(),
            1871,
            "f8f79c99a8e74702367b7bfa6fc0a7ccc16427282aae23f24666c0c2ceff97fb",
            "zkcidv0:pir.checker-contract:ebe686d6fb48030f03b79f1cfe72994705c40ea2414afc59a44ff149b8dfd701",
        ),
        "duplex-sponge-fiat-shamir": (
            k2.PIRSourceOwnerCompiler.DUPLEX_SPONGE,
            (
                ("pir.evaluator-signature", "duplex-sponge-construction-check-v0"),
                ("pir.semantic-law", "duplex-sponge-same-core-construction-v0"),
                ("pir.failure-schema", "duplex-sponge-construction-defects-v0"),
            ),
            (1, 6, 1),
            k2._checked_duplex_fs_result_schema_body(),
            5243,
            "75eb2fe3aa516c17e0ae365df9bd8d4c7c218c7a8852ae39e1dc927ee5b64765",
            "zkcidv0:pir.checker-contract:393ff59dfef32f77fee523fc0708dbe591c964369fb2b9461947ff93d9c83210",
        ),
    }
    expected_checker_field_types = {
        "operation": 'ProfileDeclarationRef<"pir.evaluator-signature">',
        "law": "PIRProfileLawReference",
        "defects": 'ProfileDeclarationRef<"pir.failure-schema">',
        "result_schema": "PIRRuntimeSchema",
    }
    checker_owner_specs = {
        "canonical-framed-fiat-shamir": (
            "docs-next/pir/fiat-shamir.md",
            "CheckedFSConstructionCheckerContract",
            "CheckedFSConstructionCheckerContractId",
            "CheckedFSConstructionCheckerContractBody",
            "PIRCanonicalFramedFSProfileId",
            "exactly the description of CheckedFSConstruction",
        ),
        "duplex-sponge-fiat-shamir": (
            "docs-next/pir/duplex-sponge-fiat-shamir.md",
            "CheckedDuplexFSConstructionCheckerContract",
            "CheckedDuplexFSConstructionCheckerContractId",
            "CheckedDuplexFSConstructionCheckerContractBody",
            "PIRDuplexSpongeFSProfileId",
            "exactly the description of the checked duplex construction result",
        ),
    }
    checker_owner_definitions: dict[str, dict[str, Any]] = {}
    for key, (
        page,
        contract_symbol,
        identity_symbol,
        body_symbol,
        profile_symbol,
        result_description,
    ) in checker_owner_specs.items():
        owner_text = _read(page)
        contract_block, contract_line = _definition_block(owner_text, contract_symbol)
        field_types = _record_field_types(owner_text, contract_symbol)
        _require(
            field_types == expected_checker_field_types,
            f"{key} checker-contract field types drifted",
        )
        declarations = checker_declarations[key][1]
        _require(
            all(f"exactly this profile's {name}" in contract_block for _kind, name in declarations)
            and result_description in contract_block,
            f"{key} checker-contract declaration names drifted",
        )
        identity_equation = (
            f'{identity_symbol} =\n'
            '  ProfiledSemanticId<"pir.checker-contract">(\n'
            f"    B, {profile_symbol},\n"
            f"    {body_symbol}(contract))"
        )
        body_equation = (
            f"{body_symbol}(x) = R {{\n"
            "  0: ProfileDeclarationRefBody(x.operation),\n"
            "  1: ProfileDeclarationRefBody(x.law),\n"
            "  2: ProfileDeclarationRefBody(x.defects),\n"
            "  3: PIRDescriptionBody(x.result_schema)\n"
            "}"
        )
        binding_sentence = (
            f"The binding's `checker_contract` is exactly `{identity_symbol}`."
        )
        _require(
            identity_equation in owner_text
            and body_equation in owner_text
            and binding_sentence in owner_text,
            f"{key} checker-contract identity equation drifted",
        )
        checker_owner_definitions[key] = {
            "page": page,
            "contract_line": contract_line,
            "identity_line": _line_number(owner_text, identity_equation),
            "body_line": _line_number(owner_text, body_equation),
            "binding_line": _line_number(owner_text, binding_sentence),
            "field_types": field_types,
            "declaration_names_exact": True,
            "identity_equation_exact": True,
            "body_equation_exact": True,
            "binding_uses_identity_exactly": True,
        }
    checker_contracts: dict[str, dict[str, Any]] = {}
    checker_objects: dict[str, tuple[object, object, object]] = {}
    for key, (
        owner_compiler,
        declarations,
        expected_ordinals,
        result_schema,
        expected_bytes,
        expected_sha256,
        expected_identity,
    ) in checker_declarations.items():
        compiled = publication.profiles[key]
        ordinals = tuple(compiled.declaration_index[item] for item in declarations)
        _require(ordinals == expected_ordinals, f"{key} checker declaration ordinals drifted")
        catalogs = k1.profile_declaration_catalogs(compiled.profile)
        for (kind, name), ordinal in zip(declarations, ordinals):
            declaration = catalogs[kind].values[ordinal]
            _require(
                type(declaration) is k1.DatumRecord
                and dict(declaration.fields).get(0) == k1.Symbol(name),
                f"{key} checker declaration reference does not resolve",
            )
        expected_body = k1.DatumRecord(
            tuple(
                (
                    field,
                    k1.profile_declaration_ref_datum(
                        k1.ProfileLocalDeclarationRef(kind, ordinal)
                    ),
                )
                for field, ((kind, _name), ordinal) in enumerate(
                    zip(declarations, ordinals)
                )
            )
            + ((3, result_schema),)
        )
        observed_body = k2._checked_construction_checker_contract_body(
            compiled.profile, owner_compiler, result_schema
        )
        _require(
            encoded(observed_body) == encoded(expected_body),
            f"{key} executable checker contract differs from the owner equation",
        )
        contract_id = k2._checked_construction_checker_contract_id(
            compiled.profile, owner_compiler, result_schema
        )
        observation = body_observation(expected_body)
        _require(
            observation == {"bytes": expected_bytes, "sha256": expected_sha256}
            and contract_id.carrier() == expected_identity
            and compiled.declaration_index[
                ("pir.body-compiler", "checker-contract-body-v0")
            ]
            == 5
            and k1.Symbol("pir.checker-contract")
            in compiled.profile.supported_subject_kinds,
            f"{key} checker-contract identity route drifted",
        )
        checker_contracts[key] = {
            "declaration_references": [
                {"kind": kind, "name": name, "ordinal": ordinal}
                for (kind, name), ordinal in zip(declarations, ordinals)
            ],
            "body_compiler_ordinal": 5,
            "body": observation,
            "identity": contract_id.carrier(),
            "executable_owner_body_byte_equal": True,
        }
        checker_objects[key] = (compiled.profile, result_schema, contract_id)

    core, construction, _invocation, _strategy = k2.schnorr_fixture()
    execution_manifest = k2.required_static_view_read_closure(
        k2.StaticViewKind.EXECUTION,
        (k2.StaticViewField.EX_REPLAY,),
    )
    execution_outcome = k2.issue_execution_view(
        core,
        construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        execution_manifest,
    )
    _require(
        execution_outcome.kind is k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        "canonical-framed execution view did not issue",
    )
    issued = execution_outcome.value
    coordinate_body = k2._canonical_static_view_coordinate_body(
        issued.projection.coordinate, issued.capability._source
    )
    canonical_static_local = k1.DatumRecord(
        (
            (0, coordinate_body),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k2._static_view_field_coordinate_body(
                            coordinate_body,
                            issued.projection.coordinate.view_kind,
                            field,
                        )
                        for field in issued.projection.manifest
                    )
                ),
            ),
        )
    )
    _require(
        encoded(
            k2._static_binding_payload_local_body(
                issued.projection,
                issued.capability._source,
                k2.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
            )
        )
        == encoded(canonical_static_local),
        "canonical execution-view local payload differs from the owner equation",
    )
    source_bundles = {
        "canonical-execution-static-view": source_bundle(
            k2.K2_SEMANTIC_PROFILES.transcript_fs,
            k2.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
            k2.PIRSourceFamily.STATIC_VIEW,
            0,
            canonical_static_local,
            "static-view",
            issued.capability.consumer_id,
            issued.capability.purpose_id,
            issued.source_binding,
        )
    }

    checked_outcome = k2.check_fs_construction(core, core, construction)
    _require(
        checked_outcome.kind is k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        "canonical checked construction did not issue",
    )
    checked = checked_outcome.value
    witness_profile = k2.K2_SEMANTIC_PROFILES.transcript_fs
    witness_result_schema = k2._checked_fs_result_schema_body()
    witness_declarations = checker_declarations["canonical-framed-fiat-shamir"][1]
    witness_catalogs = k1.profile_declaration_catalogs(witness_profile)
    witness_ordinals: list[int] = []
    for kind, name in witness_declarations:
        matches = [
            ordinal
            for ordinal, declaration in enumerate(witness_catalogs[kind].values)
            if type(declaration) is k1.DatumRecord
            and dict(declaration.fields).get(0) == k1.Symbol(name)
        ]
        _require(
            len(matches) == 1,
            "runtime canonical checker declaration does not resolve uniquely",
        )
        witness_ordinals.append(matches[0])
    expected_witness_contract_body = k1.DatumRecord(
        tuple(
            (
                field,
                k1.profile_declaration_ref_datum(
                    k1.ProfileLocalDeclarationRef(kind, ordinal)
                ),
            )
            for field, ((kind, _name), ordinal) in enumerate(
                zip(witness_declarations, witness_ordinals)
            )
        )
        + ((3, witness_result_schema),)
    )
    witness_contract_body = k2._checked_construction_checker_contract_body(
        witness_profile,
        k2.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        witness_result_schema,
    )
    _require(
        encoded(witness_contract_body) == encoded(expected_witness_contract_body),
        "runtime canonical checker contract differs from the owner equation",
    )
    witness_contract_id = k2._authority_id(
        witness_profile, "pir.checker-contract", expected_witness_contract_body
    )
    result = checked.result
    canonical_checked_local = k1.DatumRecord(
        (
            (0, k2._any_content_ref(result.source_protocol_id, "source Protocol")),
            (1, k2._any_content_ref(result.target_protocol_id, "target Protocol")),
            (2, k2._any_content_ref(result.shared_core_id, "shared Core")),
            (
                3,
                k2._any_content_ref(
                    result.transcript_construction_id, "transcript construction"
                ),
            ),
            (4, witness_result_schema),
            (5, k2._any_content_ref(witness_contract_id, "checker contract")),
        )
    )
    _require(
        encoded(k2._checked_fs_binding_payload_local_body(result, witness_profile))
        == encoded(canonical_checked_local),
        "canonical checked local payload differs from the owner equation",
    )
    source_bundles["canonical-checked-construction"] = source_bundle(
        witness_profile,
        k2.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        k2.PIRSourceFamily.CHECKED_CONSTRUCTION,
        1,
        canonical_checked_local,
        "checked-fs-construction",
        checked.capability.consumer_id,
        checked.capability.purpose_id,
        checked.source_binding,
    )

    duplex_profile, duplex_result_schema, duplex_contract_id = checker_objects[
        "duplex-sponge-fiat-shamir"
    ]
    protocol_id = k2.protocol_id(
        core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR
    )
    core_id = k2.core_id(core)
    construction_id = k2.construction_id(core, construction)
    duplex_coordinate_body = k1.DatumRecord(
        (
            (
                0,
                k1.DatumVariant(
                    0,
                    k1.DatumRecord(
                        ((0, k2._any_content_ref(protocol_id, "duplex Protocol")),)
                    ),
                ),
            ),
            (1, k2._any_content_ref(duplex_profile.identity, "duplex profile")),
        )
    )
    duplex_field_coordinate = k1.DatumRecord(
        (
            (0, duplex_coordinate_body),
            (1, k1.DatumSeq((k1.DatumVariant(0, k1.Nat(0)),))),
            (2, k1.DatumVariant(4, k1.UNIT)),
        )
    )
    duplex_static_local = k1.DatumRecord(
        (
            (0, duplex_coordinate_body),
            (1, k1.DatumSeq((duplex_field_coordinate,))),
        )
    )
    source_bundles["duplex-static-view"] = source_bundle(
        duplex_profile,
        k2.PIRSourceOwnerCompiler.DUPLEX_SPONGE,
        k2.PIRSourceFamily.STATIC_VIEW,
        0,
        duplex_static_local,
        "static-view",
        core_id,
        core_id,
    )
    duplex_checked_local = k1.DatumRecord(
        (
            (0, k2._any_content_ref(protocol_id, "duplex source Protocol")),
            (1, k2._any_content_ref(protocol_id, "duplex target Protocol")),
            (2, k2._any_content_ref(core_id, "duplex shared Core")),
            (3, k2._any_content_ref(construction_id, "duplex construction")),
            (4, duplex_result_schema),
            (5, k2._any_content_ref(duplex_contract_id, "duplex checker contract")),
        )
    )
    _require(
        encoded(
            k2._checked_construction_binding_payload_local_body(
                protocol_id,
                protocol_id,
                core_id,
                construction_id,
                duplex_profile,
                k2.PIRSourceOwnerCompiler.DUPLEX_SPONGE,
                duplex_result_schema,
            )
        )
        == encoded(duplex_checked_local),
        "duplex checked local payload differs from the owner equation",
    )
    source_bundles["duplex-checked-construction"] = source_bundle(
        duplex_profile,
        k2.PIRSourceOwnerCompiler.DUPLEX_SPONGE,
        k2.PIRSourceFamily.CHECKED_CONSTRUCTION,
        1,
        duplex_checked_local,
        "checked-fs-construction",
        core_id,
        core_id,
    )

    former_contract_id = k2._authority_id(
        witness_profile,
        "pir.fs-construction-checker-contract",
        k1.DatumRecord(((0, k1.Symbol("bounded-check-fs-construction-v0")),)),
    )
    former_checked_local = k1.DatumRecord(
        canonical_checked_local.fields[:-1]
        + ((5, k2._any_content_ref(former_contract_id, "former checker")),)
    )
    former_local_coordinate_rejected = (
        encoded(k1.DatumVariant(1, former_checked_local))
        != encoded(k1.DatumVariant(1, canonical_checked_local))
    )
    _require(former_local_coordinate_rejected, "former checker coordinate was accepted")

    checker_contract_complete = (
        len(checker_owner_definitions) == 2
        and len(checker_contracts) == 2
        and all(
            row["executable_owner_body_byte_equal"]
            and len(row["declaration_references"]) == 3
            for row in checker_contracts.values()
        )
        and former_local_coordinate_rejected
    )
    executable_preimage_matches_owner = all(
        all(subject["byte_equal"] for subject in bundle["subjects"].values())
        for bundle in source_bundles.values()
    )
    model_compiler_calls = protocol_model.count("compile_pir_source_subject_body(")
    model_uses_bound_canonical_compiler = executable_preimage_matches_owner
    model_uses_current_interaction_compiler = (
        "PIRSourceOwnerCompiler.INTERACTION" in protocol_model
    )
    textual_complete = sites == direct_sites + dispatched_sites
    return {
        "pir_markdown_pages_scanned": len(PIR_MARKDOWN_PAGES),
        "identity_constructor_sites": sites,
        "profile_compiler_definitions": len(compiler_pages),
        "direct_compiler_sites": direct_sites,
        "owner_profile_dispatch_sites": dispatched_sites,
        "profile_compilers": compiler_rows,
        "profile_compiler_pages": {
            f"{prefix}.{kind}": page
            for (prefix, kind), page in sorted(compiler_pages.items())
        },
        "generic_dispatch_manifest_bindings": dispatcher_bindings,
        "textual_preimage_equations_complete": textual_complete,
        "canonical_framed_execution_call_line": _line_number(
            analysis_model, "fs_execution = _affirmative_pir_view("
        ),
        "owner_profile_selection_line": _line_number(
            protocol_model, "owner_profile = ("
        ),
        "canonical_compiler_calls_in_model": model_compiler_calls,
        "model_selects_transcript_profile": model_selects_transcript_profile,
        "model_uses_current_interaction_compiler": model_uses_current_interaction_compiler,
        "model_uses_bound_canonical_compiler": model_uses_bound_canonical_compiler,
        "source_subject_bundles": source_bundles,
        "executable_preimage_matches_owner": executable_preimage_matches_owner,
        "source_subject_byte_comparisons": sum(
            len(bundle["subjects"]) for bundle in source_bundles.values()
        ),
        "checker_owner_definitions": checker_owner_definitions,
        "checker_contracts": checker_contracts,
        "runtime_canonical_checker_contract": {
            "declaration_ordinals": witness_ordinals,
            "body": body_observation(expected_witness_contract_body),
            "identity": witness_contract_id.carrier(),
            "executable_owner_body_byte_equal": True,
        },
        "checker_contract_complete": checker_contract_complete,
        "former_checker_coordinate_rejected": former_local_coordinate_rejected,
        "complete": (
            textual_complete
            and model_selects_transcript_profile
            and model_uses_bound_canonical_compiler
            and executable_preimage_matches_owner
        ),
    }


def _challenge_transition_representability(pages: dict[str, str]) -> dict[str, Any]:
    canonical = pages["docs-next/pir/fiat-shamir.md"]
    fields = _record_field_types(canonical, "ChallengeTransitionViewBody")
    expected_fields = [
        "transcript_construction_id",
        "core_id",
        "namespace_derivation_law",
        "exact_length_law",
        "state_update_before_decode_law",
        "retry_law",
        "sampling_failure_law",
        "challenge_rules",
    ]
    _require(list(fields) == expected_fields, "challenge-transition view fields drifted")
    for snippet in (
        "challenge_ref: ChallengeRef,",
        "position: Natural,",
        "acceptance_abi: ChallengeABI,",
        "decoder_abi: ChallengeABI,",
        "draw_bounds: { squeeze_length: Natural, maximum_draws: Natural }",
        "challenge_rules: CanonicalSeq<ChallengeTransitionRule>",
    ):
        _require(snippet in canonical, "challenge-transition rule shape drifted")

    rule_fields = list(_record_field_types(canonical, "ChallengeTransitionRule"))
    abi_fields = list(_record_field_types(canonical, "ChallengeABI"))
    _require(
        rule_fields
        == [
            "challenge_ref",
            "position",
            "acceptance_abi",
            "decoder_abi",
            "draw_bounds",
        ]
        and abi_fields == ["use", "input_types", "result_type"],
        "challenge-transition nested body fields drifted",
    )

    countermodel_rules = [
        {
            "challenge_ref": 0,
            "position": 0,
            "acceptance_abi": {
                "use": {
                    "algorithm": "accept-boolean-0",
                    "evaluation_contract": "accept-contract-0",
                },
                "input_types": ["TranscriptBytesType"],
                "result_type": "BooleanType",
            },
            "decoder_abi": {
                "use": {
                    "algorithm": "decode-boolean-0",
                    "evaluation_contract": "decode-contract-0",
                },
                "input_types": ["TranscriptBytesType"],
                "result_type": "BooleanType",
            },
            "draw_bounds": {"squeeze_length": 1, "maximum_draws": 1},
        },
        {
            "challenge_ref": 1,
            "position": 1,
            "acceptance_abi": {
                "use": {
                    "algorithm": "accept-root-natural-1",
                    "evaluation_contract": "accept-contract-1",
                },
                "input_types": ["TranscriptBytesType"],
                "result_type": "BooleanType",
            },
            "decoder_abi": {
                "use": {
                    "algorithm": "decode-root-natural-1",
                    "evaluation_contract": "decode-contract-1",
                },
                "input_types": ["TranscriptBytesType"],
                "result_type": "RootNat(2)",
            },
            "draw_bounds": {"squeeze_length": 2, "maximum_draws": 3},
        },
    ]

    # Project exactly the fields declared by the repaired nested body, once per
    # construction rule and in construction order.  This makes a singleton
    # selection, an ABI union, or a homogenizing rewrite observable.
    projected_rules = [
        {field: rule[field] for field in rule_fields}
        for rule in countermodel_rules
    ]
    laws = {
        "namespace_derivation_law": "canonical-framed-prefix-and-domain-v0",
        "exact_length_law": "canonical-framed-body-grammar-v0",
        "state_update_before_decode_law": "canonical-framed-admission-and-execution-v0",
        "retry_law": "canonical-framed-admission-and-execution-v0",
        "sampling_failure_law": "canonical-framed-admission-and-execution-v0",
    }
    value_by_field: dict[str, Any] = {
        "transcript_construction_id": "two-rule-construction",
        "core_id": "two-rule-core",
        **laws,
        "challenge_rules": projected_rules,
    }
    derived_body = {field: value_by_field[field] for field in fields}
    dropped_rules = [
        rule for rule in countermodel_rules if rule not in projected_rules
    ]
    changed_rules = [
        (source, target)
        for source, target in zip(countermodel_rules, projected_rules)
        if source != target
    ]
    _require(
        "projected entry by entry\nfrom the construction's `challenge_rules`"
        in canonical
        and "the challenge occurrence's\nposition in the exact total Core schedule"
        in canonical,
        "challenge-rule projection equation drifted",
    )
    complete = (
        len(projected_rules) == len(countermodel_rules) == 2
        and not dropped_rules
        and not changed_rules
        and list(derived_body) == expected_fields
    )
    return {
        "countermodel_input_rules": 2,
        "challenge_rule_fields": rule_fields,
        "challenge_abi_fields": abi_fields,
        "derived_view_body": derived_body,
        "derived_challenge_rules": projected_rules,
        "derived_rule_count": len(projected_rules),
        "dropped_rules": len(dropped_rules),
        "changed_rules": len(changed_rules),
        "shared_law_field_count": 5,
        "complete": complete,
    }


def _influence_view_review(pages: dict[str, str]) -> dict[str, Any]:
    canonical = pages["docs-next/pir/fiat-shamir.md"]
    _require(
        _definition_count(canonical, "InfluenceAtom") == 1,
        "InfluenceAtom does not have exactly one definition",
    )
    algebra = canonical.split("InfluenceAtom =", 1)[1].split("```", 1)[0]
    atom_names = re.findall(r"(?:^|\n)\s*(?:\|\s*)?(\w+Atom)\(", algebra)
    expected_atom_names = [
        "CoreHeaderAtom",
        "ConstructionHeaderAtom",
        "ApplicationDomainAtom",
        "ScopeOpenedAtom",
        "PublicBindingAtom",
        "GuardOutcomeAtom",
        "ProverMessageAtom",
        "VerifierMessageAtom",
        "OraclePublicationAtom",
        "OracleQueryAtom",
        "OracleAnswerAtom",
        "ChallengeConditionAtom",
        "ModuleFrameAtom",
        "ChallengeDrawAtom",
    ]
    _require(atom_names == expected_atom_names, "InfluenceAtom algebra drifted")
    atom_body = canonical.split("InfluenceAtomBody =", 1)[1].split(
        "TransitionInputBody =", 1
    )[0]
    atom_tags = [int(item) for item in re.findall(r"V\((\d+),", atom_body)]
    _require(atom_tags == list(range(14)), "InfluenceAtom body tags drifted")
    for snippet in (
        "StaticInfluenceAtom =",
        "Atom(InfluenceAtom)",
        "EveryActualDrawOf(ChallengeRef)",
        "a symbolic draw entry is required by items 9\nand 10 of Section 5.2",
        "body therefore states the complete requirement",
        "one entry per\nstatic influence atom of `c`'s schedule universe",
    ):
        _require(snippet in canonical, "required-influence projection law drifted")

    tags = dict(zip(atom_names, atom_tags))

    def encode_atom(atom: tuple[str, Any]) -> tuple[Any, ...]:
        name, value = atom
        tag = tags[name]
        if name in {"CoreHeaderAtom", "ConstructionHeaderAtom"}:
            payload: Any = ("Y", ("ContentRefV0", value))
        elif name == "ApplicationDomainAtom":
            payload = ("DeclarationRefBody", ("Module", value))
        elif name == "ScopeOpenedAtom":
            payload = ("S", [("N", scope) for scope in value])
        elif name in {
            "PublicBindingAtom",
            "GuardOutcomeAtom",
            "ProverMessageAtom",
            "VerifierMessageAtom",
            "OraclePublicationAtom",
            "OracleQueryAtom",
            "OracleAnswerAtom",
        }:
            payload = ("N", value)
        elif name in {"ChallengeConditionAtom", "ChallengeDrawAtom"}:
            challenge, ordinal = value
            payload = ("R", {0: ("N", challenge), 1: ("N", ordinal)})
        elif name == "ModuleFrameAtom":
            effect, ordinal = value
            payload = (
                "R",
                {0: ("FSModuleEffectCoordinateBody", effect), 1: ("N", ordinal)},
            )
        else:
            raise ReviewError(f"no exact InfluenceAtomBody arm for {name}")
        return ("V", tag, payload)

    headers = [
        ("CoreHeaderAtom", "core-id"),
        ("ConstructionHeaderAtom", "construction-id"),
        ("ApplicationDomainAtom", "application-domain-ref"),
    ]
    root_opening = [
        ("ScopeOpenedAtom", (0,)),
        ("PublicBindingAtom", 0),
        ("PublicBindingAtom", 1),
    ]

    def project_entries(challenge: int) -> list[dict[str, Any]]:
        concrete = [*headers, *root_opening]
        result = [
            {
                "atom": {"kind": "Atom", "value": atom},
                "atom_body": encode_atom(atom),
                "required": True,
            }
            for atom in concrete
        ]
        result.extend(
            {
                "atom": {"kind": "EveryActualDrawOf", "challenge_ref": prior},
                "required": True,
            }
            for prior in range(challenge)
        )
        return result

    def expand_symbolic_draws(
        entries: list[dict[str, Any]], actual_draw_counts: dict[int, int]
    ) -> list[tuple[Any, ...]]:
        expanded: list[tuple[Any, ...]] = []
        for entry in entries:
            atom = entry["atom"]
            if atom["kind"] == "Atom":
                expanded.append(encode_atom(tuple(atom["value"])))
                continue
            challenge = int(atom["challenge_ref"])
            expanded.extend(
                encode_atom(("ChallengeDrawAtom", (challenge, ordinal)))
                for ordinal in range(actual_draw_counts[challenge])
            )
        return expanded

    first_challenge_entries = project_entries(0)
    second_challenge_entries = project_entries(1)
    first_tags = [entry["atom_body"][1] for entry in first_challenge_entries]
    symbolic_second = [
        entry
        for entry in second_challenge_entries
        if entry["atom"]["kind"] == "EveryActualDrawOf"
    ]
    expanded_second = expand_symbolic_draws(
        second_challenge_entries, {0: 2}
    )
    expanded_second_tags = [body[1] for body in expanded_second]
    complete = (
        first_tags == [0, 1, 2, 3, 4, 4]
        and [entry["atom"]["value"][1] for entry in first_challenge_entries[-2:]]
        == [0, 1]
        and len(symbolic_second) == 1
        and symbolic_second[0]["atom"]["challenge_ref"] == 0
        and symbolic_second[0]["required"] is True
        and expanded_second_tags == [0, 1, 2, 3, 4, 4, 13, 13]
    )
    return {
        "influence_atom_definitions": 1,
        "influence_atom_algebra": atom_names,
        "influence_atom_body_tags": atom_tags,
        "first_challenge_required_entries": first_challenge_entries,
        "two_challenge_second_entries": second_challenge_entries,
        "two_challenge_second_expansion_for_two_actual_draws": expanded_second,
        "distinct_public_binding_coordinates": [0, 1],
        "core_header_needs_no_occurrence_coordinate": True,
        "items_9_and_10_present": True,
        "symbolic_prior_draw_entry_present": True,
        "complete": complete,
    }


def _analysis_read_catalog_review() -> dict[str, Any]:
    analysis = _read(ANALYSIS_PAGE)
    interaction = _read("docs-next/pir/interactive-core.md")
    canonical = _read("docs-next/pir/fiat-shamir.md")
    control = _read(ANALYSIS_READ_CATALOG_CONTROL)
    body_pattern = re.compile(r"^(\w+ViewBody) = \{\n(.*?)^\}", re.DOTALL | re.MULTILINE)
    field_pattern = re.compile(r"^  (\w+):", re.MULTILINE)
    selection_pattern = re.compile(
        r"Analysis(Static|Execution)ViewFields\(subject,(\w+),\s*\[(.*?)\]\)",
        re.DOTALL,
    )
    axis_body = {
        "FreshExecutionView": "ExecutionViewBody",
        "FiatShamirExecutionView": "CanonicalFramedExecutionViewBody",
    }
    bodies: dict[str, list[str]] = {}
    body_types: dict[str, dict[str, str]] = {}
    for text in (interaction, canonical):
        for match in body_pattern.finditer(text):
            _require(match.group(1) not in bodies, "an owner view body is defined twice")
            bodies[match.group(1)] = field_pattern.findall(match.group(2))
            body_types[match.group(1)] = _record_field_types(text, match.group(1))

    rows: list[dict[str, Any]] = []
    missing: list[dict[str, Any]] = []
    duplicate_selections: list[dict[str, Any]] = []
    for match in selection_pattern.finditer(analysis):
        view = match.group(2)
        body = axis_body.get(view, f"{view}Body")
        names = [
            item.strip()
            for item in match.group(3).replace("\n", " ").split(",")
            if item.strip()
        ]
        absent = [item for item in names if item not in bodies.get(body, [])]
        if absent:
            missing.append({"view": view, "body": body, "fields": absent})
        duplicates = sorted({name for name in names if names.count(name) > 1})
        if duplicates:
            duplicate_selections.append(
                {"view": view, "body": body, "fields": duplicates}
            )
        rows.append(
            {
                "view": view,
                "body": body,
                "selected_fields": names,
                "selected_field_types": {
                    name: body_types.get(body, {}).get(name)
                    for name in names
                },
                "line": analysis.count("\n", 0, match.start()) + 1,
            }
        )
    literal_calls = len(
        re.findall(
            r"Analysis(?:Static|Execution)ViewFields\(subject,[A-Z][A-Za-z0-9_]+,",
            analysis,
        )
    )
    _require(len(rows) == literal_calls == 10, "Analysis owner-read selection census drifted")
    _require(sum(len(row["selected_fields"]) for row in rows) == 66, "selected field census drifted")
    _require(not missing, "an Analysis selection no longer resolves to its owner body")
    _require(not duplicate_selections, "an Analysis owner-read selection is duplicated")
    control_markers = (
        "SELECTION = re.compile(",
        "selections = list(SELECTION.finditer(self.catalog))",
        "for match in selections:",
        "self.assertIn(body, self.bodies",
        "self.assertEqual(len(names), len(set(names))",
        "missing = [name for name in names if name not in self.bodies[body]]",
        "self.assertEqual([], missing",
    )
    developer_control_covers = all(marker in control for marker in control_markers)
    _require(developer_control_covers, "developer read-catalog control drifted")
    resolution_markers = (
        "subtree_paths",
        "every atomic",
        "field name at the selected depth",
        "denotes the\n  ordinal path of that field",
    )
    exact_subtree_resolution = all(marker in analysis for marker in resolution_markers)
    _require(exact_subtree_resolution, "leaf/subtree resolution law drifted")

    # A selected name is always the root of one exact ordinal subtree; an
    # atomic field is the degenerate one-leaf case.  The owner type determines
    # which case it is, so no caller choice between a leaf and subtree remains.
    selected_subtree_roots = sum(
        any(
            token in (field_type or "")
            for token in ("Seq<", "Map<", "{", "Schema", "Description")
        )
        for row in rows
        for field_type in row["selected_field_types"].values()
    )
    return {
        "selection_count": len(rows),
        "selected_field_count": 66,
        "selections": rows,
        "missing_owner_fields": missing,
        "duplicate_selected_fields": duplicate_selections,
        "developer_control_covers_current_literal_calls": developer_control_covers,
        "developer_control_is_sufficient_for_literal_field_join": developer_control_covers,
        "developer_control_proves_recursive_leaf_meaning": False,
        "selected_subtree_roots": selected_subtree_roots,
        "subtree_projection_law_is_exact": exact_subtree_resolution,
        "ambiguous_leaf_or_subtree_selections": [],
        "complete": (
            not missing
            and not duplicate_selections
            and developer_control_covers
            and exact_subtree_resolution
        ),
    }


def _public_setup_review(pages: dict[str, str]) -> dict[str, Any]:
    interaction = pages["docs-next/pir/interactive-core.md"]
    analysis = _read(ANALYSIS_PAGE)
    for snippet in (
        "InvocationDetermined(P, OccurrenceOutput(_, _)) = false",
        "entries         = every SessionContext or PublicParameter binding b of P",
        "run_established = every SessionContext or PublicParameter binding b of P",
        "changing a public input that is bound\nonly as a Statement and read by no covered binding leaves the quotient\nunchanged",
    ):
        _require(snippet in interaction, "public-setup formation law drifted")

    view_block, _view_line = _definition_block(
        interaction, "PublicSetupInvocationViewBody"
    )
    entry_block, _entry_line = _definition_block(
        interaction, "PublicSetupInvocationEntry"
    )
    view_fields = re.findall(r"^  ([a-z][a-z0-9_]*):", view_block, re.MULTILINE)
    entry_fields = re.findall(r"^  ([a-z][a-z0-9_]*):", entry_block, re.MULTILINE)
    _require(
        view_fields == ["protocol_id", "core_id", "entries", "run_established"]
        and entry_fields
        == ["binding_ref", "scope_ref", "class", "value_type", "value"],
        "public-setup view body fields drifted",
    )

    def invocation_determined(value_ref: tuple[Any, ...]) -> bool:
        tag = value_ref[0]
        if tag in {"PublicInput", "Constant"}:
            return True
        if tag == "Derived":
            return all(invocation_determined(value) for value in value_ref[1])
        if tag in {"OccurrenceOutput", "VerifierPrivateInput"}:
            return False
        raise ReviewError(f"unknown public-setup ValueRef arm {tag}")

    def resolve_value(
        value_ref: tuple[Any, ...], invocation: dict[int, Any]
    ) -> Any:
        tag = value_ref[0]
        if tag == "PublicInput":
            return invocation[int(value_ref[1])]
        if tag == "Constant":
            return value_ref[1]
        if tag == "Derived":
            return (
                "DerivedValue",
                tuple(resolve_value(value, invocation) for value in value_ref[1]),
            )
        raise ReviewError("a non-invocation-determined value was resolved as setup")

    def encode_entry(entry: dict[str, Any]) -> tuple[Any, ...]:
        class_tag = {"SessionContext": 0, "PublicParameter": 1}[entry["class"]]
        return (
            "R",
            {
                0: ("N", entry["binding_ref"]),
                1: ("N", entry["scope_ref"]),
                2: ("V", class_tag, "Unit"),
                3: ("ValueTypeBody", entry["value_type"]),
                4: entry["value"],
            },
        )

    def project_setup(
        protocol: dict[str, Any], invocation: dict[int, Any]
    ) -> dict[str, Any]:
        entries: list[dict[str, Any]] = []
        run_established: list[int] = []
        for binding in sorted(protocol["bindings"], key=lambda item: item["binding_ref"]):
            if binding["class"] not in {"SessionContext", "PublicParameter"}:
                continue
            if invocation_determined(binding["value_ref"]):
                entries.append(
                    {
                        "binding_ref": binding["binding_ref"],
                        "scope_ref": binding["scope_ref"],
                        "class": binding["class"],
                        "value_type": binding["value_type"],
                        "value": resolve_value(binding["value_ref"], invocation),
                    }
                )
            else:
                run_established.append(binding["binding_ref"])
        body = (
            "R",
            {
                0: ("ContentRef", protocol["protocol_id"]),
                1: ("ContentRef", protocol["core_id"]),
                2: ("S", [encode_entry(entry) for entry in entries]),
                3: ("S", [("N", binding) for binding in run_established]),
            },
        )
        return {
            "protocol_id": protocol["protocol_id"],
            "core_id": protocol["core_id"],
            "entries": entries,
            "run_established": run_established,
            "body": body,
        }

    review_protocol = {
        "protocol_id": "protocol-id",
        "core_id": "core-id",
        "bindings": [
            {
                "binding_ref": 0,
                "scope_ref": 1,
                "class": "SessionContext",
                "value_type": "RootBool",
                "value_ref": ("OccurrenceOutput", 0, 0),
            }
        ],
    }
    countermodel_body = project_setup(review_protocol, {})
    expected_countermodel_encoding = (
        "R",
        {
            0: ("ContentRef", "protocol-id"),
            1: ("ContentRef", "core-id"),
            2: ("S", []),
            3: ("S", [("N", 0)]),
        },
    )
    countermodel_represented_exactly = (
        countermodel_body["entries"] == []
        and countermodel_body["run_established"] == [0]
        and countermodel_body["body"] == expected_countermodel_encoding
    )

    # The membership partition is fixed by the Protocol, but an included
    # entry's value comes from the invocation.  This second minimal fixture is
    # an executable discriminator for the page's one-view-per-Protocol claim.
    invocation_valued_protocol = {
        "protocol_id": "invocation-valued-protocol",
        "core_id": "invocation-valued-core",
        "bindings": [
            {
                "binding_ref": 0,
                "scope_ref": 0,
                "class": "SessionContext",
                "value_type": "RootBool",
                "value_ref": ("PublicInput", 0),
            }
        ],
    }
    false_view = project_setup(invocation_valued_protocol, {0: False})
    true_view = project_setup(invocation_valued_protocol, {0: True})
    same_protocol_two_public_input_values_yield_two_views = (
        false_view["body"] != true_view["body"]
    )

    statement_only_protocol = {
        "protocol_id": "statement-only-protocol",
        "core_id": "statement-only-core",
        "bindings": [
            {
                "binding_ref": 0,
                "scope_ref": 0,
                "class": "Statement",
                "value_type": "RootBool",
                "value_ref": ("PublicInput", 0),
            }
        ],
    }
    statement_false = project_setup(statement_only_protocol, {0: False})
    statement_true = project_setup(statement_only_protocol, {0: True})
    statement_invariance_exclusion_exact = (
        statement_false["body"] == statement_true["body"]
        and false_view["body"] != true_view["body"]
    )

    fixed_setup_fragment = analysis.split("AFKFixedPublicSetupBody(S) =", 1)[1].split(
        "Formation also evaluates", 1
    )[0]
    analysis_requires_empty = bool(
        re.search(
            r"run_established.{0,160}(?:empty|be empty)",
            fixed_setup_fragment,
            re.DOTALL,
        )
    )
    analysis_requires_complete_entries = (
        "both entry sequences must be\nbyte-identical and contain exactly every `PublicParameter` and `SessionContext`"
        in fixed_setup_fragment
    )
    protocol_and_invocation_uniqueness_claim = (
        "Membership in both sequences is decided by the Protocol alone, and the\n"
        "entries' values by the invocation, so every admitted Protocol has a setup\n"
        "view and has exactly one per invocation up to the covered-value equivalence"
        in interaction
    )
    protocol_only_complete_sequences = not (
        same_protocol_two_public_input_values_yield_two_views
    )
    return {
        "review_countermodel": countermodel_body,
        "review_countermodel_expected_canonical_body": (
            "R{0:ContentRef(protocol-id),1:ContentRef(core-id),2:S[],3:S[N(0)]}"
        ),
        "review_countermodel_represented_exactly": countermodel_represented_exactly,
        "entry_membership_decided_by_protocol": True,
        "run_established_membership_decided_by_protocol": True,
        "entry_values_decided_by_protocol": False,
        "same_protocol_two_public_input_values_yield_two_views": (
            same_protocol_two_public_input_values_yield_two_views
        ),
        "invocation_value_discriminator": {
            "false_body": false_view["body"],
            "true_body": true_view["body"],
        },
        "protocol_only_complete_sequences": protocol_only_complete_sequences,
        "owner_claims_one_view_per_protocol": False,
        "owner_claims_one_view_per_protocol_and_invocation": (
            protocol_and_invocation_uniqueness_claim
        ),
        "one_view_per_protocol_is_derivable": False,
        "one_view_per_protocol_and_invocation_is_derivable": (
            countermodel_represented_exactly
            and same_protocol_two_public_input_values_yield_two_views
            and protocol_and_invocation_uniqueness_claim
        ),
        "analysis_fixed_setup_scope": "OutsideScope",
        "analysis_fixed_setup_judged_here": False,
        "analysis_requires_run_established_empty": analysis_requires_empty,
        "analysis_still_requires_all_bindings_in_entries": analysis_requires_complete_entries,
        "analysis_fixed_setup_projection_line": _line_number(
            analysis,
            "AnalysisLawTerm<AFKFixedPublicSetupProjection> that first requires the",
        ),
        "analysis_complete_entry_claim_line": _line_number(
            analysis, "both entry sequences must be"
        ),
        "owner_uniqueness_claim_line": _line_number(
            interaction, "Membership in both sequences is decided by the Protocol alone"
        ),
        "statement_invariance_exclusion_exact": statement_invariance_exclusion_exact,
        "complete": (
            countermodel_represented_exactly
            and same_protocol_two_public_input_values_yield_two_views
            and protocol_and_invocation_uniqueness_claim
            and statement_invariance_exclusion_exact
        ),
    }


def _reference_closure_review(pages: dict[str, str]) -> dict[str, Any]:
    interaction_path = "docs-next/pir/interactive-core.md"
    canonical_path = "docs-next/pir/fiat-shamir.md"
    duplex_path = "docs-next/pir/duplex-sponge-fiat-shamir.md"
    interaction = pages[interaction_path]
    canonical = pages[canonical_path]
    duplex = pages[duplex_path]
    foundation = _read(FOUNDATION)

    union = interaction.split("PIRReference =", 1)[1].split(
        "PIRReferenceBody(x)", 1
    )[0]
    compact_union = " ".join(union.split())
    for reference in CORE_LOCAL_REFERENCE_TYPES:
        _require(
            union.count(reference) == 1,
            f"{interaction_path}:{_line_number(interaction, 'PIRReference =')}: "
            f"PIRReference does not contain {reference} exactly once",
        )
    _require(
        len(re.findall(r"(?:^|\| )ValueRef(?:\n|$)", union, flags=re.MULTILINE)) == 1
        and "ProtocolDeclarationRef<K> for a declaration kind K that the exact-used owner-module"
        in compact_union
        and "closure of the selected profile recognizes" in compact_union
        and 'the canonical-framed profile adds "pir.fs-application-domain"'
        in compact_union,
        f"{interaction_path}:{_line_number(interaction, 'PIRReference =')}: "
        "PIRReference arm shape drifted",
    )

    section_two = interaction.split(
        "Several Core fields need nominal semantic coordinates", 1
    )[1].split("## 3. Subjects and identities", 1)[0]
    interaction_kind_lines = {
        match.group(1): interaction.count("\n", 0, interaction.find(
            match.group(0), interaction.find(section_two)
        )) + 1
        for match in re.finditer(r'`"(pir\.[a-z0-9-]+)"`', section_two)
    }
    section_two_kinds = sorted(interaction_kind_lines)
    _require(
        section_two_kinds
        == [
            "pir.challenge-domain",
            "pir.challenge-sharing-contract",
            "pir.claim-contract",
            "pir.coin-correlation-group",
            "pir.message-channel",
            "pir.oracle-binding-contract",
            "pir.oracle-domain-law",
            "pir.public-coin-law",
            "pir.reduction-contract",
        ],
        f"{interaction_path}:{_line_number(interaction, 'The exact-used PIR owner-module closure')}: "
        "Section 2 declaration-kind census drifted",
    )

    family_addition_pattern = re.compile(
        r"owner-module closure additionally recognizes\s+"
        r"`ProtocolDeclarationRef<\"([^\"]+)\">`"
    )
    canonical_additions = {
        match.group(1): canonical.count("\n", 0, match.start(1)) + 1
        for match in family_addition_pattern.finditer(canonical)
    }
    duplex_additions = {
        match.group(1): duplex.count("\n", 0, match.start(1)) + 1
        for match in family_addition_pattern.finditer(duplex)
    }
    _require(
        canonical_additions == {"pir.fs-application-domain": 69},
        f"{canonical_path}:{_line_number(canonical, 'owner-module closure additionally recognizes')}: "
        "canonical-framed declaration-kind additions drifted",
    )
    _require(
        not duplex_additions,
        f"{duplex_path}:{_line_number(duplex, 'owner-module closure additionally recognizes')}: "
        "the duplex profile unexpectedly adds a declaration kind",
    )

    profile_import_lines = {
        "interaction": None,
        "canonical-framed-fiat-shamir": _line_number(canonical, "profile imports are"),
        "duplex-sponge-fiat-shamir": _line_number(
            duplex, "imports exactly `PIRInteractionProfile`"
        ),
    }
    _require(
        profile_import_lines["canonical-framed-fiat-shamir"] == 79
        and profile_import_lines["duplex-sponge-fiat-shamir"] == 58,
        "family profile-import lines drifted",
    )
    _require(
        "The exact no-extra authenticated closure" in duplex
        and "contains this profile and `PIRInteractionProfileId`, and no"
        in duplex,
        f"{duplex_path}:{_line_number(duplex, 'The exact no-extra authenticated closure')}: "
        "the duplex profile's no-extra closure statement drifted",
    )

    recognized_kinds = {
        "interaction": section_two_kinds,
        "canonical-framed-fiat-shamir": sorted(
            set(section_two_kinds) | set(canonical_additions)
        ),
        "duplex-sponge-fiat-shamir": section_two_kinds,
    }
    profile_pages = {
        "interaction": interaction_path,
        "canonical-framed-fiat-shamir": canonical_path,
        "duplex-sponge-fiat-shamir": duplex_path,
    }
    profile_rows = {
        "interaction": VIEW_SCHEMAS[interaction_path],
        "canonical-framed-fiat-shamir": VIEW_SCHEMAS[canonical_path],
        "duplex-sponge-fiat-shamir": VIEW_SCHEMAS[duplex_path],
    }

    @dataclass(frozen=True)
    class TypeDefinition:
        expression: str
        line: int
        page: str

    def type_definitions(page: str, text: str) -> dict[str, TypeDefinition]:
        definitions: dict[str, TypeDefinition] = {}
        for fence in re.finditer(r"```text\n(.*?)\n```", text, flags=re.DOTALL):
            block = fence.group(1)
            starts = list(
                re.finditer(
                    r"^([A-Z][A-Za-z0-9_]*)\s*=\s*(.*)$",
                    block,
                    flags=re.MULTILINE,
                )
            )
            for index, start in enumerate(starts):
                end = starts[index + 1].start() if index + 1 < len(starts) else len(block)
                blank = block.find("\n\n", start.end())
                if blank >= 0:
                    end = min(end, blank)
                expression = start.group(2) + block[start.end() : end]
                definitions[start.group(1)] = TypeDefinition(
                    expression=expression,
                    line=text.count("\n", 0, fence.start(1) + start.start()) + 1,
                    page=page,
                )
        return definitions

    interaction_definitions = type_definitions(interaction_path, interaction)
    interaction_definitions["MessageDeclaration"] = TypeDefinition(
        expression="ProverMessageDecl | VerifierMessageDecl",
        line=_line_number(interaction, "declaration: exact Message declaration"),
        page=interaction_path,
    )

    terminal_arms = {
        **{reference: "PIRReference" for reference in CORE_LOCAL_REFERENCE_TYPES},
        "ValueRef": "PIRReference",
        "PIRProfileLawReference": "PIRProfileLawReference",
        "ModuleEffectRef": "AdmittedModuleEffect",
        "AdmittedModuleEffectAtom": "AdmittedModuleEffect",
        "PortableAlgorithmRef": "Bytes",
    }
    ignored_continuation_prefixes = (
        "exactly the description",
        "FSChallengeReceipt",
        "DuplexInitializationReceipt",
    )

    census: list[dict[str, Any]] = []
    uncovered: list[dict[str, Any]] = []
    cycles: list[str] = []

    def normalized_expression(expression: str) -> str:
        lines = [
            line
            for line in expression.splitlines()
            if not line.strip().startswith(ignored_continuation_prefixes)
        ]
        value = "\n".join(lines)
        value = value.replace("exact Message declaration", "MessageDeclaration")
        value = value.replace("exact Oracle declaration", "OracleDecl")
        value = value.replace(
            ", with ModuleEffectRef one opaque admitted atom", ""
        )
        return value

    token_pattern = re.compile(r"\b[A-Z][A-Za-z0-9_]*\b")
    protocol_pattern = re.compile(r'ProtocolDeclarationRef<"([^"]+)">')

    def inspect_definition(
        *,
        profile: str,
        view: str,
        name: str,
        definitions: dict[str, TypeDefinition],
        stack: tuple[str, ...],
    ) -> None:
        if name in stack:
            cycles.append(" -> ".join((*stack, name)))
            return
        definition = definitions.get(name)
        _require(
            definition is not None,
            f"{profile_pages[profile]}:1: static view body {name} is absent",
        )
        assert definition is not None
        expression = normalized_expression(definition.expression)
        masked = list(expression)
        occurrence = 0

        def record_leaf(
            *, leaf_type: str, arm: str | None, offset: int, kind: str | None = None
        ) -> None:
            nonlocal occurrence
            occurrence += 1
            line = definition.line + expression.count("\n", 0, offset)
            row = {
                "profile": profile,
                "view": view,
                "path": " -> ".join((*stack, name)),
                "type": leaf_type,
                "page": definition.page,
                "line": line,
                "occurrence": occurrence,
                "arms": [] if arm is None else [arm],
            }
            if kind is not None:
                row["declaration_kind"] = kind
            census.append(row)
            if arm is None:
                uncovered.append(row)

        for match in protocol_pattern.finditer(expression):
            kind = match.group(1)
            arm = "PIRReference" if kind in recognized_kinds[profile] else None
            record_leaf(
                leaf_type=f'ProtocolDeclarationRef<"{kind}">',
                arm=arm,
                offset=match.start(),
                kind=kind,
            )
            for position in range(match.start(), match.end()):
                masked[position] = " "

        for match in token_pattern.finditer("".join(masked)):
            token = match.group(0)
            if token in terminal_arms:
                record_leaf(
                    leaf_type=token,
                    arm=terminal_arms[token],
                    offset=match.start(),
                )
            elif token in definitions:
                inspect_definition(
                    profile=profile,
                    view=view,
                    name=token,
                    definitions=definitions,
                    stack=(*stack, name),
                )
            elif token.endswith("Ref"):
                record_leaf(leaf_type=token, arm=None, offset=match.start())

    for profile, rows in profile_rows.items():
        local_definitions = type_definitions(
            profile_pages[profile], pages[profile_pages[profile]]
        )
        definitions = {**interaction_definitions, **local_definitions}
        definitions["MessageDeclaration"] = interaction_definitions["MessageDeclaration"]
        for view, body in rows:
            inspect_definition(
                profile=profile,
                view=view,
                name=body,
                definitions=definitions,
                stack=(),
            )

    _require(not cycles, f"static-view reference walk encountered cycles: {cycles}")
    for row in census:
        _require(
            len(row["arms"]) <= 1,
            f"{row['page']}:{row['line']}: {row['type']} has overlapping atomic arms",
        )

    direct_protocol_kinds = sorted(
        {
            row["declaration_kind"]
            for row in census
            if "declaration_kind" in row
        }
    )
    unrecognized_kinds = sorted(
        {
            row["declaration_kind"]
            for row in uncovered
            if "declaration_kind" in row
        }
    )
    counts_by_profile: dict[str, int] = {}
    counts_by_view: dict[str, int] = {}
    counts_by_type: dict[str, int] = {}
    counts_by_arm: dict[str, int] = {}
    source_lines: dict[str, dict[str, list[int]]] = {}
    for row in census:
        counts_by_profile[row["profile"]] = counts_by_profile.get(row["profile"], 0) + 1
        view_key = f"{row['profile']}:{row['view']}"
        counts_by_view[view_key] = counts_by_view.get(view_key, 0) + 1
        counts_by_type[row["type"]] = counts_by_type.get(row["type"], 0) + 1
        for arm in row["arms"]:
            counts_by_arm[arm] = counts_by_arm.get(arm, 0) + 1
        type_pages = source_lines.setdefault(row["type"], {})
        type_pages.setdefault(row["page"], []).append(row["line"])
    source_lines = {
        leaf_type: {
            page: sorted(set(lines)) for page, lines in sorted(type_pages.items())
        }
        for leaf_type, type_pages in sorted(source_lines.items())
    }
    census_digest = hashlib.sha256(
        json.dumps(census, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()

    recognition = {
        "interaction": {
            "page": interaction_path,
            "import_line": None,
            "recognized_kinds": [
                {"kind": kind, "page": interaction_path, "line": interaction_kind_lines[kind]}
                for kind in section_two_kinds
            ],
            "added_kinds": [],
            "determinate": True,
        },
        "canonical-framed-fiat-shamir": {
            "page": canonical_path,
            "import_line": profile_import_lines["canonical-framed-fiat-shamir"],
            "recognized_kinds": [
                {
                    "kind": kind,
                    "page": canonical_path if kind in canonical_additions else interaction_path,
                    "line": canonical_additions.get(kind, interaction_kind_lines.get(kind)),
                }
                for kind in recognized_kinds["canonical-framed-fiat-shamir"]
            ],
            "added_kinds": [
                {"kind": kind, "page": canonical_path, "line": line}
                for kind, line in sorted(canonical_additions.items())
            ],
            "determinate": True,
        },
        "duplex-sponge-fiat-shamir": {
            "page": duplex_path,
            "import_line": profile_import_lines["duplex-sponge-fiat-shamir"],
            "declaration_catalog_line": _line_number(
                duplex, "Its declaration catalog contains"
            ),
            "no_extra_closure_line": _line_number(
                duplex, "The exact no-extra authenticated closure"
            ),
            "recognized_kinds": [
                {"kind": kind, "page": interaction_path, "line": interaction_kind_lines[kind]}
                for kind in section_two_kinds
            ],
            "added_kinds": [],
            "determinate": True,
        },
    }

    usage_markers = {
        "pir.message-channel": "declaration: exact Message declaration",
        "pir.challenge-domain": 'domain: ProtocolDeclarationRef<"pir.challenge-domain">',
        "pir.public-coin-law": 'fresh_law: ProtocolDeclarationRef<"pir.public-coin-law">',
        "pir.coin-correlation-group": "correlation: CoinCorrelation",
        "pir.challenge-sharing-contract": "reduction_use: ReductionUsePolicy",
        "pir.claim-contract": 'contract: ProtocolDeclarationRef<"pir.claim-contract">',
        "pir.reduction-contract": 'contract: ProtocolDeclarationRef<"pir.reduction-contract">',
        "pir.oracle-binding-contract": "declaration: exact Oracle declaration",
        "pir.oracle-domain-law": "declaration: exact Oracle declaration",
    }
    for kind, marker in usage_markers.items():
        _require(
            marker in interaction,
            f"{interaction_path}:1: no static-view path reaches {kind}",
        )

    body_required = (
        "N(ordinal) for a Core-local dense ordinal",
        "ValueRefBody(x) for a ValueRef",
        "ModuleDeclarationRefBody(x) for a ProtocolDeclarationRef",
        "the union is closed under the selected profile",
        "a ModuleEffectRef takes the AdmittedModuleEffect arm",
    )
    _require(
        all(item in " ".join(interaction.split()) for item in body_required),
        f"{interaction_path}:{_line_number(interaction, 'PIRReferenceBody(x)')}: "
        "PIRReferenceBody delegation drifted",
    )
    atomic_required = (
        "Unit | Natural | MetaBoolean | MetaSymbol | Bytes",
        "ValueType | CanonicalValue(ValueType)",
        "PIRReference | PIRProfileLawReference | AdmittedModuleEffect",
    )
    _require(
        all(item in interaction for item in atomic_required),
        f"{interaction_path}:{_line_number(interaction, 'PIRViewAtomicBoundary =')}: "
        "PIRViewAtomicBoundary arm census drifted",
    )
    _require(
        "PortableAlgorithmRef := PortableAlgorithmId" in foundation
        and "Foundation\nsemantic references" in interaction
        and "algorithm, evaluation-contract, or module identity leaf closes to that identity alone"
        in " ".join(interaction.split()),
        "the Foundation identity-leaf classification drifted",
    )

    return {
        "interaction_core_local_reference_leaves": list(CORE_LOCAL_REFERENCE_TYPES),
        "value_reference_leaf": "ValueRef",
        "static_view_bodies": sum(len(rows) for rows in profile_rows.values()),
        "reference_leaf_occurrences": len(census),
        "reference_leaf_census": census,
        "reference_leaf_census_sha256": census_digest,
        "reference_leaf_counts_by_profile": dict(sorted(counts_by_profile.items())),
        "reference_leaf_counts_by_view": dict(sorted(counts_by_view.items())),
        "reference_leaf_counts_by_type": dict(sorted(counts_by_type.items())),
        "reference_leaf_counts_by_atomic_arm": dict(sorted(counts_by_arm.items())),
        "reference_leaf_source_lines": source_lines,
        "protocol_declaration_kind_leaves": direct_protocol_kinds,
        "recognized_declaration_kinds_by_profile": recognition,
        "unrecognized_declaration_kinds": unrecognized_kinds,
        "separate_atomic_reference_arms": {
            "PIRProfileLawReference": "PIRProfileLawReference",
            "ModuleEffectRef": "AdmittedModuleEffect",
            "PortableAlgorithmRef": "Bytes through its exact ContentRefV0 body",
        },
        "pir_reference_body_delegations": 3,
        "atomic_boundary_uncovered_leaves": uncovered,
        "complete": not uncovered
        and not unrecognized_kinds
        and all(row["determinate"] for row in recognition.values()),
    }


def _declaration_body_review(
    pages: dict[str, str], references: dict[str, Any]
) -> dict[str, Any]:
    interaction_path = "docs-next/pir/interactive-core.md"
    canonical_path = "docs-next/pir/fiat-shamir.md"
    interaction = pages[interaction_path]
    canonical = pages[canonical_path]
    foundation = _read(FOUNDATION)

    recognition = references["recognized_declaration_kinds_by_profile"]
    recognition_sites: dict[str, dict[str, Any]] = {}
    for row in recognition["interaction"]["recognized_kinds"]:
        recognition_sites[row["kind"]] = {
            "page": row["page"],
            "line": row["line"],
        }
    for profile in ("canonical-framed-fiat-shamir", "duplex-sponge-fiat-shamir"):
        for row in recognition[profile]["added_kinds"]:
            _require(
                row["kind"] not in recognition_sites,
                f"{row['page']}:{row['line']}: declaration kind is recognized twice",
            )
            recognition_sites[row["kind"]] = {
                "page": row["page"],
                "line": row["line"],
            }

    nominal_kinds = {
        "pir.message-channel",
        "pir.challenge-domain",
        "pir.public-coin-law",
        "pir.coin-correlation-group",
        "pir.challenge-sharing-contract",
        "pir.claim-contract",
        "pir.reduction-contract",
        "pir.oracle-binding-contract",
    }
    nominal_body_line = _line_number(interaction, "NominalProtocolDeclarationBody =")
    nominal_claim_line = _line_number(
        interaction,
        "The exact-used PIR owner-module closure recognizes this body",
    )
    nominal_body_present = (
        _definition_count(interaction, "NominalProtocolDeclarationBody") == 1
        and "The exact-used PIR owner-module closure recognizes this body for the declaration kinds"
        in " ".join(interaction.split())
    )
    oracle_body_line = _line_number(
        interaction, "The exact declaration body resolved by a `LogicalAccess.domain_law` is:"
    )
    oracle_encoding_line = _line_number(
        interaction, "OracleDomainLawDeclarationBody(x) = R {"
    )
    compact_interaction = " ".join(interaction.split())
    oracle_body_present = all(
        marker in compact_interaction
        for marker in (
            "The exact declaration body resolved by a `LogicalAccess.domain_law` is:",
            "OracleDomainLawDeclarationBody = {",
            "After authenticating its owner module, admission lifts `index_type`",
            "This finite executable predicate is the complete v0 domain law.",
            "OracleDomainLawDeclarationBody(x) = R {",
        )
    )
    canonical_body_line = _line_number(
        canonical, "The exact-used PIR owner-module closure additionally recognizes"
    )
    canonical_body_present = all(
        marker in canonical
        for marker in (
            '`ProtocolDeclarationRef<"pir.fs-application-domain">`, and this profile fixes',
            "its declaration body: exactly the companion page's",
            "`NominalProtocolDeclarationBody`, one nonempty semantic symbol and no other",
            "and a declaration with any other shape is `Malformed`.",
            "The reference keeps\nthe companion page's `ModuleDeclarationRefBody`.",
        )
    )

    formation_marker = (
        "recognized-declaration-formation=for-every-recognized-kind-K,"
        "strict-decoding-into-K's-exact-typed-body-grammar-precedes-owner-context-interpretation;"
        "wrong-constructor,tag,record-field-set-or-order,or-field-carrier-is-Malformed;"
        "only-after-formation-can-closed-owner-admission-run"
    )
    formation_line = _line_number(foundation, "recognized-declaration-formation=")
    generic_malformed_admission = formation_marker in foundation
    local_canonical_malformed_line = _line_number(
        canonical, "and a declaration with any other shape is `Malformed`."
    )

    rows: list[dict[str, Any]] = []
    missing_bodies: list[dict[str, Any]] = []
    ambiguous_body_owners: list[dict[str, Any]] = []
    missing_malformed_admission: list[dict[str, Any]] = []
    for kind, recognized_at in sorted(recognition_sites.items()):
        body_claims: list[dict[str, Any]] = []
        for page, text in pages.items():
            if not page.startswith("docs-next/pir/"):
                continue
            for paragraph in re.finditer(
                r"(?:\A|\n\n)(.*?)(?=\n\n|\Z)", text, flags=re.DOTALL
            ):
                block = paragraph.group(1)
                if kind in block and any(
                    phrase in block
                    for phrase in (
                        "recognizes this body",
                        "exact body and admission law",
                        "declaration body:",
                    )
                ):
                    body_claims.append(
                        {
                            "page": page,
                            "line": text.count("\n", 0, paragraph.start(1)) + 1,
                        }
                    )
        body_claims = [
            {
                "page": page,
                "line": min(
                    row["line"] for row in body_claims if row["page"] == page
                ),
            }
            for page in sorted({row["page"] for row in body_claims})
        ]
        body_owners: list[dict[str, Any]] = []
        malformed_admissions: list[dict[str, Any]] = []
        if (
            kind in nominal_kinds
            and nominal_body_present
            and body_claims
            == [{"page": interaction_path, "line": nominal_claim_line}]
        ):
            body_owners.append(
                {
                    "page": interaction_path,
                    "lines": [nominal_body_line, nominal_body_line + 2],
                    "body": "NominalProtocolDeclarationBody",
                }
            )
        elif (
            kind == "pir.oracle-domain-law"
            and oracle_body_present
            and body_claims
            == [{"page": interaction_path, "line": nominal_claim_line}]
        ):
            body_owners.append(
                {
                    "page": interaction_path,
                    "lines": [oracle_body_line, oracle_body_line + 27],
                    "encoding_lines": [oracle_encoding_line, oracle_encoding_line + 3],
                    "body": "OracleDomainLawDeclarationBody",
                }
            )
        elif (
            kind == "pir.fs-application-domain"
            and canonical_body_present
            and body_claims
            == [{"page": canonical_path, "line": canonical_body_line}]
        ):
            body_owners.append(
                {
                    "page": canonical_path,
                    "lines": [canonical_body_line, canonical_body_line + 8],
                    "body": "NominalProtocolDeclarationBody",
                }
            )
            malformed_admissions.append(
                {
                    "page": canonical_path,
                    "line": local_canonical_malformed_line,
                    "scope": "kind-local",
                }
            )
        if generic_malformed_admission:
            malformed_admissions.append(
                {
                    "page": FOUNDATION,
                    "line": formation_line,
                    "scope": "every recognized declaration kind",
                }
            )

        if not body_owners:
            missing_bodies.append({"kind": kind, "recognized_at": recognized_at})
        elif len(body_owners) != 1 or len(body_claims) != 1:
            ambiguous_body_owners.append(
                {
                    "kind": kind,
                    "recognized_at": recognized_at,
                    "body_claims": body_claims,
                    "body_owners": body_owners,
                }
            )
        if not malformed_admissions:
            missing_malformed_admission.append(
                {"kind": kind, "recognized_at": recognized_at}
            )
        rows.append(
            {
                "kind": kind,
                "recognized_at": recognized_at,
                "body_claims": body_claims,
                "body_owners": body_owners,
                "malformed_shape_admissions": malformed_admissions,
                "closed": len(body_claims) == 1
                and len(body_owners) == 1
                and bool(malformed_admissions),
            }
        )

    return {
        "recognized_declaration_kinds": len(recognition_sites),
        "recognized_profile_kind_instances": sum(
            len(row["recognized_kinds"]) for row in recognition.values()
        ),
        "declaration_body_rows": rows,
        "declaration_body_owner_pages": sorted(
            {
                owner["page"]
                for row in rows
                for owner in row["body_owners"]
            }
        ),
        "generic_malformed_formation_owner": {
            "page": FOUNDATION,
            "line": formation_line,
            "present": generic_malformed_admission,
        },
        "missing_declaration_bodies": missing_bodies,
        "ambiguous_declaration_body_owners": ambiguous_body_owners,
        "missing_malformed_shape_admissions": missing_malformed_admission,
        "complete": not missing_bodies
        and not ambiguous_body_owners
        and not missing_malformed_admission
        and all(row["closed"] for row in rows),
    }


def _table_entries(text: str, table_name: str) -> tuple[dict[tuple[str, str], tuple[str, str, bool, int]], int]:
    header = f"{table_name} = CanonicalMap ["
    _require(text.count(header) == 1, f"law selection table {table_name} is absent or ambiguous")
    start = text.index(header)
    end = text.find("\n]", start)
    _require(end >= 0, f"law selection table {table_name} is not closed")
    block = text[start : end + 2]
    entries: dict[tuple[str, str], tuple[str, str, bool, int]] = {}
    pattern = re.compile(
        r"^  \(([^,\n]+), ([^)\n]+)\)\n      -> ([^\n]+)$", re.MULTILINE
    )
    for match in pattern.finditer(block):
        key = (match.group(1), match.group(2))
        rhs = match.group(3).strip().removesuffix(",")
        imported = rhs.startswith("interaction ") and rhs.endswith(", imported")
        if rhs.startswith("the profile's pir.semantic-law declaration "):
            target_profile = "self"
            target_name = rhs.removeprefix(
                "the profile's pir.semantic-law declaration "
            )
        elif imported:
            target_profile = "interaction"
            target_name = rhs.removeprefix("interaction ").removesuffix(", imported")
        else:
            target_profile = "self"
            target_name = rhs
        line = text.count("\n", 0, start + match.start()) + 1
        _require(key not in entries, f"law selection table {table_name} repeats {key}")
        entries[key] = (target_profile, target_name, imported, line)
    return entries, text.count("\n", 0, start) + 1


def _law_path_line(text: str, body: str, path: str) -> int | None:
    block, start_line = _definition_block(text, body)
    parts = path.split(".")
    if len(parts) == 1:
        match = re.search(
            rf"\b{re.escape(parts[0])}: PIRProfileLawReference\b", block
        )
    else:
        parent, child = parts
        inline = re.search(
            rf"\b{re.escape(parent)}:\s*\{{(?:(?!\n  [a-z][a-z0-9_]*:).)*?"
            rf"\b{re.escape(child)}: PIRProfileLawReference\b",
            block,
            flags=re.DOTALL,
        )
        if inline is not None:
            match = inline
        else:
            parent_match = re.search(
                rf"\b{re.escape(parent)}: ([A-Za-z][A-Za-z0-9_]*)", block
            )
            if parent_match is None:
                return None
            alias = parent_match.group(1)
            try:
                alias_fields = _record_field_types(text, alias)
            except ReviewError:
                return None
            if alias_fields.get(child, "").removesuffix(",") != "PIRProfileLawReference":
                return None
            match = parent_match
    if match is None:
        return None
    return start_line + block.count("\n", 0, match.start())


def _source_fragment(text: str, manifest: dict[str, Any], name: str) -> tuple[str, int]:
    fragment = next((item for item in manifest["fragments"] if item["name"] == name), None)
    _require(fragment is not None, f"manifest fragment {name} is absent")
    assert fragment is not None
    start_token = f"<!-- {fragment['start']} -->"
    end_token = f"<!-- {fragment['end']} -->"
    _require(
        text.count(start_token) == text.count(end_token) == 1,
        f"manifest fragment {name} markers are absent or ambiguous",
    )
    start = text.index(start_token) + len(start_token)
    end = text.index(end_token, start)
    return text[start:end], text.count("\n", 0, start) + 1


def _law_selection_review(pages: dict[str, str]) -> dict[str, Any]:
    manifests = {
        key: _json(config["manifest"])
        for key, config in LAW_SELECTION_CONFIG.items()
    }
    catalogs = {
        key: [
            row
            for row in manifest["definitions"]
            if row["kind"] == "pir.semantic-law"
        ]
        for key, manifest in manifests.items()
    }
    ordinals = {
        key: {row["name"]: ordinal for ordinal, row in enumerate(rows)}
        for key, rows in catalogs.items()
    }
    mismatches: list[str] = []
    profile_metrics: dict[str, Any] = {}
    selected_coordinates: list[dict[str, Any]] = []

    def mismatch(relative: str, line: int, message: str) -> None:
        mismatches.append(f"{relative}:{line}: {message}")

    for profile, config in LAW_SELECTION_CONFIG.items():
        relative = config["page"]
        text = pages[relative]
        manifest_relative = config["manifest"]
        manifest = manifests[profile]
        expected = {
            (view, path): (target_profile, name)
            for view, path, target_profile, name in config["fields"]
        }
        entries, table_line = _table_entries(text, config["table"])
        parsed = {
            key: (
                profile if value[0] == "self" else value[0],
                value[1],
            )
            for key, value in entries.items()
        }
        for key in sorted(set(expected) - set(parsed)):
            mismatch(relative, table_line, f"selection table omits {key[0]}.{key[1]}")
        for key in sorted(set(parsed) - set(expected)):
            mismatch(relative, entries[key][3], f"selection table has extra {key[0]}.{key[1]}")
        for key in sorted(set(expected) & set(parsed)):
            if parsed[key] != expected[key]:
                mismatch(
                    relative,
                    entries[key][3],
                    f"selection for {key[0]}.{key[1]} names {parsed[key]} instead of {expected[key]}",
                )

        displayed_count = 0
        path_lines: dict[str, int] = {}
        for view, (body, _schema_definition) in config["views"].items():
            block, _start_line = _definition_block(text, body)
            displayed_count += block.count("PIRProfileLawReference")
            fields = _record_field_types(text, body)
            for field_type in fields.values():
                alias = field_type.removesuffix(",")
                if alias == "ScheduleCorrespondence":
                    alias_block, _alias_line = _definition_block(text, alias)
                    displayed_count += alias_block.count("PIRProfileLawReference")
        for view, path, target_profile, name in config["fields"]:
            body = config["views"][view][0]
            line = _law_path_line(text, body, path)
            if line is None:
                mismatch(relative, _line_number(text, f"{body} = {{"), f"{view}.{path} is not displayed as PIRProfileLawReference")
                continue
            path_lines[f"{view}.{path}"] = line
            target_rows = [
                row for row in catalogs[target_profile] if row["name"] == name
            ]
            table_line_for_entry = entries.get((view, path), ("", "", False, table_line))[3]
            if len(target_rows) != 1:
                mismatch(
                    relative,
                    table_line_for_entry,
                    f"{view}.{path} names an absent or duplicate pir.semantic-law {target_profile}/{name}",
                )
                continue
            selected_coordinates.append(
                {
                    "profile": profile,
                    "field": f"{view}.{path}",
                    "target_profile": target_profile,
                    "declaration": name,
                    "catalog_ordinal": ordinals[target_profile][name],
                    "field_line": line,
                    "table_line": table_line_for_entry,
                }
            )
            imported = target_profile != profile
            parsed_imported = entries.get((view, path), ("", "", False, 0))[2]
            if imported != parsed_imported:
                mismatch(relative, table_line_for_entry, f"{view}.{path} import marker disagrees with its target profile")
            if imported:
                schema_name = config["views"][view][1]
                schemas = [
                    row
                    for row in manifest["definitions"]
                    if row["kind"] == "pir.static-view-schema"
                    and row["name"] == schema_name
                ]
                dependency = {
                    "profile": target_profile,
                    "kind": "pir.semantic-law",
                    "name": name,
                }
                if len(schemas) != 1 or dependency not in schemas[0]["dependencies"]:
                    manifest_text = _read(manifest_relative)
                    mismatch(
                        manifest_relative,
                        _line_number(manifest_text, f'"name": "{schema_name}"'),
                        f"{view}.{path} lacks its imported declaration dependency",
                    )

        if displayed_count != len(config["fields"]):
            mismatch(
                relative,
                table_line,
                f"displayed PIRProfileLawReference count is {displayed_count}, expected {len(config['fields'])}",
            )

        old = json.loads(_git_bytes(config["ordinal_base"], manifest_relative))
        old_laws = [
            row["name"]
            for row in old["definitions"]
            if row["kind"] == "pir.semantic-law"
        ]
        current_laws = [row["name"] for row in catalogs[profile]]
        moved = [
            name
            for ordinal, name in enumerate(old_laws)
            if ordinal >= len(current_laws) or current_laws[ordinal] != name
        ]
        if moved:
            manifest_text = _read(manifest_relative)
            for name in moved:
                mismatch(
                    manifest_relative,
                    _line_number(manifest_text, f'"name": "{name}"'),
                    f"pre-existing law {name} moved from its catalog ordinal",
                )
        new_laws = set(current_laws) - set(old_laws)
        if new_laws != config["new_laws"]:
            mismatch(
                manifest_relative,
                1,
                f"new semantic-law set is {sorted(new_laws)}, expected {sorted(config['new_laws'])}",
            )
        selector_lines: dict[str, int] = {}
        for row in catalogs[profile]:
            if row["name"] not in new_laws:
                continue
            fragment, fragment_line = _source_fragment(text, manifest, row["fragment"])
            count = fragment.count(row["selector"])
            line = _line_number(text, row["selector"])
            selector_lines[row["name"]] = line
            if count != 1:
                mismatch(
                    relative,
                    line if row["selector"] in text else fragment_line,
                    f"selector for new declaration {row['name']} occurs {count} times in fragment {row['fragment']}",
                )

        profile_metrics[profile] = {
            "displayed_law_fields": displayed_count,
            "table_entries": len(entries),
            "field_lines": path_lines,
            "preexisting_law_ordinals_checked": len(old_laws),
            "preexisting_laws_moved": moved,
            "new_declarations": sorted(new_laws),
            "new_declaration_selector_lines": selector_lines,
        }

    return {
        "profiles": profile_metrics,
        "displayed_law_fields": sum(
            value["displayed_law_fields"] for value in profile_metrics.values()
        ),
        "table_entries": sum(value["table_entries"] for value in profile_metrics.values()),
        "selected_coordinates": selected_coordinates,
        "imported_entries": sum(
            coordinate["target_profile"] != coordinate["profile"]
            for coordinate in selected_coordinates
        ),
        "mismatches": mismatches,
        "complete": not mismatches,
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
    _require(field_count == 91, "the eight family body displays no longer contain 91 fields")
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
    for low in (False, True):
        for h in (False, True):
            if low:
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

    def compile_at(revision: str) -> tuple[dict[str, Any], dict[str, Any]]:
        manifests: dict[str, dict[str, Any]] = {}
        pages: dict[str, bytes] = {}
        for key, (relative, _manifest) in _all_manifests().items():
            try:
                manifest = json.loads(_git_bytes(revision, relative))
            except json.JSONDecodeError as error:
                raise ReviewError(f"cannot decode {relative} at {revision}") from error
            manifests[key] = manifest
            for page in _source_page_paths(manifest):
                pages[page] = _git_bytes(revision, page)
        return (
            reference.identity_table(
                reference.compile_repository(
                    manifest_overrides=manifests,
                    page_overrides=pages,
                )
            ),
            cold.identity_table(
                cold.compile_repository(
                    manifest_overrides=manifests,
                    page_overrides=pages,
                )
            ),
        )

    reference_baseline, cold_baseline = compile_at(ROUND_SEVEN_COMMIT)
    _require(
        reference_baseline == cold_baseline,
        "publication compilers disagree at the round-seven head",
    )
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
            "endpoint-source-view",
            "oir-projection-relation",
            "relations",
            "analysis-cryptographic-property",
            "analysis-afk-transport",
            "analysis-afk-theorem-source-validation",
            "analysis-incremental-composition",
            "analysis-incremental-composition-source-validation",
        ]
        and stable == ["oir-endpoint-graph", "analysis-kernel"],
        "the repair rotation cone drifted",
    )
    reference_round_eight, cold_round_eight = compile_at(ROUND_EIGHT_COMMIT)
    _require(
        reference_round_eight == cold_round_eight,
        "publication compilers disagree at the round-eight head",
    )
    round_eight_rotated = [
        key
        for key in reference.PROFILE_KEYS
        if reference_table["profiles"][key]
        != reference_round_eight["profiles"][key]
    ]
    round_eight_stable = [
        key for key in reference.PROFILE_KEYS if key not in round_eight_rotated
    ]
    _require(
        round_eight_rotated
        == [
            "canonical-framed-fiat-shamir",
            "duplex-sponge-fiat-shamir",
            "public-setup",
            "commitment-opening",
            "oracle-commitment",
            "interface-plan",
            "endpoint-source-view",
            "oir-projection-relation",
            "relations",
            "analysis-cryptographic-property",
            "analysis-afk-transport",
            "analysis-afk-theorem-source-validation",
            "analysis-incremental-composition",
            "analysis-incremental-composition-source-validation",
        ]
        and round_eight_stable
        == [
            "interaction",
            "verifier-derived-query-plan",
            "oir-endpoint-graph",
            "analysis-kernel",
        ],
        "the round-eight-to-current rotation cone drifted",
    )
    reference_migration_base, cold_migration_base = compile_at(MIGRATION_BASE_COMMIT)
    _require(
        reference_migration_base == cold_migration_base,
        "publication compilers disagree at the migration base",
    )
    migration_rotated = [
        key
        for key in reference.PROFILE_KEYS
        if reference_table["profiles"][key]
        != reference_migration_base["profiles"][key]
    ]
    migration_stable = [
        key for key in reference.PROFILE_KEYS if key not in migration_rotated
    ]
    _require(
        migration_rotated
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
        and migration_stable == ["analysis-kernel"],
        "the migration-base rotation cone drifted",
    )
    return {
        "compiler_agreement": True,
        "round_seven_compiler_agreement": True,
        "round_eight_compiler_agreement": True,
        "migration_base_compiler_agreement": True,
        "compiled_profiles": len(reference_table["profiles"]),
        "comparison_head": ROUND_SEVEN_COMMIT,
        "rotated_profiles": rotated,
        "rotation_count": len(rotated),
        "stable_profiles": stable,
        "round_eight_head": ROUND_EIGHT_COMMIT,
        "round_eight_rotated_profiles": round_eight_rotated,
        "round_eight_rotation_count": len(round_eight_rotated),
        "round_eight_stable_profiles": round_eight_stable,
        "migration_base": MIGRATION_BASE_COMMIT,
        "migration_base_rotated_profiles": migration_rotated,
        "migration_base_rotation_count": len(migration_rotated),
        "migration_base_stable_profiles": migration_stable,
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
    expected_existing_revisions = {
        "docs-next/oir/profiles/endpoint-graph.json": {
            ("oir.body-compiler", "endpoint-graph-body-v0"): 1,
            ("oir.semantic-law", "endpoint-contract-derivation-v0"): 1,
        },
        "docs-next/oir/profiles/projection-relation.json": {
            ("oir.body-compiler", "projection-proposition-body-v0"): 1,
            ("oir.semantic-law", "exact-endpoint-projection-v0"): 1,
        },
        "docs-next/pir/profiles/canonical-framed-fiat-shamir.json": {
            ("pir.semantic-law", "canonical-framed-same-core-construction-v0"): 1,
            ("pir.semantic-law", "canonical-framed-source-views-v0"): 4,
        },
        "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json": {
            ("pir.semantic-law", "duplex-sponge-source-views-v0"): 2,
        },
        "docs-next/pir/profiles/endpoint-source-view.json": {
            ("pir.body-compiler", "endpoint-source-view-body-v0"): 1,
            ("pir.semantic-law", "supplement-authority-v0"): 1,
        },
        "docs-next/pir/profiles/interaction.json": {
            ("pir.body-compiler", "interactive-core-body-v0"): 1,
            ("pir.semantic-law", "core-admission-v0"): 1,
            ("pir.semantic-law", "execution-and-replay-v0"): 1,
            ("pir.semantic-law", "public-coin-eligibility-v0"): 1,
            ("pir.semantic-law", "static-view-issuance-v0"): 2,
        },
        "docs-next/pir/profiles/interface-plan.json": {
            ("pir.body-compiler", "interface-plan-body-v0"): 1,
            ("pir.semantic-law", "interface-admission-v0"): 1,
            ("pir.semantic-law", "plan-witness-authority-v0"): 1,
        },
        "docs-next/pir/profiles/public-setup.json": {
            ("pir.body-compiler", "public-setup-invocation-view-body-v0"): 1,
            ("pir.semantic-law", "public-setup-projection-and-issuance-v0"): 2,
        },
    }
    revision_bumps = 0
    new_definitions = 0
    expected_profile_revisions = {
        "docs-next/oir/profiles/endpoint-graph.json": 1,
        "docs-next/oir/profiles/projection-relation.json": 1,
        "docs-next/pir/profiles/canonical-framed-fiat-shamir.json": 5,
        "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json": 4,
        "docs-next/pir/profiles/endpoint-source-view.json": 2,
        "docs-next/pir/profiles/interaction.json": 3,
        "docs-next/pir/profiles/interface-plan.json": 2,
        "docs-next/pir/profiles/public-setup.json": 2,
    }
    expected_new_revisions = {
        "docs-next/oir/profiles/endpoint-graph.json": {},
        "docs-next/oir/profiles/projection-relation.json": {},
        "docs-next/pir/profiles/canonical-framed-fiat-shamir.json": {
            ("pir.static-view-schema", "required-influence-view-v0"): 1,
            ("pir.static-view-schema", "challenge-transition-view-v0"): 2,
            ("pir.static-view-schema", "execution-view-v0"): 3,
        },
        "docs-next/pir/profiles/duplex-sponge-fiat-shamir.json": {
            ("pir.body-compiler", "source-binding-payload-body-v0"): 1,
            ("pir.body-compiler", "source-capability-requirement-body-v0"): 1,
            ("pir.body-compiler", "source-no-policy-body-v0"): 1,
            ("pir.body-compiler", "source-policy-closure-body-v0"): 1,
            ("pir.static-view-schema", "duplex-encoded-input-coverage-view-v0"): 1,
            ("pir.static-view-schema", "duplex-fs-construction-view-v0"): 1,
            ("pir.static-view-schema", "execution-view-v0"): 1,
            ("pir.semantic-law", "duplex-sponge-same-core-construction-v0"): 1,
        },
        "docs-next/pir/profiles/endpoint-source-view.json": {
            ("pir.body-compiler", "source-binding-payload-body-v0"): 1,
            ("pir.body-compiler", "source-capability-requirement-body-v0"): 1,
            ("pir.body-compiler", "source-no-policy-body-v0"): 1,
            ("pir.body-compiler", "source-policy-closure-body-v0"): 1,
        },
        "docs-next/pir/profiles/interaction.json": {
            ("pir.body-compiler", "source-binding-payload-body-v0"): 1,
            ("pir.body-compiler", "source-capability-requirement-body-v0"): 1,
            ("pir.body-compiler", "source-no-policy-body-v0"): 1,
            ("pir.body-compiler", "source-policy-closure-body-v0"): 1,
            ("pir.semantic-law", "static-view-schema-resolution-v0"): 1,
            ("pir.static-view-schema", "strategy-decision-view-v0"): 1,
            ("pir.static-view-schema", "execution-view-v0"): 1,
        },
        "docs-next/pir/profiles/interface-plan.json": {
            ("pir.body-compiler", "source-binding-payload-body-v0"): 1,
            ("pir.body-compiler", "source-capability-requirement-body-v0"): 1,
            ("pir.body-compiler", "source-no-policy-body-v0"): 1,
            ("pir.body-compiler", "source-policy-closure-body-v0"): 1,
        },
        "docs-next/pir/profiles/public-setup.json": {},
    }
    for relative in MIGRATED_MANIFESTS:
        try:
            old_text = subprocess.run(
                ["git", "show", f"{MIGRATION_BASE_COMMIT}:{relative}"],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            ).stdout
            old = json.loads(old_text)
        except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
            raise ReviewError(f"cannot reconstruct the migration base for {relative}") from error
        current = _json(relative)
        _require(
            old["revision"] == 0
            and current["revision"] == expected_profile_revisions[relative],
            "a migrated profile revision differs",
        )
        old_rows = {(row["kind"], row["name"]): row for row in old["definitions"]}
        observed_existing_revisions: dict[tuple[str, str], int] = {}
        observed_new_revisions: dict[tuple[str, str], int] = {}
        for row in current["definitions"]:
            key = (row["kind"], row["name"])
            if key not in old_rows:
                if row["revision"] == 0:
                    new_definitions += 1
                else:
                    observed_new_revisions[key] = row["revision"]
            elif row["revision"] != old_rows[key]["revision"]:
                _require(old_rows[key]["revision"] == 0, "the migration base revision drifted")
                observed_existing_revisions[key] = row["revision"]
        _require(
            observed_existing_revisions == expected_existing_revisions[relative],
            "the selected existing-definition revision map drifted",
        )
        _require(
            observed_new_revisions == expected_new_revisions[relative],
            "the post-creation definition revision map drifted",
        )
        revision_bumps += len(observed_existing_revisions) + len(observed_new_revisions)

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
        [
            _json(path)["revision"]
            for path in MIGRATED_MANIFESTS
        ] == [1, 1, 5, 4, 2, 3, 2, 2],
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
    references = _reference_closure_review(pages)
    law_selection = _law_selection_review(pages)
    declaration_bodies = _declaration_body_review(pages, references)
    terminal = _terminal_review(pages["docs-next/pir/interactive-core.md"])
    pcgraph = _pcgraph_review(pages["docs-next/pir/interactive-core.md"])
    manifests = _manifest_review(pages)
    publication = _publication_review()
    decisions = _decision_review(pages, manifests, view)
    interface_completion = _interface_completion_review(pages)
    source_identity = _source_identity_review()
    challenge_transition = _challenge_transition_representability(pages)
    influence_view = _influence_view_review(pages)
    analysis_read_catalog = _analysis_read_catalog_review()
    public_setup = _public_setup_review(pages)

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
        Finding(
            "pir-reference-closure",
            "Affirmative" if references["complete"] else "CannotAnswer",
            "F0V2C1-A-PIR-REFERENCE-CLOSURE"
            if references["complete"]
            else "F0V2C1-C-PIR-REFERENCE-CLOSURE",
        ),
        Finding(
            "static-view-law-selection",
            "Affirmative" if law_selection["complete"] else "CannotAnswer",
            "F0V2C1-A-STATIC-VIEW-LAW-SELECTION"
            if law_selection["complete"]
            else "F0V2C1-C-STATIC-VIEW-LAW-SELECTION",
        ),
        Finding(
            "declaration-body-closure",
            "Affirmative" if declaration_bodies["complete"] else "CannotAnswer",
            "F0V2C1-A-DECLARATION-BODY-CLOSURE"
            if declaration_bodies["complete"]
            else "F0V2C1-C-DECLARATION-BODY-NOT-CLOSED",
        ),
        Finding(
            "interface-completion-derivability",
            "Affirmative" if interface_completion["complete"] else "CannotAnswer",
            "F0V2C1-A-INTERFACE-COMPLETION-DERIVABILITY"
            if interface_completion["complete"]
            else "F0V2C1-C-INTERFACE-COMPLETION-DERIVATION",
        ),
        Finding(
            "source-authority-preimage-equations",
            "Affirmative" if source_identity["complete"] else "CannotAnswer",
            "F0V2C1-A-SOURCE-AUTHORITY-PREIMAGES"
            if source_identity["complete"]
            else "F0V2C1-C-CANONICAL-BINDING-PREIMAGE",
        ),
        Finding(
            "checked-construction-checker-contract",
            "Affirmative" if source_identity["checker_contract_complete"] else "CannotAnswer",
            "F0V2C1-A-CHECKER-CONTRACT-IDENTITY-DERIVED"
            if source_identity["checker_contract_complete"]
            else "F0V2C1-C-CHECKER-CONTRACT-IDENTITY",
        ),
        Finding(
            "challenge-transition-representability",
            "Affirmative" if challenge_transition["complete"] else "CannotAnswer",
            "F0V2C1-A-CHALLENGE-TRANSITION-REPRESENTABLE"
            if challenge_transition["complete"]
            else "F0V2C1-C-CHALLENGE-TRANSITION-NOT-REPRESENTABLE",
        ),
        Finding(
            "influence-view-exactness",
            "Affirmative" if influence_view["complete"] else "CannotAnswer",
            "F0V2C1-A-INFLUENCE-VIEW-EXACT"
            if influence_view["complete"]
            else "F0V2C1-C-INFLUENCE-VIEW-NOT-EXACT",
        ),
        Finding(
            "analysis-read-catalog-join",
            "Affirmative" if analysis_read_catalog["complete"] else "CannotAnswer",
            "F0V2C1-A-ANALYSIS-READ-CATALOG-JOIN"
            if analysis_read_catalog["complete"]
            else "F0V2C1-C-ANALYSIS-READ-CATALOG-JOIN",
        ),
        Finding(
            "public-setup-view-totality",
            "Affirmative" if public_setup["complete"] else "CannotAnswer",
            "F0V2C1-A-PUBLIC-SETUP-VIEW-TOTAL"
            if public_setup["complete"]
            else "F0V2C1-C-PUBLIC-SETUP-VIEW-TOTALITY",
        ),
    ]
    metrics = {
        "source_sha256": _source_hashes(),
        "decisions": decisions,
        "terminal": terminal,
        "pcgraph": pcgraph,
        "views": view,
        "references": references,
        "law_selection": law_selection,
        "declaration_bodies": declaration_bodies,
        "manifests": manifests,
        "publication": publication,
        "interface_completion": interface_completion,
        "source_identity": source_identity,
        "challenge_transition": challenge_transition,
        "influence_view": influence_view,
        "analysis_read_catalog": analysis_read_catalog,
        "public_setup": public_setup,
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
    actual = {
        "aggregate": _aggregate(findings),
        "finding_codes": [item.value() for item in findings],
        "metrics_sha256": _canonical_sha256(metrics),
    }
    _require(expected == actual, "frozen finding or evidence projection drifted")
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
                    "metrics_sha256": _canonical_sha256(metrics),
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
