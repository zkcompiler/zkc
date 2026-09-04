#!/usr/bin/env python3
"""Run the B2B constructor-complete schema and inhabitance gate."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

import independent
import model


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EXPECTED = HERE / "expected-findings.json"
CENSUS = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
BOUNDED_SOURCE = (
    ROOT / "evaluation/formal-source-view-bodies-f0v2b1/normalized-schema.json"
)

AGGREGATE = "F0V2B2B-A-CONSTRUCTOR-COMPLETE-SCHEMA-INHABITANCE"
EXPECTED_VARIANTS: dict[str, list[int]] = {
    "BindingClass": [0, 1, 2],
    "ChallengeInterpretation": [0],
    "ClaimCreation": [0, 1],
    "ClaimDisposition": [0, 1],
    "ClaimSource": [0, 1],
    "ClaimUsage": [0, 1],
    "ClaimUse": [0, 1],
    "CoinCorrelation": [0, 1],
    "CoreEffect": list(range(8)),
    "MessageClass": [0, 1],
    "MessageDeclaration": [0, 1],
    "OracleEffect": [0, 1, 2],
    "OracleOrigin": [0, 1],
    "OraclePublicationMode": [0, 1, 2],
    "OracleReceiptSchema": [0, 1, 2],
    "OracleVisibility": [0, 1],
    "PCClass": [0, 1, 2, 3],
    "PCNode": list(range(14)),
    "ProverMoveType": [0, 1, 2],
    "ReadCoordinate": list(range(10)),
    "ReductionUse": [0, 1],
    "ScopeOpening": [0, 1],
    "TerminalVerdict": [0, 1, 2],
}
REPAIR_DEFINITIONS: dict[str, set[str]] = {
    "joint-correlation-and-shared-reduction-use": {
        "CoinCorrelation",
        "ReductionUse",
    },
    "deterministic-verifier-message-effect": {"VerifierMessageDeclaration"},
    "apply-reduction-effect": {"ReductionRef"},
    "standard-oracle-effect-and-lifecycle": {
        "OracleEffect",
        "OracleVisibility",
    },
    "admitted-module-effect-atom": {"AdmittedModuleEffect"},
    "all-fourteen-pcnode-cases": {"PCNode"},
    "oracle-and-module-prover-moves": {"ProverMoveType"},
    "all-ten-prover-read-coordinates": {"ReadCoordinate"},
    "challenge-reduction-consumers": {"ReductionConsumerEntry"},
    "oracle-lifecycle-view-entries": {"OracleEntry", "OracleDeclaration"},
    "supported-extension-view-entries": {"SupportedExtensionEntry"},
    "claim-creation-use-and-reduction-entries": {
        "ClaimCreation",
        "ClaimUse",
        "ReductionEntry",
    },
    "terminal-claim-dispositions": {
        "ClaimDispositionEntry",
        "TerminalDispositionEntry",
    },
    "runtime-oracle-receipt-schema": {"OracleReceiptSchema"},
}


class GateFailure(RuntimeError):
    """The B2B evidence or its frozen classification drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _raw_sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise GateFailure(f"cannot hash predecessor {path}") from error


def _load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure(f"cannot read {path}") from error
    if type(value) is not dict:
        raise GateFailure(f"{path} is not a JSON object")
    return value


def _variant_tags(source: dict[str, Any], name: str) -> list[int]:
    definition = source["definitions"].get(name)
    if type(definition) is not dict or set(definition) != {"variant"}:
        raise GateFailure(f"{name} is not one exact named variant")
    return [entry[0] for entry in definition["variant"]]


def _compiled_stats(schema: dict[str, Any]) -> dict[str, Any]:
    counts = {"atom": 0, "record": 0, "variant": 0, "sequence": 0}
    variant_cases = 0
    minimum_one_sequences = 0
    sorted_unique_sequences = 0
    maximum_depth = 0
    work: list[tuple[dict[str, Any], int]] = [(schema, 0)]
    while work:
        node, depth = work.pop()
        maximum_depth = max(maximum_depth, depth)
        kind = node["node"]
        counts[kind] += 1
        if kind == "record":
            work.extend((child, depth + 1) for _ordinal, child in node["fields"])
        elif kind == "variant":
            variant_cases += len(node["cases"])
            work.extend((child, depth + 1) for _ordinal, child in node["cases"])
        elif kind == "sequence":
            minimum_one_sequences += node["min"] == 1
            sorted_unique_sequences += node["discipline"] == "sorted-unique"
            work.append((node["element"], depth + 1))
    return {
        "nodes": sum(counts.values()),
        "node_kinds": counts,
        "variant_cases": variant_cases,
        "minimum_one_sequences": minimum_one_sequences,
        "sorted_unique_sequences": sorted_unique_sequences,
        "maximum_depth": maximum_depth,
    }


def _raw_nodes(source: dict[str, Any]) -> list[dict[str, Any]]:
    nodes: list[dict[str, Any]] = []
    work = [*source["definitions"].values()]
    work.extend(entry["schema"] for entry in source["views"].values())
    while work:
        node = work.pop()
        nodes.append(node)
        if "record" in node:
            work.extend(entry[1] for entry in node["record"])
        elif "variant" in node:
            work.extend(entry[1] for entry in node["variant"])
        elif "sequence" in node:
            work.append(node["sequence"]["element"])
    return nodes


def _assert_source_closure(
    source: dict[str, Any], census: dict[str, Any], bounded: dict[str, Any]
) -> dict[str, Any]:
    predecessor = source["predecessor"]
    if predecessor != model.PREDECESSOR or predecessor != independent.PREDECESSOR:
        raise GateFailure("source predecessor declaration differs across compilers")
    if _raw_sha256(CENSUS) != predecessor["census_sha256"]:
        raise GateFailure("B2A census bytes drifted from the B2B pin")
    if _raw_sha256(BOUNDED_SOURCE) != predecessor["bounded_source_sha256"]:
        raise GateFailure("B1 bounded source bytes drifted from the B2B pin")
    if census.get("format") != predecessor["census_format"]:
        raise GateFailure("B2A census format drifted")
    if census.get("owner_profile") != source["owner_profile"]:
        raise GateFailure("B2A and B2B owner profiles differ")

    exact_tags = {name: _variant_tags(source, name) for name in EXPECTED_VARIANTS}
    if exact_tags != EXPECTED_VARIANTS:
        raise GateFailure("named B2B variant tables differ from the exact closure")
    missing = census["b1_gap"]["missing_variant_tags"]
    repaired_cases = 0
    for name, tags in missing.items():
        if not set(tags) <= set(exact_tags[name]):
            raise GateFailure(f"B2B did not repair every B1 case of {name}")
        repaired_cases += len(tags)

    repair_names = census["b1_gap"]["required_schema_repairs"]
    if set(repair_names) != set(REPAIR_DEFINITIONS):
        raise GateFailure("B2A repair group inventory drifted")
    definitions = set(source["definitions"])
    if any(not required <= definitions for required in REPAIR_DEFINITIONS.values()):
        raise GateFailure("one B2A repair group has no closed B2B definition")

    raw_nodes = _raw_nodes(source)
    maximum_zero = [
        node
        for node in raw_nodes
        if "sequence" in node and node["sequence"]["max"] == 0
    ]
    if maximum_zero or "Empty" in definitions:
        raise GateFailure("B2B retained a B1 maximum-zero placeholder")
    minimum_one = [
        node
        for node in raw_nodes
        if "sequence" in node and node["sequence"]["min"] == 1
    ]
    sorted_unique = [
        node
        for node in raw_nodes
        if "sequence" in node and node["sequence"]["discipline"] == "sorted-unique"
    ]
    if not minimum_one or not sorted_unique:
        raise GateFailure("B2B did not encode lower bounds and collection discipline")

    if bounded.get("format") != "zkc.formal-source-view-bodies-f0v2b1.schema-source.v0":
        raise GateFailure("B1 predecessor format drifted")
    if len(census["b1_gap"]["empty_references"]) != 8:
        raise GateFailure("B1 empty-reference census drifted")
    return {
        "repaired_variant_cases": repaired_cases,
        "repaired_empty_references": len(census["b1_gap"]["empty_references"]),
        "repair_groups": len(repair_names),
        "minimum_one_source_sequences": len(minimum_one),
        "sorted_unique_source_sequences": len(sorted_unique),
        "named_variant_cases": sum(len(tags) for tags in exact_tags.values()),
    }


SOURCE_MUTATIONS = (
    "profile-digest-substitution",
    "predecessor-census-substitution",
    "format-substitution",
    "outer-field-insertion",
    "compiler-catalog-reordering",
    "law-catalog-duplication",
    "owner-kind-substitution",
    "view-order-substitution",
    "unknown-definition-reference",
    "definition-cycle",
    "unused-definition",
    "record-ordinal-duplication",
    "variant-ordinal-duplication",
    "empty-record",
    "empty-variant",
    "negative-sequence-minimum",
    "inverted-sequence-interval",
    "sequence-maximum-overflow",
    "sequence-discipline-substitution",
    "unknown-atom-kind",
    "unknown-body-compiler",
    "unknown-law-reference",
    "record-field-removal",
    "variant-case-removal",
    "variant-tag-substitution",
    "nonempty-lower-bound-removal",
    "sorted-unique-discipline-removal",
    "module-boundary-substitution",
    "unused-compiler-insertion",
    "unused-law-insertion",
)


def _mutate_source(source: dict[str, Any], name: str) -> None:
    definitions = source["definitions"]
    if name == "profile-digest-substitution":
        source["owner_profile"]["profile_digest"] = "00" * 32
    elif name == "predecessor-census-substitution":
        source["predecessor"]["census_sha256"] = "00" * 32
    elif name == "format-substitution":
        source["format"] += ".other"
    elif name == "outer-field-insertion":
        source["wildcard"] = True
    elif name == "compiler-catalog-reordering":
        source["body_compilers"][:2] = reversed(source["body_compilers"][:2])
    elif name == "law-catalog-duplication":
        source["laws"].append(source["laws"][-1])
    elif name == "owner-kind-substitution":
        source["views"]["EffectView"]["owner_subject_kind"] = "pir.protocol"
    elif name == "view-order-substitution":
        source["view_order"][:2] = reversed(source["view_order"][:2])
    elif name == "unknown-definition-reference":
        definitions["BindingEntry"]["record"][0][1]["ref"] = "UnknownRef"
    elif name == "definition-cycle":
        definitions["Unit"] = {"ref": "Unit"}
    elif name == "unused-definition":
        definitions["ZZUnused"] = {"atom": {"kind": "unit"}}
    elif name == "record-ordinal-duplication":
        definitions["BindingEntry"]["record"][1][0] = 0
    elif name == "variant-ordinal-duplication":
        definitions["BindingClass"]["variant"][1][0] = 0
    elif name == "empty-record":
        definitions["BindingEntry"]["record"] = []
    elif name == "empty-variant":
        definitions["BindingClass"]["variant"] = []
    elif name == "negative-sequence-minimum":
        definitions["ScopePath"]["sequence"]["min"] = -1
    elif name == "inverted-sequence-interval":
        definitions["ScopePath"]["sequence"]["min"] = 16385
    elif name == "sequence-maximum-overflow":
        definitions["ScopePath"]["sequence"]["max"] = 16385
    elif name == "sequence-discipline-substitution":
        definitions["ScopePath"]["sequence"]["discipline"] = "bag"
    elif name == "unknown-atom-kind":
        definitions["AdmittedModuleEffect"]["atom"]["kind"] = "any"
    elif name == "unknown-body-compiler":
        definitions["AlgorithmRef"]["atom"]["compiler"] = "unknown-v0"
    elif name == "unknown-law-reference":
        definitions["StrategyDecisionViewBody"]["record"][2][1]["atom"]["law"] = (
            "unknown-v0"
        )
    elif name == "record-field-removal":
        definitions["EffectViewBody"]["record"].pop()
    elif name == "variant-case-removal":
        definitions["CoreEffect"]["variant"].pop()
    elif name == "variant-tag-substitution":
        definitions["CoreEffect"]["variant"][-1][0] = 17
    elif name == "nonempty-lower-bound-removal":
        definitions["ScopePath"]["sequence"]["min"] = 0
    elif name == "sorted-unique-discipline-removal":
        definitions["PCGraphResult"]["record"][0][1]["sequence"]["discipline"] = (
            "ordered"
        )
    elif name == "module-boundary-substitution":
        definitions["AdmittedModuleEffect"]["atom"] = {"kind": "unit"}
    elif name == "unused-compiler-insertion":
        source["body_compilers"].append("zz-unused-body-v0")
    elif name == "unused-law-insertion":
        source["laws"].append("zz-unused-law-v0")
    else:  # pragma: no cover - frozen mutation catalog
        raise AssertionError(f"unknown source mutation {name}")


def _source_mutation_evidence(
    source: dict[str, Any], accepted_digest: str, findings: list[Finding]
) -> dict[str, int]:
    recursive_grammar_refusals = 0
    iterative_grammar_refusals = 0
    for name in SOURCE_MUTATIONS:
        candidate = copy.deepcopy(source)
        _mutate_source(candidate, name)
        if model.digest(candidate) == accepted_digest:
            raise GateFailure(f"source mutation {name} did not change source identity")
        if independent.digest(candidate) == accepted_digest:
            raise GateFailure(f"cold source identity accepted mutation {name}")
        try:
            model.compile_source(candidate)
        except (model.SchemaError, RecursionError):
            recursive_grammar_refusals += 1
        try:
            independent.compile_source(candidate)
        except independent.IndependentError:
            iterative_grammar_refusals += 1
        findings.append(
            _finding(
                name,
                "Refused",
                "F0V2B2B-R-SOURCE-" + name.upper().replace("-", "_"),
                "both source identities refuse the changed grammar; malformed changes also fail compilation",
            )
        )
    return {
        "source_mutations": len(SOURCE_MUTATIONS),
        "recursive_grammar_refusals": recursive_grammar_refusals,
        "iterative_grammar_refusals": iterative_grammar_refusals,
    }


def _transform_first(
    schema: dict[str, Any],
    value: Any,
    predicate: Callable[[dict[str, Any], Any], bool],
    transform: Callable[[dict[str, Any], Any], Any],
) -> tuple[Any, bool]:
    if predicate(schema, value):
        return transform(schema, copy.deepcopy(value)), True
    kind = schema["node"]
    if kind == "record":
        for ordinal, child in schema["fields"]:
            replacement, changed = _transform_first(
                child, value[ordinal], predicate, transform
            )
            if changed:
                result = copy.deepcopy(value)
                result[ordinal] = replacement
                return result, True
    elif kind == "variant":
        child = next(
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        )
        replacement, changed = _transform_first(
            child, value["value"], predicate, transform
        )
        if changed:
            result = copy.deepcopy(value)
            result["value"] = replacement
            return result, True
    elif kind == "sequence":
        for index, item in enumerate(value):
            replacement, changed = _transform_first(
                schema["element"], item, predicate, transform
            )
            if changed:
                result = copy.deepcopy(value)
                result[index] = replacement
                return result, True
    return value, False


def _mutated_value(
    suites: dict[str, list[Any]],
    schemas: dict[str, Any],
    view: str,
    predicate: Callable[[dict[str, Any], Any], bool],
    transform: Callable[[dict[str, Any], Any], Any],
) -> Any:
    for value in suites[view]:
        replacement, changed = _transform_first(
            schemas[view], value, predicate, transform
        )
        if changed:
            return replacement
    raise GateFailure(f"no active {view} value exposes one requested mutation target")


def _alter_first_body(value: Any) -> bool:
    if type(value) is dict:
        if set(value) == {"compiler", "body"}:
            value["body"] = "01"
            return True
        return any(_alter_first_body(child) for child in value.values())
    if type(value) is list:
        return any(_alter_first_body(child) for child in value)
    return False


def _source_order_reversal(_schema: dict[str, Any], value: Any) -> Any:
    return {key: copy.deepcopy(value[key]) for key in reversed(list(value))}


def _overflow_sequence(schema: dict[str, Any], value: Any) -> Any:
    return [copy.deepcopy(value[0]) for _ in range(schema["max"] + 1)]


def _descending_pair(_schema: dict[str, Any], value: Any) -> Any:
    second = copy.deepcopy(value[0])
    if not _alter_first_body(second):
        raise GateFailure("cannot form a second sorted-sequence inhabitant")
    return sorted([copy.deepcopy(value[0]), second], key=model.wire, reverse=True)


VALUE_MUTATIONS: tuple[
    tuple[
        str,
        str,
        Callable[[dict[str, Any], Any], bool],
        Callable[[dict[str, Any], Any], Any],
    ],
    ...,
] = (
    (
        "record-field-omission",
        "PublicBindingView",
        lambda node, _value: node["node"] == "record",
        lambda _node, value: {key: child for key, child in list(value.items())[:-1]},
    ),
    (
        "record-field-insertion",
        "PublicBindingView",
        lambda node, _value: node["node"] == "record",
        lambda _node, value: {**value, 99: None},
    ),
    (
        "record-field-reordering",
        "PublicBindingView",
        lambda node, _value: node["node"] == "record",
        _source_order_reversal,
    ),
    (
        "unknown-variant-case",
        "StrategyDecisionView",
        lambda node, _value: node["node"] == "variant",
        lambda _node, value: {"case": 999, "value": value["value"]},
    ),
    (
        "variant-payload-omission",
        "StrategyDecisionView",
        lambda node, _value: node["node"] == "variant",
        lambda _node, value: {"case": value["case"]},
    ),
    (
        "nonempty-sequence-empty",
        "PublicBindingView",
        lambda node, value: (
            node["node"] == "sequence" and node["min"] == 1 and bool(value)
        ),
        lambda _node, _value: [],
    ),
    (
        "sequence-maximum-overflow",
        "PublicBindingView",
        lambda node, value: (
            node["node"] == "sequence"
            and node["min"] == 1
            and node["element"]["node"] == "atom"
            and bool(value)
        ),
        _overflow_sequence,
    ),
    (
        "sorted-unique-duplication",
        "PublicCoinView",
        lambda node, value: (
            node["node"] == "sequence"
            and node["discipline"] == "sorted-unique"
            and len(value) == 1
        ),
        lambda _node, value: [copy.deepcopy(value[0]), copy.deepcopy(value[0])],
    ),
    (
        "sorted-unique-reordering",
        "PublicCoinView",
        lambda node, value: (
            node["node"] == "sequence"
            and node["discipline"] == "sorted-unique"
            and len(value) == 1
        ),
        _descending_pair,
    ),
    (
        "canonical-compiler-substitution",
        "EffectView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "canonical-body"
        ),
        lambda _node, value: {**value, "compiler": "unknown-v0"},
    ),
    (
        "canonical-body-nonhex",
        "EffectView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "canonical-body"
        ),
        lambda _node, value: {**value, "body": "gg"},
    ),
    (
        "exact-law-substitution",
        "ExecutionView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "exact-profile-law"
        ),
        lambda _node, value: {**value, "name": "unknown-v0"},
    ),
    (
        "natural-overflow",
        "PublicCoinView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "natural"
        ),
        lambda node, _value: node["atom"]["max"] + 1,
    ),
    (
        "boolean-type-substitution",
        "PublicCoinView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "meta-boolean"
        ),
        lambda _node, _value: 0,
    ),
    (
        "module-boundary-field-omission",
        "EffectView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "admitted-module-effect"
        ),
        lambda _node, value: {
            key: child for key, child in value.items() if key != "payload_body"
        },
    ),
    (
        "module-boundary-noncanonical-hex",
        "EffectView",
        lambda node, _value: (
            node["node"] == "atom" and node["atom"]["kind"] == "admitted-module-effect"
        ),
        lambda _node, value: {**value, "payload_body": "AA"},
    ),
    (
        "unit-inhabitation",
        "ExecutionView",
        lambda node, _value: node["node"] == "atom" and node["atom"]["kind"] == "unit",
        lambda _node, _value: 0,
    ),
    (
        "sequence-type-substitution",
        "ClaimReductionView",
        lambda node, _value: node["node"] == "sequence",
        lambda _node, _value: {},
    ),
)


def _value_mutation_evidence(
    schemas: dict[str, Any],
    suites: dict[str, list[Any]],
    findings: list[Finding],
) -> dict[str, int]:
    for name, view, predicate, transform in VALUE_MUTATIONS:
        candidate = _mutated_value(suites, schemas, view, predicate, transform)
        recursive_refused = False
        iterative_refused = False
        try:
            model.validate(schemas[view], candidate)
        except model.SchemaError:
            recursive_refused = True
        try:
            independent.validate(schemas[view], candidate)
        except independent.IndependentError:
            iterative_refused = True
        if not recursive_refused or not iterative_refused:
            raise GateFailure(
                f"value mutation {name} did not fail through both validators"
            )
        findings.append(
            _finding(
                name,
                "Refused",
                "F0V2B2B-R-VALUE-" + name.upper().replace("-", "_"),
                f"both schema validators refuse the mutated {view} inhabitant",
            )
        )
    return {
        "value_mutations": len(VALUE_MUTATIONS),
        "recursive_value_refusals": len(VALUE_MUTATIONS),
        "iterative_value_refusals": len(VALUE_MUTATIONS),
    }


def _snapshot(report: dict[str, Any]) -> dict[str, Any]:
    findings = report["findings"]
    return {
        "format": "zkc.formal-source-view-schema-f0v2b2b.expected.v0",
        "aggregate": report["aggregate"],
        "summary": report["summary"],
        "evidence": report["evidence"],
        "finding_codes": [
            [finding["outcome"], finding["code"]] for finding in findings
        ],
        "findings_sha256": model.digest(findings),
    }


def run() -> dict[str, Any]:
    findings: list[Finding] = []
    recursive_source = model.load_source()
    iterative_source = independent.load_source()
    if recursive_source != iterative_source:
        raise GateFailure("the two strict JSON readers reconstructed different sources")
    source = recursive_source
    census = _load_json(CENSUS)
    bounded = _load_json(BOUNDED_SOURCE)
    closure = _assert_source_closure(source, census, bounded)
    findings.append(
        _finding(
            "authenticated-predecessor-pins",
            "Affirmative",
            "F0V2B2B-A-PREDECESSOR-PINS",
            "the B2A census, B1 source, and exact Interaction owner profile match their frozen B2B pins",
        )
    )

    recursive_schemas, recursive_owners, recursive_stats = model.compile_source(source)
    iterative_schemas, iterative_owners, iterative_stats = independent.compile_source(
        iterative_source
    )
    if recursive_schemas != iterative_schemas:
        raise GateFailure("recursive and iterative source compilers disagree")
    if recursive_owners != iterative_owners:
        raise GateFailure("recursive and iterative owner catalogs disagree")
    if recursive_stats["source_node_count"] != iterative_stats["source_node_count"]:
        raise GateFailure("the two compilers counted different source nodes")
    schemas = recursive_schemas
    findings.append(
        _finding(
            "dual-source-compilation",
            "Affirmative",
            "F0V2B2B-A-DUAL-SOURCE-COMPILATION",
            "recursive dependency expansion and iterative topological worklist expansion produce byte-identical six-view schemas",
        )
    )
    findings.append(
        _finding(
            "six-view-owner-catalog",
            "Affirmative",
            "F0V2B2B-A-SIX-VIEW-OWNER-CATALOG",
            "five schemas bind pir.interactive-core and ExecutionView binds pir.protocol in exact view order",
        )
    )
    findings.append(
        _finding(
            "closed-named-variant-surface",
            "Affirmative",
            "F0V2B2B-A-NAMED-VARIANT-CLOSURE",
            f"the exact named target surface contains {closure['named_variant_cases']} cases, including all CoreEffect, PCNode, ProverMoveType, and ReadCoordinate tags",
        )
    )
    findings.append(
        _finding(
            "b1-constructor-delta-repaired",
            "Affirmative",
            "F0V2B2B-A-B1-DELTA-REPAIRED",
            f"all {closure['repaired_variant_cases']} missing B1 cases and {closure['repaired_empty_references']} maximum-zero references have structural replacements",
        )
    )
    findings.append(
        _finding(
            "b2a-repair-topology",
            "Affirmative",
            "F0V2B2B-A-REPAIR-TOPOLOGY",
            f"all {closure['repair_groups']} B2A repair groups map to closed definitions",
        )
    )
    findings.append(
        _finding(
            "sequence-contract-expressivity",
            "Affirmative",
            "F0V2B2B-A-SEQUENCE-CONTRACTS",
            f"the source distinguishes lower bounds and sorted-unique discipline at {closure['minimum_one_source_sequences']} and {closure['sorted_unique_source_sequences']} sequence sites",
        )
    )

    suites: dict[str, list[Any]] = {}
    coverage: dict[str, dict[str, int]] = {}
    schema_evidence: dict[str, Any] = {}
    total_values = 0
    total_requirements = 0
    for view in source["view_order"]:
        schema = schemas[view]
        values = model.inhabitants(schema)
        expected_coverage = model.coverage_requirements(schema)
        observed_coverage: set[str] = set()
        for value in values:
            model.validate(schema, value)
            independent.validate(schema, value)
            observed_coverage |= model.observe_coverage(schema, value)
        if observed_coverage != expected_coverage:
            missing = sorted(expected_coverage - observed_coverage)
            raise GateFailure(f"{view} inhabitance missed {missing[:3]}")
        suites[view] = values
        coverage[view] = {
            "inhabitants": len(values),
            "requirements": len(expected_coverage),
        }
        stats = _compiled_stats(schema)
        schema_evidence[view] = {
            "owner_subject_kind": recursive_owners[view],
            "schema_digest": model.digest(schema),
            "inhabitant_suite_digest": model.digest(values),
            **stats,
            **coverage[view],
        }
        total_values += len(values)
        total_requirements += len(expected_coverage)
    findings.append(
        _finding(
            "schema-directed-constructor-inhabitance",
            "Affirmative",
            "F0V2B2B-A-CONSTRUCTOR-INHABITANCE",
            f"{total_values} additive inhabitants cover all {total_requirements} reachable record, variant, sequence, and atom boundary requirements",
        )
    )
    findings.append(
        _finding(
            "dual-inhabitant-validation",
            "Affirmative",
            "F0V2B2B-A-DUAL-INHABITANT-VALIDATION",
            "every generated inhabitant is accepted by both recursive and iterative value validators",
        )
    )
    findings.append(
        _finding(
            "fresh-runtime-oracle-schema",
            "Affirmative",
            "F0V2B2B-A-FRESH-ORACLE-RECEIPT-SCHEMA",
            "Fresh ExecutionView structurally inhabits Published, Queried, and Answered Oracle receipt-schema branches with both visibility tags",
        )
    )

    source_digest = model.digest(source)
    mutation_evidence = _source_mutation_evidence(source, source_digest, findings)
    mutation_evidence.update(_value_mutation_evidence(schemas, suites, findings))

    cannot_answer = (
        (
            "extended-core-admission",
            "F0V2B2B-C-EXTENDED-CORE-ADMISSION",
            "syntactic inhabitants are not authenticated or admitted Core carriers; B2C owns that judgment",
        ),
        (
            "owner-view-projection",
            "F0V2B2B-C-OWNER-VIEW-PROJECTION",
            "no inhabitant is asserted to be the exact projection of an admitted owner; B2C owns dual derivation",
        ),
        (
            "pcgraph-transfer-semantics",
            "F0V2B2B-C-PCGRAPH-TRANSFER-SEMANTICS",
            "PCGraph fields and cases form, but edge construction, transfer, sinks, and logical cones remain B2C/B2D obligations",
        ),
        (
            "runtime-record-semantics",
            "F0V2B2B-C-RUNTIME-RECORD-SEMANTICS",
            "receipt schema branches form, but generated run, replay, arity, visibility, and causal-generation laws remain B2D obligations",
        ),
        (
            "profile-publication-and-migration",
            "F0V2B2B-C-PROFILE-PUBLICATION-MIGRATION",
            "this source is a research candidate and does not rotate or publish the Interaction profile",
        ),
        (
            "implementation-correspondence",
            "F0V2B2B-C-IMPLEMENTATION-CORRESPONDENCE",
            "the live compiler/runtime is not claimed to derive or consume these schemas",
        ),
        (
            "formal-and-cryptographic-claims",
            "F0V2B2B-C-FORMAL-CRYPTOGRAPHIC-CLAIMS",
            "finite executable agreement is not a proof, theorem truth, relation satisfaction, FS soundness, or Q1",
        ),
    )
    findings.extend(
        _finding(name, "CannotAnswer", code, detail)
        for name, code, detail in cannot_answer
    )

    serialized = [asdict(finding) for finding in findings]
    summary = {
        "total": len(serialized),
        "Affirmative": sum(item["outcome"] == "Affirmative" for item in serialized),
        "CannotAnswer": sum(item["outcome"] == "CannotAnswer" for item in serialized),
        "Refused": sum(item["outcome"] == "Refused" for item in serialized),
    }
    return {
        "aggregate": {"outcome": "Affirmative", "code": AGGREGATE},
        "summary": summary,
        "evidence": {
            "source_digest": source_digest,
            "owner_profile": source["owner_profile"],
            "predecessor": source["predecessor"],
            "recursive_compiler": recursive_stats,
            "iterative_compiler": iterative_stats,
            "closure": closure,
            "coverage": coverage,
            "views": schema_evidence,
            "total_inhabitants": total_values,
            "total_coverage_requirements": total_requirements,
            "mutations": mutation_evidence,
        },
        "findings": serialized,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        report = run()
        snapshot = _snapshot(report)
        if args.check:
            expected = _load_json(EXPECTED)
            if snapshot != expected:
                raise GateFailure("B2B result differs from expected-findings.json")
            summary = report["summary"]
            print(
                "[formal-source-view-schema-f0v2b2b] "
                f"{summary['total']}/{summary['total']} findings; "
                f"Affirmative/{AGGREGATE}; "
                f"{report['evidence']['total_inhabitants']} inhabitants, "
                f"{report['evidence']['total_coverage_requirements']} requirements"
            )
        else:
            print(json.dumps(snapshot, indent=2, sort_keys=True))
    except (GateFailure, model.SchemaError, independent.IndependentError) as error:
        print(f"[formal-source-view-schema-f0v2b2b] FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
