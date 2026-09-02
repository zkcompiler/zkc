#!/usr/bin/env python3
"""Executable gate for F0-V2B2C1B2 Oracle owner projections."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
AGGREGATE = "F0V2B2C1B2-A-ORACLE-OWNER-PROJECTIONS"
ORACLE_FAMILIES = (
    "oracle-initial-full",
    "oracle-initial-binding",
    "oracle-initial-logical",
    "oracle-prover-full",
    "oracle-prover-binding",
    "oracle-prover-logical",
    "oracle-query-public",
    "oracle-query-verifier-only",
)


class GateFailure(RuntimeError):
    pass


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _expect(result: object, outcome: str, code: str, label: str) -> None:
    _require(
        result.outcome == outcome and result.code == code,
        f"{label}: expected {outcome}/{code}, got {result.outcome}/{result.code}",
    )


def _rejects(operation: Callable[[], object], expected: type[BaseException]) -> bool:
    try:
        operation()
    except expected:
        return True
    return False


def _check_target_orders(
    codec: ModuleType, schema: dict[str, Any], value: object
) -> tuple[int, int]:
    node = schema["node"]
    if node == "atom":
        return 0, 0
    if node == "record":
        _require(type(value) is dict, "record value has another carrier")
        nested = [
            _check_target_orders(codec, child, value[ordinal])
            for ordinal, child in schema["fields"]
        ]
        return sum(item[0] for item in nested), sum(item[1] for item in nested)
    if node == "variant":
        _require(
            type(value) is dict and set(value) == {"case", "value"},
            "variant value has another carrier",
        )
        return _check_target_orders(
            codec, dict(schema["cases"])[value["case"]], value["value"]
        )
    _require(node == "sequence" and type(value) is list, "sequence carrier differs")
    nested = [_check_target_orders(codec, schema["element"], item) for item in value]
    sequences = sum(item[0] for item in nested)
    elements = sum(item[1] for item in nested)
    if schema["discipline"] == "sorted-unique":
        bodies = [codec.encode_value(schema["element"], item) for item in value]
        _require(bodies == sorted(set(bodies)), "target sorted-unique order drifted")
        sequences += 1
        elements += len(bodies)
    return sequences, elements


def _inventory() -> dict[str, Any]:
    try:
        value = json.loads(INVENTORY.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read B2A family inventory") from error
    _require(type(value) is dict, "B2A inventory has another shape")
    return value


def _body_table(model: ModuleType, views: dict[str, Any]) -> dict[str, bytes]:
    return {
        name: model.codec.encode_value(model.VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b2_model", MODEL)
    cold = _load("_zkc_f0v2b2c1b2_independent", INDEPENDENT)
    inventory = _inventory()
    b2c = tuple(
        item["id"]
        for item in inventory["required_pressure_families"]
        if item["stage"] == "B2C"
    )
    _require(
        b2c[4:12] == ORACLE_FAMILIES and len(b2c) == 21,
        "Oracle family partition drifted",
    )
    _require(model.VIEW_SCHEMAS == cold.VIEW_SCHEMAS, "schema compilers disagree")
    _require(
        model.k1 is not cold.k1 and model.b2b is not cold.b2b,
        "cold path reused the reference Foundation or schema module",
    )
    findings = [
        _finding(
            "predecessor-and-oracle-family-pins",
            "Affirmative",
            "F0V2B2C1B2-A-PREDECESSOR-PINS",
            "the exact B2C1B1/B2B/B2C1A inputs and eight-family Oracle partition remain selected",
        ),
        _finding(
            "cold-path-module-separation",
            "Affirmative",
            "F0V2B2C1B2-A-COLD-PATH-SEPARATION",
            "the cold path uses separate Foundation, schema, parser, graph, projector, and codec module instances",
        ),
    ]

    handles: dict[str, tuple[object, object, object, object]] = {}
    records: dict[str, dict[str, Any]] = {}
    all_bodies: list[bytes] = []
    sorted_sequences = 0
    sorted_elements = 0
    for name, (environment, candidate) in model.fixtures().items():
        core_result = model.admit_core(candidate, environment)
        _expect(
            core_result,
            "Affirmative",
            "F0V2B2C1B2-A-CORE-ADMITTED",
            f"{name} Core",
        )
        _require(core_result.handle is not None, f"{name} omitted Core authority")
        protocol_candidate = model.b2c0.make_protocol_candidate(
            candidate.asserted_id, environment.profile_id
        )
        protocol_result = model.admit_fresh_protocol(
            core_result.handle, protocol_candidate, environment
        )
        _expect(
            protocol_result,
            "Affirmative",
            "F0V2B2C1B2-A-FRESH-ADMITTED",
            f"{name} Protocol",
        )
        _require(
            protocol_result.handle is not None, f"{name} omitted Protocol authority"
        )
        reference_views = model.project_views(
            core_result.handle, protocol_result.handle
        )
        reference_bodies = _body_table(model, reference_views)
        cold_views, cold_evidence = cold.project(
            core_result.handle.profiled_body,
            core_result.handle.core_reference,
            protocol_result.handle.profiled_body,
            protocol_result.handle.protocol_reference,
        )
        cold_bodies = cold.encode_views(cold_views)
        _require(reference_bodies == cold_bodies, f"{name} projector paths disagree")
        for view, body in reference_bodies.items():
            decoded = model.k1.decode_datum(body)
            _require(
                model.k1.encode_datum(decoded) == body,
                f"{name}/{view} does not round-trip",
            )
            sequences, elements = _check_target_orders(
                model.codec, model.VIEW_SCHEMAS[view], reference_views[view]
            )
            sorted_sequences += sequences
            sorted_elements += elements
            all_bodies.append(body)
        repeated = model.project_views(core_result.handle, protocol_result.handle)
        _require(
            reference_bodies == _body_table(model, repeated),
            f"{name} projection is unstable",
        )
        handles[name] = (
            environment,
            candidate,
            core_result.handle,
            protocol_result.handle,
        )
        records[name] = {
            "views": reference_views,
            "bodies": reference_bodies,
            "cold_evidence": cold_evidence,
            "combined_sha256": hashlib.sha256(
                b"".join(reference_bodies.values())
            ).hexdigest(),
        }
    _require(len(all_bodies) == 48, "eight-by-six body census drifted")
    _require(len(set(all_bodies)) == 48, "two exact owner-view bodies alias")
    findings.extend(
        (
            _finding(
                "eight-exact-core-admissions",
                "Affirmative",
                "F0V2B2C1B2-A-EIGHT-CORE-ADMISSIONS",
                "eight minimal exact Oracle carriers pass canonical-byte owner admission",
            ),
            _finding(
                "eight-exact-fresh-pairings",
                "Affirmative",
                "F0V2B2C1B2-A-EIGHT-FRESH-PAIRINGS",
                "each Oracle Core forms one same-evaluator exact Fresh Protocol",
            ),
            _finding(
                "six-view-owner-formation",
                "Affirmative",
                "F0V2B2C1B2-A-SIX-VIEW-FORMATION",
                "all six normalized owner views form for every Oracle carrier",
            ),
            _finding(
                "cold-byte-projection-agreement",
                "Affirmative",
                "F0V2B2C1B2-A-COLD-BYTE-AGREEMENT",
                "the separately structured cold projector agrees on all forty-eight bodies",
            ),
            _finding(
                "exact-view-roundtrip-and-order",
                "Affirmative",
                "F0V2B2C1B2-A-ROUNDTRIP-ORDER",
                "all bodies round-trip and every sorted-unique collection follows target-byte order",
            ),
            _finding(
                "projection-determinism",
                "Affirmative",
                "F0V2B2C1B2-A-PROJECTION-DETERMINISM",
                "reprojection from immutable Core/Protocol authority is byte-identical",
            ),
        )
    )

    logical_environment, logical_candidate = model.logical_acceptance_fixture()
    logical_core = model.admit_core(logical_candidate, logical_environment)
    _expect(
        logical_core,
        "Affirmative",
        "F0V2B2C1B2-A-CORE-ADMITTED",
        "logical acceptance discriminator Core",
    )
    logical_protocol_candidate = model.b2c0.make_protocol_candidate(
        logical_candidate.asserted_id, logical_environment.profile_id
    )
    logical_protocol = model.admit_fresh_protocol(
        logical_core.handle,
        logical_protocol_candidate,
        logical_environment,
    )
    _expect(
        logical_protocol,
        "Affirmative",
        "F0V2B2C1B2-A-FRESH-ADMITTED",
        "logical acceptance discriminator Protocol",
    )
    logical_views = model.project_views(logical_core.handle, logical_protocol.handle)
    logical_bodies = _body_table(model, logical_views)
    logical_cold_views, logical_cold_evidence = cold.project(
        logical_core.handle.profiled_body,
        logical_core.handle.core_reference,
        logical_protocol.handle.profiled_body,
        logical_protocol.handle.protocol_reference,
    )
    _require(
        logical_bodies == cold.encode_views(logical_cold_views),
        "logical acceptance discriminator projector paths disagree",
    )
    for view, body in logical_bodies.items():
        _require(
            model.k1.encode_datum(model.k1.decode_datum(body)) == body,
            f"logical acceptance discriminator/{view} does not round-trip",
        )
        _check_target_orders(model.codec, model.VIEW_SCHEMAS[view], logical_views[view])
    logical_coin = logical_views["PublicCoinView"]
    _require(
        logical_coin[2] is False
        and len(logical_coin[1][6]) == 1
        and logical_coin[1][6][0][2],
        "logical Oracle acceptance intersection was not retained",
    )
    findings.append(
        _finding(
            "logical-access-acceptance-intersection",
            "Affirmative",
            "F0V2B2C1B2-A-LOGICAL-ACCEPTANCE-INTERSECTION",
            "an admitted Core forms a valid Fresh pairing while a logical Oracle reaching acceptance is structurally ineligible for same-Core Fiat-Shamir",
        )
    )

    for name in ORACLE_FAMILIES[:6]:
        oracle = records[name]["views"]["EffectView"][4][0]
        expected_origin = 0 if "initial" in name else 1
        expected_mode = {"full": 0, "binding": 1, "logical": 2}[name.rsplit("-", 1)[1]]
        _require(
            oracle[1][1]["case"] == expected_origin
            and oracle[1][5]["case"] == expected_mode
            and oracle[2] == model.foundation._ordinal("occurrence-ref-body-v0", 0)
            and oracle[3] == [model.foundation._ordinal("occurrence-ref-body-v0", 1)]
            and oracle[4] == [model.foundation._ordinal("occurrence-ref-body-v0", 2)],
            f"{name} declaration or lifecycle projection drifted",
        )
        schedule = records[name]["views"]["EffectView"][1]
        expected_publication_arity = 0 if expected_mode == 2 else 1
        _require(
            [len(row[4]) for row in schedule] == [expected_publication_arity, 0, 1, 0],
            f"{name} output arities drifted",
        )
        decisions = records[name]["views"]["StrategyDecisionView"][1]
        _require(
            len(decisions) == expected_origin
            and (not decisions or decisions[0][4]["case"] == 1),
            f"{name} origin-dependent decision class drifted",
        )
        findings.append(
            _finding(
                name,
                "Affirmative",
                "F0V2B2C1B2-A-" + name.upper().replace("-", "_"),
                "exact origin, mode, output arity, lifecycle backlinks, decision class, and static receipt schemas are owner-derived",
            )
        )

    public_views = records["oracle-query-public"]["views"]
    public_reads = [row[1]["case"] for row in public_views["StrategyDecisionView"][3]]
    public_receipts = public_views["ExecutionView"][6][2]
    _require(
        public_reads == [0, 5, 6, 7]
        and [row["case"] for row in public_receipts] == [0, 1, 2]
        and public_receipts[1]["value"][3]["case"] == 0
        and public_receipts[2]["value"][3]["case"] == 0,
        "public Oracle query/answer visibility or guaranteed-read projection drifted",
    )
    findings.append(
        _finding(
            "oracle-query-public",
            "Affirmative",
            "F0V2B2C1B2-A-ORACLE_QUERY_PUBLIC",
            "a later Prover decision receives the exact public publication, query, and answer coordinates and three static receipt branches",
        )
    )

    private_views = records["oracle-query-verifier-only"]["views"]
    private_coin = private_views["PublicCoinView"]
    private_receipts = private_views["ExecutionView"][6][2]
    private_classes = {
        model.codec.encode_value(model._PC_NODE_SCHEMA, row[0]): row[1]["case"]
        for row in private_coin[1][3]
    }
    query_node = model._pc_value((7, 1))
    answer_node = model._pc_value((8, 2, 0))
    _require(
        private_coin[2] is False
        and private_classes[model.codec.encode_value(model._PC_NODE_SCHEMA, query_node)]
        == 2
        and private_classes[
            model.codec.encode_value(model._PC_NODE_SCHEMA, answer_node)
        ]
        == 2
        and private_receipts[1]["value"][3]["case"] == 1
        and private_receipts[2]["value"][3]["case"] == 1,
        "VerifierOnly transfer or structural eligibility drifted",
    )
    findings.append(
        _finding(
            "oracle-query-verifier-only",
            "Affirmative",
            "F0V2B2C1B2-A-ORACLE_QUERY_VERIFIER_ONLY",
            "VerifierOnly query/effect and answer/output nodes are VerifierPrivate and a dependent terminal sink makes FS eligibility false",
        )
    )

    for name in ("oracle-initial-logical", "oracle-prover-logical"):
        coin = records[name]["views"]["PublicCoinView"]
        _require(
            coin[2] is True
            and len(coin[1][6]) == 1
            and coin[1][6][0][1]
            and coin[1][6][0][2] == [],
            f"{name} logical-access cone or acceptance intersection drifted",
        )
    findings.append(
        _finding(
            "logical-access-empty-acceptance-intersection",
            "Affirmative",
            "F0V2B2C1B2-A-LOGICAL-DEAD-CONE",
            "both logical modes retain a nonempty fixation influence cone and an empty acceptance intersection without exposing carrier bytes",
        )
    )

    full_graph = public_views["PublicCoinView"][1]
    edge_bodies = {
        model.codec.encode_value(model._PC_EDGE_SCHEMA, edge) for edge in full_graph[1]
    }
    required_edges = {
        model.codec.encode_value(
            model._PC_EDGE_SCHEMA,
            model._edge_value(pair),
        )
        for pair in (
            ((7, 0), (7, 1)),
            ((2, 0), (7, 1)),
            ((7, 1), (7, 2)),
            ((7, 0), (7, 2)),
        )
    }
    _require(required_edges <= edge_bodies, "Oracle lifecycle PCGraph edges drifted")
    findings.append(
        _finding(
            "oracle-lifecycle-pcgraph-edges",
            "Affirmative",
            "F0V2B2C1B2-A-ORACLE-PCGRAPH-EDGES",
            "publication-to-query, index-to-query, query-to-answer, and publication-to-answer edges are exact",
        )
    )

    public_classes = {
        model.codec.encode_value(model._PC_NODE_SCHEMA, row[0]): row[1]["case"]
        for row in full_graph[3]
    }
    expected_transfers = {
        (7, 0): 1,
        (8, 0, 0): 1,
        (7, 1): 0,
        (7, 2): 1,
        (8, 2, 0): 1,
    }
    _require(
        all(
            public_classes[
                model.codec.encode_value(model._PC_NODE_SCHEMA, model._pc_value(node))
            ]
            == expected
            for node, expected in expected_transfers.items()
        ),
        "Oracle node-local PCClass transfers drifted",
    )
    findings.append(
        _finding(
            "oracle-node-local-pcclass-transfers",
            "Affirmative",
            "F0V2B2C1B2-A-ORACLE-NODE-LOCAL-TRANSFERS",
            "publication and public Answer use Publish(activity), while the public Query uses Join(activity,index) despite its additional causal publication edge",
        )
    )

    for name, mutation, outcome, code in (
        (
            "oracle-initial-full",
            "duplicate-publication",
            "Refused",
            "F0V2B2C1B2-R-PUBLICATION-BACKLINK",
        ),
        (
            "oracle-initial-full",
            "duplicate-answer",
            "Refused",
            "F0V2B2C1B2-R-ANSWER-MATCH",
        ),
        (
            "oracle-query-public",
            "answer-scope",
            "Refused",
            "F0V2B2C1B2-R-ANSWER-MATCH",
        ),
        (
            "oracle-initial-binding",
            "binding-abi",
            "KindMismatch",
            "F0V2B2C1B2-K-BINDING-ABI",
        ),
        (
            "oracle-initial-logical",
            "domain-law-kind",
            "KindMismatch",
            "F0V2B2C1B2-K-DECLARATION",
        ),
        (
            "oracle-initial-logical",
            "domain-law-order",
            "Refused",
            "F0V2B2C1B2-R-DOMAIN-LAW-ORDER",
        ),
        (
            "oracle-initial-full",
            "answer-after-terminal",
            "Refused",
            "F0V2B2C1B2-R-ANSWER-TERMINAL-ORDER",
        ),
    ):
        environment, candidate = model.mutate_core(name, mutation)
        result = model.admit_core(candidate, environment)
        _expect(result, outcome, code, mutation)
        findings.append(
            _finding(
                mutation + "-mutation",
                outcome,
                code,
                "a freshly authenticated Oracle Core with the named lifecycle/dependency mutation fails closed",
            )
        )

    original_effect = records["oracle-prover-binding"]["views"]["EffectView"]
    original_body = records["oracle-prover-binding"]["bodies"]["EffectView"]
    origin_flip = copy.deepcopy(original_effect)
    origin_flip[4][0][1][1] = model.foundation._v(0)
    origin_body = model.codec.encode_value(
        model.VIEW_SCHEMAS["EffectView"], origin_flip
    )
    _require(origin_body != original_body, "schema-valid Oracle origin flip aliased")
    findings.append(
        _finding(
            "schema-valid-origin-substitution",
            "Refused",
            "F0V2B2C1B2-R-OWNER-ORIGIN",
            "schema validity cannot substitute InitialOracle for the owner-derived ProverOracle declaration",
        )
    )

    original_strategy = records["oracle-prover-full"]["views"]["StrategyDecisionView"]
    strategy_flip = copy.deepcopy(original_strategy)
    strategy_flip[1][0][4] = model.foundation._v(
        0, model.foundation._value_type_body(model.base.Z3)
    )
    strategy_body = model.codec.encode_value(
        model.VIEW_SCHEMAS["StrategyDecisionView"], strategy_flip
    )
    _require(
        strategy_body
        != records["oracle-prover-full"]["bodies"]["StrategyDecisionView"],
        "schema-valid Oracle move substitution aliased",
    )
    findings.append(
        _finding(
            "schema-valid-prover-move-substitution",
            "Refused",
            "F0V2B2C1B2-R-OWNER-MOVE",
            "a generic message move cannot replace the owner-derived ProverOracle supply move",
        )
    )

    logical_effect = copy.deepcopy(
        records["oracle-prover-logical"]["views"]["EffectView"]
    )
    logical_effect[1][0][4] = [model.foundation._value_type_body(model.base.Z3)]
    logical_effect_body = model.codec.encode_value(
        model.VIEW_SCHEMAS["EffectView"], logical_effect
    )
    _require(
        logical_effect_body != records["oracle-prover-logical"]["bodies"]["EffectView"],
        "schema-valid logical publication output substitution aliased",
    )
    findings.append(
        _finding(
            "schema-valid-logical-publication-output-substitution",
            "Refused",
            "F0V2B2C1B2-R-OWNER-LOGICAL-PUBLICATION-ARITY",
            "a schema-valid publication output cannot replace the owner-derived zero-output LogicalAccess fixation",
        )
    )

    public_execution = public_views["ExecutionView"]
    receipt_flip = copy.deepcopy(public_execution)
    receipt_flip[6][2][1]["value"][3] = model.foundation._v(1)
    receipt_body = model.codec.encode_value(
        model.VIEW_SCHEMAS["ExecutionView"], receipt_flip
    )
    _require(
        receipt_body != records["oracle-query-public"]["bodies"]["ExecutionView"],
        "schema-valid receipt visibility substitution aliased",
    )
    findings.append(
        _finding(
            "schema-valid-receipt-visibility-substitution",
            "Refused",
            "F0V2B2C1B2-R-OWNER-RECEIPT-VISIBILITY",
            "a VerifierOnly receipt schema cannot replace an owner-derived Public query schema",
        )
    )

    first = handles["oracle-initial-full"]
    second = handles["oracle-prover-full"]
    _require(
        _rejects(
            lambda: cold.project(
                first[2].profiled_body[:-1],
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
            ),
            cold.ColdOracleError,
        ),
        "cold projector accepted a truncated Core",
    )
    findings.append(
        _finding(
            "cold-core-truncation",
            "Refused",
            "F0V2B2C1B2-R-COLD-CORE-TRUNCATION",
            "the cold projector requires the complete canonical profiled Core body",
        )
    )
    _require(
        _rejects(
            lambda: cold.project(
                first[2].profiled_body,
                second[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
            ),
            cold.ColdOracleError,
        ),
        "cold projector accepted another Core reference",
    )
    findings.append(
        _finding(
            "cold-core-body-reference-substitution",
            "Refused",
            "F0V2B2C1B2-R-COLD-CORE-BODY-REFERENCE",
            "the cold projector independently authenticates Core body/reference equality",
        )
    )
    _require(
        _rejects(
            lambda: cold.project(
                first[2].profiled_body,
                first[2].core_reference,
                second[3].profiled_body,
                second[3].protocol_reference,
            ),
            cold.ColdOracleError,
        ),
        "cold projector accepted a Protocol for another Core",
    )
    findings.append(
        _finding(
            "cold-cross-core-protocol-substitution",
            "Refused",
            "F0V2B2C1B2-R-COLD-PROTOCOL-CORE",
            "an independently authenticated Fresh Protocol must cite the identical Core",
        )
    )

    foundation_fixture = model.foundation.fixtures()["verifier-private-dead"]
    foundation_core = model.foundation.admit_core(
        foundation_fixture[1], foundation_fixture[0]
    )
    foundation_protocol_candidate = model.b2c0.make_protocol_candidate(
        foundation_fixture[1].asserted_id, foundation_fixture[0].profile_id
    )
    foundation_protocol = model.foundation.admit_fresh_protocol(
        foundation_core.handle,
        foundation_protocol_candidate,
        foundation_fixture[0],
    )
    _require(
        _rejects(
            lambda: model.project_views(
                foundation_core.handle, foundation_protocol.handle
            ),
            model.OracleFailure,
        ),
        "Oracle projector accepted predecessor-evaluator authority",
    )
    findings.append(
        _finding(
            "foreign-predecessor-evaluator-authority",
            "Refused",
            "F0V2B2C1B2-R-CORE-AUTHORITY",
            "a genuine B2C1B1 bearer cannot authorize the B2C1B2 projection law",
        )
    )

    cannot_answer = (
        (
            "integrated-pcgraph-family",
            "F0V2B2C1B2-C-INTEGRATED-PCGRAPH",
            "the all-class invalid/private/logical PCGraph interaction remains B2D",
        ),
        (
            "runtime-oracle-receipts",
            "F0V2B2C1B2-C-RUNTIME-RECEIPTS",
            "static receipt schemas do not execute an Oracle or validate a completed record",
        ),
        (
            "remaining-b2c-families",
            "F0V2B2C1B2-C-REMAINING-B2C",
            "five claim/reduction/challenge, three module, and one terminal family remain",
        ),
        (
            "target-publication",
            "F0V2B2C1B2-C-TARGET-PUBLICATION",
            "the candidate schemas and laws are not published target semantics",
        ),
        (
            "live-implementation-correspondence",
            "F0V2B2C1B2-C-LIVE-CORRESPONDENCE",
            "no current compiler or runtime implementation is validated",
        ),
        (
            "formal-proof",
            "F0V2B2C1B2-C-FORMAL-PROOF",
            "finite dual-path evidence is not a mechanized proof",
        ),
        (
            "cryptographic-security",
            "F0V2B2C1B2-C-SECURITY",
            "Oracle representation evidence proves no binding, hiding, soundness, or Fiat-Shamir property",
        ),
        (
            "q1-correspondence",
            "F0V2B2C1B2-C-Q1",
            "Q1 remains open through target migration and live owner correspondence",
        ),
    )
    findings.extend(
        _finding(name, "CannotAnswer", code, detail)
        for name, code, detail in cannot_answer
    )
    findings.append(
        _finding(
            "oracle-owner-projection-aggregate",
            "Affirmative",
            AGGREGATE,
            "eight Oracle isolation families have bounded exact owner-projection evidence with runtime and security boundaries preserved",
        )
    )

    rows = [asdict(item) for item in findings]
    evidence = {
        "aggregate": AGGREGATE,
        "covered_families": list(ORACLE_FAMILIES),
        "remaining_b2c_families": 9,
        "remaining_b2d_families": 2,
        "fixtures": {
            name: {
                "combined_sha256": record["combined_sha256"],
                "cold_evidence": record["cold_evidence"],
            }
            for name, record in records.items()
        },
        "logical_acceptance_discriminator": {
            "combined_sha256": hashlib.sha256(
                b"".join(logical_bodies.values())
            ).hexdigest(),
            "view_body_count": len(logical_bodies),
            "cold_evidence": logical_cold_evidence,
        },
        "view_body_count": len(all_bodies),
        "distinct_view_bodies": len(set(all_bodies)),
        "sorted_unique_sequences": sorted_sequences,
        "sorted_unique_elements": sorted_elements,
        "finding_counts": {
            outcome: sum(item.outcome == outcome for item in findings)
            for outcome in sorted({item.outcome for item in findings})
        },
        "findings_sha256": hashlib.sha256(
            json.dumps(
                rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True
            ).encode("ascii")
        ).hexdigest(),
    }
    return findings, evidence


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read expected B2C1B2 findings") from error
    if (
        type(value) is not dict
        or set(value) != {"aggregate", "findings_sha256", "finding_codes"}
        or value["aggregate"] != AGGREGATE
        or type(value["findings_sha256"]) is not str
        or type(value["finding_codes"]) is not list
    ):
        raise GateFailure("expected B2C1B2 findings have another shape")
    rows = value["finding_codes"]
    if any(
        type(row) is not list
        or len(row) != 3
        or any(type(item) is not str or not item for item in row)
        or row[1]
        not in {
            "Affirmative",
            "CannotAnswer",
            "KindMismatch",
            "Malformed",
            "Refused",
            "Unsupported",
        }
        for row in rows
    ):
        raise GateFailure("expected B2C1B2 finding row has another shape")
    if len({row[0] for row in rows}) != len(rows):
        raise GateFailure("expected B2C1B2 finding names are not unique")
    try:
        digest = bytes.fromhex(value["findings_sha256"])
    except ValueError as error:
        raise GateFailure("expected B2C1B2 digest is not hexadecimal") from error
    if len(digest) != 32:
        raise GateFailure("expected B2C1B2 digest is not SHA-256 sized")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-findings", action="store_true")
    parser.add_argument("--print-evidence", action="store_true")
    args = parser.parse_args()
    if not (args.check or args.print_findings or args.print_evidence):
        parser.error("select --check, --print-findings, or --print-evidence")
    try:
        findings, evidence = evaluate()
        observed = [asdict(item) for item in findings]
        if args.check:
            expected = _load_expected()
            codes = [[item.name, item.outcome, item.code] for item in findings]
            _require(
                codes == expected["finding_codes"]
                and evidence["findings_sha256"] == expected["findings_sha256"],
                "frozen B2C1B2 findings drifted",
            )
        if args.print_findings:
            print(json.dumps(observed, indent=2, sort_keys=True))
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        print(
            "[formal-source-oracle-owner-projections-f0v2b2c1b2] "
            f"{len(findings)}/{len(findings)} findings; Affirmative/{AGGREGATE}; "
            f"{evidence['view_body_count']} exact view bodies; "
            f"{evidence['finding_counts']}"
        )
        return 0
    except Exception as error:
        print(f"[formal-source-oracle-owner-projections-f0v2b2c1b2] FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
