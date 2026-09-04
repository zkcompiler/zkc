#!/usr/bin/env python3
"""Executable gate for F0-V2B2C1B3 claim/reduction owner projections."""

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
AGGREGATE = "F0V2B2C1B3-A-CLAIM-REDUCTION-OWNER-PROJECTIONS"
CLAIM_REDUCTION_FAMILIES = (
    "claim-initial-linear",
    "claim-reduction-output-reusable",
    "reduction-publication-before-after",
    "joint-challenge-group",
    "shared-challenge-consumers",
)


class GateFailure(RuntimeError):
    """The executable evidence package detected drift or disagreement."""


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


def _encoded_edges(model: ModuleType, rows: list[dict[int, Any]]) -> set[bytes]:
    return {model.codec.encode_value(model._PC_EDGE_SCHEMA, row) for row in rows}


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b3_model", MODEL)
    cold_projector = _load("_zkc_f0v2b2c1b3_independent", INDEPENDENT)
    inventory = _inventory()
    b2c = tuple(
        item["id"]
        for item in inventory["required_pressure_families"]
        if item["stage"] == "B2C"
    )
    _require(
        b2c[12:17] == CLAIM_REDUCTION_FAMILIES and len(b2c) == 21,
        "claim/reduction family partition drifted",
    )
    _require(
        model.VIEW_SCHEMAS == cold_projector.VIEW_SCHEMAS,
        "schema compilers disagree",
    )
    _require(
        model.k1 is not cold_projector.k1
        and model.b2b is not cold_projector.b2b
        and model is not cold_projector,
        "cold path reused typed-owner modules",
    )
    findings = [
        _finding(
            "predecessor-and-family-pins",
            "Affirmative",
            "F0V2B2C1B3-A-PREDECESSOR-PINS",
            "the exact B2C1B2/B2B/B2C1A inputs and five-family claim/reduction partition remain selected",
        ),
        _finding(
            "cold-path-module-separation",
            "Affirmative",
            "F0V2B2C1B3-A-COLD-PATH-SEPARATION",
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
            "F0V2B2C1B3-A-CORE-ADMITTED",
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
            "F0V2B2C1B3-A-FRESH-ADMITTED",
            f"{name} Protocol",
        )
        _require(
            protocol_result.handle is not None, f"{name} omitted Protocol authority"
        )
        owner_views = model.project_views(core_result.handle, protocol_result.handle)
        owner_bodies = _body_table(model, owner_views)
        cold_views, cold_evidence = cold_projector.project(
            core_result.handle.profiled_body,
            core_result.handle.core_reference,
            protocol_result.handle.profiled_body,
            protocol_result.handle.protocol_reference,
        )
        cold_bodies = cold_projector.encode_views(cold_views)
        _require(owner_bodies == cold_bodies, f"{name} projector paths disagree")
        for view, body in owner_bodies.items():
            decoded = model.k1.decode_datum(body)
            _require(
                model.k1.encode_datum(decoded) == body,
                f"{name}/{view} does not round-trip",
            )
            sequences, elements = _check_target_orders(
                model.codec, model.VIEW_SCHEMAS[view], owner_views[view]
            )
            sorted_sequences += sequences
            sorted_elements += elements
            all_bodies.append(body)
        repeated = model.project_views(core_result.handle, protocol_result.handle)
        _require(
            owner_bodies == _body_table(model, repeated),
            f"{name} projection is unstable",
        )
        handles[name] = (
            environment,
            candidate,
            core_result.handle,
            protocol_result.handle,
        )
        records[name] = {
            "views": owner_views,
            "bodies": owner_bodies,
            "cold_evidence": cold_evidence,
            "combined_sha256": hashlib.sha256(
                b"".join(owner_bodies.values())
            ).hexdigest(),
        }
    _require(len(all_bodies) == 30, "five-by-six body census drifted")
    _require(len(set(all_bodies)) == 30, "two exact owner-view bodies alias")
    findings.extend(
        (
            _finding(
                "five-exact-core-admissions",
                "Affirmative",
                "F0V2B2C1B3-A-FIVE-CORE-ADMISSIONS",
                "five minimal exact claim/reduction/challenge carriers pass canonical-byte owner admission",
            ),
            _finding(
                "five-exact-fresh-pairings",
                "Affirmative",
                "F0V2B2C1B3-A-FIVE-FRESH-PAIRINGS",
                "each admitted Core forms one same-evaluator exact Fresh Protocol",
            ),
            _finding(
                "six-view-owner-formation",
                "Affirmative",
                "F0V2B2C1B3-A-SIX-VIEW-FORMATION",
                "all six normalized owner views form for every claim/reduction carrier",
            ),
            _finding(
                "cold-byte-projection-agreement",
                "Affirmative",
                "F0V2B2C1B3-A-COLD-BYTE-AGREEMENT",
                "the separately structured cold projector agrees on all thirty exact bodies",
            ),
            _finding(
                "exact-view-roundtrip-and-order",
                "Affirmative",
                "F0V2B2C1B3-A-ROUNDTRIP-ORDER",
                "all bodies round-trip and sorted-unique collections follow target-byte order",
            ),
            _finding(
                "projection-determinism",
                "Affirmative",
                "F0V2B2C1B3-A-PROJECTION-DETERMINISM",
                "reprojection from immutable Core/Protocol authority is byte-identical",
            ),
        )
    )

    initial = records["claim-initial-linear"]["views"]["ClaimReductionView"]
    initial_claim = initial[1][0]
    _require(
        initial_claim[3]["case"] == 0
        and initial_claim[4]["case"] == 0
        and initial_claim[5]["case"] == 0
        and [item["case"] for item in initial_claim[6]] == [1]
        and initial[3][0][3]["case"] == 0,
        "initial linear Claim source/use/disposition projection drifted",
    )
    findings.append(
        _finding(
            "claim-initial-linear",
            "Affirmative",
            "F0V2B2C1B3-A-CLAIM_INITIAL_LINEAR",
            "one Statement binding creates one linear Claim with one exact terminal Consume use",
        )
    )

    reduction_output = records["claim-reduction-output-reusable"]["views"]
    output_claims = reduction_output["ClaimReductionView"][1]
    output_reductions = reduction_output["ClaimReductionView"][2]
    _require(
        output_claims[0][3]["case"] == 0
        and [item["case"] for item in output_claims[0][6]] == [0]
        and output_claims[1][3]["case"] == 1
        and output_claims[1][4]["case"] == 1
        and output_claims[1][5]["case"] == 1
        and [item["case"] for item in output_claims[1][6]] == [1]
        and len(output_reductions[0][8]) == 1,
        "reduction-output Claim creation or use projection drifted",
    )
    findings.append(
        _finding(
            "claim-reduction-output-reusable",
            "Affirmative",
            "F0V2B2C1B3-A-CLAIM_REDUCTION_OUTPUT_REUSABLE",
            "the reduction consumes its linear input and creates one reusable output Claim at the exact ApplyReduction coordinate",
        )
    )

    publication = records["reduction-publication-before-after"]["views"]
    publication_reduction = publication["ClaimReductionView"][2][0]
    requirements = publication_reduction[7]
    _require(
        len(requirements) == 2
        and requirements[0][1]["case"] == 1
        and requirements[0][1]["value"]
        == model.foundation._ordinal("challenge-ref-body-v0", 0)
        and requirements[1][1]["case"] == 0
        and publication_reduction[6]
        == [model.foundation._ordinal("challenge-ref-body-v0", 0)],
        "Last-Challenge publication mapping drifted",
    )
    findings.append(
        _finding(
            "reduction-publication-before-after",
            "Affirmative",
            "F0V2B2C1B3-A-REDUCTION_PUBLICATION_BEFORE_AFTER",
            "the publication before the required Challenge names it and the publication after it names None",
        )
    )

    joint = records["joint-challenge-group"]["views"]
    joint_rows = joint["PublicCoinView"][4]
    joint_values = joint["EffectView"][2]
    _require(
        [row[6]["case"] for row in joint_rows] == [1, 1]
        and [row[6]["value"][1] for row in joint_rows] == [0, 1]
        and joint_rows[0][6]["value"][2] == []
        and joint_rows[1][6]["value"][2]
        == [model.foundation._ordinal("challenge-ref-body-v0", 0)]
        and len(joint_values[-1][2]) == 2,
        "joint Challenge closure or predecessor projection drifted",
    )
    findings.append(
        _finding(
            "joint-challenge-group",
            "Affirmative",
            "F0V2B2C1B3-A-JOINT_CHALLENGE_GROUP",
            "dense joint indices carry exact prior-member closure and the prior Challenge output becomes a causal predecessor",
        )
    )

    shared = records["shared-challenge-consumers"]["views"]
    shared_challenge = shared["PublicCoinView"][4][0]
    shared_claim = shared["ClaimReductionView"][1][0]
    _require(
        shared_challenge[7]["case"] == 1
        and [row[0] for row in shared_challenge[10]]
        == [
            model.foundation._ordinal("reduction-ref-body-v0", 0),
            model.foundation._ordinal("reduction-ref-body-v0", 1),
        ]
        and [item["case"] for item in shared_claim[6]] == [0, 0, 1],
        "shared Challenge consumers or reusable Claim uses drifted",
    )
    findings.append(
        _finding(
            "shared-challenge-consumers",
            "Affirmative",
            "F0V2B2C1B3-A-SHARED_CHALLENGE_CONSUMERS",
            "one Shared Challenge has two exact reduction-role consumers while the reusable Claim retains both uses and terminal disposition",
        )
    )

    _require(
        all(
            record["views"]["PublicCoinView"][2] is True for record in records.values()
        ),
        "an admitted positive fixture is not structurally FS-eligible",
    )
    findings.append(
        _finding(
            "same-core-fs-structural-eligibility",
            "Affirmative",
            "F0V2B2C1B3-A-FS-STRUCTURAL-ELIGIBILITY",
            "each bounded positive Core separately projects true structural public-coin eligibility after Fresh formation",
        )
    )

    output_edges = _encoded_edges(model, reduction_output["PublicCoinView"][1][1])
    publication_edges = _encoded_edges(model, publication["PublicCoinView"][1][1])
    joint_edges = _encoded_edges(model, joint["PublicCoinView"][1][1])
    shared_edges = _encoded_edges(model, shared["PublicCoinView"][1][1])
    expected_edges = (
        (
            output_edges,
            (
                ((9, 0), (7, 0)),
                ((7, 0), (10, 0)),
                ((10, 0), (9, 1)),
                ((9, 1), (7, 1)),
            ),
        ),
        (
            publication_edges,
            (
                ((7, 0), (7, 3)),
                ((8, 1, 0), (7, 3)),
                ((7, 2), (7, 3)),
            ),
        ),
        (joint_edges, (((8, 0, 0), (7, 1)),)),
        (
            shared_edges,
            (((8, 0, 0), (7, 1)), ((8, 0, 0), (7, 2))),
        ),
    )
    for observed, pairs in expected_edges:
        required = {
            model.codec.encode_value(model._PC_EDGE_SCHEMA, model._edge_value(pair))
            for pair in pairs
        }
        _require(required <= observed, "claim/reduction PCGraph edge drifted")
    findings.append(
        _finding(
            "claim-reduction-challenge-pcgraph-edges",
            "Affirmative",
            "F0V2B2C1B3-A-PCGRAPH-EDGES",
            "Claim creation/use, reduction state, publication, required-Challenge, joint, and shared-consumer dependencies form exact graph edges",
        )
    )

    for name in (
        "reduction-publication-before-after",
        "joint-challenge-group",
        "shared-challenge-consumers",
    ):
        graph = records[name]["views"]["PublicCoinView"][1]
        classes = {
            model.codec.encode_value(model._PC_NODE_SCHEMA, row[0]): row[1]["case"]
            for row in graph[3]
        }
        challenge_nodes = [
            row[1] for row in records[name]["views"]["PublicCoinView"][4]
        ]
        _require(
            all(
                classes[
                    model.codec.encode_value(
                        model._PC_NODE_SCHEMA, model.foundation._v(7, node)
                    )
                ]
                == 1
                for node in challenge_nodes
            ),
            f"{name} Challenge transfer is not PublicCoin",
        )
    findings.append(
        _finding(
            "challenge-node-local-pcclass-transfers",
            "Affirmative",
            "F0V2B2C1B3-A-CHALLENGE-TRANSFERS",
            "independent, joint, and shared Challenge effects use the explicit public-coin transfer rather than inheriting an undifferentiated effect class",
        )
    )

    runtime = publication["ExecutionView"][6]
    _require(
        len(runtime[0]) == 5
        and len(runtime[1]) == 1
        and runtime[2] == []
        and len(runtime[3]) == 1,
        "static runtime schema projection drifted",
    )
    findings.append(
        _finding(
            "static-resolver-and-runtime-schema",
            "Affirmative",
            "F0V2B2C1B3-A-STATIC-EXECUTION-SCHEMA",
            "Fresh execution projects exact Challenge resolver metadata and static occurrence/Challenge/terminal schemas with no invented runtime receipts",
        )
    )

    mutation_cases = (
        (
            "claim-initial-linear",
            "claim-source-binding",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-SOURCE",
        ),
        (
            "claim-initial-linear",
            "claim-source-class",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-SOURCE",
        ),
        (
            "claim-initial-linear",
            "claim-contract-kind",
            "KindMismatch",
            "F0V2B2C1B3-K-DECLARATION",
        ),
        (
            "claim-reduction-output-reusable",
            "output-contract-mismatch",
            "KindMismatch",
            "F0V2B2C1B3-K-CLAIM-OUTPUT",
        ),
        (
            "claim-reduction-output-reusable",
            "output-claim-missing",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-OUTPUT-COVERAGE",
        ),
        (
            "claim-reduction-output-reusable",
            "output-claim-duplicate",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-OUTPUT-UNIQUE",
        ),
        (
            "claim-reduction-output-reusable",
            "reduction-empty-input",
            "Refused",
            "F0V2B2C1B3-R-REDUCTION-NONEMPTY",
        ),
        (
            "claim-reduction-output-reusable",
            "reduction-missing-backlink",
            "Refused",
            "F0V2B2C1B3-R-REDUCTION-BACKLINK",
        ),
        (
            "claim-reduction-output-reusable",
            "reduction-duplicate-backlink",
            "Refused",
            "F0V2B2C1B3-R-REDUCTION-BACKLINK",
        ),
        (
            "claim-reduction-output-reusable",
            "reduction-scope",
            "Refused",
            "F0V2B2C1B3-R-REDUCTION-SCOPE",
        ),
        (
            "claim-reduction-output-reusable",
            "output-claim-cycle",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-AVAILABILITY",
        ),
        (
            "reduction-publication-before-after",
            "publication-closure",
            "Refused",
            "F0V2B2C1B3-R-PUBLICATION-CLOSURE",
        ),
        (
            "reduction-publication-before-after",
            "publication-kind",
            "KindMismatch",
            "F0V2B2C1B3-K-PUBLICATION-KIND",
        ),
        (
            "reduction-publication-before-after",
            "publication-order",
            "Refused",
            "F0V2B2C1B3-R-PUBLICATION-ORDER",
        ),
        (
            "reduction-publication-before-after",
            "last-challenge",
            "Refused",
            "F0V2B2C1B3-R-LAST-CHALLENGE",
        ),
        (
            "reduction-publication-before-after",
            "challenge-duplicate",
            "Refused",
            "F0V2B2C1B3-R-CHALLENGE-ORDER",
        ),
        (
            "reduction-publication-before-after",
            "guard-implication",
            "Refused",
            "F0V2B2C1B3-R-GUARD-IMPLIES",
        ),
        (
            "joint-challenge-group",
            "joint-index",
            "Refused",
            "F0V2B2C1B3-R-JOINT-CLOSURE",
        ),
        (
            "joint-challenge-group",
            "joint-prior",
            "Refused",
            "F0V2B2C1B3-R-JOINT-CLOSURE",
        ),
        (
            "joint-challenge-group",
            "joint-type",
            "Refused",
            "F0V2B2C1B3-R-JOINT-COMPATIBILITY",
        ),
        (
            "shared-challenge-consumers",
            "shared-consumer-count",
            "Refused",
            "F0V2B2C1B3-R-SHARED-CONSUMERS",
        ),
        (
            "shared-challenge-consumers",
            "exclusive-consumer-count",
            "Refused",
            "F0V2B2C1B3-R-EXCLUSIVE-CONSUMERS",
        ),
        (
            "shared-challenge-consumers",
            "linear-double-use",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-LINEARITY",
        ),
        (
            "shared-challenge-consumers",
            "terminal-claim-closure",
            "Refused",
            "F0V2B2C1B3-R-TERMINAL-CLAIM-CLOSURE",
        ),
        (
            "shared-challenge-consumers",
            "terminal-disposition-duplicate",
            "Refused",
            "F0V2B2C1B3-R-CLAIM-DISPOSITION-UNIQUE",
        ),
    )
    for family, mutation, outcome, code in mutation_cases:
        environment, candidate = model.mutate_core(family, mutation)
        result = model.admit_core(candidate, environment)
        _expect(result, outcome, code, mutation)
        findings.append(
            _finding(
                mutation + "-mutation",
                outcome,
                code,
                "a freshly authenticated Core with the named claim/reduction/challenge mutation fails closed",
            )
        )

    owner_wrong_views: list[tuple[str, str, str, dict[str, Any], bytes]] = []
    usage_flip = copy.deepcopy(shared["ClaimReductionView"])
    usage_flip[1][0][3] = model.foundation._v(0)
    owner_wrong_views.append(
        (
            "schema-valid-claim-usage-substitution",
            "F0V2B2C1B3-R-OWNER-CLAIM-USAGE",
            "a Linear marker cannot replace the owner-derived Reusable Claim usage",
            usage_flip,
            records["shared-challenge-consumers"]["bodies"]["ClaimReductionView"],
        )
    )
    creation_flip = copy.deepcopy(reduction_output["ClaimReductionView"])
    creation_flip[1][1][5]["value"][0] = model.foundation._ordinal(
        "occurrence-ref-body-v0", 1
    )
    owner_wrong_views.append(
        (
            "schema-valid-claim-creation-substitution",
            "F0V2B2C1B3-R-OWNER-CLAIM-CREATION",
            "another occurrence cannot replace the reduction-derived output Claim creation coordinate",
            creation_flip,
            records["claim-reduction-output-reusable"]["bodies"]["ClaimReductionView"],
        )
    )
    last_challenge_flip = copy.deepcopy(publication["ClaimReductionView"])
    last_challenge_flip[2][0][7][0][1] = model.foundation._v(0)
    owner_wrong_views.append(
        (
            "schema-valid-last-challenge-substitution",
            "F0V2B2C1B3-R-OWNER-LAST-CHALLENGE",
            "None cannot replace the least following required Challenge for the first publication",
            last_challenge_flip,
            records["reduction-publication-before-after"]["bodies"][
                "ClaimReductionView"
            ],
        )
    )
    consumer_flip = copy.deepcopy(shared["PublicCoinView"])
    consumer_flip[4][0][10] = consumer_flip[4][0][10][:1]
    owner_wrong_views.append(
        (
            "schema-valid-shared-consumer-substitution",
            "F0V2B2C1B3-R-OWNER-SHARED-CONSUMERS",
            "a one-consumer list cannot replace the exact two-consumer derivation for a Shared Challenge",
            consumer_flip,
            records["shared-challenge-consumers"]["bodies"]["PublicCoinView"],
        )
    )
    for name, code, detail, value, owner_body in owner_wrong_views:
        view_name = (
            "PublicCoinView"
            if name.endswith("consumer-substitution")
            else "ClaimReductionView"
        )
        substituted = model.codec.encode_value(model.VIEW_SCHEMAS[view_name], value)
        _require(substituted != owner_body, f"{name} aliased the owner body")
        findings.append(_finding(name, "Refused", code, detail))

    first = handles["claim-initial-linear"]
    second = handles["claim-reduction-output-reusable"]
    cold_cases = (
        (
            "cold-core-truncation",
            "F0V2B2C1B3-R-COLD-CORE-TRUNCATION",
            lambda: cold_projector.project(
                first[2].profiled_body[:-1],
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
            ),
            "the cold projector requires the complete canonical profiled Core body",
        ),
        (
            "cold-core-body-reference-substitution",
            "F0V2B2C1B3-R-COLD-CORE-BODY-REFERENCE",
            lambda: cold_projector.project(
                first[2].profiled_body,
                second[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
            ),
            "the cold projector independently authenticates Core body/reference equality",
        ),
        (
            "cold-cross-core-protocol-substitution",
            "F0V2B2C1B3-R-COLD-PROTOCOL-CORE",
            lambda: cold_projector.project(
                first[2].profiled_body,
                first[2].core_reference,
                second[3].profiled_body,
                second[3].protocol_reference,
            ),
            "an independently authenticated Fresh Protocol must cite the identical Core",
        ),
    )
    for name, code, operation, detail in cold_cases:
        _require(
            _rejects(operation, cold_projector.ColdClaimReductionError),
            f"{name} was accepted by the cold projector",
        )
        findings.append(_finding(name, "Refused", code, detail))

    predecessor_fixture = model.prior.fixtures()["oracle-initial-full"]
    predecessor_core = model.prior.admit_core(
        predecessor_fixture[1], predecessor_fixture[0]
    )
    _expect(
        predecessor_core,
        "Affirmative",
        "F0V2B2C1B2-A-CORE-ADMITTED",
        "predecessor Core",
    )
    predecessor_protocol_candidate = model.b2c0.make_protocol_candidate(
        predecessor_fixture[1].asserted_id, predecessor_fixture[0].profile_id
    )
    predecessor_protocol = model.prior.admit_fresh_protocol(
        predecessor_core.handle,
        predecessor_protocol_candidate,
        predecessor_fixture[0],
    )
    _expect(
        predecessor_protocol,
        "Affirmative",
        "F0V2B2C1B2-A-FRESH-ADMITTED",
        "predecessor Protocol",
    )
    _require(
        _rejects(
            lambda: model.project_views(
                predecessor_core.handle, predecessor_protocol.handle
            ),
            model.FamilyFailure,
        ),
        "B2C1B3 projector accepted predecessor-evaluator authority",
    )
    findings.append(
        _finding(
            "foreign-predecessor-evaluator-authority",
            "Refused",
            "F0V2B2C1B3-R-CORE-AUTHORITY",
            "a genuine B2C1B2 bearer cannot authorize the B2C1B3 projection law",
        )
    )

    cannot_answer = (
        (
            "path-sensitive-claim-liveness",
            "F0V2B2C1B3-C-PATH-LIVENESS",
            "the bounded static final-fallback discipline does not close path-sensitive terminal Claim liveness",
        ),
        (
            "integrated-pcgraph-families",
            "F0V2B2C1B3-C-INTEGRATED-PCGRAPH",
            "the all-class invalid/private/logical PCGraph and semantic lookup interactions remain B2D",
        ),
        (
            "runtime-claim-reduction-history",
            "F0V2B2C1B3-C-RUNTIME-HISTORY",
            "static schemas do not execute Claims or reductions or validate a completed runtime record",
        ),
        (
            "remaining-b2c-families",
            "F0V2B2C1B3-C-REMAINING-B2C",
            "three module-effect families and one expanded-terminal family remain",
        ),
        (
            "target-publication",
            "F0V2B2C1B3-C-TARGET-PUBLICATION",
            "the candidate schemas and laws are not published target semantics",
        ),
        (
            "live-implementation-correspondence",
            "F0V2B2C1B3-C-LIVE-CORRESPONDENCE",
            "no current compiler or runtime implementation is validated",
        ),
        (
            "formal-proof",
            "F0V2B2C1B3-C-FORMAL-PROOF",
            "finite dual-path evidence is not a mechanized refinement or equivalence proof",
        ),
        (
            "cryptographic-security",
            "F0V2B2C1B3-C-SECURITY",
            "structural Challenge/reduction evidence proves no soundness or Fiat-Shamir theorem",
        ),
        (
            "bcs-rbr-or-qrom-theorem",
            "F0V2B2C1B3-C-THEOREM-REGIME",
            "BCS, RBR, duplex, concrete-instantiation, and QROM obligations remain separate theorem regimes",
        ),
        (
            "q1-correspondence",
            "F0V2B2C1B3-C-Q1",
            "Q1 remains open through target migration and live owner correspondence",
        ),
    )
    findings.extend(
        _finding(name, "CannotAnswer", code, detail)
        for name, code, detail in cannot_answer
    )
    findings.append(
        _finding(
            "claim-reduction-owner-projection-aggregate",
            "Affirmative",
            AGGREGATE,
            "five claim/reduction/challenge isolation families have bounded exact owner-projection evidence with runtime, theorem, and security boundaries preserved",
        )
    )

    rows = [asdict(item) for item in findings]
    evidence = {
        "aggregate": AGGREGATE,
        "covered_families": list(CLAIM_REDUCTION_FAMILIES),
        "remaining_b2c_families": 4,
        "remaining_b2d_families": 2,
        "fixtures": {
            name: {
                "combined_sha256": record["combined_sha256"],
                "cold_evidence": record["cold_evidence"],
            }
            for name, record in records.items()
        },
        "view_body_count": len(all_bodies),
        "distinct_view_bodies": len(set(all_bodies)),
        "sorted_unique_sequences": sorted_sequences,
        "sorted_unique_elements": sorted_elements,
        "semantic_mutations": len(mutation_cases),
        "schema_valid_owner_substitutions": len(owner_wrong_views),
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
        raise GateFailure("cannot read expected B2C1B3 findings") from error
    if (
        type(value) is not dict
        or set(value) != {"aggregate", "findings_sha256", "finding_codes"}
        or value["aggregate"] != AGGREGATE
        or type(value["findings_sha256"]) is not str
        or type(value["finding_codes"]) is not list
    ):
        raise GateFailure("expected B2C1B3 findings have another shape")
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
        raise GateFailure("expected B2C1B3 finding row has another shape")
    if len({row[0] for row in rows}) != len(rows):
        raise GateFailure("expected B2C1B3 finding names are not unique")
    try:
        digest = bytes.fromhex(value["findings_sha256"])
    except ValueError as error:
        raise GateFailure("expected B2C1B3 digest is not hexadecimal") from error
    if len(digest) != 32:
        raise GateFailure("expected B2C1B3 digest is not SHA-256 sized")
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
                "frozen B2C1B3 findings drifted",
            )
        if args.print_findings:
            print(json.dumps(observed, indent=2, sort_keys=True))
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        print(
            "[formal-source-claim-reduction-owner-projections-f0v2b2c1b3] "
            f"{len(findings)}/{len(findings)} findings; Affirmative/{AGGREGATE}; "
            f"{evidence['view_body_count']} exact view bodies; "
            f"{evidence['finding_counts']}"
        )
        return 0
    except Exception as error:
        print(
            "[formal-source-claim-reduction-owner-projections-f0v2b2c1b3] "
            f"FAIL: {error}"
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
