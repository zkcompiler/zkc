#!/usr/bin/env python3
"""Run the F0-V2B2D1 integrated PublicCoin graph closure gate."""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import pickle
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
PREDECESSOR_EXPECTED = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-projections-f0v2b2c1b5b2"
    / "expected-findings.json"
)
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
TARGET_SOURCE = ROOT / "docs-next/pir/interactive-core.md"

AGGREGATE = "F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE"
PROFILE_DIGEST = "9a971206c68eab0b5b5e8124787bfce2f5335467a576b242190750e773941d2f"
PROFILE_BODY_SHA256 = "fbba36f4b0e15dcc55ef60d4d251b0286c9627726c1bf6f827c95784fcd00f70"
GRAMMAR_SHA256 = "b380d872d7400ea6d22c225733700ba2506427b16a03b7491d2136ac2f23c23b"
SCHEMA_SOURCE_SHA256 = (
    "c06c9e13e1c10d33943325c5b234f1f7178b3aec3502df874284451ac0195ee7"
)
EXPECTED_SCENARIOS = {
    "integrated-baseline": (91, 151, (55, 28, 5, 3), 49, 9, 0, 0, True),
    "private-verifier-output-sink": (
        91,
        151,
        (53, 28, 7, 3),
        49,
        9,
        1,
        0,
        False,
    ),
    "invalid-module-control-sink": (
        91,
        151,
        (55, 28, 5, 3),
        50,
        10,
        1,
        0,
        False,
    ),
    "history-challenge-condition": (
        91,
        151,
        (54, 12, 5, 20),
        49,
        9,
        0,
        0,
        False,
    ),
    "logical-reject-preemption": (
        91,
        146,
        (54, 29, 5, 3),
        48,
        9,
        0,
        1,
        False,
    ),
}


class GateFailure(RuntimeError):
    """The package detected drift, disagreement, or an accepted mutation."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


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


def _algorithm_preimages(model: ModuleType, fixture: object) -> tuple[Any, ...]:
    return tuple(
        sorted(
            (
                (
                    item.identity.internal_reference(),
                    model.k1.algorithm_preimage(item),
                )
                for item in fixture.algorithms
            ),
            key=lambda item: item[0],
        )
    )


def _cold_project(
    model: ModuleType, independent: ModuleType, fixture: object
) -> tuple[dict[int, Any], dict[str, Any]]:
    return independent.project(
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
        model.raw_module_sources(fixture.environment),
        _algorithm_preimages(model, fixture),
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )


def _evidence_value(value: object) -> dict[str, Any]:
    return {
        "nodes": value.nodes,
        "edges": value.edges,
        "topological": value.topological,
        "classes": dict(value.classes),
        "sinks": value.sinks,
        "acceptance_sinks": value.acceptance_sinks,
        "private_predecessors": value.private_predecessors,
        "logical_cones": dict(value.logical_cones),
        "logical_intersections": dict(value.logical_intersections),
        "challenge_validity": dict(value.challenge_validity),
        "challenge_observation_order": dict(value.challenge_observation_order),
        "eligible": value.eligible,
    }


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


def _remove_edge(model: ModuleType, value: dict[int, Any], edge: object) -> None:
    encoded = model.codec.encode_value(model._PC_EDGE_SCHEMA, model._edge_value(edge))
    rows = value[1][1]
    retained = [
        row
        for row in rows
        if model.codec.encode_value(model._PC_EDGE_SCHEMA, row) != encoded
    ]
    _require(len(retained) + 1 == len(rows), f"test edge is absent: {edge}")
    value[1][1] = retained


def _owner_substitutions(
    model: ModuleType, owner_value: dict[int, Any]
) -> tuple[tuple[str, bytes], ...]:
    substitutions: list[tuple[str, bytes]] = []

    changed = copy.deepcopy(owner_value)
    changed[1][1] = changed[1][1][1:]
    substitutions.append(
        (
            "graph-edge",
            model.codec.encode_value(model.VIEW_SCHEMAS["PublicCoinView"], changed),
        )
    )

    changed = copy.deepcopy(owner_value)
    old_case = changed[1][3][0][1]["case"]
    changed[1][3][0][1] = model.foundation._v((old_case + 1) % 4)
    substitutions.append(
        (
            "class-transfer",
            model.codec.encode_value(model.VIEW_SCHEMAS["PublicCoinView"], changed),
        )
    )

    changed = copy.deepcopy(owner_value)
    changed[1][4] = changed[1][4][1:]
    substitutions.append(
        (
            "sink",
            model.codec.encode_value(model.VIEW_SCHEMAS["PublicCoinView"], changed),
        )
    )

    changed = copy.deepcopy(owner_value)
    _remove_edge(model, changed, ((11, 0), (6, 21)))
    substitutions.append(
        (
            "terminal-preemption",
            model.codec.encode_value(model.VIEW_SCHEMAS["PublicCoinView"], changed),
        )
    )

    changed = copy.deepcopy(owner_value)
    injected = changed[1][5][0]
    changed[1][6][0][2] = [injected]
    substitutions.append(
        (
            "logical-intersection",
            model.codec.encode_value(model.VIEW_SCHEMAS["PublicCoinView"], changed),
        )
    )
    return tuple(substitutions)


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2d1_model", MODEL)
    independent = _load("_zkc_f0v2b2d1_independent", INDEPENDENT)
    findings: list[Finding] = []

    predecessor = json.loads(PREDECESSOR_EXPECTED.read_text(encoding="utf-8"))
    _require(
        predecessor["aggregate"] == "F0V2B2C1B5B2-A-EXACT-TERMINAL-OWNER-PROJECTIONS"
        and predecessor["findings_sha256"]
        == "583c0dfca38bc7a7d99b380039044eb936e58e7ca0409f36610975572601f437",
        "B5B2 predecessor result drifted",
    )
    findings.append(
        _finding("predecessor-pin", "Affirmative", "F0V2B2D1-A-PREDECESSOR-PIN")
    )

    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    b2d = tuple(
        item["id"]
        for item in inventory["required_pressure_families"]
        if item["stage"] == "B2D"
    )
    _require(
        b2d
        == (
            "pcgraph-invalid-private-logical",
            "fresh-runtime-oracle-receipts",
        ),
        "B2D family partition drifted",
    )
    findings.extend(
        (
            _finding("b2d-family-pin", "Affirmative", "F0V2B2D1-A-FAMILY-PIN"),
            _finding(
                "runtime-family-deferred",
                "CannotAnswer",
                "F0V2B2D1-C-FRESH-RUNTIME-RECEIPTS",
            ),
        )
    )

    target = TARGET_SOURCE.read_text(encoding="utf-8")
    _require(
        "PublishOracle with LogicalAccess:" in target
        and "effect = Publish(activity); there is no output node" in target
        and "the effect node of every Public Query together with the producer node"
        in target
        and "of its index" in target,
        "migrated logical-publication or public-Query coordinates drifted",
    )
    node_names = (
        "PublicInputNode",
        "VerifierPrivateInputNode",
        "ConstantNode",
        "DerivedValueNode",
        "ScopeOpeningNode",
        "BindingObservationNode",
        "OccurrenceActivityNode",
        "OccurrenceEffectNode",
        "OccurrenceOutputNode",
        "ClaimStateNode",
        "ReductionStateNode",
        "TerminalDecisionNode",
        "ModuleControlNode",
        "ModuleOutputNode",
    )
    _require(
        all(name in target for name in node_names)
        and "PCClass = StaticPublic | PublicHistory | VerifierPrivate | Invalid"
        in target
        and "terminal-preemption edges" in target
        and "LogicalAccessInfluenceCone(o) intersect AcceptanceSinks(core) = {}"
        in target
        and "F0V2B2D1" not in target,
        "target graph law or nonpublication boundary drifted",
    )
    findings.extend(
        (
            _finding("target-law-pin", "Affirmative", "F0V2B2D1-A-TARGET-LAW-PIN"),
            _finding(
                "target-authority-untouched",
                "Affirmative",
                "F0V2B2D1-A-NONPUBLICATION",
            ),
        )
    )

    model_source = MODEL.read_text(encoding="utf-8")
    independent_source = INDEPENDENT.read_text(encoding="utf-8")
    _require(
        "derive_graph(core" in model_source
        and "def _derive_graph(" in independent_source
        and "model.py" not in independent_source
        and "import model" not in independent_source
        and "from model" not in independent_source,
        "owner and cold graph sources are not separated",
    )
    _require(
        model is not independent
        and model.k1 is not independent.k1
        and model.codec is not independent.codec,
        "cold path reused typed-owner module instances",
    )
    findings.extend(
        (
            _finding(
                "graph-source-separation", "Affirmative", "F0V2B2D1-A-GRAPH-SEPARATION"
            ),
            _finding(
                "cold-module-separation", "Affirmative", "F0V2B2D1-A-COLD-MODULES"
            ),
        )
    )

    profile = model.profile_evidence()
    cold_schema = independent.configure(PROFILE_DIGEST, PROFILE_BODY_SHA256)
    _require(
        profile["candidate_interaction_digest"] == PROFILE_DIGEST
        and profile["candidate_interaction_body_sha256"] == PROFILE_BODY_SHA256
        and profile["schema_grammar_sha256"] == GRAMMAR_SHA256
        and profile["schema_source_sha256"] == SCHEMA_SOURCE_SHA256
        and cold_schema["schema_grammar_sha256"] == GRAMMAR_SHA256
        and cold_schema["schema_source_sha256"] == SCHEMA_SOURCE_SHA256,
        "candidate profile or grammar identity drifted",
    )
    _require(
        model.VIEW_SCHEMAS == independent.VIEW_SCHEMAS
        and model.VIEW_SCHEMA_STATS["definition_count"] == 88
        and model.VIEW_SCHEMA_STATS["source_node_count"] == 459
        and model.VIEW_SCHEMA_STATS["maximum_source_depth"] == 17,
        "schema compiler paths disagree",
    )
    findings.extend(
        (
            _finding(
                "profile-and-grammar-pin", "Affirmative", "F0V2B2D1-A-GRAMMAR-BINDING"
            ),
            _finding(
                "dual-schema-agreement", "Affirmative", "F0V2B2D1-A-SCHEMA-AGREEMENT"
            ),
        )
    )

    owner_values: dict[str, dict[int, Any]] = {}
    owner_bodies: dict[str, bytes] = {}
    owner_handles: dict[str, object] = {}
    graph_metrics: dict[str, Any] = {}
    sorted_sequences = 0
    sorted_elements = 0
    for name, fixture in model.fixtures().items():
        core_result = model.admit_core(fixture.candidate, fixture.environment)
        _expect(
            core_result,
            "Affirmative",
            "F0V2B2D1-A-CORE-ADMITTED",
            f"{name} Core",
        )
        _require(core_result.handle is not None, f"{name} omitted Core authority")
        protocol_result = model.admit_fresh_protocol(
            core_result.handle, fixture.protocol_candidate, fixture.environment
        )
        _expect(
            protocol_result,
            "Affirmative",
            "F0V2B2D1-A-FRESH-ADMITTED",
            f"{name} Fresh Protocol",
        )
        owner_value, owner_evidence = model.project_public_coin(core_result.handle)
        owner_body = model.public_coin_body(core_result.handle)
        cold_value, cold_evidence = _cold_project(model, independent, fixture)
        cold_body = independent.encode_public_coin(cold_value)
        _require(owner_body == cold_body, f"{name} owner/cold bytes disagree")
        _require(
            _evidence_value(owner_evidence) == cold_evidence,
            f"{name} owner/cold evidence tables disagree",
        )
        _require(
            owner_body == model.public_coin_body(core_result.handle),
            f"{name} owner projection is nondeterministic",
        )
        decoded = model.k1.decode_datum(owner_body)
        _require(
            model.k1.encode_datum(decoded) == owner_body,
            f"{name} PublicCoin body does not round-trip",
        )
        sequences, elements = _check_target_orders(
            model.codec, model.VIEW_SCHEMAS["PublicCoinView"], owner_value
        )
        sorted_sequences += sequences
        sorted_elements += elements
        class_counts = tuple(
            list(owner_evidence.classes.values()).count(index) for index in range(4)
        )
        logical_intersections = sum(
            len(value) for value in owner_evidence.logical_intersections.values()
        )
        observed = (
            len(owner_evidence.nodes),
            len(owner_evidence.edges),
            class_counts,
            len(owner_evidence.sinks),
            len(owner_evidence.acceptance_sinks),
            len(owner_evidence.private_predecessors),
            logical_intersections,
            owner_evidence.eligible,
        )
        _require(observed == EXPECTED_SCENARIOS[name], f"{name} metrics drifted")
        expected_fs = {
            "integrated-baseline": (
                "Affirmative",
                "F0V2B2D1-A-FS-STRUCTURAL",
            ),
            "logical-reject-preemption": (
                "Refused",
                "F0V2B2D1-R-LOGICAL-INTERSECTION",
            ),
        }.get(name, ("Refused", "F0V2B2D1-R-PUBLIC-COIN"))
        _expect(model.admit_fiat_shamir(core_result.handle), *expected_fs, name)
        owner_values[name] = owner_value
        owner_bodies[name] = owner_body
        owner_handles[name] = core_result.handle
        graph_metrics[name] = {
            "nodes": observed[0],
            "edges": observed[1],
            "classes": observed[2],
            "sinks": observed[3],
            "acceptance_sinks": observed[4],
            "private_predecessors": observed[5],
            "logical_intersections": observed[6],
            "eligible": observed[7],
        }
    findings.extend(
        (
            _finding("five-core-admissions", "Affirmative", "F0V2B2D1-A-FIVE-CORES"),
            _finding("five-fresh-pairings", "Affirmative", "F0V2B2D1-A-FIVE-FRESH"),
            _finding(
                "dual-projection-byte-agreement",
                "Affirmative",
                "F0V2B2D1-A-VIEW-AGREEMENT",
            ),
            _finding(
                "complete-evidence-table-agreement",
                "Affirmative",
                "F0V2B2D1-A-EVIDENCE-AGREEMENT",
            ),
            _finding(
                "canonical-roundtrip-and-order",
                "Affirmative",
                "F0V2B2D1-A-CANONICAL-BODIES",
            ),
            _finding(
                "deterministic-reprojection", "Affirmative", "F0V2B2D1-A-DETERMINISM"
            ),
        )
    )

    baseline_handle = owner_handles["integrated-baseline"]
    baseline_evidence = model.project_public_coin(baseline_handle)[1]
    _require(
        {item[0] for item in baseline_evidence.nodes} == set(range(14))
        and set(baseline_evidence.classes.values()) == set(range(4)),
        "full PCNode or PCClass inhabitance drifted",
    )
    preemption = {
        ((11, 0), (6, 21)),
        ((11, 0), (6, 22)),
        ((11, 1), (6, 22)),
    }
    _require(
        preemption <= set(baseline_evidence.edges), "terminal-preemption edge is absent"
    )
    _require(
        baseline_evidence.private_predecessors == ()
        and all(not value for value in baseline_evidence.logical_intersections.values())
        and all(baseline_evidence.challenge_validity.values())
        and all(baseline_evidence.challenge_observation_order.values()),
        "baseline eligibility witness drifted",
    )
    findings.extend(
        (
            _finding(
                "all-pcnode-and-class-cases",
                "Affirmative",
                "F0V2B2D1-A-BRANCH-INHABITANCE",
            ),
            _finding(
                "terminal-preemption-edges",
                "Affirmative",
                "F0V2B2D1-A-TERMINAL-PREEMPTION",
            ),
            _finding(
                "baseline-public-coin-eligible", "Affirmative", "F0V2B2D1-A-PUBLIC-COIN"
            ),
            _finding(
                "baseline-structural-fs", "Affirmative", "F0V2B2D1-A-FS-STRUCTURAL"
            ),
        )
    )

    negative_codes = {
        "private-verifier-output-sink": "F0V2B2D1-R-PRIVATE-SINK",
        "invalid-module-control-sink": "F0V2B2D1-R-INVALID-SINK",
        "history-challenge-condition": "F0V2B2D1-R-CHALLENGE-TRANSFER",
        "logical-reject-preemption": "F0V2B2D1-R-LOGICAL-PREEMPTION",
    }
    for name, code in negative_codes.items():
        _require(not graph_metrics[name]["eligible"], f"{name} became eligible")
        findings.append(_finding(name, "Refused", code))

    substitutions = _owner_substitutions(model, owner_values["integrated-baseline"])
    for name, body in substitutions:
        _require(body != owner_bodies["integrated-baseline"], f"{name} did not mutate")
        result = model.admit_public_coin_claim(baseline_handle, body)
        _expect(
            result,
            "Refused",
            "F0V2B2D1-R-PUBLIC-COIN-SUBSTITUTION",
            name,
        )
    _expect(
        model.admit_public_coin_claim(
            baseline_handle, owner_bodies["integrated-baseline"]
        ),
        "Affirmative",
        "F0V2B2D1-A-PUBLIC-COIN-CLAIM",
        "exact PublicCoin claim",
    )
    findings.extend(
        (
            _finding("exact-owner-view-claim", "Affirmative", "F0V2B2D1-A-EXACT-CLAIM"),
            _finding(
                "five-schema-valid-substitutions",
                "Refused",
                "F0V2B2D1-R-FIVE-SUBSTITUTIONS",
            ),
        )
    )

    fixture = model.fixture("integrated-baseline")
    terminals = list(fixture.core.terminals)
    terminals[0] = replace(terminals[0], public_outputs=(model.base.PublicInputRef(0),))
    outside = replace(fixture.core, terminals=tuple(terminals))
    outside_result = model.admit_core(
        model.rebuild(outside, fixture.environment), fixture.environment
    )
    _expect(
        outside_result,
        "Refused",
        "F0V2B2D1-R-BOUNDED-CARRIER",
        "unknown semantic Core",
    )
    findings.append(
        _finding("unknown-semantic-core", "Refused", "F0V2B2D1-R-BOUNDED-CARRIER")
    )

    alternate = model.fixture("history-challenge-condition")
    forged = replace(fixture.candidate, asserted_id=alternate.candidate.asserted_id)
    _expect(
        model.admit_core(forged, fixture.environment),
        "Malformed",
        "F0V2B2D1-M-CORE-ID",
        "Core ID/body substitution",
    )
    cross_protocol = model.admit_fresh_protocol(
        baseline_handle, alternate.protocol_candidate, fixture.environment
    )
    _expect(
        cross_protocol,
        "Refused",
        "F0V2B2D1-R-PROTOCOL-CORE",
        "cross-Core Fresh Protocol",
    )
    findings.extend(
        (
            _finding("core-id-body-substitution", "Malformed", "F0V2B2D1-M-CORE-ID"),
            _finding(
                "cross-core-fresh-substitution", "Refused", "F0V2B2D1-R-PROTOCOL-CORE"
            ),
        )
    )

    preimages = _algorithm_preimages(model, fixture)
    modules = model.raw_module_sources(fixture.environment)
    contract = model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference()
    cold_args = (
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
    )
    _require(
        _rejects(
            lambda: independent.project(
                fixture.candidate.profiled_body[:-1],
                *cold_args[1:],
                modules,
                preimages,
                contract,
            ),
            independent.ColdIntegratedError,
        ),
        "cold path accepted truncated Core bytes",
    )
    _require(
        _rejects(
            lambda: independent.project(*cold_args, modules, preimages[:-1], contract),
            independent.ColdIntegratedError,
        ),
        "cold path accepted missing algorithm preimage",
    )
    swapped_modules = list(modules)
    swapped_modules[0] = (swapped_modules[0][0], swapped_modules[1][1])
    _require(
        _rejects(
            lambda: independent.project(
                *cold_args, tuple(swapped_modules), preimages, contract
            ),
            independent.ColdIntegratedError,
        ),
        "cold path accepted substituted module body",
    )
    _require(
        _rejects(
            lambda: independent.project(*cold_args, modules, preimages, contract[:-1]),
            independent.ColdIntegratedError,
        ),
        "cold path accepted another evaluation contract",
    )
    findings.extend(
        (
            _finding("cold-core-truncation", "Malformed", "F0V2B2D1-M-COLD-CORE"),
            _finding("cold-algorithm-closure", "Refused", "F0V2B2D1-R-COLD-ALGORITHM"),
            _finding("cold-module-preimage", "Refused", "F0V2B2D1-R-COLD-MODULE"),
            _finding("cold-contract-closure", "Refused", "F0V2B2D1-R-COLD-CONTRACT"),
        )
    )

    _require(
        _rejects(lambda: copy.copy(baseline_handle), TypeError)
        and _rejects(lambda: copy.deepcopy(baseline_handle), TypeError)
        and _rejects(lambda: pickle.dumps(baseline_handle), TypeError)
        and _rejects(
            lambda: model.project_public_coin(object()), model.IntegratedFailure
        ),
        "process-local owner authority became forgeable",
    )
    findings.append(
        _finding("process-local-authority", "Refused", "F0V2B2D1-R-AUTHORITY")
    )

    findings.extend(
        (
            _finding(
                "pcgraph-family-closure", "Affirmative", "F0V2B2D1-A-B2D-ONE-OF-TWO"
            ),
            _finding(
                "logical-publication-transfer-wording",
                "Affirmative",
                "F0V2B2D1-A-LOGICAL-TRANSFER-WORDING",
            ),
            _finding(
                "public-query-sink-coordinate-wording",
                "Affirmative",
                "F0V2B2D1-A-QUERY-SINK-WORDING",
            ),
            _finding(
                "target-profile-publication",
                "CannotAnswer",
                "F0V2B2D1-C-TARGET-PUBLICATION",
            ),
            _finding(
                "live-implementation-correspondence",
                "CannotAnswer",
                "F0V2B2D1-C-LIVE-CORRESPONDENCE",
            ),
            _finding(
                "projection-refinement-proof",
                "CannotAnswer",
                "F0V2B2D1-C-REFINEMENT-PROOF",
            ),
            _finding(
                "cryptographic-or-fs-theorem",
                "CannotAnswer",
                "F0V2B2D1-C-CRYPTOGRAPHIC-THEOREM",
            ),
            _finding("f1-q1-correspondence", "CannotAnswer", "F0V2B2D1-C-F1-Q1"),
            _finding("integrated-pcgraph-closure", "Affirmative", AGGREGATE),
        )
    )

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    metrics = {
        "findings": len(findings),
        "findings_sha256": checksum,
        "scenarios": len(owner_bodies),
        "exact_view_bodies": len(owner_bodies),
        "exact_view_body_bytes": sum(len(body) for body in owner_bodies.values()),
        "schema_definitions": model.VIEW_SCHEMA_STATS["definition_count"],
        "schema_source_nodes": model.VIEW_SCHEMA_STATS["source_node_count"],
        "sorted_unique_sequences": sorted_sequences,
        "sorted_unique_elements": sorted_elements,
        "schema_valid_owner_substitutions": len(substitutions),
        "pc_graphs": graph_metrics,
        "b2d_families_closed": 1,
        "b2d_families_total": len(b2d),
    }
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot load frozen findings") from error
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    findings, metrics = evaluate()
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.check and observed != _load_expected():
        print(
            json.dumps(
                {"expected": _load_expected(), "observed": observed},
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    output: dict[str, Any] = {
        "aggregate": AGGREGATE,
        "outcomes": dict(sorted(counts.items())),
        "metrics": metrics,
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
