#!/usr/bin/env python3
"""Run the exact Terminal-owner projection gate on the migrated text."""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass, replace
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
PREDECESSOR_EXPECTED = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-contracts-f0v2b2c1b5b1"
    / "expected-findings.json"
)
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
TARGET_SOURCE = ROOT / "docs-next/pir/interactive-core.md"
COLD_PUBLICATION = ROOT / "evaluation/semantic-profile-publication/independent.py"
AGGREGATE = "F0V2B2C1B5B2-A-EXACT-TERMINAL-OWNER-PROJECTIONS"
PROFILE_DIGEST = "0af785eb8159ca2182843c62f72898e3c17266c5a7d9b317cfe2ae463d840474"
PROFILE_BODY_SHA256 = "c2dee0bc0bef91610a16acf8587444c57663ec83a87a948a51f320b194381d4a"
GRAMMAR_SHA256 = "f88b5a5e48046cf4e9079410dbb6ea572316aa51de175d2ed009f18ec6e48292"
SCHEMA_SOURCE_SHA256 = (
    "c87b09d89ddbe92f8a6cdad8eae6bb0dbcfea6ed69e65e335e551efba0f6e03d"
)
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


def _body_table(model: ModuleType, views: dict[str, Any]) -> dict[str, bytes]:
    return {
        name: model.codec.encode_value(model.VIEW_SCHEMAS[name], value)
        for name, value in views.items()
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


def _algorithms_for(
    model: ModuleType, fixture: object, core: object
) -> tuple[object, ...]:
    references, _contracts = model._ordinary_references(core)
    return tuple(item for item in fixture.algorithms if item.identity in references)


def _candidate_for(
    model: ModuleType, fixture: object, core: object
) -> tuple[object, object, tuple[object, ...]]:
    algorithms = _algorithms_for(model, fixture, core)
    environment, candidate = model.candidate_for(core, fixture.module, algorithms)
    return environment, candidate, algorithms


def _cold_project(
    model: ModuleType,
    independent: ModuleType,
    environment: object,
    candidate: object,
    algorithms: tuple[object, ...],
) -> tuple[dict[str, Any], dict[str, Any]]:
    protocol = model.b2c0.make_protocol_candidate(
        candidate.asserted_id, environment.profile_id
    )
    preimages = {
        item.identity.internal_reference(): model.k1.algorithm_preimage(item)
        for item in algorithms
    }
    return independent.project(
        candidate.profiled_body,
        candidate.asserted_id.internal_reference(),
        protocol.profiled_body,
        protocol.asserted_id.internal_reference(),
        preimages,
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )


def _replace_terminal(core: object, index: int, **changes: object) -> object:
    terminals = list(core.terminals)
    terminals[index] = replace(terminals[index], **changes)
    return replace(core, terminals=tuple(terminals))


def _replace_occurrence(core: object, index: int, **changes: object) -> object:
    occurrences = list(core.occurrences)
    occurrences[index] = replace(occurrences[index], **changes)
    return replace(core, occurrences=tuple(occurrences))


def _replace_check(core: object, index: int, **changes: object) -> object:
    checks = list(core.checks)
    checks[index] = replace(checks[index], **changes)
    return replace(core, checks=tuple(checks))


def _replace_claim(core: object, index: int, **changes: object) -> object:
    claims = list(core.claims)
    claims[index] = replace(claims[index], **changes)
    return replace(core, claims=tuple(claims))


def _mutation(model: ModuleType, fixture: object, name: str) -> object:
    core = fixture.core
    identity = fixture.algorithms[0].identity
    contract = model.k1.DEFAULT_EVALUATION_CONTRACT.identity
    weak_guard = model.base.EvaluateGuard(
        identity, contract, (model.base.PublicInputRef(1),)
    )
    if name == "required-check-reference":
        return _replace_terminal(core, 0, required_true_checks=(9,))
    if name == "required-check-duplicate":
        return _replace_terminal(core, 0, required_true_checks=(0, 0))
    if name == "required-reduction-reference":
        return _replace_terminal(core, 0, required_applied_reductions=(9,))
    if name == "required-reduction-duplicate":
        return _replace_terminal(core, 0, required_applied_reductions=(0, 0))
    if name == "required-reduction-unsorted":
        return _replace_terminal(core, 0, required_applied_reductions=(1, 0))
    if name == "terminal-claim-omitted":
        return _replace_terminal(core, 0, terminal_claims=())
    if name == "terminal-claim-wrong":
        return _replace_terminal(core, 0, terminal_claims=(2,))
    if name == "terminal-claim-duplicate":
        return _replace_terminal(core, 0, terminal_claims=(1, 1))
    if name == "final-fallback-guarded":
        return _replace_occurrence(core, 5, guard=weak_guard)
    if name == "accept-guard-omits-check":
        occurrences = list(core.occurrences)
        occurrences[1] = replace(occurrences[1], guard=weak_guard)
        occurrences[2] = replace(occurrences[2], guard=weak_guard)
        return replace(core, occurrences=tuple(occurrences))
    if name == "check-not-guaranteed":
        return _replace_occurrence(core, 0, guard=weak_guard)
    if name == "required-reduction-after-terminal":
        occurrences = list(core.occurrences)
        occurrences[1], occurrences[2] = occurrences[2], occurrences[1]
        return replace(core, occurrences=tuple(occurrences))
    if name == "linear-consumer-overlap":
        occurrences = list(core.occurrences)
        moved = occurrences.pop(3)
        occurrences.insert(2, moved)
        return replace(core, occurrences=tuple(occurrences))
    if name == "check-abi":
        return _replace_check(
            core,
            0,
            inputs=(model.base.PublicInputRef(0), model.base.PublicInputRef(1)),
        )
    if name == "claim-output-ssa":
        return _replace_claim(core, 1, source=model.b3.ReductionOutputClaimSource(1, 0))
    if name == "missing-terminal-backlink":
        return replace(core, occurrences=core.occurrences[:-1])
    if name == "duplicate-terminal-backlink":
        return replace(
            core,
            occurrences=(
                *core.occurrences,
                model.base.OccurrenceDecl(
                    0, model.base.AlwaysGuard(), model.base.TerminalEffect(2)
                ),
            ),
        )
    raise KeyError(name)


MUTATIONS: tuple[tuple[str, str, str], ...] = (
    (
        "required-check-reference",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    ("required-check-duplicate", "Refused", "F0V2B2C1B5B2-R-CANONICAL-SET"),
    (
        "required-reduction-reference",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "required-reduction-duplicate",
        "Refused",
        "F0V2B2C1B5B2-R-CANONICAL-SET",
    ),
    (
        "required-reduction-unsorted",
        "Refused",
        "F0V2B2C1B5B2-R-CANONICAL-SET",
    ),
    (
        "terminal-claim-omitted",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "terminal-claim-wrong",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    ("terminal-claim-duplicate", "Refused", "F0V2B2C1B5B2-R-CANONICAL-SET"),
    (
        "final-fallback-guarded",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "accept-guard-omits-check",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "check-not-guaranteed",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "required-reduction-after-terminal",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    (
        "linear-consumer-overlap",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
    ),
    ("check-abi", "KindMismatch", "F0V2B2C1B5B2-K-CHECK-ABI"),
    ("claim-output-ssa", "Refused", "F0V2B2C1B5B2-R-CLAIM-SSA"),
    (
        "missing-terminal-backlink",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-BACKLINK",
    ),
    (
        "duplicate-terminal-backlink",
        "Refused",
        "F0V2B2C1B5B2-R-TERMINAL-BACKLINK",
    ),
)


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b5b2_model", MODEL)
    independent = _load("_zkc_f0v2b2c1b5b2_independent", INDEPENDENT)
    cold_publication = _load("_zkc_f0v2b2c1b5b2_cold_publication", COLD_PUBLICATION)
    findings: list[Finding] = []

    predecessor = json.loads(PREDECESSOR_EXPECTED.read_text(encoding="utf-8"))
    _require(
        predecessor["aggregate"] == "F0V2B2C1B5B1-A-TERMINAL-CONTRACT-SELECTION"
        and predecessor["findings_sha256"]
        == "1f89c704a2af3e01b86711858d3d11ae7a20bb394520eb6c7b21b6513a058ba5",
        "B5B1 predecessor result drifted",
    )
    findings.append(
        _finding("predecessor-pin", "Affirmative", "F0V2B2C1B5B2-A-PREDECESSOR-PIN")
    )

    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    b2c = tuple(
        item["id"]
        for item in inventory["required_pressure_families"]
        if item["stage"] == "B2C"
    )
    _require(
        len(b2c) == 21 and b2c[-1] == "terminal-abort-consume-discharge",
        "B2C terminal family partition drifted",
    )
    findings.append(_finding("family-pin", "Affirmative", "F0V2B2C1B5B2-A-FAMILY-PIN"))

    target = TARGET_SOURCE.read_text(encoding="utf-8")
    terminal_start = target.index("TerminalDecl = {")
    terminal_end = target.index("At an active terminal", terminal_start)
    terminal_source = target[terminal_start:terminal_end]
    _require(
        "ClaimDisposition = Consume | Discharge" in target
        and "required_true_checks" in terminal_source
        and "required_applied_reductions" in terminal_source
        and "terminal_claims" in terminal_source
        and "TerminalContract(t)" in target
        and "DerivedClaimDisposition(Accept) = Consume" in target
        and "F0V2B2C1B5B2" not in target,
        "migrated Terminal owner contract drifted",
    )
    findings.extend(
        (
            _finding(
                "target-contract-pin",
                "Affirmative",
                "F0V2B2C1B5B2-A-TARGET-CONTRACT-PIN",
            ),
            _finding(
                "authored-owner-profile",
                "Affirmative",
                "F0V2B2C1B5B2-A-AUTHORED-OWNER",
            ),
        )
    )

    model_source = MODEL.read_text(encoding="utf-8")
    independent_source = INDEPENDENT.read_text(encoding="utf-8")
    _require(
        "import itertools" not in model_source
        and "terminal_contracts.analyze" in model_source
        and "import itertools" in independent_source
        and "terminal_contracts" not in independent_source
        and "import model" not in independent_source
        and "from model" not in independent_source,
        "abstract and exhaustive paths are not source-separated",
    )
    _require(
        model is not independent
        and model.k1 is not independent.k1
        and model.b2b is not independent.b2b,
        "cold path reused typed-owner module instances",
    )
    findings.extend(
        (
            _finding(
                "analysis-oracle-source-separation",
                "Affirmative",
                "F0V2B2C1B5B2-A-ORACLE-SEPARATION",
            ),
            _finding(
                "cold-module-separation",
                "Affirmative",
                "F0V2B2C1B5B2-A-COLD-MODULES",
            ),
        )
    )

    candidate_publication, grammar_digest = model.candidate_publication()
    cold_candidate = cold_publication.compile_repository()
    for key in model.publication.PROFILE_KEYS:
        reference = candidate_publication.profiles[key]
        observed = cold_candidate.profiles[key]
        _require(
            reference.body_bytes == observed.body_bytes
            and reference.profile_id.internal_reference() == observed.identifier.ref(),
            f"publication compilers disagree for {key}",
        )
    profile = model.profile_evidence()
    _require(
        profile["candidate_interaction_digest"] == PROFILE_DIGEST
        and profile["candidate_interaction_body_sha256"] == PROFILE_BODY_SHA256,
        "migrated Interaction identity drifted",
    )
    _require(
        profile["profiles_compiled"] == sorted(model.publication.PROFILE_KEYS)
        and candidate_publication.profiles["interaction"].manifest["revision"] == 3,
        "migrated profile catalog or Interaction revision drifted",
    )
    findings.extend(
        (
            _finding(
                "dual-publication-compiler-agreement",
                "Affirmative",
                "F0V2B2C1B5B2-A-PUBLICATION-AGREEMENT",
            ),
            _finding(
                "interaction-revision-and-identity",
                "Affirmative",
                "F0V2B2C1B5B2-A-INTERACTION-R3",
            ),
            _finding(
                "complete-profile-catalog",
                "Affirmative",
                "F0V2B2C1B5B2-A-PROFILE-CATALOG",
            ),
        )
    )

    cold_schema = independent.configure(PROFILE_DIGEST, PROFILE_BODY_SHA256)
    _require(
        grammar_digest == GRAMMAR_SHA256
        and profile["schema_grammar_sha256"] == GRAMMAR_SHA256
        and profile["schema_source_sha256"] == SCHEMA_SOURCE_SHA256
        and cold_schema["schema_grammar_sha256"] == GRAMMAR_SHA256
        and cold_schema["schema_source_sha256"] == SCHEMA_SOURCE_SHA256,
        "candidate grammar binding drifted",
    )
    _require(
        model.VIEW_SCHEMAS == independent.VIEW_SCHEMAS
        and model.VIEW_OWNERS == independent.VIEW_OWNERS
        and model.VIEW_SCHEMA_STATS["definition_count"] == 88
        and model.VIEW_SCHEMA_STATS["source_node_count"] == 459
        and model.VIEW_SCHEMA_STATS["maximum_source_depth"] == 17,
        "schema compilation paths disagree",
    )
    findings.extend(
        (
            _finding(
                "owner-free-grammar-digest-binding",
                "Affirmative",
                "F0V2B2C1B5B2-A-GRAMMAR-BINDING",
            ),
            _finding(
                "dual-schema-compiler-agreement",
                "Affirmative",
                "F0V2B2C1B5B2-A-SCHEMA-AGREEMENT",
            ),
        )
    )

    fixture = model.fixture()
    core_result = model.admit_core(fixture.candidate, fixture.environment)
    _expect(
        core_result,
        "Affirmative",
        "F0V2B2C1B5B2-A-CORE-ADMITTED",
        "reference Core",
    )
    _require(core_result.handle is not None, "Core admission omitted authority")
    protocol_result = model.admit_fresh_protocol(
        core_result.handle, fixture.protocol_candidate, fixture.environment
    )
    _expect(
        protocol_result,
        "Affirmative",
        "F0V2B2C1B5B2-A-FRESH-ADMITTED",
        "reference Fresh Protocol",
    )
    _require(protocol_result.handle is not None, "Protocol admission omitted authority")
    findings.extend(
        (
            _finding(
                "candidate-core-admission",
                "Affirmative",
                "F0V2B2C1B5B2-A-CORE-ADMISSION",
            ),
            _finding(
                "fresh-protocol-pairing",
                "Affirmative",
                "F0V2B2C1B5B2-A-PROTOCOL-PAIRING",
            ),
        )
    )

    owner_views = model.project_views(core_result.handle, protocol_result.handle)
    owner_bodies = _body_table(model, owner_views)
    cold_views, cold_evidence = _cold_project(
        model,
        independent,
        fixture.environment,
        fixture.candidate,
        fixture.algorithms,
    )
    cold_bodies = independent.encode_views(cold_views)
    _require(owner_bodies == cold_bodies, "reference and cold projectors disagree")
    repeated_views = model.project_views(core_result.handle, protocol_result.handle)
    _require(
        owner_bodies == _body_table(model, repeated_views),
        "owner projection is not deterministic",
    )
    sorted_sequences = 0
    sorted_elements = 0
    for name, body in owner_bodies.items():
        decoded = model.k1.decode_datum(body)
        _require(
            model.k1.encode_datum(decoded) == body,
            f"{name} body does not round-trip",
        )
        sequences, elements = _check_target_orders(
            model.codec, model.VIEW_SCHEMAS[name], owner_views[name]
        )
        sorted_sequences += sequences
        sorted_elements += elements
    findings.extend(
        (
            _finding(
                "six-view-byte-agreement",
                "Affirmative",
                "F0V2B2C1B5B2-A-SIX-VIEW-AGREEMENT",
            ),
            _finding(
                "exact-body-roundtrip",
                "Affirmative",
                "F0V2B2C1B5B2-A-BODY-ROUNDTRIP",
            ),
            _finding(
                "deterministic-reprojection",
                "Affirmative",
                "F0V2B2C1B5B2-A-DETERMINISM",
            ),
            _finding(
                "target-sorted-unique-order",
                "Affirmative",
                "F0V2B2C1B5B2-A-CANONICAL-ORDER",
            ),
        )
    )

    summary = dict(core_result.handle.structural_summary)
    validation = summary["validation"]
    analysis = validation.terminal_analysis
    execution = cold_evidence["terminal_execution"]
    _require(
        execution["assignments"] == 8
        and execution["verdict_counts"] == {"Accept": 2, "Reject": 3, "Abort": 3},
        "cold first-active branch partition drifted",
    )
    _require(
        analysis.check_entailments == ((0, 0, 0),)
        and analysis.reduction_requirements == ((0, 0), (1, 1), (2, 1))
        and analysis.terminal_live_claims == ((1,), (2,), (2,))
        and analysis.terminal_dispositions
        == (
            ((1, "Consume"),),
            ((2, "Discharge"),),
            ((2, "Discharge"),),
        ),
        "abstract Terminal contract facts drifted",
    )
    findings.extend(
        (
            _finding(
                "finite-first-active-partition",
                "Affirmative",
                "F0V2B2C1B5B2-A-FIRST-ACTIVE-PARTITION",
            ),
            _finding(
                "required-check-entailment",
                "Affirmative",
                "F0V2B2C1B5B2-A-CHECK-ENTAILMENT",
            ),
            _finding(
                "required-reduction-closure",
                "Affirmative",
                "F0V2B2C1B5B2-A-REDUCTION-CLOSURE",
            ),
            _finding(
                "exact-live-claim-closure",
                "Affirmative",
                "F0V2B2C1B5B2-A-CLAIM-CLOSURE",
            ),
            _finding(
                "verdict-derived-dispositions",
                "Affirmative",
                "F0V2B2C1B5B2-A-DERIVED-DISPOSITIONS",
            ),
            _finding(
                "abstract-exhaustive-agreement",
                "Affirmative",
                "F0V2B2C1B5B2-A-ANALYSIS-ORACLE-AGREEMENT",
            ),
        )
    )

    effect = owner_views["EffectView"]
    claim_reduction = owner_views["ClaimReductionView"]
    _require(
        len(effect[5]) == 1
        and len(effect[6]) == 3
        and [len(row[3]) for row in effect[6]] == [1, 0, 0]
        and [len(row[4]) for row in effect[6]] == [1, 1, 1]
        and [len(row[5]) for row in effect[6]] == [1, 1, 1],
        "EffectView Check or expanded Terminal rows drifted",
    )
    _require(
        [row[3]["case"] for row in claim_reduction[3]] == [0, 1, 1]
        and [len(row[2]) for row in claim_reduction[4]] == [1, 1, 1],
        "ClaimReductionView derived Terminal rows drifted",
    )
    findings.extend(
        (
            _finding(
                "effect-check-and-terminal-rows",
                "Affirmative",
                "F0V2B2C1B5B2-A-EFFECT-ROWS",
            ),
            _finding(
                "claim-disposition-and-requirement-rows",
                "Affirmative",
                "F0V2B2C1B5B2-A-CLAIM-REDUCTION-ROWS",
            ),
        )
    )

    graph_evidence = cold_evidence["pc_graph"]
    _require(
        graph_evidence
        == {
            "nodes": 28,
            "edges": 49,
            "eligible": True,
            "check_sinks": 1,
            "reduction_sinks": 2,
            "terminal_sinks": 3,
        },
        "expanded-Terminal PCGraph metrics drifted",
    )
    encoded_edges = {
        model.codec.encode_value(model._PC_EDGE_SCHEMA, row)
        for row in owner_views["PublicCoinView"][1][1]
    }
    required_edges = {
        ((8, 0, 0), (7, 2)),
        ((10, 0), (7, 2)),
        ((9, 1), (7, 2)),
        ((0, 1), (7, 2)),
        ((10, 1), (7, 4)),
        ((9, 2), (7, 4)),
        ((0, 2), (7, 4)),
        ((10, 1), (7, 5)),
        ((9, 2), (7, 5)),
        ((0, 0), (7, 5)),
    }
    expected_edges = {
        model.codec.encode_value(model._PC_EDGE_SCHEMA, model._edge_value(edge))
        for edge in required_edges
    }
    _require(expected_edges <= encoded_edges, "Terminal dependency edge is absent")
    hidden_edges = {
        model.codec.encode_value(
            model._PC_EDGE_SCHEMA,
            model._edge_value(((8, 0, 0), (7, occurrence))),
        )
        for occurrence in (4, 5)
    }
    _require(
        encoded_edges.isdisjoint(hidden_edges),
        "failure fallback acquired an implicit Check gate",
    )
    findings.extend(
        (
            _finding(
                "expanded-terminal-pcgraph",
                "Affirmative",
                "F0V2B2C1B5B2-A-PCGRAPH",
            ),
            _finding(
                "explicit-terminal-dependency-edges",
                "Affirmative",
                "F0V2B2C1B5B2-A-TERMINAL-EDGES",
            ),
            _finding(
                "no-implicit-fallback-check-edge",
                "Affirmative",
                "F0V2B2C1B5B2-A-NO-HIDDEN-GATING",
            ),
        )
    )

    substitutions: list[tuple[str, str, dict[str, Any]]] = []
    changed = copy.deepcopy(owner_views)
    changed["EffectView"][6][0][3] = []
    substitutions.append(("terminal-check", "EffectView", changed))
    changed = copy.deepcopy(owner_views)
    changed["EffectView"][6][0][4] = []
    substitutions.append(("terminal-reduction", "EffectView", changed))
    changed = copy.deepcopy(owner_views)
    changed["EffectView"][6][0][5] = []
    substitutions.append(("terminal-claim", "EffectView", changed))
    changed = copy.deepcopy(owner_views)
    changed["ClaimReductionView"][3][0][3] = model.foundation._v(1)
    substitutions.append(("claim-disposition", "ClaimReductionView", changed))
    changed = copy.deepcopy(owner_views)
    changed["ClaimReductionView"][4][0][2] = []
    substitutions.append(
        ("terminal-reduction-requirement", "ClaimReductionView", changed)
    )
    changed = copy.deepcopy(owner_views)
    check_edge = model.codec.encode_value(
        model._PC_EDGE_SCHEMA,
        model._edge_value(((8, 0, 0), (7, 2))),
    )
    rows = changed["PublicCoinView"][1][1]
    changed["PublicCoinView"][1][1] = [
        row
        for row in rows
        if model.codec.encode_value(model._PC_EDGE_SCHEMA, row) != check_edge
    ]
    substitutions.append(("terminal-graph-edge", "PublicCoinView", changed))
    for label, view_name, changed_views in substitutions:
        body = model.codec.encode_value(
            model.VIEW_SCHEMAS[view_name], changed_views[view_name]
        )
        _require(
            body != owner_bodies[view_name],
            f"schema-valid owner substitution did not change {label} bytes",
        )
    findings.append(
        _finding(
            "schema-valid-owner-substitutions",
            "Refused",
            "F0V2B2C1B5B2-R-OWNER-SUBSTITUTION",
        )
    )

    old_terminal = {
        0: effect[6][0][0],
        1: effect[6][0][1],
        2: effect[6][0][2],
        3: effect[6][0][3],
        4: [{0: effect[6][0][5][0], 1: model.foundation._v(0)}],
        5: effect[6][0][6],
    }
    _require(
        _rejects(
            lambda: model.codec.encode_value(
                model.codec.record_field(model.VIEW_SCHEMAS["EffectView"], 6)[
                    "element"
                ],
                old_terminal,
            ),
            Exception,
        ),
        "old authored-disposition Terminal row remained schema-valid",
    )
    findings.append(
        _finding(
            "authored-disposition-row-reintroduced",
            "Malformed",
            "F0V2B2C1B5B2-M-OLD-TERMINAL-ROW",
        )
    )

    mutation_agreement = 0
    for name, outcome, code in MUTATIONS:
        mutated_core = _mutation(model, fixture, name)
        environment, candidate, algorithms = _candidate_for(
            model, fixture, mutated_core
        )
        result = model.admit_core(candidate, environment)
        _expect(result, outcome, code, name)
        _require(
            _rejects(
                lambda e=environment, c=candidate, a=algorithms: _cold_project(
                    model, independent, e, c, a
                ),
                Exception,
            ),
            f"cold path accepted mutation {name}",
        )
        findings.append(_finding(name, outcome, code))
        mutation_agreement += 1
    findings.append(
        _finding(
            "semantic-mutation-path-agreement",
            "Affirmative",
            "F0V2B2C1B5B2-A-MUTATION-AGREEMENT",
        )
    )

    alternate_core = _replace_terminal(
        fixture.core, 0, public_outputs=(model.base.PublicInputRef(0),)
    )
    alternate_environment, alternate_candidate, _alternate_algorithms = _candidate_for(
        model, fixture, alternate_core
    )
    forged_candidate = replace(
        fixture.candidate, asserted_id=alternate_candidate.asserted_id
    )
    forged_result = model.admit_core(forged_candidate, fixture.environment)
    _expect(
        forged_result,
        "Malformed",
        "F0V2B2C1B5B2-M-CORE-ID",
        "Core body/reference substitution",
    )
    findings.append(
        _finding(
            "core-body-reference-substitution",
            "Malformed",
            "F0V2B2C1B5B2-M-CORE-ID",
        )
    )

    alternate_protocol = model.b2c0.make_protocol_candidate(
        alternate_candidate.asserted_id, alternate_environment.profile_id
    )
    cross_protocol = model.admit_fresh_protocol(
        core_result.handle, alternate_protocol, fixture.environment
    )
    _expect(
        cross_protocol,
        "Refused",
        "F0V2B2C1B5B2-R-PROTOCOL-CORE",
        "cross-Core Protocol",
    )
    findings.append(
        _finding(
            "cross-core-protocol-substitution",
            "Refused",
            "F0V2B2C1B5B2-R-PROTOCOL-CORE",
        )
    )

    preimages = {
        item.identity.internal_reference(): model.k1.algorithm_preimage(item)
        for item in fixture.algorithms
    }
    contract_reference = (
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference()
    )
    _require(
        _rejects(
            lambda: independent.project(
                fixture.candidate.profiled_body[:-1],
                fixture.candidate.asserted_id.internal_reference(),
                fixture.protocol_candidate.profiled_body,
                fixture.protocol_candidate.asserted_id.internal_reference(),
                preimages,
                contract_reference,
            ),
            independent.ColdTerminalError,
        ),
        "cold path accepted truncated Core bytes",
    )
    findings.append(
        _finding(
            "cold-core-truncation",
            "Malformed",
            "F0V2B2C1B5B2-M-COLD-CORE",
        )
    )
    _require(
        _rejects(
            lambda: independent.project(
                fixture.candidate.profiled_body,
                fixture.candidate.asserted_id.internal_reference(),
                fixture.protocol_candidate.profiled_body,
                fixture.protocol_candidate.asserted_id.internal_reference(),
                {},
                contract_reference,
            ),
            independent.ColdTerminalError,
        ),
        "cold path accepted missing algorithm closure",
    )
    findings.append(
        _finding(
            "cold-algorithm-closure-missing",
            "Refused",
            "F0V2B2C1B5B2-R-COLD-ALGORITHM-CLOSURE",
        )
    )
    swapped_preimages = dict(preimages)
    references = tuple(swapped_preimages)
    swapped_preimages[references[0]] = swapped_preimages[references[1]]
    _require(
        _rejects(
            lambda: independent.project(
                fixture.candidate.profiled_body,
                fixture.candidate.asserted_id.internal_reference(),
                fixture.protocol_candidate.profiled_body,
                fixture.protocol_candidate.asserted_id.internal_reference(),
                swapped_preimages,
                contract_reference,
            ),
            independent.ColdTerminalError,
        ),
        "cold path accepted substituted algorithm preimage",
    )
    findings.append(
        _finding(
            "cold-algorithm-preimage-substitution",
            "Refused",
            "F0V2B2C1B5B2-R-COLD-ALGORITHM-ID",
        )
    )
    _require(
        _rejects(
            lambda: model.project_views(object(), protocol_result.handle),
            model.FamilyFailure,
        )
        and _rejects(
            lambda: model.project_views(core_result.handle, object()),
            model.FamilyFailure,
        ),
        "projection accepted foreign authority",
    )
    findings.append(
        _finding(
            "process-local-authority-separation",
            "Refused",
            "F0V2B2C1B5B2-R-AUTHORITY",
        )
    )

    findings.extend(
        (
            _finding(
                "bounded-b2c-family-closure",
                "Affirmative",
                "F0V2B2C1B5B2-A-B2C-21-OF-21",
            ),
            _finding(
                "target-profile-publication",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-TARGET-PUBLICATION",
            ),
            _finding(
                "live-implementation-correspondence",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-LIVE-CORRESPONDENCE",
            ),
            _finding(
                "projection-refinement-proof",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-REFINEMENT-PROOF",
            ),
            _finding(
                "terminal-analysis-formal-proof",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-ANALYSIS-PROOF",
            ),
            _finding(
                "cryptographic-or-fiat-shamir-theorem",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-CRYPTOGRAPHIC-THEOREM",
            ),
            _finding(
                "f1-q1-correspondence",
                "CannotAnswer",
                "F0V2B2C1B5B2-C-F1-Q1",
            ),
            _finding("exact-terminal-owner-projections", "Affirmative", AGGREGATE),
        )
    )

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    metrics = {
        "findings": len(findings),
        "findings_sha256": checksum,
        "profiles_compared": len(model.publication.PROFILE_KEYS),
        "schema_definitions": model.VIEW_SCHEMA_STATS["definition_count"],
        "schema_source_nodes": model.VIEW_SCHEMA_STATS["source_node_count"],
        "exact_view_bodies": len(owner_bodies),
        "exact_view_body_bytes": sum(len(item) for item in owner_bodies.values()),
        "sorted_unique_sequences": sorted_sequences,
        "sorted_unique_elements": sorted_elements,
        "runtime_assignments": execution["assignments"],
        "terminal_counts": execution["verdict_counts"],
        "pc_graph": graph_evidence,
        "schema_valid_owner_substitutions": len(substitutions),
        "semantic_mutations": mutation_agreement,
        "candidate_analysis_operations": analysis.operations,
        "b2c_families_closed": len(b2c),
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
    if args.check:
        expected = _load_expected()
        if observed != expected:
            print(
                json.dumps(
                    {"expected": expected, "observed": observed},
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
