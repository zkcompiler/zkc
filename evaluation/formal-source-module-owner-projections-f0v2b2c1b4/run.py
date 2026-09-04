#!/usr/bin/env python3
"""Executable gate for F0-V2B2C1B4 module owner projections."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
AGGREGATE = "F0V2B2C1B4-A-MODULE-OWNER-PROJECTIONS"
MODULE_FAMILIES = (
    "module-no-decision",
    "module-prover-decision",
    "module-prover-publication",
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
        f"{label}: expected {outcome}/{code}, got {result.outcome}/{result.code}: {result.detail}",
    )


def _rejects(operation: Callable[[], object], expected: type[BaseException]) -> bool:
    try:
        operation()
    except expected:
        return True
    return False


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


def _replace_occurrence_effect(
    model: ModuleType, core: object, index: int, effect: object
) -> object:
    occurrences = list(core.occurrences)
    occurrences[index] = replace(occurrences[index], effect=effect)
    return replace(core, occurrences=tuple(occurrences))


def _candidate(
    model: ModuleType, environment: object, core: object
) -> tuple[object, object]:
    return environment, model.rebuild(core, environment)


def _module_rebased_case(
    model: ModuleType,
    environment: object,
    core: object,
    semantics: tuple[object, ...],
) -> tuple[object, object]:
    module = model.extension_module(semantics)
    occurrences = []
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) is model.ModuleEffectRef:
            effect = replace(
                effect,
                module=module.identity,
                declaration=replace(effect.declaration, module=module.identity),
            )
            occurrence = replace(occurrence, effect=effect)
        occurrences.append(occurrence)
    changed_core = replace(
        core,
        used_modules=(module.identity,),
        occurrences=tuple(occurrences),
    )
    changed_environment = replace(
        environment,
        module_preimages=MappingProxyType({module.identity: module}),
    )
    return _candidate(model, changed_environment, changed_core)


def _declaration_mutation(
    model: ModuleType,
    environment: object,
    core: object,
    declaration: int,
    transform: Callable[[object], object],
) -> tuple[object, object]:
    semantics = list(model.supported_semantics())
    semantics[declaration] = transform(semantics[declaration])
    return _module_rebased_case(model, environment, core, tuple(semantics))


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b4_model", MODEL)
    cold_projector = _load("_zkc_f0v2b2c1b4_independent", INDEPENDENT)
    inventory = _inventory()
    b2c = tuple(
        item["id"]
        for item in inventory["required_pressure_families"]
        if item["stage"] == "B2C"
    )
    _require(
        b2c[17:20] == MODULE_FAMILIES and len(b2c) == 21,
        "module family partition drifted",
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
            "F0V2B2C1B4-A-PREDECESSOR-PINS",
            "the exact B2C1B3/B2B/B2C1A inputs and three-family module partition remain selected",
        ),
        _finding(
            "cold-path-module-separation",
            "Affirmative",
            "F0V2B2C1B4-A-COLD-PATH-SEPARATION",
            "the cold path uses separate Foundation, schema, parser, graph, projector, and codec instances",
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
            "F0V2B2C1B4-A-CORE-ADMITTED",
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
            "F0V2B2C1B4-A-FRESH-ADMITTED",
            f"{name} Protocol",
        )
        _require(
            protocol_result.handle is not None,
            f"{name} omitted Protocol authority",
        )
        owner_views = model.project_views(core_result.handle, protocol_result.handle)
        owner_bodies = _body_table(model, owner_views)
        module_sources = model.raw_module_sources(environment)
        cold_views, cold_evidence = cold_projector.project(
            core_result.handle.profiled_body,
            core_result.handle.core_reference,
            protocol_result.handle.profiled_body,
            protocol_result.handle.protocol_reference,
            module_sources,
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
            "module_sources": module_sources,
            "combined_sha256": hashlib.sha256(
                b"".join(owner_bodies.values())
            ).hexdigest(),
        }
    _require(len(all_bodies) == 18, "three-by-six body census drifted")
    _require(len(set(all_bodies)) == 18, "two exact owner-view bodies alias")
    findings.extend(
        (
            _finding(
                "three-exact-core-admissions",
                "Affirmative",
                "F0V2B2C1B4-A-THREE-CORE-ADMISSIONS",
                "three minimal exact module carriers pass canonical-byte owner admission",
            ),
            _finding(
                "three-exact-fresh-pairings",
                "Affirmative",
                "F0V2B2C1B4-A-THREE-FRESH-PAIRINGS",
                "each admitted module Core forms one same-evaluator exact Fresh Protocol",
            ),
            _finding(
                "six-view-owner-formation",
                "Affirmative",
                "F0V2B2C1B4-A-SIX-VIEW-FORMATION",
                "all six normalized owner views form for every module carrier",
            ),
            _finding(
                "cold-source-projection-agreement",
                "Affirmative",
                "F0V2B2C1B4-A-COLD-SOURCE-AGREEMENT",
                "the independent cold projector agrees on all eighteen bodies after authenticating module sources",
            ),
            _finding(
                "exact-view-roundtrip-and-order",
                "Affirmative",
                "F0V2B2C1B4-A-ROUNDTRIP-ORDER",
                "all bodies round-trip and sorted-unique collections follow target-byte order",
            ),
            _finding(
                "projection-determinism",
                "Affirmative",
                "F0V2B2C1B4-A-PROJECTION-DETERMINISM",
                "reprojection from immutable Core and Protocol authority is byte-identical",
            ),
        )
    )

    no_decision = records["module-no-decision"]
    decision = records["module-prover-decision"]
    publication = records["module-prover-publication"]
    _require(
        no_decision["cold_evidence"]["decision_classes"] == (0,)
        and no_decision["views"]["StrategyDecisionView"][1] == []
        and len(no_decision["views"]["EffectView"][7]) == 1,
        "NoProverDecision owner projection drifted",
    )
    findings.append(
        _finding(
            "module-no-decision",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE_NO_DECISION",
            "one exact deterministic module declaration contributes no prover move and one supported extension atom",
        )
    )

    decision_reads = decision["views"]["StrategyDecisionView"][3]
    _require(
        decision["cold_evidence"]["decision_classes"] == (1, 1)
        and len(decision["views"]["StrategyDecisionView"][1]) == 2
        and len(decision["views"]["StrategyDecisionView"][4]) == 2
        and [row[1]["case"] for row in decision_reads].count(8) == 1
        and [row[1]["case"] for row in decision_reads].count(9) == 1,
        "ProverDecision move/read projection drifted",
    )
    findings.append(
        _finding(
            "module-prover-decision",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE_PROVER_DECISION",
            "two exact module decisions expose typed module moves, one observed module output, and one prior-own-move read",
        )
    )

    publication_strategy = publication["views"]["StrategyDecisionView"]
    _require(
        publication["cold_evidence"]["decision_classes"] == (2,)
        and len(publication_strategy[1]) == 1
        and publication_strategy[1][0][4]["case"] == 2
        and len(publication["views"]["EffectView"][7]) == 1,
        "ProverPublication owner projection drifted",
    )
    findings.append(
        _finding(
            "module-prover-publication",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE_PROVER_PUBLICATION",
            "one exact publication declaration exposes a typed module move and a public module observation",
        )
    )

    _require(
        all(
            record["cold_evidence"]["module_sources"] == 1
            and len(record["module_sources"]) == 1
            for record in records.values()
        ),
        "exact used-module preimage closure drifted",
    )
    findings.append(
        _finding(
            "authenticated-used-module-preimage-closure",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE-PREIMAGE-CLOSURE",
            "each Core reference is supplemented by the exact authenticated used-module preimage closure before projection",
        )
    )

    no_env = handles["module-no-decision"][0]
    algorithm = model.identity_algorithm()
    semantics = model.supported_semantics()[0]
    _require(
        semantics.outputs[0].reconstruction_algorithm == algorithm.identity
        and semantics.outputs[0].reconstruction_contract
        == model.k1.DEFAULT_EVALUATION_CONTRACT.identity
        and set(no_env.algorithm_preimages) == {algorithm.identity}
        and set(no_env.contract_preimages)
        == {model.k1.DEFAULT_EVALUATION_CONTRACT.identity},
        "deterministic reconstruction closure drifted",
    )
    findings.append(
        _finding(
            "deterministic-module-reconstruction-authority",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE-RECONSTRUCTION",
            "the deterministic public output names an authenticated exact total reconstruction algorithm and contract",
        )
    )

    eligibility = {
        name: record["views"]["PublicCoinView"][2] for name, record in records.items()
    }
    _require(
        eligibility
        == {
            "module-no-decision": True,
            "module-prover-decision": False,
            "module-prover-publication": True,
        },
        "module FS eligibility split drifted",
    )
    findings.append(
        _finding(
            "admission-is-distinct-from-fs-eligibility",
            "Affirmative",
            "F0V2B2C1B4-A-ADMISSION-ELIGIBILITY-SPLIT",
            "all three Cores are admitted while a private prover-module output reaching acceptance remains structurally FS-ineligible",
        )
    )

    expected_graphs = {
        "module-no-decision": (11, 15, 0),
        "module-prover-decision": (16, 25, 3),
        "module-prover-publication": (11, 15, 1),
    }
    for name, (nodes, edges, output_class) in expected_graphs.items():
        graph = records[name]["views"]["PublicCoinView"][1]
        evidence = records[name]["cold_evidence"]["pc_graph"]
        _require(
            evidence["nodes"] == nodes and evidence["edges"] == edges,
            f"{name} graph census drifted",
        )
        class_rows = {
            model.codec.encode_value(model._PC_NODE_SCHEMA, row[0]): row[1]["case"]
            for row in graph[3]
        }
        module_node = model.foundation._v(
            13,
            {
                0: model.foundation._ordinal("occurrence-ref-body-v0", 0),
                1: 0,
            },
        )
        _require(
            class_rows[model.codec.encode_value(model._PC_NODE_SCHEMA, module_node)]
            == output_class,
            f"{name} module transfer class drifted",
        )
    findings.append(
        _finding(
            "module-pcgraph-transfer-classes",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE-PCGRAPH-TRANSFERS",
            "declaration-owned dependencies and deterministic, private, and publication transfers produce exact graph classes",
        )
    )

    graph_edges = {
        model.codec.encode_value(model._PC_EDGE_SCHEMA, row)
        for row in publication["views"]["PublicCoinView"][1][1]
    }
    required_edges = {
        ((0, 0), (13, 0, 0)),
        ((6, 0), (13, 0, 0)),
        ((7, 0), (13, 0, 0)),
        ((13, 0, 0), (8, 0, 0)),
        ((13, 0, 0), (12, 0, 0)),
    }
    expected_edges = {
        model.codec.encode_value(model._PC_EDGE_SCHEMA, model._edge_value(edge))
        for edge in required_edges
    }
    _require(expected_edges <= graph_edges, "module PCGraph dependency edge drifted")
    findings.append(
        _finding(
            "module-declaration-owned-pcgraph-edges",
            "Affirmative",
            "F0V2B2C1B4-A-MODULE-PCGRAPH-EDGES",
            "payload, activity, effect, module-output, occurrence-output, and control dependencies form explicit exact edges",
        )
    )

    runtime = decision["views"]["ExecutionView"][6]
    _require(
        len(runtime[0]) == 3
        and runtime[1] == []
        and runtime[2] == []
        and len(runtime[3]) == 1,
        "module runtime schema projection drifted",
    )
    findings.append(
        _finding(
            "static-module-runtime-schema",
            "Affirmative",
            "F0V2B2C1B4-A-STATIC-EXECUTION-SCHEMA",
            "Fresh execution projects exact occurrence-output and terminal schemas without inventing module runtime receipts",
        )
    )

    no_environment, _no_candidate, no_handle, _no_protocol = handles[
        "module-no-decision"
    ]
    no_core = model.retained_core(no_handle)
    decision_environment, _decision_candidate, decision_handle, _decision_protocol = (
        handles["module-prover-decision"]
    )
    decision_core = model.retained_core(decision_handle)
    (
        publication_environment,
        _publication_candidate,
        publication_handle,
        _publication_protocol,
    ) = handles["module-prover-publication"]
    publication_core = model.retained_core(publication_handle)
    original_module = next(iter(no_environment.module_preimages.values()))
    foreign_semantics = list(model.supported_semantics())
    foreign_semantics[0] = replace(
        foreign_semantics[0], name="bounded-deterministic-public-foreign"
    )
    foreign_module = model.extension_module(tuple(foreign_semantics))

    first_effect = no_core.occurrences[0].effect
    payload_empty = replace(first_effect, payload=model.ModulePayload(()))
    future_effect = replace(
        decision_core.occurrences[0].effect,
        payload=model.ModulePayload((model.base.OccurrenceOutputRef(1, 0),)),
    )
    z4 = model.k1.ValueType(model.k1.NAT_DOMAIN, model.k1.NatSchema(3))
    wrong_type_core = replace(no_core, public_inputs=(model.base.InputDecl(z4),))
    owner_mismatch_effect = replace(first_effect, module=foreign_module.identity)
    owner_mismatch_core = _replace_occurrence_effect(
        model, no_core, 0, owner_mismatch_effect
    )
    owner_mismatch_core = replace(
        owner_mismatch_core,
        used_modules=tuple(
            sorted(
                (original_module.identity, foreign_module.identity),
                key=lambda item: item.internal_reference(),
            )
        ),
    )
    owner_mismatch_environment = replace(
        no_environment,
        module_preimages=MappingProxyType(
            {
                original_module.identity: original_module,
                foreign_module.identity: foreign_module,
            }
        ),
    )
    wrong_kind_effect = replace(
        first_effect,
        declaration=replace(
            first_effect.declaration,
            declaration_kind="pir.challenge-domain",
        ),
    )
    wrong_ordinal_effect = replace(
        first_effect,
        declaration=replace(first_effect.declaration, local_ordinal=3),
    )
    extra_modules = tuple(
        sorted(
            (original_module.identity, foreign_module.identity),
            key=lambda item: item.internal_reference(),
        )
    )
    extra_module_environment = replace(
        no_environment,
        module_preimages=MappingProxyType(
            {
                original_module.identity: original_module,
                foreign_module.identity: foreign_module,
            }
        ),
    )
    wrong_algorithm = model.k1.CanonicalAlgorithm(
        model.k1.Symbol("f0v2b2c1b4.wrong-reconstruction"),
        (model.base.Z3,),
        model.k1.Variable(0, model.base.Z3),
    )
    terminal_first = replace(
        no_core,
        occurrences=(no_core.occurrences[-1], *no_core.occurrences[:-1]),
    )
    invalid_terminal = model.base.OccurrenceDecl(
        0, model.base.AlwaysGuard(), model.base.TerminalEffect(1)
    )
    bad_backlink_core = replace(
        no_core,
        occurrences=(
            no_core.occurrences[0],
            invalid_terminal,
            no_core.occurrences[-1],
        ),
    )

    direct_mutations: tuple[
        tuple[str, str, str, Callable[[], tuple[object, object]], str], ...
    ] = (
        (
            "module-payload-arity",
            "Malformed",
            "F0V2B2C1B4-M-MODULE-PAYLOAD-ARITY",
            lambda: _candidate(
                model,
                no_environment,
                _replace_occurrence_effect(model, no_core, 0, payload_empty),
            ),
            "a freshly authenticated module payload cannot omit its declared input",
        ),
        (
            "module-payload-availability",
            "Refused",
            "F0V2B2C1B4-R-MODULE-PAYLOAD-AVAILABILITY",
            lambda: _candidate(
                model,
                decision_environment,
                _replace_occurrence_effect(model, decision_core, 0, future_effect),
            ),
            "a module payload cannot read a future occurrence output",
        ),
        (
            "module-payload-abi",
            "KindMismatch",
            "F0V2B2C1B4-K-MODULE-PAYLOAD-ABI",
            lambda: _candidate(model, no_environment, wrong_type_core),
            "a module payload value type must equal its declaration ABI",
        ),
        (
            "module-owner-declaration-mismatch",
            "Refused",
            "F0V2B2C1B4-R-MODULE-OWNER",
            lambda: _candidate(model, owner_mismatch_environment, owner_mismatch_core),
            "the effect owner and declaration owner must be identical",
        ),
        (
            "module-declaration-kind",
            "KindMismatch",
            "F0V2B2C1B4-K-MODULE-DECLARATION",
            lambda: _candidate(
                model,
                no_environment,
                _replace_occurrence_effect(model, no_core, 0, wrong_kind_effect),
            ),
            "a module effect must select the exact core-effect declaration kind",
        ),
        (
            "module-declaration-coordinate",
            "Refused",
            "F0V2B2C1B4-R-MODULE-COORDINATE",
            lambda: _candidate(
                model,
                no_environment,
                _replace_occurrence_effect(model, no_core, 0, wrong_ordinal_effect),
            ),
            "a module effect cannot select an absent local declaration",
        ),
        (
            "used-module-omission",
            "Refused",
            "F0V2B2C1B4-R-EXACT-USED-MODULES",
            lambda: _candidate(
                model, no_environment, replace(no_core, used_modules=())
            ),
            "used_modules cannot omit a direct module-effect owner",
        ),
        (
            "used-module-extra",
            "Refused",
            "F0V2B2C1B4-R-EXACT-USED-MODULES",
            lambda: _candidate(
                model,
                extra_module_environment,
                replace(no_core, used_modules=extra_modules),
            ),
            "used_modules cannot assert an unreferenced semantic module",
        ),
        (
            "module-preimage-missing",
            "MissingDependency",
            "F0V2B2C1B4-D-MODULE-PREIMAGE",
            lambda: _candidate(
                model,
                replace(no_environment, module_preimages=MappingProxyType({})),
                no_core,
            ),
            "a used module requires its exact semantic preimage",
        ),
        (
            "module-preimage-extra",
            "Refused",
            "F0V2B2C1B4-R-EXACT-MODULE-PREIMAGES",
            lambda: _candidate(model, extra_module_environment, no_core),
            "ambient unreferenced module preimages are not accepted as closure",
        ),
        (
            "module-preimage-id",
            "Refused",
            "F0V2B2C1B4-R-MODULE-ID",
            lambda: _candidate(
                model,
                replace(
                    no_environment,
                    module_preimages=MappingProxyType(
                        {original_module.identity: foreign_module}
                    ),
                ),
                no_core,
            ),
            "a module preimage must authenticate the referenced module ID",
        ),
        (
            "reconstruction-algorithm-missing",
            "MissingDependency",
            "F0V2B2C1B4-D-RECONSTRUCTION-ALGORITHM",
            lambda: _candidate(
                model,
                replace(no_environment, algorithm_preimages=MappingProxyType({})),
                no_core,
            ),
            "a deterministic public module output requires its algorithm preimage",
        ),
        (
            "reconstruction-contract-missing",
            "MissingDependency",
            "F0V2B2C1B4-D-RECONSTRUCTION-CONTRACT",
            lambda: _candidate(
                model,
                replace(no_environment, contract_preimages=MappingProxyType({})),
                no_core,
            ),
            "a deterministic public module output requires its contract preimage",
        ),
        (
            "reconstruction-module-closure-missing",
            "MissingDependency",
            "F0V2B2C1B4-D-RECONSTRUCTION-MODULES",
            lambda: _candidate(
                model,
                replace(no_environment, algorithm_modules=MappingProxyType({})),
                no_core,
            ),
            "a reconstruction algorithm requires an explicit module closure",
        ),
        (
            "reconstruction-algorithm-extra",
            "Refused",
            "F0V2B2C1B4-R-EXACT-ALGORITHMS",
            lambda: _candidate(
                model,
                replace(
                    decision_environment,
                    algorithm_preimages=MappingProxyType(
                        {algorithm.identity: algorithm}
                    ),
                    algorithm_modules=MappingProxyType(
                        {algorithm.identity: MappingProxyType({})}
                    ),
                ),
                decision_core,
            ),
            "an unrelated reconstruction algorithm cannot enter the exact closure",
        ),
        (
            "reconstruction-algorithm-id",
            "Refused",
            "F0V2B2C1B4-R-RECONSTRUCTION-ID",
            lambda: _candidate(
                model,
                replace(
                    no_environment,
                    algorithm_preimages=MappingProxyType(
                        {algorithm.identity: wrong_algorithm}
                    ),
                ),
                no_core,
            ),
            "a reconstruction preimage must authenticate the declaration-owned ID",
        ),
        (
            "terminal-not-final",
            "Refused",
            "F0V2B2C1B4-R-TERMINAL-FALLBACK",
            lambda: _candidate(model, no_environment, terminal_first),
            "the bounded carrier requires its unconditional terminal fallback last",
        ),
        (
            "terminal-backlink",
            "Refused",
            "F0V2B2C1B4-R-TERMINAL-BACKLINK",
            lambda: _candidate(model, no_environment, bad_backlink_core),
            "an extra terminal occurrence cannot name an absent declaration",
        ),
    )
    for name, outcome, code, operation, detail in direct_mutations:
        environment, candidate = operation()
        result = model.admit_core(candidate, environment)
        _expect(result, outcome, code, name)
        findings.append(_finding(name, outcome, code, detail))

    activity = model.ModuleDependency(model.ModuleDependencyKind.ACTIVITY)
    declaration_mutations: tuple[
        tuple[str, int, Callable[[object], object], str, str, str], ...
    ] = (
        (
            "module-declaration-support-pin",
            0,
            lambda item: replace(item, name=item.name + "-drift"),
            "Unsupported",
            "F0V2B2C1B4-U-MODULE-DECLARATION",
            "a valid but unadvertised module declaration is not silently accepted",
        ),
        (
            "module-dependency-duplicate",
            0,
            lambda item: replace(
                item,
                outputs=(
                    replace(
                        item.outputs[0],
                        dependencies=(*item.outputs[0].dependencies, activity),
                    ),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-EDGE-UNIQUE",
            "declaration-owned dependency edges must be unique",
        ),
        (
            "module-dependency-effect-omission",
            0,
            lambda item: replace(
                item,
                outputs=(
                    replace(
                        item.outputs[0],
                        dependencies=tuple(
                            dep
                            for dep in item.outputs[0].dependencies
                            if dep.kind is not model.ModuleDependencyKind.EFFECT
                        ),
                    ),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-EDGE-CLOSURE",
            "a module result cannot omit its effect dependency",
        ),
        (
            "module-dependency-input-coordinate",
            0,
            lambda item: replace(
                item,
                outputs=(
                    replace(
                        item.outputs[0],
                        dependencies=tuple(
                            model.ModuleDependency(dep.kind, 1)
                            if dep.kind is model.ModuleDependencyKind.PAYLOAD_INPUT
                            else dep
                            for dep in item.outputs[0].dependencies
                        ),
                    ),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-EDGE-REF",
            "a declaration dependency cannot name an absent payload input",
        ),
        (
            "module-lifecycle-work-bound",
            0,
            lambda item: replace(item, work_bound=0),
            "Refused",
            "F0V2B2C1B4-R-MODULE-LIFECYCLE",
            "the exact module lifecycle requires a positive bounded work rule",
        ),
        (
            "deterministic-output-visibility",
            0,
            lambda item: replace(
                item,
                outputs=(
                    replace(
                        item.outputs[0], visibility=model.ModuleVisibility.INTERNAL
                    ),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-RECONSTRUCTION",
            "a deterministic reconstructed output must be public",
        ),
        (
            "publication-output-visibility",
            2,
            lambda item: replace(
                item,
                outputs=(
                    replace(
                        item.outputs[0],
                        visibility=model.ModuleVisibility.PROVER_ONLY,
                    ),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-PUBLICATION",
            "a ProverPublication requires an exact public observation",
        ),
        (
            "internal-output-visibility",
            1,
            lambda item: replace(
                item,
                outputs=(
                    replace(item.outputs[0], visibility=model.ModuleVisibility.PUBLIC),
                ),
            ),
            "Refused",
            "F0V2B2C1B4-R-MODULE-INTERNAL-OUTPUT",
            "a private module move output cannot be asserted public",
        ),
        (
            "publication-influence-missing",
            2,
            lambda item: replace(item, influence_output=None),
            "Refused",
            "F0V2B2C1B4-R-MODULE-PUBLICATION",
            "a ProverPublication must identify its unique public influence output",
        ),
        (
            "nonpublication-influence",
            1,
            lambda item: replace(item, influence_output=0),
            "Refused",
            "F0V2B2C1B4-R-MODULE-INFLUENCE",
            "a nonpublication module cannot assert publication influence",
        ),
    )
    for name, declaration, transform, outcome, code, detail in declaration_mutations:
        bases = {
            0: (no_environment, no_core),
            1: (decision_environment, decision_core),
            2: (publication_environment, publication_core),
        }
        base_environment, base_core = bases[declaration]
        environment, candidate = _declaration_mutation(
            model, base_environment, base_core, declaration, transform
        )
        result = model.admit_core(candidate, environment)
        _expect(result, outcome, code, name)
        findings.append(_finding(name, outcome, code, detail))

    owner_wrong_views: list[tuple[str, str, str, str, dict[str, Any], bytes]] = []
    extension_removed = copy.deepcopy(no_decision["views"]["EffectView"])
    extension_removed[7] = []
    owner_wrong_views.append(
        (
            "schema-valid-supported-extension-omission",
            "EffectView",
            "F0V2B2C1B4-R-OWNER-SUPPORTED-EXTENSION",
            "the admitted module effect cannot disappear from SupportedExtensionAtom",
            extension_removed,
            no_decision["bodies"]["EffectView"],
        )
    )
    move_type_changed = copy.deepcopy(publication["views"]["StrategyDecisionView"])
    move_type_changed[1][0][4]["value"][1] = model.foundation._value_type_body(z4)
    owner_wrong_views.append(
        (
            "schema-valid-module-move-type-substitution",
            "StrategyDecisionView",
            "F0V2B2C1B4-R-OWNER-MODULE-MOVE-TYPE",
            "another type body cannot replace the declaration-owned module move ABI",
            move_type_changed,
            publication["bodies"]["StrategyDecisionView"],
        )
    )
    edge_removed = copy.deepcopy(publication["views"]["PublicCoinView"])
    edge_removed[1][1] = edge_removed[1][1][1:]
    owner_wrong_views.append(
        (
            "schema-valid-module-edge-omission",
            "PublicCoinView",
            "F0V2B2C1B4-R-OWNER-MODULE-EDGE",
            "a schema-valid graph cannot omit a declaration-derived module edge",
            edge_removed,
            publication["bodies"]["PublicCoinView"],
        )
    )
    class_changed = copy.deepcopy(decision["views"]["PublicCoinView"])
    for row in class_changed[1][3]:
        if row[0]["case"] == 13:
            row[1] = model.foundation._v(1)
            break
    owner_wrong_views.append(
        (
            "schema-valid-module-class-substitution",
            "PublicCoinView",
            "F0V2B2C1B4-R-OWNER-MODULE-CLASS",
            "PublicCoin cannot replace the private declaration-owned module transfer class",
            class_changed,
            decision["bodies"]["PublicCoinView"],
        )
    )
    observed_removed = copy.deepcopy(decision["views"]["StrategyDecisionView"])
    observed_removed[3] = [row for row in observed_removed[3] if row[1]["case"] != 8]
    owner_wrong_views.append(
        (
            "schema-valid-observed-module-read-omission",
            "StrategyDecisionView",
            "F0V2B2C1B4-R-OWNER-OBSERVED-MODULE-READ",
            "a later module decision retains its guaranteed observed-module read",
            observed_removed,
            decision["bodies"]["StrategyDecisionView"],
        )
    )
    prior_move_removed = copy.deepcopy(decision["views"]["StrategyDecisionView"])
    prior_move_removed[3] = [
        row for row in prior_move_removed[3] if row[1]["case"] != 9
    ]
    owner_wrong_views.append(
        (
            "schema-valid-prior-own-move-read-omission",
            "StrategyDecisionView",
            "F0V2B2C1B4-R-OWNER-PRIOR-MOVE-READ",
            "a later module decision retains its guaranteed prior-own-move read",
            prior_move_removed,
            decision["bodies"]["StrategyDecisionView"],
        )
    )
    for name, view_name, code, detail, value, owner_body in owner_wrong_views:
        substituted = model.codec.encode_value(model.VIEW_SCHEMAS[view_name], value)
        _require(substituted != owner_body, f"{name} aliased the owner body")
        findings.append(_finding(name, "Refused", code, detail))

    first = handles["module-no-decision"]
    second = handles["module-prover-decision"]
    source_reference, source_body = records["module-no-decision"]["module_sources"][0]
    cold_cases = (
        (
            "cold-module-source-missing",
            "F0V2B2C1B4-R-COLD-MODULE-SOURCE-MISSING",
            lambda: cold_projector.project(
                first[2].profiled_body,
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
                (),
            ),
            "the cold projector cannot classify a module from its Core reference alone",
        ),
        (
            "cold-module-source-body-substitution",
            "F0V2B2C1B4-R-COLD-MODULE-BODY",
            lambda: cold_projector.project(
                first[2].profiled_body,
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
                ((source_reference, source_body[:-1] + bytes((source_body[-1] ^ 1,))),),
            ),
            "the cold projector authenticates the complete module body against its reference",
        ),
        (
            "cold-module-source-truncation",
            "F0V2B2C1B4-R-COLD-MODULE-TRUNCATION",
            lambda: cold_projector.project(
                first[2].profiled_body,
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
                ((source_reference, source_body[:-1]),),
            ),
            "the cold projector requires a complete canonical module preimage",
        ),
        (
            "cold-core-truncation",
            "F0V2B2C1B4-R-COLD-CORE-TRUNCATION",
            lambda: cold_projector.project(
                first[2].profiled_body[:-1],
                first[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
                records["module-no-decision"]["module_sources"],
            ),
            "the cold projector requires the complete canonical profiled Core body",
        ),
        (
            "cold-core-body-reference-substitution",
            "F0V2B2C1B4-R-COLD-CORE-BODY-REFERENCE",
            lambda: cold_projector.project(
                first[2].profiled_body,
                second[2].core_reference,
                first[3].profiled_body,
                first[3].protocol_reference,
                records["module-no-decision"]["module_sources"],
            ),
            "the cold projector independently authenticates Core body/reference equality",
        ),
        (
            "cold-cross-core-protocol-substitution",
            "F0V2B2C1B4-R-COLD-PROTOCOL-CORE",
            lambda: cold_projector.project(
                first[2].profiled_body,
                first[2].core_reference,
                second[3].profiled_body,
                second[3].protocol_reference,
                records["module-no-decision"]["module_sources"],
            ),
            "an independently authenticated Fresh Protocol must cite the identical Core",
        ),
    )
    for name, code, operation, detail in cold_cases:
        _require(
            _rejects(operation, cold_projector.ColdModuleError),
            f"{name} was accepted by the cold projector",
        )
        findings.append(_finding(name, "Refused", code, detail))

    predecessor_fixture = model.prior.fixtures()["claim-initial-linear"]
    predecessor_core = model.prior.admit_core(
        predecessor_fixture[1], predecessor_fixture[0]
    )
    _expect(
        predecessor_core,
        "Affirmative",
        "F0V2B2C1B3-A-CORE-ADMITTED",
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
        "F0V2B2C1B3-A-FRESH-ADMITTED",
        "predecessor Protocol",
    )
    _require(
        _rejects(
            lambda: model.project_views(
                predecessor_core.handle, predecessor_protocol.handle
            ),
            model.FamilyFailure,
        ),
        "B2C1B4 projector accepted predecessor-evaluator authority",
    )
    findings.append(
        _finding(
            "foreign-predecessor-evaluator-authority",
            "Refused",
            "F0V2B2C1B4-R-CORE-AUTHORITY",
            "a genuine B2C1B3 bearer cannot authorize the B2C1B4 projection law",
        )
    )

    cannot_answer = (
        (
            "expanded-terminal-family",
            "F0V2B2C1B4-C-EXPANDED-TERMINAL",
            "the final expanded-terminal B2C family remains B2C1B5",
        ),
        (
            "integrated-pcgraph-families",
            "F0V2B2C1B4-C-INTEGRATED-PCGRAPH",
            "all-class invalid/private/logical graph interactions remain B2D",
        ),
        (
            "runtime-module-history",
            "F0V2B2C1B4-C-RUNTIME-HISTORY",
            "static schemas do not execute a module or validate a completed module event history",
        ),
        (
            "general-module-language",
            "F0V2B2C1B4-C-GENERAL-MODULE-LANGUAGE",
            "one exact supported fixture module does not establish a general extension-module language",
        ),
        (
            "target-publication",
            "F0V2B2C1B4-C-TARGET-PUBLICATION",
            "candidate module schemas and laws are not published target semantics",
        ),
        (
            "live-implementation-correspondence",
            "F0V2B2C1B4-C-LIVE-CORRESPONDENCE",
            "no current compiler, module loader, or runtime implementation is validated",
        ),
        (
            "formal-proof",
            "F0V2B2C1B4-C-FORMAL-PROOF",
            "finite dual-path evidence is not a mechanized refinement or equivalence proof",
        ),
        (
            "cryptographic-security",
            "F0V2B2C1B4-C-SECURITY",
            "module structural eligibility proves no soundness or Fiat-Shamir theorem",
        ),
        (
            "bcs-rbr-duplex-or-qrom-theorem",
            "F0V2B2C1B4-C-THEOREM-REGIME",
            "BCS, RBR, duplex, concrete-instantiation, and QROM obligations remain separate theorem regimes",
        ),
        (
            "q1-correspondence",
            "F0V2B2C1B4-C-Q1",
            "Q1 remains open through target migration and live owner correspondence",
        ),
    )
    findings.extend(
        _finding(name, "CannotAnswer", code, detail)
        for name, code, detail in cannot_answer
    )
    findings.append(
        _finding(
            "module-owner-projection-aggregate",
            "Affirmative",
            AGGREGATE,
            "three semantic-module isolation families have bounded exact owner-projection evidence with runtime, theorem, and security boundaries preserved",
        )
    )

    rows = [asdict(item) for item in findings]
    evidence = {
        "aggregate": AGGREGATE,
        "covered_families": list(MODULE_FAMILIES),
        "remaining_b2c_families": 1,
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
        "semantic_mutations": len(direct_mutations) + len(declaration_mutations),
        "schema_valid_owner_substitutions": len(owner_wrong_views),
        "cold_negative_controls": len(cold_cases),
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
        raise GateFailure("cannot read expected B2C1B4 findings") from error
    if (
        type(value) is not dict
        or set(value) != {"aggregate", "findings_sha256", "finding_codes"}
        or value["aggregate"] != AGGREGATE
        or type(value["findings_sha256"]) is not str
        or type(value["finding_codes"]) is not list
    ):
        raise GateFailure("expected B2C1B4 findings have another shape")
    rows = value["finding_codes"]
    allowed = {
        "Affirmative",
        "CannotAnswer",
        "KindMismatch",
        "Malformed",
        "MissingDependency",
        "Refused",
        "Unsupported",
    }
    if any(
        type(row) is not list
        or len(row) != 3
        or any(type(item) is not str or not item for item in row)
        or row[1] not in allowed
        for row in rows
    ):
        raise GateFailure("expected B2C1B4 finding row has another shape")
    if len({row[0] for row in rows}) != len(rows):
        raise GateFailure("expected B2C1B4 finding names are not unique")
    try:
        digest = bytes.fromhex(value["findings_sha256"])
    except ValueError as error:
        raise GateFailure("expected B2C1B4 digest is not hexadecimal") from error
    if len(digest) != 32:
        raise GateFailure("expected B2C1B4 digest is not SHA-256 sized")
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
                "frozen B2C1B4 findings drifted",
            )
        if args.print_findings:
            print(json.dumps(observed, indent=2, sort_keys=True))
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        print(
            "[formal-source-module-owner-projections-f0v2b2c1b4] "
            f"{len(findings)}/{len(findings)} findings; Affirmative/{AGGREGATE}; "
            f"{evidence['view_body_count']} exact view bodies; "
            f"{evidence['finding_counts']}"
        )
        return 0
    except Exception as error:
        print(f"[formal-source-module-owner-projections-f0v2b2c1b4] FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
