#!/usr/bin/env python3
"""Reverse cold-view and non-uniqueness reconstruction for F2-P0."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEDGER = HERE / "contract-ledger.json"
B1 = ROOT / "evaluation/formal-source-view-bodies-f0v2b1"
F1 = ROOT / "evaluation/formal-source-target-core-f1r1b"
F2_LEDGER = ROOT / "evaluation/formal-provider-observables-f2o0/generated/ledger.json"


class IndependentFailure(RuntimeError):
    pass


def _module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise IndependentFailure(f"cannot load module at {path}")
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value


def _json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IndependentFailure(f"cannot decode {path}") from error


def _sha_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha_value(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def _cold_basis() -> dict[str, int]:
    ledger = _json(LEDGER)
    if ledger.get("cutoff") != "de49641aba0086b1e3f7eff48f5276ffd8af2845":
        raise IndependentFailure("cold path sees another cutoff")
    range_count = 0
    anchor_count = 0
    paths: set[str] = set()
    entries = ledger.get("contract_sources", []) + ledger.get("predecessor_sources", [])
    for source in entries:
        if source["path"] in paths:
            raise IndependentFailure("cold path sees a duplicate source pin")
        paths.add(source["path"])
        target = ROOT.joinpath(*source["path"].split("/"))
        if _sha_file(target) != source["sha256"]:
            raise IndependentFailure(f"cold source pin mismatch: {source['path']}")
        text = target.read_text(encoding="utf-8").splitlines()
        for citation in source.get("ranges", []):
            range_count += 1
            selected = text[citation["start"] - 1 : citation["end"]]
            if len(selected) != citation["end"] - citation["start"] + 1:
                raise IndependentFailure(f"cold citation is out of range: {citation['id']}")
            flattened = "\n".join(selected)
            missing = [anchor for anchor in citation["anchors"] if anchor not in flattened]
            if missing:
                raise IndependentFailure(f"cold citation lost anchors: {citation['id']}")
            anchor_count += len(citation["anchors"])
    if len(ledger.get("contract_sources", [])) != 3 or len(entries) != 10:
        raise IndependentFailure("cold path sees another source partition")
    return {
        "contract_sources": 3,
        "predecessor_sources": 7,
        "cited_ranges": range_count,
        "anchors": anchor_count,
    }


def _decode_small_nat(body: dict[str, str], compiler: str) -> int:
    if body.get("compiler") != compiler:
        raise IndependentFailure(f"wrong cold compiler for {compiler}")
    raw = bytes.fromhex(body.get("body", ""))
    if len(raw) != 10 or raw[0] != 3 or int.from_bytes(raw[1:9], "big") != 1:
        raise IndependentFailure("cold path saw another small-natural body")
    return raw[9]


def _cold_property_gaps() -> list[str]:
    source = _json(F2_LEDGER)
    if set(source) != {
        "authority",
        "constructs",
        "format",
        "gaps",
        "marker",
        "premises",
        "provider",
        "rendering_rules",
        "subject",
    }:
        raise IndependentFailure("cold F2 ledger has another outer shape")
    observed = []
    for item in source["constructs"]:
        candidate = item["source"].get("no_source_coordinate")
        if candidate and candidate.get("class") == "property-premise":
            observed.append(item["id"])
    expected = [
        "provider.witness-type",
        "provider.prover-state-type",
        "provider.relation",
        "provider.commit",
        "provider.respond",
    ]
    if observed != expected:
        raise IndependentFailure("cold F2 property gap inventory differs")
    return observed


def _cold_truth_table() -> tuple[str, dict[tuple[int, int, int, int], bool]]:
    interpreter = _module("_zkc_f2p0_term_interpreter", F1 / "independent.py")
    fixture = interpreter.r.make_fixture()
    table: dict[tuple[int, int, int, int], bool] = {}
    bits = bytearray()
    for y in range(3):
        for commitment in range(3):
            for challenge in range(3):
                for response in range(3):
                    key = (y, commitment, challenge, response)
                    value = interpreter.interpret_term(fixture.schnorr_algorithm.term, key)
                    if type(value) is not bool:
                        raise IndependentFailure("cold term interpreter returned non-Boolean")
                    if value != (response == (commitment + challenge * y) % 3):
                        raise IndependentFailure(f"cold verifier differs at {key!r}")
                    table[key] = value
                    bits.append(value)
    return hashlib.sha256(bytes(bits)).hexdigest(), table


def _countermodels(table: dict[tuple[int, int, int, int], bool]) -> list[dict[str, Any]]:
    first_good = first_bad = 0
    for statement in range(3):
        witness = statement
        for state in range(3):
            for coin in range(3):
                answer = (state + coin * witness) % 3
                first_good += int(table[(statement, state, coin, answer)])
                first_bad += int(table[(statement, state, coin, (answer + 1) % 3)])
    second_good = second_bad = 0
    for statement in range(3):
        for coin in range(3):
            answer = coin * statement % 3
            second_good += int(table[(statement, 0, coin, answer)])
            second_bad += int(table[(statement, 0, coin, (answer + 1) % 3)])
    if (first_good, first_bad, second_good, second_bad) != (27, 0, 9, 0):
        raise IndependentFailure("finite countermodel census drifted")
    return [
        {
            "name": "knowledge-shaped",
            "relation": "rel(y,x) iff y=x in Z3",
            "witness_carrier": "Z3",
            "private_state_carrier": "Z3 nonce",
            "commit": "a:=r",
            "respond": "z:=r+c*x mod 3",
            "accepted_honest_runs": first_good,
            "rejected_plus_one_controls": 27 - first_bad,
        },
        {
            "name": "statement-only",
            "relation": "rel(y,unit) is always true",
            "witness_carrier": "Unit",
            "private_state_carrier": "Unit",
            "commit": "a:=0",
            "respond": "z:=c*y mod 3",
            "accepted_honest_runs": second_good,
            "rejected_plus_one_controls": 9 - second_bad,
        },
    ]


def _matrix() -> dict[str, Any]:
    return {
        "relation-predicate": {
            "current_role_site": "Statement binding 0 names the public side only",
            "current_premise_coordinate": None,
            "conditional_owner_coordinates": [
                "RelationSemanticModel.evaluator",
                "CheckedRelationSatisfaction",
            ],
            "after_authored_bundle": "owner-local partial decision coordinate",
            "provider_residual": "total Stmt->Wit->Bool translation, termination basis, and acceptance correspondence",
            "current_outcome": "CannotAnswer",
        },
        "witness-type": {
            "current_role_site": None,
            "current_premise_coordinate": None,
            "conditional_owner_coordinates": [
                "RelationInterface.private_witness[i].value_type",
                "PlanWitnessBinding.witness_edges[i]",
            ],
            "after_authored_bundle": "exact type-and-occurrence coordinate",
            "provider_residual": "provider carrier translation unless the exact representation is reused",
            "current_outcome": "CannotAnswer",
        },
        "prover-private-state": {
            "current_role_site": None,
            "current_premise_coordinate": None,
            "conditional_owner_coordinates": [
                "ProverPlan.persistent_state[i].value_type",
                "PlanExecutionState",
            ],
            "after_authored_bundle": "exact Plan state vector and adapter-state coordinate",
            "provider_residual": "translation from the richer adapter-private state to one provider PrvState carrier",
            "current_outcome": "CannotAnswer",
        },
        "honest-commit": {
            "current_role_site": "StrategyDecisionView decision 0",
            "current_premise_coordinate": None,
            "conditional_owner_coordinates": [
                "ProverPlan.decision_recipes[0]",
                "PlanStrategyStep(decision 0)",
            ],
            "after_authored_bundle": "exact strategy recipe coordinate",
            "provider_residual": "relation-relative honesty/correctness and provider-field correspondence",
            "current_outcome": "CannotAnswer",
        },
        "honest-respond": {
            "current_role_site": "StrategyDecisionView decision 2",
            "current_premise_coordinate": None,
            "conditional_owner_coordinates": [
                "ProverPlan.decision_recipes[2]",
                "PlanStrategyStep(decision 2)",
            ],
            "after_authored_bundle": "exact strategy recipe coordinate",
            "provider_residual": "relation-relative honesty/correctness and provider-field correspondence",
            "current_outcome": "CannotAnswer",
        },
    }


def reconstruct() -> dict[str, Any]:
    basis = _cold_basis()
    cold = _module("_zkc_f2p0_cold_views", B1 / "independent.py")
    candidate = cold.build_candidate()
    observation = cold.observe(candidate)
    strategy = candidate["values"]["StrategyDecisionView"]
    decisions = [
        _decode_small_nat(row[0], "decision-ref-body-v0") for row in strategy[1]
    ]
    occurrences = [
        _decode_small_nat(row[1], "occurrence-ref-body-v0") for row in strategy[1]
    ]
    public = candidate["values"]["PublicBindingView"]
    statement_binding = _decode_small_nat(public[2][0][0], "binding-ref-body-v0")
    if decisions != [0, 2] or occurrences != [0, 2] or statement_binding != 0:
        raise IndependentFailure("cold role-site reconstruction drifted")
    truth_digest, table = _cold_truth_table()
    ambiguity = _countermodels(table)
    subject = {
        "core_digest": observation["owner"]["core_digest"],
        "protocol_digest": observation["owner"]["protocol_digest"],
        "statement_binding": statement_binding,
        "decision_ordinals": decisions,
        "verifier_equation": "z=(a+c*y) mod 3",
        "verifier_truth_table_sha256": truth_digest,
        "verifier_cases": len(table),
        "view_leaf_count": observation["total_leaf_count"],
    }
    agreement = {
        "aggregate": "CannotAnswer/F2P0-C-EXACT-COUPLING-UNDERDETERMINED",
        "subject": subject,
        "f2_property_gaps": _cold_property_gaps(),
        "contract_route": [
            "RelationDefinition -> RelationInterface -> RelationSemanticModel",
            "RelationInterface -> RelationInstance",
            "Protocol -> ProtocolRelationBinding -> RelationInterface",
            "ProverPlan -> PlanRealizes -> PlanStrategyStep",
            "ProverPlan -> PlanWitnessSurface -> PlanWitnessBinding -> RelationInterface",
        ],
        "premises": _matrix(),
        "ambiguity_witnesses": ambiguity,
        "selection": "neither finite completion is selected or admitted",
    }
    return {
        "path": "reverse-cold-view-countermodel",
        "basis": basis,
        "agreement": agreement,
        "agreement_sha256": _sha_value(agreement),
    }
