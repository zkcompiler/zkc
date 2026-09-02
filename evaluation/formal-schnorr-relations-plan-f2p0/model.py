#!/usr/bin/env python3
"""Forward typed reconstruction for the F2-P0 Relations--Plan audit."""

from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEDGER = HERE / "contract-ledger.json"
F1 = ROOT / "evaluation/formal-source-target-core-f1r1b"
F2_LEDGER = ROOT / "evaluation/formal-provider-observables-f2o0/generated/ledger.json"


class AuditFailure(RuntimeError):
    pass


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AuditFailure(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditFailure(f"cannot read JSON at {path}") from error


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_digest(value: Any) -> str:
    body = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(body).hexdigest()


def validate_basis() -> dict[str, int]:
    ledger = _read_json(LEDGER)
    if tuple(ledger) != (
        "format",
        "cutoff",
        "question",
        "contract_sources",
        "predecessor_sources",
    ):
        raise AuditFailure("contract ledger has another outer shape")
    if ledger["format"] != "zkc.formal-schnorr-relations-plan-f2p0.contract-ledger.v0":
        raise AuditFailure("contract ledger has another format")
    ranges = 0
    anchors = 0
    for source in (*ledger["contract_sources"], *ledger["predecessor_sources"]):
        path = ROOT / source["path"]
        if _digest(path) != source["sha256"]:
            raise AuditFailure(f"pinned source drifted: {source['path']}")
        if "ranges" not in source:
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for item in source["ranges"]:
            ranges += 1
            if not 1 <= item["start"] <= item["end"] <= len(lines):
                raise AuditFailure(f"invalid cited range {item['id']}")
            excerpt = "\n".join(lines[item["start"] - 1 : item["end"]])
            for anchor in item["anchors"]:
                anchors += 1
                if anchor not in excerpt:
                    raise AuditFailure(f"missing cited anchor {item['id']}: {anchor}")
    return {
        "contract_sources": len(ledger["contract_sources"]),
        "predecessor_sources": len(ledger["predecessor_sources"]),
        "cited_ranges": ranges,
        "anchors": anchors,
    }


def _property_gaps() -> list[str]:
    ledger = _read_json(F2_LEDGER)
    result = []
    for construct in ledger["constructs"]:
        source = construct["source"]
        gap = source.get("no_source_coordinate")
        if gap is not None and gap["class"] == "property-premise":
            result.append(construct["id"])
    expected = [
        "provider.witness-type",
        "provider.prover-state-type",
        "provider.relation",
        "provider.commit",
        "provider.respond",
    ]
    if result != expected:
        raise AuditFailure(f"F2-O0 property-gap inventory drifted: {result!r}")
    return result


def _evaluate_truth_table(owner: ModuleType, fixture: object) -> tuple[str, Any]:
    evaluator = owner.k1.Evaluator()
    for values, expected in (((1, 2, 2, 1), True), ((1, 2, 2, 0), False)):
        inputs = tuple(
            owner.k1.admit_value(owner.Z3, owner.k1.Nat(value)) for value in values
        )
        result = evaluator.evaluate(
            fixture.schnorr_algorithm,
            inputs,
            modules=owner.k1.FIXTURE_MODULE_PREIMAGES,
        )
        if (
            result.outcome is not owner.k1.Outcome.COMPLETED
            or result.completion.value.datum is not expected
        ):
            raise AuditFailure(f"K1 verifier sample differs at {values!r}")

    # The direct path reconstructs the finite table from the pinned target's
    # authored equation.  The cold path below interprets all 81 term cases.
    bits: list[int] = []
    table: dict[tuple[int, int, int, int], bool] = {}
    for values in itertools.product(range(3), repeat=4):
        y, commitment, challenge, response = values
        observed = response == (commitment + challenge * y) % 3
        table[values] = observed
        bits.append(int(observed))
    return hashlib.sha256(bytes(bits)).hexdigest(), table


def _ambiguity_witnesses(table: dict[tuple[int, int, int, int], bool]) -> list[dict[str, Any]]:
    knowledge_runs = []
    knowledge_bad = []
    for y, witness, nonce, challenge in itertools.product(range(3), repeat=4):
        if y != witness:
            continue
        commitment = nonce
        response = (nonce + challenge * witness) % 3
        knowledge_runs.append(table[(y, commitment, challenge, response)])
        knowledge_bad.append(table[(y, commitment, challenge, (response + 1) % 3)])

    statement_runs = []
    statement_bad = []
    for y, challenge in itertools.product(range(3), repeat=2):
        commitment = 0
        response = (challenge * y) % 3
        statement_runs.append(table[(y, commitment, challenge, response)])
        statement_bad.append(table[(y, commitment, challenge, (response + 1) % 3)])

    if not all(knowledge_runs) or any(knowledge_bad):
        raise AuditFailure("knowledge-shaped ambiguity witness failed its controls")
    if not all(statement_runs) or any(statement_bad):
        raise AuditFailure("statement-only ambiguity witness failed its controls")
    return [
        {
            "name": "knowledge-shaped",
            "relation": "rel(y,x) iff y=x in Z3",
            "witness_carrier": "Z3",
            "private_state_carrier": "Z3 nonce",
            "commit": "a:=r",
            "respond": "z:=r+c*x mod 3",
            "accepted_honest_runs": len(knowledge_runs),
            "rejected_plus_one_controls": len(knowledge_bad),
        },
        {
            "name": "statement-only",
            "relation": "rel(y,unit) is always true",
            "witness_carrier": "Unit",
            "private_state_carrier": "Unit",
            "commit": "a:=0",
            "respond": "z:=c*y mod 3",
            "accepted_honest_runs": len(statement_runs),
            "rejected_plus_one_controls": len(statement_bad),
        },
    ]


def _premise_matrix() -> dict[str, Any]:
    cannot = "CannotAnswer"
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
            "current_outcome": cannot,
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
            "current_outcome": cannot,
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
            "current_outcome": cannot,
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
            "current_outcome": cannot,
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
            "current_outcome": cannot,
        },
    }


def _agreement(subject: dict[str, Any], ambiguity: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "aggregate": "CannotAnswer/F2P0-C-EXACT-COUPLING-UNDERDETERMINED",
        "subject": subject,
        "f2_property_gaps": _property_gaps(),
        "contract_route": [
            "RelationDefinition -> RelationInterface -> RelationSemanticModel",
            "RelationInterface -> RelationInstance",
            "Protocol -> ProtocolRelationBinding -> RelationInterface",
            "ProverPlan -> PlanRealizes -> PlanStrategyStep",
            "ProverPlan -> PlanWitnessSurface -> PlanWitnessBinding -> RelationInterface",
        ],
        "premises": _premise_matrix(),
        "ambiguity_witnesses": ambiguity,
        "selection": "neither finite completion is selected or admitted",
    }


def reconstruct() -> dict[str, Any]:
    basis = validate_basis()
    owner = _load("_zkc_f2p0_direct_owner", F1 / "reference_model.py")
    fixture = owner.make_fixture()
    core_result = owner.admit_core(fixture.core_candidate, fixture.environment)
    if core_result.outcome != "Affirmative":
        raise AuditFailure(f"F1 Core no longer admits: {core_result}")
    protocol_result = owner.admit_fresh_protocol(
        core_result.handle, fixture.protocol_candidate, fixture.environment
    )
    if protocol_result.outcome != "Affirmative":
        raise AuditFailure(f"F1 Protocol no longer admits: {protocol_result}")
    core = core_result.handle.core
    decision_ordinals = [
        ordinal
        for ordinal, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is owner.ProverMessageEffect
    ]
    if decision_ordinals != [0, 2]:
        raise AuditFailure(f"Prover decision sites drifted: {decision_ordinals!r}")
    if (
        len(core.public_bindings) != 1
        or core.public_bindings[0].binding_class is not owner.BindingClass.STATEMENT
        or core.public_bindings[0].value != owner.PublicInputRef(0)
    ):
        raise AuditFailure("F1 Statement binding drifted")
    truth_digest, table = _evaluate_truth_table(owner, fixture)
    ambiguity = _ambiguity_witnesses(table)
    subject = {
        "core_digest": core_result.handle.core_id.digest.hex(),
        "protocol_digest": protocol_result.handle.protocol_id.digest.hex(),
        "statement_binding": 0,
        "decision_ordinals": decision_ordinals,
        "verifier_equation": "z=(a+c*y) mod 3",
        "verifier_truth_table_sha256": truth_digest,
        "verifier_cases": len(table),
        "view_leaf_count": 329,
    }
    agreement = _agreement(subject, ambiguity)
    return {
        "path": "forward-typed-owner",
        "basis": basis,
        "agreement": agreement,
        "agreement_sha256": _canonical_digest(agreement),
    }
