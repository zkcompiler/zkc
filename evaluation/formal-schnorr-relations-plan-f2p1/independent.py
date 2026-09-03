#!/usr/bin/env python3
"""Cold dictionary reconstruction for the F2-P1 candidate bundle."""

from __future__ import annotations

import copy
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
SOURCE_PINS = HERE / "source-pins.json"
F1 = ROOT / "evaluation/formal-source-target-core-f1r1b"

CANDIDATE_REGIME = "zkc.f2p1.finite-additive-schnorr-candidate.v0"
AGGREGATE = "F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE"
INITIAL_CLAIM_CODE = "F2P1-C-INITIAL-CLAIM-ABSENT"


class IndependentFailure(RuntimeError):
    pass


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise IndependentFailure(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IndependentFailure(f"cannot decode {path}") from error


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical(value)).hexdigest()


def _id(kind: str, body: Any) -> str:
    value = {"regime": CANDIDATE_REGIME, "kind": kind, "body": body}
    return f"candidatev0:{kind}:{_digest(value)}"


def _source_basis() -> dict[str, int]:
    ledger = _json(SOURCE_PINS)
    if (
        set(ledger) != {"format", "cutoff", "question", "sources"}
        or ledger["format"]
        != "zkc.formal-schnorr-relations-plan-f2p1.source-pins.v0"
    ):
        raise IndependentFailure("cold source ledger has another shape")
    cited_ranges = 0
    cited_anchors = 0
    seen: set[str] = set()
    for source in ledger["sources"]:
        path = ROOT.joinpath(*source["path"].split("/"))
        if source["path"] in seen:
            raise IndependentFailure("cold source ledger repeats a path")
        seen.add(source["path"])
        if hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
            raise IndependentFailure(f"cold source pin drifted: {source['path']}")
        lines = path.read_text(encoding="utf-8").splitlines()
        for cited in source.get("ranges", []):
            cited_ranges += 1
            excerpt = lines[cited["start"] - 1 : cited["end"]]
            if len(excerpt) != cited["end"] - cited["start"] + 1:
                raise IndependentFailure(f"cold range is incomplete: {cited['id']}")
            text = "\n".join(excerpt)
            for anchor in cited["anchors"]:
                cited_anchors += 1
                if anchor not in text:
                    raise IndependentFailure(
                        f"cold source anchor is absent: {cited['id']} / {anchor}"
                    )
    return {
        "source_files": len(ledger["sources"]),
        "ranges": cited_ranges,
        "anchors": cited_anchors,
    }


def _type_token(k1: ModuleType, value_type: object) -> str:
    encoded = k1.encode_datum(k1.value_type_datum(value_type))
    return "k1-value-type-v0:" + hashlib.sha256(encoded).hexdigest()


def _declaration(module: str, kind: str, ordinal: int) -> dict[str, Any]:
    return {"module": module, "declaration_kind": kind, "local_ordinal": ordinal}


def _role_ref(interface: str, role: str, ordinal: int) -> dict[str, Any]:
    return {"owner_id": interface, "role": role, "canonical_ordinal": ordinal}


def _algorithm(name: str, inputs: list[str], output: str, equation: str) -> dict[str, Any]:
    return {
        "name": name,
        "inputs": inputs,
        "output": output,
        "failures": [],
        "equation": equation,
    }


def _cold_bundle(f1: ModuleType, fixture: object) -> dict[str, Any]:
    z3 = _type_token(f1.k1, f1.r.Z3)
    boolean = _type_token(f1.k1, f1.k1.BOOL)
    protocol_id = fixture.protocol_candidate.asserted_id.carrier()
    core_id = fixture.core_candidate.asserted_id.carrier()
    contract_id = f1.k1.DEFAULT_EVALUATION_CONTRACT.identity.carrier()

    relation_algorithm = _algorithm(
        "F2P1FiniteAdditiveDlogRelation",
        [z3, z3, z3, z3],
        boolean,
        "decide Y = x . G in the additive group (Z/3Z,+), G=1; c and z are phase inputs and are ignored by this predicate",
    )
    commit_algorithm = _algorithm(
        "F2P1FiniteAdditiveSchnorrCommit", [z3], z3, "A := r"
    )
    respond_algorithm = _algorithm(
        "F2P1FiniteAdditiveSchnorrRespond",
        [z3, z3, z3],
        z3,
        "z := r + c*x mod 3",
    )
    relation_algorithm_id = _id("foundation.portable-algorithm", relation_algorithm)
    commit_algorithm_id = _id("foundation.portable-algorithm", commit_algorithm)
    respond_algorithm_id = _id("foundation.portable-algorithm", respond_algorithm)

    language = {
        "payload_type": "record<scalar_modulus:natural,group_order:natural,generator:Z3,group_operation:symbol,scalar_action:symbol>",
        "model_program_type": "finite-additive-dlog-program-v0",
    }
    satisfaction_evaluator = {
        "language_ordinal": 0,
        "model_program": "Y == scalar_action(x,G)",
        "role_vectors": {
            "public_instance": [z3],
            "oracle_statements": [],
            "phase_inputs": [z3, z3],
            "private_witness": [z3],
        },
        "start_algorithm": relation_algorithm_id,
        "resume_algorithms": [],
    }
    module_body = {
        "name": "f2p1.finite-additive-schnorr-relations",
        "catalogs": [
            {"kind": "relations.definition-language", "declarations": [language]},
            {
                "kind": "relations.satisfaction-evaluator",
                "declarations": [satisfaction_evaluator],
            },
        ],
    }
    module_id = _id("foundation.semantic-module", module_body)
    algebra = {
        "scalar_carrier": "Z/3Z",
        "group_carrier": "Z/3Z",
        "scalar_modulus": 3,
        "group_order": 3,
        "group_operation": "(u + v) mod 3",
        "scalar_action": "s . g = (s*g) mod 3 by repeated addition",
        "generator": 1,
        "carrier_identification": "the fixture uses the same Z3 carrier for scalars and additive-group elements",
        "relation": "Y = x . G",
    }
    definition_body = {
        "used_modules": [module_id],
        "language": _declaration(module_id, "relations.definition-language", 0),
        "payload": algebra,
    }
    definition_id = _id("relations.definition", definition_body)
    value_decl = {"value_type": z3}
    interface_body = {
        "used_modules": [],
        "definition_id": definition_id,
        "public_instance": [value_decl],
        "private_witness": [value_decl],
        "oracle_statements": [],
        "phase_inputs": [value_decl, value_decl],
    }
    interface_id = _id("relations.interface", interface_body)
    model_body = {
        "used_modules": [module_id],
        "definition_id": definition_id,
        "interface_id": interface_id,
        "evaluator": _declaration(
            module_id, "relations.satisfaction-evaluator", 0
        ),
        "assumptions": [],
    }
    model_id = _id("relations.semantic-model", model_body)
    question_id = _id(
        "relations.definition-model-question",
        {"definition_id": definition_id, "semantic_model_id": model_id},
    )

    instance_bodies: list[dict[str, Any]] = []
    for y, c, z in itertools.product(range(3), repeat=3):
        instance_bodies.append(
            {
                "used_modules": [],
                "interface_id": interface_id,
                "public_values": [
                    {
                        "ref": _role_ref(interface_id, "PublicInstance", 0),
                        "value_type": z3,
                        "value": y,
                    }
                ],
                "oracle_public_bindings": [],
                "phase_values": [
                    {
                        "ref": _role_ref(interface_id, "PhaseInput", 0),
                        "value_type": z3,
                        "value": c,
                    },
                    {
                        "ref": _role_ref(interface_id, "PhaseInput", 1),
                        "value_type": z3,
                        "value": z,
                    },
                ],
            }
        )
    instance_ids = [_id("relations.instance", body) for body in instance_bodies]

    protocol_binding = {
        "used_modules": [],
        "protocol_id": protocol_id,
        "relation_interfaces": [interface_id],
        "statement_edges": [
            {
                "source": {
                    "ref": _role_ref(interface_id, "PublicInstance", 0),
                    "selector": "Whole",
                },
                "target": {"binding": 0, "selector": "Whole"},
            }
        ],
        "phase_edges": [
            {
                "source": {
                    "ref": _role_ref(interface_id, "PhaseInput", 0),
                    "selector": "Whole",
                },
                "target": {
                    "case": "ChallengeValue",
                    "challenge": 0,
                    "selector": "Whole",
                },
            },
            {
                "source": {
                    "ref": _role_ref(interface_id, "PhaseInput", 1),
                    "selector": "Whole",
                },
                "target": {
                    "case": "PublicOccurrenceOutput",
                    "occurrence": 2,
                    "output_ordinal": 0,
                    "selector": "Whole",
                },
            },
        ],
        "oracle_edges": [],
        "claim_meanings": [],
        "reduction_meanings": [],
        "commitment_groundings": [],
    }

    plan_body = {
        "protocol_id": protocol_id,
        "private_material": [
            {"key": "x", "kind": "WitnessIngress", "value_type": z3}
        ],
        "randomness_requirements": [
            {"value_type": z3, "first_available_at": 0}
        ],
        "persistent_state": [
            {
                "value_type": z3,
                "initial": {"case": "Constant", "value_type": z3, "value": 0},
            }
        ],
        "decision_recipes": [
            {
                "decision": 0,
                "recipe": {
                    "nodes": [
                        {
                            "algorithm": commit_algorithm_id,
                            "evaluation": contract_id,
                            "inputs": [{"case": "PrivateRandomness", "ref": 0}],
                            "output_type": z3,
                        }
                    ],
                    "move": {
                        "case": "MessageValue",
                        "value": {"case": "NodeOutput", "ref": 0},
                    },
                    "state_after": [
                        {
                            "slot": 0,
                            "binding": {
                                "case": "ReplaceState",
                                "value": {"case": "NodeOutput", "ref": 0},
                            },
                        }
                    ],
                },
            },
            {
                "decision": 2,
                "recipe": {
                    "nodes": [
                        {
                            "algorithm": respond_algorithm_id,
                            "evaluation": contract_id,
                            "inputs": [
                                {"case": "StateBefore", "ref": 0},
                                {
                                    "case": "PlanRead",
                                    "coordinate": {
                                        "case": "ObservedChallenge",
                                        "occurrence": 1,
                                    },
                                },
                                {"case": "PrivateMaterial", "ref": 0},
                            ],
                            "output_type": z3,
                        }
                    ],
                    "move": {
                        "case": "MessageValue",
                        "value": {"case": "NodeOutput", "ref": 0},
                    },
                    "state_after": [
                        {"slot": 0, "binding": {"case": "KeepState"}}
                    ],
                },
            },
        ],
        "derived_witness_exports": [],
        "accepted_terminal_recipes": [],
    }
    plan_id = _id("pir.prover-plan", plan_body)
    surface_body = {
        "protocol_id": protocol_id,
        "entries": [
            {
                "key": "x",
                "entry": {
                    "role": "WitnessIngress",
                    "value_type": z3,
                    "occurrence_class": "SuppliedForGeneration",
                },
            }
        ],
    }
    surface_id = _id("pir.plan-witness-surface", surface_body)
    witness_binding = {
        "used_modules": [],
        "plan_witness_surface_id": surface_id,
        "relation_interface_id": interface_id,
        "witness_edges": [
            {
                "source": {
                    "ref": _role_ref(interface_id, "PrivateWitness", 0),
                    "selector": "Whole",
                },
                "target": {"ref": "x", "selector": "Whole"},
            }
        ],
    }
    identities = {
        "relation_evaluator_algorithm": relation_algorithm_id,
        "commit_algorithm": commit_algorithm_id,
        "respond_algorithm": respond_algorithm_id,
        "semantic_module": module_id,
        "relation_definition": definition_id,
        "relation_interface": interface_id,
        "semantic_model": model_id,
        "definition_model_question": question_id,
        "representative_instance": instance_ids[16],
        "instance_family": _id(
            "relations.instance-family", {"instance_ids": instance_ids}
        ),
        "protocol_binding": _id("relations.protocol-binding", protocol_binding),
        "prover_plan": plan_id,
        "plan_witness_surface": surface_id,
        "plan_witness_binding": _id(
            "relations.plan-witness-binding", witness_binding
        ),
    }
    identities["candidate_bundle"] = _id(
        "evaluation.f2p1-candidate-bundle", identities
    )
    bodies = {
        "semantic_module": module_body,
        "relation_definition": definition_body,
        "relation_interface": interface_body,
        "semantic_model": model_body,
        "relation_instances": instance_bodies,
        "protocol_binding": protocol_binding,
        "prover_plan": plan_body,
        "plan_witness_surface": surface_body,
        "plan_witness_binding": witness_binding,
    }
    return {
        "protocol_id": protocol_id,
        "core_id": core_id,
        "z3": z3,
        "boolean": boolean,
        "contract_id": contract_id,
        "algebra": algebra,
        "bodies": bodies,
        "identities": identities,
        "algorithm_bodies": {
            relation_algorithm_id: relation_algorithm,
            commit_algorithm_id: commit_algorithm,
            respond_algorithm_id: respond_algorithm,
        },
    }


def _validate_cold_bundle(bundle: dict[str, Any], core: object) -> None:
    bodies = bundle["bodies"]
    ids = bundle["identities"]
    if _id("foundation.semantic-module", bodies["semantic_module"]) != ids["semantic_module"]:
        raise IndependentFailure("cold semantic-module identity differs")
    if _id("relations.definition", bodies["relation_definition"]) != ids["relation_definition"]:
        raise IndependentFailure("cold relation-definition identity differs")
    if _id("relations.interface", bodies["relation_interface"]) != ids["relation_interface"]:
        raise IndependentFailure("cold relation-Interface identity differs")
    if _id("relations.semantic-model", bodies["semantic_model"]) != ids["semantic_model"]:
        raise IndependentFailure("cold semantic-model identity differs")
    if _id("relations.protocol-binding", bodies["protocol_binding"]) != ids["protocol_binding"]:
        raise IndependentFailure("cold Protocol-binding identity differs")
    if _id("pir.prover-plan", bodies["prover_plan"]) != ids["prover_plan"]:
        raise IndependentFailure("cold Plan identity differs")
    if _id("pir.plan-witness-surface", bodies["plan_witness_surface"]) != ids["plan_witness_surface"]:
        raise IndependentFailure("cold witness-surface identity differs")
    if _id("relations.plan-witness-binding", bodies["plan_witness_binding"]) != ids["plan_witness_binding"]:
        raise IndependentFailure("cold witness-binding identity differs")

    interface = bodies["relation_interface"]
    roles = (
        interface["public_instance"],
        interface["private_witness"],
        interface["oracle_statements"],
        interface["phase_inputs"],
    )
    if tuple(len(items) for items in roles) != (1, 1, 0, 2):
        raise IndependentFailure("cold four-role Interface census differs")
    if any(
        item["value_type"] != bundle["z3"]
        for items in (roles[0], roles[1], roles[3])
        for item in items
    ):
        raise IndependentFailure("cold Interface type differs")
    if len(bodies["relation_instances"]) != 27 or len(
        {_id("relations.instance", value) for value in bodies["relation_instances"]}
    ) != 27:
        raise IndependentFailure("cold relation-instance family differs")
    if len(core.claims) != 0 or bodies["protocol_binding"]["claim_meanings"] != []:
        raise IndependentFailure("cold claim-free binding differs")
    if [item["decision"] for item in bodies["prover_plan"]["decision_recipes"]] != [0, 2]:
        raise IndependentFailure("cold Plan decision coverage differs")
    if bodies["plan_witness_surface"]["entries"][0]["entry"] != {
        "role": "WitnessIngress",
        "value_type": bundle["z3"],
        "occurrence_class": "SuppliedForGeneration",
    }:
        raise IndependentFailure("cold witness extraction differs")
    edge = bodies["plan_witness_binding"]["witness_edges"][0]
    if (
        edge["source"]["ref"]["role"] != "PrivateWitness"
        or edge["target"] != {"ref": "x", "selector": "Whole"}
    ):
        raise IndependentFailure("cold witness binding differs")

    for y, x, c, z in itertools.product(range(3), repeat=4):
        from_definition = y == (x * bundle["algebra"]["generator"]) % 3
        from_model = y == x
        if from_definition != from_model:
            raise IndependentFailure("cold definition/model table differs")


def _cold_honest_runs(f1: ModuleType, fixture: object, bundle: dict[str, Any]) -> dict[str, int]:
    accepted = 0
    rejected = 0
    valid_pairs = 0
    for statement, witness in itertools.product(range(3), repeat=2):
        if statement != witness:
            continue
        valid_pairs += 1
        for nonce, challenge in itertools.product(range(3), repeat=2):
            commitment = nonce
            response = (nonce + challenge * witness) % 3
            good = f1.interpret_term(
                fixture.schnorr_algorithm.term,
                (statement, commitment, challenge, response),
            )
            bad = f1.interpret_term(
                fixture.schnorr_algorithm.term,
                (statement, commitment, challenge, (response + 1) % 3),
            )
            if good is not True or bad is not False:
                raise IndependentFailure("cold honest-run or plus-one control differs")
            accepted += 1
            rejected += 1
    if (valid_pairs, accepted, rejected) != (3, 27, 27):
        raise IndependentFailure("cold honest-run census differs")
    return {
        "valid_statement_witness_pairs": valid_pairs,
        "accepted_honest_runs": accepted,
        "rejected_plus_one_controls": rejected,
    }


def _cold_mutations(bundle: dict[str, Any], core: object) -> dict[str, list[str]]:
    binding = bundle["bodies"]["protocol_binding"]
    wrong_statement = copy.deepcopy(binding)
    wrong_statement["statement_edges"][0]["target"]["binding"] = 1
    if wrong_statement["statement_edges"][0]["target"]["binding"] < len(
        core.public_bindings
    ):
        raise IndependentFailure("cold wrong-statement mutation remained in range")

    swapped = copy.deepcopy(binding)
    swapped["phase_edges"][0]["target"], swapped["phase_edges"][1]["target"] = (
        swapped["phase_edges"][1]["target"],
        swapped["phase_edges"][0]["target"],
    )
    if _id("relations.protocol-binding", swapped) == bundle["identities"]["protocol_binding"]:
        raise IndependentFailure("cold swapped-role mutation retained identity")

    wrong_interface = copy.deepcopy(bundle["bodies"]["relation_interface"])
    wrong_interface["private_witness"] = [{"value_type": bundle["boolean"]}]
    surface_type = bundle["bodies"]["plan_witness_surface"]["entries"][0]["entry"][
        "value_type"
    ]
    if wrong_interface["private_witness"][0]["value_type"] == surface_type:
        raise IndependentFailure("cold wrong-witness mutation retained endpoint type")

    outside = copy.deepcopy(bundle["bodies"]["prover_plan"])
    outside["decision_recipes"][1]["recipe"]["nodes"][0]["inputs"][0] = {
        "case": "PlanRead",
        "coordinate": {"case": "ObservedMessage", "occurrence": 2},
    }
    decision = outside["decision_recipes"][1]["decision"]
    occurrence = outside["decision_recipes"][1]["recipe"]["nodes"][0]["inputs"][0][
        "coordinate"
    ]["occurrence"]
    if occurrence < decision:
        raise IndependentFailure("cold unavailable-read mutation became prior")

    wrong_protocol = copy.deepcopy(binding)
    wrong_protocol["protocol_id"] = bundle["protocol_id"][:-1] + (
        "0" if bundle["protocol_id"][-1] != "0" else "1"
    )
    if wrong_protocol["protocol_id"] == bundle["protocol_id"]:
        raise IndependentFailure("cold wrong-Protocol mutation retained identity")

    return {
        "wrong-statement-edge": ["Refused", "F2P1-R-STATEMENT-EDGE"],
        "swapped-phase-roles": ["Refused", "F2P1-R-PHASE-ROLE-SWAP"],
        "different-witness-type": ["Refused", "F2P1-R-WITNESS-TYPE"],
        "plan-read-outside-guaranteed": ["Negative", "F2P1-N-PLAN-READ"],
        "wrong-protocol-id": ["Refused", "F2P1-R-WRONG-PROTOCOL"],
    }


def _premises(bundle: dict[str, Any]) -> dict[str, dict[str, Any]]:
    ids = bundle["identities"]
    interface = ids["relation_interface"]
    return {
        "relation-predicate": {
            "coordinate": f"RelationSemanticModel({ids['semantic_model']}).evaluator",
            "operand": ids["relation_evaluator_algorithm"],
            "meaning": "Y = x . G in (Z/3Z,+), G=1; phase c and z do not alter relation truth",
        },
        "witness-type": {
            "coordinate": f"RelationInterface({interface}).private_witness[0].value_type + PlanWitnessBinding.witness_edges[0]",
            "operand": bundle["z3"],
            "meaning": "x in Z/3Z supplied by Plan WitnessIngress key x",
        },
        "prover-private-state": {
            "coordinate": f"ProverPlan({ids['prover_plan']}).persistent_state[0] -> PlanExecutionState[0]",
            "operand": bundle["z3"],
            "meaning": "nonce r, initialized to 0 and replaced by the decision-0 randomness value",
        },
        "honest-commit": {
            "coordinate": "ProverPlan.decision_recipes[0].nodes[0] -> PlanStrategyStep(decision 0)",
            "operand": ids["commit_algorithm"],
            "meaning": "A := r",
        },
        "honest-respond": {
            "coordinate": "ProverPlan.decision_recipes[2].nodes[0] -> PlanStrategyStep(decision 2)",
            "operand": ids["respond_algorithm"],
            "meaning": "z := r + c*x mod 3",
        },
    }


def reconstruct() -> dict[str, Any]:
    basis = _source_basis()
    f1 = _load("_zkc_f2p1_cold_f1", F1 / "independent.py")
    fixture = f1.r.make_fixture()
    expected = _json(F1 / "expected-identities.json")
    core_body = f1.core_profiled_body(
        fixture.core_candidate.core, fixture.environment.profile_id
    )
    protocol_body = f1.protocol_profiled_body(
        fixture.core_candidate.asserted_id, fixture.environment.profile_id
    )
    if "sha256:" + hashlib.sha256(core_body).hexdigest() != expected["core_body_sha256"]:
        raise IndependentFailure("cold F1 Core body differs")
    if "sha256:" + hashlib.sha256(protocol_body).hexdigest() != expected["protocol_body_sha256"]:
        raise IndependentFailure("cold F1 Protocol body differs")
    core = fixture.core_candidate.core
    decisions = [
        index
        for index, item in enumerate(core.occurrences)
        if type(item.effect).__name__ == "ProverMessageEffect"
    ]
    if (
        decisions != [0, 2]
        or len(core.public_bindings) != 1
        or core.public_bindings[0].binding_class.name != "STATEMENT"
        or len(core.claims) != 0
    ):
        raise IndependentFailure("cold F1 role or claim census differs")

    bundle = _cold_bundle(f1, fixture)
    _validate_cold_bundle(bundle, core)
    honest = _cold_honest_runs(f1, fixture, bundle)
    mutations = _cold_mutations(bundle, core)
    blocker = {
        "name": "initial-claim-meaning",
        "outcome": "CannotAnswer",
        "code": INITIAL_CLAIM_CODE,
        "owner_contract": "docs-next/relations/relation-model.md Section 7.3 lines 1856-1860",
        "subject_evidence": "evaluation/formal-source-target-core-f1r1b/reference_model.py line 794: claims=()",
        "reason": "ClaimMeaningBinding requires a K2 ClaimRef; inventing InitialClaim(BindingRef(0)) would create claim flow not owned by the admitted Protocol and rotate its identity",
    }
    agreement = {
        "aggregate": f"CannotAnswer/{AGGREGATE}",
        "subject": {
            "core_id": bundle["core_id"],
            "protocol_id": bundle["protocol_id"],
            "statement_binding": 0,
            "challenge_occurrence": 1,
            "response_occurrence": 2,
            "claim_count": len(core.claims),
            "verifier_equation": "z = A + cY mod 3",
        },
        "algebra": bundle["algebra"],
        "role_labels": {
            "public_instance[0]": "Y",
            "private_witness[0]": "x",
            "oracle_statements": "empty",
            "phase_inputs[0]": "c",
            "phase_inputs[1]": "z",
        },
        "bodies": bundle["bodies"],
        "identities": bundle["identities"],
        "premises": _premises(bundle),
        "plan_realizes": {
            "plan_id": bundle["identities"]["prover_plan"],
            "protocol_id": bundle["protocol_id"],
            "decision_recipes": decisions,
            "guaranteed_reads": [
                {
                    "decision": 2,
                    "coordinate": "ObservedChallenge(OccurrenceRef(1))",
                }
            ],
            "state_slots": [0],
        },
        "blockers": [blocker],
        "mutations": mutations,
        "measurements": {
            "definition_model_rows": 81,
            "relation_instances": 27,
            "statement_edges": 1,
            "phase_edges": 2,
            "claim_meanings": 0,
            **honest,
            "candidate_identities": len(bundle["identities"]),
        },
    }
    return {
        "path": "reverse-cold-dictionary",
        "basis": basis,
        "agreement": agreement,
        "agreement_sha256": _digest(agreement),
    }
