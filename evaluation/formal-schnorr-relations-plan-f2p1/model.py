#!/usr/bin/env python3
"""Typed candidate construction for the F2-P1 Schnorr Relations--Plan lane."""

from __future__ import annotations

import copy
from dataclasses import dataclass
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
EVALUATION_CONTRACT_KIND = "foundation.evaluation-contract"
AGGREGATE = "F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE"
INITIAL_CLAIM_CODE = "F2P1-C-INITIAL-CLAIM-ABSENT"


class CandidateFailure(RuntimeError):
    """A stable qualified outcome from the bounded candidate checker."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise CandidateFailure("CheckerFailure", "F2P1-X-LOAD", f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CandidateFailure(
            "CheckerFailure", "F2P1-X-JSON", f"cannot read {path}"
        ) from error


def _sha_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha_value(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _candidate_id(kind: str, body: Any) -> str:
    digest = _sha_value({"regime": CANDIDATE_REGIME, "kind": kind, "body": body})
    return f"candidatev0:{kind}:{digest}"


def _require(condition: bool, outcome: str, code: str, detail: str) -> None:
    if not condition:
        raise CandidateFailure(outcome, code, detail)


def validate_source_pins() -> dict[str, int]:
    ledger = _read_json(SOURCE_PINS)
    _require(
        ledger.get("format")
        == "zkc.formal-schnorr-relations-plan-f2p1.source-pins.v0",
        "Malformed",
        "F2P1-M-SOURCE-PINS",
        "source-pin format differs",
    )
    ranges = 0
    anchors = 0
    for source in ledger.get("sources", []):
        path = ROOT / source["path"]
        _require(
            _sha_file(path) == source["sha256"],
            "Refused",
            "F2P1-R-SOURCE-DRIFT",
            f"pinned source drifted: {source['path']}",
        )
        lines = path.read_text(encoding="utf-8").splitlines()
        for cited in source.get("ranges", []):
            ranges += 1
            _require(
                1 <= cited["start"] <= cited["end"] <= len(lines),
                "Malformed",
                "F2P1-M-SOURCE-RANGE",
                f"source range is invalid: {cited['id']}",
            )
            excerpt = "\n".join(lines[cited["start"] - 1 : cited["end"]])
            for anchor in cited["anchors"]:
                anchors += 1
                _require(
                    anchor in excerpt,
                    "Refused",
                    "F2P1-R-SOURCE-ANCHOR",
                    f"source anchor is absent: {cited['id']} / {anchor}",
                )
    return {"source_files": len(ledger["sources"]), "ranges": ranges, "anchors": anchors}


def _type_token(k1: ModuleType, value_type: object) -> str:
    body = k1.encode_datum(k1.value_type_datum(value_type))
    return "k1-value-type-v0:" + hashlib.sha256(body).hexdigest()


def _ref(module_id: str, kind: str, ordinal: int) -> dict[str, Any]:
    return {"module": module_id, "declaration_kind": kind, "local_ordinal": ordinal}


def _relation_ref(interface_id: str, role: str, ordinal: int) -> dict[str, Any]:
    return {"owner_id": interface_id, "role": role, "canonical_ordinal": ordinal}


@dataclass(frozen=True)
class RelationDefinitionCandidate:
    used_modules: tuple[str, ...]
    language: dict[str, Any]
    payload: dict[str, Any]

    def body(self) -> dict[str, Any]:
        return {
            "used_modules": list(self.used_modules),
            "language": self.language,
            "payload": self.payload,
        }


@dataclass(frozen=True)
class RelationInterfaceCandidate:
    used_modules: tuple[str, ...]
    definition_id: str
    public_instance: tuple[dict[str, str], ...]
    private_witness: tuple[dict[str, str], ...]
    oracle_statements: tuple[dict[str, str], ...]
    phase_inputs: tuple[dict[str, str], ...]

    def body(self) -> dict[str, Any]:
        return {
            "used_modules": list(self.used_modules),
            "definition_id": self.definition_id,
            "public_instance": list(self.public_instance),
            "private_witness": list(self.private_witness),
            "oracle_statements": list(self.oracle_statements),
            "phase_inputs": list(self.phase_inputs),
        }


@dataclass(frozen=True)
class RelationSemanticModelCandidate:
    used_modules: tuple[str, ...]
    definition_id: str
    interface_id: str
    evaluator: dict[str, Any]
    assumptions: tuple[dict[str, Any], ...]

    def body(self) -> dict[str, Any]:
        return {
            "used_modules": list(self.used_modules),
            "definition_id": self.definition_id,
            "interface_id": self.interface_id,
            "evaluator": self.evaluator,
            "assumptions": list(self.assumptions),
        }


@dataclass(frozen=True)
class RelationInstanceCandidate:
    used_modules: tuple[str, ...]
    interface_id: str
    public_values: tuple[dict[str, Any], ...]
    oracle_public_bindings: tuple[dict[str, Any], ...]
    phase_values: tuple[dict[str, Any], ...]

    def body(self) -> dict[str, Any]:
        return {
            "used_modules": list(self.used_modules),
            "interface_id": self.interface_id,
            "public_values": list(self.public_values),
            "oracle_public_bindings": list(self.oracle_public_bindings),
            "phase_values": list(self.phase_values),
        }


@dataclass(frozen=True)
class CandidateArtifacts:
    protocol_id: str
    core_id: str
    z3_type: str
    bool_type: str
    evaluation_contract_id: str
    algorithm_bodies: dict[str, dict[str, Any]]
    module_body: dict[str, Any]
    definition: RelationDefinitionCandidate
    interface: RelationInterfaceCandidate
    model: RelationSemanticModelCandidate
    instances: tuple[RelationInstanceCandidate, ...]
    protocol_binding: dict[str, Any]
    plan: dict[str, Any]
    witness_surface: dict[str, Any]
    witness_binding: dict[str, Any]
    identities: dict[str, str]


def _algorithm_body(
    name: str, inputs: list[str], output: str, equation: str
) -> dict[str, Any]:
    return {
        "name": name,
        "inputs": inputs,
        "output": output,
        "failures": [],
        "equation": equation,
    }


def _instance(interface_id: str, z3_type: str, y: int, c: int, z: int) -> RelationInstanceCandidate:
    return RelationInstanceCandidate(
        (),
        interface_id,
        (
            {
                "ref": _relation_ref(interface_id, "PublicInstance", 0),
                "value_type": z3_type,
                "value": y,
            },
        ),
        (),
        (
            {
                "ref": _relation_ref(interface_id, "PhaseInput", 0),
                "value_type": z3_type,
                "value": c,
            },
            {
                "ref": _relation_ref(interface_id, "PhaseInput", 1),
                "value_type": z3_type,
                "value": z,
            },
        ),
    )


def _build_artifacts(f1: ModuleType, fixture: object) -> CandidateArtifacts:
    z3_type = _type_token(f1.k1, f1.Z3)
    bool_type = _type_token(f1.k1, f1.k1.BOOL)
    protocol_id = fixture.protocol_candidate.asserted_id.carrier()
    core_id = fixture.core_candidate.asserted_id.carrier()
    evaluation_contract_id = f1.k1.DEFAULT_EVALUATION_CONTRACT.identity.carrier()

    relation_evaluator_body = _algorithm_body(
        "F2P1FiniteAdditiveDlogRelation",
        [z3_type, z3_type, z3_type, z3_type],
        bool_type,
        "decide Y = x . G in the additive group (Z/3Z,+), G=1; c and z are phase inputs and are ignored by this predicate",
    )
    commit_body = _algorithm_body(
        "F2P1FiniteAdditiveSchnorrCommit", [z3_type], z3_type, "A := r"
    )
    respond_body = _algorithm_body(
        "F2P1FiniteAdditiveSchnorrRespond",
        [z3_type, z3_type, z3_type],
        z3_type,
        "z := r + c*x mod 3",
    )
    relation_evaluator_id = _candidate_id(
        "foundation.portable-algorithm", relation_evaluator_body
    )
    commit_id = _candidate_id("foundation.portable-algorithm", commit_body)
    respond_id = _candidate_id("foundation.portable-algorithm", respond_body)
    algorithm_bodies = {
        relation_evaluator_id: relation_evaluator_body,
        commit_id: commit_body,
        respond_id: respond_body,
    }

    language_body = {
        "payload_type": "record<scalar_modulus:natural,group_order:natural,generator:Z3,group_operation:symbol,scalar_action:symbol>",
        "model_program_type": "finite-additive-dlog-program-v0",
    }
    evaluator_contract_body = {
        "language_ordinal": 0,
        "model_program": "Y == scalar_action(x,G)",
        "role_vectors": {
            "public_instance": [z3_type],
            "oracle_statements": [],
            "phase_inputs": [z3_type, z3_type],
            "private_witness": [z3_type],
        },
        "start_algorithm": relation_evaluator_id,
        "resume_algorithms": [],
    }
    module_body = {
        "name": "f2p1.finite-additive-schnorr-relations",
        "catalogs": [
            {"kind": "relations.definition-language", "declarations": [language_body]},
            {
                "kind": "relations.satisfaction-evaluator",
                "declarations": [evaluator_contract_body],
            },
        ],
    }
    module_id = _candidate_id("foundation.semantic-module", module_body)

    payload = {
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
    definition = RelationDefinitionCandidate(
        (module_id,), _ref(module_id, "relations.definition-language", 0), payload
    )
    definition_id = _candidate_id("relations.definition", definition.body())

    value_decl = {"value_type": z3_type}
    interface = RelationInterfaceCandidate(
        (),
        definition_id,
        (value_decl,),
        (value_decl,),
        (),
        (value_decl, value_decl),
    )
    interface_id = _candidate_id("relations.interface", interface.body())
    model = RelationSemanticModelCandidate(
        (module_id,),
        definition_id,
        interface_id,
        _ref(module_id, "relations.satisfaction-evaluator", 0),
        (),
    )
    model_id = _candidate_id("relations.semantic-model", model.body())
    question_body = {"definition_id": definition_id, "semantic_model_id": model_id}
    question_id = _candidate_id("relations.definition-model-question", question_body)

    instances = tuple(
        _instance(interface_id, z3_type, y, c, z)
        for y, c, z in itertools.product(range(3), repeat=3)
    )
    instance_ids = tuple(
        _candidate_id("relations.instance", item.body()) for item in instances
    )
    representative_index = 1 * 9 + 2 * 3 + 1

    protocol_binding = {
        "used_modules": [],
        "protocol_id": protocol_id,
        "relation_interfaces": [interface_id],
        "statement_edges": [
            {
                "source": {
                    "ref": _relation_ref(interface_id, "PublicInstance", 0),
                    "selector": "Whole",
                },
                "target": {"binding": 0, "selector": "Whole"},
            }
        ],
        "phase_edges": [
            {
                "source": {
                    "ref": _relation_ref(interface_id, "PhaseInput", 0),
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
                    "ref": _relation_ref(interface_id, "PhaseInput", 1),
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

    commit_node = {
        "algorithm": commit_id,
        "evaluation": evaluation_contract_id,
        "inputs": [{"case": "PrivateRandomness", "ref": 0}],
        "output_type": z3_type,
    }
    respond_node = {
        "algorithm": respond_id,
        "evaluation": evaluation_contract_id,
        "inputs": [
            {"case": "StateBefore", "ref": 0},
            {
                "case": "PlanRead",
                "coordinate": {"case": "ObservedChallenge", "occurrence": 1},
            },
            {"case": "PrivateMaterial", "ref": 0},
        ],
        "output_type": z3_type,
    }
    plan = {
        "protocol_id": protocol_id,
        "private_material": [
            {"key": "x", "kind": "WitnessIngress", "value_type": z3_type}
        ],
        "randomness_requirements": [
            {"value_type": z3_type, "first_available_at": 0}
        ],
        "persistent_state": [
            {
                "value_type": z3_type,
                "initial": {
                    "case": "Constant",
                    "value_type": z3_type,
                    "value": 0,
                },
            }
        ],
        "decision_recipes": [
            {
                "decision": 0,
                "recipe": {
                    "nodes": [commit_node],
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
                    "nodes": [respond_node],
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
    plan_id = _candidate_id("pir.prover-plan", plan)
    witness_surface = {
        "protocol_id": protocol_id,
        "entries": [
            {
                "key": "x",
                "entry": {
                    "role": "WitnessIngress",
                    "value_type": z3_type,
                    "occurrence_class": "SuppliedForGeneration",
                },
            }
        ],
    }
    surface_id = _candidate_id("pir.plan-witness-surface", witness_surface)
    witness_binding = {
        "used_modules": [],
        "plan_witness_surface_id": surface_id,
        "relation_interface_id": interface_id,
        "witness_edges": [
            {
                "source": {
                    "ref": _relation_ref(interface_id, "PrivateWitness", 0),
                    "selector": "Whole",
                },
                "target": {"ref": "x", "selector": "Whole"},
            }
        ],
    }

    identities = {
        "relation_evaluator_algorithm": relation_evaluator_id,
        "commit_algorithm": commit_id,
        "respond_algorithm": respond_id,
        "semantic_module": module_id,
        "relation_definition": definition_id,
        "relation_interface": interface_id,
        "semantic_model": model_id,
        "definition_model_question": question_id,
        "representative_instance": instance_ids[representative_index],
        "instance_family": _candidate_id(
            "relations.instance-family", {"instance_ids": list(instance_ids)}
        ),
        "protocol_binding": _candidate_id(
            "relations.protocol-binding", protocol_binding
        ),
        "prover_plan": plan_id,
        "plan_witness_surface": surface_id,
        "plan_witness_binding": _candidate_id(
            "relations.plan-witness-binding", witness_binding
        ),
    }
    identities["candidate_bundle"] = _candidate_id(
        "evaluation.f2p1-candidate-bundle", identities
    )
    return CandidateArtifacts(
        protocol_id,
        core_id,
        z3_type,
        bool_type,
        evaluation_contract_id,
        algorithm_bodies,
        module_body,
        definition,
        interface,
        model,
        instances,
        protocol_binding,
        plan,
        witness_surface,
        witness_binding,
        identities,
    )


def _admit_relation_candidates(artifacts: CandidateArtifacts) -> dict[str, int]:
    payload = artifacts.definition.payload
    _require(
        artifacts.definition.used_modules
        == (artifacts.identities["semantic_module"],)
        and artifacts.definition.language
        == _ref(
            artifacts.identities["semantic_module"],
            "relations.definition-language",
            0,
        )
        and payload
        == {
            "scalar_carrier": "Z/3Z",
            "group_carrier": "Z/3Z",
            "scalar_modulus": 3,
            "group_order": 3,
            "group_operation": "(u + v) mod 3",
            "scalar_action": "s . g = (s*g) mod 3 by repeated addition",
            "generator": 1,
            "carrier_identification": "the fixture uses the same Z3 carrier for scalars and additive-group elements",
            "relation": "Y = x . G",
        },
        "Refused",
        "F2P1-R-RELATION-DEFINITION",
        "relation definition is not the exact finite additive candidate",
    )
    interface = artifacts.interface
    _require(
        interface.definition_id == artifacts.identities["relation_definition"]
        and interface.used_modules == ()
        and tuple(item["value_type"] for item in interface.public_instance)
        == (artifacts.z3_type,)
        and tuple(item["value_type"] for item in interface.private_witness)
        == (artifacts.z3_type,)
        and interface.oracle_statements == ()
        and tuple(item["value_type"] for item in interface.phase_inputs)
        == (artifacts.z3_type, artifacts.z3_type),
        "Refused",
        "F2P1-R-RELATION-INTERFACE",
        "the four Interface roles differ from the candidate",
    )
    _require(
        artifacts.model.definition_id == artifacts.identities["relation_definition"]
        and artifacts.model.interface_id == artifacts.identities["relation_interface"]
        and artifacts.model.used_modules
        == (artifacts.identities["semantic_module"],)
        and artifacts.model.evaluator
        == _ref(
            artifacts.identities["semantic_module"],
            "relations.satisfaction-evaluator",
            0,
        )
        and artifacts.model.assumptions == (),
        "Refused",
        "F2P1-R-RELATION-MODEL",
        "semantic model does not close over the exact definition and Interface",
    )

    correspondence_rows = 0
    for y, x, c, z in itertools.product(range(3), repeat=4):
        definition_value = y == (x * payload["generator"]) % payload["group_order"]
        model_value = y == x
        _require(
            definition_value == model_value,
            "CheckerFailure",
            "F2P1-X-DEFINITION-MODEL",
            "finite definition and evaluator disagree",
        )
        correspondence_rows += 1

    seen_instance_ids: set[str] = set()
    for instance in artifacts.instances:
        _require(
            instance.interface_id == artifacts.identities["relation_interface"]
            and instance.used_modules == ()
            and instance.oracle_public_bindings == ()
            and [item["ref"]["canonical_ordinal"] for item in instance.public_values]
            == [0]
            and [item["ref"]["canonical_ordinal"] for item in instance.phase_values]
            == [0, 1]
            and all(
                item["value_type"] == artifacts.z3_type
                and type(item["value"]) is int
                and 0 <= item["value"] < 3
                for item in (*instance.public_values, *instance.phase_values)
            ),
            "Refused",
            "F2P1-R-RELATION-INSTANCE",
            "relation instance is not total and exactly typed",
        )
        seen_instance_ids.add(_candidate_id("relations.instance", instance.body()))
    _require(
        len(artifacts.instances) == 27 and len(seen_instance_ids) == 27,
        "CheckerFailure",
        "F2P1-X-INSTANCE-FAMILY",
        "the finite instance family is incomplete",
    )
    return {"definition_model_rows": correspondence_rows, "relation_instances": 27}


def _check_protocol_binding(
    artifacts: CandidateArtifacts,
    core: object,
    binding: dict[str, Any],
    *,
    exact_candidate: bool,
) -> dict[str, Any]:
    _require(
        binding.get("protocol_id") == artifacts.protocol_id,
        "Refused",
        "F2P1-R-WRONG-PROTOCOL",
        "ProtocolRelationBinding names another Protocol",
    )
    _require(
        binding.get("used_modules") == []
        and binding.get("relation_interfaces")
        == [artifacts.identities["relation_interface"]],
        "Refused",
        "F2P1-R-BINDING-CLOSURE",
        "Protocol binding exact-used closure differs",
    )
    statement_edges = binding.get("statement_edges")
    _require(
        type(statement_edges) is list and len(statement_edges) == 1,
        "Refused",
        "F2P1-R-STATEMENT-EDGE",
        "the relation public role is not bound exactly once",
    )
    statement = statement_edges[0]
    _require(
        statement.get("source", {}).get("ref")
        == _relation_ref(
            artifacts.identities["relation_interface"], "PublicInstance", 0
        )
        and statement.get("source", {}).get("selector") == "Whole"
        and statement.get("target") == {"binding": 0, "selector": "Whole"}
        and len(core.public_bindings) == 1
        and core.public_bindings[0].binding_class.name == "STATEMENT",
        "Refused",
        "F2P1-R-STATEMENT-EDGE",
        "statement edge does not name exact Statement binding zero",
    )
    phase_edges = binding.get("phase_edges")
    _require(
        type(phase_edges) is list
        and len(phase_edges) == 2
        and sorted(
            edge["source"]["ref"]["canonical_ordinal"] for edge in phase_edges
        )
        == [0, 1],
        "Refused",
        "F2P1-R-PHASE-EDGES",
        "phase edges are not total for the candidate Interface",
    )
    for edge in phase_edges:
        ordinal = edge["source"]["ref"]["canonical_ordinal"]
        target = edge["target"]
        formed = (
            target
            == {"case": "ChallengeValue", "challenge": 0, "selector": "Whole"}
            or target
            == {
                "case": "PublicOccurrenceOutput",
                "occurrence": 2,
                "output_ordinal": 0,
                "selector": "Whole",
            }
        )
        _require(
            formed and ordinal in (0, 1),
            "Refused",
            "F2P1-R-PHASE-EDGES",
            "phase edge target is not the F1 challenge or response",
        )
    _require(
        binding.get("oracle_edges") == []
        and binding.get("reduction_meanings") == []
        and binding.get("commitment_groundings") == [],
        "Refused",
        "F2P1-R-BINDING-CLOSURE",
        "unused binding families are not exact empty sequences",
    )
    if binding.get("claim_meanings"):
        _require(
            bool(core.claims),
            "CannotAnswer",
            INITIAL_CLAIM_CODE,
            "Section 7.3 requires a K2 ClaimRef, but the F1-R1B Core has no Claim",
        )
    _require(
        binding.get("claim_meanings") == [],
        "Refused",
        "F2P1-R-CLAIM-CLOSURE",
        "the claim-meaning sequence is not exact for the claim-free Core",
    )
    if exact_candidate:
        _require(
            binding == artifacts.protocol_binding,
            "Refused",
            "F2P1-R-PHASE-ROLE-SWAP",
            "a structurally formed binding is not the exact authored phase-role binding",
        )
    return {
        "statement_edges": 1,
        "phase_edges": 2,
        "claim_meanings": 0,
    }


def _recipe_operand_type(
    artifacts: CandidateArtifacts,
    core: object,
    plan: dict[str, Any],
    operand: dict[str, Any],
    prior_node_types: list[str],
) -> str:
    case = operand.get("case")
    if case == "PrivateMaterial":
        return plan["private_material"][operand["ref"]]["value_type"]
    if case == "PrivateRandomness":
        return plan["randomness_requirements"][operand["ref"]]["value_type"]
    if case == "StateBefore":
        return plan["persistent_state"][operand["ref"]]["value_type"]
    if case == "NodeOutput":
        _require(
            type(operand.get("ref")) is int
            and 0 <= operand["ref"] < len(prior_node_types),
            "Malformed",
            "F2P1-M-PLAN-NODE-ORDER",
            "node output is not earlier in the local recipe",
        )
        return prior_node_types[operand["ref"]]
    if case == "PlanRead":
        coordinate = operand.get("coordinate", {})
        occurrence = coordinate.get("occurrence")
        _require(
            type(occurrence) is int and 0 <= occurrence < len(core.occurrences),
            "Malformed",
            "F2P1-M-PLAN-READ",
            "Plan read occurrence is unformed",
        )
        effect = core.occurrences[occurrence].effect
        coordinate_case = coordinate.get("case")
        if coordinate_case == "ObservedChallenge":
            _require(
                type(effect).__name__ == "ChallengeEffect",
                "KindMismatch",
                "F2P1-K-PLAN-READ",
                "ObservedChallenge names another effect kind",
            )
            return artifacts.z3_type
        if coordinate_case == "ObservedMessage":
            _require(
                type(effect).__name__ == "ProverMessageEffect",
                "KindMismatch",
                "F2P1-K-PLAN-READ",
                "ObservedMessage names another effect kind",
            )
            return artifacts.z3_type
    raise CandidateFailure("Malformed", "F2P1-M-PLAN-OPERAND", "unknown operand")


def _admit_plan(
    artifacts: CandidateArtifacts, core: object, plan: dict[str, Any]
) -> str:
    _require(
        plan.get("protocol_id") == artifacts.protocol_id,
        "Refused",
        "F2P1-R-PLAN-PROTOCOL",
        "ProverPlan names another Protocol",
    )
    _require(
        plan.get("private_material")
        == [{"key": "x", "kind": "WitnessIngress", "value_type": artifacts.z3_type}]
        and plan.get("randomness_requirements")
        == [{"value_type": artifacts.z3_type, "first_available_at": 0}]
        and plan.get("persistent_state")
        == [
            {
                "value_type": artifacts.z3_type,
                "initial": {
                    "case": "Constant",
                    "value_type": artifacts.z3_type,
                    "value": 0,
                },
            }
        ],
        "Refused",
        "F2P1-R-PLAN-PRIVATE-SURFACE",
        "Plan witness, nonce requirement, or nonce state differs",
    )
    _require(
        plan.get("derived_witness_exports") == []
        and plan.get("accepted_terminal_recipes") == [],
        "Refused",
        "F2P1-R-PLAN-CLOSURE",
        "unused Plan output families are not exact empty sequences",
    )
    decisions = plan.get("decision_recipes")
    _require(
        type(decisions) is list
        and len({entry.get("decision") for entry in decisions}) == len(decisions)
        and all(entry.get("decision") in (0, 2) for entry in decisions),
        "Malformed",
        "F2P1-M-PLAN-DECISIONS",
        "Plan decision map has an unformed key",
    )
    for entry in decisions:
        recipe = entry["recipe"]
        prior_types: list[str] = []
        for node in recipe["nodes"]:
            algorithm = artifacts.algorithm_bodies.get(node["algorithm"])
            _require(
                algorithm is not None
                and node["evaluation"] == artifacts.evaluation_contract_id,
                "MissingDependency",
                "F2P1-D-PLAN-ALGORITHM",
                "recipe algorithm or evaluation contract is unavailable",
            )
            input_types = [
                _recipe_operand_type(artifacts, core, plan, operand, prior_types)
                for operand in node["inputs"]
            ]
            _require(
                input_types == algorithm["inputs"]
                and node["output_type"] == algorithm["output"],
                "KindMismatch",
                "F2P1-K-PLAN-ALGORITHM-ABI",
                "recipe node ABI differs",
            )
            prior_types.append(node["output_type"])
        move = recipe["move"]
        _require(
            move.get("case") == "MessageValue"
            and _recipe_operand_type(
                artifacts, core, plan, move["value"], prior_types
            )
            == artifacts.z3_type,
            "KindMismatch",
            "F2P1-K-PLAN-MOVE",
            "decision move is not an exact Z3 MessageValue",
        )
        _require(
            recipe.get("state_after") is not None
            and [item.get("slot") for item in recipe["state_after"]] == [0],
            "Malformed",
            "F2P1-M-PLAN-STATE",
            "decision state map is not total",
        )
        binding = recipe["state_after"][0]["binding"]
        if binding.get("case") == "ReplaceState":
            _require(
                _recipe_operand_type(
                    artifacts, core, plan, binding["value"], prior_types
                )
                == artifacts.z3_type,
                "KindMismatch",
                "F2P1-K-PLAN-STATE",
                "replacement state type differs",
            )
        else:
            _require(
                binding == {"case": "KeepState"},
                "Malformed",
                "F2P1-M-PLAN-STATE",
                "state binding branch differs",
            )
    return _candidate_id("pir.prover-plan", plan)


def _plan_realizes(
    artifacts: CandidateArtifacts, core: object, plan: dict[str, Any]
) -> dict[str, Any]:
    plan_id = _admit_plan(artifacts, core, plan)
    decisions = [
        ordinal
        for ordinal, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect).__name__ == "ProverMessageEffect"
    ]
    recipes = {entry["decision"]: entry["recipe"] for entry in plan["decision_recipes"]}
    _require(
        sorted(recipes) == decisions,
        "Negative",
        "F2P1-N-PLAN-COVERAGE",
        "decision recipes do not cover every and only Prover decisions",
    )
    direct_randomness_sites: list[int] = []
    for decision, recipe in recipes.items():
        for node in recipe["nodes"]:
            for operand in node["inputs"]:
                if operand.get("case") == "PrivateRandomness":
                    direct_randomness_sites.append(decision)
                if operand.get("case") != "PlanRead":
                    continue
                coordinate = operand["coordinate"]
                occurrence = coordinate["occurrence"]
                _require(
                    occurrence < decision,
                    "Negative",
                    "F2P1-N-PLAN-READ",
                    "Plan reads a value outside the guaranteed prior prefix",
                )
        expected_effect = core.occurrences[decision].effect
        _require(
            type(expected_effect).__name__ == "ProverMessageEffect"
            and recipe["move"]["case"] == "MessageValue",
            "Negative",
            "F2P1-N-PLAN-MOVE",
            "Plan move shape differs from the Prover decision",
        )
    _require(
        direct_randomness_sites == [0],
        "Negative",
        "F2P1-N-RANDOMNESS",
        "nonce randomness is not pathwise one-shot at decision zero",
    )
    return {
        "plan_id": plan_id,
        "protocol_id": artifacts.protocol_id,
        "decision_recipes": decisions,
        "guaranteed_reads": [
            {"decision": 2, "coordinate": "ObservedChallenge(OccurrenceRef(1))"}
        ],
        "state_slots": [0],
    }


def _extract_witness_surface(
    artifacts: CandidateArtifacts, plan: dict[str, Any]
) -> dict[str, Any]:
    entries = [
        {
            "key": item["key"],
            "entry": {
                "role": "WitnessIngress",
                "value_type": item["value_type"],
                "occurrence_class": "SuppliedForGeneration",
            },
        }
        for item in plan["private_material"]
        if item["kind"] == "WitnessIngress"
    ]
    surface = {"protocol_id": plan["protocol_id"], "entries": entries}
    _require(
        surface == artifacts.witness_surface,
        "CheckerFailure",
        "F2P1-X-WITNESS-SURFACE",
        "typed witness-surface extraction differs from the candidate",
    )
    return surface


def _check_witness_binding(
    artifacts: CandidateArtifacts,
    surface: dict[str, Any],
    interface_body: dict[str, Any],
    interface_id: str,
    binding: dict[str, Any],
) -> None:
    _require(
        binding.get("plan_witness_surface_id")
        == _candidate_id("pir.plan-witness-surface", surface)
        and binding.get("relation_interface_id") == interface_id
        and binding.get("used_modules") == [],
        "Refused",
        "F2P1-R-WITNESS-BINDING-SUBJECT",
        "PlanWitnessBinding names another subject",
    )
    edges = binding.get("witness_edges")
    _require(
        type(edges) is list and len(edges) == len(interface_body["private_witness"]) == 1,
        "Refused",
        "F2P1-R-WITNESS-BINDING-CLOSURE",
        "witness edge map is not total",
    )
    edge = edges[0]
    entries = {item["key"]: item["entry"] for item in surface["entries"]}
    target = entries.get(edge.get("target", {}).get("ref"))
    source_ordinal = edge.get("source", {}).get("ref", {}).get("canonical_ordinal")
    _require(
        source_ordinal == 0
        and target is not None
        and edge["source"]["selector"] == edge["target"]["selector"] == "Whole"
        and interface_body["private_witness"][0]["value_type"]
        == target["value_type"],
        "Refused",
        "F2P1-R-WITNESS-TYPE",
        "relation witness and Plan witness-surface types differ",
    )


def _evaluate_algorithm(artifacts: CandidateArtifacts, algorithm: str, values: list[int]) -> int:
    if algorithm == artifacts.identities["commit_algorithm"]:
        return values[0]
    if algorithm == artifacts.identities["respond_algorithm"]:
        return (values[0] + values[1] * values[2]) % 3
    raise CandidateFailure(
        "MissingDependency", "F2P1-D-EXECUTION-ALGORITHM", "unknown Plan algorithm"
    )


def _execute_plan(
    artifacts: CandidateArtifacts, x: int, nonce: int, challenge: int
) -> tuple[int, int]:
    recipes = {
        entry["decision"]: entry["recipe"] for entry in artifacts.plan["decision_recipes"]
    }
    state = [0]
    commit = recipes[0]["nodes"][0]
    commitment = _evaluate_algorithm(artifacts, commit["algorithm"], [nonce])
    state[0] = commitment
    respond = recipes[2]["nodes"][0]
    response = _evaluate_algorithm(
        artifacts, respond["algorithm"], [state[0], challenge, x]
    )
    return commitment, response


def _honest_runs(artifacts: CandidateArtifacts) -> dict[str, int]:
    accepted = 0
    rejected = 0
    valid_pairs = 0
    for y, x in itertools.product(range(3), repeat=2):
        if y != (x * artifacts.definition.payload["generator"]) % 3:
            continue
        valid_pairs += 1
        for nonce, challenge in itertools.product(range(3), repeat=2):
            commitment, response = _execute_plan(artifacts, x, nonce, challenge)
            _require(
                response == (commitment + challenge * y) % 3,
                "CheckerFailure",
                "F2P1-X-HONEST-RUN",
                "bound honest Plan failed the F1 verifier equation",
            )
            accepted += 1
            _require(
                (response + 1) % 3 != (commitment + challenge * y) % 3,
                "CheckerFailure",
                "F2P1-X-PLUS-ONE",
                "plus-one response control unexpectedly accepted",
            )
            rejected += 1
    return {
        "valid_statement_witness_pairs": valid_pairs,
        "accepted_honest_runs": accepted,
        "rejected_plus_one_controls": rejected,
    }


def _premise_table(artifacts: CandidateArtifacts) -> dict[str, dict[str, Any]]:
    interface_id = artifacts.identities["relation_interface"]
    return {
        "relation-predicate": {
            "coordinate": f"RelationSemanticModel({artifacts.identities['semantic_model']}).evaluator",
            "operand": artifacts.identities["relation_evaluator_algorithm"],
            "meaning": "Y = x . G in (Z/3Z,+), G=1; phase c and z do not alter relation truth",
        },
        "witness-type": {
            "coordinate": f"RelationInterface({interface_id}).private_witness[0].value_type + PlanWitnessBinding.witness_edges[0]",
            "operand": artifacts.z3_type,
            "meaning": "x in Z/3Z supplied by Plan WitnessIngress key x",
        },
        "prover-private-state": {
            "coordinate": f"ProverPlan({artifacts.identities['prover_plan']}).persistent_state[0] -> PlanExecutionState[0]",
            "operand": artifacts.z3_type,
            "meaning": "nonce r, initialized to 0 and replaced by the decision-0 randomness value",
        },
        "honest-commit": {
            "coordinate": "ProverPlan.decision_recipes[0].nodes[0] -> PlanStrategyStep(decision 0)",
            "operand": artifacts.identities["commit_algorithm"],
            "meaning": "A := r",
        },
        "honest-respond": {
            "coordinate": "ProverPlan.decision_recipes[2].nodes[0] -> PlanStrategyStep(decision 2)",
            "operand": artifacts.identities["respond_algorithm"],
            "meaning": "z := r + c*x mod 3",
        },
    }


def _body_catalog(artifacts: CandidateArtifacts) -> dict[str, Any]:
    return {
        "semantic_module": artifacts.module_body,
        "relation_definition": artifacts.definition.body(),
        "relation_interface": artifacts.interface.body(),
        "semantic_model": artifacts.model.body(),
        "relation_instances": [item.body() for item in artifacts.instances],
        "protocol_binding": artifacts.protocol_binding,
        "prover_plan": artifacts.plan,
        "plan_witness_surface": artifacts.witness_surface,
        "plan_witness_binding": artifacts.witness_binding,
    }


def reconstruct() -> dict[str, Any]:
    basis = validate_source_pins()
    f1 = _load("_zkc_f2p1_typed_f1", F1 / "reference_model.py")
    fixture = f1.make_fixture()
    expected = _read_json(F1 / "expected-identities.json")
    core_result = f1.admit_core(fixture.core_candidate, fixture.environment)
    _require(
        core_result.outcome == "Affirmative" and core_result.handle is not None,
        "CannotAnswer",
        "F2P1-C-F1-SUBJECT",
        "F1-R1B Core no longer admits",
    )
    protocol_result = f1.admit_fresh_protocol(
        core_result.handle, fixture.protocol_candidate, fixture.environment
    )
    _require(
        protocol_result.outcome == "Affirmative"
        and fixture.protocol_candidate.asserted_id.carrier()
        == expected["fresh_protocol_id"],
        "CannotAnswer",
        "F2P1-C-F1-SUBJECT",
        "F1-R1B Fresh Protocol no longer admits at the frozen identity",
    )
    core = core_result.handle.core
    decisions = [
        ordinal
        for ordinal, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect).__name__ == "ProverMessageEffect"
    ]
    _require(
        decisions == [0, 2]
        and len(core.public_bindings) == 1
        and core.public_bindings[0].binding_class.name == "STATEMENT",
        "CannotAnswer",
        "F2P1-C-F1-ROLES",
        "F1-R1B role sites drifted",
    )

    artifacts = _build_artifacts(f1, fixture)
    relation_metrics = _admit_relation_candidates(artifacts)
    binding_metrics = _check_protocol_binding(
        artifacts, core, artifacts.protocol_binding, exact_candidate=True
    )
    admitted_plan_id = _admit_plan(artifacts, core, artifacts.plan)
    realization = _plan_realizes(artifacts, core, artifacts.plan)
    _require(
        admitted_plan_id == artifacts.identities["prover_plan"]
        and realization["plan_id"] == admitted_plan_id,
        "CheckerFailure",
        "F2P1-X-PLAN-IDENTITY",
        "Plan admission and PlanRealizes identity disagree",
    )
    surface = _extract_witness_surface(artifacts, artifacts.plan)
    _check_witness_binding(
        artifacts,
        surface,
        artifacts.interface.body(),
        artifacts.identities["relation_interface"],
        artifacts.witness_binding,
    )
    honest = _honest_runs(artifacts)

    claim_attempt = copy.deepcopy(artifacts.protocol_binding)
    claim_attempt["claim_meanings"] = [
        {
            "claim": {"case": "InitialClaim", "binding": 0},
            "instance_recipe": "candidate relation instance recipe",
        }
    ]
    try:
        _check_protocol_binding(artifacts, core, claim_attempt, exact_candidate=False)
    except CandidateFailure as error:
        _require(
            (error.outcome, error.code) == ("CannotAnswer", INITIAL_CLAIM_CODE),
            "CheckerFailure",
            "F2P1-X-CLAIM-CLASSIFICATION",
            "initial-claim absence received another outcome",
        )
    else:  # pragma: no cover - fail-closed guard
        raise CandidateFailure(
            "CheckerFailure", "F2P1-X-CLAIM", "absent initial claim was accepted"
        )

    mutation_results: dict[str, list[str]] = {}

    wrong_statement = copy.deepcopy(artifacts.protocol_binding)
    wrong_statement["statement_edges"][0]["target"]["binding"] = 1
    try:
        _check_protocol_binding(artifacts, core, wrong_statement, exact_candidate=False)
    except CandidateFailure as error:
        mutation_results["wrong-statement-edge"] = [error.outcome, error.code]

    swapped = copy.deepcopy(artifacts.protocol_binding)
    swapped["phase_edges"][0]["target"], swapped["phase_edges"][1]["target"] = (
        swapped["phase_edges"][1]["target"],
        swapped["phase_edges"][0]["target"],
    )
    _check_protocol_binding(artifacts, core, swapped, exact_candidate=False)
    try:
        _check_protocol_binding(artifacts, core, swapped, exact_candidate=True)
    except CandidateFailure as error:
        mutation_results["swapped-phase-roles"] = [error.outcome, error.code]

    wrong_interface = artifacts.interface.body()
    wrong_interface["private_witness"] = [{"value_type": artifacts.bool_type}]
    wrong_interface_id = _candidate_id("relations.interface", wrong_interface)
    wrong_witness_binding = copy.deepcopy(artifacts.witness_binding)
    wrong_witness_binding["relation_interface_id"] = wrong_interface_id
    wrong_witness_binding["witness_edges"][0]["source"]["ref"]["owner_id"] = (
        wrong_interface_id
    )
    try:
        _check_witness_binding(
            artifacts,
            surface,
            wrong_interface,
            wrong_interface_id,
            wrong_witness_binding,
        )
    except CandidateFailure as error:
        mutation_results["different-witness-type"] = [error.outcome, error.code]

    outside_read = copy.deepcopy(artifacts.plan)
    outside_read["decision_recipes"][1]["recipe"]["nodes"][0]["inputs"][0] = {
        "case": "PlanRead",
        "coordinate": {"case": "ObservedMessage", "occurrence": 2},
    }
    _admit_plan(artifacts, core, outside_read)
    try:
        _plan_realizes(artifacts, core, outside_read)
    except CandidateFailure as error:
        mutation_results["plan-read-outside-guaranteed"] = [error.outcome, error.code]

    wrong_protocol = copy.deepcopy(artifacts.protocol_binding)
    wrong_protocol["protocol_id"] = artifacts.protocol_id[:-1] + (
        "0" if artifacts.protocol_id[-1] != "0" else "1"
    )
    try:
        _check_protocol_binding(artifacts, core, wrong_protocol, exact_candidate=False)
    except CandidateFailure as error:
        mutation_results["wrong-protocol-id"] = [error.outcome, error.code]

    expected_mutations = {
        "wrong-statement-edge": ["Refused", "F2P1-R-STATEMENT-EDGE"],
        "swapped-phase-roles": ["Refused", "F2P1-R-PHASE-ROLE-SWAP"],
        "different-witness-type": ["Refused", "F2P1-R-WITNESS-TYPE"],
        "plan-read-outside-guaranteed": ["Negative", "F2P1-N-PLAN-READ"],
        "wrong-protocol-id": ["Refused", "F2P1-R-WRONG-PROTOCOL"],
    }
    _require(
        mutation_results == expected_mutations,
        "CheckerFailure",
        "F2P1-X-MUTATIONS",
        f"mutation outcomes differ: {mutation_results!r}",
    )

    blockers = [
        {
            "name": "initial-claim-meaning",
            "outcome": "CannotAnswer",
            "code": INITIAL_CLAIM_CODE,
            "owner_contract": "docs-next/relations/relation-model.md Section 7.3 lines 1856-1860",
            "subject_evidence": "evaluation/formal-source-target-core-f1r1b/reference_model.py line 794: claims=()",
            "reason": "ClaimMeaningBinding requires a K2 ClaimRef; inventing InitialClaim(BindingRef(0)) would create claim flow not owned by the admitted Protocol and rotate its identity",
        }
    ]
    agreement = {
        "aggregate": f"CannotAnswer/{AGGREGATE}",
        "subject": {
            "core_id": artifacts.core_id,
            "protocol_id": artifacts.protocol_id,
            "statement_binding": 0,
            "challenge_occurrence": 1,
            "response_occurrence": 2,
            "claim_count": len(core.claims),
            "verifier_equation": "z = A + cY mod 3",
        },
        "algebra": artifacts.definition.payload,
        "role_labels": {
            "public_instance[0]": "Y",
            "private_witness[0]": "x",
            "oracle_statements": "empty",
            "phase_inputs[0]": "c",
            "phase_inputs[1]": "z",
        },
        "bodies": _body_catalog(artifacts),
        "identities": artifacts.identities,
        "premises": _premise_table(artifacts),
        "plan_realizes": realization,
        "blockers": blockers,
        "mutations": mutation_results,
        "measurements": {
            **relation_metrics,
            **binding_metrics,
            **honest,
            "candidate_identities": len(artifacts.identities),
        },
    }
    return {
        "path": "forward-typed-candidate",
        "basis": basis,
        "agreement": agreement,
        "agreement_sha256": _sha_value(agreement),
    }
