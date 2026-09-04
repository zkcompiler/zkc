"""Raw-dictionary reconstruction for the bounded BCS composition probe."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


class IndependentError(ValueError):
    pass


def _bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _id(label: str, value: Any) -> str:
    return "probe:" + label + ":" + hashlib.sha256(label.encode("ascii") + b"\0" + _bytes(value)).hexdigest()


def _core_id(profile: str, oracles: list[dict[str, Any]], challenges: list[dict[str, Any]], occurrences: list[dict[str, Any]]) -> str:
    normalized_oracles = []
    for item in oracles:
        normalized_oracles.append(
            {
                "ref": item["ref"],
                "origin": item["origin"],
                "mode": item["mode"],
                "index_type": item["index_type"],
                "element_type": item["element_type"],
                "maximum_entries": item["maximum_entries"],
                "domain": tuple(item["domain"]),
            }
        )
    normalized_challenges = [
        {
            "ref": item["ref"],
            "interpretation": item["interpretation"],
            "domain_size": item["domain_size"],
        }
        for item in challenges
    ]
    body = {
        "interaction_profile": profile,
        "oracles": normalized_oracles,
        "challenges": normalized_challenges,
        "occurrences": occurrences,
    }
    return _id("pir.interactive-core", body)


def _validate_source(raw: dict[str, Any]) -> None:
    oracles = raw["oracles"]
    challenges = raw["challenges"]
    occurrences = raw["occurrences"]
    if len(oracles) != 2 or {item["mode"] for item in oracles} != {"LogicalAccess"}:
        raise IndependentError("BCS-R-COLD-SOURCE-ORACLES")
    if len(challenges) != 2 or {item["interpretation"] for item in challenges} != {"Fresh"}:
        raise IndependentError("BCS-R-COLD-SOURCE-CHALLENGES")
    if any(item["domain"] != list(range(item["maximum_entries"])) for item in oracles):
        raise IndependentError("BCS-R-COLD-DOMAIN-LAW")
    positions = {item["ref"]: index for index, item in enumerate(occurrences)}
    if len(positions) != len(occurrences):
        raise IndependentError("BCS-R-COLD-SCHEDULE-ALIAS")
    for item in occurrences:
        if any(dep not in positions or positions[dep] >= positions[item["ref"]] for dep in item["dependencies"]):
            raise IndependentError("BCS-R-COLD-SCHEDULE-ORDER")
    queries = [item for item in occurrences if item["effect"] == "QueryOracle"]
    answers = [item for item in occurrences if item["effect"] == "AnswerOracle"]
    checks = [item for item in occurrences if item["effect"] == "InvokeCheck"]
    terminals = [item for item in occurrences if item["effect"] == "ReachTerminal"]
    if len(queries) != 2 or len(answers) != 2 or len(checks) != 1 or len(terminals) != 2:
        raise IndependentError("BCS-R-COLD-SOURCE-CENSUS")
    if set(checks[0]["dependencies"]) != {item["ref"] for item in answers}:
        raise IndependentError("BCS-R-COLD-CHECK-CLOSURE")
    if terminals[0]["terminal"]["required_true_checks"] != [checks[0]["ref"]]:
        raise IndependentError("BCS-R-COLD-ACCEPT-CLOSURE")
    if terminals[-1]["guard"] != "Always" or terminals[-1]["terminal"]["verdict"] != "Reject" or occurrences[-1] != terminals[-1]:
        raise IndependentError("BCS-R-COLD-FALLBACK")


def _elaborate(raw: dict[str, Any], profile: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    target_oracles = []
    for oracle in raw["oracles"]:
        item = dict(oracle)
        item["mode"] = "PublicBinding"
        target_oracles.append(item)
    output: list[dict[str, Any]] = []
    occurrence_map: list[tuple[str, str]] = []
    answer_map: list[tuple[str, str]] = []
    inserted: list[str] = []
    required_opening_checks: list[str] = []
    for source in raw["occurrences"]:
        item = json.loads(json.dumps(source))
        suffix = "zero" if item.get("oracle") == "layer-zero" else "one"
        if item["effect"] == "PublishOracle":
            item["outputs"] = ["commitment-" + suffix]
            item["binding_algorithm"] = profile["binding_algorithm"]
            item["binding_type"] = "bytes32"
        elif item["effect"] == "AnswerOracle":
            item["effect"] = "ReceiveOpeningResponse"
            original_answer = item["outputs"][0]
            item["outputs"] = ["opening-response-" + suffix]
            item["evidence_type"] = profile["opening_evidence_type"]
            output.append(item)
            decode = {
                "ref": "decode-opening-" + suffix,
                "effect": "DecodeOpeningResponse",
                "dependencies": [item["ref"]],
                "outputs": [original_answer, "opening-evidence-" + suffix],
                "oracle": item["oracle"],
            }
            group = {
                "ref": "claim-group-check-" + suffix,
                "effect": "InvokeCheck",
                "dependencies": [item["ref"], "query-layer-" + suffix],
                "outputs": ["claim-group-ok-" + suffix],
                "algorithm": "check-opening-claim-group",
            }
            opening = {
                "ref": "opening-check-" + suffix,
                "effect": "InvokeCheck",
                "dependencies": [decode["ref"], group["ref"]],
                "outputs": ["opening-ok-" + suffix],
                "algorithm": "verify-opening-group",
            }
            output.extend((decode, group, opening))
            occurrence_map.append((source["ref"], item["ref"]))
            answer_map.append((original_answer, original_answer))
            inserted.extend((decode["ref"], group["ref"], opening["ref"]))
            required_opening_checks.extend((group["ref"], opening["ref"]))
            continue
        elif item["effect"] == "ReachTerminal" and item["terminal"]["verdict"] == "Accept":
            item["dependencies"] = list(dict.fromkeys([*item["dependencies"], *required_opening_checks]))
            item["terminal"]["required_true_checks"] = [
                *item["terminal"]["required_true_checks"],
                *required_opening_checks,
            ]
        output.append(item)
        occurrence_map.append((source["ref"], item["ref"]))
    return target_oracles, output, {
        "occurrence_map": occurrence_map,
        "answer_map": answer_map,
        "inserted_target_effects": inserted,
    }


def _view_digests(source_id: str, raw: dict[str, Any], names: list[str]) -> dict[str, str]:
    if names != ["PublicBindingView", "StrategyDecisionView", "PublicCoinView", "EffectView", "ClaimReductionView", "ExecutionView"]:
        raise IndependentError("BCS-R-COLD-VIEW-CATALOG")
    occurrences = raw["occurrences"]
    decisions = [item for item in occurrences if item["effect"] == "PublishOracle"]
    logical = any(item["mode"] == "LogicalAccess" for item in raw["oracles"])
    graph = _graph(occurrences)
    bodies = [
        {
            "core_id": source_id,
            "scopes": [{"scope_ref": "root", "parent": None, "opening": "Initially", "scope_path": ["root"]}],
            "bindings": [],
        },
        {
            "core_id": source_id,
            "decision_points": [
                {
                    "decision_ref": item["ref"],
                    "occurrence_ref": item["ref"],
                    "scope_path": ["root"],
                    "guard": "Always",
                    "move_type": {
                        "kind": "OracleMove",
                        "oracle_ref": item["oracle"],
                        "publication_mode": next(oracle["mode"] for oracle in raw["oracles"] if oracle["ref"] == item["oracle"]),
                    },
                    "prior_decision_refs": [prior["ref"] for prior in decisions[:index]],
                }
                for index, item in enumerate(decisions)
            ],
            "prover_view_formation_law": "pir.prover-view-formation-law",
            "guaranteed_prover_reads": [],
            "legal_move_types": [{"decision_ref": item["ref"], "move_type": "OracleMove"} for item in decisions],
        },
        {
            "core_id": source_id,
            "graph": graph,
            "structural_public_coin_eligibility": not logical,
            "verifier_private_predecessors": [],
            "challenges": [
                {
                    "challenge_ref": item["ref"],
                    "occurrence_ref": next(occurrence["ref"] for occurrence in occurrences if occurrence.get("challenge") == item["ref"]),
                    "scope_ref": "root",
                    "value_type": "field-element",
                    "domain": "finite-domain-" + str(item["domain_size"]),
                    "fresh_law": "pir.public-coin-law",
                    "correlation": "Independent",
                    "reduction_use": "NoReductionUse",
                    "public_conditions": [],
                    "public_condition_predecessors": [],
                    "reduction_consumers": [],
                }
                for item in raw["challenges"]
            ],
        },
        {
            "core_id": source_id,
            "occurrence_schedule": [
                {
                    "occurrence_ref": item["ref"],
                    "scope_path": ["root"],
                    "guard": item.get("guard", "Always"),
                    "effect": item["effect"],
                    "output_types": ["probe-value" for _ in item["outputs"]],
                }
                for item in occurrences
            ],
            "values": [
                {"value_ref": output, "value_type": "probe-value", "direct_predecessors": item["dependencies"]}
                for item in occurrences for output in item["outputs"]
            ],
            "messages": [
                {"occurrence_ref": item["ref"], "message_kind": item["effect"]}
                for item in occurrences if item["effect"] == "ReceiveOpeningResponse"
            ],
            "oracles": [
                {
                    "oracle_ref": oracle["ref"],
                    "declaration": oracle,
                    "publication_occurrence": next(item["ref"] for item in occurrences if item["effect"] == "PublishOracle" and item.get("oracle") == oracle["ref"]),
                    "queries": [item["ref"] for item in occurrences if item["effect"] == "QueryOracle" and item.get("oracle") == oracle["ref"]],
                    "answers": [item["ref"] for item in occurrences if item["effect"] in {"AnswerOracle", "ReceiveOpeningResponse"} and item.get("oracle") == oracle["ref"]],
                }
                for oracle in raw["oracles"]
            ],
            "checks": [
                {
                    "check_ref": item["ref"],
                    "algorithm": item.get("algorithm"),
                    "evaluation_contract": "probe-total-bool",
                    "inputs": item["dependencies"],
                    "occurrence_ref": item["ref"],
                }
                for item in occurrences if item["effect"] == "InvokeCheck"
            ],
            "terminals": [
                {"terminal_ref": item["ref"], **item["terminal"], "occurrence_ref": item["ref"]}
                for item in occurrences if item["effect"] == "ReachTerminal"
            ],
            "supported_extensions": [],
        },
        {"core_id": source_id, "claims": [], "reductions": [], "terminal_dispositions": []},
        {
            "protocol_id": _id("pir.protocol", {"core_id": source_id, "interpretation": "Fresh"}),
            "core_id": source_id,
            "challenge_interpretation": "Fresh",
            "visible_history_law": "pir.visible-history-law",
            "resolver_coordinates": [
                {
                    "challenge_ref": item["ref"],
                    "occurrence_ref": next(occurrence["ref"] for occurrence in occurrences if occurrence.get("challenge") == item["ref"]),
                    "value_type": "field-element",
                    "domain": "finite-domain-" + str(item["domain_size"]),
                    "fresh_law": "pir.public-coin-law",
                    "public_conditions": [],
                    "prior_joint_members": [],
                }
                for item in raw["challenges"]
            ],
            "generated_execution_law": "pir.generated-execution-law",
            "run_record_schema": "CompletedProtocolRecord",
            "interpretation_failure_schema": None,
            "outcome_partition": "ProtocolOutcomeLane",
            "replay_qualification_law": "pir.replay-qualification-law",
            "relation_run_view_issuance_law": "pir.relation-run-view-law",
        },
    ]
    return {name: hashlib.sha256(_bytes(body)).hexdigest() for name, body in zip(names, bodies)}


def _graph(occurrences: list[dict[str, Any]]) -> dict[str, Any]:
    edges = {(dep, item["ref"]) for item in occurrences for dep in item["dependencies"]}
    position = {item["ref"]: index for index, item in enumerate(occurrences)}
    cones: dict[str, list[str]] = {}
    for publication in (item["ref"] for item in occurrences if item["effect"] == "PublishOracle"):
        pending = [publication]
        reached = {publication}
        while pending:
            source = pending.pop()
            for left, right in edges:
                if left == source and right not in reached:
                    reached.add(right)
                    pending.append(right)
        if "accept" not in reached:
            raise IndependentError("BCS-R-COLD-COMMITMENT-CONE")
        cones[publication] = sorted(reached, key=position.get)
    return {
        "edge_count": len(edges),
        "acceptance_sink": "accept",
        "publication_cones": cones,
        "digest": hashlib.sha256(_bytes(sorted(edges))).hexdigest(),
    }


def evaluate(path: Path) -> dict[str, Any]:
    document = json.loads(path.read_text(encoding="utf-8"))
    if document.get("format") != "zkc.bcs-compilation-probe.v0":
        raise IndependentError("BCS-R-COLD-FORMAT")
    source = document["source_core"]
    profile_name = document["interaction_profile"]
    _validate_source(source)
    source_id = _core_id(profile_name, source["oracles"], source["challenges"], source["occurrences"])
    views = _view_digests(source_id, source, document["required_source_views"])
    target_oracles, target_occurrences, maps = _elaborate(source, document["commitment_profile"])
    target_id = _core_id(profile_name, target_oracles, source["challenges"], target_occurrences)
    if target_id == source_id or {item["mode"] for item in target_oracles} != {"PublicBinding"}:
        raise IndependentError("BCS-R-COLD-TARGET-ADMISSION")
    positions = {item["ref"]: index for index, item in enumerate(target_occurrences)}
    if len(positions) != len(target_occurrences):
        raise IndependentError("BCS-R-COLD-TARGET-ALIAS")
    for item in target_occurrences:
        if any(dep not in positions or positions[dep] >= positions[item["ref"]] for dep in item["dependencies"]):
            raise IndependentError("BCS-R-COLD-TARGET-ORDER")
    target_body = {
        "interaction_profile": profile_name,
        "oracles": [
            {
                "ref": item["ref"],
                "origin": item["origin"],
                "mode": item["mode"],
                "index_type": item["index_type"],
                "element_type": item["element_type"],
                "maximum_entries": item["maximum_entries"],
                "domain": tuple(item["domain"]),
            }
            for item in target_oracles
        ],
        "challenges": [
            {"ref": item["ref"], "interpretation": item["interpretation"], "domain_size": item["domain_size"]}
            for item in source["challenges"]
        ],
        "occurrences": target_occurrences,
    }
    fresh = _id("pir.protocol", {"core_id": target_id, "interpretation": "Fresh"})
    construction = _id("pir.transcript-construction", {"core_id": target_id, "family": "canonical-framed"})
    fs = _id("pir.protocol", {"core_id": target_id, "interpretation": "FiatShamir", "construction_id": construction})
    target_view_input = {
        "oracles": target_oracles,
        "challenges": source["challenges"],
        "occurrences": target_occurrences,
    }
    target_views = _view_digests(target_id, target_view_input, document["required_source_views"])
    view_relations = {
        name: {
            "source_view_digest": digest,
            "target_view_digest": target_views[name],
            "target_owner": target_id if name != "ExecutionView" else fresh,
            "map": "transition-coordinate-map-plus-declared-insertions",
        }
        for name, digest in views.items()
    }
    premise_entries = document["chosen_soundness_statement"]["premises"]
    missing = [item["name"] for item in premise_entries if item["owner_coordinate"] is None]
    provisional = [item["name"] for item in premise_entries if item["owner_coordinate"] is not None and "exact-family" in item["owner_coordinate"]]
    transition = {
        "owner": "pir.oracle-commitment-construction",
        "source_core_id": source_id,
        "target_core_id": target_id,
        **maps,
        "requires_independent_target_admission": True,
        "target_readmitted": True,
        "compiler_role": "consume-owner-checked-transition",
        "compiler_activation_claimed": False,
        "view_relation_digest": hashlib.sha256(_bytes(view_relations)).hexdigest(),
        "view_relations": len(view_relations),
    }
    return {
        "source": {"admitted": True, "core_id": source_id, "logical_oracles": 2, "fresh_challenges": 2, "occurrences": len(source["occurrences"]), "views": views},
        "target": {"admitted": True, "core_id": target_id, "public_binding_oracles": 2, "occurrences": len(target_occurrences), "views": target_views, "body": target_body},
        "transition": transition,
        "identity_cone": {
            "interaction_profile_unchanged": True,
            "source_target_core_rotated": True,
            "target_fresh_protocol_id": fresh,
            "target_fs_protocol_id": fs,
            "transcript_construction_id": construction,
            "same_target_core_for_fresh_and_fs": True,
            "influence": _graph(target_occurrences),
        },
        "premises": {
            "statement": document["chosen_soundness_statement"]["text"],
            "entries": premise_entries,
            "missing_coordinates": missing,
            "provisional_family_coordinates": provisional,
            "all_exactly_coordinated": not missing and not provisional,
        },
    }
