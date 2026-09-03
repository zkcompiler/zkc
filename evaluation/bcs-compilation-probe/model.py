"""Typed bounded composition model for the BCS compilation probe."""

from __future__ import annotations

from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path
from typing import Any


class ProbeError(ValueError):
    """The finite fixture falls outside the probe's exact carrier."""


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _identity(kind: str, body: Any) -> str:
    digest = hashlib.sha256(kind.encode("ascii") + b"\x00" + _canonical(body)).hexdigest()
    return f"probe:{kind}:{digest}"


@dataclass(frozen=True)
class Oracle:
    ref: str
    origin: str
    mode: str
    index_type: str
    element_type: str
    maximum_entries: int
    domain: tuple[int, ...]


@dataclass(frozen=True)
class Challenge:
    ref: str
    interpretation: str
    domain_size: int


@dataclass(frozen=True)
class Occurrence:
    ref: str
    effect: str
    dependencies: tuple[str, ...]
    outputs: tuple[str, ...]
    payload: dict[str, Any]


@dataclass(frozen=True)
class Core:
    interaction_profile: str
    oracles: tuple[Oracle, ...]
    challenges: tuple[Challenge, ...]
    occurrences: tuple[Occurrence, ...]

    def body(self) -> dict[str, Any]:
        return {
            "interaction_profile": self.interaction_profile,
            "oracles": [item.__dict__ for item in self.oracles],
            "challenges": [item.__dict__ for item in self.challenges],
            "occurrences": [
                {
                    "ref": item.ref,
                    "effect": item.effect,
                    "dependencies": list(item.dependencies),
                    "outputs": list(item.outputs),
                    **item.payload,
                }
                for item in self.occurrences
            ],
        }

    @property
    def identity(self) -> str:
        return _identity("pir.interactive-core", self.body())


VIEW_NAMES = (
    "PublicBindingView",
    "StrategyDecisionView",
    "PublicCoinView",
    "EffectView",
    "ClaimReductionView",
    "ExecutionView",
)


def _load(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if raw.get("format") != "zkc.bcs-compilation-probe.v0":
        raise ProbeError("BCS-R-FIXTURE-FORMAT")
    return raw


def _parse_core(raw: dict[str, Any], interaction_profile: str) -> Core:
    oracles = tuple(
        Oracle(
            item["ref"],
            item["origin"],
            item["mode"],
            item["index_type"],
            item["element_type"],
            item["maximum_entries"],
            tuple(item["domain"]),
        )
        for item in raw["oracles"]
    )
    challenges = tuple(
        Challenge(item["ref"], item["interpretation"], item["domain_size"])
        for item in raw["challenges"]
    )
    occurrences = []
    for item in raw["occurrences"]:
        payload = {
            key: value
            for key, value in item.items()
            if key not in {"ref", "effect", "dependencies", "outputs"}
        }
        occurrences.append(
            Occurrence(
                item["ref"],
                item["effect"],
                tuple(item["dependencies"]),
                tuple(item["outputs"]),
                payload,
            )
        )
    return Core(interaction_profile, oracles, challenges, tuple(occurrences))


def admit_source(core: Core) -> None:
    if len(core.oracles) != 2 or any(item.mode != "LogicalAccess" for item in core.oracles):
        raise ProbeError("BCS-R-SOURCE-ORACLE-SHAPE")
    if len(core.challenges) != 2 or any(item.interpretation != "Fresh" for item in core.challenges):
        raise ProbeError("BCS-R-SOURCE-CHALLENGE-SHAPE")
    oracle_refs = {item.ref for item in core.oracles}
    challenge_refs = {item.ref for item in core.challenges}
    if len(oracle_refs) != 2 or len(challenge_refs) != 2:
        raise ProbeError("BCS-R-SOURCE-REFERENCE-ALIAS")
    for oracle in core.oracles:
        if oracle.maximum_entries != len(oracle.domain):
            raise ProbeError("BCS-R-SOURCE-DOMAIN-CARDINALITY")
        if oracle.domain != tuple(range(oracle.maximum_entries)):
            raise ProbeError("BCS-R-SOURCE-DOMAIN-LAW")

    available: set[str] = set()
    seen: set[str] = set()
    publications: dict[str, int] = {}
    queries: dict[str, str] = {}
    answers: dict[str, str] = {}
    checks: list[Occurrence] = []
    terminals: list[Occurrence] = []
    for index, occurrence in enumerate(core.occurrences):
        if occurrence.ref in seen or any(dep not in seen for dep in occurrence.dependencies):
            raise ProbeError("BCS-R-SOURCE-SCHEDULE")
        if occurrence.effect == "PublishOracle":
            oracle = occurrence.payload.get("oracle")
            if oracle not in oracle_refs or occurrence.outputs:
                raise ProbeError("BCS-R-SOURCE-LOGICAL-PUBLICATION")
            publications[oracle] = index
        elif occurrence.effect == "SampleChallenge":
            challenge = occurrence.payload.get("challenge")
            if challenge not in challenge_refs or len(occurrence.outputs) != 1:
                raise ProbeError("BCS-R-SOURCE-FRESH-CHALLENGE")
        elif occurrence.effect == "QueryOracle":
            oracle = occurrence.payload.get("oracle")
            index_rule = occurrence.payload.get("index", {})
            if oracle not in publications or publications[oracle] >= index:
                raise ProbeError("BCS-R-SOURCE-QUERY-ORDER")
            if index_rule.get("operation") != "ChallengeModulo":
                raise ProbeError("BCS-R-SOURCE-QUERY-INDEX")
            challenge = next(
                (item for item in core.challenges if item.ref == index_rule.get("challenge")),
                None,
            )
            if challenge is None or challenge.domain_size != index_rule.get("modulus"):
                raise ProbeError("BCS-R-SOURCE-QUERY-DOMAIN")
            queries[occurrence.ref] = oracle
        elif occurrence.effect == "AnswerOracle":
            if len(occurrence.dependencies) != 1:
                raise ProbeError("BCS-R-SOURCE-ANSWER-ARITY")
            query = occurrence.dependencies[0]
            if queries.get(query) != occurrence.payload.get("oracle"):
                raise ProbeError("BCS-R-SOURCE-ANSWER-QUERY")
            answers[occurrence.ref] = occurrence.outputs[0]
        elif occurrence.effect == "InvokeCheck":
            checks.append(occurrence)
        elif occurrence.effect == "ReachTerminal":
            terminals.append(occurrence)
        seen.add(occurrence.ref)
        available.update(occurrence.outputs)

    if len(publications) != 2 or len(queries) != 2 or len(answers) != 2:
        raise ProbeError("BCS-R-SOURCE-ORACLE-LIFECYCLE")
    if len(checks) != 1 or set(checks[0].dependencies) != set(answers):
        raise ProbeError("BCS-R-SOURCE-CHECK-CLOSURE")
    if len(terminals) != 2:
        raise ProbeError("BCS-R-SOURCE-TERMINAL-CENSUS")
    accept, fallback = terminals
    if (
        accept.payload.get("terminal", {}).get("verdict") != "Accept"
        or accept.payload.get("terminal", {}).get("required_true_checks") != [checks[0].ref]
        or fallback.payload.get("terminal", {}).get("verdict") != "Reject"
        or fallback.payload.get("guard") != "Always"
        or core.occurrences[-1] != fallback
    ):
        raise ProbeError("BCS-R-SOURCE-MIGRATED-TERMINAL")


def issue_views(core: Core, names: tuple[str, ...]) -> dict[str, str]:
    if names != VIEW_NAMES:
        raise ProbeError("BCS-R-SOURCE-VIEW-CATALOG")
    schedule = [item.ref for item in core.occurrences]
    decisions = [item for item in core.occurrences if item.effect == "PublishOracle"]
    graph = _influence(core)
    logical = any(item.mode == "LogicalAccess" for item in core.oracles)
    bodies = {
        "PublicBindingView": {
            "core_id": core.identity,
            "scopes": [
                {
                    "scope_ref": "root",
                    "parent": None,
                    "opening": "Initially",
                    "scope_path": ["root"],
                }
            ],
            "bindings": [],
        },
        "StrategyDecisionView": {
            "core_id": core.identity,
            "decision_points": [
                {
                    "decision_ref": item.ref,
                    "occurrence_ref": item.ref,
                    "scope_path": ["root"],
                    "guard": "Always",
                    "move_type": {
                        "kind": "OracleMove",
                        "oracle_ref": item.payload["oracle"],
                        "publication_mode": next(
                            oracle.mode
                            for oracle in core.oracles
                            if oracle.ref == item.payload["oracle"]
                        ),
                    },
                    "prior_decision_refs": [prior.ref for prior in decisions[:index]],
                }
                for index, item in enumerate(decisions)
            ],
            "prover_view_formation_law": "pir.prover-view-formation-law",
            "guaranteed_prover_reads": [],
            "legal_move_types": [
                {"decision_ref": item.ref, "move_type": "OracleMove"}
                for item in decisions
            ],
        },
        "PublicCoinView": {
            "core_id": core.identity,
            "graph": graph,
            "structural_public_coin_eligibility": not logical,
            "verifier_private_predecessors": [],
            "challenges": [
                {
                    "challenge_ref": item.ref,
                    "occurrence_ref": next(
                        occurrence.ref
                        for occurrence in core.occurrences
                        if occurrence.payload.get("challenge") == item.ref
                    ),
                    "scope_ref": "root",
                    "value_type": "field-element",
                    "domain": f"finite-domain-{item.domain_size}",
                    "fresh_law": "pir.public-coin-law",
                    "correlation": "Independent",
                    "reduction_use": "NoReductionUse",
                    "public_conditions": [],
                    "public_condition_predecessors": [],
                    "reduction_consumers": [],
                }
                for item in core.challenges
            ],
        },
        "EffectView": {
            "core_id": core.identity,
            "occurrence_schedule": [
                {
                    "occurrence_ref": item.ref,
                    "scope_path": ["root"],
                    "guard": item.payload.get("guard", "Always"),
                    "effect": item.effect,
                    "output_types": ["probe-value" for _ in item.outputs],
                }
                for item in core.occurrences
            ],
            "values": [
                {
                    "value_ref": output,
                    "value_type": "probe-value",
                    "direct_predecessors": list(item.dependencies),
                }
                for item in core.occurrences
                for output in item.outputs
            ],
            "messages": [
                {"occurrence_ref": item.ref, "message_kind": item.effect}
                for item in core.occurrences
                if item.effect in {"ReceiveOpeningResponse"}
            ],
            "oracles": [
                {
                    "oracle_ref": oracle.ref,
                    "declaration": oracle.__dict__,
                    "publication_occurrence": next(
                        item.ref
                        for item in core.occurrences
                        if item.effect == "PublishOracle"
                        and item.payload.get("oracle") == oracle.ref
                    ),
                    "queries": [
                        item.ref
                        for item in core.occurrences
                        if item.effect == "QueryOracle"
                        and item.payload.get("oracle") == oracle.ref
                    ],
                    "answers": [
                        item.ref
                        for item in core.occurrences
                        if item.effect in {"AnswerOracle", "ReceiveOpeningResponse"}
                        and item.payload.get("oracle") == oracle.ref
                    ],
                }
                for oracle in core.oracles
            ],
            "checks": [
                {
                    "check_ref": item.ref,
                    "algorithm": item.payload.get("algorithm"),
                    "evaluation_contract": "probe-total-bool",
                    "inputs": list(item.dependencies),
                    "occurrence_ref": item.ref,
                }
                for item in core.occurrences
                if item.effect == "InvokeCheck"
            ],
            "terminals": [
                {
                    "terminal_ref": item.ref,
                    **item.payload["terminal"],
                    "occurrence_ref": item.ref,
                }
                for item in core.occurrences
                if item.effect == "ReachTerminal"
            ],
            "supported_extensions": [],
        },
        "ClaimReductionView": {
            "core_id": core.identity,
            "claims": [],
            "reductions": [],
            "terminal_dispositions": [],
        },
        "ExecutionView": {
            "protocol_id": _identity(
                "pir.protocol", {"core_id": core.identity, "interpretation": "Fresh"}
            ),
            "core_id": core.identity,
            "challenge_interpretation": "Fresh",
            "visible_history_law": "pir.visible-history-law",
            "resolver_coordinates": [
                {
                    "challenge_ref": item.ref,
                    "occurrence_ref": next(
                        occurrence.ref
                        for occurrence in core.occurrences
                        if occurrence.payload.get("challenge") == item.ref
                    ),
                    "value_type": "field-element",
                    "domain": f"finite-domain-{item.domain_size}",
                    "fresh_law": "pir.public-coin-law",
                    "public_conditions": [],
                    "prior_joint_members": [],
                }
                for item in core.challenges
            ],
            "generated_execution_law": "pir.generated-execution-law",
            "run_record_schema": "CompletedProtocolRecord",
            "interpretation_failure_schema": None,
            "outcome_partition": "ProtocolOutcomeLane",
            "replay_qualification_law": "pir.replay-qualification-law",
            "relation_run_view_issuance_law": "pir.relation-run-view-law",
        },
    }
    return {name: hashlib.sha256(_canonical(bodies[name])).hexdigest() for name in names}


def elaborate(core: Core, profile: dict[str, Any]) -> tuple[Core, dict[str, Any]]:
    target_oracles = tuple(replace(item, mode="PublicBinding") for item in core.oracles)
    target_occurrences: list[Occurrence] = []
    occurrence_map: list[tuple[str, str]] = []
    answer_map: list[tuple[str, str]] = []
    inserted: list[str] = []
    opening_checks: list[str] = []
    for occurrence in core.occurrences:
        if occurrence.effect == "PublishOracle":
            suffix = "zero" if occurrence.payload["oracle"] == "layer-zero" else "one"
            target = replace(
                occurrence,
                outputs=(f"commitment-{suffix}",),
                payload={
                    **occurrence.payload,
                    "binding_algorithm": profile["binding_algorithm"],
                    "binding_type": "bytes32",
                },
            )
            target_occurrences.append(target)
            occurrence_map.append((occurrence.ref, target.ref))
            continue
        if occurrence.effect == "AnswerOracle":
            suffix = "zero" if occurrence.payload["oracle"] == "layer-zero" else "one"
            response = replace(
                occurrence,
                effect="ReceiveOpeningResponse",
                outputs=(f"opening-response-{suffix}",),
                payload={**occurrence.payload, "evidence_type": profile["opening_evidence_type"]},
            )
            decode = Occurrence(
                f"decode-opening-{suffix}",
                "DecodeOpeningResponse",
                (response.ref,),
                (occurrence.outputs[0], f"opening-evidence-{suffix}"),
                {"oracle": occurrence.payload["oracle"]},
            )
            group_check = Occurrence(
                f"claim-group-check-{suffix}",
                "InvokeCheck",
                (response.ref, f"query-layer-{suffix}"),
                (f"claim-group-ok-{suffix}",),
                {"algorithm": "check-opening-claim-group"},
            )
            opening_check = Occurrence(
                f"opening-check-{suffix}",
                "InvokeCheck",
                (decode.ref, group_check.ref),
                (f"opening-ok-{suffix}",),
                {"algorithm": "verify-opening-group"},
            )
            target_occurrences.extend((response, decode, group_check, opening_check))
            occurrence_map.append((occurrence.ref, response.ref))
            answer_map.append((occurrence.outputs[0], decode.outputs[0]))
            inserted.extend((decode.ref, group_check.ref, opening_check.ref))
            opening_checks.extend((group_check.ref, opening_check.ref))
            continue
        if occurrence.effect == "ReachTerminal":
            terminal = dict(occurrence.payload["terminal"])
            if terminal["verdict"] == "Accept":
                terminal["required_true_checks"] = [
                    *terminal["required_true_checks"],
                    *opening_checks,
                ]
                dependencies = tuple(dict.fromkeys((*occurrence.dependencies, *opening_checks)))
                target = replace(
                    occurrence,
                    dependencies=dependencies,
                    payload={**occurrence.payload, "terminal": terminal},
                )
            else:
                target = occurrence
            target_occurrences.append(target)
            occurrence_map.append((occurrence.ref, target.ref))
            continue
        target_occurrences.append(occurrence)
        occurrence_map.append((occurrence.ref, occurrence.ref))

    target = Core(core.interaction_profile, target_oracles, core.challenges, tuple(target_occurrences))
    transition = {
        "owner": "pir.oracle-commitment-construction",
        "source_core_id": core.identity,
        "target_core_id": target.identity,
        "occurrence_map": occurrence_map,
        "answer_map": answer_map,
        "inserted_target_effects": inserted,
        "requires_independent_target_admission": True,
        "target_readmitted": True,
        "compiler_role": "consume-owner-checked-transition",
        "compiler_activation_claimed": False,
    }
    return target, transition


def admit_target(source: Core, target: Core, transition: dict[str, Any]) -> None:
    if source.identity == target.identity:
        raise ProbeError("BCS-R-TARGET-IDENTITY-DID-NOT-ROTATE")
    if any(item.mode != "PublicBinding" for item in target.oracles):
        raise ProbeError("BCS-R-TARGET-ORACLE-MODE")
    refs = [item.ref for item in target.occurrences]
    if len(refs) != len(set(refs)):
        raise ProbeError("BCS-R-TARGET-REFERENCE-ALIAS")
    index = {ref: position for position, ref in enumerate(refs)}
    for occurrence in target.occurrences:
        if any(dep not in index or index[dep] >= index[occurrence.ref] for dep in occurrence.dependencies):
            raise ProbeError("BCS-R-TARGET-DEPENDENCY-ORDER")
    for oracle in target.oracles:
        publish = next(item for item in target.occurrences if item.payload.get("oracle") == oracle.ref and item.effect == "PublishOracle")
        sample = next(item for item in target.occurrences if item.effect == "SampleChallenge" and item.payload.get("challenge") == ("query-zero" if oracle.ref == "layer-zero" else "query-one"))
        response = next(item for item in target.occurrences if item.payload.get("oracle") == oracle.ref and item.effect == "ReceiveOpeningResponse")
        if not publish.outputs or not index[publish.ref] < index[sample.ref] < index[response.ref]:
            raise ProbeError("BCS-R-TARGET-COMMIT-CHALLENGE-OPEN-ORDER")
    accept = next(item for item in target.occurrences if item.ref == "accept")
    required = set(accept.payload["terminal"]["required_true_checks"])
    if required != {"fold-check", *transition["inserted_target_effects"][1::3], *transition["inserted_target_effects"][2::3]}:
        raise ProbeError("BCS-R-TARGET-ACCEPTANCE-CLOSURE")
    if transition["target_core_id"] != target.identity or not transition["target_readmitted"]:
        raise ProbeError("BCS-R-TARGET-READMISSION")


def _influence(core: Core) -> dict[str, Any]:
    edges: set[tuple[str, str]] = set()
    for item in core.occurrences:
        edges.update((dep, item.ref) for dep in item.dependencies)
    index = {item.ref: pos for pos, item in enumerate(core.occurrences)}
    publications = [item.ref for item in core.occurrences if item.effect == "PublishOracle"]
    accepting = "accept"
    cones: dict[str, list[str]] = {}
    for publication in publications:
        reached = {publication}
        changed = True
        while changed:
            changed = False
            for source, target in edges:
                if source in reached and target not in reached:
                    reached.add(target)
                    changed = True
        cones[publication] = sorted(reached, key=index.get)
        if accepting not in reached:
            raise ProbeError("BCS-R-TARGET-COMMITMENT-CONE")
    return {
        "edge_count": len(edges),
        "acceptance_sink": accepting,
        "publication_cones": cones,
        "digest": hashlib.sha256(_canonical(sorted(edges))).hexdigest(),
    }


def evaluate(path: Path) -> dict[str, Any]:
    raw = _load(path)
    source = _parse_core(raw["source_core"], raw["interaction_profile"])
    admit_source(source)
    views = issue_views(source, tuple(raw["required_source_views"]))
    target, transition = elaborate(source, raw["commitment_profile"])
    admit_target(source, target, transition)
    target_views = issue_views(target, tuple(raw["required_source_views"]))
    influence = _influence(target)
    target_fresh_protocol = _identity(
        "pir.protocol", {"core_id": target.identity, "interpretation": "Fresh"}
    )
    construction = _identity(
        "pir.transcript-construction",
        {"core_id": target.identity, "family": "canonical-framed"},
    )
    target_fs_protocol = _identity(
        "pir.protocol",
        {
            "core_id": target.identity,
            "interpretation": "FiatShamir",
            "construction_id": construction,
        },
    )
    premises = raw["chosen_soundness_statement"]["premises"]
    missing = [item["name"] for item in premises if item["owner_coordinate"] is None]
    provisional = [
        item["name"]
        for item in premises
        if item["owner_coordinate"] is not None and "exact-family" in item["owner_coordinate"]
    ]
    view_relation = {
        name: {
            "source_view_digest": digest,
            "target_view_digest": target_views[name],
            "target_owner": target.identity if name != "ExecutionView" else target_fresh_protocol,
            "map": "transition-coordinate-map-plus-declared-insertions",
        }
        for name, digest in views.items()
    }
    return {
        "source": {
            "admitted": True,
            "core_id": source.identity,
            "logical_oracles": len(source.oracles),
            "fresh_challenges": len(source.challenges),
            "occurrences": len(source.occurrences),
            "views": views,
        },
        "target": {
            "admitted": True,
            "core_id": target.identity,
            "public_binding_oracles": len(target.oracles),
            "occurrences": len(target.occurrences),
            "views": target_views,
            "body": target.body(),
        },
        "transition": {
            **transition,
            "view_relation_digest": hashlib.sha256(_canonical(view_relation)).hexdigest(),
            "view_relations": len(view_relation),
        },
        "identity_cone": {
            "interaction_profile_unchanged": source.interaction_profile == target.interaction_profile,
            "source_target_core_rotated": source.identity != target.identity,
            "target_fresh_protocol_id": target_fresh_protocol,
            "target_fs_protocol_id": target_fs_protocol,
            "transcript_construction_id": construction,
            "same_target_core_for_fresh_and_fs": True,
            "influence": influence,
        },
        "premises": {
            "statement": raw["chosen_soundness_statement"]["text"],
            "entries": premises,
            "missing_coordinates": missing,
            "provisional_family_coordinates": provisional,
            "all_exactly_coordinated": not missing and not provisional,
        },
    }
