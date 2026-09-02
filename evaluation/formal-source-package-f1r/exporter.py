#!/usr/bin/env python3
"""Untrusted producer for the bounded F1-R package corpus.

The checkers do not import this module and do not accept any identity merely
because this producer emitted it.  The source bodies are manually formed
research fixtures, not live zkc owner views.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


FORMAT = "zkc.formal-source-package.f1r.v0"
CONTRACT_SCHEMA = "zkc.formal-source-contract.f1r.v0"
CONTRACT_DOMAIN = "zkc/f1r/contract/v0"
AUTH_DOMAIN = "zkc/f1r/auth-node/v0"
PACKAGE_DOMAIN = "zkc/f1r/package/v0"


Json = Any


def canonical_json(value: Json) -> bytes:
    """Producer-side implementation; neither checker imports it."""

    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def value_id(domain: str, value: Json) -> str:
    digest = hashlib.sha256(
        domain.encode("ascii") + b"\x00" + canonical_json(value)
    ).hexdigest()
    return f"sha256:{digest}"


def node(
    coordinate: str,
    kind: str,
    profile: str,
    dependencies: Iterable[str],
    body: dict[str, Json],
) -> dict[str, Json]:
    dependency_list = sorted(dependencies)
    complete_body: dict[str, Json] = copy.deepcopy(body)
    complete_body["imports"] = dependency_list
    return {
        "coordinate": coordinate,
        "kind": kind,
        "profile": profile,
        "dependencies": dependency_list,
        "body": complete_body,
    }


def common_relation_nodes() -> list[dict[str, Json]]:
    scalar = node(
        "foundation.type.scalar",
        "FoundationType",
        "f1r-manual-foundation-types-v0",
        [],
        {
            "name": "Scalar",
            "role": "challenge-response-field",
            "visibility": "type-only",
        },
    )
    group = node(
        "foundation.type.group",
        "FoundationType",
        "f1r-manual-foundation-types-v0",
        [],
        {
            "name": "Group",
            "role": "additive-commitment-group",
            "visibility": "type-only",
        },
    )
    definition = node(
        "relations.schnorr.definition",
        "RelationDefinition",
        "f1r-manual-schnorr-relation-v0",
        ["foundation.type.group", "foundation.type.scalar"],
        {
            "equation": {
                "left": ["scalar-mul", "witness.x", "generator.G"],
                "right": "statement.Y",
            },
            "name": "SchnorrDiscreteLog",
            "statement_role": "statement.Y",
            "witness_role": "witness.x",
        },
    )
    model = node(
        "relations.schnorr.model",
        "RelationModel",
        "f1r-manual-schnorr-relation-v0",
        [
            "foundation.type.group",
            "foundation.type.scalar",
            "relations.schnorr.definition",
        ],
        {
            "group_role": "additive-commutative-group",
            "scalar_role": "field-module-scalar",
            "sampling_role": "uniform-scalar",
        },
    )
    instance = node(
        "relations.schnorr.instance",
        "RelationInstance",
        "f1r-manual-schnorr-relation-v0",
        ["relations.schnorr.model"],
        {
            "generator": "generator.G",
            "roles": {
                "challenge": "challenge.c",
                "commitment": "message.A",
                "response": "response.z",
                "statement": "statement.Y",
                "witness": "witness.x",
            },
        },
    )
    return [scalar, group, definition, model, instance]


def fresh_nodes() -> tuple[list[dict[str, Json]], list[str]]:
    nodes = common_relation_nodes()
    core = node(
        "pir.core.schnorr-fresh",
        "InteractiveCore",
        "f1r-manual-pir-core-v0",
        [
            "foundation.type.group",
            "foundation.type.scalar",
            "relations.schnorr.instance",
        ],
        {
            "challenge": {
                "dependencies": ["message.A", "statement.Y"],
                "domain": "schnorr.challenge.v0",
                "occurrence": "challenge.c",
                "sharing": "Unique",
                "space": "uniform-scalar",
            },
            "claim_reduction": {
                "challenge_uses": ["challenge.c"],
                "check_uses": ["check.schnorr-equation"],
                "input_claim": "claim.knowledge-of-x",
                "output_claim": "claim.schnorr-equation",
            },
            "interface": {
                "public_bindings": [
                    {"coordinate": "statement.Y", "type": "Group"}
                ]
            },
            "occurrences": [
                {
                    "id": "message.A",
                    "kind": "Receive",
                    "value_type": "Group",
                    "visibility": "Public",
                },
                {
                    "id": "challenge.c",
                    "kind": "Challenge",
                    "value_type": "Scalar",
                    "visibility": "Public",
                },
                {
                    "id": "response.z",
                    "kind": "Receive",
                    "value_type": "Scalar",
                    "visibility": "Public",
                },
                {
                    "id": "check.schnorr-equation",
                    "kind": "Check",
                    "predicate": "zG=A+cY",
                    "visibility": "Public",
                },
                {
                    "condition": "check.schnorr-equation",
                    "id": "terminal.accept",
                    "kind": "Terminal",
                    "visibility": "Public",
                },
            ],
        },
    )
    protocol = node(
        "pir.protocol.schnorr-fresh",
        "Protocol",
        "f1r-manual-fresh-public-coin-v0",
        ["pir.core.schnorr-fresh"],
        {
            "challenge_interpretation": "PublicCoin",
            "core": "pir.core.schnorr-fresh",
            "execution": {
                "failure_precedence": [
                    "MalformedInput",
                    "MissingMessage",
                    "SamplingFailure",
                    "CheckRejected",
                    "Accepted",
                ],
                "order": [
                    "message.A",
                    "challenge.c",
                    "response.z",
                    "check.schnorr-equation",
                    "terminal.accept",
                ],
                "terminal": "terminal.accept",
            },
            "regime": "Fresh",
        },
    )
    correspondence = node(
        "relations.schnorr.fresh-correspondence",
        "ProtocolRelationCorrespondence",
        "f1r-manual-fresh-schnorr-correspondence-v0",
        ["pir.protocol.schnorr-fresh", "relations.schnorr.instance"],
        {
            "acceptance_check": "check.schnorr-equation",
            "direction": "ProtocolAcceptsIffVerifierRelation",
            "role_map": {
                "challenge.c": "challenge",
                "message.A": "commitment",
                "response.z": "response",
                "statement.Y": "statement",
            },
        },
    )
    nodes.extend([core, protocol, correspondence])
    roots = [
        "pir.core.schnorr-fresh",
        "pir.protocol.schnorr-fresh",
        "relations.schnorr.fresh-correspondence",
        "relations.schnorr.instance",
    ]
    return nodes, roots


def shared_nodes() -> tuple[list[dict[str, Json]], list[str]]:
    nodes = common_relation_nodes()
    core = node(
        "pir.core.schnorr-shared",
        "InteractiveCore",
        "f1r-manual-pir-core-v0",
        [
            "foundation.type.group",
            "foundation.type.scalar",
            "relations.schnorr.instance",
        ],
        {
            "occurrences": [
                {"id": "A.message", "kind": "Receive", "value_type": "Group"},
                {"id": "B.message", "kind": "Receive", "value_type": "Group"},
                {
                    "id": "challenge.joint",
                    "kind": "Challenge",
                    "value_type": "Scalar",
                },
                {"id": "A.response", "kind": "Receive", "value_type": "Scalar"},
                {"id": "B.response", "kind": "Receive", "value_type": "Scalar"},
                {"id": "A.check", "kind": "Check", "value_type": "Bool"},
                {"id": "B.check", "kind": "Check", "value_type": "Bool"},
                {"id": "terminal.accept", "kind": "Terminal"},
            ],
            "reductions": [
                {
                    "challenge_occurrence": "challenge.joint",
                    "check_occurrence": "A.check",
                    "coordinate": "reduction.A",
                },
                {
                    "challenge_occurrence": "challenge.joint",
                    "check_occurrence": "B.check",
                    "coordinate": "reduction.B",
                },
            ],
            "shared_challenge": {
                "consumers": ["reduction.A", "reduction.B"],
                "occurrence": "challenge.joint",
                "sample_symbol": "c",
                "sharing": "Shared",
            },
        },
    )
    protocol = node(
        "pir.protocol.schnorr-shared",
        "Protocol",
        "f1r-manual-fresh-shared-challenge-v0",
        ["pir.core.schnorr-shared"],
        {
            "challenge_interpretation": "PublicCoin",
            "core": "pir.core.schnorr-shared",
            "execution": {
                "failure_precedence": ["A.CheckRejected", "B.CheckRejected", "Accepted"],
                "order": [
                    "A.message",
                    "B.message",
                    "challenge.joint",
                    "A.response",
                    "B.response",
                    "A.check",
                    "B.check",
                    "terminal.accept",
                ],
                "terminal": "terminal.accept",
            },
            "regime": "Fresh",
        },
    )
    correspondence = node(
        "relations.schnorr.shared-correspondence",
        "ProtocolRelationCorrespondence",
        "f1r-manual-fresh-schnorr-correspondence-v0",
        ["pir.protocol.schnorr-shared", "relations.schnorr.instance"],
        {
            "direction": "TwoReductionsOneSharedChallenge",
            "reduction_map": {
                "reduction.A": "relations.schnorr.instance",
                "reduction.B": "relations.schnorr.instance",
            },
            "shared_occurrence": "challenge.joint",
        },
    )
    nodes.extend([core, protocol, correspondence])
    roots = [
        "pir.core.schnorr-shared",
        "pir.protocol.schnorr-shared",
        "relations.schnorr.instance",
        "relations.schnorr.shared-correspondence",
    ]
    return nodes, roots


def fs_nodes() -> tuple[list[dict[str, Json]], list[str]]:
    nodes = common_relation_nodes()
    core = node(
        "pir.core.schnorr-fs",
        "InteractiveCore",
        "f1r-manual-pir-core-v0",
        [
            "foundation.type.group",
            "foundation.type.scalar",
            "relations.schnorr.instance",
        ],
        {
            "fs": {
                "challenge_occurrence": "challenge.c",
                "domain": "schnorr.fs.challenge.v0",
                "sample_failure": "SamplingFailure",
                "space": "uniform-scalar",
                "transcript_influence": ["statement.Y", "message.A"],
            },
            "occurrences": [
                {"id": "message.A", "kind": "Receive", "value_type": "Group"},
                {"id": "challenge.c", "kind": "Challenge", "value_type": "Scalar"},
                {"id": "response.z", "kind": "Receive", "value_type": "Scalar"},
                {"id": "check.schnorr-equation", "kind": "Check"},
                {"id": "terminal.accept", "kind": "Terminal"},
            ],
        },
    )
    protocol = node(
        "pir.protocol.schnorr-fs",
        "Protocol",
        "f1r-manual-canonical-fiat-shamir-v0",
        ["pir.core.schnorr-fs"],
        {
            "challenge_interpretation": "CanonicalFiatShamir",
            "core": "pir.core.schnorr-fs",
            "execution": {
                "failure_precedence": [
                    "MalformedInput",
                    "SamplingFailure",
                    "CheckRejected",
                    "Accepted",
                ],
                "order": [
                    "message.A",
                    "challenge.c",
                    "response.z",
                    "check.schnorr-equation",
                    "terminal.accept",
                ],
                "terminal": "terminal.accept",
            },
            "regime": "FiatShamir",
        },
    )
    correspondence = node(
        "relations.schnorr.fs-correspondence",
        "ProtocolRelationCorrespondence",
        "f1r-manual-fs-schnorr-correspondence-v0",
        ["pir.protocol.schnorr-fs", "relations.schnorr.instance"],
        {
            "acceptance_check": "check.schnorr-equation",
            "direction": "FSProtocolAcceptsIffVerifierRelation",
            "transcript_boundary": "before-challenge.c",
        },
    )
    nodes.extend([core, protocol, correspondence])
    roots = [
        "pir.core.schnorr-fs",
        "pir.protocol.schnorr-fs",
        "relations.schnorr.fs-correspondence",
        "relations.schnorr.instance",
    ]
    return nodes, roots


def read(
    coordinate: str,
    source_node: str,
    source_pointer: str,
    value_kind: str,
    requires: Iterable[str] = (),
) -> dict[str, Json]:
    return {
        "coordinate": coordinate,
        "source_node": source_node,
        "source_pointer": source_pointer,
        "value_kind": value_kind,
        "requires": sorted(requires),
    }


def contract_body(
    semantic_profile: str,
    nodes: list[dict[str, Json]],
    roots: list[str],
    reads: list[dict[str, Json]],
    read_roots: list[str],
    protected_observations: dict[str, list[str]],
) -> dict[str, Json]:
    by_coordinate = {str(item["coordinate"]): item for item in nodes}
    requirements = [
        {
            "coordinate": coordinate,
            "kind": by_coordinate[coordinate]["kind"],
            "profile": by_coordinate[coordinate]["profile"],
        }
        for coordinate in sorted(roots)
    ]
    return {
        "contract_schema": CONTRACT_SCHEMA,
        "excluded_support_kinds": [
            "CausalCapability",
            "ConfidentialValue",
            "MutablePlanState",
            "SecretWitnessValue",
        ],
        "finite_controls": {
            "max_auth_nodes": 128,
            "max_depth": 64,
            "max_reads": 512,
            "max_wire_bytes": 1048576,
        },
        "package_schema": FORMAT,
        "protected_observations": {
            observation: sorted(protected_observations[observation])
            for observation in sorted(protected_observations)
        },
        "read_catalog": sorted(reads, key=lambda item: str(item["coordinate"])),
        "read_roots": sorted(read_roots),
        "root_requirements": requirements,
        "semantic_profile": semantic_profile,
    }


def fresh_contract(
    nodes: list[dict[str, Json]], roots: list[str]
) -> dict[str, Json]:
    core = "pir.core.schnorr-fresh"
    protocol = "pir.protocol.schnorr-fresh"
    reads = [
        read(
            "view.claim-reduction.challenge-uses",
            core,
            "/body/claim_reduction/challenge_uses",
            "OccurrenceIdSequence",
        ),
        read(
            "view.claim-reduction.check-uses",
            core,
            "/body/claim_reduction/check_uses",
            "OccurrenceIdSequence",
        ),
        read(
            "view.claim-reduction.input-claim",
            core,
            "/body/claim_reduction/input_claim",
            "ClaimCoordinate",
        ),
        read(
            "view.claim-reduction.output-claim",
            core,
            "/body/claim_reduction/output_claim",
            "ClaimCoordinate",
            [
                "view.claim-reduction.challenge-uses",
                "view.claim-reduction.check-uses",
                "view.claim-reduction.input-claim",
            ],
        ),
        read(
            "view.effect.occurrences",
            core,
            "/body/occurrences",
            "EffectSequence",
        ),
        read(
            "view.execution.failure-precedence",
            protocol,
            "/body/execution/failure_precedence",
            "FailurePrecedence",
        ),
        read(
            "view.execution.order",
            protocol,
            "/body/execution/order",
            "OccurrenceOrder",
        ),
        read(
            "view.execution.terminal",
            protocol,
            "/body/execution/terminal",
            "TerminalCoordinate",
            ["view.execution.failure-precedence", "view.execution.order"],
        ),
        read(
            "view.protocol.challenge-interpretation",
            protocol,
            "/body/challenge_interpretation",
            "ChallengeInterpretation",
            ["view.protocol.core", "view.protocol.regime"],
        ),
        read(
            "view.protocol.core",
            protocol,
            "/body/core",
            "CoreCoordinate",
        ),
        read(
            "view.protocol.regime",
            protocol,
            "/body/regime",
            "ProtocolRegime",
        ),
        read(
            "view.public-binding.statement-coordinate",
            core,
            "/body/interface/public_bindings/0/coordinate",
            "PublicBindingCoordinate",
        ),
        read(
            "view.public-binding.statement-type",
            core,
            "/body/interface/public_bindings/0/type",
            "TypeCoordinate",
            ["view.public-binding.statement-coordinate"],
        ),
        read(
            "view.public-coin.challenge-dependencies",
            core,
            "/body/challenge/dependencies",
            "OccurrenceDependencySequence",
        ),
        read(
            "view.public-coin.challenge-domain",
            core,
            "/body/challenge/domain",
            "ChallengeDomain",
        ),
        read(
            "view.public-coin.challenge-occurrence",
            core,
            "/body/challenge/occurrence",
            "OccurrenceId",
        ),
        read(
            "view.public-coin.challenge-sharing",
            core,
            "/body/challenge/sharing",
            "ChallengeSharing",
            [
                "view.public-coin.challenge-dependencies",
                "view.public-coin.challenge-domain",
                "view.public-coin.challenge-occurrence",
                "view.public-coin.challenge-space",
            ],
        ),
        read(
            "view.public-coin.challenge-space",
            core,
            "/body/challenge/space",
            "ChallengeSpace",
        ),
        read(
            "view.relation.definition-equation",
            "relations.schnorr.definition",
            "/body/equation",
            "RelationEquation",
        ),
        read(
            "view.relation.instance-roles",
            "relations.schnorr.instance",
            "/body/roles",
            "RelationRoleMap",
        ),
        read(
            "view.relation.model-roles",
            "relations.schnorr.model",
            "/body",
            "RelationModel",
        ),
        read(
            "view.relation.protocol-correspondence",
            "relations.schnorr.fresh-correspondence",
            "/body/role_map",
            "ProtocolRelationMap",
            [
                "view.relation.definition-equation",
                "view.relation.instance-roles",
                "view.relation.model-roles",
            ],
        ),
    ]
    return contract_body(
        "f1r-manual-fresh-public-coin-v0",
        nodes,
        roots,
        reads,
        [
            "view.claim-reduction.output-claim",
            "view.effect.occurrences",
            "view.execution.terminal",
            "view.protocol.challenge-interpretation",
            "view.public-binding.statement-type",
            "view.public-coin.challenge-sharing",
            "view.relation.protocol-correspondence",
        ],
        {
            "ChallengeCorrelation": [
                "view.claim-reduction.challenge-uses",
                "view.protocol.challenge-interpretation",
                "view.public-coin.challenge-dependencies",
                "view.public-coin.challenge-domain",
                "view.public-coin.challenge-occurrence",
                "view.public-coin.challenge-sharing",
                "view.public-coin.challenge-space",
            ],
            "FailurePrecedence": ["view.execution.failure-precedence"],
            "OccurrenceIdentity": [
                "view.effect.occurrences",
                "view.protocol.core",
            ],
            "OccurrenceOrder": ["view.execution.order"],
            "PublicBinding": [
                "view.public-binding.statement-coordinate",
                "view.public-binding.statement-type",
            ],
            "RelationRoleMap": [
                "view.claim-reduction.check-uses",
                "view.claim-reduction.input-claim",
                "view.claim-reduction.output-claim",
                "view.relation.definition-equation",
                "view.relation.instance-roles",
                "view.relation.model-roles",
                "view.relation.protocol-correspondence",
            ],
            "TerminalMeaning": [
                "view.execution.terminal",
                "view.protocol.regime",
            ],
        },
    )


def shared_contract(
    nodes: list[dict[str, Json]], roots: list[str]
) -> dict[str, Json]:
    core = "pir.core.schnorr-shared"
    protocol = "pir.protocol.schnorr-shared"
    reads = [
        read(
            "view.effect.occurrences",
            core,
            "/body/occurrences",
            "EffectSequence",
        ),
        read(
            "view.execution.order",
            protocol,
            "/body/execution/order",
            "OccurrenceOrder",
        ),
        read(
            "view.reduction.A.challenge",
            core,
            "/body/reductions/0/challenge_occurrence",
            "OccurrenceId",
        ),
        read(
            "view.reduction.B.challenge",
            core,
            "/body/reductions/1/challenge_occurrence",
            "OccurrenceId",
        ),
        read(
            "view.shared-challenge.binding",
            core,
            "/body/shared_challenge",
            "SharedChallengeBinding",
            [
                "view.effect.occurrences",
                "view.execution.order",
                "view.reduction.A.challenge",
                "view.reduction.B.challenge",
            ],
        ),
    ]
    return contract_body(
        "f1r-manual-fresh-shared-challenge-v0",
        nodes,
        roots,
        reads,
        ["view.shared-challenge.binding"],
        {
            "ChallengeCorrelation": [
                "view.reduction.A.challenge",
                "view.reduction.B.challenge",
                "view.shared-challenge.binding",
            ],
            "Interleaving": ["view.execution.order"],
            "OccurrenceIdentity": ["view.effect.occurrences"],
            "OccurrenceOrder": ["view.execution.order"],
            "SharedChallengeIdentity": [
                "view.reduction.A.challenge",
                "view.reduction.B.challenge",
                "view.shared-challenge.binding",
            ],
        },
    )


def fs_contract(
    nodes: list[dict[str, Json]], roots: list[str]
) -> dict[str, Json]:
    core = "pir.core.schnorr-fs"
    protocol = "pir.protocol.schnorr-fs"
    reads = [
        read(
            "view.effect.occurrences",
            core,
            "/body/occurrences",
            "EffectSequence",
        ),
        read(
            "view.execution.failure-precedence",
            protocol,
            "/body/execution/failure_precedence",
            "FailurePrecedence",
        ),
        read(
            "view.execution.order",
            protocol,
            "/body/execution/order",
            "OccurrenceOrder",
        ),
        read(
            "view.fs.challenge.domain",
            core,
            "/body/fs/domain",
            "ChallengeDomain",
        ),
        read(
            "view.fs.challenge.sampling-failure",
            core,
            "/body/fs/sample_failure",
            "FailureKind",
            [
                "view.effect.occurrences",
                "view.execution.failure-precedence",
                "view.execution.order",
                "view.fs.challenge.domain",
                "view.fs.challenge.space",
                "view.fs.transcript.influence.commitment",
                "view.fs.transcript.influence.statement",
                "view.protocol.challenge-interpretation",
            ],
        ),
        read(
            "view.fs.challenge.space",
            core,
            "/body/fs/space",
            "ChallengeSpace",
        ),
        read(
            "view.fs.transcript.influence.commitment",
            core,
            "/body/fs/transcript_influence/1",
            "TranscriptInputCoordinate",
        ),
        read(
            "view.fs.transcript.influence.statement",
            core,
            "/body/fs/transcript_influence/0",
            "TranscriptInputCoordinate",
        ),
        read(
            "view.protocol.challenge-interpretation",
            protocol,
            "/body/challenge_interpretation",
            "ChallengeInterpretation",
            ["view.protocol.regime"],
        ),
        read(
            "view.protocol.regime",
            protocol,
            "/body/regime",
            "ProtocolRegime",
        ),
    ]
    return contract_body(
        "f1r-manual-canonical-fiat-shamir-v0",
        nodes,
        roots,
        reads,
        ["view.fs.challenge.sampling-failure"],
        {
            "ChallengeDomain": [
                "view.fs.challenge.domain",
                "view.fs.challenge.space",
                "view.protocol.challenge-interpretation",
                "view.protocol.regime",
            ],
            "FailurePrecedence": ["view.execution.failure-precedence"],
            "OccurrenceIdentity": ["view.effect.occurrences"],
            "OccurrenceOrder": ["view.execution.order"],
            "SamplingFailure": ["view.fs.challenge.sampling-failure"],
            "TranscriptInfluence": [
                "view.fs.transcript.influence.commitment",
                "view.fs.transcript.influence.statement",
            ],
        },
    )


def seal_nodes(raw_nodes: list[dict[str, Json]]) -> list[dict[str, Json]]:
    by_coordinate = {str(item["coordinate"]): item for item in raw_nodes}
    memo: dict[str, str] = {}
    active: set[str] = set()

    def compute(coordinate: str) -> str:
        if coordinate in memo:
            return memo[coordinate]
        if coordinate in active:
            raise ValueError(f"cyclic producer fixture at {coordinate}")
        active.add(coordinate)
        current = by_coordinate[coordinate]
        dependencies = [
            {"coordinate": dependency, "id": compute(dependency)}
            for dependency in current["dependencies"]
        ]
        preimage: dict[str, Json] = {
            "body": current["body"],
            "coordinate": current["coordinate"],
            "dependencies": dependencies,
            "kind": current["kind"],
            "profile": current["profile"],
        }
        result = value_id(AUTH_DOMAIN, preimage)
        active.remove(coordinate)
        memo[coordinate] = result
        return result

    sealed: list[dict[str, Json]] = []
    for coordinate in sorted(by_coordinate):
        current = copy.deepcopy(by_coordinate[coordinate])
        current["asserted_id"] = compute(coordinate)
        sealed.append(current)
    return sealed


def read_closure(contract: dict[str, Json]) -> list[str]:
    catalog = {
        str(item["coordinate"]): item for item in contract["read_catalog"]
    }
    seen: set[str] = set()
    active: set[str] = set()

    def visit(coordinate: str) -> None:
        if coordinate in seen:
            return
        if coordinate in active:
            raise ValueError(f"cyclic read fixture at {coordinate}")
        active.add(coordinate)
        for dependency in catalog[coordinate]["requires"]:
            visit(str(dependency))
        active.remove(coordinate)
        seen.add(coordinate)

    for root in contract["read_roots"]:
        visit(str(root))
    return sorted(seen)


def pointer_select(node_value: dict[str, Json], pointer: str) -> Json:
    current: Json = node_value
    if pointer == "":
        return current
    for token in pointer.split("/")[1:]:
        token = token.replace("~1", "/").replace("~0", "~")
        if isinstance(current, dict):
            current = current[token]
        elif isinstance(current, list):
            current = current[int(token)]
        else:
            raise KeyError(pointer)
    return copy.deepcopy(current)


def form_package(
    raw_nodes: list[dict[str, Json]],
    roots: list[str],
    contract_body_value: dict[str, Json],
) -> dict[str, Json]:
    sealed = seal_nodes(raw_nodes)
    nodes = {str(item["coordinate"]): item for item in sealed}
    contract_id = value_id(CONTRACT_DOMAIN, contract_body_value)
    contract: dict[str, Json] = {
        "asserted_id": contract_id,
        "body": copy.deepcopy(contract_body_value),
    }
    catalog = {
        str(item["coordinate"]): item
        for item in contract_body_value["read_catalog"]
    }
    manifest = read_closure(contract_body_value)
    projection: list[dict[str, Json]] = []
    ledger: list[dict[str, Json]] = []
    for coordinate in manifest:
        row = catalog[coordinate]
        source_node = str(row["source_node"])
        source_pointer = str(row["source_pointer"])
        source = nodes[source_node]
        value = pointer_select(
            {"body": source["body"]},
            source_pointer,
        )
        projection.append(
            {
                "coordinate": coordinate,
                "source_node": source_node,
                "source_pointer": source_pointer,
                "value": value,
                "value_kind": row["value_kind"],
            }
        )
        ledger.append(
            {
                "coordinate": coordinate,
                "source_node": source_node,
                "source_pointer": source_pointer,
            }
        )
    package: dict[str, Json] = {
        "authentication": {"nodes": sealed, "roots": sorted(roots)},
        "contract": contract,
        "format": FORMAT,
        "ledger": ledger,
        "manifest": manifest,
        "projection": projection,
        "semantic_profile": contract_body_value["semantic_profile"],
    }
    package["asserted_package_id"] = value_id(PACKAGE_DOMAIN, package)
    return package


def reseal_package(package: dict[str, Json]) -> dict[str, Json]:
    result = copy.deepcopy(package)
    result.pop("asserted_package_id", None)
    result["asserted_package_id"] = value_id(PACKAGE_DOMAIN, result)
    return result


def reseal_contract_and_package(package: dict[str, Json]) -> dict[str, Json]:
    result = copy.deepcopy(package)
    contract = result["contract"]
    contract["asserted_id"] = value_id(CONTRACT_DOMAIN, contract["body"])
    return reseal_package(result)


def remove_read(package: dict[str, Json], coordinate: str) -> dict[str, Json]:
    result = copy.deepcopy(package)
    result["manifest"] = [
        item for item in result["manifest"] if item != coordinate
    ]
    result["projection"] = [
        item
        for item in result["projection"]
        if item["coordinate"] != coordinate
    ]
    result["ledger"] = [
        item for item in result["ledger"] if item["coordinate"] != coordinate
    ]
    return reseal_package(result)


def append_read(
    package: dict[str, Json],
    coordinate: str,
    source_node: str,
    source_pointer: str,
    value_kind: str,
) -> dict[str, Json]:
    result = copy.deepcopy(package)
    nodes = {
        str(item["coordinate"]): item
        for item in result["authentication"]["nodes"]
    }
    value = pointer_select(
        {"body": nodes[source_node]["body"]},
        source_pointer,
    )
    result["manifest"].append(coordinate)
    result["manifest"].sort()
    result["projection"].append(
        {
            "coordinate": coordinate,
            "source_node": source_node,
            "source_pointer": source_pointer,
            "value": value,
            "value_kind": value_kind,
        }
    )
    result["projection"].sort(key=lambda item: str(item["coordinate"]))
    result["ledger"].append(
        {
            "coordinate": coordinate,
            "source_node": source_node,
            "source_pointer": source_pointer,
        }
    )
    result["ledger"].sort(key=lambda item: str(item["coordinate"]))
    return reseal_package(result)


def replace_projection_value(
    package: dict[str, Json], coordinate: str, value: Json
) -> dict[str, Json]:
    result = copy.deepcopy(package)
    for row in result["projection"]:
        if row["coordinate"] == coordinate:
            row["value"] = copy.deepcopy(value)
            return reseal_package(result)
    raise KeyError(coordinate)


def build_corpus() -> tuple[dict[str, dict[str, Json]], dict[str, str]]:
    fresh_raw, fresh_roots = fresh_nodes()
    shared_raw, shared_roots = shared_nodes()
    fs_raw, fs_roots = fs_nodes()
    fresh = form_package(
        fresh_raw,
        fresh_roots,
        fresh_contract(fresh_raw, fresh_roots),
    )
    shared = form_package(
        shared_raw,
        shared_roots,
        shared_contract(shared_raw, shared_roots),
    )
    fs = form_package(
        fs_raw,
        fs_roots,
        fs_contract(fs_raw, fs_roots),
    )

    root_body = copy.deepcopy(fresh)
    for item in root_body["authentication"]["nodes"]:
        if item["coordinate"] == "pir.core.schnorr-fresh":
            item["body"]["challenge"]["domain"] = "attacker.challenge.v0"
            break
    root_body = reseal_package(root_body)

    phantom = append_read(
        fresh,
        "view.provider.phantom",
        "pir.core.schnorr-fresh",
        "/body/challenge/space",
        "ChallengeSpace",
    )

    alias = copy.deepcopy(shared)
    for row in alias["projection"]:
        if row["coordinate"] == "view.reduction.B.challenge":
            row["source_pointer"] = "/body/reductions/0/challenge_occurrence"
            break
    for row in alias["ledger"]:
        if row["coordinate"] == "view.reduction.B.challenge":
            row["source_pointer"] = "/body/reductions/0/challenge_occurrence"
            break
    alias = reseal_package(alias)

    duplicated_challenge = replace_projection_value(
        shared,
        "view.shared-challenge.binding",
        {
            "consumers": ["reduction.A", "reduction.B"],
            "draws": [
                {"occurrence": "challenge.A", "sample_symbol": "c"},
                {"occurrence": "challenge.B", "sample_symbol": "c"},
            ],
            "sharing": "IndependentEqualValues",
        },
    )

    reordered = copy.deepcopy(shared)
    order = next(
        row
        for row in reordered["projection"]
        if row["coordinate"] == "view.execution.order"
    )
    order["value"][0], order["value"][1] = order["value"][1], order["value"][0]
    reordered = reseal_package(reordered)

    cross_profile = copy.deepcopy(fresh)
    cross_profile["semantic_profile"] = "f1r-manual-canonical-fiat-shamir-v0"
    cross_profile = reseal_package(cross_profile)

    confidential = append_read(
        fresh,
        "view.owner-local.witness-x",
        "relations.schnorr.instance",
        "/body/roles/witness",
        "ConfidentialValue",
    )
    capability = append_read(
        fresh,
        "view.owner-local.strategy-call",
        "pir.protocol.schnorr-fresh",
        "/body/regime",
        "CausalCapability",
    )

    retained_package_id = copy.deepcopy(fresh)
    retained_package_id["ledger"][0]["source_pointer"] = "/body/not-the-source"

    uncovered = copy.deepcopy(fresh)
    uncovered_reads = uncovered["contract"]["body"]["protected_observations"][
        "TerminalMeaning"
    ]
    uncovered_reads.remove("view.protocol.regime")
    uncovered = reseal_contract_and_package(uncovered)

    contract_alias = copy.deepcopy(shared)
    for row in contract_alias["contract"]["body"]["read_catalog"]:
        if row["coordinate"] == "view.reduction.B.challenge":
            row["source_pointer"] = "/body/reductions/0/challenge_occurrence"
            break
    for collection in (contract_alias["projection"], contract_alias["ledger"]):
        for row in collection:
            if row["coordinate"] == "view.reduction.B.challenge":
                row["source_pointer"] = "/body/reductions/0/challenge_occurrence"
                break
    contract_alias = reseal_contract_and_package(contract_alias)

    dormant = copy.deepcopy(fresh)
    dormant["contract"]["body"]["read_catalog"].append(
        {
            "coordinate": "view.dormant.unreached",
            "requires": [],
            "source_node": "pir.core.schnorr-fresh",
            "source_pointer": "/body/challenge/domain",
            "value_kind": "ChallengeDomain",
        }
    )
    dormant["contract"]["body"]["read_catalog"].sort(
        key=lambda row: str(row["coordinate"])
    )
    dormant = reseal_contract_and_package(dormant)

    packages = {
        "aliased-contract-source": contract_alias,
        "cross-profile-replay": cross_profile,
        "dormant-read-catalog": dormant,
        "duplicate-shared-challenge": duplicated_challenge,
        "equal-typed-coordinate-alias": alias,
        "fresh-positive": fresh,
        "fs-positive": fs,
        "omit-fs-transcript-input": remove_read(
            fs, "view.fs.transcript.influence.commitment"
        ),
        "omit-order-dependency": remove_read(fresh, "view.execution.order"),
        "phantom-provider-read": phantom,
        "reorder-interleaved-occurrences": reordered,
        "retained-package-id": retained_package_id,
        "root-body-retained-id": root_body,
        "serialize-causal-capability": capability,
        "serialize-confidential-value": confidential,
        "shared-positive": shared,
        "uncovered-protected-read": uncovered,
    }
    duplicate_key = json.dumps(
        fresh,
        ensure_ascii=True,
        indent=2,
        sort_keys=True,
    )
    duplicate_key = duplicate_key.replace(
        "{\n",
        f'{{\n  "format": "{FORMAT}",\n',
        1,
    )
    raw = {"duplicate-json-key": duplicate_key + "\n"}
    return packages, raw


def write_corpus(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    packages, raw = build_corpus()
    for name, package in packages.items():
        encoded = json.dumps(
            package,
            ensure_ascii=True,
            indent=2,
            sort_keys=False,
        )
        (output / f"{name}.json").write_text(encoded + "\n", encoding="ascii")
    for name, text in raw.items():
        (output / f"{name}.json").write_text(text, encoding="ascii")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    write_corpus(args.output)
    print(f"wrote F1-R corpus to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
