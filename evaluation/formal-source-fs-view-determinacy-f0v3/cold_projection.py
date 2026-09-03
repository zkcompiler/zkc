"""Cold projections from inert witness records, without importing witness models."""

from __future__ import annotations

import hashlib
import json
from typing import Any

from support import algorithm_use, body, law, raw_body, record, ref, variant


class ColdProjectionError(ValueError):
    """An inert witness record did not have the selected finite shape."""


def _ordered_unique(values: list[dict[str, str]]) -> list[dict[str, str]]:
    return sorted(
        {json.dumps(value, sort_keys=True): value for value in values}.values(),
        key=lambda value: json.dumps(value, sort_keys=True),
    )


def _scope(scope: dict[str, Any]) -> dict[int, Any]:
    if set(scope) != {"name", "parent", "open_before"}:
        raise ColdProjectionError("cold K2 scope has another shape")
    return record(
        ref("scope-ref-body-v0", scope["name"]),
        variant(0) if scope["parent"] is None else variant(1, ref("scope-ref-body-v0", scope["parent"])),
        (
            variant(0)
            if scope["open_before"] is None
            else variant(1, ref("occurrence-ref-body-v0", scope["open_before"]))
        ),
    )


def k2_values(raw: dict[str, Any]) -> dict[str, Any]:
    if set(raw) != {
        "name",
        "ids",
        "construction",
        "inputs",
        "scopes",
        "schedule",
        "additions",
        "result",
    }:
        raise ColdProjectionError("cold K2 carrier has another outer shape")
    ids = raw["ids"]
    construction = raw["construction"]
    if set(ids) != {"core", "construction", "fresh_protocol", "fs_protocol"}:
        raise ColdProjectionError("cold K2 identifier set differs")
    if set(construction) != {
        "application_domain",
        "sample_bytes",
        "max_attempts",
        "state_bytes",
        "version",
        "initial_state",
    }:
        raise ColdProjectionError("cold K2 construction has another shape")
    cid = raw_body("core-id-body-v0", bytes.fromhex(ids["core"]))
    tid = raw_body("transcript-construction-id-body-v0", bytes.fromhex(ids["construction"]))
    schedule = raw["schedule"]
    schedule_value = [
        record(
            index,
            ref("occurrence-ref-body-v0", item["name"]),
            ref("occurrence-kind-body-v0", item["kind"]),
        )
        for index, item in enumerate(schedule)
    ]
    challenges = [
        (index, item)
        for index, item in enumerate(schedule)
        if item["kind"] == "challenge"
    ]
    influence_entries = []
    for index, challenge in challenges:
        prior_atoms = [
            record(
                ref("occurrence-ref-body-v0", prior["name"]),
                [ref("occurrence-kind-body-v0", kind) for kind in prior["influence_kinds"]],
                prior["guard_nontrivial"],
            )
            for prior in schedule[:index]
            if prior["influence_kinds"]
        ]
        influence_entries.append(
            record(ref("challenge-ref-body-v0", challenge["name"]), prior_atoms)
        )
    additions_by_challenge = {
        item["challenge"]: item["publications"] for item in raw["additions"]
    }
    additions = [
        record(
            ref("challenge-ref-body-v0", challenge["name"]),
            [
                ref("value-ref-body-v0", name)
                for name in additions_by_challenge[challenge["name"]]
            ],
        )
        for _index, challenge in challenges
    ]
    influence_kinds = _ordered_unique(
        [
            ref("occurrence-kind-body-v0", kind)
            for item in schedule
            for kind in item["influence_kinds"]
        ]
    )
    if not influence_kinds:
        raise ColdProjectionError("cold K2 carrier has no influence constructor")
    transcript = record(
        tid,
        cid,
        ref("value-type-body-v0", f"Bytes[{construction['state_bytes']}]"),
        ref("value-type-body-v0", "Bytes"),
        body("canonical-value-body-v0", construction["initial_state"]),
        law("canonical-framed", "canonical-framed-body-grammar-v0"),
        algorithm_use(construction["version"] + ":absorb", "k2-absorb-contract-v1"),
        algorithm_use(construction["version"] + ":squeeze", "k2-squeeze-contract-v1"),
        algorithm_use(construction["version"] + ":advance", "k2-advance-contract-v1"),
        body("protocol-declaration-ref-body-v0", construction["application_domain"]),
        ref("semantic-failure-type-body-v0", "SamplingExhausted"),
        law("canonical-framed", "canonical-framed-source-views-v0"),
        schedule_value,
    )
    influence = record(
        tid,
        cid,
        influence_kinds,
        [_scope(scope) for scope in raw["scopes"]],
        influence_entries,
        additions,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
    )
    transition = record(
        tid,
        cid,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
        record(
            algorithm_use("big-endian-rejection-accept-v1", "k2-accept-contract-v1"),
            [ref("value-type-body-v0", "Bytes"), ref("value-type-body-v0", "Natural")],
            ref("value-type-body-v0", "Boolean"),
        ),
        record(
            algorithm_use("big-endian-rejection-decode-v1", "k2-decode-contract-v1"),
            [ref("value-type-body-v0", "Bytes"), ref("value-type-body-v0", "Natural")],
            ref("value-type-body-v0", "Natural"),
        ),
        record(construction["sample_bytes"], construction["max_attempts"]),
        law("canonical-framed", "canonical-framed-body-grammar-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        [
            record(ref("challenge-ref-body-v0", item["name"]), index)
            for index, item in challenges
        ],
    )
    result = raw["result"]
    result_value = record(
        body("runtime-schema-body-v0", "CheckedFSConstruction"),
        raw_body("protocol-id-body-v0", bytes.fromhex(ids["fresh_protocol"])),
        raw_body("protocol-id-body-v0", bytes.fromhex(ids["fs_protocol"])),
        cid,
        tid,
        [
            record(ref("occurrence-ref-body-v0", left), ref("occurrence-ref-body-v0", right))
            for left, right in result["occurrence_map"]
        ],
        [
            record(ref("value-ref-body-v0", left), ref("value-ref-body-v0", right))
            for left, right in result["value_map"]
        ],
        [
            record(ref("challenge-ref-body-v0", left), ref("challenge-ref-body-v0", right))
            for left, right in result["challenge_map"]
        ],
        record(
            variant(0),
            law("canonical-framed", "canonical-framed-same-core-construction-v0"),
        ),
    )
    return {
        "CanonicalTranscriptDeclarationView": transcript,
        "CanonicalRequiredInfluenceView": influence,
        "CanonicalChallengeTransitionView": transition,
        "CanonicalFSConstructionView": result_value,
    }


def _canonical_json(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _framed_hash(domain: str, parts: tuple[bytes, ...]) -> str:
    digest = hashlib.sha256()
    encoded_domain = domain.encode("ascii")
    digest.update(len(encoded_domain).to_bytes(8, "big"))
    digest.update(encoded_domain)
    for part in parts:
        digest.update(len(part).to_bytes(8, "big"))
        digest.update(part)
    return "sha256:" + digest.hexdigest()


def _semantic_id(kind: str, value: Any) -> str:
    return _framed_hash(
        "zkc.semantic." + kind,
        (b"semantic-regime:duplex-sponge-evaluation", _canonical_json(value)),
    )


def duplex_values(raw: dict[str, Any]) -> dict[str, Any]:
    if set(raw) != {"schema", "core", "construction"}:
        raise ColdProjectionError("cold duplex fixture has another outer shape")
    core = raw["core"]
    declaration = raw["construction"]
    if declaration["core_id"] != _semantic_id("pir.interactive-core", core):
        raise ColdProjectionError("cold duplex Core identity differs")
    cid_text = declaration["core_id"]
    tid_text = _semantic_id("pir.transcript-construction", declaration)
    cid = body("core-id-body-v0", cid_text)
    tid = body("transcript-construction-id-body-v0", tid_text)
    bindings = [
        ref("binding-ref-body-v0", item["name"])
        for item in core["initial_bindings"]
    ]
    messages = [item for item in core["schedule"] if item["kind"] == "ProverMessage"]
    challenges = [item for item in core["schedule"] if item["kind"] == "Challenge"]
    schedule = [
        record(index, ref("occurrence-ref-body-v0", item["name"]), ref("occurrence-kind-body-v0", item["kind"]))
        for index, item in enumerate(core["schedule"])
    ]
    salt_coordinate = record(variant(0), 0)
    material_schema = record(
        salt_coordinate,
        ref("value-type-body-v0", "Sigma5Sequence"),
        declaration["salt_length"],
    )
    message_entries = [
        record(
            ref("occurrence-ref-body-v0", item["occurrence"]),
            algorithm_use(item["codec"] + ":" + item["algorithm"], "duplex-message-codec-contract-v0"),
            item["encoded_length"],
        )
        for item in declaration["message_codecs"]
    ]
    transcript = record(
        tid,
        cid,
        variant(0),
        ref("value-type-body-v0", "Sigma5"),
        body("canonical-value-body-v0", 0),
        declaration["rate"],
        declaration["capacity"],
        record(
            ref("value-type-body-v0", "DuplexState<Sigma5,rate=3,capacity=2>"),
            law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        ),
        record(
            ref("value-type-body-v0", f"BinaryInstance<{declaration['instance_bit_bound']}>"),
            law("duplex-sponge", "duplex-sponge-body-grammar-v0"),
        ),
        record(bindings, law("duplex-sponge", "duplex-sponge-source-views-v0")),
        algorithm_use("StartHash:" + declaration["provider_interface"][0], "duplex-start-contract-v0"),
        algorithm_use("ForwardPermutation:" + declaration["provider_interface"][1], "duplex-permutation-contract-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        material_schema,
        message_entries,
        record(
            [
                record(ref("occurrence-ref-body-v0", item["name"]), ref("value-type-body-v0", item["value_type"]))
                for item in messages
            ],
            [
                record(ref("challenge-ref-body-v0", item["name"]), ref("value-type-body-v0", item["value_type"]))
                for item in challenges
            ],
        ),
        schedule,
        schedule,
        record(
            len(core["schedule"]),
            sum(item["encoded_length"] for item in declaration["message_codecs"]),
            sum(item["squeeze_length"] for item in declaration["challenge_decoders"]),
        ),
    )
    coverage_entries = []
    prior_messages = []
    for item in core["schedule"]:
        if item["kind"] == "ProverMessage":
            prior_messages.append(item)
        elif item["kind"] == "Challenge":
            atoms = [variant(0, binding) for binding in bindings]
            atoms.append(variant(1, salt_coordinate))
            atoms.extend(
                variant(2, ref("occurrence-ref-body-v0", message["name"]))
                for message in prior_messages
            )
            coverage_entries.append(record(ref("challenge-ref-body-v0", item["name"]), atoms))
    coverage = record(
        tid,
        cid,
        bindings,
        salt_coordinate,
        coverage_entries,
        [ref("occurrence-ref-body-v0", item["name"]) for item in messages],
        [ref("challenge-ref-body-v0", item["name"]) for item in challenges],
        law("duplex-sponge", "duplex-sponge-prover-required-prefix-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        [],
    )
    decoder_entries = [
        record(
            ref("challenge-ref-body-v0", item["occurrence"]),
            item["squeeze_length"],
            algorithm_use(item["decoder"] + ":" + item["algorithm"], "duplex-decoder-contract-v0"),
        )
        for item in declaration["challenge_decoders"]
    ]
    transition = record(
        tid,
        cid,
        decoder_entries,
        law("duplex-sponge", "duplex-sponge-admission-and-execution-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        variant(0),
        variant(0),
        variant(0),
        [ref("challenge-ref-body-v0", item["name"]) for item in challenges],
        [ref("challenge-ref-body-v0", item["name"]) for item in challenges],
        [
            record(ref("challenge-ref-body-v0", item["name"]), ref("occurrence-ref-body-v0", item["name"]), index)
            for index, item in enumerate(challenges)
        ],
    )
    return {
        "DuplexTranscriptDeclarationView": transcript,
        "DuplexEncodedInputCoverageView": coverage,
        "DuplexChallengeTransitionView": transition,
    }
