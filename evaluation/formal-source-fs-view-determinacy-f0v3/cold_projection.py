"""Cold projections from inert witness records, without importing witness models."""

from __future__ import annotations

import hashlib
import json
from typing import Any

from support import algorithm_use, body, law, raw_body, record, ref, variant


class ColdProjectionError(ValueError):
    """An inert witness record did not have the selected finite shape."""


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


def _framed_occurrence(item: dict[str, Any]) -> bool:
    return (
        item["guard_nontrivial"]
        or item["kind"]
        in {
            "prover-message",
            "verifier-message",
            "oracle-publish",
            "oracle-query",
            "oracle-answer",
        }
        or (item["kind"] == "challenge" and bool(item["dependencies"]))
    )


def _scope_path(scopes: list[dict[str, Any]], name: str) -> list[dict[str, str]]:
    by_name = {item["name"]: item for item in scopes}
    path: list[str] = []
    current: str | None = name
    while current is not None:
        path.append(current)
        current = by_name[current]["parent"]
    return [ref("scope-ref-body-v0", item) for item in reversed(path)]


def _static_atom(tag: int, payload: Any, required: bool) -> dict[int, Any]:
    return record(variant(0, variant(tag, payload)), required)


def _symbolic_draw(challenge: str) -> dict[int, Any]:
    return record(
        variant(1, ref("challenge-ref-body-v0", challenge)),
        True,
    )


def _value_type(raw: dict[str, Any], value_ref: dict[str, str]) -> dict[str, str]:
    if value_ref["kind"] == "input":
        selected = tuple(item for item in raw["inputs"] if item["name"] == value_ref["name"])
        if len(selected) != 1:
            raise ColdProjectionError("cold fixture condition names another input")
        sort = selected[0]["value_sort"]
    else:
        selected = tuple(item for item in raw["schedule"] if item["name"] == value_ref["name"])
        if len(selected) != 1:
            raise ColdProjectionError("cold fixture condition names another occurrence")
        occurrence = selected[0]
        if occurrence["kind"] == "challenge":
            sort = "nat"
        elif occurrence["kind"] == "prover-message":
            sort = occurrence["prover_value_sort"]
        else:
            raise ColdProjectionError("cold fixture condition result type is not represented")
    names = {"bytes": "Bytes", "nat": "Natural", "bool": "Boolean", "oracle": "Oracle"}
    return ref("value-type-body-v0", names[sort])


def _required_entries(raw: dict[str, Any], cid: Any, tid: Any) -> list[dict[int, Any]]:
    scopes = raw["scopes"]
    schedule = raw["schedule"]
    challenges = [
        (index, item)
        for index, item in enumerate(schedule)
        if item["kind"] == "challenge"
    ]
    action_tags = {
        "prover-message": 6,
        "verifier-message": 7,
        "oracle-publish": 8,
        "oracle-query": 9,
        "oracle-answer": 10,
    }
    by_scope = {item["name"]: item for item in scopes}

    def ancestry(scope: str) -> set[str]:
        result: set[str] = set()
        current: str | None = scope
        while current is not None:
            result.add(current)
            current = by_scope[current]["parent"]
        return result

    result = []
    for challenge_index, challenge in challenges:
        required_scopes = ancestry(challenge["scope"])
        entries = [
            _static_atom(0, cid, True),
            _static_atom(1, tid, True),
            _static_atom(
                2,
                body(
                    "protocol-declaration-ref-body-v0",
                    raw["construction"]["application_domain"],
                ),
                True,
            ),
        ]

        def add_scopes(open_before: str | None) -> None:
            for scope in scopes:
                if scope["open_before"] != open_before:
                    continue
                is_required = scope["name"] in required_scopes
                entries.append(
                    _static_atom(3, _scope_path(scopes, scope["name"]), is_required)
                )
                for binding in raw["inputs"]:
                    if binding["scope"] == scope["name"] and binding["role"] != "verifier-private":
                        entries.append(
                            _static_atom(
                                4,
                                ref("binding-ref-body-v0", binding["name"]),
                                is_required,
                            )
                        )

        add_scopes(None)
        for index, occurrence in enumerate(schedule[: challenge_index + 1]):
            add_scopes(occurrence["name"])
            if occurrence["guard_nontrivial"]:
                entries.append(
                    _static_atom(
                        5,
                        ref("occurrence-ref-body-v0", occurrence["name"]),
                        True,
                    )
                )
            if occurrence["kind"] == "challenge":
                entries.extend(
                    _static_atom(
                        11,
                        record(
                            ref("challenge-ref-body-v0", occurrence["name"]),
                            ordinal,
                        ),
                        index == challenge_index,
                    )
                    for ordinal, _dependency in enumerate(occurrence["dependencies"])
                )
                if index < challenge_index:
                    entries.append(_symbolic_draw(occurrence["name"]))
            elif index < challenge_index and occurrence["kind"] in action_tags:
                entries.append(
                    _static_atom(
                        action_tags[occurrence["kind"]],
                        ref("occurrence-ref-body-v0", occurrence["name"]),
                        True,
                    )
                )
        result.append(
            record(ref("challenge-ref-body-v0", challenge["name"]), entries)
        )
    return result


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
        if _framed_occurrence(item)
    ]
    challenges = [
        (index, item)
        for index, item in enumerate(schedule)
        if item["kind"] == "challenge"
    ]
    influence_entries = _required_entries(raw, cid, tid)
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
        [_scope(scope) for scope in raw["scopes"]],
        influence_entries,
        additions,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
    )
    rules = []
    for position, item in challenges:
        input_types = [ref("value-type-body-v0", "Bytes")]
        input_types.extend(_value_type(raw, dependency) for dependency in item["dependencies"])
        rules.append(
            record(
                ref("challenge-ref-body-v0", item["name"]),
                position,
                record(
                    algorithm_use("big-endian-rejection-accept-v1", "k2-accept-contract-v1"),
                    input_types,
                    ref("value-type-body-v0", "Boolean"),
                ),
                record(
                    algorithm_use("big-endian-rejection-decode-v1", "k2-decode-contract-v1"),
                    input_types,
                    ref("value-type-body-v0", "Natural"),
                ),
                record(construction["sample_bytes"], construction["max_attempts"]),
            )
        )
    transition = record(
        tid,
        cid,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
        law("canonical-framed", "canonical-framed-body-grammar-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        rules,
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
    values = {
        "CanonicalTranscriptDeclarationView": transcript,
        "CanonicalRequiredInfluenceView": influence,
        "CanonicalFSConstructionView": result_value,
    }
    values["CanonicalChallengeTransitionView"] = transition
    return values


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
