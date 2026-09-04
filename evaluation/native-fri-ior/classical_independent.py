"""Independent public replay for the exact classical FRI control.

This module deliberately reimplements closed-term framing, Fiat--Shamir
sampling, Goldilocks arithmetic, Merkle authentication, occurrence coverage,
and the three fold equations.  It imports identity-bearing constants and
semantic subjects from :mod:`friiormodel.classical`, but never calls that
module's generators, transcript operations, commitment operations, fold
operation, or verifiers.

An affirmative result is one finite public replay result.  It is not a FRI
proximity theorem, a commitment-security result, a Fiat--Shamir theorem, or a
general correspondence claim between implementations.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import hmac
from typing import Any

from friiormodel.classical import (
    DEFAULT_CLASSICAL_LIMITS,
    DIGEST_BYTES,
    DOMAIN_GENERATORS,
    DOMAIN_ORDERS,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_COMMITMENT_PROFILE,
    EXACT_CLASSICAL_FRI_PROFILE,
    FOLD_ROUNDS,
    FS_FOLD_DOMAIN,
    FS_FOLD_LABELS,
    FS_PREFIX_SCHEMA,
    FS_QUERY_DOMAIN,
    FS_QUERY_LABELS,
    GOLDILOCKS_MODULUS,
    LAYER_QUERY_OCCURRENCES,
    LEAF_HASH_DOMAIN,
    MAX_FS_SAMPLER_ATTEMPTS,
    NODE_HASH_DOMAIN,
    PUBLIC_INPUT_SCHEMA,
    PUBLIC_PROOF_SCHEMA,
    QUERY_REPETITIONS,
    SALT_BYTES,
)


MAX_TERM_BYTES = 1 << 16
MAX_TERM_NODES = 2048
MAX_TERM_DEPTH = 24
MAX_OPENINGS = LAYER_QUERY_OCCURRENCES

RESOURCE_FIELDS = (
    "field_operations",
    "hash_calls",
    "hash_bytes",
    "merkle_nodes",
    "transcript_frames",
    "sampler_attempts",
    "grinding_trials",
    "logical_query_occurrences",
    "unique_openings",
    "proof_bytes",
)
DEFAULT_LIMITS = {
    name: getattr(DEFAULT_CLASSICAL_LIMITS, name) for name in RESOURCE_FIELDS
}


class _ReplayFailure(Exception):
    def __init__(self, outcome: str, boundary: str, code: str, detail: str) -> None:
        super().__init__(code)
        self.outcome = outcome
        self.boundary = boundary
        self.code = code
        self.detail = detail


def _fail(outcome: str, boundary: str, code: str, detail: str) -> None:
    raise _ReplayFailure(outcome, boundary, code, detail)


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        _fail(
            "Malformed",
            "classical-independent:term-encoding",
            "FRI-IOR-CLASSICAL-INDEPENDENT-001",
            "a canonical length lies outside the unsigned 64-bit range",
        )
    return value.to_bytes(8, "big")


def canonical_term_bytes(value: Any) -> bytes:
    """Independently encode one bounded exact-JSON closed finite term."""

    nodes = 0

    def over_bytes() -> None:
        _fail(
            "DeterministicLimitExceeded",
            "classical-independent:term-encoding",
            "FRI-IOR-CLASSICAL-INDEPENDENT-002",
            "the closed term exceeds its canonical byte bound",
        )

    def extend(target: bytearray, addition: bytes) -> None:
        if len(target) + len(addition) > MAX_TERM_BYTES:
            over_bytes()
        target.extend(addition)

    def encode(current: Any, depth: int) -> bytes:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES or depth > MAX_TERM_DEPTH:
            _fail(
                "DeterministicLimitExceeded",
                "classical-independent:term-encoding",
                "FRI-IOR-CLASSICAL-INDEPENDENT-003",
                "the closed term exceeds its node or depth bound",
            )

        if current is None:
            result = b"N"
        elif current is False:
            result = b"F"
        elif current is True:
            result = b"T"
        elif type(current) is int:
            magnitude = abs(current)
            width = max(1, (magnitude.bit_length() + 7) // 8)
            if 10 + width > MAX_TERM_BYTES:
                over_bytes()
            body = b"\x00" if magnitude == 0 else magnitude.to_bytes(width, "big")
            result = b"I" + (b"+" if current >= 0 else b"-") + _u64(width) + body
        elif type(current) is str:
            body = current.encode("utf-8")
            if 9 + len(body) > MAX_TERM_BYTES:
                over_bytes()
            result = b"S" + _u64(len(body)) + body
        elif type(current) is list:
            if len(current) > MAX_TERM_NODES:
                _fail(
                    "DeterministicLimitExceeded",
                    "classical-independent:term-encoding",
                    "FRI-IOR-CLASSICAL-INDEPENDENT-003",
                    "the closed term exceeds its node bound",
                )
            encoded = bytearray(b"L" + _u64(len(current)))
            for child_value in current:
                child = encode(child_value, depth + 1)
                extend(encoded, _u64(len(child)))
                extend(encoded, child)
            result = bytes(encoded)
        elif type(current) is dict:
            if len(current) > MAX_TERM_NODES or not all(
                type(key) is str for key in current
            ):
                _fail(
                    "Malformed",
                    "classical-independent:term-encoding",
                    "FRI-IOR-CLASSICAL-INDEPENDENT-004",
                    "closed maps require bounded exact text keys",
                )
            keys = [(key.encode("utf-8"), key) for key in current]
            if sum(len(encoded) for encoded, _ in keys) > MAX_TERM_BYTES:
                over_bytes()
            encoded = bytearray(b"M" + _u64(len(keys)))
            for _, key in sorted(keys):
                key_body = encode(key, depth + 1)
                value_body = encode(current[key], depth + 1)
                extend(encoded, _u64(len(key_body)))
                extend(encoded, key_body)
                extend(encoded, _u64(len(value_body)))
                extend(encoded, value_body)
            result = bytes(encoded)
        else:
            _fail(
                "Malformed",
                "classical-independent:term-encoding",
                "FRI-IOR-CLASSICAL-INDEPENDENT-005",
                "the replay accepts exact JSON carrier types only",
            )
        if len(result) > MAX_TERM_BYTES:
            over_bytes()
        return result

    return encode(value, 0)


def _same_term(first: Any, second: Any) -> bool:
    return hmac.compare_digest(canonical_term_bytes(first), canonical_term_bytes(second))


def _object(value: Any, keys: set[str], boundary: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-006",
            "a public object has missing, extra, or wrong-kind members",
        )
    return value


def _array(value: Any, boundary: str) -> list[Any]:
    if type(value) is not list:
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-007",
            "a public sequence must use the JSON array carrier",
        )
    return value


def _bounded_int(value: Any, minimum: int, maximum: int, boundary: str) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-008",
            "an integer is outside its exact canonical range",
        )
    return value


def _field(value: Any, boundary: str) -> int:
    return _bounded_int(value, 0, GOLDILOCKS_MODULUS - 1, boundary)


def _hex(value: Any, width: int, boundary: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 2 * width
        or any(character not in "0123456789abcdef" for character in value)
    ):
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-009",
            "a byte string is not canonical lowercase hexadecimal",
        )
    return bytes.fromhex(value)


def _bounded_hex(
    value: Any,
    *,
    minimum: int,
    maximum: int,
    boundary: str,
) -> bytes:
    if (
        type(value) is not str
        or len(value) % 2 != 0
        or not 2 * minimum <= len(value) <= 2 * maximum
        or any(character not in "0123456789abcdef" for character in value)
    ):
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-010",
            "a variable-length byte string is not canonical bounded hexadecimal",
        )
    return bytes.fromhex(value)


class _Counter:
    def __init__(self, limits: dict[str, int]) -> None:
        self.limits = dict(limits)
        self.used = {name: 0 for name in RESOURCE_FIELDS}

    def reserve(self, **charges: int) -> None:
        if set(charges) - set(RESOURCE_FIELDS) or any(
            type(value) is not int or value < 0 for value in charges.values()
        ):
            raise RuntimeError("invalid independent resource charge")
        proposed = {
            name: self.used[name] + charges.get(name, 0) for name in RESOURCE_FIELDS
        }
        if any(proposed[name] > self.limits[name] for name in RESOURCE_FIELDS):
            _fail(
                "DeterministicLimitExceeded",
                "classical-independent:resources",
                "FRI-IOR-CLASSICAL-INDEPENDENT-090",
                "the replay would exceed a selected resource limit",
            )
        self.used = proposed

    def hash(self, payload: bytes, *, merkle: bool = False) -> bytes:
        self.reserve(
            hash_calls=1,
            hash_bytes=len(payload),
            merkle_nodes=1 if merkle else 0,
        )
        return hashlib.sha256(payload).digest()

    def snapshot(self) -> dict[str, int]:
        return dict(self.used)


def _select_limits(candidate: Any) -> dict[str, int]:
    if candidate is None:
        return dict(DEFAULT_LIMITS)
    if type(candidate) is not dict or set(candidate) != set(RESOURCE_FIELDS):
        _fail(
            "Malformed",
            "classical-independent:resources",
            "FRI-IOR-CLASSICAL-INDEPENDENT-091",
            "limits must name every resource dimension exactly once",
        )
    selected: dict[str, int] = {}
    for name in RESOURCE_FIELDS:
        value = candidate[name]
        if type(value) is not int or value < 0:
            _fail(
                "Malformed",
                "classical-independent:resources",
                "FRI-IOR-CLASSICAL-INDEPENDENT-092",
                "every resource limit must be a non-negative integer",
            )
        selected[name] = value
    return selected


def _add(left: int, right: int) -> int:
    return (left + right) % GOLDILOCKS_MODULUS


def _sub(left: int, right: int) -> int:
    return (left - right) % GOLDILOCKS_MODULUS


def _mul(left: int, right: int) -> int:
    return (left * right) % GOLDILOCKS_MODULUS


def _inverse(value: int) -> int:
    if value == 0:
        _fail(
            "Refused",
            "classical-independent:fold",
            "FRI-IOR-CLASSICAL-INDEPENDENT-050",
            "a fold attempted to invert zero",
        )
    return pow(value, GOLDILOCKS_MODULUS - 2, GOLDILOCKS_MODULUS)


def _fold(point: int, positive: int, negative: int, challenge: int, counter: _Counter) -> int:
    """Evaluate the binary even/odd fold without producer arithmetic."""

    counter.reserve(field_operations=8)
    half = _mul(_add(positive, negative), _inverse(2))
    odd = _mul(_sub(positive, negative), _inverse(_mul(2, point)))
    return _add(half, _mul(challenge, odd))


@dataclass(frozen=True, slots=True)
class _Opening:
    layer: int
    pair_index: int
    positive: int
    negative: int
    salt: bytes
    authentication_path: tuple[bytes, ...]


@dataclass(frozen=True, slots=True)
class _Selector:
    query_ordinal: int
    layer: int
    opening_index: int


def _parse_root(value: Any, expected_layer: int) -> bytes:
    boundary = "classical-independent:proof-formation"
    root = _object(
        value,
        {"layer", "digest", "commitment_profile_id"},
        boundary,
    )
    if _bounded_int(root["layer"], 0, FOLD_ROUNDS - 1, boundary) != expected_layer:
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-011",
            "the three roots must retain exact layer order",
        )
    if not _same_term(
        root["commitment_profile_id"],
        EXACT_CLASSICAL_COMMITMENT_PROFILE.identity.to_term(),
    ):
        _fail(
            "Unsupported",
            "classical-independent:commitment-profile",
            "FRI-IOR-CLASSICAL-INDEPENDENT-012",
            "a root selects an unsupported commitment profile",
        )
    return _hex(root["digest"], DIGEST_BYTES, boundary)


def _parse_opening(value: Any) -> _Opening:
    boundary = "classical-independent:proof-formation"
    opening = _object(
        value,
        {
            "layer",
            "pair_index",
            "positive",
            "negative",
            "salt",
            "authentication_path",
            "commitment_profile_id",
        },
        boundary,
    )
    layer = _bounded_int(opening["layer"], 0, FOLD_ROUNDS - 1, boundary)
    pair_index = _bounded_int(
        opening["pair_index"],
        0,
        DOMAIN_ORDERS[layer] // 2 - 1,
        boundary,
    )
    if not _same_term(
        opening["commitment_profile_id"],
        EXACT_CLASSICAL_COMMITMENT_PROFILE.identity.to_term(),
    ):
        _fail(
            "Unsupported",
            "classical-independent:commitment-profile",
            "FRI-IOR-CLASSICAL-INDEPENDENT-013",
            "an opening selects an unsupported commitment profile",
        )
    path = _array(opening["authentication_path"], boundary)
    if len(path) > 6:
        _fail(
            "Malformed",
            boundary,
            "FRI-IOR-CLASSICAL-INDEPENDENT-014",
            "an authentication path exceeds the finite carrier bound",
        )
    return _Opening(
        layer=layer,
        pair_index=pair_index,
        positive=_field(opening["positive"], boundary),
        negative=_field(opening["negative"], boundary),
        salt=_hex(opening["salt"], SALT_BYTES, boundary),
        authentication_path=tuple(
            _hex(item, DIGEST_BYTES, boundary) for item in path
        ),
    )


def _parse_selector(value: Any) -> _Selector:
    boundary = "classical-independent:proof-formation"
    selector = _object(
        value,
        {"occurrence_ordinal", "opening_index"},
        boundary,
    )
    ordinal = _bounded_int(
        selector["occurrence_ordinal"],
        0,
        LAYER_QUERY_OCCURRENCES - 1,
        boundary,
    )
    return _Selector(
        query_ordinal=ordinal // FOLD_ROUNDS,
        layer=ordinal % FOLD_ROUNDS,
        opening_index=_bounded_int(
            selector["opening_index"], 0, MAX_OPENINGS - 1, boundary
        ),
    )


def _parse_public_terms(
    public_inputs: Any,
    proof: Any,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Validate and decode the exact JSON-compatible public carriers."""

    inputs_bytes = canonical_term_bytes(public_inputs)
    proof_bytes = canonical_term_bytes(proof)
    inputs = _object(
        public_inputs,
        {
            "schema",
            "profile_id",
            "committed_core_id",
            "statement",
            "application_context",
        },
        "classical-independent:public-input-formation",
    )
    if inputs["schema"] != PUBLIC_INPUT_SCHEMA:
        _fail(
            "Malformed",
            "classical-independent:public-input-formation",
            "FRI-IOR-CLASSICAL-INDEPENDENT-015",
            "the public-input schema is unsupported",
        )
    if not _same_term(
        inputs["profile_id"], EXACT_CLASSICAL_FRI_PROFILE.identity.to_term()
    ):
        _fail(
            "Unsupported",
            "classical-independent:profile-admission",
            "FRI-IOR-CLASSICAL-INDEPENDENT-016",
            "the public input selects an unsupported classical FRI profile",
        )
    expected_core = EXACT_CLASSICAL_COMMITTED_CORE.identity.to_term()
    if not _same_term(inputs["committed_core_id"], expected_core):
        _fail(
            "Unsupported",
            "classical-independent:core-admission",
            "FRI-IOR-CLASSICAL-INDEPENDENT-017",
            "the public input selects an unsupported committed Core",
        )
    statement = _bounded_hex(
        inputs["statement"],
        minimum=1,
        maximum=1 << 14,
        boundary="classical-independent:public-input-formation",
    )
    application_context = _bounded_hex(
        inputs["application_context"],
        minimum=1,
        maximum=1 << 14,
        boundary="classical-independent:public-input-formation",
    )

    public_proof = _object(
        proof,
        {
            "schema",
            "committed_core_id",
            "roots",
            "terminal_scalar",
            "opening_table",
            "occurrence_selectors",
        },
        "classical-independent:proof-formation",
    )
    if public_proof["schema"] != PUBLIC_PROOF_SCHEMA:
        _fail(
            "Malformed",
            "classical-independent:proof-formation",
            "FRI-IOR-CLASSICAL-INDEPENDENT-018",
            "the public-proof schema is unsupported",
        )
    if not _same_term(public_proof["committed_core_id"], expected_core):
        _fail(
            "Unsupported",
            "classical-independent:core-admission",
            "FRI-IOR-CLASSICAL-INDEPENDENT-019",
            "the proof selects an unsupported committed Core",
        )
    roots_value = _array(
        public_proof["roots"], "classical-independent:proof-formation"
    )
    openings_value = _array(
        public_proof["opening_table"], "classical-independent:proof-formation"
    )
    selectors_value = _array(
        public_proof["occurrence_selectors"],
        "classical-independent:proof-formation",
    )
    if (
        len(roots_value) != FOLD_ROUNDS
        or len(openings_value) > MAX_OPENINGS
        or len(selectors_value) != LAYER_QUERY_OCCURRENCES
    ):
        _fail(
            "Malformed",
            "classical-independent:proof-formation",
            "FRI-IOR-CLASSICAL-INDEPENDENT-020",
            "a proof sequence has the wrong exact finite cardinality",
        )
    parsed_inputs = {
        "statement": statement,
        "application_context": application_context,
        "canonical_byte_length": len(inputs_bytes),
        "term": public_inputs,
        "committed_core_id_term": inputs["committed_core_id"],
    }
    parsed_proof = {
        "roots": tuple(
            _parse_root(root, layer) for layer, root in enumerate(roots_value)
        ),
        "root_terms": tuple(roots_value),
        "terminal_scalar": _field(
            public_proof["terminal_scalar"],
            "classical-independent:proof-formation",
        ),
        "opening_table": tuple(_parse_opening(item) for item in openings_value),
        "selectors": tuple(_parse_selector(item) for item in selectors_value),
        "canonical_byte_length": len(proof_bytes),
    }
    return parsed_inputs, parsed_proof


def _fs_prefix(
    inputs: dict[str, Any],
    root_terms: tuple[dict[str, Any], ...],
    fold_challenges: tuple[int, ...],
    terminal_scalar: int | None,
    *,
    purpose: str,
    label: str,
    attempt: int,
) -> dict[str, Any]:
    return {
        "schema": FS_PREFIX_SCHEMA,
        "public_inputs": inputs["term"],
        "committed_core_id": inputs["committed_core_id_term"],
        "purpose": purpose,
        "label": label,
        "roots": list(root_terms),
        "fold_challenges": list(fold_challenges),
        "terminal_scalar": terminal_scalar,
        "attempt": attempt,
    }


def _derive_fiat_shamir_values(
    inputs: dict[str, Any],
    proof: dict[str, Any],
    counter: _Counter,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    challenges: list[int] = []
    root_terms: tuple[dict[str, Any], ...] = proof["root_terms"]
    for layer, label in enumerate(FS_FOLD_LABELS):
        for attempt in range(MAX_FS_SAMPLER_ATTEMPTS):
            prefix = _fs_prefix(
                inputs,
                root_terms[: layer + 1],
                tuple(challenges),
                None,
                purpose="fold-challenge",
                label=label,
                attempt=attempt,
            )
            payload = FS_FOLD_DOMAIN + canonical_term_bytes(prefix)
            counter.reserve(transcript_frames=1, sampler_attempts=1)
            candidate = int.from_bytes(counter.hash(payload)[:8], "big")
            if candidate < GOLDILOCKS_MODULUS:
                challenges.append(candidate)
                break
        else:
            _fail(
                "DeterministicLimitExceeded",
                "classical-independent:fs-fold-sampling",
                "FRI-IOR-CLASSICAL-INDEPENDENT-021",
                "the bounded canonical field sampler exhausted all attempts",
            )
    challenge_tuple = tuple(challenges)
    query_indices: list[int] = []
    for label in FS_QUERY_LABELS:
        prefix = _fs_prefix(
            inputs,
            root_terms,
            challenge_tuple,
            proof["terminal_scalar"],
            purpose="query-index",
            label=label,
            attempt=0,
        )
        payload = FS_QUERY_DOMAIN + canonical_term_bytes(prefix)
        counter.reserve(transcript_frames=1, sampler_attempts=1)
        query_indices.append(
            counter.hash(payload)[0] & (DOMAIN_ORDERS[0] - 1)
        )
    if len(challenge_tuple) != FOLD_ROUNDS or len(query_indices) != QUERY_REPETITIONS:
        raise RuntimeError("incomplete independent Fiat-Shamir derivation")
    return challenge_tuple, tuple(query_indices)


def _cover_occurrences(
    proof: dict[str, Any],
    query_indices: tuple[int, ...],
    counter: _Counter,
) -> tuple[tuple[_Opening, ...], tuple[dict[str, int], ...]]:
    """Require one exact table and selector for all twelve logical queries."""

    table: tuple[_Opening, ...] = proof["opening_table"]
    keys = tuple((opening.layer, opening.pair_index) for opening in table)
    if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
        _fail(
            "Refused",
            "classical-independent:occurrence-coverage",
            "FRI-IOR-CLASSICAL-INDEPENDENT-030",
            "the opening table is not in strict canonical key order",
        )
    expected: list[dict[str, int]] = []
    for query_ordinal, initial_index in enumerate(query_indices):
        current_index = initial_index
        for layer in range(FOLD_ROUNDS):
            half = DOMAIN_ORDERS[layer] // 2
            pair_index = current_index % half
            expected.append(
                {
                    "ordinal": query_ordinal * FOLD_ROUNDS + layer,
                    "query_ordinal": query_ordinal,
                    "layer": layer,
                    "sampled_index": current_index,
                    "pair_index": pair_index,
                    "parent_index": pair_index,
                }
            )
            current_index = pair_index
    expected_keys = tuple(
        sorted({(item["layer"], item["pair_index"]) for item in expected})
    )
    if keys != expected_keys:
        _fail(
            "Refused",
            "classical-independent:occurrence-coverage",
            "FRI-IOR-CLASSICAL-INDEPENDENT-031",
            "the opening table does not exactly cover all derived layer queries",
        )
    selectors: tuple[_Selector, ...] = proof["selectors"]
    covered: list[_Opening] = []
    for expected_occurrence, selector in zip(expected, selectors, strict=True):
        if (
            selector.query_ordinal != expected_occurrence["query_ordinal"]
            or selector.layer != expected_occurrence["layer"]
            or selector.opening_index >= len(table)
        ):
            _fail(
                "Refused",
                "classical-independent:occurrence-coverage",
                "FRI-IOR-CLASSICAL-INDEPENDENT-032",
                "a selector changed a logical occurrence or points outside the table",
            )
        opening = table[selector.opening_index]
        if opening.layer != expected_occurrence["layer"] or opening.pair_index != (
            expected_occurrence["pair_index"]
        ):
            _fail(
                "Refused",
                "classical-independent:occurrence-coverage",
                "FRI-IOR-CLASSICAL-INDEPENDENT-033",
                "a selector does not name its derived layer opening",
            )
        covered.append(opening)
    counter.reserve(
        logical_query_occurrences=LAYER_QUERY_OCCURRENCES,
        unique_openings=len(table),
        proof_bytes=proof["canonical_byte_length"],
    )
    return tuple(covered), tuple(expected)


def _leaf_hash(opening: _Opening, counter: _Counter) -> bytes:
    payload = (
        LEAF_HASH_DOMAIN
        + bytes((opening.layer,))
        + opening.pair_index.to_bytes(2, "big")
        + opening.positive.to_bytes(8, "big")
        + opening.negative.to_bytes(8, "big")
        + opening.salt
    )
    return counter.hash(payload, merkle=True)


def _authenticate(opening: _Opening, root: bytes, counter: _Counter) -> None:
    expected_depth = (DOMAIN_ORDERS[opening.layer] // 2).bit_length() - 1
    if len(opening.authentication_path) != expected_depth:
        _fail(
            "Refused",
            "classical-independent:opening-authentication",
            "FRI-IOR-CLASSICAL-INDEPENDENT-040",
            "an opening path has the wrong exact depth",
        )
    digest = _leaf_hash(opening, counter)
    running = opening.pair_index
    for sibling in opening.authentication_path:
        if running & 1:
            payload = NODE_HASH_DOMAIN + sibling + digest
        else:
            payload = NODE_HASH_DOMAIN + digest + sibling
        digest = counter.hash(payload, merkle=True)
        running //= 2
    if not hmac.compare_digest(digest, root):
        _fail(
            "Refused",
            "classical-independent:opening-authentication",
            "FRI-IOR-CLASSICAL-INDEPENDENT-041",
            "an opening does not authenticate to its declared single root",
        )


def _selected_value(opening: _Opening, sampled_index: int) -> int:
    half = DOMAIN_ORDERS[opening.layer] // 2
    if sampled_index == opening.pair_index:
        return opening.positive
    if sampled_index == opening.pair_index + half:
        return opening.negative
    _fail(
        "Refused",
        "classical-independent:fold",
        "FRI-IOR-CLASSICAL-INDEPENDENT-050",
        "a next-layer opening does not contain the required sampled value",
    )


def _check_folds(
    covered: tuple[_Opening, ...],
    occurrences: tuple[dict[str, int], ...],
    fold_challenges: tuple[int, ...],
    terminal_scalar: int,
    counter: _Counter,
) -> None:
    points = tuple(
        tuple(
            pow(generator, index, GOLDILOCKS_MODULUS)
            for index in range(DOMAIN_ORDERS[layer])
        )
        for layer, generator in enumerate(DOMAIN_GENERATORS[:FOLD_ROUNDS])
    )
    for ordinal, (opening, occurrence) in enumerate(
        zip(covered, occurrences, strict=True)
    ):
        expected = _fold(
            points[opening.layer][opening.pair_index],
            opening.positive,
            opening.negative,
            fold_challenges[opening.layer],
            counter,
        )
        if opening.layer < FOLD_ROUNDS - 1:
            target_occurrence = occurrences[ordinal + 1]
            target_opening = covered[ordinal + 1]
            if target_occurrence["layer"] != opening.layer + 1:
                raise RuntimeError("non-canonical independent occurrence order")
            target = _selected_value(
                target_opening,
                occurrence["parent_index"],
            )
        else:
            target = terminal_scalar
        if expected != target:
            if opening.layer == 0:
                fold_code = "FRI-IOR-CLASSICAL-INDEPENDENT-051"
            elif opening.layer == 1:
                fold_code = "FRI-IOR-CLASSICAL-INDEPENDENT-052"
            else:
                fold_code = "FRI-IOR-CLASSICAL-INDEPENDENT-053"
            _fail(
                "Refused",
                f"classical-independent:fold-{opening.layer}",
                fold_code,
                "an authenticated binary-fold equation does not match its target",
            )


def _outcome(
    outcome: str,
    boundary: str,
    code: str,
    detail: str,
    counter: _Counter | None,
    selected_limits: dict[str, int] | None,
    **evidence: Any,
) -> dict[str, Any]:
    evidence["resource_usage"] = (
        {name: 0 for name in RESOURCE_FIELDS}
        if counter is None
        else counter.snapshot()
    )
    evidence["selected_limits"] = (
        None if selected_limits is None else dict(selected_limits)
    )
    return {
        "outcome": outcome,
        "boundary": boundary,
        "code": code,
        "detail": detail,
        "subject": None,
        "evidence": evidence,
    }


def verify_public_classical_fri(
    public_inputs: Any,
    proof: Any,
    *,
    limits: Any = None,
) -> dict[str, Any]:
    """Independently replay one exact strong-FS public proof projection."""

    selected_limits: dict[str, int] | None = None
    counter: _Counter | None = None
    try:
        selected_limits = _select_limits(limits)
        counter = _Counter(selected_limits)
        inputs, parsed_proof = _parse_public_terms(public_inputs, proof)
        challenges, query_indices = _derive_fiat_shamir_values(
            inputs,
            parsed_proof,
            counter,
        )
        covered, occurrences = _cover_occurrences(
            parsed_proof,
            query_indices,
            counter,
        )
        for opening in parsed_proof["opening_table"]:
            _authenticate(opening, parsed_proof["roots"][opening.layer], counter)
        _check_folds(
            covered,
            occurrences,
            challenges,
            parsed_proof["terminal_scalar"],
            counter,
        )
        replay_digest = hashlib.sha256(
            b"zkc.classical-fri.independent-public-replay.v1\x00"
            + canonical_term_bytes(public_inputs)
            + canonical_term_bytes(proof)
        ).hexdigest()
        return _outcome(
            "Affirmative",
            "classical-independent:public-replay",
            "FRI-IOR-CLASSICAL-INDEPENDENT-100",
            "the separately coded exact strong-FS public replay accepts",
            counter,
            selected_limits,
            verdict="Accept",
            fold_challenges=list(challenges),
            ordered_initial_domain_indices=list(query_indices),
            query_repetitions=QUERY_REPETITIONS,
            logical_layer_query_occurrences=LAYER_QUERY_OCCURRENCES,
            authenticated_oracle_value_occurrences=2
            * LAYER_QUERY_OCCURRENCES,
            unique_authenticated_openings=len(parsed_proof["opening_table"]),
            fold_checks=LAYER_QUERY_OCCURRENCES,
            proof_bytes=parsed_proof["canonical_byte_length"],
            public_replay_digest=replay_digest,
            establishes_proximity_theorem=False,
            establishes_commitment_binding=False,
            establishes_fiat_shamir_security=False,
            establishes_checker_correspondence=False,
        )
    except _ReplayFailure as error:
        return _outcome(
            error.outcome,
            error.boundary,
            error.code,
            error.detail,
            counter,
            selected_limits,
        )
    except Exception as error:  # pragma: no cover - defensive fail-closed seam
        return _outcome(
            "CheckerFailure",
            "classical-independent:public-replay",
            "FRI-IOR-CLASSICAL-INDEPENDENT-099",
            f"unexpected independent replay failure: {type(error).__name__}",
            counter,
            selected_limits,
        )


__all__ = [
    "DEFAULT_LIMITS",
    "RESOURCE_FIELDS",
    "canonical_term_bytes",
    "verify_public_classical_fri",
]
