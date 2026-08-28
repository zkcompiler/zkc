"""Separately coded public replay for one finite committed FRI profile.

This module deliberately depends only on the Python standard library.  Its
input surface is two closed JSON-shaped values: public inputs and a public
proof.  It reconstructs the transcript, work check, ordered query draws,
Merkle authentication, fold equations, and terminal-degree check from those
values alone.

An affirmative outcome is intentionally narrow.  It says that this exact
finite public replay accepted.  It does not establish a proximity theorem,
an outer relation, a knowledge property, or correspondence with another
checker.  Resource limits are request-local validation policy and are kept
out of the transcript and public replay digest.
"""

from __future__ import annotations

import hashlib
import hmac
from types import MappingProxyType
from typing import Any


MODULUS = 97
EXTENSION_NONRESIDUE = 5
DOMAIN_GENERATORS = (8, 64, 22)
DOMAIN_ORDERS = (16, 8, 4)
DOMAIN_NAMES = ("D0", "D1", "D2")
QUERY_COUNT = 4
CAP_SIZE = 2
SALT_BYTES = 16
MAX_AUTHENTICATION_DEPTH = 2
MAX_TERMINAL_COEFFICIENTS = 5
TERMINAL_DEGREE_BOUND_EXCLUSIVE = 2
MAX_OPENING_TABLE_ENTRIES = 8
MAX_TERM_BYTES = 1 << 16
MAX_TERM_NODES = 2048
MAX_TERM_DEPTH = 24
MAX_REJECTION_ATTEMPTS = 64
GRINDING_BITS = 2

_RESOURCE_FIELDS = (
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

DEFAULT_LIMITS = MappingProxyType(
    {
        "field_operations": 1024,
        "hash_calls": 128,
        "hash_bytes": 1 << 15,
        "merkle_nodes": 128,
        "transcript_frames": 128,
        "sampler_attempts": 1024,
        "grinding_trials": 1 << 16,
        "logical_query_occurrences": 64,
        "unique_openings": 64,
        "proof_bytes": 1 << 16,
    }
)

HARD_LIMITS = MappingProxyType(
    {
        "field_operations": 4096,
        "hash_calls": 256,
        "hash_bytes": 1 << 16,
        "merkle_nodes": 256,
        "transcript_frames": 256,
        "sampler_attempts": 4096,
        "grinding_trials": 1 << 20,
        "logical_query_occurrences": 256,
        "unique_openings": 128,
        "proof_bytes": 1 << 20,
    }
)

_GENESIS_DOMAIN = b"zkc.fri-ior.transcript-genesis.v1\x00"
_ABSORB_DOMAIN = b"zkc.fri-ior.transcript-absorb.v1\x00"
_SQUEEZE_DOMAIN = b"zkc.fri-ior.transcript-squeeze.v1\x00"
_QUERY_EXPAND_DOMAIN = b"zkc.fri-ior.query-expand.v1\x00"
_WORK_DOMAIN = b"zkc.fri-ior.work-check.v1\x00"
_LEAF_HASH_DOMAIN = b"zkc.fri-ior.antipodal-leaf.v1\x00"
_NODE_HASH_DOMAIN = b"zkc.fri-ior.merkle-node.v1\x00"

_CLOSED_TERM_CODEC = "closed-finite-term.v1"
_CAP_CODEC = "sha256-two-node-cap.v1"
_TERMINAL_CODEC = "ascending-fp2-coefficients.v1"
_NONCE_CODEC = "u32be.v1"
_FP2_SAMPLER = "sha256-u16be-rejection-fp97-extension2.v1"
_SEED_SAMPLER = "sha256-bytes32.v1"
_QUERY_SAMPLER = "sha256-u16be-low-bits-power-of-two-range.v1"
_WORK_RULE = "sha256-leading-zero-bits.v1"

_STATEMENT_NAMESPACE = "zkc/fri-ior/statement/v1"
_CONTEXT_NAMESPACE = "zkc/fri-ior/application-context/v1"
_CAP0_NAMESPACE = "zkc/fri-ior/cap/0/v1"
_CAP1_NAMESPACE = "zkc/fri-ior/cap/1/v1"
_BETA0_NAMESPACE = "zkc/fri-ior/fold-challenge/0/v1"
_BETA1_NAMESPACE = "zkc/fri-ior/fold-challenge/1/v1"
_TERMINAL_NAMESPACE = "zkc/fri-ior/terminal-polynomial/v1"
_WORK_SEED_NAMESPACE = "zkc/fri-ior/work-seed/v1"
_NONCE_NAMESPACE = "zkc/fri-ior/grinding-nonce/v1"
_WORK_CHECK_NAMESPACE = "zkc/fri-ior/work-check/v1"
_QUERY_SEED_NAMESPACE = "zkc/fri-ior/query-seed/v1"
_QUERY_OCCURRENCES_NAMESPACE = "zkc/fri-ior/query-occurrences/v1"


class _ReplayFailure(Exception):
    def __init__(self, outcome: str, boundary: str, code: str, detail: str) -> None:
        super().__init__(code)
        self.outcome = outcome
        self.boundary = boundary
        self.code = code
        self.detail = detail


def _failure(outcome: str, boundary: str, code: str, detail: str) -> None:
    raise _ReplayFailure(outcome, boundary, code, detail)


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        _failure(
            "Malformed",
            "independent:term-encoding",
            "FRI-IOR-INDEPENDENT-001",
            "a canonical length is outside the unsigned 64-bit range",
        )
    return value.to_bytes(8, "big")


def canonical_term_bytes(value: Any) -> bytes:
    """Encode a bounded JSON value with the witness's closed-term framing.

    The implementation is independent and intentionally accepts exact JSON
    carrier types only: null, booleans, integers, text, arrays, and objects
    with text keys.  Host subclasses and non-JSON byte carriers are rejected.
    """

    nodes = 0

    def over_bytes() -> None:
        _failure(
            "DeterministicLimitExceeded",
            "independent:term-encoding",
            "FRI-IOR-INDEPENDENT-002",
            "the canonical JSON term exceeds its byte bound",
        )

    def extend(target: bytearray, addition: bytes) -> None:
        if len(target) + len(addition) > MAX_TERM_BYTES:
            over_bytes()
        target.extend(addition)

    def encode(current: Any, depth: int) -> bytes:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES or depth > MAX_TERM_DEPTH:
            _failure(
                "DeterministicLimitExceeded",
                "independent:term-encoding",
                "FRI-IOR-INDEPENDENT-003",
                "the canonical JSON term exceeds its node or depth bound",
            )

        if current is None:
            result = b"N"
        elif current is False:
            result = b"F"
        elif current is True:
            result = b"T"
        elif type(current) is int:
            magnitude = abs(current)
            body_length = max(1, (magnitude.bit_length() + 7) // 8)
            if 10 + body_length > MAX_TERM_BYTES:
                over_bytes()
            body = b"\x00" if magnitude == 0 else magnitude.to_bytes(body_length, "big")
            result = b"I" + (b"+" if current >= 0 else b"-") + _u64(len(body)) + body
        elif type(current) is str:
            encoded_text = current.encode("utf-8")
            if 9 + len(encoded_text) > MAX_TERM_BYTES:
                over_bytes()
            result = b"S" + _u64(len(encoded_text)) + encoded_text
        elif type(current) is list:
            if len(current) > MAX_TERM_NODES:
                _failure(
                    "DeterministicLimitExceeded",
                    "independent:term-encoding",
                    "FRI-IOR-INDEPENDENT-003",
                    "the canonical JSON term exceeds its node bound",
                )
            encoded = bytearray(b"L" + _u64(len(current)))
            for child_value in current:
                child = encode(child_value, depth + 1)
                extend(encoded, _u64(len(child)))
                extend(encoded, child)
            result = bytes(encoded)
        elif type(current) is dict:
            if len(current) > MAX_TERM_NODES:
                _failure(
                    "DeterministicLimitExceeded",
                    "independent:term-encoding",
                    "FRI-IOR-INDEPENDENT-003",
                    "the canonical JSON term exceeds its node bound",
                )
            if not all(type(key) is str for key in current):
                _failure(
                    "Malformed",
                    "independent:term-encoding",
                    "FRI-IOR-INDEPENDENT-004",
                    "canonical JSON objects require exact text keys",
                )
            encoded_keys: list[tuple[bytes, str]] = []
            key_bytes_total = 0
            for key in current:
                key_bytes = key.encode("utf-8")
                key_bytes_total += len(key_bytes)
                if key_bytes_total > MAX_TERM_BYTES:
                    over_bytes()
                encoded_keys.append((key_bytes, key))
            encoded = bytearray(b"M" + _u64(len(encoded_keys)))
            for _, key in sorted(encoded_keys):
                key_body = encode(key, depth + 1)
                value_body = encode(current[key], depth + 1)
                extend(encoded, _u64(len(key_body)))
                extend(encoded, key_body)
                extend(encoded, _u64(len(value_body)))
                extend(encoded, value_body)
            result = bytes(encoded)
        else:
            _failure(
                "Malformed",
                "independent:term-encoding",
                "FRI-IOR-INDEPENDENT-005",
                "the public replay surface accepts exact JSON carrier types only",
            )

        if len(result) > MAX_TERM_BYTES:
            over_bytes()
        return result

    return encode(value, 0)


def _exact_profile() -> dict[str, Any]:
    domains = [
        {
            "name": name,
            "generator": generator,
            "order": order,
            "point_order": "successive-generator-powers",
            "pairing": "first-half-index-with-index-plus-half-order",
        }
        for name, generator, order in zip(
            DOMAIN_NAMES, DOMAIN_GENERATORS, DOMAIN_ORDERS, strict=True
        )
    ]
    return {
        "name": "zkc.fri-ior.f97-binary-two-round.v1",
        "field": {
            "modulus": MODULUS,
            "primitive_generator": 5,
            "extension": {"degree": 2, "polynomial": [-5, 0, 1]},
        },
        "domains": domains,
        "folding_arity": 2,
        "initial_degree_bound_exclusive": 8,
        "terminal_representation": {
            "max_coefficient_count": MAX_TERMINAL_COEFFICIENTS,
            "zero_polynomial": "one-zero-coefficient",
            "nonzero_polynomial": "final-coefficient-must-be-nonzero",
        },
        "terminal_degree_bound_exclusive": TERMINAL_DEGREE_BOUND_EXCLUSIVE,
        "round_count": 2,
        "ordered_query_count": QUERY_COUNT,
        "query_occurrences_preserve_order_and_multiplicity": True,
        "commitment": {
            "hash": "sha256",
            "salt_bytes": SALT_BYTES,
            "cap_size": CAP_SIZE,
            "leaf_layout": "ordered-antipodal-evaluation-pair",
        },
    }


def _step(
    kind: str,
    occurrence: str,
    namespace: str,
    codec: str,
    sampler: str | None,
    feeds_state: bool,
    protected: list[str],
) -> dict[str, Any]:
    return {
        "kind": kind,
        "occurrence": occurrence,
        "namespace": namespace,
        "codec": codec,
        "sampler": sampler,
        "feeds_transcript_state": feeds_state,
        "protected_occurrences": protected,
    }


def _exact_plan() -> dict[str, Any]:
    return {
        "model": "FriIorTypedSha256FiatShamir.v1",
        "profile_name": "zkc.fri-ior.f97-binary-two-round.v1",
        "profile_id": {
            "kind": "SemanticId",
            "version": 1,
            "subject_kind": "fri-ior-profile",
            "domain": "fri-ior.profile.v1",
            "semantic_regime": (
                "zkc.fri-ior.closed-finite-term.v1.sha256."
                "ef96aaf009ec016e122fb2135d1b8f104ee539eb463a5e35109b9e7bbbc52cd4"
            ),
            "digest": "65be87b5873b968cee3a04f53d2a8fb0fb87af2f27121c941064dce76d2e19a3",
        },
        "hash_suite": "sha256.v1",
        "framing": "typed-length-delimited-big-endian.v1",
        "grinding_bits": GRINDING_BITS,
        "grinding_nonce_bytes": 4,
        "grinding_search_attempt_bound": 256,
        "rejection_attempt_bound": MAX_REJECTION_ATTEMPTS,
        "query_domain_size": DOMAIN_ORDERS[0],
        "query_count": QUERY_COUNT,
        "steps": [
            _step(
                "AbsorbPublication",
                "statement",
                _STATEMENT_NAMESPACE,
                _CLOSED_TERM_CODEC,
                None,
                True,
                ["fold-challenge[0]", "fold-challenge[1]", "work-seed", "query-seed"],
            ),
            _step(
                "AbsorbPublication",
                "application-context",
                _CONTEXT_NAMESPACE,
                _CLOSED_TERM_CODEC,
                None,
                True,
                ["fold-challenge[0]", "fold-challenge[1]", "work-seed", "query-seed"],
            ),
            _step(
                "AbsorbPublication",
                "cap[0]",
                _CAP0_NAMESPACE,
                _CAP_CODEC,
                None,
                True,
                ["fold-challenge[0]", "fold-challenge[1]", "work-seed", "query-seed"],
            ),
            _step(
                "DeriveChallenge",
                "fold-challenge[0]",
                _BETA0_NAMESPACE,
                "fp97-extension2-u8-pair.v1",
                _FP2_SAMPLER,
                True,
                ["fold-challenge[1]", "work-seed", "query-seed"],
            ),
            _step(
                "AbsorbPublication",
                "cap[1]",
                _CAP1_NAMESPACE,
                _CAP_CODEC,
                None,
                True,
                ["fold-challenge[1]", "work-seed", "query-seed"],
            ),
            _step(
                "DeriveChallenge",
                "fold-challenge[1]",
                _BETA1_NAMESPACE,
                "fp97-extension2-u8-pair.v1",
                _FP2_SAMPLER,
                True,
                ["work-seed", "query-seed"],
            ),
            _step(
                "AbsorbPublication",
                "terminal-polynomial",
                _TERMINAL_NAMESPACE,
                _TERMINAL_CODEC,
                None,
                True,
                ["work-seed", "query-seed"],
            ),
            _step(
                "DeriveChallenge",
                "work-seed",
                _WORK_SEED_NAMESPACE,
                "bytes32.v1",
                _SEED_SAMPLER,
                True,
                ["work-check", "query-seed"],
            ),
            _step(
                "AbsorbPublication",
                "grinding-nonce",
                _NONCE_NAMESPACE,
                _NONCE_CODEC,
                None,
                True,
                ["work-check", "query-seed"],
            ),
            _step(
                "CheckWork",
                "work-check",
                _WORK_CHECK_NAMESPACE,
                "bytes32.v1",
                _WORK_RULE,
                False,
                ["query-seed"],
            ),
            _step(
                "DeriveChallenge",
                "query-seed",
                _QUERY_SEED_NAMESPACE,
                "bytes32.v1",
                _SEED_SAMPLER,
                True,
                ["query-occurrences"],
            ),
            _step(
                "SampleOccurrences",
                "query-occurrences",
                _QUERY_OCCURRENCES_NAMESPACE,
                "u16be-low-bits-initial-domain-index.v1",
                _QUERY_SAMPLER,
                False,
                [],
            ),
        ],
    }


class _Counter:
    def __init__(self, selected: dict[str, int]) -> None:
        self.limits = selected
        self.used = {name: 0 for name in _RESOURCE_FIELDS}

    def reserve(self, **charges: int) -> None:
        proposed = {
            name: self.used[name] + charges.get(name, 0) for name in _RESOURCE_FIELDS
        }
        if any(proposed[name] > self.limits[name] for name in _RESOURCE_FIELDS):
            _failure(
                "DeterministicLimitExceeded",
                "independent:resources",
                "FRI-IOR-INDEPENDENT-090",
                "the replay would exceed a selected resource limit",
            )
        self.used = proposed

    def hash(self, payload: bytes, *, merkle_node: bool = False) -> bytes:
        self.reserve(
            hash_calls=1,
            hash_bytes=len(payload),
            merkle_nodes=1 if merkle_node else 0,
        )
        return hashlib.sha256(payload).digest()

    def snapshot(self) -> dict[str, int]:
        return dict(self.used)


def _selected_limits(candidate: Any) -> dict[str, int]:
    if candidate is None:
        return dict(DEFAULT_LIMITS)
    if type(candidate) is not dict or set(candidate) != set(_RESOURCE_FIELDS):
        _failure(
            "Malformed",
            "independent:resources",
            "FRI-IOR-INDEPENDENT-091",
            "limits must be one exact JSON object over all resource dimensions",
        )
    selected: dict[str, int] = {}
    for name in _RESOURCE_FIELDS:
        value = candidate[name]
        if type(value) is not int or value < 0:
            _failure(
                "Malformed",
                "independent:resources",
                "FRI-IOR-INDEPENDENT-092",
                "every selected resource limit must be a non-negative integer",
            )
        if value > HARD_LIMITS[name]:
            _failure(
                "DeterministicLimitExceeded",
                "independent:resources",
                "FRI-IOR-INDEPENDENT-093",
                "a selected resource limit exceeds the verifier hard cap",
            )
        selected[name] = value
    return selected


def _require_object(value: Any, keys: set[str], boundary: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-006",
            "a public object has missing, extra, or wrong-kind members",
        )
    return value


def _require_list(value: Any, boundary: str) -> list[Any]:
    if type(value) is not list:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-007",
            "a public sequence must use the JSON array carrier",
        )
    return value


def _hex_bytes(value: Any, byte_count: int, boundary: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 2 * byte_count
        or any(character not in "0123456789abcdef" for character in value)
    ):
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-008",
            "a hexadecimal byte string is not in its exact canonical form",
        )
    return bytes.fromhex(value)


def _parse_fp2(value: Any, boundary: str) -> tuple[int, int]:
    encoded = _require_list(value, boundary)
    if (
        len(encoded) != 2
        or any(type(coordinate) is not int for coordinate in encoded)
        or any(not 0 <= coordinate < MODULUS for coordinate in encoded)
    ):
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-009",
            "an extension-field element must be two canonical F_97 integers",
        )
    return (encoded[0], encoded[1])


def _parse_cap(value: Any, boundary: str) -> tuple[bytes, bytes]:
    cap = _require_object(value, {"hash", "cap_size", "nodes"}, boundary)
    nodes = _require_list(cap["nodes"], boundary)
    if cap["hash"] != "sha256" or cap["cap_size"] != CAP_SIZE or len(nodes) != CAP_SIZE:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-010",
            "the exact profile requires a two-node SHA-256 cap",
        )
    return (_hex_bytes(nodes[0], 32, boundary), _hex_bytes(nodes[1], 32, boundary))


def _parse_terminal(value: Any) -> tuple[tuple[int, int], ...]:
    boundary = "independent:proof-formation"
    terminal = _require_object(value, {"coefficient_order", "coefficients"}, boundary)
    coefficients = _require_list(terminal["coefficients"], boundary)
    if (
        terminal["coefficient_order"] != "ascending"
        or not 1 <= len(coefficients) <= MAX_TERMINAL_COEFFICIENTS
    ):
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-011",
            "the terminal polynomial has a wrong order or coefficient count",
        )
    parsed = tuple(_parse_fp2(item, boundary) for item in coefficients)
    if len(parsed) > 1 and parsed[-1] == (0, 0):
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-012",
            "a nonzero canonical polynomial cannot have a trailing zero coefficient",
        )
    return parsed


def _parse_opening(value: Any) -> dict[str, Any]:
    boundary = "independent:proof-formation"
    opening = _require_object(
        value,
        {
            "domain",
            "pair_index",
            "positive",
            "negative",
            "salt",
            "authentication_path",
        },
        boundary,
    )
    if type(opening["domain"]) is not str:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-013",
            "opening domain is not text",
        )
    pair_index = opening["pair_index"]
    if type(pair_index) is not int or pair_index < 0:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-014",
            "opening index is not non-negative",
        )
    path_values = _require_list(opening["authentication_path"], boundary)
    if len(path_values) > MAX_AUTHENTICATION_DEPTH:
        _failure(
            "Malformed",
            boundary,
            "FRI-IOR-INDEPENDENT-015",
            "authentication path is too deep",
        )
    return {
        "domain": opening["domain"],
        "pair_index": pair_index,
        "positive": _parse_fp2(opening["positive"], boundary),
        "negative": _parse_fp2(opening["negative"], boundary),
        "salt": _hex_bytes(opening["salt"], SALT_BYTES, boundary),
        "authentication_path": tuple(
            _hex_bytes(item, 32, boundary) for item in path_values
        ),
    }


def _parse_public_values(
    public_inputs: Any, proof: Any
) -> tuple[dict[str, Any], dict[str, Any]]:
    canonical_term_bytes(public_inputs)
    canonical_term_bytes(proof)
    inputs = _require_object(
        public_inputs,
        {"schema", "profile", "transcript_plan", "statement", "application_context"},
        "independent:public-input-formation",
    )
    if inputs["schema"] != "zkc.fri-ior.committed-public-inputs.v1":
        _failure(
            "Malformed",
            "independent:public-input-formation",
            "FRI-IOR-INDEPENDENT-016",
            "the public-input schema is unsupported or malformed",
        )
    if inputs["profile"] != _exact_profile():
        _failure(
            "Unsupported",
            "independent:profile-admission",
            "FRI-IOR-INDEPENDENT-017",
            "the public input does not select the one exact finite profile",
        )
    if inputs["transcript_plan"] != _exact_plan():
        _failure(
            "Unsupported",
            "independent:plan-admission",
            "FRI-IOR-INDEPENDENT-018",
            "the public input does not select the one exact transcript plan",
        )

    public_proof = _require_object(
        proof,
        {
            "schema",
            "cap0",
            "cap1",
            "terminal_polynomial",
            "grinding_nonce",
            "opening_table",
            "occurrence_selectors",
        },
        "independent:proof-formation",
    )
    if public_proof["schema"] != "zkc.fri-ior.public-proof.v1":
        _failure(
            "Malformed",
            "independent:proof-formation",
            "FRI-IOR-INDEPENDENT-019",
            "the public proof schema is unsupported or malformed",
        )
    cap0 = _parse_cap(public_proof["cap0"], "independent:proof-formation")
    cap1 = _parse_cap(public_proof["cap1"], "independent:proof-formation")
    nonce = public_proof["grinding_nonce"]
    if type(nonce) is not int or not 0 <= nonce < 1 << 32:
        _failure(
            "Malformed",
            "independent:proof-formation",
            "FRI-IOR-INDEPENDENT-020",
            "the grinding nonce is not an unsigned 32-bit integer",
        )
    opening_values = _require_list(
        public_proof["opening_table"], "independent:proof-formation"
    )
    selector_values = _require_list(
        public_proof["occurrence_selectors"], "independent:proof-formation"
    )
    if (
        len(opening_values) > MAX_OPENING_TABLE_ENTRIES
        or len(selector_values) > QUERY_COUNT
    ):
        _failure(
            "Malformed",
            "independent:proof-formation",
            "FRI-IOR-INDEPENDENT-021",
            "a proof sequence exceeds the exact finite carrier bound",
        )
    opening_table: list[dict[str, Any]] = []
    for item in opening_values:
        entry = _require_object(
            item, {"layer", "opening"}, "independent:proof-formation"
        )
        if type(entry["layer"]) is not int or entry["layer"] < 0:
            _failure(
                "Malformed",
                "independent:proof-formation",
                "FRI-IOR-INDEPENDENT-022",
                "an opening-table layer is not a non-negative integer",
            )
        opening_table.append(
            {"layer": entry["layer"], "opening": _parse_opening(entry["opening"])}
        )
    selectors: list[dict[str, int]] = []
    for item in selector_values:
        selector = _require_object(
            item,
            {"ordinal", "layer0_opening_index", "layer1_opening_index"},
            "independent:proof-formation",
        )
        if any(
            type(selector[name]) is not int or selector[name] < 0 for name in selector
        ):
            _failure(
                "Malformed",
                "independent:proof-formation",
                "FRI-IOR-INDEPENDENT-023",
                "occurrence-selector coordinates must be non-negative integers",
            )
        selectors.append(dict(selector))
    parsed_proof = {
        "cap0": cap0,
        "cap1": cap1,
        "terminal": _parse_terminal(public_proof["terminal_polynomial"]),
        "nonce": nonce,
        "opening_table": opening_table,
        "selectors": selectors,
        "canonical_byte_length": len(canonical_term_bytes(public_proof)),
        "cap0_term": public_proof["cap0"],
        "cap1_term": public_proof["cap1"],
        "terminal_term": public_proof["terminal_polynomial"],
    }
    return inputs, parsed_proof


def _frame(namespace: str, codec: str, payload: bytes, counter: _Counter) -> bytes:
    namespace_bytes = namespace.encode("ascii")
    codec_bytes = codec.encode("ascii")
    if (
        len(namespace_bytes) >= 1 << 16
        or len(codec_bytes) >= 1 << 16
        or len(payload) >= 1 << 32
    ):
        _failure(
            "Malformed",
            "independent:transcript-framing",
            "FRI-IOR-INDEPENDENT-024",
            "a framed transcript component exceeds its codec bound",
        )
    counter.reserve(transcript_frames=1)
    return (
        len(namespace_bytes).to_bytes(2, "big")
        + namespace_bytes
        + len(codec_bytes).to_bytes(2, "big")
        + codec_bytes
        + len(payload).to_bytes(4, "big")
        + payload
    )


def _absorb(
    state: bytes, namespace: str, codec: str, payload: bytes, counter: _Counter
) -> bytes:
    framed = _frame(namespace, codec, payload, counter)
    return counter.hash(_ABSORB_DOMAIN + state + framed)


def _squeeze(
    state: bytes, namespace: str, sampler: str, attempt: int, counter: _Counter
) -> bytes:
    framed = _frame(namespace, sampler, attempt.to_bytes(2, "big"), counter)
    return counter.hash(_SQUEEZE_DOMAIN + state + framed)


def _sample_fp2(
    state: bytes, namespace: str, counter: _Counter
) -> tuple[tuple[int, int], bytes]:
    cardinality = MODULUS * MODULUS
    ceiling = ((1 << 16) // cardinality) * cardinality
    for attempt in range(MAX_REJECTION_ATTEMPTS):
        counter.reserve(sampler_attempts=1)
        digest = _squeeze(state, namespace, _FP2_SAMPLER, attempt, counter)
        candidate = int.from_bytes(digest[:2], "big")
        if candidate < ceiling:
            residue = candidate % cardinality
            return ((residue // MODULUS, residue % MODULUS), digest)
    _failure(
        "DeterministicLimitExceeded",
        "independent:transcript",
        "FRI-IOR-INDEPENDENT-025",
        "the intrinsic extension-field sampler bound was exhausted",
    )


def _derive_seed(state: bytes, namespace: str, counter: _Counter) -> bytes:
    counter.reserve(sampler_attempts=1)
    return _squeeze(state, namespace, _SEED_SAMPLER, 0, counter)


def _derive_transcript(
    inputs: dict[str, Any], proof: dict[str, Any], counter: _Counter
) -> dict[str, Any]:
    genesis_term = {
        "model": "FriIorTypedSha256FiatShamir.v1",
        "profile": _exact_profile(),
        "hash_suite": "sha256.v1",
        "framing": "typed-length-delimited-big-endian.v1",
    }
    state = counter.hash(_GENESIS_DOMAIN + canonical_term_bytes(genesis_term))
    state = _absorb(
        state,
        _STATEMENT_NAMESPACE,
        _CLOSED_TERM_CODEC,
        canonical_term_bytes(inputs["statement"]),
        counter,
    )
    state = _absorb(
        state,
        _CONTEXT_NAMESPACE,
        _CLOSED_TERM_CODEC,
        canonical_term_bytes(inputs["application_context"]),
        counter,
    )
    state = _absorb(
        state,
        _CAP0_NAMESPACE,
        _CAP_CODEC,
        canonical_term_bytes(proof["cap0_term"]),
        counter,
    )
    beta0, state = _sample_fp2(state, _BETA0_NAMESPACE, counter)
    state = _absorb(
        state,
        _CAP1_NAMESPACE,
        _CAP_CODEC,
        canonical_term_bytes(proof["cap1_term"]),
        counter,
    )
    beta1, state = _sample_fp2(state, _BETA1_NAMESPACE, counter)
    state = _absorb(
        state,
        _TERMINAL_NAMESPACE,
        _TERMINAL_CODEC,
        canonical_term_bytes(proof["terminal_term"]),
        counter,
    )
    work_seed = _derive_seed(state, _WORK_SEED_NAMESPACE, counter)
    state = work_seed
    nonce_bytes = proof["nonce"].to_bytes(4, "big")
    state = _absorb(state, _NONCE_NAMESPACE, _NONCE_CODEC, nonce_bytes, counter)
    counter.reserve(grinding_trials=1)
    work_payload = _frame(
        _WORK_CHECK_NAMESPACE,
        _WORK_RULE,
        work_seed + nonce_bytes,
        counter,
    )
    work_digest = counter.hash(_WORK_DOMAIN + work_payload)
    if work_digest[0] >> (8 - GRINDING_BITS) != 0:
        _failure(
            "Refused",
            "independent:work-check",
            "FRI-IOR-INDEPENDENT-026",
            "the published nonce fails the exact two-bit work predicate",
        )
    query_seed = _derive_seed(state, _QUERY_SEED_NAMESPACE, counter)
    queries: list[int] = []
    for ordinal in range(QUERY_COUNT):
        counter.reserve(sampler_attempts=1)
        framed = _frame(
            _QUERY_OCCURRENCES_NAMESPACE,
            _QUERY_SAMPLER,
            ordinal.to_bytes(2, "big"),
            counter,
        )
        digest = counter.hash(_QUERY_EXPAND_DOMAIN + query_seed + framed)
        queries.append(int.from_bytes(digest[:2], "big") & (DOMAIN_ORDERS[0] - 1))
    return {
        "beta0": beta0,
        "beta1": beta1,
        "work_digest": work_digest,
        "query_seed": query_seed,
        "queries": tuple(queries),
    }


def _cover_occurrences(
    proof: dict[str, Any], transcript: dict[str, Any], counter: _Counter
) -> list[dict[str, Any]]:
    table = proof["opening_table"]
    keys = tuple((entry["layer"], entry["opening"]["pair_index"]) for entry in table)
    if keys != tuple(sorted(keys)) or len(set(keys)) != len(keys):
        _failure(
            "Refused",
            "independent:occurrence-coverage",
            "FRI-IOR-INDEPENDENT-030",
            "the opening table is not in strict canonical key order",
        )
    for entry in table:
        layer = entry["layer"]
        if layer not in (0, 1) or entry["opening"]["domain"] != DOMAIN_NAMES[layer]:
            _failure(
                "Refused",
                "independent:occurrence-coverage",
                "FRI-IOR-INDEPENDENT-031",
                "an opening row has an unsupported layer or wrong domain",
            )
    expected_keys = tuple(
        sorted(
            {
                key
                for query in transcript["queries"]
                for key in ((0, query % 8), (1, query % 4))
            }
        )
    )
    if keys != expected_keys:
        _failure(
            "Refused",
            "independent:occurrence-coverage",
            "FRI-IOR-INDEPENDENT-032",
            "the opening table does not exactly cover all derived draws",
        )
    selectors = proof["selectors"]
    if len(selectors) != QUERY_COUNT or tuple(
        item["ordinal"] for item in selectors
    ) != tuple(range(QUERY_COUNT)):
        _failure(
            "Refused",
            "independent:occurrence-coverage",
            "FRI-IOR-INDEPENDENT-033",
            "selectors do not preserve the four occurrence identities in order",
        )
    covered: list[dict[str, Any]] = []
    for ordinal, (query, selector) in enumerate(
        zip(transcript["queries"], selectors, strict=True)
    ):
        indices = (selector["layer0_opening_index"], selector["layer1_opening_index"])
        if any(index >= len(table) for index in indices):
            _failure(
                "Refused",
                "independent:occurrence-coverage",
                "FRI-IOR-INDEPENDENT-034",
                "an occurrence selector points outside the opening table",
            )
        layer0 = table[indices[0]]
        layer1 = table[indices[1]]
        if (layer0["layer"], layer0["opening"]["pair_index"]) != (0, query % 8) or (
            layer1["layer"],
            layer1["opening"]["pair_index"],
        ) != (1, query % 4):
            _failure(
                "Refused",
                "independent:occurrence-coverage",
                "FRI-IOR-INDEPENDENT-035",
                "an occurrence selector does not name its derived layer queries",
            )
        covered.append(
            {
                "ordinal": ordinal,
                "query": query,
                "layer0": layer0["opening"],
                "layer1": layer1["opening"],
            }
        )
    counter.reserve(
        logical_query_occurrences=2 * len(covered),
        unique_openings=len(table),
        proof_bytes=proof["canonical_byte_length"],
    )
    return covered


def _leaf_hash(opening: dict[str, Any], counter: _Counter) -> bytes:
    domain_bytes = opening["domain"].encode("ascii")
    payload = (
        _LEAF_HASH_DOMAIN
        + bytes((len(domain_bytes),))
        + domain_bytes
        + opening["pair_index"].to_bytes(2, "big")
        + bytes(opening["positive"])
        + bytes(opening["negative"])
        + opening["salt"]
    )
    return counter.hash(payload, merkle_node=True)


def _authenticate(
    layer: int, opening: dict[str, Any], cap: tuple[bytes, bytes], counter: _Counter
) -> None:
    pair_count = DOMAIN_ORDERS[layer] // 2
    if opening["pair_index"] >= pair_count:
        _failure(
            "Refused",
            "independent:opening-authentication",
            "FRI-IOR-INDEPENDENT-040",
            "an opening index lies outside its committed domain",
        )
    expected_depth = (pair_count // CAP_SIZE).bit_length() - 1
    if len(opening["authentication_path"]) != expected_depth:
        _failure(
            "Refused",
            "independent:opening-authentication",
            "FRI-IOR-INDEPENDENT-041",
            "an authentication path does not reach the two-node cap",
        )
    running = _leaf_hash(opening, counter)
    index = opening["pair_index"]
    for sibling in opening["authentication_path"]:
        left, right = (running, sibling) if index % 2 == 0 else (sibling, running)
        running = counter.hash(_NODE_HASH_DOMAIN + left + right, merkle_node=True)
        index //= 2
    if index >= CAP_SIZE or not hmac.compare_digest(running, cap[index]):
        _failure(
            "Refused",
            "independent:opening-authentication",
            "FRI-IOR-INDEPENDENT-042",
            "an opening does not authenticate to its selected cap node",
        )


def _fp2_add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return ((left[0] + right[0]) % MODULUS, (left[1] + right[1]) % MODULUS)


def _fp2_sub(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return ((left[0] - right[0]) % MODULUS, (left[1] - right[1]) % MODULUS)


def _fp2_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return (
        (left[0] * right[0] + EXTENSION_NONRESIDUE * left[1] * right[1]) % MODULUS,
        (left[0] * right[1] + left[1] * right[0]) % MODULUS,
    )


def _fp2_scale(value: tuple[int, int], scalar: int) -> tuple[int, int]:
    return ((value[0] * scalar) % MODULUS, (value[1] * scalar) % MODULUS)


def _binary_fold(
    point: int,
    positive: tuple[int, int],
    negative: tuple[int, int],
    challenge: tuple[int, int],
    counter: _Counter,
) -> tuple[int, int]:
    counter.reserve(field_operations=8)
    inverse_two = pow(2, MODULUS - 2, MODULUS)
    even = _fp2_scale(_fp2_add(positive, negative), inverse_two)
    inverse_two_x = pow((2 * point) % MODULUS, MODULUS - 2, MODULUS)
    odd = _fp2_scale(_fp2_sub(positive, negative), inverse_two_x)
    return _fp2_add(even, _fp2_mul(challenge, odd))


def _evaluate(
    coefficients: tuple[tuple[int, int], ...], point: int, counter: _Counter
) -> tuple[int, int]:
    counter.reserve(field_operations=2 * len(coefficients))
    result = (0, 0)
    base = (point, 0)
    for coefficient in reversed(coefficients):
        result = _fp2_add(_fp2_mul(result, base), coefficient)
    return result


def _check_folds(
    covered: list[dict[str, Any]],
    transcript: dict[str, Any],
    terminal: tuple[tuple[int, int], ...],
    counter: _Counter,
) -> None:
    d0_points = tuple(
        pow(DOMAIN_GENERATORS[0], index, MODULUS) for index in range(DOMAIN_ORDERS[0])
    )
    d1_points = tuple(
        pow(DOMAIN_GENERATORS[1], index, MODULUS) for index in range(DOMAIN_ORDERS[1])
    )
    d2_points = tuple(
        pow(DOMAIN_GENERATORS[2], index, MODULUS) for index in range(DOMAIN_ORDERS[2])
    )
    for occurrence in covered:
        query = occurrence["query"]
        pair_index = query % 8
        expected = _binary_fold(
            d0_points[pair_index],
            occurrence["layer0"]["positive"],
            occurrence["layer0"]["negative"],
            transcript["beta0"],
            counter,
        )
        next_index = query % 8
        published = (
            occurrence["layer1"]["positive"]
            if next_index < 4
            else occurrence["layer1"]["negative"]
        )
        if expected != published:
            _failure(
                "Refused",
                "independent:first-fold",
                "FRI-IOR-INDEPENDENT-050",
                "an authenticated occurrence fails the first fold equation",
            )
    for occurrence in covered:
        pair_index = occurrence["query"] % 4
        expected = _binary_fold(
            d1_points[pair_index],
            occurrence["layer1"]["positive"],
            occurrence["layer1"]["negative"],
            transcript["beta1"],
            counter,
        )
        published = _evaluate(terminal, d2_points[pair_index], counter)
        if expected != published:
            _failure(
                "Refused",
                "independent:second-fold",
                "FRI-IOR-INDEPENDENT-051",
                "an authenticated occurrence fails the fold-to-terminal equation",
            )
    degree = -1 if terminal == ((0, 0),) else len(terminal) - 1
    if degree >= TERMINAL_DEGREE_BOUND_EXCLUSIVE:
        _failure(
            "Refused",
            "independent:terminal-degree",
            "FRI-IOR-INDEPENDENT-052",
            "the terminal polynomial exceeds the exact semantic degree bound",
        )


def _outcome(
    outcome: str,
    boundary: str,
    code: str,
    detail: str,
    counter: _Counter | None,
    selected: dict[str, int] | None,
    **evidence: Any,
) -> dict[str, Any]:
    evidence["resource_usage"] = (
        {name: 0 for name in _RESOURCE_FIELDS}
        if counter is None
        else counter.snapshot()
    )
    evidence["selected_limits"] = None if selected is None else dict(selected)
    return {
        "outcome": outcome,
        "boundary": boundary,
        "code": code,
        "detail": detail,
        "subject": None,
        "evidence": evidence,
    }


def verify_public_fri(
    public_inputs: Any,
    proof: Any,
    *,
    limits: Any = None,
) -> dict[str, Any]:
    """Replay one exact public proof under privately owned finite counters."""

    selected: dict[str, int] | None = None
    counter: _Counter | None = None
    try:
        selected = _selected_limits(limits)
        counter = _Counter(selected)
        inputs, parsed_proof = _parse_public_values(public_inputs, proof)
        transcript = _derive_transcript(inputs, parsed_proof, counter)
        covered = _cover_occurrences(parsed_proof, transcript, counter)
        for entry in parsed_proof["opening_table"]:
            layer = entry["layer"]
            cap = parsed_proof["cap0"] if layer == 0 else parsed_proof["cap1"]
            _authenticate(layer, entry["opening"], cap, counter)
        _check_folds(covered, transcript, parsed_proof["terminal"], counter)
        replay_digest = hashlib.sha256(
            b"zkc.fri-ior.independent-public-replay.v1\x00"
            + canonical_term_bytes(public_inputs)
            + canonical_term_bytes(proof)
        ).hexdigest()
        return _outcome(
            "Affirmative",
            "independent:public-replay",
            "FRI-IOR-INDEPENDENT-100",
            "the exact separately coded public replay accepts",
            counter,
            selected,
            verdict="Accept",
            beta0=list(transcript["beta0"]),
            beta1=list(transcript["beta1"]),
            ordered_initial_domain_indices=list(transcript["queries"]),
            random_draw_count=len(transcript["queries"]),
            logical_layer_query_occurrences=2 * len(covered),
            unique_authenticated_openings=len(parsed_proof["opening_table"]),
            first_fold_checks=len(covered),
            second_fold_checks=len(covered),
            proof_bytes=parsed_proof["canonical_byte_length"],
            public_replay_digest=replay_digest,
            establishes_outer_relation=False,
            establishes_proximity_theorem=False,
            establishes_checker_correspondence=False,
        )
    except _ReplayFailure as error:
        return _outcome(
            error.outcome,
            error.boundary,
            error.code,
            error.detail,
            counter,
            selected,
        )
    except Exception as error:  # pragma: no cover - defensive boundary
        return _outcome(
            "CheckerFailure",
            "independent:public-replay",
            "FRI-IOR-INDEPENDENT-099",
            f"unexpected independent replay failure: {type(error).__name__}",
            counter,
            selected,
        )


__all__ = [
    "DEFAULT_LIMITS",
    "HARD_LIMITS",
    "canonical_term_bytes",
    "verify_public_fri",
]
