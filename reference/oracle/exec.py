"""Independent execution semantics and vectors for the toy OIR profile.

PIR closure and OIR execution are intentionally separate claims.  The
sumcheck, Chaum--Pedersen, and OR-sigma artifacts are explicit analysis
residuals at the PIR boundary, yet their projected verifier programs remain
useful executable witnesses.  This module executes those programs without
calling the C++ implementation.
"""

from __future__ import annotations

import hashlib
import json
import sys

from . import babybear, model, witnesses
from .model import Bind


P = 4611686018427394499
Q = 2305843009213697249
G = 4
MODULUS = {"tg": P, "scalar": Q}


def be8(value: int) -> bytes:
    return value.to_bytes(8, "big")


def decimal_u64(text: str) -> int:
    if not (text and text.isascii() and text.isdigit()):
        raise ValueError(f"not a decimal uint64: {text!r}")
    value = int(text)
    if value >= 1 << 64:
        raise ValueError(f"not a decimal uint64: {text!r}")
    return value


class Duplex:
    """The domain-separated deterministic duplex used by the toy profile."""

    def __init__(self, source_id: str):
        self.state = hashlib.sha256(source_id.encode("ascii")).digest()

    def clone(self) -> "Duplex":
        """The transcript peek's mechanism (endpoints.md §6.2): a
        pow_search trial runs on a copy, never on the live state."""
        twin = Duplex.__new__(Duplex)
        twin.state = self.state
        return twin

    def absorb(self, value: int) -> None:
        self.state = hashlib.sha256(self.state + b"\x00" + be8(value)).digest()

    def squeeze(self, domain: str, space: int) -> int:
        self.state = hashlib.sha256(
            self.state + b"\x01" + domain.encode("ascii")
        ).digest()
        return int.from_bytes(self.state[:8], "big") % space


def run(protocol: dict, statement: dict[str, str], proof: bytes) -> dict:
    """Execute a projected verifier program and return its classified result."""

    document = model.project(protocol, model.VOCABULARY)
    statement_classes = {
        event.label: event.payload_class
        for event in protocol["events"]
        if isinstance(event, Bind)
    }
    environment: dict[tuple, int] = {}
    challenges: list[str] = []
    duplex: Duplex | None = None
    cursor = 0
    verdict: dict | None = None

    def reject(kind: str, diagnostic: str) -> None:
        nonlocal verdict
        verdict = {
            "verdict": kind,
            "challenges": challenges,
            "diag": diagnostic,
        }

    for index, label in enumerate(document["statement_labels"]):
        value = decimal_u64(statement[label])
        modulus = MODULUS.get(statement_classes[label])
        if modulus is not None and value >= modulus:
            return {
                "verdict": "public_binding_failure",
                "challenges": [],
                "diag": f"statement value '{label}' out of range",
            }
        environment["a", index] = value

    def value(reference: list) -> int:
        return environment[tuple(reference)]

    for index, row in enumerate(document["program"]):
        tag = row[0]
        if tag == "init":
            if row[1:] != ["toy_duplex", "artifact-id"]:
                raise AssertionError("execution witness left the toy profile")
            duplex = Duplex(document["source"])
        elif tag == "const":
            environment["r", index, 0] = decimal_u64(row[1])
        elif tag == "absorb":
            assert duplex is not None
            duplex.absorb(value(row[2]))
        elif tag == "read":
            if cursor + 8 > len(proof):
                reject("abi_decode_failure", f"proof stream underrun at '{row[2]}'")
            else:
                decoded = int.from_bytes(proof[cursor : cursor + 8], "big")
                cursor += 8
                modulus = MODULUS.get(row[3])
                if modulus is not None and decoded >= modulus:
                    reject("abi_decode_failure", f"non-canonical value at '{row[2]}'")
                else:
                    environment["r", index, 1] = decoded
        elif tag == "squeeze":
            count = decimal_u64(row[4])
            space = decimal_u64(row[7])
            assert (
                duplex is not None
                and row[6] == "uniform"
                and space >= 2
                and count == 1
            ), "the toy executable profile supports scalar squeezes only"
            squeezed = duplex.squeeze(row[5], space)
            environment["r", index, 1] = squeezed
            challenges.append(str(squeezed))
        elif tag == "f_neg":
            environment["r", index, 0] = (Q - value(row[1]) % Q) % Q
        elif tag == "f_add":
            environment["r", index, 0] = (value(row[1]) + value(row[2])) % Q
        elif tag == "f_mul":
            environment["r", index, 0] = value(row[1]) * value(row[2]) % Q
        elif tag == "g_exp":
            environment["r", index, 0] = pow(value(row[1]), value(row[2]), P)
        elif tag == "g_mul":
            environment["r", index, 0] = value(row[1]) * value(row[2]) % P
        elif tag == "assert_eq":
            if value(row[1]) != value(row[2]):
                reject("check_failure", f"check '{row[3]}' failed")
        elif tag == "expect_end":
            if cursor != len(proof):
                reject("proof_trailing_data", "proof stream not exhausted")
        elif tag == "decide":
            pass
        else:
            raise AssertionError(f"row outside the executable toy profile: {tag}")
        if verdict is not None:
            return verdict
    return {"verdict": "accept", "challenges": challenges, "diag": ""}


def prove_schnorr(source_ref: str, x: int = 123456789, k: int = 987654321):
    y, commitment = pow(G, x, P), pow(G, k, P)
    duplex = Duplex(source_ref)
    duplex.absorb(y)
    duplex.absorb(commitment)
    challenge = duplex.squeeze("schnorr.c", 1 << 61)
    response = (k + challenge * x) % Q
    return y, commitment, challenge, response


H = int(witnesses.CP_H)


def prove_chaum_pedersen(
    source_ref: str, x: int = 192837465, k: int = 564738291
):
    y1, y2 = pow(G, x, P), pow(H, x, P)
    a1, a2 = pow(G, k, P), pow(H, k, P)
    duplex = Duplex(source_ref)
    for member in (y1, y2, a1, a2):
        duplex.absorb(member)
    challenge = duplex.squeeze("cp.c", 1 << 61)
    response = (k + challenge * x) % Q
    return y1, y2, a1, a2, challenge, response


def prove_or(
    source_ref: str,
    x1: int = 123454321,
    k1: int = 1122334455,
    c2: int = 998877665544332211,
    z2: int = 443322110099887766,
):
    y1, y2 = pow(G, x1, P), pow(G, 777666555, P)
    a1 = pow(G, k1, P)
    a2 = pow(G, z2, P) * pow(y2, Q - c2, P) % P
    duplex = Duplex(source_ref)
    for member in (y1, y2, a1, a2):
        duplex.absorb(member)
    challenge = duplex.squeeze("or.c", 1 << 61)
    c1 = (challenge - c2) % Q
    z1 = (k1 + c1 * x1) % Q
    return y1, y2, a1, a2, challenge, c1, c2, z1, z2


def forge_or_ignoring_challenge():
    c1, z1 = 111111111111111111, 222222222222222222
    c2, z2 = 333333333333333333, 444444444444444444
    y1, y2 = pow(G, 123454321, P), pow(G, 777666555, P)
    a1 = pow(G, z1, P) * pow(y1, Q - c1, P) % P
    a2 = pow(G, z2, P) * pow(y2, Q - c2, P) % P
    return y1, y2, a1, a2, c1, c2, z1, z2


def prove_sumcheck(source_ref: str, claimed_sum: int = 3) -> list[int]:
    duplex = Duplex(source_ref)
    duplex.absorb(claimed_sum)
    first = [0, 3, 0]
    for coefficient in first:
        duplex.absorb(coefficient)
    c1 = duplex.squeeze("sumcheck.c1", 1 << 61)
    return first + [c1, c1, 0]


def cheat_sumcheck(source_ref: str, claimed_sum: int = 5) -> list[int]:
    inverse_two = (Q + 1) // 2
    first = [1, 3, 0]
    duplex = Duplex(source_ref)
    duplex.absorb(claimed_sum)
    for coefficient in first:
        duplex.absorb(coefficient)
    c1 = duplex.squeeze("sumcheck.c1", 1 << 61)
    b0 = (2 * c1 + 1) * inverse_two % Q
    return first + [b0, c1, 0]


def coefficients_hex(coefficients: list[int]) -> str:
    return b"".join(be8(value) for value in coefficients).hex()


def schnorr_cases(source_ref: str):
    y, commitment, _challenge, response = prove_schnorr(source_ref)
    honest = (be8(commitment) + be8(response)).hex()
    statement = {"y": str(y)}
    return [
        ("honest", statement, honest, "accept"),
        (
            "tampered_response",
            statement,
            (be8(commitment) + be8((response + 1) % Q)).hex(),
            "check_failure",
        ),
        ("trailing_byte", statement, honest + "00", "proof_trailing_data"),
        ("truncated", statement, honest[:16], "abi_decode_failure"),
        (
            "noncanonical_value",
            statement,
            (be8(P) + be8(response)).hex(),
            "abi_decode_failure",
        ),
    ]


def sumcheck_cases(source_ref: str):
    honest_coefficients = prove_sumcheck(source_ref)
    honest = coefficients_hex(honest_coefficients)
    tampered = list(honest_coefficients)
    tampered[3] = (tampered[3] + 1) % Q
    statement = {"s": "3"}
    return [
        ("honest", statement, honest, "accept"),
        ("false_statement", {"s": "4"}, honest, "check_failure"),
        (
            "tampered_message",
            statement,
            coefficients_hex(tampered),
            "check_failure",
        ),
        (
            "consistent_cheat",
            {"s": "5"},
            coefficients_hex(cheat_sumcheck(source_ref)),
            "check_failure",
        ),
        ("trailing_byte", statement, honest + "00", "proof_trailing_data"),
        ("truncated", statement, honest[:48], "abi_decode_failure"),
        (
            "noncanonical_value",
            statement,
            coefficients_hex([Q, 3, 0, 0, 0, 0]),
            "abi_decode_failure",
        ),
    ]


def chaum_pedersen_cases(source_ref: str):
    y1, y2, a1, a2, _challenge, response = prove_chaum_pedersen(source_ref)
    honest = (be8(a1) + be8(a2) + be8(response)).hex()
    statement = {"y1": str(y1), "y2": str(y2)}
    return [
        ("honest", statement, honest, "accept"),
        (
            "tampered_response",
            statement,
            (be8(a1) + be8(a2) + be8((response + 1) % Q)).hex(),
            "check_failure",
        ),
        (
            "mismatched_statement",
            {"y1": str(y1), "y2": str(pow(H, 3, P))},
            honest,
            "check_failure",
        ),
        ("trailing_byte", statement, honest + "00", "proof_trailing_data"),
        ("truncated", statement, honest[:32], "abi_decode_failure"),
        (
            "noncanonical_value",
            statement,
            (be8(P) + be8(a2) + be8(response)).hex(),
            "abi_decode_failure",
        ),
    ]


def or_sigma_cases(source_ref: str):
    y1, y2, a1, a2, _challenge, c1, c2, z1, z2 = prove_or(source_ref)
    honest = (be8(a1) + be8(a2) + be8(c1) + be8(c2) + be8(z1) + be8(z2)).hex()
    statement = {"y1": str(y1), "y2": str(y2)}
    fy1, fy2, fa1, fa2, fc1, fc2, fz1, fz2 = forge_or_ignoring_challenge()
    forged = (
        be8(fa1) + be8(fa2) + be8(fc1) + be8(fc2) + be8(fz1) + be8(fz2)
    ).hex()
    return [
        ("honest", statement, honest, "accept"),
        (
            "tampered_response",
            statement,
            (
                be8(a1)
                + be8(a2)
                + be8(c1)
                + be8(c2)
                + be8((z1 + 1) % Q)
                + be8(z2)
            ).hex(),
            "check_failure",
        ),
        (
            "shifted_shares",
            statement,
            (
                be8(a1)
                + be8(a2)
                + be8((c1 + 1) % Q)
                + be8((c2 - 1) % Q)
                + be8(z1)
                + be8(z2)
            ).hex(),
            "check_failure",
        ),
        (
            "ignored_challenge",
            {"y1": str(fy1), "y2": str(fy2)},
            forged,
            "check_failure",
        ),
        ("trailing_byte", statement, honest + "00", "proof_trailing_data"),
        ("truncated", statement, honest[:48], "abi_decode_failure"),
        (
            "noncanonical_value",
            statement,
            (
                be8(a1)
                + be8(a2)
                + be8(Q)
                + be8(c2)
                + be8(z1)
                + be8(z2)
            ).hex(),
            "abi_decode_failure",
        ),
    ]


CASES = {
    "schnorr": (witnesses.SCHNORR, schnorr_cases),
    "sumcheck": (witnesses.SUMCHECK, sumcheck_cases),
    "chaum-pedersen": (witnesses.CHAUM_PEDERSEN, chaum_pedersen_cases),
    "or-sigma": (witnesses.OR_SIGMA, or_sigma_cases),
}


# --------------------------------------------------------------------------
# The independent real execution profile: the same projected rows, executed
# over the twin's own BabyBear Poseidon2-16 duplex
# and the pinned codec framings — one OIR artifact under two independent
# supplier sets.  Word layouts mirror the pinned constructions: every
# framed symbol is a 32-bit big-endian canonical field word, multi-word
# values carry their least-significant 32-bit limb first, and squeeze
# derivation is the tuple bijection for ext values (no reduction) or the
# low-bits mask (the space is a power of two) for the rest.
# --------------------------------------------------------------------------

REAL_SPONGE = "plonky3_bb31_poseidon2_w16_r8_lenpad"
REAL_WORDS = {"rs": 8, "ext_field": 4, "pow_value": 1, "query_index": 1}


def _real_words(value: int, count: int) -> list[int]:
    return [(value >> (32 * i)) & 0xFFFFFFFF for i in range(count)]


def run_real(protocol: dict, statement: dict[str, str], proof: bytes) -> dict:
    """Execute a projected verifier program under the real profile."""

    vocabulary = witnesses.PLONKY3_FRI_VOCABULARY
    document = model.project(protocol, vocabulary, "verifier")
    statement_classes = {
        event.label: event.payload_class
        for event in protocol["events"]
        if isinstance(event, Bind)
    }
    environment: dict[tuple, int] = {}
    classes: dict[tuple, str] = {}
    challenges: list[str] = []
    duplex: babybear.Duplex | None = None
    cursor = 0
    verdict: dict | None = None

    def reject(kind: str, diagnostic: str) -> None:
        nonlocal verdict
        verdict = {
            "verdict": kind,
            "challenges": challenges,
            "diag": diagnostic,
        }

    for index, label in enumerate(document["statement_labels"]):
        text = statement[label]
        if not (text and text.isascii() and text.isdigit()):
            raise ValueError(f"not a decimal statement value: {text!r}")
        value = int(text)
        if value >= 1 << 512:
            raise ValueError(f"statement value too wide: {text!r}")
        environment["a", index] = value
        classes["a", index] = statement_classes[label]

    def value(reference: list) -> int:
        return environment[tuple(reference)]

    def value_class(reference: list) -> str:
        return classes[tuple(reference)]

    for index, row in enumerate(document["program"]):
        tag = row[0]
        if tag == "init":
            if row[1:] != [REAL_SPONGE, "artifact-id"]:
                raise AssertionError("execution witness left the real profile")
            duplex = babybear.Duplex(document["source"])
        elif tag == "const":
            environment["r", index, 0] = int(row[1])
            classes["r", index, 0] = row[2]
        elif tag == "absorb":
            assert duplex is not None
            for word in _real_words(
                value(row[2]), REAL_WORDS[value_class(row[2])]
            ):
                duplex.absorb_word(word)
        elif tag == "read":
            width = 4 * REAL_WORDS[row[3]]
            if cursor + width > len(proof):
                reject(
                    "abi_decode_failure",
                    f"proof stream underrun at '{row[2]}'",
                )
            else:
                words = [
                    int.from_bytes(proof[cursor + 4 * i : cursor + 4 * i + 4],
                                   "big")
                    for i in range(REAL_WORDS[row[3]])
                ]
                cursor += width
                if any(word >= babybear.P for word in words):
                    reject(
                        "abi_decode_failure",
                        f"non-canonical value at '{row[2]}'",
                    )
                else:
                    environment["r", index, 1] = sum(
                        word << (32 * i) for i, word in enumerate(words)
                    )
                    classes["r", index, 1] = row[3]
        elif tag == "squeeze":
            assert duplex is not None
            payload_class = row[3]
            count = decimal_u64(row[4])
            rule = row[6]
            space = int(row[7])
            assert space >= 2 and (
                (rule == "uniform" and count == 1)
                or (rule == "uniform_independent" and count >= 1)
            ), "sampling rule outside the real profile"
            drawn: list[int] = []
            for _ in range(count):
                if payload_class == "ext_field":
                    words = [duplex.squeeze_word() for _ in range(4)]
                    drawn.append(
                        sum(word << (32 * i) for i, word in enumerate(words))
                    )
                else:
                    drawn.append(duplex.squeeze_word() % space)
            environment["r", index, 1] = drawn[0] if count == 1 else 0
            classes["r", index, 1] = payload_class
            challenges.append("|".join(str(v) for v in drawn))
        elif tag == "assert_eq":
            if value(row[1]) != value(row[2]):
                reject("check_failure", f"check '{row[3]}' failed")
        elif tag == "expect_end":
            if cursor != len(proof):
                reject("proof_trailing_data", "proof stream not exhausted")
        elif tag == "decide":
            pass
        else:
            raise AssertionError(
                f"row outside the executable real profile: {tag}"
            )
        if verdict is not None:
            return verdict
    return {"verdict": "accept", "challenges": challenges, "diag": ""}


def plonky3_fri_cases(source_ref: str):
    del source_ref
    return [
        ("empty-proof", {"f_root": "1"}, "", "abi_decode_failure"),
        (
            "non-canonical-root",
            {"f_root": "1"},
            f"{babybear.P:08x}" + "00" * 28,
            "abi_decode_failure",
        ),
    ]


REAL_CASES = {
    "plonky3-fri": (witnesses.PLONKY3_FRI_REAL, plonky3_fri_cases),
}


def real_vectors(name: str) -> dict:
    protocol, cases = REAL_CASES[name]
    vocabulary = witnesses.PLONKY3_FRI_VOCABULARY
    source_ref = "sha256:" + model.compute_id(protocol, vocabulary)
    emitted = []
    for case_name, statement, proof, expected in cases(source_ref):
        result = run_real(protocol, statement, bytes.fromhex(proof))
        assert result["verdict"] == expected, (case_name, result)
        emitted.append(
            {
                "name": case_name,
                "statement": statement,
                "proof": proof,
                "expect": expected,
                "challenges": result["challenges"],
            }
        )
    return {
        "artifact_id": model.compute_oir_id(protocol, vocabulary, "verifier"),
        "vectors": emitted,
    }


def vectors(name: str) -> dict:
    try:
        protocol, cases = CASES[name]
    except KeyError:
        raise ValueError(f"unknown executable witness {name!r}") from None
    source_ref = "sha256:" + model.compute_id(protocol, model.VOCABULARY)
    emitted = []
    for case_name, statement, proof, expected in cases(source_ref):
        result = run(protocol, statement, bytes.fromhex(proof))
        assert result["verdict"] == expected, (case_name, result)
        emitted.append(
            {
                "name": case_name,
                "statement": statement,
                "proof": proof,
                "expect": expected,
                "challenges": result["challenges"],
            }
        )
    return {
        "artifact_id": model.compute_oir_id(protocol, model.VOCABULARY),
        "source": source_ref,
        "vectors": emitted,
    }


def _sigma_commit_fill(values, handles):
    (generator,) = values
    (payload,) = handles
    k = int.from_bytes(payload[8:16], "big")
    return [pow(generator, k, P)], [payload]


def _sigma_response_fill(values, handles):
    (challenge,) = values
    (payload,) = handles
    x = int.from_bytes(payload[:8], "big")
    k = int.from_bytes(payload[8:16], "big")
    return [(k + (challenge % Q) * (x % Q)) % Q], []


TOY_FILLS = {
    "zkc.hole.sigma-commit": _sigma_commit_fill,
    "zkc.hole.sigma-response": _sigma_response_fill,
}


def prove_derived(
    protocol: dict,
    statement: dict[str, str],
    witness_payloads: dict[str, bytes],
) -> dict:
    """Run the derived prover document with the toy fills — the
    orchestration the hand-written provers above now mirror. Returns the
    emitted proof bytes and the replica sponge's challenge log, both of
    which the carrier's prove path must reproduce exactly."""

    document = model.project(protocol, model.VOCABULARY, "prover_skeleton")
    fills = {
        model.VOCABULARY.digest_for("hole_contracts", name): fill
        for name, fill in TOY_FILLS.items()
    }
    n_statement = len(document["statement_labels"])
    values: dict[tuple, int] = {}
    handles: dict[tuple, bytes] = {}
    for index, label in enumerate(document["statement_labels"]):
        values[("a", index)] = decimal_u64(statement[label])
    for index, (label, _cls) in enumerate(protocol["routes"]["witnesses"]):
        handles[("a", n_statement + index)] = witness_payloads[label]

    def key(ref):
        return tuple(
            tuple(part) if isinstance(part, list) else part for part in ref
        )

    duplex = None
    proof = b""
    challenges: list[str] = []
    for row_index, row in enumerate(document["program"]):
        tag = row[0]
        if tag == "init":
            duplex = Duplex(document["source"])
        elif tag == "absorb":
            duplex.absorb(values[key(row[2])])
        elif tag == "const":
            values[("r", row_index, 0)] = decimal_u64(row[1])
        elif tag == "write":
            proof += be8(values[key(row[2])])
        elif tag == "squeeze":
            space = int(row[7])
            value = duplex.squeeze(row[5], space)
            values[("r", row_index, 1)] = value
            challenges.append(str(value))
        elif tag == "hole_call" and ["sponge"] in row[2]:
            # The transcript peek (endpoints.md §6.2): the fill never
            # holds the sponge — each trial runs on a clone — and the
            # trial is re-derived from the three rows after the hole
            # (the nonce write, its absorb, the pow squeeze), so a
            # neighborhood that is not the verifier's own check refuses.
            # The search is canonical ascending, least witness first.
            program = document["program"]
            (value_index,) = [
                index
                for index, descriptor in enumerate(row[2])
                if descriptor[0] == "val"
            ]
            (sponge_index,) = [
                index
                for index, descriptor in enumerate(row[2])
                if descriptor == ["sponge"]
            ]
            nonce_ref = ["r", row_index, value_index]
            write_row = program[row_index + 1]
            absorb_row = program[row_index + 2]
            squeeze_row = program[row_index + 3]
            bits = int(row[6][0])
            if not (
                write_row[0] == "write"
                and write_row[2] == nonce_ref
                and absorb_row[0] == "absorb"
                and absorb_row[1] == ["r", row_index, sponge_index]
                and absorb_row[2] == nonce_ref
                and squeeze_row[0] == "squeeze"
                and squeeze_row[1] == ["r", row_index + 2, 0]
                and squeeze_row[4] == "1"
                and squeeze_row[6] == "uniform"
                and squeeze_row[7] == str(1 << bits)
            ):
                raise model.Refusal(
                    "pow_search hole: the trial the fill would run is not "
                    "the check the verifier performs"
                )
            domain, space = squeeze_row[5], int(squeeze_row[7])
            for nonce in range(P):
                probe = duplex.clone()
                probe.absorb(nonce)
                if probe.squeeze(domain, space) == 0:
                    values[("r", row_index, value_index)] = nonce
                    break
            else:
                raise model.Refusal(
                    f"no nonce below {P} satisfies the proof-of-work "
                    "condition"
                )
        elif tag == "hole_call":
            fill = fills[row[5]]
            operand_values = []
            operand_handles = []
            for ref in row[1]:
                entry = key(ref)
                if entry in values:
                    operand_values.append(values[entry])
                else:
                    operand_handles.append(handles[entry])
            value_results, handle_results = fill(
                operand_values, operand_handles
            )
            value_index = 0
            handle_index = 0
            for result_index, descriptor in enumerate(row[2]):
                if descriptor[0] == "val":
                    values[("r", row_index, result_index)] = value_results[
                        value_index
                    ]
                    value_index += 1
                elif descriptor[0] == "handle":
                    handles[("r", row_index, result_index)] = handle_results[
                        handle_index
                    ]
                    handle_index += 1
        elif tag in {"end_stream", "finish"}:
            pass
        else:
            raise model.Refusal(
                f"derived prover cannot execute row {tag!r}"
            )
    return {"proof": proof.hex(), "challenges": challenges}


def main(argv: list[str] | None = None) -> None:
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] == "derived-prove":
        name = args[1]
        statement: dict[str, str] = {}
        payloads: dict[str, bytes] = {}
        for entry in args[2:]:
            kind, _, pair = entry.partition(":")
            label, _, value = pair.partition("=")
            if kind == "s":
                statement[label] = value
            elif kind == "w":
                payloads[label] = bytes.fromhex(value)
            else:
                raise SystemExit("entries are s:<label>=<v> or w:<label>=<hex>")
        record = prove_derived(
            witnesses.PIR_WITNESSES[name], statement, payloads
        )
        print("prover challenges: " + ",".join(record["challenges"]))
        print("proof: " + record["proof"])
        return
    if len(args) != 1:
        choices = ", ".join(sorted(CASES) + sorted(REAL_CASES))
        raise SystemExit(f"usage: python -m oracle.exec NAME ({choices})")
    if args[0] in REAL_CASES:
        # The real-profile vector file predates the toy emitter's sorted
        # form; its field order is part of the committed bytes the twin
        # regenerates, so it is preserved rather than resorted.
        json.dump(real_vectors(args[0]), sys.stdout, indent=1)
    else:
        json.dump(vectors(args[0]), sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
