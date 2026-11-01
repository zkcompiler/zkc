"""Independent canonical ABI oracle for verify(bytes[],bytes,bytes).

The target's deliberately strict profile rejects holes, shared/overlapping tails,
nonzero padding and trailing data. Solidity's general decoder is more permissive.
Offsets inside bytes[] are relative to its element-head area, after its length.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "support"))
from hash_chain_reference import keccak256  # noqa: E402

SELECTOR = keccak256(b"verify(bytes[],bytes,bytes)")[:4]
MAX_CALLDATA = 256 * 1024


def word(value):
    return value.to_bytes(32, "big")


def blob(value):
    return word(len(value)) + value + bytes(-len(value) % 32)


def encode_verify(public, context, proof):
    tails = [blob(value) for value in public]
    cursor = 32 * len(tails)
    offsets = []
    for tail in tails:
        offsets.append(word(cursor))
        cursor += len(tail)
    array = word(len(tails)) + b"".join(offsets + tails)
    context_tail, proof_tail = blob(context), blob(proof)
    encoded = SELECTOR + b"".join([
        word(96), word(96 + len(array)),
        word(96 + len(array) + len(context_tail)),
        array, context_tail, proof_tail,
    ])
    if len(encoded) > MAX_CALLDATA:
        raise ValueError("abi-size")
    return encoded


def decode_verify(data):
    """Decode only the unique canonical, fully consumed encoding."""
    if len(data) > MAX_CALLDATA or len(data) < 100 or data[:4] != SELECTOR:
        raise ValueError("abi-selector-or-size")
    body = data[4:]

    def number(at):
        if at < 0 or at + 32 > len(body):
            raise ValueError("abi-word")
        return int.from_bytes(body[at:at + 32], "big")

    def take(at):
        length = number(at)
        start = at + 32
        end = start + length
        padded = end + (-length % 32)
        if padded > len(body) or any(body[end:padded]):
            raise ValueError("abi-tail-or-padding")
        return body[start:end], padded

    if number(0) != 96:
        raise ValueError("abi-array-offset")
    count = number(96)
    base = 128
    cursor = base + 32 * count
    if cursor > len(body):
        raise ValueError("abi-count")
    public = []
    for i in range(count):
        if number(base + 32 * i) != cursor - base:
            raise ValueError("abi-element-offset")
        value, cursor = take(cursor)
        public.append(value)
    if number(32) != cursor:
        raise ValueError("abi-context-offset")
    context, cursor = take(cursor)
    if number(64) != cursor:
        raise ValueError("abi-proof-offset")
    proof, cursor = take(cursor)
    if cursor != len(body):
        raise ValueError("abi-trailing")
    return public, context, proof


def malformed_cases(valid):
    """Named mutations passed verbatim to the deployed verifier by integration."""
    public, context, proof = decode_verify(valid)

    def replace(at, value):
        return valid[:at] + word(value) + valid[at + 32:]

    cases = {
        "selector": bytes([valid[0] ^ 1]) + valid[1:],
        "short-head": valid[:99],
        "unaligned": replace(4, 97),
        "head-overlap": replace(4, 64),
        "offset-overflow": replace(36, (1 << 256) - 1),
        "proof-context-overlap": replace(68, int.from_bytes(valid[36:68], "big")),
        "array-count-overflow": replace(100, (1 << 256) - 1),
        "truncated": valid[:-1],
        "trailing": valid + bytes(32),
    }
    context_at = int.from_bytes(valid[36:68], "big") + 4
    # Preserve every value and standard ABI offset relationship while inserting
    # an otherwise-permissible gap between the array and context tails.
    hole = bytearray(valid[:context_at] + bytes(32) + valid[context_at:])
    hole[36:68] = word(int.from_bytes(valid[36:68], "big") + 32)
    hole[68:100] = word(int.from_bytes(valid[68:100], "big") + 32)
    cases["hole"] = bytes(hole)
    count = int.from_bytes(valid[100:132], "big")
    if count:
        cases["element-head-overlap"] = replace(132, 0)
    if count > 1:
        cases["element-tail-overlap"] = replace(164, int.from_bytes(valid[132:164], "big"))
    tails = [(132 + int.from_bytes(valid[132 + 32 * i:164 + 32 * i], "big"), value)
             for i, value in enumerate(public)]
    tails += [(context_at, context), (4 + int.from_bytes(valid[68:100], "big"), proof)]
    for at, value in tails:
        if len(value) % 32:
            padding = at + 32 + len(value)
            cases["padding"] = valid[:padding] + b"\x01" + valid[padding + 1:]
            break
    return cases
