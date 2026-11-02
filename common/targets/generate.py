#!/usr/bin/env python3
"""Validate the EVM target declaration and project it into C++.

`evm.json` is the one authored source of `zkc.evm-target/0`. This generator
checks every rule of the format and writes the compiler's
`zkc/Target/Evm/Declaration.h.inc`. The Rust SDK build checks the same rules
independently in `crates/zkc/build.rs`; neither reader trusts the other's
output. Only the Python standard library is used.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

FORMAT = "zkc.evm-target/0"
KEYS = ("format", "abi", "solc", "default_fork", "forks", "validation_gas", "limits", "reverts")
FORK_KEYS = ("name", "solc", "hardfork", "transaction_gas_cap", "runtime_code_bytes",
             "initcode_bytes", "rules")
# The emitted verifier copies memory with MCOPY.
REQUIRED_RULE = "EIP-5656"
U64 = (1 << 64) - 1


class Refusal(ValueError):
    """A broken rule of the declaration format, named for the shared cases."""

    def __init__(self, rule, detail):
        super().__init__(f"evm-target {rule}: {detail}")
        self.rule = rule


ROUND_CONSTANTS = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
# Rotation offsets r[x][y] of the rho step.
ROTATIONS = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]


def _rotate(value, count):
    return ((value << count) | (value >> (64 - count))) & U64 if count else value


def _permute(lanes):
    a = [[lanes[x + 5 * y] for y in range(5)] for x in range(5)]
    for constant in ROUND_CONSTANTS:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotate(c[(x + 1) % 5], 1) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rotate(a[x][y], ROTATIONS[x][y])
        a = [[b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y]) for y in range(5)]
             for x in range(5)]
        a[0][0] ^= constant
    return [a[x][y] for y in range(5) for x in range(5)]


def keccak256(data):
    """Ethereum's Keccak-256: rate 136 bytes, original padding byte 0x01."""
    rate = 136
    padded = bytearray(data) + b"\x01"
    padded += bytes(-len(padded) % rate)
    padded[-1] |= 0x80
    lanes = [0] * 25
    for start in range(0, len(padded), rate):
        for i in range(rate // 8):
            lanes[i] ^= int.from_bytes(padded[start + 8 * i:start + 8 * i + 8], "little")
        lanes = _permute(lanes)
    return b"".join(lane.to_bytes(8, "little") for lane in lanes[:4])


def identity(data):
    """The declaration identity: its format and the SHA-256 of its exact bytes."""
    return f"{FORMAT}:{hashlib.sha256(data).hexdigest()}"


def _unique_object(pairs):
    keys = [key for key, _ in pairs]
    for key in keys:
        if keys.count(key) > 1:
            raise Refusal("keys", f"duplicate key {key}")
    return dict(pairs)


def _no_number(text):
    raise Refusal("keys", f"non-integer number {text}")


def load(data):
    """Parse exact JSON: no duplicate keys, no fractional or special numbers."""
    try:
        text = data.decode("ascii")
    except UnicodeDecodeError:
        raise Refusal("format", "the declaration is ASCII") from None
    try:
        return json.loads(text, object_pairs_hook=_unique_object, parse_float=_no_number,
                          parse_constant=_no_number)
    except json.JSONDecodeError as error:
        raise Refusal("format", f"malformed JSON: {error}") from None


def _object(value, keys, where):
    if not isinstance(value, dict):
        raise Refusal("keys", f"{where} is an object")
    if set(value) != set(keys):
        raise Refusal("keys", f"{where} has exactly the fields {', '.join(keys)}")
    return value


def _string(value, pattern, rule, where):
    if not isinstance(value, str) or not re.fullmatch(pattern, value):
        raise Refusal(rule, f"{where} must match {pattern}")
    return value


def _natural(value, rule, where, minimum=1):
    if isinstance(value, bool) or not isinstance(value, int) or not minimum <= value <= U64:
        raise Refusal(rule, f"{where} is an integer from {minimum} to 2^64-1")
    return value


def _list(value, rule, where):
    if not isinstance(value, list) or not value:
        raise Refusal(rule, f"{where} is a nonempty list")
    return value


def _unique(values, rule, where):
    if len(set(values)) != len(values):
        raise Refusal(rule, f"duplicate {where}")


def validate(document):
    """Check every rule of the format; return the document unchanged."""
    _object(document, KEYS, "the declaration")
    if document["format"] != FORMAT:
        raise Refusal("format", f"format must be {FORMAT}")

    abi = _object(document["abi"], ("signature", "selector", "json"), "abi")
    signature = _string(abi["signature"], r"[a-z][A-Za-z0-9_]*\(([a-z0-9\[\]]+(,[a-z0-9\[\]]+)*)?\)",
                        "abi", "abi.signature")
    function, parameters = signature[:-1].split("(")
    selector = _string(abi["selector"], r"[0-9a-f]{8}", "selector", "abi.selector")
    if keccak256(signature.encode()).hex()[:8] != selector:
        raise Refusal("selector", "abi.selector differs from Keccak-256 of abi.signature")
    entries = abi["json"]
    if not isinstance(entries, list) or len(entries) != 1:
        raise Refusal("abi", "abi.json declares exactly one function")
    entry = _object(entries[0], ("type", "name", "stateMutability", "inputs", "outputs"),
                    "abi.json function")
    if entry["type"] != "function" or entry["name"] != function:
        raise Refusal("abi", "abi.json names the signature's function")
    if entry["stateMutability"] not in ("pure", "view", "nonpayable", "payable"):
        raise Refusal("abi", "abi.json has a Solidity state mutability")
    for side in ("inputs", "outputs"):
        if not isinstance(entry[side], list):
            raise Refusal("abi", f"abi.json {side} is a list")
        for port in entry[side]:
            _object(port, ("name", "type"), f"abi.json {side} entry")
            _string(port["name"], r"[A-Za-z_][A-Za-z0-9_]*", "abi", f"abi.json {side} name")
            _string(port["type"], r"[a-z0-9\[\]]+", "abi", f"abi.json {side} type")
        _unique([port["name"] for port in entry[side]], "abi", f"abi.json {side} name")
    if ",".join(port["type"] for port in entry["inputs"]) != parameters:
        raise Refusal("abi", "abi.json inputs differ from abi.signature")

    solc = _object(document["solc"], ("version", "optimizer"), "solc")
    _string(solc["version"], r"[0-9]+\.[0-9]+\.[0-9]+\+commit\.[0-9a-f]{8}", "solc", "solc.version")
    optimizer = _object(solc["optimizer"], ("enabled", "details"), "solc.optimizer")
    details = _object(optimizer["details"], ("yul", "yulDetails"), "solc.optimizer.details")
    steps = _object(details["yulDetails"], ("optimizerSteps",), "solc.optimizer.details.yulDetails")
    if not isinstance(optimizer["enabled"], bool) or not isinstance(details["yul"], bool):
        raise Refusal("solc", "solc.optimizer switches are Booleans")
    _string(steps["optimizerSteps"], r"[!-~]+", "solc", "solc.optimizer steps")

    forks = _list(document["forks"], "fork", "forks")
    for fork in forks:
        _object(fork, FORK_KEYS, "fork")
        _string(fork["name"], r"[a-z]+", "fork", "fork name")
        _string(fork["solc"], r"[a-z]+", "fork", "fork solc")
        _string(fork["hardfork"], r"[A-Z][A-Za-z]*", "fork", "fork hardfork")
        if fork["transaction_gas_cap"] is not None:
            _natural(fork["transaction_gas_cap"], "fork", "fork transaction_gas_cap")
        _natural(fork["runtime_code_bytes"], "fork", "fork runtime_code_bytes")
        _natural(fork["initcode_bytes"], "fork", "fork initcode_bytes")
        rules = _list(fork["rules"], "rules", "fork rules")
        for rule in rules:
            _string(rule, r"EIP-[1-9][0-9]*", "rules", "fork rule")
        _unique(rules, "rules", f"rule of fork {fork['name']}")
        if REQUIRED_RULE not in rules:
            raise Refusal("rules", f"fork {fork['name']} must include {REQUIRED_RULE}")
    for key in ("name", "solc", "hardfork"):
        _unique([fork[key] for fork in forks], "fork", f"fork {key}")
    if document["default_fork"] not in [fork["name"] for fork in forks]:
        raise Refusal("default-fork", "default_fork must name a declared fork")
    _natural(document["validation_gas"], "validation-gas", "validation_gas")

    limits = _list(document["limits"], "limit", "limits")
    for limit in limits:
        _object(limit, ("name", "minimum", "maximum"), "limit")
        _string(limit["name"], r"[a-z][a-z0-9]*(_[a-z0-9]+)*", "limit", "limit name")
        _natural(limit["minimum"], "limit", "limit minimum")
        _natural(limit["maximum"], "limit", "limit maximum")
        if limit["minimum"] > limit["maximum"]:
            raise Refusal("limit", f"limit {limit['name']} has its minimum above its maximum")
    _unique([limit["name"] for limit in limits], "limit", "limit name")

    reverts = _list(document["reverts"], "revert", "reverts")
    for revert in reverts:
        _object(revert, ("class", "tag"), "revert class")
        _string(revert["class"], r"[a-z]+", "revert", "revert class name")
        _string(revert["tag"], r"[A-Z]{4}", "revert", "revert tag")
    for key in ("class", "tag"):
        _unique([revert[key] for revert in reverts], "revert", f"revert {key}")
    return document


def check(data):
    """Load and validate exact declaration bytes."""
    return validate(load(data))


def _cstring(text):
    if not all(" " <= character <= "~" for character in text):
        raise Refusal("format", "projected strings are printable ASCII")
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _member(name):
    head, *tail = name.split("_")
    return head + "".join(part.capitalize() for part in tail)


def _canonical(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True)


def render_cpp(document, declaration_identity):
    """Project the validated declaration as X-macro tables and constants."""
    forks, limits = document["forks"], document["limits"]
    lines = [
        f"// Generated from common/targets/evm.json ({FORMAT}) by",
        "// common/targets/generate.py. Do not edit.",
        "#ifndef ZKC_TARGET_EVM_DECLARATION_H_INC",
        "#define ZKC_TARGET_EVM_DECLARATION_H_INC",
        "",
        "// X(Enumerator, name, solc, hardfork, runtimeCodeBytes, initcodeBytes)",
        "#define ZKC_EVM_TARGET_FORKS(X) \\",
    ]
    lines += [f"  X({fork['name'].capitalize()}, {_cstring(fork['name'])}, "
              f"{_cstring(fork['solc'])}, {_cstring(fork['hardfork'])}, "
              f"{fork['runtime_code_bytes']}ull, {fork['initcode_bytes']}ull) \\" for fork in forks]
    lines += ["", f"#define ZKC_EVM_TARGET_DEFAULT_FORK {document['default_fork'].capitalize()}", "",
              "// X(member, name, minimum, maximum)", "#define ZKC_EVM_TARGET_LIMITS(X) \\"]
    lines += [f"  X({_member(limit['name'])}, {_cstring(limit['name'])}, "
              f"{limit['minimum']}ull, {limit['maximum']}ull) \\" for limit in limits]
    lines += ["", "// X(class, tag, word): word is the tag's big-endian ASCII value.",
              "#define ZKC_EVM_TARGET_REVERTS(X) \\"]
    lines += [f"  X({revert['class']}, {_cstring(revert['tag'])}, "
              f"0x{revert['tag'].encode().hex()}u) \\" for revert in document["reverts"]]
    abi, solc = document["abi"], document["solc"]
    constants = [
        ("identity", declaration_identity),
        ("abiSignature", abi["signature"]),
        ("abiSelector", abi["selector"]),
        ("abiJson", _canonical(abi["json"])),
        ("solcVersion", solc["version"]),
        ("solcRelease", solc["version"].split("+")[0]),
        ("solcOptimizerJson", _canonical(solc["optimizer"])),
        ("solcOptimizerSteps", solc["optimizer"]["details"]["yulDetails"]["optimizerSteps"]),
    ]
    lines += ["", "namespace zkc::evm_target {"]
    lines += [f"inline constexpr char {name}[] = {_cstring(value)};" for name, value in constants]
    lines += ["} // namespace zkc::evm_target", "", "#endif", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True, help="the authored evm.json")
    parser.add_argument("--output", type=Path, help="the C++ Declaration.h.inc to write")
    args = parser.parse_args()
    data = args.source.read_bytes()
    try:
        document = check(data)
    except Refusal as refusal:
        print(refusal, file=sys.stderr)
        return 1
    if args.output:
        text = render_cpp(document, identity(data))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        if not args.output.exists() or args.output.read_text() != text:
            args.output.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
