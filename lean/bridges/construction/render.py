#!/usr/bin/env python3
"""Render a `zkc.constructed-participant/0` export as transparent Lean data.

This is a tested data boundary. Operations are classified by exact name,
operation binding and attribute set. An unrecognized operation is retained as
unsupported for the Lean rule to refuse; a recognized operation with another
shape, an unknown type or a malformed origin refuses the whole export.
Occurrence origins are decoded from their canonical bytes and re-encoded
exactly. No proof is generated here and no meaning is assigned to any
operation.
"""

import argparse
import json
from pathlib import Path
import re


FORMAT = "zkc.constructed-participant/0"
TEMPLATE = "zkc.native-origin-template/0"
SCALAR_DOMAINS = {"field": r'!algebra\.field<"([^"\\]+)">', "group": r'!algebra\.group<"([^"\\]+)">'}
CALCULATIONS = {
    "algebra.field_add": ("fieldAdd", "field"),
    "algebra.field_subtract": ("fieldSubtract", "field"),
    "algebra.field_multiply": ("fieldMultiply", "field"),
    "algebra.field_equal": ("fieldEqual", "field"),
    "algebra.group_add": ("groupAdd", "group"),
    "algebra.group_equal": ("groupEqual", "group"),
}


class Refused(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Refused(message)


def record(value, size):
    require(isinstance(value, list) and len(value) == size, f"expected array of size {size}")
    return value


def text(value):
    require(isinstance(value, str) and len(value.encode("utf-8")) <= 4096, "expected a bounded string")
    escapes = {'"': r'\"', '\\': r'\\', '\n': r'\n', '\r': r'\r', '\t': r'\t'}

    def character(char):
        if char in escapes:
            return escapes[char]
        if ord(char) < 32 or ord(char) == 127:
            return f"\\u{ord(char):04x}"
        return char
    return '"' + ''.join(character(char) for char in value) + '"'


def nat(value, limit=1 << 20):
    require(type(value) is int and 0 <= value <= limit, "invalid bounded natural")
    return str(value)


def decimal(value, limit=1024):
    require(isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value) is not None
            and int(value) < limit, "invalid canonical decimal")
    return str(int(value))


def seq(values, render):
    require(isinstance(values, list) and len(values) <= 4096, "invalid bounded array")
    return "[" + ", ".join(render(value) for value in values) + "]"


def sort(value):
    """Return (Lean term, logical kind) for an exported MLIR type string."""
    require(isinstance(value, str), "type must be a string")
    if value == "i1":
        return ".data .boolean", ("boolean", None)
    for kind, pattern in SCALAR_DOMAINS.items():
        match = re.fullmatch(pattern, value)
        if match:
            return f".data (.{kind} {text(match[1])})", (kind, match[1])
    match = re.fullmatch(r'!local\.capability<"transcript:([^"\\]+)">', value)
    if match:
        return f".transcript {text(match[1])}", ("transcript", match[1])
    if value == "!algebra.indices":
        return ".indices", ("indices", None)
    raise Refused(f"unsupported exported type {value!r}")


def scalar_ty(kind):
    tag, domain = kind
    require(tag in ("boolean", "field", "group"), "expected a scalar data type")
    return ".boolean" if tag == "boolean" else f"(.{tag} {text(domain)})"


def decode_tree(data, offset=0, depth=0):
    require(depth <= 16 and offset + 9 <= len(data), "truncated origin")
    tag, count = data[offset], int.from_bytes(data[offset + 1:offset + 9], "little")
    offset += 9
    if tag == 0:
        require(offset + count <= len(data), "truncated origin text")
        return data[offset:offset + count].decode("utf-8"), offset + count
    require(tag == 1 and count <= 64, "invalid origin tag")
    items = []
    for _ in range(count):
        item, offset = decode_tree(data, offset, depth + 1)
        items.append(item)
    return items, offset


def encode_tree(tree):
    if isinstance(tree, str):
        raw = tree.encode("utf-8")
        return b"\0" + len(raw).to_bytes(8, "little") + raw
    return b"\1" + len(tree).to_bytes(8, "little") + b"".join(encode_tree(item) for item in tree)


def origin(hex_text):
    require(isinstance(hex_text, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", hex_text) is not None
            and len(hex_text) <= 4096, "origin must be lowercase even-length hex")
    data = bytes.fromhex(hex_text)
    tree, end = decode_tree(data)
    require(end == len(data), "trailing origin bytes")
    require(encode_tree(tree).hex() == hex_text, "noncanonical origin encoding")
    require(isinstance(tree, list) and len(tree) == 5 and tree[0] == TEMPLATE, "not an origin template")
    _, entry, steps, coordinates, event = tree
    require(isinstance(entry, str) and steps == [] and coordinates == [], "only flat origins are supported")
    require(isinstance(event, list) and event and all(isinstance(item, str) for item in event), "invalid origin event")
    return f"⟨{text(entry)}, {seq(event, text)}⟩"


def attributes(value):
    require(isinstance(value, list), "attributes must be an array")
    result = {}
    for item in value:
        name, attribute = record(item, 2)
        require(isinstance(name, str) and name not in result, "duplicate or invalid attribute")
        kind, payload = record(attribute, 2)
        require(kind in ("string", "symbol", "integer", "bool", "strings", "text"),
                "unknown attribute kind")
        result[name] = (kind, payload)
    return result


def string_attribute(attrs, name):
    kind, payload = attrs.get(name, (None, None))
    require(kind == "string" and isinstance(payload, str), f"missing string attribute {name}")
    return payload


def one_parameter(attrs):
    kind, payload = attrs.get("parameters", (None, None))
    require(kind == "strings" and isinstance(payload, list) and len(payload) == 1, "expected one parameter")
    return payload[0]


def operation(name, attrs, binding, operand_kinds, result_kinds):
    """Classify one exported operation strictly; return its Lean term."""
    if name == "protocol.receive" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        require(not operand_kinds and len(result_kinds) == 1, "receive shape")
        return (f".receive {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))} {scalar_ty(result_kinds[0])}")
    if name == "protocol.send" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        return (f".send {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))}")
    if name == "algebra.exec.indices_empty" and binding == ["indices.empty", [], ""] \
            and set(attrs) == {"binding", "parameters", "site"} and attrs["parameters"] == ("strings", []):
        return ".indicesEmpty"
    # The kernel site is a diagnostic frame name; it never enters transcript identity.
    if name == "crypto.exec.indexed_transcript_observe_data" and set(attrs) == {"binding", "parameters", "site"} \
            and isinstance(binding, list) and len(binding) == 3 \
            and binding[0] == "transcript.native.indexed.observe.data" and binding[2] == "":
        suite, leaf = record(binding[1], 2)
        require(len(operand_kinds) == 3 and operand_kinds[1][0] in ("field", "group")
                and leaf == f"{operand_kinds[1][0]}:{operand_kinds[1][1]}", "observed leaf type")
        return f".observe {text(suite)} {origin(one_parameter(attrs))}"
    if name == "crypto.exec.indexed_transcript_challenge" and set(attrs) == {"binding", "parameters", "site"} \
            and isinstance(binding, list) and len(binding) == 3 \
            and binding[0] == "transcript.native.indexed.challenge" and binding[2] == "":
        (suite,) = record(binding[1], 1)
        require(len(result_kinds) == 2 and result_kinds[0][0] == "field", "challenge results")
        return f".challenge {text(suite)} {text(result_kinds[0][1])} {origin(one_parameter(attrs))}"
    if name == "algebra.group_scale" and not attrs and binding == []:
        require(len(operand_kinds) == 2 and operand_kinds[0][0] == "group" and operand_kinds[1][0] == "field",
                "group scale operands")
        return f".calculate (.groupScale {text(operand_kinds[0][1])} {text(operand_kinds[1][1])})"
    if name in CALCULATIONS and not attrs and binding == []:
        constructor, kind = CALCULATIONS[name]
        require(len(operand_kinds) == 2 and operand_kinds[0] == operand_kinds[1] and operand_kinds[0][0] == kind,
                "calculation operands")
        return f".calculate (.{constructor} {text(operand_kinds[0][1])})"
    return f".unsupported {text(name)}"


def policy(value):
    (version, entry, producer, validator, acceptance, suite, services, public, draws,
     framing, construction) = record(value, 11)
    require(version == "zkc.native-proof-policy/0", "wrong policy version")
    pairs = [record(pair, 2) for pair in draws]
    return (f"⟨{text(entry)}, {text(producer)}, {text(validator)}, {decimal(acceptance)}, {text(suite)}, "
            f"{seq(services, decimal)}, {seq(public, decimal)}, "
            f"{seq(pairs, lambda pair: f'({text(pair[0])}, {text(pair[1])})')}, {text(framing)}, {text(construction)}⟩")


def render(data, namespace):
    version, source, candidate, selected, symbol, inputs, outputs, instructions, returned = record(data, 9)
    require(version == FORMAT, "wrong participant export version")
    require(re.fullmatch(r"(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*", namespace) is not None,
            "invalid Lean namespace")
    kinds = [sort(value)[1] for value in inputs]
    rendered = []
    for item in instructions:
        name, attrs, binding, operands, results = record(item, 5)
        require(isinstance(name, str), "operation name")
        require(isinstance(operands, list) and all(type(o) is int and 0 <= o < len(kinds) for o in operands),
                "operand reference out of range")
        result_kinds = [sort(value)[1] for value in results]
        term = operation(name, attributes(attrs), binding, [kinds[o] for o in operands], result_kinds)
        rendered.append(f"⟨{term}, {seq(operands, nat)}, {seq(results, lambda v: sort(v)[0])}⟩")
        kinds += result_kinds
    require(all(type(r) is int and 0 <= r < len(kinds) for r in returned), "returned reference out of range")
    body = ",\n    ".join(rendered)
    return f'''module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace {namespace}
open Zkc.Construction

def participant : Participant where
  source := {text(source)}
  candidate := {text(candidate)}
  policy := {policy(selected)}
  symbol := {text(symbol)}
  inputs := {seq(inputs, lambda v: sort(v)[0])}
  outputs := {seq(outputs, lambda v: sort(v)[0])}
  instructions := [
    {body}]
  returned := {seq(returned, nat)}

end {namespace}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    args.output.write_text(render(data, args.namespace), encoding="utf-8")


if __name__ == "__main__":
    main()
