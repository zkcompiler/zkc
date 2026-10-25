"""Strict nominal data types in the actual constructed participant export.

The native type spelling is only a carrier. Render the same recursive source
Ty, preserving the product nominal, constructor and ordered field types. This
reader has no value evaluator and grants no service serialization capability.
"""
import json
import re

from bridges.common.lean_render import record, require, text
from bridges.structured.snapshot import ty


def compact(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def product_tree(spelling):
    require(isinstance(spelling, str) and len(spelling) <= 1048576
            and re.fullmatch(r"variant:(?:[0-9a-f]{2})+", spelling), "invalid product spelling")
    try:
        version, nodes = record(json.loads(bytes.fromhex(spelling[8:]).decode("utf-8")), 2)
    except (ValueError, UnicodeError) as error:
        raise ValueError("invalid product encoding") from error
    require(version == "zkc.variant/0" and isinstance(nodes, list) and 0 < len(nodes) <= 4096,
            "invalid product node table")
    values, sizes, depths = [], [], []
    for node in nodes:
        if isinstance(node, str):
            value, size, depth = node, len(node.encode("utf-8")) + 2, 1
        else:
            require(isinstance(node, list), "invalid product node")
            indices = []
            for ref in node:
                require(isinstance(ref, str) and re.fullmatch(r"0|[1-9][0-9]*", ref)
                        and len(ref) < 10 and int(ref) < len(values), "invalid product reference")
                indices.append(int(ref))
            size = 2 + sum(sizes[i] + 1 for i in indices)
            depth = 1 + max((depths[i] for i in indices), default=0)
            require(size <= 1048576 and depth <= 64, "expanded product limit")
            value = [values[i] for i in indices]
        values.append(value)
        sizes.append(size)
        depths.append(depth)
    # Re-interning checks reachability, ordering, duplicate nodes, JSON and hex
    # canonicality independently of the native implementation.
    canonical, identifiers = [], {}

    def intern(value):
        node = value if isinstance(value, str) else [str(intern(child)) for child in value]
        key = compact(node)
        if key not in identifiers:
            identifiers[key] = len(canonical)
            canonical.append(node)
        return identifiers[key]

    intern(values[-1])
    require("variant:" + compact([version, canonical]).encode().hex() == spelling,
            "noncanonical product encoding")
    return values[-1]


def descriptor(value, depth=0):
    require(depth < 64, "constructed data type depth")
    if isinstance(value, list):
        nominal, alternatives = record(value, 2)
        require(nominal != "" and isinstance(alternatives, list) and len(alternatives) == 1,
                "expected one nominal product constructor")
        constructor, fields = record(alternatives[0], 2)
        require(isinstance(constructor, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", constructor)
                and isinstance(fields, list) and len(fields) <= 128, "invalid product constructor")
        identity = compact(nominal)
        text(identity, 512)
        text(constructor, 512)
        return ["product", identity, constructor, [descriptor(field, depth + 1) for field in fields]]
    require(isinstance(value, str), "invalid data descriptor")
    if value in ("bool", "index"):
        return [value]
    match = re.fullmatch(r"(field|group|vector):([^<>@\s]+)", value)
    if match:
        return [match[1], match[2]]
    if value.startswith("sequence<") and value.endswith(">"):
        return ["sequence", descriptor(value[9:-1], depth + 1)]
    require(False, "unsupported data descriptor")


def data_type(spelling, depth=0):
    require(depth < 64 and isinstance(spelling, str), "invalid constructed data type")
    if spelling == "i1":
        return ["bool"]
    if spelling == "ui64":
        return ["index"]
    match = re.fullmatch(r'!algebra\.(field|group|field_vector)<"([^"\\]+)">', spelling)
    if match:
        return ["vector" if match[1] == "field_vector" else match[1], match[2]]
    if spelling.startswith("!data.sequence<") and spelling.endswith(">"):
        return ["sequence", data_type(spelling[15:-1], depth + 1)]
    match = re.fullmatch(r'!data\.variant<"(variant:[0-9a-f]+)">', spelling)
    if match:
        return descriptor(product_tree(match[1]), depth + 1)
    require(False, "unsupported constructed data type")


def render_type(value):
    return ty(value)
