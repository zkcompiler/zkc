"""Bounded reference for mathematical subject bytes; no semantic admission."""

import hashlib
import json

MAX_BYTES = 16 << 20
MAX_JSON_BYTES = 1 << 20
MAX_NODES = 200_000
MAX_ITEMS = 32_768
MAX_DEPTH = 64
PREFIX = b"zkc.math.subject.v1\0"
PREFIXES = {"zkc.math.v1": PREFIX, "zkc.math.located.v1": b"zkc.math.located.v1\0"}


def utf8_size(text, limit):
    if len(text) > limit:
        raise ValueError("UTF-8 limit")
    size = 0
    for offset in range(0, len(text), 1024):
        size += len(text[offset:offset + 1024].encode("utf-8", errors="strict"))
        if size > limit:
            raise ValueError("UTF-8 limit")
    return size


def pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError("duplicate object key")
        result[key] = value
    return result


def natural(text):
    if not text or len(text) > 20 or not text.isascii() or not text.isdecimal():
        raise ValueError("invalid natural")
    if len(text) > 1 and text[0] == "0":
        raise ValueError("noncanonical natural")
    value = int(text)
    if value >= 1 << 64:
        raise ValueError("natural range")
    return value


def parse(text):
    utf8_size(text, MAX_JSON_BYTES)
    # Transport preflight bounds JSON work; encode enforces converted-tree limits.
    stack = []
    quoted = escaped = False
    tokens = 0
    for char in text:
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
            tokens += 1
        elif char in "[{":
            stack.append(0)
            tokens += 1
            if len(stack) > MAX_DEPTH:
                raise ValueError("JSON depth limit")
        elif char in "]}":
            if not stack:
                raise ValueError("JSON delimiter")
            stack.pop()
        elif char == "," and stack:
            stack[-1] += 1
            tokens += 1
            if stack[-1] >= MAX_ITEMS:
                raise ValueError("JSON item limit")
        if tokens > MAX_NODES:
            raise ValueError("JSON node limit")

    def refuse(value):
        raise ValueError(f"unsupported JSON number: {value}")

    try:
        result = json.loads(text, object_pairs_hook=pairs, parse_int=natural,
                            parse_float=refuse, parse_constant=refuse)
        encode(result)
        return result
    except (RecursionError, UnicodeError) as error:
        raise ValueError("invalid or excessive JSON") from error


def from_tree(tree):
    if type(tree) is not list or not tree or type(tree[0]) is not str:
        raise ValueError("typed tree shape")
    tag, *items = tree
    if tag == "boolean" and len(items) == 1 and items[0] in ("true", "false"):
        return items[0] == "true"
    if tag == "natural" and len(items) == 1 and type(items[0]) is str:
        return natural(items[0])
    if tag == "string" and len(items) == 1 and type(items[0]) is str:
        return items[0]
    if tag == "array":
        return [from_tree(item) for item in items]
    if tag == "object" and len(items) % 2 == 0:
        result = {}
        previous = None
        for i in range(0, len(items), 2):
            key, item = items[i:i + 2]
            if type(key) is not str:
                raise ValueError("object key")
            order = key.encode("utf-8")
            if previous is not None and order <= previous:
                raise ValueError("unordered/duplicate key")
            previous = order
            result[key] = from_tree(item)
        return result
    raise ValueError("typed tree kind")


def tree_bytes(tree):
    output = bytearray()
    nodes = 0

    def emit(data):
        if len(output) + len(data) > MAX_BYTES:
            raise ValueError("byte limit")
        output.extend(data)

    def visit(item, depth):
        nonlocal nodes
        nodes += 1
        if nodes > MAX_NODES or depth > MAX_DEPTH:
            raise ValueError("node/depth limit")
        if type(item) is str:
            raw = item.encode("utf-8", errors="strict")
            emit(b"\0" + len(raw).to_bytes(8, "little"))
            emit(raw)
        elif type(item) is list:
            if len(item) > MAX_ITEMS:
                raise ValueError("item limit")
            emit(b"\1" + len(item).to_bytes(8, "little"))
            for child in item:
                visit(child, depth + 1)
        else:
            raise ValueError("logical tree kind")

    visit(tree, 0)
    return bytes(output)


def encode(value):
    # Stream the conversion: no intermediate tree proportional to hostile input.
    output = bytearray()
    nodes = 0

    def emit(data):
        if len(output) + len(data) > MAX_BYTES:
            raise ValueError("byte limit")
        output.extend(data)

    def charge(depth):
        nonlocal nodes
        nodes += 1
        if nodes > MAX_NODES or depth > MAX_DEPTH:
            raise ValueError("node/depth limit")

    def string(text, depth):
        charge(depth)
        size = utf8_size(text, MAX_BYTES - len(output) - 9)
        emit(b"\0" + size.to_bytes(8, "little"))
        for offset in range(0, len(text), 1024):
            emit(text[offset:offset + 1024].encode("utf-8", errors="strict"))

    def array(count, depth):
        charge(depth)
        if count > MAX_ITEMS:
            raise ValueError("item limit")
        emit(b"\1" + count.to_bytes(8, "little"))

    def visit(item, depth):
        if type(item) in (bool, int, str):
            if type(item) is bool:
                tag, text = "boolean", "true" if item else "false"
            elif type(item) is int:
                if not 0 <= item < 1 << 64:
                    raise ValueError("integer range")
                tag, text = "natural", str(item)
            else:
                tag, text = "string", item
            array(2, depth)
            string(tag, depth + 1)
            string(text, depth + 1)
        elif type(item) is list:
            array(1 + len(item), depth)
            string("array", depth + 1)
            for child in item:
                visit(child, depth + 1)
        elif type(item) is dict:
            array(1 + 2 * len(item), depth)
            string("object", depth + 1)
            # Bound key storage before creating the sorting list.
            key_bytes = 0
            for key in item:
                if type(key) is not str or len(key) > MAX_BYTES - key_bytes:
                    raise ValueError("object key limit")
                key_bytes += utf8_size(key, MAX_BYTES - len(output) - key_bytes)
                if key_bytes > MAX_BYTES - len(output):
                    raise ValueError("object key bytes")
            for key in sorted(item, key=lambda key: key.encode("utf-8")):
                string(key, depth + 1)
                visit(item[key], depth + 1)
        else:
            raise ValueError("unsupported value")

    visit(value, 0)
    return bytes(output)


def decode(raw):
    if len(raw) > MAX_BYTES:
        raise ValueError("byte limit")
    offset = 0
    nodes = 0

    def take(size):
        nonlocal offset
        if size > len(raw) - offset:
            raise ValueError("truncated tree")
        result = raw[offset:offset + size]
        offset += size
        return result

    def visit(depth):
        nonlocal nodes
        nodes += 1
        if nodes > MAX_NODES or depth > MAX_DEPTH:
            raise ValueError("node/depth limit")
        tag = take(1)
        if tag not in (b"\0", b"\1"):
            raise ValueError("unknown tree tag")
        count = int.from_bytes(take(8), "little")
        if tag == b"\0":
            return take(count).decode("utf-8", errors="strict")
        if count > MAX_ITEMS or count > (len(raw) - offset) // 9:
            raise ValueError("item limit")
        return [visit(depth + 1) for _ in range(count)]

    tree = visit(0)
    if offset != len(raw):
        raise ValueError("trailing bytes")
    return from_tree(tree)


def digest(subject):
    if type(subject) is not dict or set(subject) != {"profile", "manifest", "module"}:
        raise ValueError("subject envelope")
    if type(subject["profile"]) is not str or subject["profile"] not in PREFIXES:
        raise ValueError("subject profile")
    return hashlib.sha256(PREFIXES[subject["profile"]] + encode(subject)).hexdigest()
