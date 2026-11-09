"""Strict native artifact checks; none of these predicates establish a Lean proof."""

import re


class Refused(ValueError):
    """A native artifact does not satisfy its declared transport contract."""


def require(condition, message):
    if not condition:
        raise Refused(message)


def validate_origin(value, depth=0, remaining=None):
    """Validate a retained origin term without rendering or interpreting Lean syntax."""
    if remaining is None:
        remaining = [4096]
    require(remaining[0] > 0, "origin term count limit")
    remaining[0] -= 1
    require(depth < 64, "origin nesting limit")
    require(isinstance(value, list) and value, "empty or invalid origin term")
    tag, *args = value

    def arity(count):
        require(len(args) == count, f"origin {tag}: expected {count} arguments")

    def string(item, limit=512):
        require(isinstance(item, str) and item and "\0" not in item
                and len(item.encode('utf-8')) <= limit, "empty or invalid origin string")

    def decimal(item):
        string(item)
        require(re.fullmatch(r"0|[1-9][0-9]*", item) is not None,
                "noncanonical origin decimal")

    def child(item):
        validate_origin(item, depth + 1, remaining)

    def children(items):
        require(isinstance(items, list) and len(items) <= 512, "origin argument limit")
        for item in items:
            child(item)

    if tag == 'nat':
        arity(1)
        decimal(args[0])
    elif tag in ('field', 'group'):
        arity(1)
        string(args[0])
    elif tag in ('domain', 'asset'):
        arity(2)
        for item in args:
            string(item)
    elif tag in ('bool', 'index', 'unit'):
        arity(0)
    elif tag == 'tuple':
        arity(1)
        children(args[0])
    elif tag == 'array':
        arity(2)
        child(args[0])
        decimal(args[1])
    elif tag == 'nominal':
        arity(3)
        kind, path, arguments = args
        require(kind in ('record', 'logical_record', 'variant', 'associated', 'module'),
                'invalid origin nominal kind')
        string(path)
        def initial(char):
            return ord(char) >= 128 or 'a' <= char <= 'z' or 'A' <= char <= 'Z' or char == '_'
        require(all(part and initial(part[0]) and
                    all(initial(char) or '0' <= char <= '9' for char in part)
                    for part in path.split('::')), 'invalid origin path')
        children(arguments)
    elif tag in ('builtin', 'formal'):
        arity(2)
        string(args[0])
        children(args[1])
    else:
        raise Refused('unknown origin term')
