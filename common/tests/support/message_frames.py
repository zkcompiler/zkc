"""Inspect and mutate canonical aggregate proof frames in integration tests.

These helpers cover the declared variant/sequence framing only. They do not
decide logical type admission or validate cryptographic leaves.
"""


def tag(frame):
    assert len(frame) >= 6 and frame[:5] == b'ZKCV\x00'
    return frame[5]


def children(frame):
    """Return children of a known variant (65) or sequence (69) frame."""
    kind = tag(frame)
    assert kind in (65, 69) and len(frame) >= 10
    result, offset = [], 10
    while offset < len(frame):
        assert offset + 4 <= len(frame)
        size = int.from_bytes(frame[offset:offset + 4], 'little')
        offset += 4
        assert size >= 6 and offset + size <= len(frame)
        child = frame[offset:offset + size]
        tag(child)
        result.append(child)
        offset += size
    assert offset == len(frame)
    if kind == 69:
        assert len(result) == int.from_bytes(frame[6:10], 'little')
    return result


def with_children(frame, values):
    """Keep the original alternative or sequence kind, rebuilding lengths."""
    kind = tag(frame)
    assert kind in (65, 69)
    values = list(values)
    for value in values:
        tag(value)
    header = frame[:10] if kind == 65 else frame[:6] + len(values).to_bytes(4, 'little')
    return header + b''.join(len(value).to_bytes(4, 'little') + value for value in values)


def replace_child(frame, path, replacement):
    """Replace exactly one nested child while retaining enclosing alternatives."""
    if not path:
        tag(replacement)
        return replacement
    values = children(frame)
    index, *remaining = path
    assert 0 <= index < len(values)
    values[index] = replace_child(values[index], remaining, replacement)
    return with_children(frame, values)
