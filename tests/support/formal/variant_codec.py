"""Fixture-only encoder/decoder of the self-contained local variant DAG.

Production readers implement this independently; tests use this to build both
valid and deliberately invalid semantic trees, not to decide admission.
"""
import json


def tree(spelling):
    version, nodes = json.loads(bytes.fromhex(spelling.removeprefix('variant:')))
    assert version == 'zkc.variant/1'
    values = []
    for node in nodes:
        values.append(node if isinstance(node, str) else [values[int(r)] for r in node])
    return values[-1]


def encode_tree(value):
    nodes, ids = [], {}

    def intern(value):
        node = value if isinstance(value, str) else [str(intern(v)) for v in value]
        key = json.dumps(node, ensure_ascii=False, separators=(',', ':'))
        if key not in ids:
            ids[key] = len(nodes)
            nodes.append(node)
        return ids[key]

    intern(value)
    raw = json.dumps(['zkc.variant/1', nodes], ensure_ascii=False, separators=(',', ':'))
    return 'variant:' + raw.encode().hex()


def descriptor(nominal, alternatives):
    arms = [[label, [tree(t) if t.startswith('variant:') and '@' not in t else t
                     for t in payload]] for label, payload in alternatives]
    return encode_tree([nominal, arms])
