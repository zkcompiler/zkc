"""Render the native proof descriptor's transmitted messages and draws as Lean data."""
from bridges.common import lean_render as lean
from bridges.construction.render import policy


def render(deployment, source_identity, namespace):
    _, source, descriptor, _, _, _, _, _, _ = lean.record(deployment, 9)
    lean.require(deployment[0] == "zkc.native-proof/0" and "sha256:" + source == source_identity,
                 "descriptor source differs from selected original")
    version, raw_policy, format_, events, _, messages, gates, _, _ = lean.record(descriptor, 9)
    lean.require(version == "zkc.native-proof-descriptor/0" and format_ == "zkc.native-origin/0"
                 and gates == [], "unsupported descriptor profile")
    policy_literal = policy(raw_policy)
    codecs = {}
    for encoded, ty, codec in map(lambda row: lean.record(row, 3), lean.record(messages)):
        lean.require(encoded not in codecs, "duplicate message codec")
        codecs[encoded] = (ty, codec)
    rows = []
    seen = set()
    for row in lean.record(events):
        lean.record(row)
        lean.require(len(row) >= 2, "missing descriptor event")
        kind, encoded, *args = row
        origin = lean.origin(encoded)
        _, entry, _, _, event = lean.template(encoded)
        lean.require(entry == raw_policy[1] and encoded not in seen, "wrong entry or repeated event")
        seen.add(encoded)
        if kind == "message":
            lean.require(not args and event[0] == "message" and encoded in codecs, "missing transmitted message")
            ty, codec = codecs.pop(encoded)
            observation = f".message {lean.text(ty)} {lean.text(codec)}"
        elif kind == "query":
            lean.require(not args and event[0] == "query" and event[5] == "draw", "expected field draw")
            observation = ".draw"
        elif kind == "index":
            lean.require(len(args) == 1 and event[0] == "query" and event[5] == "index", "expected index draw")
            observation = f".index {lean.decimal(args[0], limit=1 << 64)}"
        else:
            raise lean.Refused("unsupported descriptor event " + str(kind))
        rows.append(f"⟨{origin}, {observation}⟩")
    lean.require(not codecs, "message codec without descriptor event")
    ns = lean.namespace(namespace)
    rendered = ",\n  ".join(rows)
    return f"""module

public import Zkc.Executable.DescriptorEvents

@[expose] public section

/-! Generated from the selected proof entry's native descriptor by the subject bridge. -/
namespace {ns}

def original : String := {lean.text(source_identity)}

def policy : Zkc.Construction.Policy := {policy_literal}

def events : List Zkc.Executable.Descriptor.Event := [
  {rendered}]

end {ns}
"""
