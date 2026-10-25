#!/usr/bin/env python3
"""Strict compiled-pair container reader and transparent Lean data renderer.

The container orders the actual producer and validator exports. The fixed
request must separately authenticate those artifacts; matching digests do not
establish a source-to-constructed correspondence theorem.
"""
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render  # noqa: E402
from bridges.construction import render as participant  # noqa: E402

FORMAT = "zkc.constructed-pair/0"


def decode(data, *, expected=None):
    """Read exactly the current shape; optionally pin a request-owned pair."""
    version, producer, validator = lean_render.record(data, 3)
    lean_render.require(version == FORMAT, "wrong pair export version")
    for child in (producer, validator):
        lean_render.record(child, 10)
        lean_render.require(child[0] == participant.FORMAT, "wrong participant export version")
        for identity in child[1:3]:
            lean_render.require(isinstance(identity, str)
                                and re.fullmatch(r"sha256:[0-9a-f]{64}", identity), "invalid artifact identity")
        policy = lean_render.record(child[3], 11)
        lean_render.require(policy[0] == "zkc.native-proof-policy/0", "wrong policy version")
        lean_render.require(all(isinstance(policy[i], str) and policy[i] for i in (1, 2, 3)),
                            "invalid pair roles")
        lean_render.require(policy[2] != policy[3], "pair roles coincide")
        lean_render.require(isinstance(child[4], str) and child[4], "missing participant symbol")
        # Reuse exact operation, binding, type, reference and region validation.
        participant.render_declaration(child, "CheckedPairChild")
    lean_render.require(producer[1:4] == validator[1:4], "pair source, candidate or policy mismatch")
    lean_render.require(producer[4] != validator[4], "pair participants coincide")
    if expected is not None:
        lean_render.require(data == expected, "pair differs from fixed selection")
    return producer, validator


def render(data, namespace):
    producer, validator = decode(data)
    lean_render.namespace(namespace)
    children = "\n".join(participant.render_declaration(child, namespace + "." + role)
                         for role, child in (("Producer", producer), ("Validator", validator)))
    return f'''module

public import Zkc.Construction.AuthoredPair

@[expose] public section

{children}
namespace {namespace}

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end {namespace}
'''


if __name__ == "__main__":
    lean_render.render_main(render, __doc__)
