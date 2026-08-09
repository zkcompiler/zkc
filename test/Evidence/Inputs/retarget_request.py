"""Point a derivation request at a different sealed artifact.

A negative fixture differs from its positive by one perturbation, so it seals to
a different identity while its claim positions and descriptors are unchanged.
Rather than keeping a second near-identical request that would drift from the
first, this rewrites the identity in place, reading it from the sealed module so
nothing is transcribed by hand.

Usage: retarget_request.py REQUEST SEALED_MLIR
"""

import json
import re
import sys


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        text = handle.read()
    with open(argv[2], encoding="utf-8") as handle:
        sealed = handle.read()

    identities = set(re.findall(r'pir\.sealed\s+"[^"]*"\s+id\s+"([0-9a-f]{64})"',
                                sealed))
    if len(identities) != 1:
        sys.stderr.write(
            f"expected exactly one sealed artifact, found {len(identities)}\n")
        return 2
    target = identities.pop()

    request = json.loads(text)
    present = {node["artifact_id"]
               for node in _walk(request["derivation"])}
    if len(present) != 1:
        sys.stderr.write(
            f"the request names {len(present)} artifacts, expected one\n")
        return 2
    sys.stdout.write(text.replace(present.pop(), target))
    return 0


def _walk(node):
    """Every object in the request that names an artifact."""
    if isinstance(node, dict):
        if "artifact_id" in node:
            yield node
        for value in node.values():
            yield from _walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk(value)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
