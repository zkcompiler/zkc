"""Point a derivation request at a different sealed artifact.

A negative fixture differs from its positive by one perturbation, so it seals to
a different identity while its claim positions and descriptors are unchanged.
Rather than keeping a second near-identical request that would drift from the
first, this rewrites the identity in place, reading it from the sealed module so
nothing is transcribed by hand.

The artifact is named either by a sealed module, whose identity is read
out of its text, or by an artifact directory, where sealing named the
file for its own content. Both spellings appear in the suite because
both are what the surrounding test already has in hand.

Usage: retarget_request.py REQUEST (SEALED_MLIR | ARTIFACTS_DIR) [OUT]
"""

import json
import re
import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) not in (3, 4):
        sys.stderr.write(__doc__ or "")
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        text = handle.read()
    source = Path(argv[2])
    if source.is_dir():
        identities = {path.stem for path in source.glob("*.mlirbc")}
    else:
        identities = set(re.findall(
            r'pir\.sealed\s+"[^"]*"\s+id\s+"([0-9a-f]{64})"',
            source.read_text(encoding="utf-8")))
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
    retargeted = text.replace(present.pop(), target)
    if len(argv) == 4:
        Path(argv[3]).write_text(retargeted, encoding="utf-8")
    else:
        sys.stdout.write(retargeted)
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
