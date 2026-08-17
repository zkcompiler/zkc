#!/usr/bin/env python3
"""Hold a generated vocabulary to the checked-in one where they overlap.

The seal judgment is fail-closed against a closed vocabulary, and for a
generated instance that vocabulary is written by the same tool that
wrote the spine it will judge. That is the arrangement working for
entries the family mints for itself: seal holds the spine to a
contract, whoever wrote it. It is not the arrangement working for
entries that also exist in the repository's registry, where a
generator could redefine a contract and then satisfy its own
redefinition — seal would pass over a protocol that means something
else than the registry says.

So every identifier the two documents share carries the same
definition, with one exemption below, and an exemption that stops being
needed is itself a failure: a stale one would hide the next drift.
"""

import json
import sys
from pathlib import Path

# An entry whose generated form differs from the registry's by design,
# with the reason. Anything not listed here must match exactly.
EXEMPT = {
    "reduction_contracts.fri": (
        "the contract is depth-parameterized: the registry pins the shipped "
        "depth-one form, and an instance of depth k emits the depth-k form, "
        "which is the same theorem over more rounds"
    ),
}


def canonical(value) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


generated = json.loads(Path(sys.argv[1]).read_text())
registry = json.loads(Path(sys.argv[2]).read_text())

shared = 0
drifted = []
exercised = set()
for section in sorted(set(generated) & set(registry)):
    left, right = generated[section], registry[section]
    if not isinstance(left, dict) or not isinstance(right, dict):
        continue
    for name in sorted(set(left) & set(right)):
        key = f"{section}.{name}"
        shared += 1
        if canonical(left[name]) == canonical(right[name]):
            continue
        if key in EXEMPT:
            exercised.add(key)
            continue
        drifted.append(key)

failures = []
if drifted:
    failures.append(
        "generated vocabulary redefines registry entries: "
        + ", ".join(drifted)
    )
stale = sorted(set(EXEMPT) - exercised)
if stale:
    failures.append(
        "exemptions no longer needed, and a stale one hides the next "
        "drift: " + ", ".join(stale)
    )
if shared == 0:
    failures.append("no shared identifiers: the gate would pass vacuously")

if failures:
    for line in failures:
        print(line)
    raise SystemExit(1)
print(f"{shared} shared identifiers, {len(exercised)} exempt, none redefined")
