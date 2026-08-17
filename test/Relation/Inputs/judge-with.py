#!/usr/bin/env python3
"""Run the relation judgment against a mutated contract, and render it flat.

Each case wants one field of the checked-in contract moved and the
resulting judgment read back. Doing that inline per case would put the
same JSON surgery in every RUN line, and rendering the document as one
line per list is what lets a check assert the disagreements *and* that
the agreements survived them.

Usage: judge-with.py TOOL ARTIFACT_PATH_FILE REGISTRY_DIR BYTES
                     EXPECTED_STATUS none | field.path=value[,...]
"""

import json
import pathlib
import subprocess
import sys

tool = sys.argv[1]
artifact = pathlib.Path(sys.argv[2]).read_text().strip()
registry = pathlib.Path(sys.argv[3])
relation_bytes = sys.argv[4]
expected = int(sys.argv[5])
mutations = sys.argv[6]

contracts = json.loads((registry / "relation-contracts.json").read_text())
entry = contracts["contracts"]["toy.r1cs.entry"]
if mutations != "none":
    for mutation in mutations.split(","):
        path, _, raw = mutation.partition("=")
        node = entry
        *parents, leaf = path.split(".")
        for step in parents:
            node = node[int(step)] if step.isdigit() else node.setdefault(step, {})
        # The replacement keeps the field's declared type. A field order
        # is a decimal *string*, and handing the loader an integer tests
        # the schema rather than the cross-check this case is about.
        node[leaf] = type(node[leaf])(raw) if leaf in node else raw

mutated = pathlib.Path("mutated-contracts.json")
mutated.write_text(json.dumps(contracts, indent=2, sort_keys=True) + "\n")

result = subprocess.run(
    [
        tool,
        artifact,
        "--contracts=%s" % mutated,
        "--contract=toy.r1cs.entry",
        "--protocol-vocabulary=%s" % (registry / "protocol-vocabulary.json"),
        "--construction-profile-registry=%s"
        % (registry / "construction-profiles.json"),
        "--relation-bytes=%s" % relation_bytes,
    ],
    capture_output=True,
    text=True,
)

if result.returncode != expected:
    print(
        "judge-with: expected status %d, got %d\n%s"
        % (expected, result.returncode, result.stderr.strip()),
        file=sys.stderr,
    )
    sys.exit(1)

# A tool that answered negatively still owes a document; saying so here
# means a check never has to remember to ask.
try:
    judgment = json.loads(result.stdout)
except json.JSONDecodeError:
    print("judge-with: the judgment is not a document:\n" + result.stdout[:400],
          file=sys.stderr)
    sys.exit(1)

print("disagreed: " + json.dumps(judgment["disagreed"]))
print("cross_checked: %d" % len(judgment["cross_checked"]))
print("computed: %d" % len(judgment["computed"]))
