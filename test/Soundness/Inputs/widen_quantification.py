"""Clone every admitted security index at adaptive_instance.

The shipped registry admits only static indices, which makes the
adaptivity coordinate fail-closed but also unexercisable: no test can
carry a non-static value through the variable rules. This widener is
what the evaluator stress test loads on its second run — the same
signature, schema-only change, so every rule and binding digest is
unchanged and the carrying rules run against a vocabulary in which the
adaptive forms exist.
"""

import json
import sys


def main() -> None:
    source, target = sys.argv[1], sys.argv[2]
    with open(source, encoding="utf-8") as handle:
        document = json.load(handle)
    indices = document["schemas"]["security_indices"]
    # Skipping what is already declared: the vocabulary admits only
    # static indices today, but the first adaptive one it declares would
    # otherwise be minted twice here, and the catalog's duplicate check
    # would fail the widened run for a reason that has nothing to do
    # with the carry it exists to exercise.
    present = {tuple(sorted(index.items())) for index in indices}
    for index in list(indices):
        clone = dict(index)
        clone["quantification"] = "adaptive_instance"
        if tuple(sorted(clone.items())) in present:
            continue
        present.add(tuple(sorted(clone.items())))
        indices.append(clone)
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(document, handle, indent=2)
        handle.write("\n")


if __name__ == "__main__":
    main()
