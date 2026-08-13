"""Print one prover vector in the reference executor's own output shape.

The emitted crate replays the committed vector; `zkc-run --prove` prints
what the interpreter produced. Rendering the vector into the interpreter's
two lines lets the test diff them directly, so the corpus and the
reference are compared rather than each being compared to a literal
spelled twice.
"""

import json
import sys


def main() -> int:
    path, name = sys.argv[1], sys.argv[2]
    with open(path, encoding="utf-8") as handle:
        corpus = json.load(handle)
    for vector in corpus["prover_vectors"]:
        if vector["name"] != name:
            continue
        print("prover challenges: " + " ".join(vector["challenges"]))
        print("proof: " + vector["proof"])
        return 0
    print(f"no vector named {name!r} in {path}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
