"""Relate a round-by-round preservation premise by `same_subject`.

The composition a preservation body performs is stated over two round
sequences that argue about the same state: the claim the premise's final
round leaves unsatisfied must be the one the conclusion's occurrence
consumes.  Both shipped preservation bindings relate their premise by
`consumed_claim`, so the connection holds today -- but it holds because
every binding author chose that relation, not because the body checks it.

This widener rewrites one preservation binding to `same_subject`, which is
an admitted relation the loader accepts.  What it demonstrates is which
layer answers: the coverage check refuses first, because a produced
consumed claim of the occurrence is then selected by no premise relation.
The body's own join stands behind that gate for the case coverage cannot
see -- a premise derived at a path occurrence, whose rounds name no state
at all.

Usage: loosen_preservation_relation.py <signature.json> <target.json>
"""

import json
import sys

BINDING = "zkc.rbr.gkr-width2-chain@reduction:gkr_width2_addmul_layer"
PORT = "source_rbr"


def main() -> None:
    source, target = sys.argv[1], sys.argv[2]
    with open(source, encoding="utf-8") as handle:
        document = json.load(handle)
    binding = document["bindings"][BINDING]
    relations = binding["premise_relations"]
    if PORT not in relations:
        raise SystemExit(f"{BINDING} has no premise port {PORT!r}")
    relations[PORT] = {"kind": "same_subject"}
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(document, handle, indent=2)
        handle.write("\n")


if __name__ == "__main__":
    main()
