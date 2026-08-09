#!/usr/bin/env python3
"""Add a parameter-carrying HoleContract, so the binding path is exercised.

The two production hole contracts declare no parameters, which leaves the
static and semantic parameter path represented but unrun: projection could
drop a binding, admission could accept a malformed one, and execution could
hand a supplier nothing, with every test still passing. This contract has the
same typed signature as the sigma commit — so the toy algebra behind it is
unchanged — plus one static parameter and one semantic parameter, which is the
whole point of it.
"""

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()

    vocabulary = json.loads(args.source.read_text())
    vocabulary["hole_contracts"]["zkc.hole.parameterized-commit"] = {
        "kind": "commit",
        "operands": [
            {"sort": "value", "role": "generator", "class": "tg", "count": "1"},
            {"sort": "handle", "role": "witness", "class": "sigma-witness"},
        ],
        "results": [
            {"sort": "value", "role": "commitment", "class": "tg",
             "count": "1"},
            {"sort": "handle", "role": "witness", "class": "sigma-witness"},
        ],
        "parameters": ["mode"],
        "semantic_parameters": ["reference_string"],
    }
    args.destination.write_text(json.dumps(vocabulary, indent=2) + "\n")


if __name__ == "__main__":
    main()
