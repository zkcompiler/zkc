#!/usr/bin/env python3
"""Add focused, valid HoleContracts used by ConstructionGraph tests."""

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()

    vocabulary = json.loads(args.source.read_text())
    holes = vocabulary["hole_contracts"]
    holes["zkc.hole.test-vector"] = {
        "kind": "evaluate",
        "operands": [
            {
                "sort": "value",
                "role": "items",
                "class": "tg",
                "count": "2",
            },
            {
                "sort": "handle",
                "role": "state",
                "class": "test-state",
            },
        ],
        "results": [
            {
                "sort": "value",
                "role": "output",
                "class": "tg",
                "count": "1",
            }
        ],
        "parameters": ["mode"],
        "semantic_parameters": ["relation"],
    }
    holes["zkc.hole.test-late"] = {
        "kind": "evaluate",
        "operands": [
            {
                "sort": "value",
                "role": "challenge",
                "class": "scalar",
                "count": "1",
            }
        ],
        "results": [
            {
                "sort": "handle",
                "role": "state",
                "class": "test-state",
            }
        ],
        "parameters": [],
        "semantic_parameters": [],
    }
    holes["zkc.hole.test-root"] = {
        "kind": "commit",
        "operands": [
            {
                "sort": "handle",
                "role": "state",
                "class": "test-state",
            }
        ],
        "results": [
            {
                "sort": "value",
                "role": "output",
                "class": "tg",
                "count": "1",
            }
        ],
        "parameters": [],
        "semantic_parameters": [],
    }
    args.destination.write_text(json.dumps(vocabulary, indent=2) + "\n")


if __name__ == "__main__":
    main()
