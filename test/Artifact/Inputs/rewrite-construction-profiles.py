#!/usr/bin/env python3
"""Create valid construction-profile authorities for lifecycle tests."""

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("case", choices=("cited-change", "uncited-addition"))
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()

    profiles = json.loads(args.source.read_text())
    if args.case == "cited-change":
        profiles["sponges"]["toy_duplex"]["capacity"] = 31
    else:
        profiles["sponges"]["zkc_test_unused"] = {
            "alphabet_order": "257",
            "capacity": 1,
            "rate": 1,
        }
    args.destination.write_text(json.dumps(profiles, indent=2) + "\n")


if __name__ == "__main__":
    main()
