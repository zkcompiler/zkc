"""Replace a derivation request's plan root with one of its premises.

Used to build the negative case for a root assumption without keeping a second
near-identical request in the tree: the positive request stays the only place
the plan is authored, so the two cannot drift apart.

Usage: hoist_plan_root.py REQUEST PORT
"""

import json
import sys


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write("usage: hoist_plan_root.py REQUEST PORT\n")
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        request = json.load(handle)
    plan = request["derivation"]["plan"]
    premises = plan.get("premises") or {}
    if argv[2] not in premises:
        sys.stderr.write(f"the plan root has no premise {argv[2]!r}\n")
        return 2
    request["derivation"]["plan"] = premises[argv[2]]
    json.dump(request, sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
