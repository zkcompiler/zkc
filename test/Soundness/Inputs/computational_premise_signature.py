"""Mint a signature whose round-by-round entry carries a primitive advantage.

The restriction this exercises is the one that keeps every computationally
supported protocol out of the Fiat-Shamir track: the round-by-round to
state-restoration rules require their premise to have empty game support,
because multiplying a premise's round maximum by a formal move budget would
otherwise produce resource times primitive advantage, outside the admitted
normal form.  No shipped rule concludes at round-by-round with a game term, so
nothing in the tree reaches the guard, and a restriction nothing reaches is
one that goes false in silence -- which is how the interleaving diagnostic
went false.

The evalopen entry rule is the base: it prices one round from contract facts,
and here its bound gains an ARSDH advantage term.  The bound stays inside the
admitted normal form (ground plus advantage), so the signature loads and the
round-by-round conclusion derives; what must refuse is the hop that reads it.

Usage: computational_premise_signature.py SIGNATURE OUT
"""

import json
import sys

RULE = "zkc.rbr.evalopen"
BINDING = RULE + "@reduction:evalopen"


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        signature = json.load(handle)

    rule = signature["rules"][RULE]
    rule["parameters"].append({"name": "algebra", "sort": "algebra_instance"})
    rule["parameters"].append({"name": "srs_degree", "sort": "integer"})

    case = rule["body"]["rounds"]["cases"][0]
    case["bound"] = {
        "kind": "add",
        "operands": [
            case["bound"],
            {
                "kind": "primitive_advantage",
                "game": {
                    "ref": "zkc.assume.arsdh",
                    "instance_arguments": [
                        {"kind": "resolved_parameter", "reference": "algebra",
                         "sort": "algebra_instance"},
                        {"kind": "resolved_parameter", "reference": "srs_degree",
                         "sort": "integer"},
                    ],
                },
                # A ground substitution, so the rule declares no resource of
                # its own: the state-restoration port's empty resource schema
                # would otherwise refuse first and the game-support guard --
                # the one under test -- would never be reached.
                "resource_substitution": {
                    "tau": {"kind": "rational_literal", "literal": "128"}
                },
            },
        ],
    }

    binding = signature["bindings"][BINDING]
    binding["parameter_bindings"]["algebra"] = {
        "kind": "resolved_parameter", "reference": "algebra",
        "sort": "algebra_instance"}
    binding["parameter_bindings"]["srs_degree"] = {
        "kind": "resolved_parameter", "reference": "srs_degree",
        "sort": "integer"}

    with open(argv[2], "w", encoding="utf-8") as handle:
        json.dump(signature, handle, indent=1, sort_keys=True)
        handle.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
