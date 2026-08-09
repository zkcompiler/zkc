"""Mint the unqualified negative variant of the shipped signature.

The registry's chain rule qualifies its appended round labels by occurrence,
and the layer entry at the foot of the chain qualifies its labels too, so a
homogeneous chain's rounds stay distinguishable.  This script produces the
same signature with contract-local indices on both, which is the negative
case: three occurrences of one contract then produce three identical label
sets and the composition refuses on the duplicate.  Deriving the variant from
the shipped signature keeps the two from drifting in anything but the
projection.

Usage: gkr_chain_signature.py SIGNATURE OUT --unqualified
"""

import json
import sys

LAYER_RULE = "zkc.rbr.gkr-width2-layer"
CHAIN_RULE = "zkc.rbr.gkr-width2-chain"


def main(argv: list[str]) -> int:
    if len(argv) != 4 or argv[3] != "--unqualified":
        sys.stderr.write(__doc__ or "")
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        signature = json.load(handle)

    for case in signature["rules"][LAYER_RULE]["body"]["rounds"]["cases"]:
        case["index_projection"] = "round_index"
    chain = signature["rules"][CHAIN_RULE]["body"]["appended_rounds"]
    for case in chain["cases"]:
        case["index_projection"] = "round_index"

    with open(argv[2], "w", encoding="utf-8") as handle:
        json.dump(signature, handle, indent=1, sort_keys=True)
        handle.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
