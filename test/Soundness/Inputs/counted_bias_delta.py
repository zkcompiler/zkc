"""Check that two Fiat-Shamir bounds differ by exactly N draws of one bias.

The two witnesses come from the same protocol but for one added challenge, so
subtracting their bounds cancels everything the two share and leaves that
challenge's contribution alone. The per-draw distance is read from the
reference twin's own derivation rather than recomputed here: a check that
recomputes the formula it is checking has only proved the formula is stable.

Usage: counted_bias_delta.py PLAIN COUNTED PER_DRAW DRAWS
"""

import json
import sys
from fractions import Fraction


def linear(quantity: dict) -> Fraction:
    for term in quantity["resource_terms"]:
        if term["exponent"] == 1:
            return Fraction(term["coefficient"])
    return Fraction(0)


def main(argv: list[str]) -> int:
    if len(argv) != 5:
        sys.stderr.write(__doc__ or "")
        return 2
    plain, counted = [
        json.load(open(path, encoding="utf-8"))["conclusion"]["result"]["bound"]
        ["quantity"] for path in argv[1:3]
    ]
    bias = json.load(open(argv[3], encoding="utf-8"))
    draws = int(argv[4])
    expected = draws * Fraction(int(bias["bias_numerator"]),
                                int(bias["bias_denominator"]))
    moved = Fraction(counted["constant"]) - Fraction(plain["constant"])
    print("constant moved by %d draws: %s"
          % (draws, "yes" if moved == expected else "no (%s)" % moved))
    moved = linear(counted) - linear(plain)
    print("linear coefficient moved by %d draws: %s"
          % (draws, "yes" if moved == expected else "no (%s)" % moved))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
