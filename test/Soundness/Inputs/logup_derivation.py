"""Re-derive the lookup bounds from the lemma, and compare to the signature.

The second reading of a source, not a second implementation of one reading:
`fri_soundcalc.py` exists for the same reason, and its history is the reason
both do. Two implementations of a misreading agree with each other.

The source is Haböck, *Multivariate lookups based on logarithmic derivatives*,
ePrint 2022/1530. Lemma 5 (set inclusion), as stated there:

    Let F be a field of characteristic p > N, and suppose that (a_i), (b_i)
    are arbitrary sequences of field elements, both of length N. Then
    {a_i} subset of {b_i} as sets, if and only if there exists a sequence
    (m_i) of field elements such that

        sum_i 1/(X + a_i) = sum_i m_i/(X + b_i)

    in the function field F(X).

Everything below is derived from that statement here, in this file, and the
arithmetic is exact.
"""

import json
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def characteristic_condition(table: int, lookups: int) -> int:
    """The common length the lemma's hypothesis is about.

    The lemma is stated for two sequences of one length N under char > N.
    Unequal lengths reduce to it by padding the shorter side with a repeated
    table entry: padding the lookup side with a table element changes neither
    the inclusion nor its truth, and padding the table side with duplicates of
    an existing entry only merges fractions onto a denominator already there,
    which the fractional decomposition (the paper's Lemma 4, which needs no
    hypothesis on the characteristic) absorbs. Either way the padded common
    length is the larger of the two.

    Both sides need the hypothesis, which is why it is not the lookup side
    alone: the proof reads the lookup-side multiplicities m_a(z) <= lookups as
    non-zero field elements, and its honest witness is m_a(b_i)/m_b(b_i), so
    the table-side multiplicities m_b(b_i) <= table must be invertible.
    """
    return max(table, lookups)


def soundness_numerator(table: int, lookups: int) -> int:
    """Points at which a false inclusion survives a uniformly sampled beta.

    Clear denominators in the identity of the lemma. Writing P for the product
    of all table + lookups linear factors, each side becomes a sum of terms,
    and every term is P with exactly one of its factors cancelled. So each term
    has degree table + lookups - 1, the difference of the two sides does too,
    and a false inclusion makes that difference a non-zero polynomial of that
    degree. A non-zero polynomial of degree d has at most d roots, so at most
    that many sampled points hide it.

    The vanishing points are not an extra escape. Where a denominator vanishes
    the produced claim is false by its own statement -- it asserts the sums are
    defined as well as equal -- so those points do not need to be added here.
    """
    return table + lookups - 1


def completeness_numerator(table: int, lookups: int) -> int:
    """Points at which an honest prover's claim fails.

    An honest prover holds a true inclusion and the lemma's multiplicities, so
    the fractional identity holds as an identity of rational functions and its
    instance at a sampled point can fail only by being undefined. That happens
    exactly at the poles: beta = -b_j for a table entry, or beta = -a_i for a
    looked-up value. This is a count of a set, not the degree of a polynomial,
    so it is one larger than the soundness numerator over the same quantities
    -- the two tracks are asymmetric and the asymmetry is not an off-by-one.
    """
    return table + lookups


def declared(signature: dict, rule: str, contract: str) -> tuple[dict, dict]:
    binding = signature["bindings"][f"{rule}@reduction:{contract}"]
    return signature["rules"][rule], binding


def arity_of(signature_vocabulary: dict, contract: str, role: str) -> int:
    """The arity a role's commitments declare, as the artifact states it."""
    profile = ROLE_PROFILES[contract][role]
    return 1 << signature_vocabulary["value_profiles"][profile]["arity_log2"]


ROLE_PROFILES = {
    "logup_bus": {
        "table": "logup_committed_column",
        "queries": "logup_committed_column",
        "multiplicities": "logup_committed_column",
    },
    "logup_range_check": {
        "table": "logup_table",
        "queries": "logup_queries",
        "multiplicities": "logup_multiplicities",
    },
}
SPACE = 2305843009213693951


def main() -> int:
    signature = json.loads(
        (REPO / "registry" / "soundness-signature.json").read_text())
    vocabulary = json.loads(
        (REPO / "registry" / "protocol-vocabulary.json").read_text())

    failures = []
    checked: set[str] = set()
    for contract in sorted(ROLE_PROFILES):
        table = arity_of(vocabulary, contract, "table")
        lookups = arity_of(vocabulary, contract, "queries")
        multiplicities = arity_of(vocabulary, contract, "multiplicities")

        # The lemma's witness sequence has one element per table entry, so a
        # multiplicity column of another length is not the object it is about.
        if multiplicities != table:
            failures.append(
                f"{contract}: multiplicities {multiplicities} != table {table}")

        expected_soundness = Fraction(soundness_numerator(table, lookups),
                                      SPACE)
        expected_completeness = Fraction(
            completeness_numerator(table, lookups), SPACE)

        # What the rules say, read back out of the signature's own text.
        rule = signature["rules"]["zkc.rbr.logup"]
        case = rule["body"]["rounds"]["cases"][0]
        shape = json.dumps(case["bound"]["quantity"], sort_keys=True)
        if '"sub"' not in shape or '"literal": "1"' not in shape:
            failures.append(
                f"{contract}: the soundness bound does not subtract the one "
                "degree the cleared identity loses")
        completeness = signature["rules"]["zkc.completeness.logup"]
        if '"sub"' in json.dumps(completeness["body"]["bound"], sort_keys=True):
            failures.append(
                f"{contract}: the completeness bound subtracts a degree, but "
                "its numerator counts a set of poles rather than a degree")

        # Against the judgments themselves, when the caller hands them over:
        # the numbers a derivation actually produced, not the numbers the
        # signature's text implies. A judgment is matched to the contract its
        # own binding names — accepting it because it equals *some* contract's
        # number would let a bound belonging to a smaller instance pass as
        # re-derived for a larger one.
        for path in sys.argv[1:]:
            document = json.loads(Path(path).read_text())
            binding = document["derivation"]["plan"]["binding"]
            if not binding.endswith(f"@reduction:{contract}"):
                continue
            conclusion = document["conclusion"]
            if conclusion["index"]["track"] == "completeness":
                actual = conclusion["result"]["bound"]["quantity"]["constant"]
                wanted = expected_completeness
            else:
                rounds = conclusion["result"]["rounds"]
                actual = rounds[0]["bound"]["quantity"]["constant"]
                wanted = expected_soundness
            if Fraction(actual) != wanted:
                failures.append(
                    f"{Path(path).name}: reports {actual} where {contract} "
                    f"re-derives {wanted.numerator}/{wanted.denominator}")
            else:
                print(f"{Path(path).name}: {actual} re-derived from the lemma")
            checked.add(path)

        print(f"{contract}: soundness {expected_soundness.numerator}/"
              f"{expected_soundness.denominator}, completeness "
              f"{expected_completeness.numerator}/"
              f"{expected_completeness.denominator}, "
              f"characteristic must exceed "
              f"{characteristic_condition(table, lookups)}")

    for path in sys.argv[1:]:
        if path not in checked:
            failures.append(
                f"{path}: names no contract this file re-derives")
    for line in failures:
        print(line)
    if failures:
        return 1
    print("logup: every theorem-derived bound matches the declared bound")
    return 0


if __name__ == "__main__":
    sys.exit(main())
