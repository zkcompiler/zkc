"""The requirement problems both implementations answer.

A requirement problem is a finite vocabulary of terms, the facts assumed about
them, the implications between predicates, and the goals to decide. The native
engine derives an answer and a certificate for each goal; the independent Lean
checker replays that certificate. Both are asked the same problems in the same
order, so they are generated here once rather than written out twice.

The hundred and twenty generated problems come from a fixed seed: the point is
a wide sample of shapes that stays the same from run to run, not a new sample
each time.
"""

import itertools
import random

RULES = [["Field", "CommRing"], ["CommRing", "Ring"], ["Group", "Monoid"]]
VOCABULARY = ["Field", "CommRing", "Ring", "Group", "Monoid", "Unproved"]
SEED = 0x5A4C


def principal():
    """The hand-written problem, whose every derivation step is named later."""
    terms = [[None, "F"], [None, "Opening"], [None, "Other"],
             [1, "ValueField"], [2, "ValueField"], [3, "Base"]]
    assumptions = [["=", [1, 2]], ["=", [0, 3]], ["Field", [0]],
                   ["Embedding", [0, 5]], ["OpeningContract", [1]]]
    goals = [["CommRing", [4]], ["Ring", [0]], ["Field", [5]],
             ["Embedding", [4, 5]], ["Embedding", [5, 4]],
             ["OpeningContract", [2]], ["=", [3, 4]]]
    return ["zkc.requirements/1", terms, assumptions, RULES, goals]


def generated():
    """A fixed sample of problem shapes: associated members, identity, embedding."""
    rng = random.Random(SEED)
    for _ in range(120):
        size = rng.randrange(1, 7)
        terms = [[None, f"T{i}"] for i in range(size)]
        for i in range(2, size):
            if rng.randrange(2):
                terms[i] = [rng.randrange(i), f"Member{i % 2}"]
                if terms[i] in terms[:i]:
                    terms[i] = [None, f"T{i}"]
        assumptions = [["=", rng.choices(range(size), k=2)]
                       for _ in range(rng.randrange(4))]
        assumptions += [[rng.choice(VOCABULARY), [rng.randrange(size)]] for _ in range(3)]
        assumptions += [["Embedding", rng.choices(range(size), k=2)]]
        goals = [["=", list(pair)] for pair in itertools.product(range(size), repeat=2)]
        goals += [[v, [i]] for v in VOCABULARY for i in range(size)]
        goals += [["Embedding", list(pair)]
                  for pair in itertools.product(range(size), repeat=2)]
        yield ["zkc.requirements/1", terms, assumptions, RULES, goals]


def applications():
    """Pure selections: congruence, order, heads, and no inverse inference."""
    terms = [[None, "F"], [None, "G"], ["apply", "Cell", [0]],
             ["apply", "Cell", [1]], [2, "State"], [3, "State"]]
    yield ["zkc.requirements/1", terms, [["=", [0, 1]]], [],
           [["=", [2, 3]], ["=", [4, 5]]]]
    yield ["zkc.requirements/1", terms, [["=", [2, 3]]], [],
           [["=", [0, 1]], ["=", [4, 5]]]]
    rng = random.Random(SEED + 1)
    for _ in range(40):
        terms = [[None, "F"], [None, "G"]]
        for i in range(2, 6):
            term = ["apply", rng.choice(["Cell", "Seal"]),
                    rng.choices(range(i), k=rng.randrange(3))]
            terms.append(term if term not in terms else [None, f"Root{i}"])
        assumptions = [["=", rng.choices(range(len(terms)), k=2)]]
        goals = [["=", list(pair)] for pair in itertools.product(range(6), repeat=2)]
        yield ["zkc.requirements/1", terms, assumptions, [], goals]


def problems():
    """Every problem, as a pair of the problem and whether every model is enumerable.

    The last one has a hundred and twenty-eight terms: the engine answers it,
    but enumerating the partitions of that universe does not finish, so nothing
    here claims to know its answers from a model.
    """
    yield principal(), True
    for problem in generated():
        yield problem, True
    for problem in applications():
        yield problem, True
    # Implication cycles, zero-argument predicates, empty and open declarations,
    # target conditions and associated members are ordinary distinct facts.
    yield ["zkc.requirements/1", [], [["Ready", []]], [],
           [["Ready", []], ["Missing", []]]], True
    yield ["zkc.requirements/1", [[None, "T"]], [["A", [0]]],
           [["A", "B"], ["B", "A"]], [["B", [0]], ["Target.avx2", [0]]]], True
    # A resource limit never turns an unknown fact into a contradiction proof.
    yield ["zkc.requirements/1", [[None, f"T{i}"] for i in range(128)],
           [["=", [i, i + 1]] for i in range(127)], [], [["=", [0, 127]]]], False
