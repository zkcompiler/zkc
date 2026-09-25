"""The malformed release candidates both implementations must refuse.

A release instruction states that a value is no longer held, so a plan that
releases nothing, releases what it does not hold, releases twice, releases a
value a later instruction reads, or carries a release in a body that has no
storage to release is not a plan at all. Each candidate below is one edit of a
well-formed candidate the compiler produced, rather than a frozen copy, so the
compiler and the independent consumer are compared on the same ten programs and
the comparison follows the encoding instead of going stale against it.
"""

import copy


def malformed(released, projected):
    """Every malformed candidate, as a pair of the diagnostic and the candidate.

    `released` is a participant candidate compiled with storage release.
    `projected` is the same source projected to participants without it: a
    release belongs to a plan, and a logical body must refuse one whatever it
    names.
    """
    arguments = [parameter[0] for parameter in released[3][0][2]]
    body = released[3][0][4]

    def edited(change):
        value = copy.deepcopy(released)
        change(value)
        return value

    candidates = [
        ("interactive-release-empty",
         edited(lambda v: v[3][0][4][0].__setitem__(1, []))),
        ("interactive-release-unavailable",
         edited(lambda v: v[3][0][4][0].__setitem__(1, ["missing"]))),
        ("interactive-release-unavailable",
         edited(lambda v: v[3][0][4][0][1].append(arguments[0]))),
        ("interactive-release-unavailable",
         edited(lambda v: v[3][0][4].insert(1, ["release", [arguments[0]]]))),
        ("interactive-resource-reuse",
         edited(lambda v: v[3][0][4][0][1].append(arguments[1]))),
        ("interactive-resource-reuse",
         edited(lambda v: v[3][0][4].insert(-1, ["release", body[-1][1]]))),
        ("interactive-ssa",
         edited(lambda v: v[3][0][4][3].__setitem__(5, [arguments[0]]))),
        ("interactive-release-context",
         edited(lambda v: v[4][0][7].insert(0, ["release", ["v0"]]))),
        ("interactive-release-shape",
         edited(lambda v: v[3][0][4][0].append("unexpected"))),
    ]

    logical = copy.deepcopy(projected)
    logical[3][0][4].insert(0, ["release", [logical[3][0][2][0][0]]])
    candidates.append(("interactive-release-context", logical))
    return candidates
