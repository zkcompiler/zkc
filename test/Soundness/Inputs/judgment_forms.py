"""Every body kind in the signature is an instance of a declared form.

`docs/spec/soundness.md` §5.1 fixes five judgment forms and states the rule
that admits a new one: entry, preservation, and scaling are data, and a new
*transformation recipe* is the one admitted reason to add a body kind, as a
specification event rather than an enum that grew.

A prose rule nobody checks is a prose rule that drifts -- the repository has
made this move twice already, for diagnostic allocation and for the `means`
sentences -- so the classification is machine-readable here and compared
against the signature the tree actually ships. Adding a body kind without
placing it in a form fails; placing it under `transformation` is possible,
and is exactly the visible moment §5.1 asks for.

Usage: judgment_forms.py <signature.json>
"""

from __future__ import annotations

import json
import sys

# The partition §5.1 declares. Chosen, not discovered: `round_scaling` folds
# into preservation if one prefers four forms, and the spec says so. What
# this table is for is that the choice is written down in one place and
# checked, rather than being re-derived differently by each reader.
FORMS = {
    "entry": {
        "special_soundness_entry",
        "native_round_by_round_entry",
        "computational_entry",
        "completeness_entry",
    },
    "preservation": {
        "special_soundness_preservation",
        "round_by_round_preservation",
    },
    "scaling": {
        "round_scaling",
    },
    "transformation": {
        "special_soundness_to_round_by_round",
        "round_by_round_to_state_restoration",
        "state_restoration_to_fiat_shamir_duplex",
    },
}

# Cut is the fifth form and deliberately has no body kind: discharging an
# assumption against a derivation of it is structural, so it lives in the
# derivation plan rather than in the signature (§3.4, §6).
STRUCTURAL_FORMS = {"cut"}


def main() -> None:
    with open(sys.argv[1], encoding="utf-8") as handle:
        signature = json.load(handle)

    classified = {}
    for form, kinds in FORMS.items():
        for kind in kinds:
            if kind in classified:
                raise SystemExit(
                    f"body kind {kind!r} is placed in two forms: "
                    f"{classified[kind]!r} and {form!r}"
                )
            classified[kind] = form

    used = {}
    for name, rule in sorted(signature["rules"].items()):
        kind = rule["body"]["kind"]
        form = classified.get(kind)
        if form is None:
            raise SystemExit(
                f"rule {name!r} has body kind {kind!r}, which no judgment form "
                "in docs/spec/soundness.md §5.1 claims. A new rule is admitted "
                "as data under entry, preservation, or scaling; a new "
                "transformation recipe is a specification event and is added "
                "to this table with the theorem it mechanizes."
            )
        used.setdefault(form, set()).add(kind)

    unused = {
        kind for kinds in FORMS.values() for kind in kinds
    } - set().union(*used.values()) if used else set()
    if unused:
        raise SystemExit(
            "these body kinds are classified but no rule uses them, so the "
            f"table describes something the signature does not have: {sorted(unused)}"
        )

    print("judgment forms: every body kind is an instance of a declared form")
    for form in sorted(FORMS):
        kinds = sorted(used.get(form, ()))
        print(f"  {form}: {len(kinds)} " + ", ".join(kinds))
    for form in sorted(STRUCTURAL_FORMS):
        print(f"  {form}: structural, no body kind")


if __name__ == "__main__":
    main()
