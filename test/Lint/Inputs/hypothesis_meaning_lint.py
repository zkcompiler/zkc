"""Every hypothesis a rule carries must say what discharging it takes.

A machine condition is decided by an evaluator, so its meaning is the code
that decides it and a reader who wants it can go there. A hypothesis is
decided by nobody: the judgment names it and hands it out, and a reader who
meets a name with no sentence behind it has no way to discharge it. That
asymmetry is why this lint covers hypotheses and not conditions.

The signature's annotations are not in its canonical document, so a loader
cannot refuse this and the digest does not cover it. A lint is what is
available, and it is what the diagnostic allocation already uses for the
same shape of claim about its own sentences.
"""

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
DEFAULT = REPO / "registry" / "soundness-signature.json"


def main(argv: list[str]) -> int:
    path = Path(argv[1]) if len(argv) > 1 else DEFAULT
    signature = json.loads(path.read_text())
    annotations = signature["annotations"]
    # A carried proposition is declared in one of two blocks: propositions
    # for the ones nobody decides, machine deciders for the ones an evaluator
    # does. Both can be carried out to a reader through an external-hypothesis
    # slot, and a name in either is declared.
    declared = dict(signature["schemas"]["propositions"])
    declared.update(signature["schemas"]["machine_deciders"])

    # Every proposition a rule carries out to the reader, whatever its name
    # begins with. Filtering on one prefix would leave the same defect in the
    # neighbouring namespaces, which is how it reached the tree twice.
    carried = sorted({
        slot["proposition_ref"]
        for rule in signature["rules"].values()
        for slot in rule.get("external_hypotheses", [])
    })

    failures = []
    for name in carried:
        entry = annotations.get(name)
        if entry is None:
            failures.append(f"{name} is carried by a rule and annotated nowhere")
            continue
        # Either form records a meaning: a sentence of its own, or a note
        # saying where it is discharged together with the source it rests on.
        if not (entry.get("statement")
                or (entry.get("notes") and entry.get("statement_basis"))):
            failures.append(f"{name} has an annotation that states no meaning")

    for name in sorted(annotations):
        if name.startswith(("zkc.hyp.", "zkc.side.")) and name not in declared:
            failures.append(f"{name} is annotated and declared nowhere")

    for line in failures:
        print(line)
    print(f"{len(carried) - len([f for f in failures if 'carried' in f or 'states no meaning' in f])}"
          f"/{len(carried)} carried propositions state what discharging them takes")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
