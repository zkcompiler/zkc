"""Select just recipes for the tested tree, including both paths of a rename."""

import os
from pathlib import PurePosixPath
import subprocess


ALL = ("test", "test-interactive", "test-written-knowledge", "test-formal")
CHARGE_CHECKS = {"WrittenCharge.lean", "ChargeConsumers.lean", "OccurrenceDepth.lean",
                 "FixedTableSampling.lean", "AuditCharge.lean", "ReplayCharge.lean",
                 "ProofArguments.lean", "SumcheckGoal.lean", "SourceRoundLaws.lean", "ReductionLayout.lean"}
INTERACTIVE_CHECKS = {"AuditInteractive.lean", "OracleNames.lean", "WorldObservation.lean",
                      "SourceProtocols.lean", "ConstructedSchnorr.lean", "constructed_merlin.py"}


def select(paths):
    recipes = set()
    for path in map(PurePosixPath, paths):
        if path.as_posix() in {"language/LANGUAGE.md", "language/CORE-LIBRARY.md"}:
            recipes.add("test-frontend")
            continue
        if path.suffix == ".md" or path.parts[0] == "docs":
            continue
        if path.as_posix() in {"lean/formal/Zkc/Tools/Formal/DrawCharge.lean",
                               "lean/compiler/Zkc/Frontend/Written/Charge.lean"}:
            recipes.add("test-written-charge")
            continue
        if path.parent == PurePosixPath("lean/formal/checks"):
            if path.name in CHARGE_CHECKS:
                recipes.add("test-written-charge")
                continue
            if path.name in INTERACTIVE_CHECKS:
                recipes.add("test-interactive")
                continue
            if path.name.endswith(".lean.in") or path.name in {"written_knowledge.py", "AuditWritten.lean"}:
                recipes.add("test-written-knowledge")
                continue
        # Compiler, formal libraries, source assemblies, manifests and harnesses
        # cross suite boundaries. Include new and unclassified inputs by default.
        return ALL
    if "test-written-knowledge" in recipes:
        recipes.discard("test-frontend")
    return tuple(recipe for recipe in (*ALL, "test-written-charge", "test-frontend") if recipe in recipes)


def select_diff(base, head):
    if base == "0" * 40 or subprocess.run(["git", "cat-file", "-e", base + "^{commit}"],
                                          stderr=subprocess.DEVNULL).returncode:
        return ALL
    data = subprocess.check_output(["git", "diff", "--no-renames", "--name-only", "-z", base, head, "--"])
    return select(os.fsdecode(path) for path in data.split(b"\0") if path)


if __name__ == "__main__":
    recipes = select_diff(os.environ["BASE"], os.environ["HEAD"])
    print("Selected recipes:", " ".join(recipes) or "none")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        print("recipes=" + " ".join(recipes), file=output)
