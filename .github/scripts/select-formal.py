"""Select just recipes for the tested tree, including both paths of a rename."""

import os
from pathlib import PurePosixPath
import subprocess


ALL = ("test", "test-interactive", "test-written-knowledge", "test-formal")
CHARGE_CHECKS = {"WrittenCharge.lean", "ChargeConsumers.lean", "OccurrenceDepth.lean",
                 "FixedTableSampling.lean", "AuditCharge.lean", "ReplayCharge.lean"}
INTERACTIVE_CHECKS = {"AuditInteractive.lean", "OracleNames.lean", "WorldObservation.lean",
                      "SourceProtocols.lean"}


def select(paths):
    recipes = set()
    for path in map(PurePosixPath, paths):
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
    return tuple(recipe for recipe in (*ALL, "test-written-charge") if recipe in recipes)


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
