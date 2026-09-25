#!/usr/bin/env python3
"""Maintain exhaustive audit imports independently of the public root imports."""

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def modules(root, directory, excluded=()):
    result = []
    for path in sorted((root / directory).rglob("*.lean")):
        if path.relative_to(root) in excluded:
            continue
        result.append(".".join(path.relative_to(root).with_suffix("").parts))
    if (root / (directory + ".lean")).exists() and Path(directory + ".lean") not in excluded:
        result.insert(0, directory.replace("/", "."))
    return result


def expected(root, library, tests, examples=(), tools=(), marker="WHOLE-LIBRARY-AUDIT-PASS"):
    excluded = {Path(tests) / "Audit.lean", Path(tests) / "LibraryImports.lean",
                # Executable wrappers each define the process-level `main`.
                # Audit their namespaced consumer/CLI implementations below,
                # and compile each wrapper separately as a Lake executable.
                Path("Tools/Interactive.lean"), Path("Tools/Artifact.lean"),
                Path("Tools/RequirementChecker.lean")}
    names = modules(root, library, excluded) + modules(root, tests, excluded)
    for directory in examples:
        names += modules(root, directory, excluded)
    for directory in tools:
        names += modules(root, directory, excluded)
    imports = (
        "-- Maintained by audit_imports.py; library, test, example and selected executable consumers are audited.\n"
        if tools else
        "-- Maintained by audit_imports.py; all library, test and example modules are audit inputs; tooling is separate.\n"
    )
    imports += "".join(f"import {name}\n" for name in names)
    families = [library, tests] + list(examples) + list(tools)
    audit = f"import {tests}.LibraryImports\nimport Tools.DeclarationAudit\n\n"
    # The widest audit names itself like the narrower ones do, so a build log
    # says which scope passed rather than leaving the broadest one as the
    # unlabelled default. Each library generated here gets its own name: two
    # scopes emitting one marker would be no more legible than the default.
    audit += ("run_cmd Tools.DeclarationAudit.check ["
              + ", ".join("`" + x.replace("/", ".") for x in families)
              + f"] \"{marker}\"\n")
    return {root / tests / "LibraryImports.lean": imports,
            root / tests / "Audit.lean": audit}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--main-only", action="store_true")
    args = parser.parse_args()
    outputs = expected(ROOT, "Zkc", "Tests", ["Examples"],
                       ["Tools/Interactive", "Tools/Artifact", "Tools/Crypto", "Tools/RequirementChecker"])
    if not args.main_only:
        outputs.update(expected(ROOT / "integrations/arklib", "ZkcArkLib", "TestsArkLib",
                                marker="ARKLIB-INTEGRATION-AUDIT-PASS"))
    for path, text in outputs.items():
        if args.write:
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise SystemExit(f"audit imports are stale: {path}; run audit_imports.py --write")
    print(f"audit import coverage: {len(outputs)} files checked")


if __name__ == "__main__":
    main()
