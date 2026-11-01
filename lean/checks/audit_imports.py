#!/usr/bin/env python3
"""Maintain exhaustive audit imports independently of the public root imports."""

import argparse
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.packages import PACKAGES, selected as select_packages


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


def expected(root, library, tests, examples=(), tools=(), marker="WHOLE-LIBRARY-AUDIT-PASS",
             extra=(), audit_imports=()):
    excluded = {Path(tests) / "Audit.lean", Path(tests) / "LibraryImports.lean"}
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
    audit = f"import {tests}.LibraryImports\n"
    audit += "".join(f"import {name}\n" for name in audit_imports)
    audit += "import ZkcTools.DeclarationAudit\n\n"
    # The widest audit names itself like the narrower ones do, so a build log
    # says which scope passed rather than leaving the broadest one as the
    # unlabelled default. Each library generated here gets its own name: two
    # scopes emitting one marker would be no more legible than the default.
    audit += ("run_cmd ZkcTools.DeclarationAudit.check ["
              + ", ".join("`" + x.replace("/", ".") for x in families)
              + f"] \"{marker}\"\n")
    audit += "".join(extra)
    return {root / tests / "LibraryImports.lean": imports,
            root / tests / "Audit.lean": audit}


# Each optional integration package: its library, its tests and its audit marker.
INTEGRATIONS = {
    "security": ("ZkcSecurity", "TestsSecurity", "SECURITY-AUDIT-PASS"),
    "arklib": ("ZkcArkLib", "TestsArkLib", "ARKLIB-AUDIT-PASS"),
    "clean": ("ZkcClean", "TestsClean", "CLEAN-INTEGRATION-AUDIT-PASS"),
}
# Further audits of a package's whole library: the security library's registry
# of named hypotheses, models and trusted links covers every proposition-valued
# declaration that heads a premise of one of its theorems.
EXTRA = {
    "security": ["run_cmd ZkcTools.DeclarationAudit.checkRegistry ZkcSecurity.Registry.audited "
               "[`ZkcSecurity, `ZkcSecurityTools, `ZkcSecurityExamples] \"REGISTRY-AUDIT-PASS\"\n"],
    "arklib": ["run_cmd ZkcTools.DeclarationAudit.checkRegistry (ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited) "
               "[`ZkcArkLib, `ZkcArkLibExamples] \"ARKLIB-REGISTRY-AUDIT-PASS\"\n"],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--main-only", action="store_true")
    selection.add_argument("--integration", action="append", choices=sorted(INTEGRATIONS),
                           help="check only the named optional packages (default: all)")
    args = parser.parse_args()
    outputs = expected(ROOT, "Zkc", "Tests", ["ZkcExamples"],
                       ["ZkcTools/Generation", "ZkcTools/JsonSupport", "ZkcTools/ProcessView", "ZkcTools/ProofAccount", "ZkcTools/Companions",
                        "ZkcTools/StructuredSource", "ZkcTools/ConstructionBindings"], marker="CORE-AUDIT-PASS")
    selected = [] if args.main_only else args.integration or sorted(INTEGRATIONS)
    for name in select_packages(selected)[1:]:
        library, tests, marker = INTEGRATIONS[name]
        examples = {"security": ["ZkcSecurityExamples"], "arklib": ["ZkcArkLibExamples"]}.get(name, [])
        tools = ["ZkcSecurityTools"] if name == "security" else []
        outputs.update(expected(PACKAGES[name][0], library, tests, examples=examples, tools=tools, marker=marker,
                                extra=EXTRA.get(name, ()),
                                audit_imports=("TestsSecurity.LibraryImports",) if name == "arklib" else ()))
    for path, text in outputs.items():
        if args.write:
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise SystemExit(f"audit imports are stale: {path}; run audit_imports.py --write")
    print(f"audit import coverage: {len(outputs)} files checked")


if __name__ == "__main__":
    main()
