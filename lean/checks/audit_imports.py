#!/usr/bin/env python3
"""Maintain exhaustive audit imports independently of the public root imports."""

import argparse
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.packages import PACKAGES, OPTIONAL, selected as select_packages


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
             extra=(), audit_imports=(), extra_modules=()):
    excluded = {Path(tests) / "Audit.lean", Path(tests) / "LibraryImports.lean"}
    names = modules(root, library, excluded) + modules(root, tests, excluded)
    for directory in examples:
        names += modules(root, directory, excluded)
    for directory in tools:
        names += modules(root, directory, excluded)
    names = [name for name in names if name not in extra_modules] + list(extra_modules)
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


def proof_audit(root):
    """Load every proof-owned body, independent of the public authoring roots."""
    names = modules(root, "ProtocolProof") + modules(root, "ProtocolProofExamples")
    header = "module\n\n-- Maintained by audit_imports.py; private bodies are required.\n"
    header += "".join(f"import all {name}\n" for name in names)
    header += "import Lean.Util.CollectAxioms\n"
    return header + """

/-!
Audit every declaration owned by this package, including generated and private declarations.
Dependencies are traversed by Lean's axiom collector; only the standard logical axioms are
allowed. The package's ordinary build separately kernel-checks each theorem.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let owned := fun moduleName : Name ↦
    (`ProtocolProof).isPrefixOf moduleName || (`ProtocolProofExamples).isPrefixOf moduleName
  for imported in environment.header.modules do
    if owned imported.module && !imported.importAll then
      throwError "Proof audit requires private module data: {imported.module}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let owner := environment.header.moduleNames[index.toNat]!
    unless owned owner do continue
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Nonstandard axiom {axiomName} in {name} (module {owner})"
    checked := checked + 1
  if checked == 0 then
    throwError "No proof declarations were audited"
  logInfo m!"Axiom audit passed: {checked} package declarations; only propext, Classical.choice, Quot.sound."
"""


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
    selection.add_argument("--integration", action="append", choices=OPTIONAL,
                           help="check only the named optional packages (default: all)")
    args = parser.parse_args()
    # Audit the shared package from this downstream package. The foundation
    # itself stays Lean/Std-only and never depends on the core audit tool.
    program = PACKAGES['program'][0]
    # A legacy audit can import the non-module audit tool. Lean loads legacy
    # imports at the private level; assert that fact before traversing bodies.
    program_audit = '-- Maintained by audit_imports.py; legacy imports load full private module data.\n'
    program_audit += ''.join(f'import {name}\n' for name in modules(program, 'ZkcProgram'))
    program_audit += ('import ZkcTools.DeclarationAudit\n\n'
                      'run_cmd do\n'
                      '  let env ← Lean.getEnv\n'
                      '  for imported in env.header.modules do\n'
                      '    if (`ZkcProgram).isPrefixOf imported.module && !imported.importAll then\n'
                      '      throwError "shared program audit requires private module data: {imported.module}"\n'
                      '  ZkcTools.DeclarationAudit.check [`ZkcProgram] "PROGRAM-AUDIT-PASS"\n')
    outputs = {ROOT / 'Tests/ProgramAudit.lean': program_audit}
    outputs.update(expected(ROOT, "Zkc", "Tests", ["ZkcExamples"],
                       ["ZkcTools/Generation", "ZkcTools/JsonSupport", "ZkcTools/ProcessView", "ZkcTools/ProofAccount", "ZkcTools/Companions",
                        "ZkcTools/StructuredSource", "ZkcTools/ConstructionBindings"], marker="CORE-AUDIT-PASS",
                            extra_modules=("Tests.ProgramAudit",)))
    selected = [] if args.main_only else args.integration or sorted(INTEGRATIONS)
    for name in select_packages(selected):
        if name == "proof":
            root = PACKAGES[name][0]
            outputs[root / "ProtocolProofChecks.lean"] = proof_audit(root)
            continue
        if name not in INTEGRATIONS:
            continue
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
