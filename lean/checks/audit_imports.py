#!/usr/bin/env python3
"""Maintain exhaustive private-body audits with isolated executable environments."""

import argparse
from pathlib import Path
import sys
import tomllib
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.packages import (LEAN, PACKAGES, OWNERS, add_selection, selection,
                              package_directory, package_modules, below, tool_module)

AUDITOR = tool_module('program', 'DeclarationAudit')
SECURITY_SCOPES = ['Zkc.Applications.Security', 'Zkc.Protocol.Bindings', 'Zkc.Protocol.Library.Families', 'Zkc.Protocol.Library.Mathematics', 'Zkc.Protocol.Library.Security', 'Zkc.Protocol.Library.Transformations', 'Zkc.Protocol.Logic', 'Zkc.Tools.IR.SourceProperties', 'Zkc.Tools.IR.TableCapacity', 'Zkc.Tools.Protocol', 'Zkc.Tools.Verification.Bindings', 'Zkc.Tools.Verification.ClaimConstruction', 'Zkc.Tools.Verification.ComponentAuthoringReport', 'Zkc.Tools.Verification.ComponentBridge', 'Zkc.Tools.Verification.ComponentDerivation', 'Zkc.Tools.Verification.ComponentReadback', 'Zkc.Tools.Verification.ComponentView', 'Zkc.Tools.Verification.Components', 'Zkc.Tools.Verification.Generation', 'Zkc.Tools.Verification.InputLaws', 'Zkc.Tools.Verification.PairConstruction', 'Zkc.Tools.Verification.SigmaReadback', 'Zkc.Tools.Verification.SourceInputClauses', 'Zkc.Tools.Verification.SourceInputReadback', 'Zkc.Tools.Verification.SourceProperties', 'Zkc.Tools.Verification.SubjectABI', 'Zkc.Tools.Verification.Sumcheck', 'Zkc.Tools.Verification.TargetEvaluation', 'Zkc.Verification.Bindings', 'Zkc.Verification.Claims', 'Zkc.Verification.Families', 'Zkc.Verification.Mathematics', 'Zkc.Verification.ProgramLogic', 'Zkc.Verification.Transformations']
ARKLIB_SCOPES = ['Zkc.Adapters.ArkLib', 'Zkc.Applications.ArkLib']


def generated_audit(module):
    return module.startswith('Zkc.Tests.') and (
        module.rsplit('.', 1)[-1] in {'Audit', 'LibraryImports', 'ProgramAudit'} or
        '.CommandAudits.' in module)


def commands(name, root=LEAN):
    config = tomllib.loads((package_directory(name, root) / 'lakefile.toml').read_text())
    return sorted({entry['root'] for entry in config.get('lean_exe', [])})


def lean_names(roots):
    return '[' + ', '.join('`' + prefix for prefix in roots) + ']'


def audit_body(roots, marker):
    return ('run_cmd do\n'
            '  let env ← Lean.getEnv\n'
            f'  let families : List Lean.Name := {lean_names(roots)}\n'
            '  for imported in env.header.modules do\n'
            '    if families.any (·.isPrefixOf imported.module) && !imported.importAll then\n'
            '      throwError "audit requires private module data: {imported.module}"\n'
            f'  ZkcTools.DeclarationAudit.check families "{marker}"\n')


def expected(name, root=LEAN):
    directory = package_directory(name, root)
    tests = f'Zkc.Tests.{OWNERS[name]}'
    modules = package_modules(name, root)
    entries = commands(name, root)
    # Commands define global main independently. Each has its own full audit;
    # importing unrelated commands together would be an invalid Lean environment.
    names = [module for module in modules if not generated_audit(module)
             and module not in entries and module != 'Zkc.Applications.CleanAudit']
    banner = '-- Maintained by audit_imports.py; legacy imports load private bodies.\n'
    imports = banner + ''.join(f'import {module}\n' for module in names)
    outputs = {directory.joinpath(*tests.split('.')) / 'LibraryImports.lean': imports}
    audit = banner + f'import {tests}.LibraryImports\nimport {AUDITOR}\n'
    if name == 'applications':
        # Registry schemas include actual subjects. Validate the complete tables
        # once at their assembly owner; core packages still audit every axiom.
        for dependency in PACKAGES:
            if dependency != name:
                audit += f'import Zkc.Tests.{OWNERS[dependency]}.LibraryImports\n'
    roots = [prefix for prefix in PACKAGES[name][1]
             if any(below(module, prefix) for module in names)]
    audit += '\n' + audit_body(roots, name.upper() + '-AUDIT-PASS')
    if name == 'applications':
        audit += ('\nrun_cmd ZkcTools.DeclarationAudit.checkRegistry '
                  'ZkcSecurity.Registry.audited ' + lean_names(SECURITY_SCOPES) +
                  ' "REGISTRY-AUDIT-PASS"\n')
        audit += ('run_cmd ZkcTools.DeclarationAudit.checkRegistry '
                  '(ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited) ' +
                  lean_names(ARKLIB_SCOPES) + ' "ARKLIB-REGISTRY-AUDIT-PASS"\n')
    outputs[directory.joinpath(*tests.split('.')) / 'Audit.lean'] = audit
    for entry in entries:
        suffix = entry.split('.')[2:]
        target = directory.joinpath(*tests.split('.'), 'CommandAudits', *suffix).with_suffix('.lean')
        text = banner + f'import {entry}\nimport {AUDITOR}\n\n'
        outputs[target] = text + audit_body([entry], 'COMMAND-AUDIT-PASS')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    add_selection(parser)
    args = parser.parse_args()
    outputs = {}
    for name in selection(args):
        outputs.update(expected(name))
    for path, text in outputs.items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise SystemExit(f'audit imports are stale: {path}; run audit_imports.py --write')
    print(f'audit import coverage: {len(outputs)} files checked')


if __name__ == '__main__':
    main()
