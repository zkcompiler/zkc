#!/usr/bin/env python3
"""Maintain exhaustive private-body audits with isolated executable environments."""

import argparse
from pathlib import Path
import sys
import tomllib
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.packages import (LEAN, PACKAGES, OWNERS, add_selection, selection, audited,
                              package_directory, package_modules, below, tool_module, selected)

AUDITOR = tool_module('program', 'DeclarationAudit')
SECURITY_SCOPES = ['Zkc.Protocol.Bindings', 'Zkc.Protocol.Library.Families', 'Zkc.Protocol.Library.Mathematics', 'Zkc.Protocol.Library.Security', 'Zkc.Protocol.Library.Transformations', 'Zkc.Protocol.Logic', 'Zkc.Tools.IR.SourceProperties', 'Zkc.Tools.IR.TableCapacity', 'Zkc.Tools.Protocol', 'Zkc.Verification.Bindings', 'Zkc.Verification.Claims', 'Zkc.Verification.Families', 'Zkc.Verification.ProgramLogic']


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


def generated(name, root=LEAN):
    """Every generated audit file of a package, whether or not its own tree can build it."""
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
    audit = banner + f'import {tests}.LibraryImports\n'
    if name == 'verification':
        # Registry schemas are names, so they need not be semantic imports of
        # a client. Load every permitted dependency's stored declarations.
        audit += ''.join(f'import Zkc.Tests.{OWNERS[dependency]}.LibraryImports\n'
                         for dependency in selected([name]) if dependency != name)
    audit += f'import {AUDITOR}\n'
    roots = [prefix for prefix in PACKAGES[name][1]
             if any(below(module, prefix) for module in names)]
    audit += '\n' + audit_body(roots, name.upper() + '-AUDIT-PASS')
    if name == 'verification':
        scopes = [prefix for prefix in SECURITY_SCOPES
                  if any(below(module, prefix) for package in PACKAGES
                         for module in package_modules(package, root))]
        audit += ('\nrun_cmd ZkcTools.DeclarationAudit.checkRegistry '
                  'ZkcSecurity.Registry.audited ' + lean_names(scopes) +
                  ' "REGISTRY-AUDIT-PASS"\n')
    outputs[directory.joinpath(*tests.split('.')) / 'Audit.lean'] = audit
    # A command audit is named after its root below `Zkc.<Root>`; roots that would share
    # that name (a tool and a test driver both called Main) keep their root component.
    short = [tuple(entry.split('.')[2:]) for entry in entries]
    for entry in entries:
        suffix = entry.split('.')[2:]
        if short.count(tuple(suffix)) > 1:
            suffix = entry.split('.')[1:]
        target = directory.joinpath(*tests.split('.'), 'CommandAudits', *suffix).with_suffix('.lean')
        text = banner + f'import {entry}\nimport {AUDITOR}\n\n'
        outputs[target] = text + audit_body([entry], 'COMMAND-AUDIT-PASS')
    return outputs


def expected(name, root=LEAN):
    """The generated audit files kept in the package's source tree."""
    outputs = generated(name, root)
    if audited(name):
        return outputs
    # Without a Lake path to the auditor the package keeps its exhaustive inventory
    # only; check_consumer_audit.py builds its other audits in a consumer workspace.
    inventory = package_directory(name, root).joinpath(*f'Zkc.Tests.{OWNERS[name]}'.split('.')) / 'LibraryImports.lean'
    return {inventory: outputs[inventory]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    add_selection(parser)
    args = parser.parse_args()
    outputs, existing = {}, set()
    for name in selection(args):
        outputs.update(expected(name))
        existing.update(path for module, path in package_modules(name).items()
                        if generated_audit(module))
    for path in sorted(existing - outputs.keys()):
        if not args.write:
            raise SystemExit(f'obsolete generated audit: {path}; run audit_imports.py --write')
        if not path.read_text().startswith('-- Maintained by audit_imports.py;'):
            raise SystemExit(f'refusing to remove an unrecognized audit: {path}')
        path.unlink()
    for path, text in outputs.items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise SystemExit(f'audit imports are stale: {path}; run audit_imports.py --write')
    print(f'audit import coverage: {len(outputs)} files checked')


if __name__ == '__main__':
    main()
