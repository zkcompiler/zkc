"""Architecture controls on synthetic migrated sources; no Lean or downloads.

This file also runs with the standard library unittest runner, so the migration
can validate its Python contracts before a migrated Lake workspace exists.
"""
import argparse
from contextlib import nullcontext
import importlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import tomllib
from types import SimpleNamespace
import unittest
from unittest.mock import patch

REPOSITORY = Path(__file__).resolve().parents[3]


class LeanArchitecture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / 'lean'
        self.root.mkdir()
        self.saved = {name: module for name, module in sys.modules.items()
                      if name.split('.')[0] in ('support', 'checks', 'reproduce')}
        for name in self.saved:
            del sys.modules[name]
        self.addCleanup(self.restore_modules)
        original_path = sys.path[:]
        self.addCleanup(lambda: sys.path.__setitem__(slice(None), original_path))
        sys.path.insert(0, str(self.root))
        for relative in ('support/packages.py', 'support/dependencies.py', 'support/lean_headers.py',
                         'support/responsibility.py', 'support/lake.py', 'support/compatibility.py',
                         'checks/check_library.py', 'checks/check_package_ownership.py',
                         'checks/audit_imports.py', 'checks/records/declarations.py', 'reproduce.py',
                         'bridges/common/lean_render.py'):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPOSITORY / 'lean' / relative, target)
        self.packages = importlib.import_module('support.packages')
        p = self.packages
        policy = {'layers': [[prefix, name] for name, (_, roots) in p.PACKAGES.items() for prefix in roots],
                  'allowed': [[name, [*p.selected([name]), 'upstream']] for name in p.PACKAGES] +
                             [['upstream', ['upstream']]], 'guards': [], 'exceptions': []}
        for name, (directory, roots) in p.PACKAGES.items():
            directory.mkdir(parents=True)
            (directory / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            for prefix in roots:
                self.source(prefix + '.Example', 'module\nimport Std\n')
            self.source(roots[0], 'module\nimport Std\n')
            required = [{'name': p.NAMES[dep], 'path': os.path.relpath(p.PACKAGES[dep][0], directory)}
                        for dep in p.DEPENDENCIES[name]]
            required += [{'name': dep, 'git': 'https://example.invalid/' + dep, 'rev': 'a' * 40}
                         for dep in sorted(p.UPSTREAM[name])]
            locks = [{'name': p.NAMES[dep], 'type': 'path',
                      'dir': os.path.relpath(p.PACKAGES[dep][0], directory)}
                     for dep in p.selected([name]) if dep != name]
            locks += [{'name': dep, 'type': 'git', 'url': 'https://example.invalid/' + dep, 'rev': 'a' * 40}
                      for dep in sorted(p.allowed_dependencies(name) - set(p.NAMES.values()))]
            (directory / 'lake-manifest.json').write_text(json.dumps({'name': p.NAMES[name], 'packages': locks}))
            config = 'name = ' + json.dumps(p.NAMES[name]) + '\ndefaultTargets = ' + json.dumps(list(roots)) + '\n'
            for requirement in required:
                config += '\n[[require]]\n' + ''.join(f'{key} = {json.dumps(value)}\n' for key, value in requirement.items())
            for prefix in roots:
                config += ('\n[[lean_lib]]\nname = ' + json.dumps(prefix) + '\nroots = ' +
                           json.dumps([prefix]) + '\nglobs = ' + json.dumps([prefix + '.+']) + '\n')
            (directory / 'lakefile.toml').write_text(config)
        self.source('Zkc.Tools.Program.IR.DeclarationAudit',
                    'import Lean\n-- BEGIN DEPENDENCY POLICY\nprivate def dependencyPolicyJson : String := r##"' +
                    json.dumps(policy) + '"##\n-- END DEPENDENCY POLICY\n')
        self.source('Zkc.Tools.Program.IR.ImportHeaders', 'import Lean\n')
        self.source('Zkc.Tools.IR.DeclarationRecords', 'import Lean\n')
        self.source('Zkc.Verification.Claims.Registry', 'module\nnamespace ZkcSecurity.Registry\nend ZkcSecurity.Registry\n')
        self.source('Zkc.Applications.ArkLib.Registry', 'module\nnamespace ZkcArkLib.Registry\nend ZkcArkLib.Registry\n')
        for name, (directory, roots) in p.PACKAGES.items():
            # Explicit executable roots, including one outside a Commands directory.
            # Each defines its own global main and needs an isolated environment.
            entries = [roots[1] + '.Commands.First', roots[1] + '.Standalone']
            with (directory / 'lakefile.toml').open('a') as config:
                for index, entry in enumerate(entries):
                    self.source(entry, 'import Std\ndef main : IO Unit := pure ()\n')
                    config.write(f'\n[[lean_exe]]\nname = "command-{index}"\nroot = "{entry}"\n')
        self.source('Zkc.Tests.Clean.Control', 'import Std\n')
        fixture = self.root / '../common/tests/fixtures/clean/air-control.json'
        fixture.parent.mkdir(parents=True)
        fixture.write_text('{}\n')

    def restore_modules(self):
        for name in list(sys.modules):
            if name.split('.')[0] in ('support', 'checks', 'reproduce'):
                del sys.modules[name]
        sys.modules.update(self.saved)

    def source(self, module, text='module\n'):
        path = self.packages.module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_selection_and_dependency_order(self):
        p = self.packages
        self.assertEqual(p.selected(), list(p.PACKAGES))
        self.assertEqual(p.selected(['arklib']), ['program', 'protocol', 'arklib'])
        self.assertEqual(p.selected(['clean']), ['program', 'ir', 'clean'])
        self.assertEqual(p.selected(['verification']), ['program', 'ir', 'protocol', 'verification'])
        self.assertEqual(p.selected(['applications', 'clean', 'applications']), list(p.PACKAGES))
        self.assertEqual(p.selected([]), [])
        for name in ('main', 'proof', 'security', 'unknown'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'unknown Lean packages'):
                p.selected([name])
        with patch.dict(p.DEPENDENCIES, {'program': ('applications',)}):
            with self.assertRaisesRegex(ValueError, 'cyclic maintained'):
                p.selected()

    def test_canonical_cli_default_all_and_explicit_core(self):
        parser = argparse.ArgumentParser()
        self.packages.add_selection(parser)
        self.assertEqual(self.packages.selection(parser.parse_args([])), list(self.packages.PACKAGES))
        self.assertEqual(self.packages.selection(parser.parse_args(['--core-only'])), list(self.packages.CORE))
        self.assertEqual(self.packages.selection(parser.parse_args(['--package', 'clean'])), ['program', 'ir', 'clean'])
        for args in (['--main-only'], ['--integration', 'arklib'], ['--package', 'main'],
                     ['--core-only', '--package', 'clean']):
            with self.subTest(args=args), patch('sys.stderr'), self.assertRaises(SystemExit):
                parser.parse_args(args)

    def test_full_prefix_and_longest_prefix_ownership(self):
        p = self.packages
        for name, (directory, roots) in p.PACKAGES.items():
            for root in roots:
                with self.subTest(root=root):
                    self.assertEqual(p.module_owner(root + '.Private'), name)
                    self.assertEqual(p.module_package(root), directory)
                    self.assertFalse(p.is_owned_module(root + 'Extra'))
        for module in ('Zkc', 'Zkc.Tools', 'Zkc.Tests', 'Zkc.Adapters', 'ZkcProgram.Execution', 'ProtocolProof.Claims'):
            with self.subTest(module=module), self.assertRaises(ValueError):
                p.module_owner(module)
        with patch.dict(p.PACKAGES, {'nested': (self.root / 'nested', ('Zkc.Program.Nested',))}):
            self.assertEqual(p.module_owner('Zkc.Program.Nested.Child'), 'nested')

    def test_enumeration_covers_root_private_tools_tests_and_refuses_misplacement(self):
        p = self.packages
        private = self.source('Zkc.IR.Internal.Private')
        files = p.package_modules('ir')
        self.assertIn('Zkc.IR', files)
        self.assertEqual(files['Zkc.IR.Internal.Private'], private)
        self.assertIn('Zkc.Tools.IR.DeclarationRecords', files)
        cache = p.PACKAGES['ir'][0] / '.lake/build/Hidden.lean'
        cache.parent.mkdir(parents=True)
        cache.write_text('not a source')
        self.assertEqual(files, p.package_modules('ir'))
        wrong = p.PACKAGES['ir'][0] / 'Zkc/Protocol/Wrong.lean'
        wrong.parent.mkdir(parents=True)
        wrong.write_text('module\n')
        with self.assertRaisesRegex(ValueError, 'misplaced'):
            p.package_modules('ir')

    def test_missing_and_empty_migrated_packages_refuse(self):
        p = self.packages
        shutil.rmtree(p.PACKAGES['applications'][0])
        with self.assertRaisesRegex(ValueError, 'migrated package is missing'):
            p.package_modules('applications')
        p.PACKAGES['applications'][0].mkdir()
        with self.assertRaisesRegex(ValueError, 'has no sources'):
            p.package_modules('applications')

    def test_tool_discovery_tracks_layout_and_refuses_missing_or_ambiguous_tools(self):
        p = self.packages
        old = p.module_path('Zkc.Tools.Program.IR.ImportHeaders')
        self.assertEqual(p.tool_module('program', 'ImportHeaders'), 'Zkc.Tools.Program.IR.ImportHeaders')
        new = self.source('Zkc.Tools.Program.ImportHeaders', old.read_text())
        with self.assertRaisesRegex(ValueError, 'expected one'):
            p.tool_module('program', 'ImportHeaders')
        old.unlink()
        self.assertEqual(p.tool_module('program', 'ImportHeaders'), 'Zkc.Tools.Program.ImportHeaders')
        new.unlink()
        with self.assertRaisesRegex(ValueError, 'expected one'):
            p.tool_module('program', 'ImportHeaders')

    def test_explicit_library_roots_and_globs(self):
        import tomllib
        p = self.packages
        config = tomllib.loads((p.PACKAGES['program'][0] / 'lakefile.toml').read_text())
        self.assertEqual(len(p.library_globs('program', config)), 3)
        for key, value in (('roots', ['Zkc']), ('globs', ['Zkc.+']), ('globs', ['Zkc.ProgramExtra.+'])):
            changed = json.loads(json.dumps(config))
            changed['lean_lib'][0][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                p.library_globs('program', changed)
        del config['lean_lib'][0]['globs']
        with self.assertRaisesRegex(ValueError, 'must be explicit'):
            p.library_globs('program', config)

    def test_exact_manifest_closures(self):
        p = self.packages
        for name, (directory, _) in p.PACKAGES.items():
            with self.subTest(name=name):
                self.assertEqual(p.check_closure(name, directory), p.allowed_dependencies(name))
        self.assertIn('mathlib', p.check_closure('program', p.PACKAGES['program'][0]))
        self.assertNotIn('zkc_verification', p.check_closure('arklib', p.PACKAGES['arklib'][0]))

    def test_dependency_pins_provider_paths_and_missing_requirements_fail(self):
        p = self.packages
        directory = p.PACKAGES['program'][0]
        path = directory / 'lake-manifest.json'
        baseline = path.read_text()
        mutations = (
            lambda m: m.update(name='wrong'),
            lambda m: m['packages'].append(m['packages'][0]),
            lambda m: m['packages'][0].update(rev='main'),
            lambda m: m['packages'][0].update(url='https://example.invalid/imposter'),
            lambda m: m.update(packages=[]),
            lambda m: m['packages'].append({'name': 'Clean', 'type': 'git', 'url': 'x', 'rev': 'a' * 40}),
        )
        for index, mutate in enumerate(mutations):
            data = json.loads(baseline)
            mutate(data)
            path.write_text(json.dumps(data))
            with self.subTest(index=index), self.assertRaises(ValueError):
                p.check_closure('program', directory)
        path.write_text(baseline)
        consumer = p.PACKAGES['ir'][0] / 'lake-manifest.json'
        data = json.loads(consumer.read_text())
        next(dep for dep in data['packages'] if dep['type'] == 'path')['dir'] = '../protocol'
        consumer.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'path dependency mismatch'):
            p.check_closure('ir', p.PACKAGES['ir'][0])

    def test_generic_audits_private_coverage_registry_consumers_and_idempotence(self):
        audit = importlib.import_module('checks.audit_imports')
        p = self.packages
        self.source('Zkc.Applications.Security.Concrete')
        self.source('Zkc.Tests.Applications.Verification.LibraryImports', 'stale')
        self.source('Zkc.Tests.Applications.Verification.Audit', 'stale')
        self.source('Zkc.Tests.IR.IR.ProgramAudit', 'stale')
        self.source('Zkc.Tests.IR.CommandAudits.IR.Commands.First', 'stale')
        for name in p.PACKAGES:
            outputs = audit.expected(name)
            imports = next(text for path, text in outputs.items() if path.name == 'LibraryImports.lean')
            generated = next(text for path, text in outputs.items() if path.name == 'Audit.lean')
            config = tomllib.loads((p.PACKAGES[name][0] / 'lakefile.toml').read_text())
            commands = {entry['root'] for entry in config['lean_exe']}
            generated_modules = {module for module in p.package_modules(name)
                                 if module.startswith('Zkc.Tests.') and (
                                     module.rsplit('.', 1)[-1] in {'Audit', 'LibraryImports', 'ProgramAudit'} or
                                     '.CommandAudits.' in module)}
            for module in p.package_modules(name):
                with self.subTest(package=name, module=module):
                    self.assertEqual(f'import {module}\n' in imports,
                                     module not in generated_modules | commands)
            command_audits = {path: text for path, text in outputs.items() if 'CommandAudits' in path.parts}
            self.assertEqual(len(command_audits), len(commands))
            for command in commands:
                matches = [text for text in command_audits.values() if f'import {command}\n' in text]
                self.assertEqual(len(matches), 1)
                command_audit = matches[0]
                self.assertIn(f'let families : List Lean.Name := [`{command}]', command_audit)
                self.assertIn('!imported.importAll', command_audit)
                self.assertIn('ZkcTools.DeclarationAudit.check families "COMMAND-AUDIT-PASS"', command_audit)
                self.assertIn(f'import {audit.AUDITOR}\n', command_audit)
                self.assertNotIn('module\n', command_audit)
                for other in commands - {command}:
                    self.assertNotIn(f'import {other}\n', command_audit)
            self.assertIn(f'{name.upper()}-AUDIT-PASS', generated)
            self.assertIn('!imported.importAll', generated)
            self.assertIn('ZkcTools.DeclarationAudit.check families', generated)
            self.assertNotIn('module\n', generated)
            if name != 'applications':
                self.assertNotIn('checkRegistry', generated)
            for path, text in outputs.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            self.assertEqual(audit.expected(name), outputs)
        applications = next(v for k, v in audit.expected('applications').items() if k.name == 'Audit.lean')
        self.assertIn('ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited', applications)
        self.assertIn('`Zkc.Applications', applications)
        for name in p.PACKAGES:
            self.assertIn(f'import Zkc.Tests.{p.OWNERS[name]}.LibraryImports\n', applications)
        verification_imports = next(v for k, v in audit.expected('verification').items() if k.name == 'LibraryImports.lean')
        applications_imports = next(v for k, v in audit.expected('applications').items() if k.name == 'LibraryImports.lean')
        self.assertIn('import Zkc.Verification.Claims.Registry\n', verification_imports)
        self.assertIn('import Zkc.Applications.ArkLib.Registry\n', applications_imports)

    def test_registry_validation_preserves_exact_security_and_arklib_scope_families(self):
        audit = importlib.import_module('checks.audit_imports')
        # Migrated old scope families, not whole package roots: widening or
        # narrowing this list changes which theorem premises require registration.
        security_scopes = [
            'Zkc.Applications.Security', 'Zkc.Protocol.Bindings', 'Zkc.Protocol.Library.Families',
            'Zkc.Protocol.Library.Mathematics', 'Zkc.Protocol.Library.Security',
            'Zkc.Protocol.Library.Transformations', 'Zkc.Protocol.Logic',
            'Zkc.Tools.IR.SourceProperties', 'Zkc.Tools.IR.TableCapacity', 'Zkc.Tools.Protocol',
            'Zkc.Tools.Verification.Bindings', 'Zkc.Tools.Verification.ClaimConstruction',
            'Zkc.Tools.Verification.ComponentAuthoringReport', 'Zkc.Tools.Verification.ComponentBridge',
            'Zkc.Tools.Verification.ComponentDerivation', 'Zkc.Tools.Verification.ComponentReadback',
            'Zkc.Tools.Verification.ComponentView', 'Zkc.Tools.Verification.Components',
            'Zkc.Tools.Verification.Generation', 'Zkc.Tools.Verification.InputLaws',
            'Zkc.Tools.Verification.PairConstruction', 'Zkc.Tools.Verification.SigmaReadback',
            'Zkc.Tools.Verification.SourceInputClauses', 'Zkc.Tools.Verification.SourceInputReadback',
            'Zkc.Tools.Verification.SourceProperties', 'Zkc.Tools.Verification.SubjectABI',
            'Zkc.Tools.Verification.Sumcheck', 'Zkc.Tools.Verification.TargetEvaluation',
            'Zkc.Verification.Bindings', 'Zkc.Verification.Claims', 'Zkc.Verification.Families',
            'Zkc.Verification.Mathematics', 'Zkc.Verification.ProgramLogic',
            'Zkc.Verification.Transformations',
        ]
        ark_scopes = ['Zkc.Adapters.ArkLib', 'Zkc.Applications.ArkLib']
        generated = next(v for k, v in audit.expected('applications').items() if k.name == 'Audit.lean')
        for registry, scopes, marker in (
            ('ZkcSecurity.Registry.audited', security_scopes, 'REGISTRY-AUDIT-PASS'),
            ('(ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited)', ark_scopes,
             'ARKLIB-REGISTRY-AUDIT-PASS'),
        ):
            names = '[' + ', '.join('`' + prefix for prefix in scopes) + ']'
            self.assertIn(f'checkRegistry {registry} {names} "{marker}"', generated)
        self.assertEqual(generated.count('checkRegistry'), 2)

    def test_audit_freshness_refuses_missing_command_and_registry_coverage(self):
        audit = importlib.import_module('checks.audit_imports')
        outputs = {path: text for name in self.packages.PACKAGES for path, text in audit.expected(name).items()}
        for path, text in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        command = next(path for path in outputs if 'CommandAudits' in path.parts)
        registry = next(path for path in outputs if path.name == 'Audit.lean' and 'applications' in path.parts)
        for path, changed in ((command, None), (registry, outputs[registry].replace('checkRegistry', 'removedRegistry'))):
            with self.subTest(path=path):
                if changed is None:
                    path.unlink()
                else:
                    path.write_text(changed)
                with patch.object(sys, 'argv', ['audit_imports.py']), self.assertRaisesRegex(SystemExit, 'audit imports are stale'):
                    audit.main()
                path.write_text(outputs[path])

    def test_record_emitter_uses_shared_inventory_ir_executable_and_preserves_names(self):
        d = importlib.import_module('checks.records.declarations')
        self.assertIs(d.PACKAGES, self.packages.PACKAGES)
        def emit(command, **kwargs):
            if command[1] == 'env':
                index = next(i for i, arg in enumerate(command) if str(arg).endswith('.jsonl'))
                families = ['.'.join(Path(arg).with_suffix('').parts) for arg in command[index + 1:]]
                rows = [{'name': module + '.fixture', 'module': module} for module in families]
                header = dict(format=d.FORMAT, families=families, modules=len(families), declarations=len(rows),
                              axiom_provenance='resolved-constant-info/0', reference_provenance='checked-stored-module/0')
                Path(command[index]).write_text(''.join(json.dumps(row) + '\n' for row in [header, *rows]))
            return SimpleNamespace(returncode=0)
        headers = SimpleNamespace(imports=lambda source, path: [line.split()[-1] for line in source.splitlines()
                                                               if line.startswith('import ')])
        with patch.object(d, 'HeaderParser', side_effect=lambda **_: nullcontext(headers)), patch.object(d.subprocess, 'run', side_effect=emit) as run:
            d.emit('applications', self.root / 'records.jsonl')
        calls = run.call_args_list
        self.assertEqual(calls[0].kwargs['cwd'], self.packages.PACKAGES['ir'][0])
        commands = [call.args[0] for call in calls if call.args[0][1] == 'env']
        self.assertEqual(len(commands), 3)  # common sources and two independent mains
        for command in commands:
            self.assertIn(str(self.packages.PACKAGES['ir'][0] / '.lake/build/bin/declaration-records'), command)
            self.assertIn('Zkc/Applications.lean', command)
            self.assertIn('Zkc/Tools/Applications/Example.lean', command)
            self.assertIn('Zkc/Tests/Applications/Example.lean', command)
            self.assertIn('ZkcArkLib.Registry.reportTable', command)
            self.assertLessEqual(sum(source in command for source in (
                'Zkc/Tools/Applications/Commands/First.lean', 'Zkc/Tools/Applications/Standalone.lean')), 1)
        merged = d.Records.load({'applications': self.root / 'records.jsonl'})
        self.assertEqual({row['module'] for row in merged.declarations},
                         set(self.packages.package_modules('applications')))
        records = d.Records(declarations=[{'name': 'PIR.fixed', 'tags': []}])
        self.assertEqual(records.get('PIR.fixed')['name'], 'PIR.fixed')
        with patch.object(d.subprocess, 'run', return_value=SimpleNamespace(returncode=1)) as run:
            self.assertEqual(d.emit('ir', self.root / 'records.jsonl').returncode, 1)
            self.assertEqual(run.call_count, 1)

    def test_record_selection_refuses_multiple_mains_cycles_and_missing_command_sources(self):
        d = importlib.import_module('checks.records.declarations')
        headers = SimpleNamespace(imports=lambda source, path: [line.split()[-1] for line in source.splitlines()
                                                               if line.startswith('import ')])
        config = self.packages.PACKAGES['applications'][0] / 'lakefile.toml'
        baseline = config.read_text()
        for defect, message in (('multiple', 'multiple executable roots'), ('cycle', 'cyclic maintained imports'),
                                ('missing', 'executable root has no owned source')):
            paths = []
            with self.subTest(defect=defect):
                if defect == 'multiple':
                    paths.append(self.source('Zkc.Tests.Applications.Conflicting',
                        'import Zkc.Tools.Applications.Commands.First\nimport Zkc.Tools.Applications.Standalone\n'))
                elif defect == 'cycle':
                    paths.append(self.source('Zkc.Tests.Applications.FirstCycle', 'import Zkc.Tests.Applications.SecondCycle\n'))
                    paths.append(self.source('Zkc.Tests.Applications.SecondCycle', 'import Zkc.Tests.Applications.FirstCycle\n'))
                else:
                    config.write_text(baseline + '\n[[lean_exe]]\nname = "missing"\nroot = "Zkc.Tools.Applications.Missing"\n')
                try:
                    with self.assertRaisesRegex(ValueError, message):
                        d.emission_groups('applications', headers)
                finally:
                    for path in paths:
                        path.unlink()
                    config.write_text(baseline)

    def test_header_parser_pins_program_toolchain_and_fails_closed(self):
        h = importlib.import_module('support.lean_headers')
        writes = []
        details = [{'module': 'Std', 'public': True, 'meta': False, 'all': False}]
        process = SimpleNamespace(stdin=SimpleNamespace(write=lambda _: None, flush=lambda: None),
                                  stdout=SimpleNamespace(readline=lambda: json.dumps({'import_details': details, 'is_module': True}) + '\n'))
        process.stdin.write = writes.append
        with patch.object(h.subprocess, 'check_output', return_value='Lean (version 4.35.0)') as version, patch.object(h.subprocess, 'Popen', return_value=process) as popen:
            parser = h.HeaderParser(lake='/tools/lake', root=self.root / 'applications')
        self.assertEqual(popen.call_args.args[0][:3], ['/tools/lake', 'env', 'lean'])
        self.assertEqual(version.call_args.args[0], ['/tools/lake', 'env', 'lean', '--version'])
        self.assertEqual(popen.call_args.kwargs['env']['ELAN_TOOLCHAIN'], 'leanprover/lean4:v4.35.0')
        with patch.object(h.subprocess, 'check_output', return_value='Lean (version 4.34.1)'), patch.object(h.subprocess, 'Popen') as wrong:
            with self.assertRaisesRegex(ValueError, 'wrong Lean toolchain'):
                h.HeaderParser(lake='/tools/native-lake')
            wrong.assert_not_called()
        self.assertEqual(popen.call_args.kwargs['cwd'], self.packages.PACKAGES['program'][0])
        self.assertTrue(str(popen.call_args.args[0][-1]).endswith('Zkc/Tools/Program/IR/ImportHeaders.lean'))
        self.assertEqual(parser.imports('import Std'), ['Std'])
        self.assertEqual(parser.details('import Std'), details)
        self.assertTrue(parser.is_module('import Std'))
        self.assertEqual(len(writes), 1)
        # The parser's flag is authoritative; Python must not infer this from
        # the first bytes (copyright comments may precede a module header).
        source = '/- Copyright Example -/\nmodule\nimport Std\n'
        self.assertTrue(parser.is_module(source))
        process.stdout.readline = lambda: json.dumps({'import_details': details, 'is_module': False}) + '\n'
        self.assertFalse(parser.is_module('module\n-- rejected by parser'))
        process.stdout.readline = lambda: ''
        with self.assertRaisesRegex(ValueError, 'terminated'):
            parser.details('import Broken')
        process.stdout.readline = lambda: '{"error": "bad modifier"}'
        with self.assertRaisesRegex(ValueError, 'invalid Lean header'):
            parser.details('bad header')

    def test_responsibility_uses_only_migrated_module_paths(self):
        r = importlib.import_module('support.responsibility')
        for name, (directory, roots) in self.packages.PACKAGES.items():
            for prefix in roots:
                relative = 'lean/' + str(self.packages.module_path(prefix + '.Example').relative_to(self.root))
                self.assertEqual(r.module_name(Path(relative)), prefix + '.Example')
        for path in ('lean/Zkc/Source.lean', 'lean/proof/ProtocolProof.lean',
                     'lean/integrations/arklib/ZkcArkLib/Fri.lean', 'lean/README.lean'):
            with self.subTest(path=path):
                self.assertIsNone(r.module_name(Path(path)))
        self.assertEqual(r.classify('lean/ir/Zkc/Tools/IR/Example.lean').responsibility, 'support-infrastructure')

    def test_reproduction_inputs_use_complete_selected_inventory_and_patch_digests(self):
        reproduce = importlib.import_module('reproduce')
        p = self.packages
        declaration = p.PACKAGES['arklib'][0] / 'compatibility.json'
        declaration.write_text('{"patch": "exact.patch"}')
        declaration.with_name('exact.patch').write_text('declared patch')
        inputs = reproduce.build_inputs(self.root, ['arklib'])
        for name in p.selected(['arklib']):
            for path in p.package_modules(name).values():
                self.assertIn(str(path.relative_to(self.root)), inputs)
        self.assertIn('adapters/arklib/exact.patch', inputs)
        self.assertNotIn('ir/lakefile.toml', inputs)
        self.assertNotIn('lakefile.toml', inputs)
        self.assertIn('checks/records/declarations.py', inputs)
        previous = inputs['adapters/arklib/exact.patch']
        declaration.with_name('exact.patch').write_text('changed patch')
        self.assertNotEqual(reproduce.build_inputs(self.root, ['arklib'])['adapters/arklib/exact.patch'], previous)
        self.assertIn('../common/tests/fixtures/clean/air-control.json', reproduce.build_inputs(self.root, ['clean']))

    def test_reproduction_materializes_sources_once_and_keeps_compatibility_validation(self):
        reproduce = importlib.import_module('reproduce')
        materialized, prepared = [], []

        def materialize(package, targets, caches):
            materialized.append(package['name'])
            (targets / package['name']).mkdir()

        with patch.object(reproduce, 'materialize', side_effect=materialize), patch.object(reproduce, 'prepare', side_effect=prepared.append):
            pins = reproduce.prepare_dependencies(self.root, [], ['applications'])
        self.assertEqual(len(materialized), len(set(materialized)))
        self.assertEqual(set(pins), set().union(*self.packages.UPSTREAM.values()))
        self.assertEqual(prepared, [directory for directory, _ in self.packages.PACKAGES.values()])
        self.assertTrue((self.packages.PACKAGES['protocol'][0] / '.lake/packages/mathlib').is_symlink())

    def test_reproduction_rejects_shared_pin_disagreement(self):
        reproduce = importlib.import_module('reproduce')
        p = self.packages
        manifest = p.PACKAGES['ir'][0] / 'lake-manifest.json'
        data = json.loads(manifest.read_text())
        next(dep for dep in data['packages'] if dep['name'] == 'mathlib')['url'] += '-imposter'
        manifest.write_text(json.dumps(data))
        with patch.object(reproduce, 'materialize', side_effect=lambda dep, targets, _: (targets / dep['name']).mkdir()), patch.object(reproduce, 'prepare'):
            with self.assertRaisesRegex(ValueError, 'incompatible shared dependency'):
                reproduce.prepare_dependencies(self.root, [], ['ir'])

    def test_reproduction_build_markers_are_mandatory(self):
        reproduce = importlib.import_module('reproduce')
        directory = self.packages.PACKAGES['program'][0]
        log = self.root / 'build.log'

        def run(command, **kwargs):
            kwargs['stdout'].write('Build completed successfully (4 jobs)\nPROGRAM-AUDIT-PASS declarations=3 theorems=1\n')
            return SimpleNamespace(returncode=0)

        with patch.object(reproduce.subprocess, 'run', side_effect=run):
            result = reproduce.checked_build('lake', directory, log, {}, reproduce.required_markers('program'))
            self.assertEqual(result['status'], 'fail')
            self.assertFalse(result['required_markers']['DEPENDENCY-AUDIT-PASS'])
            # Successful logs alone do not establish that executable targets linked.
            self.assertEqual(reproduce.checked_build('lake', directory, log, {}, ['PROGRAM-AUDIT-PASS'])['status'], 'fail')
            config = tomllib.loads((directory / 'lakefile.toml').read_text())
            for entry in config['lean_exe']:
                path = directory / '.lake/build/bin' / entry['name']
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('#!/bin/sh\nexit 0\n')
                path.chmod(0o755)
            self.assertEqual(reproduce.checked_build('lake', directory, log, {}, ['PROGRAM-AUDIT-PASS'])['status'], 'pass')
            path.chmod(0o644)
            self.assertEqual(reproduce.checked_build('lake', directory, log, {}, ['PROGRAM-AUDIT-PASS'])['status'], 'fail')
        self.assertIn('CLEAN-UPSTREAM-BOUNDARY-PASS', reproduce.required_markers('clean'))
        self.assertIn('STARK-ARKLIB-BOUNDARY-PASS', reproduce.required_markers('arklib'))
        self.assertEqual(reproduce.control_source(self.packages.PACKAGES['clean'][0]), self.packages.module_path('Zkc.Tests.Clean.Control'))

    def test_reproduction_requires_registry_markers_at_applications_owner(self):
        reproduce = importlib.import_module('reproduce')
        markers = {'REGISTRY-AUDIT-PASS', 'ARKLIB-REGISTRY-AUDIT-PASS'}
        self.assertTrue(markers <= set(reproduce.required_markers('applications')))
        for name in self.packages.PACKAGES:
            if name != 'applications':
                with self.subTest(package=name):
                    self.assertFalse(markers & set(reproduce.required_markers(name)))

    def test_source_checker_rejects_missing_imports_and_unknown_targets(self):
        checker = importlib.import_module('checks.check_library')
        with self.assertRaisesRegex(ValueError, 'missing owned import'):
            checker.check_owned_imports({'Zkc.IR.Example': ['Zkc.Program.Missing']})
        config = self.packages.PACKAGES['program'][0] / 'lakefile.toml'
        config.write_text(config.read_text().replace('defaultTargets = [', 'defaultTargets = ["Unmaintained", '))
        with self.assertRaisesRegex(ValueError, 'default targets omit maintained'):
            checker.check(['program'], 'lake')

    def test_source_checker_accepts_complete_migrated_inventory_and_refuses_pin_conflicts(self):
        checker = importlib.import_module('checks.check_library')
        module_sources = {path.read_text() for name in self.packages.PACKAGES
                          for path in self.packages.package_modules(name).values()
                          if path.read_text().startswith('module\n')}

        class Headers:
            def __enter__(self):
                return self

            def __exit__(self, *_):
                pass

            def details(self, source, path):
                return [{'module': line.split()[-1]} for line in source.splitlines()
                        if line.startswith('import ')]

            def is_module(self, source, path):
                return source in module_sources

        # Accept keyword arguments without invoking Lean.
        with patch.object(checker, 'HeaderParser', side_effect=lambda **_: Headers()):
            result = checker.check(['applications'], 'unused-lake')
            self.assertEqual(result['packages'], list(self.packages.PACKAGES))
            self.assertEqual(result['modules'], sum(len(self.packages.package_modules(name)) for name in self.packages.PACKAGES))
            source_path = self.packages.module_path('Zkc.Program.Example')
            original = source_path.read_text()
            copyright_source = '/- Copyright Example -/\n' + original
            module_sources.add(copyright_source)
            source_path.write_text(copyright_source)
            self.assertEqual(checker.check(['program'], 'unused-lake')['status'], 'pass')
            source_path.write_text('module\n-- parser refused the header')
            with self.assertRaisesRegex(ValueError, 'expected module-system source'):
                checker.check(['program'], 'unused-lake')
            source_path.write_text(original)
            path = self.packages.PACKAGES['ir'][0] / 'lake-manifest.json'
            manifest = json.loads(path.read_text())
            next(dep for dep in manifest['packages'] if dep['name'] == 'mathlib')['url'] += '-conflict'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'conflicting pin'):
                checker.check(['ir'], 'unused-lake')
    def test_reproduction_runs_every_selected_build_in_order_and_records_scopes(self):
        reproduce = importlib.import_module('reproduce')
        args = SimpleNamespace(package=['applications'], core_only=False,
                               output=Path(self.temporary.name) / 'reproduction',
                               dependency_cache=None, integration_dependency_cache=[], lake='lake')
        built = []

        def build(lake, directory, log, env, markers):
            built.append(directory)
            self.assertIn('DEPENDENCY-AUDIT-PASS', markers)
            self.assertNotIn('LEAN_PATH', env)
            self.assertEqual(env['ELAN_TOOLCHAIN'], 'leanprover/lean4:v4.35.0')
            return {'status': 'pass'}

        with patch.object(reproduce, 'prepare_dependencies', return_value={}), patch.object(reproduce.support.lake, 'resolve', return_value='/tools/lake'), patch.object(reproduce.subprocess, 'check_output', return_value='Lean (version 4.35.0)'), patch.object(reproduce.subprocess, 'run', return_value=SimpleNamespace(returncode=0)), patch.object(reproduce, 'checked_build', side_effect=build), patch.object(reproduce, 'clean_control', return_value={'status': 'pass'}) as control, patch.object(reproduce, 'run_clients', return_value={'status': 'pass'}) as clients, patch('builtins.print'):
            reproduce.run(args)
        self.assertEqual(built, [self.packages.package_directory(name, args.output / 'lean') for name in self.packages.PACKAGES])
        self.assertEqual(control.call_count, 1)
        self.assertEqual(clients.call_count, 1)
        record = json.loads((args.output / 'result.json').read_text())
        self.assertEqual(record['status'], 'pass')
        self.assertEqual(record['audit_scope'], {name: list(roots) for name, (_, roots) in self.packages.PACKAGES.items()})
        self.assertFalse(record['source_drift'])

    def test_reproduction_build_failure_cannot_turn_partial_selection_into_pass(self):
        reproduce = importlib.import_module('reproduce')
        args = SimpleNamespace(package=['applications'], core_only=False,
                               output=Path(self.temporary.name) / 'failed-reproduction',
                               dependency_cache=None, integration_dependency_cache=[], lake='lake')
        with patch.object(reproduce, 'prepare_dependencies', return_value={}), patch.object(reproduce.support.lake, 'resolve', return_value='/tools/lake'), patch.object(reproduce.subprocess, 'check_output', return_value='Lean (version 4.35.0)'), patch.object(reproduce.subprocess, 'run', return_value=SimpleNamespace(returncode=0)), patch.object(reproduce, 'checked_build', side_effect=[{'status': 'pass'}, {'status': 'fail'}]) as builds, patch.object(reproduce, 'run_clients') as clients, patch('builtins.print'), self.assertRaises(SystemExit):
            reproduce.run(args)
        self.assertEqual(builds.call_count, 2)
        clients.assert_not_called()
        record = json.loads((args.output / 'result.json').read_text())
        self.assertEqual(record['status'], 'fail')
        self.assertEqual(list(record['builds']), ['program', 'ir'])

    def test_package_resolver_never_accepts_signal_as_absence(self):
        checker = importlib.import_module('checks.check_package_ownership')
        for code in (-9, -11, 0):
            with self.subTest(code=code), patch.object(checker.subprocess, 'run', return_value=SimpleNamespace(returncode=code, stdout='', stderr='unknown package `Clean`')):
                with self.assertRaisesRegex(ValueError, 'prohibited package available'):
                    checker.check(['program'], 'lake')


if __name__ == '__main__':
    unittest.main()
