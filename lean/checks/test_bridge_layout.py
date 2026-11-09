"""Render-only controls for module ownership and preserved declaration identity."""

import json
from pathlib import Path
import sys
import tempfile
import tomllib
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

LEAN = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(LEAN))
from bridges.common.lean_render import Refused, source_package
from bridges import subject as subject_driver
from bridges.pipeline import evidence, glue, manifest
from bridges.structured import bodies, snapshot
from support.packages import module_owner, module_path, package_directory


class BridgeLayout(unittest.TestCase):
    def test_subject_outputs_separate_modules_and_namespaces(self):
        for subject in manifest.load_all():
            for key, value in subject.table('generated').items():
                if Path(value).suffix != '.lean':
                    continue
                with self.subTest(subject=subject.name, output=key):
                    module = subject.module_name(key)
                    namespace = subject.namespace(key)
                    self.assertEqual(module_path(module), subject.generated(key))
                    self.assertEqual(module_owner(module), 'applications')
                    self.assertIn('namespace ' + namespace,
                                  subject.generated(key).read_text().splitlines())
                    self.assertNotEqual(module, namespace)

    def test_manifest_refuses_missing_conflicting_and_legacy_selections(self):
        source = (LEAN / 'subjects/schnorr.toml').read_text()
        cases = [
            (source.replace('data = "ZkcExamples.Construction.SchnorrProofData"\n', ''),
             'namespaces must name exactly'),
            (source.replace('facts = "ZkcExamples.Executable.SchnorrProof"',
                            'facts = "Wrong.Namespace"'), 'must agree with executable.namespace'),
            (source.replace('connection = "Zkc.Applications.IR.Construction.SchnorrProof"',
                            'connection = "ZkcExamples.Construction.SchnorrProof"'),
             'module has no maintained package'),
            (source.replace('module = "Zkc.Applications.IR.Executable.SchnorrProof"\n', ''),
             'generated.lowering requires executable.module'),
            (source.replace('[scalar.properties.perfect-completeness]',
                            '[scalar.properties]\nbad = "x"\n[scalar.properties.perfect-completeness]'),
             'scalar.properties.bad must be a table'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'schnorr.toml'
            for text, diagnostic in cases:
                path.write_text(text)
                if diagnostic:
                    with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(Refused, diagnostic):
                        manifest.load(path)
                else:
                    manifest.load(path)

    def test_external_views_require_namespace_metadata(self):
        source = (LEAN / 'subjects/sumcheck.toml').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'sumcheck.toml'
            path.write_text(source.replace('views_namespace = "ZkcExamples.Structured.SumcheckSourceViews"\n', ''))
            with self.assertRaisesRegex(Refused, 'external admission requires'):
                manifest.load(path)

    def test_external_views_import_modules_and_reference_declaration_namespaces(self):
        entry = SimpleNamespace(names=[], types=[], slots=lambda: [], acceptance_output=0,
                                validator=1, roles=['P', 'V'], draws=[], producer=0, service=0,
                                contract='sample/0', request='[]', position=0)
        for name in ('sumcheck', 'gkr'):
            subject = manifest.load(LEAN / 'subjects' / (name + '.toml'))
            names = {key: subject.namespace(key) for key in ('glue', 'data', 'participant')}
            source = glue.construction_glue(subject, entry, names)
            module = subject.get('construction', 'views')
            namespace = subject.get('construction', 'views_namespace')
            with self.subTest(subject=name):
                self.assertIn('public import ' + module, source)
                self.assertIn('abbrev program := ' + namespace + '.program', source)
                self.assertIn(namespace + '.imported', source)
                self.assertNotIn(module + '.program', source)

    def test_retained_snapshots_render_exact_migrated_files(self):
        fixture_root = LEAN / 'bridges/structured'
        fixtures = tomllib.loads((fixture_root / 'fixtures.toml').read_text())
        checked = 0
        for stem, spec in fixtures.items():
            stages = ('Original', 'Candidate', 'Mutated') if spec['data'] == 'SchnorrResponse' else ('Original', 'Candidate')
            selections = [(stem + '-' + stage.lower(), spec['data'] + stage)
                          for stage in stages] if spec['suite'] == 'inlining' else [(stem, spec['data'])]
            for fixture, leaf in selections:
                path = fixture_root / 'fixtures' / (fixture + '.json')
                namespace = 'ZkcExamples.Structured.' + leaf + 'Data'
                module = 'Zkc.Applications.IR.Structured.' + leaf + 'Data'
                with self.subTest(fixture=fixture):
                    rendered = snapshot.render(json.loads(path.read_text()), namespace)
                    self.assertEqual(rendered.encode(), module_path(module).read_bytes())
                    self.assertIn('namespace ' + namespace, rendered)
                    checked += 1
        self.assertGreater(checked, 20)

    def test_subject_builds_each_module_in_its_owning_package(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = subject_driver.Driver(SimpleNamespace(output=Path(directory), lake='lake'))
            driver.lake = Mock()
            modules = ('Zkc.Applications.IR.Structured.SchnorrInteractiveData', 'Zkc.Program.Execution')
            driver.build(*modules)
            driver.build(*modules)
            self.assertEqual(driver.lake.call_count, len(modules))
            for call, module in zip(driver.lake.call_args_list, modules):
                self.assertEqual(call.args, ('build', '+' + module))
                self.assertEqual(call.kwargs['cwd'], package_directory(module_owner(module)))

    def test_lowering_imports_owning_module_and_preserves_theorem_namespace(self):
        subject = manifest.load(LEAN / 'subjects/schnorr.toml')
        source = evidence.lowering_module(subject, SimpleNamespace(types=[], names=[]),
                                          subject.get('executable', 'namespace'))
        self.assertIn('public import Zkc.Applications.IR.Executable.SchnorrProof', source)
        self.assertIn('validator := ZkcExamples.Executable.SchnorrProof.validator', source)
        self.assertNotIn('Zkc.Applications.IR.Executable.SchnorrProof.validator', source)

    def test_reporting_controls_preserve_claim_rejections(self):
        from checks.records import controls
        self.assertGreaterEqual(len(controls.run()), 31)

    def test_body_printer_imports_module_and_selects_namespace(self):
        source = bodies.PRINTER.format(
            data='Zkc.Applications.IR.Structured.SchnorrInteractiveData',
            data_namespace='ZkcExamples.Structured.SchnorrInteractiveData',
            views='true', closed='false')
        self.assertIn('import Zkc.Applications.IR.Structured.SchnorrInteractiveData', source)
        self.assertIn('check ZkcExamples.Structured.SchnorrInteractiveData.snapshot', source)
        self.assertNotIn('Zkc.Applications.IR.Structured.SchnorrInteractiveData.snapshot', source)

    def test_scalar_printer_receives_explicit_module_and_namespace_selections(self):
        sys.path.insert(0, str(LEAN / 'bridges/common'))
        from bridges.common import structured
        data = json.loads((LEAN / 'applications/Zkc/Applications/IR/NativePrograms/fixtures/schnorr.json').read_text())
        module = 'Zkc.Applications.IR.NativePrograms.Schnorr'
        namespace = 'ZkcExamples.NativePrograms.Schnorr'
        printed = {'inputs': 'inputs-source', 'view': 'view-source'}
        result = SimpleNamespace(returncode=0, stdout=json.dumps(printed), stderr='')
        with tempfile.TemporaryDirectory() as temporary, patch.object(
                structured.subprocess, 'run', return_value=result) as execute:
            directory = Path(temporary)
            modules = structured.views(data, directory, module, 1, namespace_prefix=namespace)
            self.assertEqual(modules, [module + suffix for suffix in ('Data', 'Inputs', 'View')])
            config = json.loads(Path(execute.call_args.args[0][-1]).read_text())
            self.assertEqual(config, [module + 'Inputs', namespace + 'Inputs', module + 'Data',
                                      namespace + 'Data.snapshot', module + 'View', namespace + 'View', 1])
            path = directory / ((module + 'Data').replace('.', '/') + '.lean')
            self.assertEqual(path.read_text(), snapshot.render(data, namespace + 'Data'))

    def test_retained_native_clients_render_without_native_reexecution(self):
        sys.path.insert(0, str(LEAN / 'bridges/common'))
        from bridges.common.verify import read_json, render_client
        fixtures = LEAN / 'applications/Zkc/Applications/IR/NativePrograms/fixtures'
        for family, forms in [('Schnorr', ('Helpers', 'Reordered', 'EarlyChallenge')),
                              ('Sumcheck', ('Helpers', 'Horner', 'WrongResidual')),
                              ('Factor', ('Expanded', 'Horner', 'WrongPoint', 'WrongResidual'))]:
            request_family = 'factor-openings' if family == 'Factor' else family.lower()
            request = read_json(LEAN / 'bridges/common/requests' / (request_family + '.json'))
            for form in forms:
                name = family + form
                data = read_json(fixtures / (family.lower() + '-' + form.lower() + '.json'))
                positive = form not in ('EarlyChallenge', 'WrongPoint', 'WrongResidual')
                source = render_client(data, request, name, positive=positive)
                role = 'Security' if family == 'Factor' else 'IR'
                module = 'Zkc.Applications.' + role + '.NativePrograms.' + name
                with self.subTest(module=module):
                    # Mechanical migration preserves the previous import order.
                    # Regeneration sorts the canonical imports and preserves every declaration byte.
                    retained = module_path(module).read_text()
                    old_imports = [line for line in retained.splitlines(keepends=True)
                                   if line.startswith('public import ')]
                    retained = retained.replace(''.join(old_imports), ''.join(sorted(old_imports)), 1)
                    self.assertEqual(source, retained)
                    self.assertIn('public import Zkc.Applications.IR.NativePrograms.Variants.' + name + 'View', source)
                    self.assertIn('ZkcExamples.NativePrograms.Variants.' + name + 'Inputs.program', source)

    def test_scratch_environment_uses_package_dependency_closure(self):
        self.assertEqual(source_package('import Zkc.IR.Source.Structured.Import'),
                         package_directory('ir'))
        self.assertEqual(source_package('import Zkc.Protocol.Claims.Receipt\n'
                                        'import Zkc.IR.Source.Structured.Import'),
                         package_directory('verification'))
        self.assertEqual(source_package('import Zkc.Applications.ArkLib.Registry\n'
                                        'import Zkc.Applications.Security.ExecutableSchnorrFiatShamir'),
                         package_directory('applications'))
        with self.assertRaises(Refused):
            source_package('import Zkc.Source.Structured.Import')


if __name__ == '__main__':
    unittest.main()
