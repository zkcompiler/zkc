"""Source-only controls for canonical package ownership and reproduction."""

import argparse
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import reproduce
from support.dependencies import audit_graph, permitted
from support.packages import (
    CORE,
    LEAN,
    NAMES,
    PACKAGES,
    add_selection,
    check_closure,
    module_owner,
    module_package,
    module_path,
    package_directory,
    package_modules,
    selected,
    selection,
)  # noqa: E402
from support.responsibility import classify


class ProgramPackages(unittest.TestCase):
    def test_independent_diamond(self):
        self.assertEqual(selected([]), [])
        self.assertEqual(selected(['ir']), ['program', 'ir'])
        self.assertEqual(selected(['arklib']), ['program', 'protocol', 'arklib'])
        self.assertEqual(selected(['clean']), ['program', 'ir', 'clean'])
        self.assertEqual(selected(), list(PACKAGES))
        self.assertNotIn('zkc_ir', check_closure('protocol', package_directory('protocol')))
        for name in PACKAGES:
            check_closure(name, package_directory(name))

    def test_cli_selection(self):
        parser = argparse.ArgumentParser()
        add_selection(parser)
        self.assertEqual(selection(parser.parse_args([])), selected())
        self.assertEqual(selection(parser.parse_args(['--core-only'])), list(CORE))
        self.assertEqual(selection(parser.parse_args(['--package', 'ir', '--package', 'arklib'])),
                         ['program', 'ir', 'protocol', 'arklib'])

    def test_module_ownership_ignores_declaration_namespaces(self):
        for name, (directory, roots) in PACKAGES.items():
            for root in roots:
                with self.subTest(package=name, module=root):
                    module = root + '.Fixture'
                    self.assertEqual(module_owner(module), name)
                    self.assertEqual(module_package(module), directory)
                    self.assertEqual(module_path(module),
                                     directory.joinpath(*module.split('.')).with_suffix('.lean'))
        for declaration_namespace in ('Zkc.Source', 'PIR', 'ZkcSecurity', 'ZkcExamples'):
            with self.assertRaises(ValueError):
                module_owner(declaration_namespace)
        self.assertEqual(classify('lean/program/Zkc/Program/Execution.lean').dependency_layer,
                         'program')
        self.assertEqual(classify('lean/protocol/Zkc/Protocol/Claims/Receipt.lean').dependency_layer,
                         'protocol')

    def test_manifest_identity_is_checked(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / 'lakefile.toml').write_text('name = "zkc_ir"\n')
            (directory / 'lake-manifest.json').write_text(json.dumps({
                'name': 'wrong', 'packages': []}))
            with self.assertRaisesRegex(ValueError, 'manifest package mismatch'):
                check_closure('ir', directory)

    def test_forbidden_edges_and_transitive_imports(self):
        for owner, dependency in [
                ('Zkc.Program.Execution', 'Mathlib.Data.Nat.Basic'),
                ('Zkc.Program.Execution', 'Zkc.IR.Source.Structured'),
                ('Zkc.Program.Execution', 'Zkc.Protocol.Claims'),
                ('Zkc.IR.Source.Structured', 'Zkc.Protocol.Claims'),
                ('Zkc.Program.Semantics.Meaning', 'Mathlib.Probability.Kernel.Basic'),
                ('Zkc.Program.Semantics.Meaning', 'Mathlib.MeasureTheory.Measure.Basic'),
                ('Zkc.Program.Execution', 'VCVio.EvalDist.PFunctorKernel'),
                ('Zkc.Protocol.Claims', 'Zkc.IR.Source.Structured'),
                ('Zkc.Protocol.Claims', 'Zkc.Applications.Security.Client'),
                ('Zkc.Protocol.Claims', 'Zkc.Tools.IR.Generation.Commands')]:
            with self.subTest(owner=owner, dependency=dependency):
                self.assertFalse(permitted(owner, dependency))
                with self.assertRaisesRegex(ValueError, 'forbidden dependency'):
                    audit_graph({owner: [dependency]}, [owner])
        self.assertTrue(permitted('Zkc.Protocol.Claims', 'Zkc.Program.Execution'))
        self.assertTrue(permitted('Zkc.IR.Source.RegionLaws', 'Zkc.Program.Region.Basic'))
        with self.assertRaisesRegex(ValueError, 'forbidden dependency'):
            audit_graph({'Zkc.Program.Execution': ['Lean.Hidden'],
                         'Lean.Hidden': ['Zkc.IR.Source.Structured']}, ['Zkc.Program'])

    def test_source_inventory_covers_every_selected_package(self):
        program = reproduce.build_inputs(LEAN, ['program'])
        all_packages = reproduce.build_inputs(LEAN)
        self.assertNotIn('lakefile.toml', all_packages)
        self.assertNotIn('lake-manifest.json', all_packages)
        for name in PACKAGES:
            for path in package_modules(name).values():
                relative = str(path.relative_to(LEAN))
                self.assertIn(relative, all_packages)
                self.assertEqual(relative in program, name == 'program')
        self.assertIn('checks/records/declarations.py', program)
        self.assertIn('ir/Zkc/Tools/IR/Commands/StructuredSource.lean', all_packages)
        self.assertFalse(any('.lake' in Path(name).parts for name in all_packages))

    def test_reproduction_materializes_each_git_source_once(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            for name in PACKAGES:
                source = package_directory(name)
                destination = package_directory(name, work)
                destination.mkdir(parents=True)
                for filename in ('lakefile.toml', 'lake-manifest.json'):
                    shutil.copy2(source / filename, destination / filename)
            materialized = []

            def materialize(package, packages, caches):
                materialized.append(package['name'])
                (packages / package['name']).mkdir()

            with patch.object(reproduce, 'materialize', side_effect=materialize), \
                    patch.object(reproduce, 'prepare'):
                pins = reproduce.prepare_dependencies(work, [], ['verification', 'arklib'])
            self.assertEqual(len(materialized), len(set(materialized)))
            self.assertEqual(set(materialized), set(pins))
            self.assertFalse(set(NAMES.values()) & set(materialized))
            self.assertTrue((work / 'protocol/.lake/packages/mathlib').is_symlink())
            self.assertFalse(list(work.rglob('*.olean')))

    def test_reproduction_rejects_redirected_local_provider(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            for name in selected(['ir']):
                destination = package_directory(name, work)
                destination.mkdir(parents=True)
                for filename in ('lakefile.toml', 'lake-manifest.json'):
                    shutil.copy2(package_directory(name) / filename, destination / filename)
            provider = work / 'outside'
            provider.mkdir()
            for filename in ('lakefile.toml', 'lake-manifest.json'):
                shutil.copy2(package_directory('program') / filename, provider / filename)
            manifest_path = package_directory('ir', work) / 'lake-manifest.json'
            manifest = json.loads(manifest_path.read_text())
            next(dep for dep in manifest['packages'] if dep['name'] == 'zkc_program')['dir'] = '../outside'
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'path dependency mismatch|unexpected maintained path dependency'), \
                    patch.object(reproduce, 'materialize'), \
                    patch.object(reproduce, 'prepare'):
                reproduce.prepare_dependencies(work, [], ['ir'])
            self.assertFalse((package_directory('ir', work) / '.lake/packages').exists())


if __name__ == '__main__':
    unittest.main()
