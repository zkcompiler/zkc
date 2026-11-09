"""Controls for package extraction and source-only reproduction; no downloads."""

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
from support.packages import LEAN, NAMES, PACKAGES, check_closure, module_package, selected
from support.responsibility import classify


class ProgramPackages(unittest.TestCase):
    def test_independent_diamond(self):
        self.assertEqual(selected([]), ['program', 'main'])
        self.assertEqual(selected(['proof']), ['program', 'main', 'proof'])
        self.assertEqual(selected(['arklib']), ['program', 'main', 'proof', 'security', 'arklib'])
        self.assertEqual(selected(['clean']), ['program', 'main', 'clean'])
        self.assertEqual(check_closure('program', LEAN / 'program'), set())
        self.assertNotIn('protocol_proof', check_closure('main', LEAN))

    def test_module_ownership_ignores_declaration_namespaces(self):
        self.assertEqual(module_package('ZkcProgram.Region.Basic'), LEAN / 'program')
        self.assertEqual(module_package('Zkc.Source.RegionLaws'), LEAN)
        self.assertEqual(classify('lean/program/ZkcProgram/Execution.lean').dependency_layer,
                         'program')
        self.assertEqual(classify('lean/proof/ProtocolProof/Claims/Receipt.lean').dependency_layer,
                         'protocol-core')

    def test_program_refuses_even_unused_package_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / 'lakefile.toml').write_text('name = "zkc_program"\n')
            (directory / 'lake-manifest.json').write_text(json.dumps({
                'name': 'zkc_program', 'packages': [
                    {'name': 'unused_provider', 'type': 'git', 'rev': 'a' * 40}]}))
            with self.assertRaisesRegex(ValueError, 'must have no package dependencies'):
                check_closure('program', directory)

    def test_closure_checks_manifest_and_inherited_provider_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / 'lakefile.toml').write_text('name = "consumer"\n')
            manifest = {'name': 'wrong', 'packages': []}
            path = directory / 'lake-manifest.json'
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'manifest package mismatch'):
                check_closure('main', directory)
            provider = directory / 'provider'
            provider.mkdir()
            (provider / 'lakefile.toml').write_text('name = "imposter"\n')
            manifest = {'name': 'consumer', 'packages': [
                {'name': 'zkc_program', 'type': 'path', 'dir': 'provider'}]}
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'locked path provider mismatch'):
                check_closure('main', directory)

    def test_forbidden_edges_and_transitive_imports(self):
        for owner, dependency in [
                ('ZkcProgram.Execution', 'Mathlib.Data.Nat.Basic'),
                ('ZkcProgram.Execution', 'Zkc.Source.Structured'),
                ('ZkcProgram.Execution', 'ProtocolProof.Claims'),
                ('Zkc.Source.Structured', 'ProtocolProof.Claims'),
                ('ProtocolProof.Claims', 'Zkc.Source.Structured'),
                ('ProtocolProof.Claims', 'ZkcSecurityExamples.Client'),
                ('ProtocolProof.Claims', 'ZkcTools.Generation.Commands')]:
            with self.subTest(owner=owner, dependency=dependency):
                self.assertFalse(permitted(owner, dependency))
                with self.assertRaisesRegex(ValueError, 'forbidden dependency'):
                    audit_graph({owner: [dependency]}, [owner])
        self.assertTrue(permitted('ProtocolProof.Claims', 'ZkcProgram.Execution'))
        self.assertTrue(permitted('Zkc.Source.RegionLaws', 'ZkcProgram.Region.Basic'))
        with self.assertRaisesRegex(ValueError, 'forbidden dependency'):
            audit_graph({'ZkcProgram.Execution': ['Lean.Hidden'],
                         'Lean.Hidden': ['Zkc.Source.Structured']}, ['ZkcProgram'])

    def test_source_inventory_covers_shared_and_optional_proof(self):
        core = reproduce.build_inputs(LEAN)
        proof = reproduce.build_inputs(LEAN, with_proof=True)
        security = reproduce.build_inputs(LEAN, with_security=True)
        for path in (LEAN / 'program').rglob('*.lean'):
            if '.lake' not in path.parts:
                self.assertIn(str(path.relative_to(LEAN)), core)
        self.assertIn('program/lake-manifest.json', core)
        self.assertNotIn('proof/ProtocolProof.lean', core)
        self.assertIn('proof/ProtocolProof.lean', proof)
        self.assertIn('proof/ProtocolProof.lean', security)
        self.assertIn('checks/records/declarations.py', core)
        self.assertIn('checks/StructuredSource.lean', core)
        self.assertFalse(any('.lake' in Path(name).parts for name in security))

    def test_reproduction_materializes_each_git_source_once(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            for name in ('program', 'main', 'proof', 'security'):
                directory = PACKAGES[name][0]
                destination = work / directory.relative_to(LEAN)
                destination.mkdir(parents=True, exist_ok=True)
                for filename in ('lakefile.toml', 'lake-manifest.json'):
                    shutil.copy2(directory / filename, destination / filename)
            materialized = []

            def materialize(package, packages, caches):
                materialized.append(package['name'])
                (packages / package['name']).mkdir()

            with patch.object(reproduce, 'materialize', side_effect=materialize):
                pins = reproduce.prepare_dependencies(work, [], [Path('proof'), Path('security')])
            self.assertEqual(len(materialized), len(set(materialized)))
            self.assertEqual(set(materialized), set(pins))
            self.assertFalse(set(NAMES.values()) & set(materialized))
            self.assertTrue((work / 'proof/.lake/packages/mathlib').is_symlink())
            self.assertEqual(list((work / 'program/.lake/packages').iterdir()), [])
            self.assertFalse(list(work.rglob('*.olean')))

    def test_reproduction_rejects_redirected_local_provider(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            (work / 'program').mkdir()
            shutil.copy2(LEAN / 'program/lake-manifest.json', work / 'program/lake-manifest.json')
            manifest = json.loads((LEAN / 'lake-manifest.json').read_text())
            program = next(dep for dep in manifest['packages'] if dep['name'] == 'zkc_program')
            program['dir'] = '../outside'
            # Check the local boundary before exercising any Git source.
            manifest['packages'] = [program]
            (work / 'lake-manifest.json').write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'unexpected maintained path dependency'):
                reproduce.prepare_dependencies(work, [])


if __name__ == '__main__':
    unittest.main()
