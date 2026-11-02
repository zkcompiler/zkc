#!/usr/bin/env python3
"""The installed catalogue rows of the Lean readers are generated from the catalog.

`Zkc/Source/Structured/InstalledCatalogue.lean` must equal a fresh rendering of
`common/catalog/declarations.json` by `bridges/common/installed_catalogue.py`.
A changed catalog row changes the generated facts, service methods follow the
sampled field's capabilities, and the generator's check refuses a module it
did not render from the current declarations.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

LEAN = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(LEAN))
from bridges.common import installed_catalogue, schema  # noqa: E402
from bridges.common.lean_render import Refused  # noqa: E402

GENERATOR = LEAN / "bridges/common/installed_catalogue.py"


def row(declarations, identity):
    (found,) = [value for value in declarations["domains"] if value["identity"] == identity]
    return found


class Generated(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="zkc-installed-catalogue-")
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.declarations = schema.declarations()

    def generator(self, *arguments):
        return subprocess.run([sys.executable, GENERATOR, *map(str, arguments)],
                              capture_output=True, text=True, timeout=60)

    def test_module_is_current(self):
        result = self.generator("--check")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(installed_catalogue.MODULE.read_text(encoding="utf-8"),
                         installed_catalogue.render(self.declarations))

    def test_every_row_and_service_is_generated(self):
        module = installed_catalogue.render(self.declarations)
        for value in self.declarations["domains"]:
            self.assertEqual(module.count(f"def Domains.«{value['identity']}» : Nominal where"), 1)
        for value in self.declarations["randomServices"]:
            self.assertEqual(module.count(f"def Services.«{value['contract']}» : Service where"), 1)

    def test_changed_row_changes_the_facts_and_the_check_refuses(self):
        changed = copy.deepcopy(self.declarations)
        octic = row(changed, "koala-bear.ext8-binomial3")
        octic["capabilities"].remove("IndexBlockRandomness")
        module = installed_catalogue.render(changed)
        self.assertNotEqual(module, installed_catalogue.render(self.declarations))
        self.assertIn('"ExtensionField", "IndexRandomness"]\n', module)
        # The service methods follow the sampled field's capabilities.
        service = module.split("def Services.«random.koala-bear.ext8-binomial3/0» : Service where\n")[1]
        self.assertTrue(service.split("\n\n")[0].endswith('methods := ["draw", "index"]'))
        source = self.directory / "declarations.json"
        source.write_text(json.dumps(changed), encoding="utf-8")
        result = self.generator("--check", "--declarations", source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("stale generated module", result.stderr)
        output = self.directory / "InstalledCatalogue.lean"
        self.assertEqual(self.generator("--write", "--declarations", source, "--output", output).returncode, 0)
        self.assertEqual(output.read_text(encoding="utf-8"), module)
        self.assertEqual(self.generator("--check", "--declarations", source, "--output", output).returncode, 0)

    def test_characteristic_is_the_modulus(self):
        changed = copy.deepcopy(self.declarations)
        row(changed, "koala-bear")["field"]["characteristic"] = "2013265921"
        self.assertIn('def Characteristics.«koala-bear» : Nat := 2013265921\n',
                      installed_catalogue.render(changed))

    def test_unrepresentable_rows_refuse(self):
        for edit, message in [
                (lambda value: row(value, "koala-bear").__setitem__("sort", "Codec"), "has no sort"),
                (lambda value: row(value, "koala-bear").__setitem__("identity", "koala»bear"), "invalid catalog identity"),
                (lambda value: row(value, "koala-bear")["field"].__setitem__("characteristic", "02"),
                 "invalid field characteristic"),
                (lambda value: value["randomServices"][0].__setitem__("field", "bls12-381.g1"),
                 "unknown sampled field")]:
            changed = copy.deepcopy(self.declarations)
            edit(changed)
            with self.subTest(message=message), self.assertRaisesRegex(Refused, message):
                installed_catalogue.render(changed)


if __name__ == "__main__":
    unittest.main()
