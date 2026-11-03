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

sys.path.insert(0, str(LEAN.parent / "common/catalog"))
import validation_cases  # noqa: E402

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
        self.assertEqual(installed_catalogue.MODULE.read_bytes(),
                         installed_catalogue.render(self.declarations).encode("utf-8"))

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
        output = self.directory / "rendered-catalogue.txt"
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

    def test_shared_service_cases(self):
        cases = validation_cases.load()
        for outcome in ("accepted", "refused"):
            for case in cases[outcome]:
                if not any(edit["table"] == "serviceMethods" for edit in case["edits"]):
                    continue
                changed, _ = validation_cases.apply(case["edits"], self.declarations, {})
                with self.subTest(outcome=outcome, case=case["name"]):
                    if outcome == "accepted":
                        installed_catalogue.render(changed)
                    else:
                        with self.assertRaises(Refused):
                            installed_catalogue.render(changed)

    def test_exact_source_row_fields(self):
        for table in ("frontendDeclarations", "serviceSignatures", "serviceMethods"):
            for field in self.declarations[table][0]:
                with self.subTest(table=table, missing=field):
                    changed = copy.deepcopy(self.declarations)
                    del changed[table][0][field]
                    with self.assertRaisesRegex(Refused, "missing catalog fields"):
                        installed_catalogue.render(changed)
            with self.subTest(table=table, unknown="extra"):
                changed = copy.deepcopy(self.declarations)
                changed[table][0]["extra"] = True
                with self.assertRaisesRegex(Refused, "unknown catalog fields"):
                    installed_catalogue.render(changed)
        for retain_prelude in (False, True):
            with self.subTest(retain_prelude=retain_prelude):
                changed = copy.deepcopy(self.declarations)
                declaration = changed["frontendDeclarations"][0]
                declaration["implicit"] = declaration["prelude"]
                if not retain_prelude:
                    del declaration["prelude"]
                with self.assertRaisesRegex(Refused, "unknown catalog fields" if retain_prelude else "missing catalog fields"):
                    installed_catalogue.render(changed)

    def test_wrong_source_row_types_refuse(self):
        for table, field, value in [
            ("serviceMethods", "identity", 1),
            ("serviceMethods", "constructor", []),
            ("serviceMethods", "name", "wrong.name"),
            ("serviceMethods", "signature", {}),
            ("serviceMethods", "capability", False),
            ("frontendDeclarations", "prelude", 1),
            ("frontendDeclarations", "association", {"kind": "rule", "target": "RandomConstructor", "extra": 1}),
            ("frontendDeclarations", "statics", None),
        ]:
            with self.subTest(table=table, field=field):
                changed = copy.deepcopy(self.declarations)
                changed[table][0][field] = value
                with self.assertRaises(Refused):
                    installed_catalogue.render(changed)

    def test_duplicate_source_names_and_identities_refuse(self):
        for table, expected in [
            ("frontendDeclarations", "duplicate frontend identity"),
            ("serviceSignatures", "duplicate service signature"),
            ("serviceMethods", "duplicate service method identity"),
        ]:
            changed = copy.deepcopy(self.declarations)
            changed[table].append(copy.deepcopy(changed[table][0]))
            with self.subTest(table=table), self.assertRaisesRegex(Refused, expected):
                installed_catalogue.render(changed)
        changed = copy.deepcopy(self.declarations)
        duplicate = copy.deepcopy(changed["frontendDeclarations"][0])
        duplicate["identity"] = "another.constructor"
        changed["frontendDeclarations"].append(duplicate)
        with self.assertRaisesRegex(Refused, "duplicate frontend ownership"):
            installed_catalogue.render(changed)
        duplicate["owner"] = "zkc::other"
        with self.assertRaisesRegex(Refused, "duplicate prelude frontend name"):
            installed_catalogue.render(changed)

    def test_random_methods_use_nominal_constructor_ownership(self):
        original = installed_catalogue.render(self.declarations)
        changed = copy.deepcopy(self.declarations)
        changed["frontendDeclarations"][0]["name"] = "OpenService"
        changed["frontendDeclarations"][0]["owner"] = "zkc::services"
        self.assertEqual(installed_catalogue.render(changed), original)
        constructor = copy.deepcopy(changed["frontendDeclarations"][0])
        constructor.update(identity="service.other", name="OtherService", prelude=False)
        changed["frontendDeclarations"].append(constructor)
        other = copy.deepcopy(changed["serviceMethods"][0])
        other.update(identity="other.sample", constructor="service.other", name="foreign")
        changed["serviceMethods"].insert(0, other)
        # A distinct method and a homonym from another constructor both stay out.
        self.assertEqual(installed_catalogue.render(changed), original)
        other["name"] = "draw"
        other["capability"] = "IndexRandomness"
        other["signature"] = "RandomIndex"
        self.assertEqual(installed_catalogue.render(changed), original)
        changed["frontendDeclarations"][0]["identity"] = "service.replacement"
        for method in changed["serviceMethods"][1:]:
            method["constructor"] = "service.replacement"
        self.assertEqual(installed_catalogue.service_methods(changed), [])

    def test_duplicate_json_members_refuse_in_cli(self):
        source = self.directory / "duplicate.json"
        encoded = json.dumps(self.declarations)
        source.write_text(encoded.replace('"prelude": true', '"prelude": true, "prelude": false', 1))
        result = self.generator("--check", "--declarations", source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("duplicate JSON member", result.stderr)

    def test_freshness_requires_identical_bytes(self):
        output = self.directory / "rendered-catalogue.txt"
        rendered = installed_catalogue.render(self.declarations).encode("utf-8")
        output.write_bytes(rendered.replace(b"\n", b"\r\n"))
        result = self.generator("--check", "--output", output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("stale generated module", result.stderr)


if __name__ == "__main__":
    unittest.main()
