#!/usr/bin/env python3
"""Descriptor refusal checks through the production component-root entry point."""
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import generate_component_roots as driver


DESCRIPTOR = '''schema = "zkc.component-roots/0"
model_module = "Example.Model"
model = "Example.model"
sampling = "Example.sampling"
field_type = "Example.Field"
group_type = "Example.Group"
capabilities = "Example.capabilities"

[[root]]
name = "Example"
source = "example.zkc"
entry = "example::Proof"
modules = { library = "library.zkc" }
target = "knowledge"
method = "sigma"
'''


class ComponentRootDescriptors(unittest.TestCase):
    def assert_refused(self, descriptor, diagnostic, arguments=()):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            config = directory / "roots.toml"
            output = directory / "must-not-exist"
            config.write_text(descriptor)
            with patch.object(driver, "Generation", side_effect=AssertionError(
                    "generation started before descriptor refusal")) as generation:
                with self.assertRaisesRegex(ValueError, diagnostic):
                    driver.main(["--config", str(config), "--output", str(output), *arguments])
                generation.assert_not_called()
            self.assertFalse(output.exists())

    def test_unknown_and_missing_keys(self):
        cases = [
            (DESCRIPTOR.replace("[[root]]", 'unexpected = "x"\n[[root]]'), "unknown keys: unexpected"),
            (DESCRIPTOR + 'unexpected = "x"\n', "unknown keys: unexpected"),
            (DESCRIPTOR + 'error_expresion = ".natural 1"\n', "unknown keys: error_expresion"),
            (DESCRIPTOR.replace('group_type = "Example.Group"\n', ""), "missing keys: group_type"),
            (DESCRIPTOR.replace('target = "knowledge"\n', ""), "missing keys: target"),
        ]
        for descriptor, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic, descriptor=descriptor):
                self.assert_refused(descriptor, diagnostic)

    def test_value_shapes(self):
        cases = [
            (DESCRIPTOR.replace('model = "Example.model"', "model = 1"), "model: expected"),
            (DESCRIPTOR.replace('source = "example.zkc"', "source = false"), "source: expected"),
            (DESCRIPTOR.replace('modules = { library = "library.zkc" }', "modules = []"), "modules: expected"),
            (DESCRIPTOR.replace('library = "library.zkc"', "library = 1"), "modules.library: expected"),
            (DESCRIPTOR.replace('[[root]]', 'receipt_normalization = true\n[[root]]'), "receipt_normalization: expected"),
            (DESCRIPTOR.replace('[[root]]', 'theorem_normalization = ["law", 1]\n[[root]]'), "theorem_normalization: expected"),
            (DESCRIPTOR.split("[[root]]")[0] + "root = []\n", "root: expected"),
            (DESCRIPTOR.split("[[root]]")[0] + "root = {}\n", "root: expected"),
            (DESCRIPTOR + "error_expression = 1\n", "error_expression: expected"),
        ]
        for descriptor, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic, descriptor=descriptor):
                self.assert_refused(descriptor, diagnostic)

    def test_names_and_installed_methods(self):
        cases = [
            (DESCRIPTOR + "[[root]]" + DESCRIPTOR.split("[[root]]")[1], "duplicate root name"),
            (DESCRIPTOR.replace('name = "Example"', 'name = "bad-name"'), "invalid root name"),
            (DESCRIPTOR.replace('method = "sigma"', 'method = "unknown"'), "uninstalled proof method"),
            (DESCRIPTOR.replace('method = "sigma"', 'method = "direct"'), "missing keys: proof_module"),
            (DESCRIPTOR + 'proof_module = "Example.Proof"\n', "unknown keys: proof_module"),
            (DESCRIPTOR + 'proof_name = "Example.proof"\n', "unknown keys: proof_name"),
        ]
        for descriptor, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic, descriptor=descriptor):
                self.assert_refused(descriptor, diagnostic)

    def test_method_inputs_are_typed_and_method_specific(self):
        for suffix, diagnostic in [
            ('method_imports = "Example.Laws"\n', "method_imports: expected a list"),
            ('method_imports = ["Example.Laws", 1]\n', "method_imports: expected a nonempty string"),
            ('nonvacuity_law = false\n', "nonvacuity_law: expected"),
        ]:
            with self.subTest(suffix=suffix):
                self.assert_refused(DESCRIPTOR + suffix, diagnostic)
        direct = DESCRIPTOR.replace('method = "sigma"',
                                    'method = "direct"\nproof_module = "Example.Proof"')
        self.assert_refused(direct + 'nonvacuity_law = "Example.nonvacuous"\n',
                            "unknown keys: nonvacuity_law")
        valid = tomllib.loads(DESCRIPTOR + 'method_imports = ["Example.Laws"]\n'
                             'nonvacuity_law = "Example.Laws.nonvacuous"\n')
        driver.validate_config(valid)

    def test_selection_cannot_hide_malformed_roots(self):
        invalid_root = DESCRIPTOR.split("[[root]]")[1].replace('"Example"', '"Other"')
        self.assert_refused(DESCRIPTOR + "[[root]]" + invalid_root + 'error_expresion = "x"\n',
                            "unknown keys: error_expresion", ["--only", "Example"])
        self.assert_refused(DESCRIPTOR, "unknown or empty root selection", ["--only", "Other"])

    def test_valid_installed_configuration_and_optional_defaults(self):
        driver.validate_config(tomllib.loads(DESCRIPTOR))
        direct = tomllib.loads(DESCRIPTOR.replace('method = "sigma"',
                                                'method = "direct"\nproof_module = "Example.Proof"'))
        driver.validate_config(direct)
        self.assertNotIn("proof_name", direct["root"][0])
        self.assertNotIn("error_expression", direct["root"][0])
        self.assertNotIn("receipt_normalization", direct)
        self.assertNotIn("theorem_normalization", direct)
        persisted = (Path(driver.__file__).parent / "roots/sampled.toml").read_text()
        installed = tomllib.loads(persisted)
        driver.validate_config(installed)
        self.assertEqual(installed, tomllib.loads(persisted))


if __name__ == "__main__":
    unittest.main()
