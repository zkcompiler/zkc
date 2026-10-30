#!/usr/bin/env python3
"""Descriptor refusal checks through the production component-root entry point."""
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import Mock, patch

import generate_component_roots as driver


DESCRIPTOR = '''schema = "zkc.component-roots/0"
model_module = "Example.Model"
model = "Example.model"
registry = "Example.registry"
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

DIRECT_DESCRIPTOR = DESCRIPTOR.replace('method = "sigma"', '''method = "direct"
proof_module = "Example.Proof"
error_bound = "1"
error_expression = ".natural 1"''')


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
            (DESCRIPTOR.replace('registry = "Example.registry"\n', ""), "missing keys: registry"),
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
            (DIRECT_DESCRIPTOR.replace('error_expression = ".natural 1"', "error_expression = 1"),
             "error_expression: expected"),
            (DIRECT_DESCRIPTOR.replace('error_bound = "1"', "error_bound = false"), "error_bound: expected"),
            (DIRECT_DESCRIPTOR.replace('error_bound = "1"', 'error_bound = " "'), "error_bound: expected"),
        ]
        for descriptor, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic, descriptor=descriptor):
                self.assert_refused(descriptor, diagnostic)

    def test_names_and_installed_methods(self):
        cases = [
            (DESCRIPTOR + "[[root]]" + DESCRIPTOR.split("[[root]]")[1], "duplicate root name"),
            (DESCRIPTOR.replace('name = "Example"', 'name = "bad-name"'), "invalid root name"),
            (DESCRIPTOR.replace('method = "sigma"', 'method = "unknown"'), "uninstalled proof method"),
            (DESCRIPTOR.replace('method = "sigma"', 'method = "direct"'), "missing keys: .*proof_module"),
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
        self.assert_refused(DIRECT_DESCRIPTOR + 'nonvacuity_law = "Example.nonvacuous"\n',
                            "unknown keys: nonvacuity_law")
        valid = tomllib.loads(DESCRIPTOR + 'method_imports = ["Example.Laws"]\n'
                             'nonvacuity_law = "Example.Laws.nonvacuous"\n')
        driver.validate_config(valid)

    def test_selection_cannot_hide_malformed_roots(self):
        invalid_root = DESCRIPTOR.split("[[root]]")[1].replace('"Example"', '"Other"')
        self.assert_refused(DESCRIPTOR + "[[root]]" + invalid_root + 'error_expresion = "x"\n',
                            "unknown keys: error_expresion", ["--only", "Example"])
        self.assert_refused(DESCRIPTOR, "unknown or empty root selection", ["--only", "Other"])

    def test_quantitative_selection_requires_both_bound_forms(self):
        for line, diagnostic in [
            ('error_bound = "1"\n', "missing keys: error_bound"),
            ('error_expression = ".natural 1"', "missing keys: error_expression"),
        ]:
            self.assert_refused(DIRECT_DESCRIPTOR.replace(line, ""), diagnostic)
        for key in ("error_bound", "error_expression"):
            self.assert_refused(DESCRIPTOR + f'{key} = "0"\n', "unknown keys: " + key)

    def test_valid_installed_configuration_and_optional_defaults(self):
        driver.validate_config(tomllib.loads(DESCRIPTOR))
        direct = tomllib.loads(DIRECT_DESCRIPTOR)
        driver.validate_config(direct)
        self.assertNotIn("proof_name", direct["root"][0])
        self.assertEqual(direct["root"][0]["error_expression"], ".natural 1")
        self.assertNotIn("receipt_normalization", direct)
        self.assertNotIn("theorem_normalization", direct)
        persisted = (Path(driver.__file__).parent / "roots/sampled.toml").read_text()
        installed = tomllib.loads(persisted)
        driver.validate_config(installed)
        self.assertEqual(installed, tomllib.loads(persisted))

    def test_direct_proof_is_assembled_before_receipt_selection(self):
        config = tomllib.loads(DIRECT_DESCRIPTOR)
        root = config["root"][0]
        with tempfile.TemporaryDirectory() as directory:
            generation = driver.Generation.__new__(driver.Generation)
            generation.directory = Path(directory)
            (generation.directory / root["name"]).mkdir()
            generation.prepare = Mock()
            generation.compile = Mock()
            generation.retain = Mock()
            printers = []

            def printer(name, source):
                printers.append(source)
                output = "CompletenessClaims.lean" if name.startswith("GenerateReceipt") else "Completeness.lean"
                (generation.directory / root["name"] / output).write_text("fresh checked printer output")

            generation.printer = printer
            generation.prove(root, config)
            endpoint = "ZkcSecurityExamples.Generated.Components.ExampleCompleteness"
            generation.retain.assert_called_once_with(endpoint, "fresh checked printer output")
            generation.compile.assert_called_once_with("Example.Proof")
            generation.receipt(root, config)
            self.assertIn("RootCompleteness.directSource", printers[0])
            self.assertIn("RootCompleteness.claimsSource", printers[1])
            # Both invocations send the exact same selection to Lean, including
            # the positive bound. The receipt cannot bypass the emitted endpoint.
            for source in printers:
                self.assertIn(driver.completeness_selection(root), source)


if __name__ == "__main__":
    unittest.main()
