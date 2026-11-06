"""Exact producer grammar and preprojection graph refusals."""

import copy
import json
from pathlib import Path
import unittest

import descriptor_schemes as schemes
from generate import load, validate

ROOT = Path(__file__).parent


class DescriptorSchemes(unittest.TestCase):
    def test_exact_complete_installation(self):
        value = load(ROOT / "declarations.json")
        validate(value)
        self.assertEqual(len(value["frontendSchemes"]), 6)

    def test_every_nested_record_rejects_extra_fields(self):
        source = load(ROOT / "declarations.json")
        for path in (("frontendSchemes", 0),
                     ("frontendSchemes", 0, "inputs", 0),
                     ("frontendSchemes", 0, "inputs", 0, "contract"),
                     ("frontendSchemes", 0, "inputs", 0, "contract", "extent")):
            with self.subTest(path=path):
                value = copy.deepcopy(source)
                at = value
                for key in path:
                    at = at[key]
                at["extra"] = False
                with self.assertRaisesRegex(ValueError, "scheme fields"):
                    validate(value)

    def test_shell_declarations_have_exact_fields(self):
        source = load(ROOT / "declarations.json")
        for tag in ("ContractConstructor", "View"):
            row = next(r for r in source["frontendDeclarations"] if r["kind"] == tag)
            for key in row:
                with self.subTest(tag=tag, missing=key):
                    value = copy.deepcopy(source)
                    target = next(r for r in value["frontendDeclarations"] if r["identity"] == row["identity"])
                    del target[key]
                    with self.assertRaises((ValueError, KeyError)):
                        validate(value)
            value = copy.deepcopy(source)
            next(r for r in value["frontendDeclarations"] if r["identity"] == row["identity"])["extra"] = True
            with self.assertRaisesRegex(ValueError, "unknown fields"):
                validate(value)

    def test_graph_cycles_depth_width_and_invalid_indices(self):
        cycle = {"kind": "product", "elements": []}
        cycle["elements"].append(cycle)
        deep = {"kind": "contract", "variable": 0}
        for _ in range(34):
            deep = {"kind": "sequence", "element": deep, "extent": {"kind": "unsized"}}
        wide = {"kind": "product", "elements": [{"kind": "contract", "variable": 0}] * 1025}
        for value, diagnostic in ((cycle, "cyclic"), (deep, "limit"), (wide, "limit"),
                                  ({"kind": "contract", "variable": True}, "index"),
                                  ({"kind": "contract", "variable": -1}, "index")):
            with self.subTest(diagnostic=diagnostic):
                with self.assertRaisesRegex(ValueError, diagnostic):
                    schemes.pattern(value)

    def test_json_duplicate_keys_are_never_overwritten(self):
        # Exercise the production decoder's object hook without changing inputs.
        from generate import unique
        for value in ('{"kind":"contract","variable":0,"variable":1}',
                      '{"kind":"unsized","kind":"extent"}'):
            with self.assertRaisesRegex(ValueError, "duplicate key"):
                json.loads(value, object_pairs_hook=unique)


if __name__ == "__main__":
    unittest.main()
