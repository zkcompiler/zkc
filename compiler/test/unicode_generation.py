"""Determinism, data integrity, and malformed-range controls for Names tables."""

import copy
import importlib.util
import json
from pathlib import Path
import unittest

from tools import records


ROOT = Path(__file__).resolve().parents[2] / "common/unicode"
SPEC = importlib.util.spec_from_file_location("unicode_generator", ROOT / "generate.py")
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class UnicodeGenerationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.profile = GENERATOR.load_profile(ROOT)

    def test_determinism_and_ranges(self):
        self.assertEqual(self.profile, GENERATOR.load_profile(ROOT))
        self.assertEqual(GENERATOR.cpp(self.profile), GENERATOR.cpp(copy.deepcopy(self.profile)))
        for key in ("identifier_start", "identifier_continue", "mathematical_symbols"):
            previous = -2
            for first, last in self.profile[key]:
                self.assertGreater(first, previous + 1)
                self.assertLessEqual(first, last)
                previous = last
        self.assertEqual(len({p[0] for p in self.profile["delimiter_pairs"]}),
                         len(self.profile["delimiter_pairs"]))

    def test_input_and_manifest_drift(self):
        root = Path(records())
        (root / "17.0.0").mkdir()
        for source in (ROOT / "17.0.0").iterdir():
            (root / "17.0.0" / source.name).symlink_to(source)
        (root / "LICENSE.txt").symlink_to(ROOT / "LICENSE.txt")
        original = json.loads((ROOT / "manifest.json").read_text())
        for name in [entry["file"] for entry in original["files"]]:
            with self.subTest(file=name):
                manifest = copy.deepcopy(original)
                next(e for e in manifest["files"] if e["file"] == name)["sha256"] = "0" * 64
                (root / "manifest.json").write_text(json.dumps(manifest))
                with self.assertRaisesRegex(ValueError, "input hash mismatch"):
                    GENERATOR.load_profile(root)
        manifest = copy.deepcopy(original)
        manifest["unicode_version"] = "18.0.0"
        (root / "manifest.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "unsupported profile field"):
            GENERATOR.load_profile(root)
        manifest = copy.deepcopy(original)
        manifest["normalizers"]["cpp"]["version"] = "2.13.0"
        (root / "manifest.json").write_text(json.dumps(manifest))
        self.assertNotEqual(GENERATOR.load_profile(root)["identity"], self.profile["identity"])
        manifest = copy.deepcopy(original)
        manifest["identifier_continue_additions"] = ["2080..208A"]
        (root / "manifest.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "unsupported profile field"):
            GENERATOR.load_profile(root)

    def test_malformed_properties(self):
        for text in ("0042..0041; XID_Start", "110000; XID_Start", "xyz; XID_Start",
                     "0041; XID_Start\n0041..0042; XID_Start", "0041 XID_Start",
                     "0041; Bad Property", "0041; XID_Start; Bad; Extra"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                GENERATOR.properties(text)
        # Different properties may overlap, and UCD17's InCB has a value column.
        result = GENERATOR.properties("0041; XID_Start\n0041; XID_Continue\n094D; InCB; Linker")
        self.assertEqual(result["XID_Start"], {0x41})
        self.assertEqual(result["InCB;Linker"], {0x94D})

    def test_malformed_categories(self):
        row = "0041;LATIN CAPITAL LETTER A;Lu;0;L;;;;;N;;;;0061;"
        for text in (row + "\n" + row, "0041;A;Lu", row.replace("0041", "110000"),
                     row.replace("LATIN CAPITAL LETTER A", "<Range, First>"),
                     row.replace("LATIN CAPITAL LETTER A", "<Range, Last>")):
            with self.subTest(text=text), self.assertRaises(ValueError):
                GENERATOR.categories(text)

    def test_malformed_brackets(self):
        for text in ("0028; 0029; o", "0028; 0028; o", "0028; 0029; bad",
                     "0028; 0029; o\n0029; 0028; c\n0028; 0029; o",
                     "0028; 0029; o\n0029; 0028; o"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                GENERATOR.brackets(text)


if __name__ == "__main__":
    unittest.main()
