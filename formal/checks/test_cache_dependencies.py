#!/usr/bin/env python3
"""Controls for selective cache preparation; never modifies actual packages."""

import json
import sys
from pathlib import Path
import tempfile
import unittest

# The tool this checks stayed in the package directory: it is a fetch, not
# a check, so it is not discovered and run beside these.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import cache_dependencies as cache  # noqa: E402
from support.lean_headers import HeaderParser  # noqa: E402


class SharedDependencyControls(unittest.TestCase):
    def fixture(self, directory, other_revision="abc", resolved=True):
        root = Path(directory)
        main, optional = root / "main", root / "optional"
        main.mkdir()
        optional.mkdir()
        package = {"name": "mathlib", "type": "git", "rev": "abc"}
        manifest = {"packagesDir": ".lake/packages", "packages": [package]}
        (main / "lake-manifest.json").write_text(json.dumps(manifest))
        manifest["packages"] = [dict(package, rev=other_revision)]
        (optional / "lake-manifest.json").write_text(json.dumps(manifest))
        source = main / ".lake/packages/mathlib"
        if resolved:
            source.mkdir(parents=True)
        return main, optional, source, optional / ".lake/packages/mathlib"

    def test_equal_pin_shares_resolved_source(self):
        with tempfile.TemporaryDirectory() as directory:
            main, optional, source, target = self.fixture(directory)
            cache.share_dependencies(main, optional)
            self.assertTrue(target.is_symlink())
            self.assertEqual(source, target.resolve())

    def test_conflicting_pin_refuses_before_linking(self):
        with tempfile.TemporaryDirectory() as directory:
            main, optional, _, target = self.fixture(directory, other_revision="def")
            with self.assertRaisesRegex(ValueError, "incompatible shared dependency"):
                cache.share_dependencies(main, optional)
            self.assertFalse(target.exists())

    def test_unresolved_main_source_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            main, optional, _, target = self.fixture(directory, resolved=False)
            with self.assertRaisesRegex(ValueError, "was not resolved"):
                cache.share_dependencies(main, optional)
            self.assertFalse(target.exists())

    def test_existing_directory_is_not_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            main, optional, _, target = self.fixture(directory)
            target.mkdir(parents=True)
            marker = target / "keep"
            marker.write_text("existing data")
            cache.share_dependencies(main, optional)
            self.assertFalse(target.is_symlink())
            self.assertEqual("existing data", marker.read_text())


class CacheRootControls(unittest.TestCase):
    def test_transitive_header_and_comment_handling(self):
        with tempfile.TemporaryDirectory() as directory, HeaderParser() as headers:
            root = Path(directory)
            caller = root / "Caller.lean"
            caller.write_text("import Middle\n-- import Mathlib\n")
            (root / "Middle.lean").write_text("import Std\nimport Mathlib.Data.Nat.Basic\n")
            roots, seen = cache.collect(headers, [caller], [root])
            self.assertEqual(["Mathlib.Data.Nat.Basic"], roots)
            self.assertEqual(2, len(seen))

    def test_unresolved_import_refuses(self):
        with tempfile.TemporaryDirectory() as directory, HeaderParser() as headers:
            root = Path(directory)
            caller = root / "Caller.lean"
            caller.write_text("import Missing\n")
            with self.assertRaisesRegex(ValueError, "cannot resolve source import Missing"):
                cache.collect(headers, [caller], [root])

    def test_foundation_does_not_select_all_mathlib(self):
        with tempfile.TemporaryDirectory() as directory, HeaderParser() as headers:
            root = Path(directory)
            caller = root / "Caller.lean"
            caller.write_text("import Std\n")
            roots, _ = cache.collect(headers, [caller], [root])
            self.assertEqual([], roots)


if __name__ == "__main__":
    unittest.main()
