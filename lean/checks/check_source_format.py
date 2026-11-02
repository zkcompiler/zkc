#!/usr/bin/env python3
"""Every compiler invocation of the Lean bridges selects a declared source format.

The selection comes from the package manifests that list the module sources,
from the fixture declarations, or from an explicit caller selection, always
through `bridges/common/source_format.py`; no bridge or check spells the
compiler option itself. A missing or unknown selection, an undeclared source
and a mixed closure refuse before the compiler runs.
"""
from pathlib import Path
import sys
import tempfile
import unittest

LEAN = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(LEAN))
sys.path.insert(0, str(LEAN / "bridges/structured"))
from bridges.common import native_entry, source_format  # noqa: E402
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.pipeline import compile as pipeline_compile, manifest  # noqa: E402
import check as structured  # noqa: E402


class Spelling(unittest.TestCase):
    def test_no_bridge_or_check_spells_the_option(self):
        helper = Path(source_format.__file__).resolve()
        offenders = [str(path.relative_to(LEAN)) for directory in ("bridges", "checks")
                     for path in sorted((LEAN / directory).rglob("*.py"))
                     if path.resolve() != helper and source_format.OPTION in path.read_text(encoding="utf-8")]
        self.assertEqual(offenders, [])


class DeclaredSelections(unittest.TestCase):
    def test_every_subject_resolves_a_declared_format(self):
        for subject in manifest.load_all():
            with self.subTest(subject=subject.name):
                self.assertIn(source_format.of_sources(subject.modules.values()), source_format.FORMATS)
                selected = pipeline_compile.options(subject, "entry")[0]
                self.assertEqual(source_format.require_option([selected]),
                                 source_format.of_sources(subject.modules.values()))

    def test_every_structured_fixture_resolves_a_declared_format(self):
        for stem, spec in structured.fixture_table().items():
            with self.subTest(fixture=stem):
                # The inlining suite compiles its one fixture source named after the table entry.
                sources = ([LEAN / "bridges/structured/fixtures" / f"{stem}.zkc"] if "module" in spec
                           else structured.fixture(stem)[1].values())
                self.assertIn(source_format.of_sources(sources), source_format.FORMATS)

    def test_package_and_fixture_sources_resolve(self):
        root = source_format.ROOT
        for path in ["examples/projects/schnorr/main.zkc", "libraries/protocols/sigma/schnorr/lib.zkc",
                     "lean/bridges/common/fixtures/factor-openings.zkc",
                     "compiler/test/fixtures/structured-source/scoped-control.zkc"]:
            with self.subTest(source=path):
                self.assertIn(source_format.of_source(root / path), source_format.FORMATS)


class Refusals(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="zkc-source-format-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name).resolve()

    def package(self, name, value=None, modules=("main.zkc",)):
        directory = self.root / name
        directory.mkdir(parents=True)
        lines = ['format = "zkc.project/0"']
        if value is not None:
            lines.append(f'source-format = "{value}"')
        lines.append("[modules]")
        for index, module in enumerate(modules):
            (directory / module).write_text("module m;\n")
            lines.append(f'm{index} = "{module}"')
        (directory / "zkc.toml").write_text("\n".join(lines) + "\n")
        return [directory / module for module in modules]

    def refuses(self, pattern, paths, declarations=None):
        with self.assertRaisesRegex(Refused, pattern):
            source_format.of_sources(paths, root=self.root, declarations=declarations or {})

    def test_missing_and_unknown_manifest_selections_refuse(self):
        self.refuses("missing source-format", self.package("missing"))
        self.refuses("unknown source-format 'zkc2'", self.package("unknown", "zkc2"))

    def test_undeclared_source_refuses(self):
        loose = self.root / "loose.zkc"
        loose.write_text("module m;\n")
        self.refuses("no package manifest lists it", [loose])
        listed = self.package("other", "zkc")
        unlisted = listed[0].with_name("unlisted.zkc")
        unlisted.write_text("module m;\n")
        self.refuses("no package manifest lists it", [unlisted])

    def test_mixed_closure_refuses(self):
        self.refuses("mixed source formats", self.package("first", "zkc") + self.package("second", "zkc-layout"))

    def test_declared_selection_is_forwarded_exactly(self):
        (layout,) = self.package("layout", "zkc-layout")
        self.assertEqual(source_format.option([layout], root=self.root, declarations={}),
                         source_format.OPTION + "zkc-layout")
        fixtures = self.root / "fixtures"
        fixtures.mkdir()
        (fixtures / "a.zkc").write_text("module a;\n")
        declared = {fixtures: "zkc-layout"}
        self.assertEqual(source_format.of_source(fixtures / "a.zkc", root=self.root, declarations=declared),
                         "zkc-layout")
        # A package manifest decides over the declaration of an enclosing fixture directory.
        (listed,) = self.package("fixtures/package", "zkc")
        self.assertEqual(source_format.of_source(listed, root=self.root, declarations=declared), "zkc")

    def test_explicit_selection_is_validated(self):
        arguments = ["--module=m=" + str(self.root / "derived.zkc"), "--subject=m::P"]
        self.assertEqual(source_format.with_option(arguments, "zkc-layout")[0], source_format.OPTION + "zkc-layout")
        with self.assertRaisesRegex(Refused, "unknown source-format"):
            source_format.with_option(arguments, "layout")

    def test_invocations_refuse_before_the_compiler_runs(self):
        calls = []
        subject = ["--module=m=main.zkc", "--subject=m::P"]
        for flags in [subject, [source_format.OPTION + "zkc2", *subject],
                      [source_format.OPTION + "zkc", source_format.OPTION + "zkc", *subject]]:
            with self.subTest(flags=flags), self.assertRaises(Refused):
                native_entry.native_subject(calls.append, "zkc-compile", flags)
        self.assertEqual(calls, [])
        loose = self.root / "loose.zkc"
        loose.write_text("module m;\n")
        undeclared = manifest.Subject(self.root / "loose.toml", {"name": "loose"}, modules={"m": loose})
        with self.assertRaises(Refused):
            pipeline_compile.options(undeclared, "m::Entry")


if __name__ == "__main__":
    unittest.main()
