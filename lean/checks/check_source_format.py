#!/usr/bin/env python3
"""Every compiler invocation of the Lean bridges selects a declared source format.

The selection of a source a package lists, and of a project-backed invocation,
is the one the SDK's project inspection reports, with the SDK's own refusals of
a missing, unknown or mixed selection anywhere in a closure. Only a fixture
that no package lists takes the fixture declarations; an explicit caller
selection is validated. Every selection goes through
`bridges/common/source_format.py`; no bridge or check spells the compiler
option itself. An undeclared source and a mixed invocation refuse before the
compiler runs, and without the SDK a package's selection refuses.

Controls that inspect packages need the SDK executable (`ZKC_NATIVE_BIN`) and
no compiler; without the SDK they are skipped and name the build to run.
"""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

LEAN = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(LEAN))
sys.path.insert(0, str(LEAN / "bridges/structured"))
from bridges.common import native_entry, source_format  # noqa: E402
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.pipeline import compile as pipeline_compile, manifest  # noqa: E402
import check as structured  # noqa: E402
sys.path.append(str(LEAN.parent / "common/tests/support"))
from toolchain import Missing, Toolchain  # noqa: E402


def missing_sdk():
    """Why the SDK's project inspection cannot run here, or None."""
    try:
        Toolchain().runtime
    except Missing as error:
        return f"the SDK's project inspection is unavailable: {error}"
    return None


MISSING_SDK = missing_sdk()
requires_sdk = unittest.skipIf(MISSING_SDK is not None, MISSING_SDK or "")


class Spelling(unittest.TestCase):
    def test_no_bridge_or_check_spells_the_option(self):
        helper = Path(source_format.__file__).resolve()
        offenders = [str(path.relative_to(LEAN)) for directory in ("bridges", "checks")
                     for path in sorted((LEAN / directory).rglob("*.py"))
                     if path.resolve() != helper and source_format.OPTION in path.read_text(encoding="utf-8")]
        self.assertEqual(offenders, [])


@requires_sdk
class DeclaredSelections(unittest.TestCase):
    def test_every_subject_resolves_a_declared_format(self):
        for subject in manifest.load_all():
            with self.subTest(subject=subject.name):
                expected = (source_format.of_project(subject.project / "zkc.toml") if subject.project is not None
                            else source_format.of_sources(subject.modules.values()))
                self.assertIn(expected, source_format.FORMATS)
                selected = pipeline_compile.options(subject, "entry")[0]
                self.assertEqual(source_format.require_option([selected]), expected)

    def test_every_structured_fixture_resolves_a_declared_format(self):
        for stem, spec in structured.fixture_table().items():
            with self.subTest(fixture=stem):
                # The inlining suite compiles its one fixture source named after the table entry.
                sources = ([LEAN / "bridges/structured/fixtures" / f"{stem}.zkc"] if "module" in spec
                           else structured.fixture(stem)[1].values())
                self.assertIn(source_format.of_sources(sources), source_format.FORMATS)

    def test_package_sources_resolve(self):
        root = source_format.ROOT
        for path in ["examples/projects/schnorr/main.zkc", "libraries/protocols/sigma/schnorr/lib.zkc"]:
            with self.subTest(source=path):
                self.assertIn(source_format.of_source(root / path), source_format.FORMATS)


class FixtureSelections(unittest.TestCase):
    def test_unpackaged_fixture_sources_resolve(self):
        root = source_format.ROOT
        for path in ["lean/bridges/common/fixtures/factor-openings.zkc",
                     "compiler/test/fixtures/structured-source/scoped-control.zkc"]:
            with self.subTest(source=path):
                self.assertIn(source_format.of_source(root / path), source_format.FORMATS)


class Refusals(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="zkc-source-format-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name).resolve()

    def package(self, name, value=None, modules=("main.zkc",), dependencies=()):
        directory = self.root / name
        directory.mkdir(parents=True)
        lines = ['format = "zkc.project/0"']
        if value is not None:
            lines.append(f'source-format = "{value}"')
        lines.append("[modules]")
        for index, module in enumerate(modules):
            (directory / module).write_text("module m;\n")
            lines.append(f'm{index} = "{module}"')
        lines.append("[dependencies]")
        for dependency in dependencies:
            lines.append(f'{dependency} = "../{dependency}"')
        (directory / "zkc.toml").write_text("\n".join(lines) + "\n")
        return [directory / module for module in modules]

    def refuses(self, pattern, paths, declarations=None):
        with self.assertRaisesRegex(Refused, pattern):
            source_format.of_sources(paths, root=self.root, declarations=declarations or {})

    @requires_sdk
    def test_missing_and_unknown_manifest_selections_refuse(self):
        # The SDK's manifest reader refuses both, with its own code.
        self.refuses("the SDK refuses the package: source-project-format", self.package("missing"))
        self.refuses("the SDK refuses the package: source-project-format", self.package("unknown", "zkc2"))

    @requires_sdk
    def test_dependency_only_manifest_disagreement_refuses(self):
        # Every manifest of a closure states one selection, including one that
        # lists no module and only names dependencies.
        leaf = self.package("leaf", "zkc", modules=("lib.zkc",))
        self.package("middle", "zkc-layout", modules=(), dependencies=("leaf",))
        main = self.package("main", "zkc", dependencies=("middle",))
        self.refuses("the SDK refuses the package: source-project-mixed-format", main + leaf)
        with self.assertRaisesRegex(Refused, "the SDK refuses the package: source-project-mixed-format"):
            source_format.of_project(self.root / "main/zkc.toml")
        # The leaf's own closure is consistent.
        self.assertEqual(source_format.of_sources(leaf, root=self.root, declarations={}), "zkc")

    def test_package_without_the_sdk_refuses(self):
        (source,) = self.package("unbuilt", "zkc")
        empty = self.root / "no-tools"
        empty.mkdir()
        with mock.patch.dict(os.environ, {"ZKC_NATIVE_BIN": str(empty)}):
            self.refuses("the SDK's project inspection selects its source format", [source])

    @requires_sdk
    def test_package_route_needs_no_compiler(self):
        (source,) = self.package("compiler-free", "zkc-layout")
        empty = self.root / "no-compiler"
        empty.mkdir()
        with mock.patch.dict(os.environ, {"ZKC_COMPILER_BIN": str(empty)}):
            self.assertEqual(source_format.of_sources([source], root=self.root, declarations={}), "zkc-layout")
            self.assertEqual(source_format.of_project(self.root / "compiler-free/zkc.toml"), "zkc-layout")

    def test_undeclared_source_refuses(self):
        loose = self.root / "loose.zkc"
        loose.write_text("module m;\n")
        self.refuses("no package manifest lists it", [loose])

    @requires_sdk
    def test_unlisted_package_source_refuses(self):
        listed = self.package("other", "zkc")
        unlisted = listed[0].with_name("unlisted.zkc")
        unlisted.write_text("module m;\n")
        self.refuses("no package manifest lists it", [unlisted])

    @requires_sdk
    def test_mixed_invocation_refuses(self):
        self.refuses("mixed source formats", self.package("first", "zkc") + self.package("second", "zkc-layout"))

    @requires_sdk
    def test_package_selection_is_forwarded_exactly(self):
        (layout,) = self.package("layout", "zkc-layout")
        self.assertEqual(source_format.option([layout], root=self.root, declarations={}),
                         source_format.OPTION + "zkc-layout")
        self.assertEqual(source_format.of_project(self.root / "layout/zkc.toml"), "zkc-layout")
        # A package decides over the declaration of an enclosing fixture directory.
        declared = {self.root / "fixtures": "zkc-layout"}
        (listed,) = self.package("fixtures/package", "zkc")
        self.assertEqual(source_format.of_source(listed, root=self.root, declarations=declared), "zkc")

    def test_fixture_declaration_is_forwarded_exactly(self):
        fixtures = self.root / "fixtures"
        fixtures.mkdir()
        (fixtures / "a.zkc").write_text("module a;\n")
        declared = {fixtures: "zkc-layout"}
        self.assertEqual(source_format.of_source(fixtures / "a.zkc", root=self.root, declarations=declared),
                         "zkc-layout")

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
