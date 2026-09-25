#!/usr/bin/env python3
"""Maintained enforcement controls; requires selected Lean and a built block-checker.

Run: python3 test_checks.py [--lean LEAN] [--lake LAKE] [--block-checker PATH]
All mutation controls use fresh temporary directories, never package sources.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import audit_imports
import check_clients
import check_foundation
import check_library
# The package directory, which is no longer this file's own now that the
# checks sit together: support/ is beside formal/, not beside this.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.lean_headers import HeaderParser  # noqa: E402
import reproduce

ROOT = Path(__file__).resolve().parents[1]
LEAN = "lean"
LAKE = "lake"
BLOCK = ROOT / ".lake/build/bin/block-checker"


class HeaderControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.headers = HeaderParser(LEAN)

    @classmethod
    def tearDownClass(cls):
        cls.headers.__exit__()

    def test_selected_lake_header_parser_without_lean_on_path(self):
        selected = shutil.which(LAKE)
        self.assertIsNotNone(selected)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copy2(ROOT / "lean-toolchain", root / "lean-toolchain")
            (root / "lakefile.toml").write_text('name = "header_control"\n')
            with patch.dict(os.environ, {"PATH": ""}), HeaderParser(root=root, lake=selected) as headers:
                self.assertEqual(headers.imports("import Std\n"), ["Std"])

    def test_comments_and_multiple_imports(self):
        source = """/- import Forbidden.Fake /- nested -/ -/
import Std -- ordinary trailing comment
import /- between tokens -/ Lean
-- import Forbidden.Line
import Init /- trailing block -/
def text := "import Forbidden.String"
"""
        self.assertEqual(self.headers.imports(source), ["Std", "Lean", "Init"])
        self.assertEqual(self.headers.imports("import Std import Lean\n"), ["Std", "Lean"])

    def test_modifiers(self):
        self.assertEqual(self.headers.imports("""module
prelude
public import Std
meta import Lean
public meta import Init
import all Std.Data.HashMap
meta import all Lean.Parser
"""), ["Std", "Lean", "Init", "Std.Data.HashMap", "Lean.Parser"])
        self.assertEqual(self.headers.imports("import «Zkc».Semantics.Execution\n"),
                         ["Zkc.Semantics.Execution"])

    def test_malformed_headers_fail(self):
        for source in ("import\n", "import /- unterminated", "public import Std\n",
                       "module\npublic import all Std\n"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.headers.imports(source)

    def test_both_boundaries_see_unused_forbidden_imports(self):
        for header in ("import Mathlib -- trailing comment\n",
                       "import /- comment -/ Mathlib\n",
                       "module\npublic import Mathlib\n",
                       "module\nmeta import all Mathlib\n",
                       "import Std import Mathlib\n"):
            with self.subTest(header=header), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "Tests").mkdir()
                (root / "Tests/FoundationAudit.lean").write_text(header)
                with self.assertRaisesRegex(ValueError, "external foundation import"):
                    check_foundation.foundation_inputs(root, self.headers)
                boundary = {"roots": ["Tests.FoundationAudit"], "external": ["Std"],
                            "forbidden": ["Mathlib"]}
                with patch.object(check_library, "ROOT", root):
                    with self.assertRaisesRegex(ValueError, "forbidden dependency Mathlib"):
                        check_library.check_boundary("control", boundary, self.headers)

    def test_foundation_inventories_shared_tool(self):
        inputs = check_foundation.foundation_inputs(ROOT, self.headers)
        self.assertIn("Tools/DeclarationAudit.lean", inputs)
        self.assertIn("Tests/Interaction.lean", inputs)
        self.assertFalse(any("Mathlib" in path for path in inputs))


class TargetControls(unittest.TestCase):
    """What building this package means is declared once, in the lakefile."""

    def test_every_declared_target_is_a_default_target(self):
        import tomllib

        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        declared = [
            entry["name"]
            for kind in ("lean_lib", "lean_exe")
            for entry in config.get(kind, [])
        ]
        self.assertTrue(declared, "the package declares something to build")
        missing = sorted(set(declared) - set(config["defaultTargets"]))
        self.assertEqual(
            missing,
            [],
            "a target nothing builds is a checker nothing runs; add it to "
            "defaultTargets rather than to a caller's list",
        )

    def test_every_executable_is_named_by_something_that_runs_it(self):
        """Building a checker is not running it.

        `relation-reference` was a default target for months with no caller
        anywhere: its library was covered but its command -- the arity, the
        exit codes, the framing -- was not.
        """
        import tomllib

        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        executables = [entry["name"] for entry in config.get("lean_exe", [])]
        repository = ROOT.parent
        # Only files that could invoke one. The lakefile names every executable
        # twice by construction -- once declared, once a default target -- so
        # counting it made this pass for everything; and this file's own prose
        # mentions two of them.
        callers = "".join(
            path.read_text(errors="replace")
            for folder in ("formal", "tests", "crates", "compiler", ".github")
            for path in sorted((repository / folder).rglob("*"))
            if path.is_file()
            and path.suffix in {".py", ".rs", ".yml"}
            and path != Path(__file__).resolve()
            and ".lake" not in path.parts
            and "target" not in path.parts
        ) + (repository / "justfile").read_text()
        unrun = [name for name in executables if name not in callers]
        self.assertEqual(
            unrun,
            [],
            "each of these is built and nothing names it; give it a caller or "
            "stop declaring it",
        )


class NativeEvaluationControls(unittest.TestCase):
    """Where native evaluation may appear, and where the audit can see it.

    `native_decide` adds a native-evaluation axiom to whatever it closes. On a
    theorem that axiom enters the environment and the declaration audit rejects
    it; on an `example` nothing enters the environment at all, so the audit
    neither sees the tactic nor could. That is why the conformance cases use
    examples and the library does not use the tactic: the audit's counts would
    otherwise describe a smaller thing than a reader takes them to.
    """

    OWNED = ("Zkc", "Tools", "Examples")

    @staticmethod
    def code(path):
        """Each line with its comments removed, so prose is not read as code.

        A doc comment saying a file uses no native evaluation must not read as
        a use of it, and a use with a comment after it must not hide behind
        one.
        """
        depth, lines = 0, []
        for line in path.read_text().splitlines():
            bare, at = "", 0
            while at < len(line):
                if depth == 0 and line.startswith("--", at):
                    break
                if line.startswith("/-", at):
                    depth += 1
                    at += 2
                elif line.startswith("-/", at):
                    depth = max(0, depth - 1)
                    at += 2
                else:
                    if depth == 0:
                        bare += line[at]
                    at += 1
            lines.append(bare)
        return lines

    @classmethod
    def mentions(cls, path):
        """Line numbers naming the tactic in code rather than in prose."""
        return [(number, line) for number, line in enumerate(cls.code(path), 1)
                if "native_decide" in line]

    def test_the_proof_library_its_tools_and_examples_use_no_native_evaluation(self):
        found = [
            f"{path.relative_to(ROOT)}:{number}"
            for directory in self.OWNED
            for path in sorted((ROOT / directory).rglob("*.lean"))
            for number, _ in self.mentions(path)
        ]
        self.assertEqual(
            found,
            [],
            "docs/assurance.md states these carry no native-evaluation axiom",
        )

    def test_conformance_cases_use_it_only_on_examples(self):
        offenders = []
        openers = {"example", "theorem", "lemma", "def", "instance", "abbrev"}
        for path in sorted((ROOT / "Tests").rglob("*.lean")):
            lines = self.code(path)
            for number, _ in self.mentions(path):
                # The declaration this closes is the last one opened above it.
                # An opener this does not recognise is an offender rather than
                # something to walk past, or an attribute or modifier in front
                # of a theorem would resolve to an example further up.
                opener = next(
                    (
                        earlier.strip()
                        for earlier in reversed(lines[:number])
                        if earlier[:1].isalpha() or earlier.lstrip().startswith("@[")
                    ),
                    "",
                )
                # A leading attribute, then any modifiers, then the keyword.
                without = re.sub(r"^@\[[^\]]*\]\s*", "", opener)
                words = [w for w in without.split() if w not in {"private", "protected", "noncomputable", "partial", "unsafe"}]
                first = words[0] if words else ""
                if first != "example":
                    offenders.append(
                        f"{path.relative_to(ROOT)}:{number} {opener[:40]}"
                        + ("" if first in openers else " (unrecognised opener)")
                    )
        self.assertEqual(
            offenders,
            [],
            "a theorem closed by native evaluation carries an axiom the audit "
            "would have to account for; these cases are examples for that reason",
        )


class BackendProfileCaseControls(unittest.TestCase):
    """The same case, stated in two files, has to stay the same case.

    Requests.lean pins what `check` decides about a request; Encodings.lean
    pins what `validate` decides about the same proposal, and `validate` ends
    in `check`. Thirty-nine cases appear in both, written out rather than
    shared, because each file reads as a statement of its own cases. Nothing
    would say so if one of them were edited and the other were not.
    """

    FILES = (
        ("Tests/BackendProfiles/Requests.lean", "request"),
        ("Tests/BackendProfiles/Encodings.lean", "proposal"),
    )

    # What the two files share today. Recorded rather than bounded, because a
    # case that stops being paired -- a renamed label, a definition wrapped
    # across lines -- would otherwise drop out of the comparison silently.
    SHARED = 39

    @classmethod
    def cases(cls, name, prefix):
        """Each labelled definition in one of those files, by its label.

        A definition this cannot read is an error rather than something to pass
        over: the comparison below is only as good as what it sees.
        """
        found, label, unread = {}, None, []
        for number, line in enumerate((ROOT / name).read_text().splitlines(), 1):
            if line.startswith("-- "):
                label = line[3:].strip().removeprefix("actual/")
            if not line.startswith(f"def {prefix}_"):
                continue
            written = re.match(rf"def {prefix}_\d+ : \S+ := (.+)$", line)
            if not written or not label:
                unread.append(f"{name}:{number}")
            else:
                found.setdefault(label, written.group(1))
        assert not unread, f"unreadable definitions: {unread}"
        return found

    def test_a_case_written_in_both_files_is_written_the_same_way(self):
        requests, encodings = (self.cases(*one) for one in self.FILES)
        shared = sorted(set(requests) & set(encodings))
        self.assertEqual(
            len(shared),
            self.SHARED,
            "the set of cases stated in both files changed; if that is right, "
            "record the new number here",
        )
        self.assertEqual(
            [one for one in shared if requests[one] != encodings[one]],
            [],
            "these cases are stated in both files and no longer agree",
        )


class AuditControls(unittest.TestCase):
    def test_only_exact_generated_paths_excluded(self):
        for library, tests in (("Zkc", "Tests"), ("ZkcArkLib", "TestsArkLib")):
            with self.subTest(library=library), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                for family in (library, tests):
                    for name in ("Audit", "LibraryImports"):
                        for parent in (root / family, root / family / "Nested"):
                            parent.mkdir(parents=True, exist_ok=True)
                            (parent / f"{name}.lean").write_text("")
                imports = audit_imports.expected(root, library, tests)[root / tests / "LibraryImports.lean"]
                for family in (library, tests):
                    for name in ("Audit", "LibraryImports"):
                        self.assertIn(f"import {family}.Nested.{name}\n", imports)
                self.assertIn(f"import {library}.Audit\n", imports)
                self.assertIn(f"import {library}.LibraryImports\n", imports)
                self.assertNotIn(f"import {tests}.Audit\n", imports)
                self.assertNotIn(f"import {tests}.LibraryImports\n", imports)

    def test_nested_unused_axioms_rejected_by_kernel_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copy2(ROOT / "lean-toolchain", root / "lean-toolchain")
            (root / "Tools").mkdir()
            shutil.copy2(ROOT / "Tools/DeclarationAudit.lean", root / "Tools/DeclarationAudit.lean")
            env = dict(os.environ, LEAN_PATH=str(root))

            def compile_module(module):
                path = Path(*module.split("."))
                return subprocess.run([LEAN, "-DwarningAsError=true", "-o", str(path.with_suffix(".olean")),
                                       str(path.with_suffix(".lean"))], cwd=root, env=env,
                                      capture_output=True, text=True, timeout=60)

            tool = compile_module("Tools.DeclarationAudit")
            self.assertEqual(tool.returncode, 0, tool.stdout + tool.stderr)
            modules = [f"{family}.Nested.{name}" for family in ("Zkc", "Tests")
                       for name in ("Audit", "LibraryImports")]
            for module in modules:
                path = root.joinpath(*module.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"namespace {module}\ntheorem ordinary : True := True.intro\nend {module}\n")
                result = compile_module(module)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for path, source in audit_imports.expected(root, "Zkc", "Tests").items():
                path.write_text(source)
            result = compile_module("Tests.LibraryImports")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            baseline = compile_module("Tests.Audit")
            self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
            self.assertIn("DEPENDENCY-AUDIT-PASS", baseline.stdout)
            for module in modules:
                with self.subTest(module=module):
                    path = root.joinpath(*module.split(".")).with_suffix(".lean")
                    original = path.read_text()
                    path.write_text(original + f"axiom {module}.unreferencedHole : False\n")
                    ordinary_build = compile_module(module)
                    self.assertEqual(ordinary_build.returncode, 0, ordinary_build.stdout + ordinary_build.stderr)
                    rejected = compile_module("Tests.Audit")
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertIn("unexpected owned axiom", rejected.stdout)
                    self.assertIn(f"{module}.unreferencedHole", rejected.stdout)
                    self.assertNotIn("DEPENDENCY-AUDIT-PASS", rejected.stdout)
                    path.write_text(original)
                    restored = compile_module(module)
                    self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)


class BlockControls(unittest.TestCase):
    def run_block(self, content):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.json"
            path.write_bytes(content)
            return subprocess.run([str(BLOCK), str(path)], capture_output=True, text=True, timeout=5)

    def test_hostile_numbers_refused_promptly(self):
        for token, reason in ((b"1e1000000000", "expected-natural"),
                              (b"1E+1000000000", "expected-natural"),
                              (b"1.5", "expected-natural"),
                              (b"9" * 1025, "number-limit")):
            with self.subTest(token=token[:30]):
                result = self.run_block(b"[" + token + b"]")
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr.strip(), reason)

    def test_oversize_refused_promptly(self):
        result = self.run_block(b"[" + b" " * (1024 * 1024) + b"]")
        self.assertEqual((result.returncode, result.stdout, result.stderr.strip()), (2, "", "byte-limit"))

    def test_byte_limit_and_invalid_utf8(self):
        at_limit = self.run_block(b"[" + b" " * (1024 * 1024 - 2) + b"]")
        self.assertEqual((at_limit.returncode, at_limit.stdout, at_limit.stderr), (0, "", ""))
        invalid = self.run_block(b"[\xff]")
        self.assertEqual((invalid.returncode, invalid.stderr.strip()), (2, "invalid-utf8"))

    def test_batch_results_keep_exit_zero_and_order(self):
        valid = {"id": "accepted", "profile": "sumcheck:q2305843009213697249",
                 "input_types": ["scalar:q2305843009213697249"], "source": [], "target": [],
                 "source_exports": [[0, "scalar:q2305843009213697249"]],
                 "target_exports": [[0, "scalar:q2305843009213697249"]],
                 "law": "identity-plus-valid-cache"}
        refused = dict(valid, id="semantic", law="unknown-law")
        malformed = {"id": "1e1000000000", "profile": "unknown"}
        result = self.run_block(json.dumps([valid, malformed, refused]).encode())
        self.assertEqual((result.returncode, result.stderr), (0, ""))
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual([row["id"] for row in rows], ["accepted", "1e1000000000", "semantic"])
        self.assertEqual([row["result"]["status"] for row in rows],
                         ["admitted-conditional", "refused-or-malformed", "semantic-law-refused"])
        wrong_shape = self.run_block(b"{}")
        self.assertEqual((wrong_shape.returncode, wrong_shape.stdout), (2, ""))


class ClientToolControls(unittest.TestCase):
    def test_selected_lake_used_and_recorded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "formal"
            (root / "clients").mkdir(parents=True)
            (root / "clients/Main.lean").write_text("namespace Client\nend Client\n")
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
            (root / "lake-manifest.json").write_text('{"packages": []}')
            selected_path = Path(directory) / "selected-lake"
            selected_path.write_text("#!/bin/sh\nexit 99\n")
            selected_path.chmod(0o755)
            selected = str(selected_path)

            def build(command, **kwargs):
                self.assertEqual(command, [selected, "--no-cache", "build"])
                kwargs["stdout"].write("DEPENDENCY-AUDIT-PASS\n")
                return subprocess.CompletedProcess(command, 0)

            with patch.dict(os.environ, {"PATH": ""}), \
                 patch.object(check_clients.subprocess, "run", side_effect=build) as run, \
                 patch.object(check_clients.subprocess, "check_output", side_effect=["Lake selected", "Lean selected"]) as version:
                record = check_clients.check(root, Path(directory) / "clients", lake=selected)
            self.assertEqual(run.call_count, 1)
            self.assertEqual([call.args[0] for call in version.call_args_list],
                             [[selected, "--version"], [selected, "env", "lean", "--version"]])
            client = record["clients"]["main"]
            self.assertEqual(record["status"], "pass")
            self.assertEqual((client["lake_executable"], client["lake_version"], client["lean_version"]),
                             (selected, "Lake selected", "Lean selected"))

    def test_reproducer_propagates_lake(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "result.json").write_text('{"status":"pass"}')
            with patch.object(reproduce.subprocess, "run") as run:
                self.assertEqual(reproduce.run_clients("/selected/lake", ROOT, output, True, {}),
                                 {"status": "pass"})
            self.assertEqual(run.call_args.args[0],
                             ["python3", "checks/check_clients.py", "--lake", "/selected/lake", "--output",
                              str(output), "--with-arklib"])

    def test_reproduction_includes_support_scripts(self):
        inputs = reproduce.build_inputs(ROOT)
        for name in ("support/lean_headers.py", "support/lake.py",
                     "checks/test_checks.py", "checks/check_foundation.py",
                     "Tools/ImportHeaders.lean"):
            self.assertIn(name, inputs)

    def test_reproduction_preserves_shared_fixture_and_detects_drift(self):
        inputs = reproduce.build_inputs(ROOT)
        name = '../tests/fixtures/variants/history-contracts.txt'
        self.assertIn(name, inputs)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory) / 'formal'
            for relative in inputs:
                target = work / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / relative, target)
            self.assertEqual(reproduce.build_inputs(work), inputs)
            fixture = work / name
            fixture.write_text(fixture.read_text() + 'unregistered.transition true\n')
            changed = reproduce.build_inputs(work)
            self.assertEqual({key for key in inputs if inputs[key] != changed[key]}, {name})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=LEAN)
    parser.add_argument("--lake", default=LAKE)
    parser.add_argument("--block-checker", type=Path, default=BLOCK)
    args, remaining = parser.parse_known_args()
    LEAN, LAKE, BLOCK = args.lean, args.lake, args.block_checker.resolve()
    unittest.main(argv=[__file__, *remaining])
