"""Tiny standalone CLI controls using existing Program and IR artifacts only.

Run with ``python3 -m unittest discover -s lean/checks -p test_invocation.py``.
No dependency builds, native tools, dynamic import emitters or kernel replay.
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.invocation import command  # noqa: E402
from support.packages import module_package, module_path  # noqa: E402


class InvocationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="zkc-cli-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.package = module_package("Zkc.IR")
        self.environment = dict(os.environ, LEAN_NUM_THREADS="2")
        self.environment.pop("LEAN_PATH", None)

    def source(self, relative, content):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def invoke(self, *arguments, overlays=(), expected=0):
        env = self.environment | {"LEAN_PATH": os.pathsep.join(map(str, overlays))}
        result = subprocess.run(command(self.package, *arguments), cwd=self.root,
                                env=env, text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def test_native_and_elan_header_parser_launchers(self):
        from support.lean_headers import HeaderParser
        pin = (self.package / "lean-toolchain").read_text().strip()
        environment = self.environment | {"ELAN_TOOLCHAIN": pin}
        prefix = Path(subprocess.check_output(
            ["lake", "env", "lean", "--print-prefix"], cwd=self.package,
            env=environment, text=True).strip())
        for arguments in ({"lake": "lake"}, {"lake": str(prefix / "bin/lake")},
                          {"lean": str(prefix / "bin/lean")}):
            with self.subTest(arguments=arguments), HeaderParser(**arguments) as parser:
                self.assertEqual(parser.imports("module\npublic import Std\n"), ["Std"])
                self.assertTrue(parser.is_module("module\npublic import Std\n"))
        source = self.source("Native.lean", "import Zkc.Program.Interaction\n#check PIR.Process\n")
        result = subprocess.run(command(self.package, source, lake=str(prefix / "bin/lake")),
                                cwd=self.root, env=environment, text=True,
                                capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_arbitrary_file_imports_distinct_shared_namespace_packages(self):
        path = self.source("Elsewhere.lean", """module
public import Zkc.Program.Execution
public meta import Zkc.IR.Source.Structured.Labels
#check PIR.Stop
#eval Zkc.Source.Structured.encodedLabel "a"
""")
        result = self.invoke(path)
        self.assertIn('"label_61"', result.stdout)
        self.assertIn("PIR.Stop", result.stdout)

    def test_run_preserves_arguments_working_directory_and_exit_code(self):
        path = self.source("Run.lean", """import Lean
def main (args : List String) : IO Unit := do
  IO.println (Lean.toJson args).compress
  IO.println (← IO.currentDir)
""")
        values = ["one space", "--setup", "file.lean", "", "한글"]
        result = self.invoke("-j2", "--run", path, *values)
        lines = result.stdout.splitlines()
        self.assertEqual(json.loads(lines[0]), values)
        self.assertEqual(lines[1], str(self.root))
        path.write_text("def main : IO UInt32 := pure 23\n")
        self.invoke("--run", path, expected=23)

    def test_generated_overlay_dependency_has_transitive_cross_package_imports(self):
        overlay = self.root / "objects"
        relative = "objects/Zkc/InvocationControls/Dependency.lean"
        path = self.source(relative, """module
public import Zkc.Program.Execution
public import Zkc.IR.Source.Structured.Labels
@[expose] public def invocationLabel : String := Zkc.Source.Structured.encodedLabel "a"
""")
        self.invoke("--root=" + str(overlay), "-o", path.with_suffix(".olean"), path)
        client = self.source("Client.lean", """module
public meta import Zkc.InvocationControls.Dependency
#eval invocationLabel
""")
        self.assertIn('"label_61"', self.invoke(client, overlays=[overlay]).stdout)

    def test_full_module_lookup_and_exact_overlay_precedence(self):
        left, right = self.root / "left", self.root / "right"
        for root, leaf, value in [(left, "Left", 11), (right, "Right", 19)]:
            path = self.source(str(root.relative_to(self.root) / "Zkc/InvocationControls" / (leaf + ".lean")),
                               f"module\n@[expose] public def probe{leaf} : Nat := {value}\n")
            self.invoke("--root=" + str(root), "-o", path.with_suffix(".olean"), path)
        client = self.source("Distinct.lean", """module
public meta import Zkc.InvocationControls.Left
public meta import Zkc.InvocationControls.Right
#eval probeLeft + probeRight
""")
        self.assertEqual(self.invoke(client, overlays=[left, right]).stdout.strip(), "30")
        # Shadow one real module with deliberately checked exact artifacts.
        # Its original declarations are retained; a fresh marker identifies it.
        module = "Zkc.IR.Source.Structured.Labels"
        for root, value in [(left, 31), (right, 47)]:
            path = self.source(str(root.relative_to(self.root) / Path(*module.split('.')).with_suffix('.lean')),
                               module_path(module).read_text() +
                               f"\npublic def invocationMarker : Nat := {value}\n")
            self.invoke("--root=" + str(root), "-o", path.with_suffix(".olean"), path)
        client.write_text("module\npublic meta import " + module + "\n#eval invocationMarker\n")
        self.assertEqual(self.invoke(client, overlays=[left, right]).stdout.strip(), "31")
        self.assertEqual(self.invoke(client, overlays=[right, left]).stdout.strip(), "47")

    def test_invalid_source_missing_module_and_missing_file_fail(self):
        path = self.source("Invalid.lean", 'def broken : Nat := "wrong"\n')
        result = self.invoke(path, expected=1)
        self.assertIn("type mismatch", result.stdout.lower())
        path.write_text("import Zkc.InvocationControls.DoesNotExist\n")
        result = self.invoke(path, expected=1)
        self.assertIn("Zkc", result.stdout + result.stderr)
        self.invoke(self.root / "Missing.lean", expected=1)

    def test_overlay_preserves_private_import_visibility(self):
        path = self.source("Visibility.lean", """module
def invocationHidden : Nat := 3
@[expose] public def invocationShown : Nat := 7
""")
        self.invoke("--root=" + str(self.root), "-o", path.with_suffix(".olean"), path)
        client = self.source("VisibilityClient.lean", "module\nimport Visibility\n#check invocationHidden\n")
        result = self.invoke(client, overlays=[self.root], expected=1)
        self.assertIn("Unknown identifier", result.stdout)
        client.write_text("module\nimport all Visibility\n#check invocationHidden\n")
        self.assertIn("invocationHidden : Nat", self.invoke(client, overlays=[self.root]).stdout)

    def test_control_options_leave_sorry_refusal_to_the_auditor(self):
        path = self.source("InvocationProofControl.lean", "import Lean\ntheorem controlHole : False := by sorry\n")
        self.invoke("-DwarningAsError=false", "-DautoImplicit=true", "--root=" + str(self.root),
                    "-o", path.with_suffix(".olean"), path)
        client = self.source("Audit.lean", """import InvocationProofControl
import Zkc.Tools.Program.DeclarationAudit
run_cmd ZkcTools.DeclarationAudit.check [`InvocationProofControl]
""")
        result = self.invoke(client, overlays=[self.root], expected=1)
        self.assertIn("unexpected axiom", result.stdout)
        self.assertIn("sorryAx", result.stdout)


if __name__ == "__main__":
    unittest.main()
