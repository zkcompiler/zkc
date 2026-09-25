"""Diagnostic excerpt and formatter regressions."""

import json
import unittest
from commands import Commands
from source_text import unlocated
from tools import compiler, records




commands = Commands(records())


class PresentationTests(unittest.TestCase):
    def run_command(self, command, text, code=None):
        result = commands.attempt([compiler, command, "-"], stdin=text)
        self.assertEqual(result.returncode, 1 if code else 0, result.stderr)
        if code:
            self.assertIn(code, result.stderr)
            self.assertFalse(result.stdout)
        return result

    def diagnostic(self, line, offset, left, right, code="source-character"):
        result = self.run_command("protocol-parse", "module {\n" + line, code)
        lines = result.stderr.splitlines()
        header = next(i for i, text in enumerate(lines) if ": error: " in text)
        self.assertIn(f"-:2:{offset + 1}: error:", lines[header])
        excerpt, caret = lines[header + 1:header + 3]
        self.assertLessEqual(len(excerpt), 166)  # 160 source bytes + markers.
        self.assertEqual(excerpt.startswith("..."), left)
        self.assertEqual(excerpt.endswith("..."), right)
        self.assertEqual(caret.count("^"), 1)
        if offset < len(line):
            self.assertIn("@bad_token", excerpt)
            position = excerpt.index("@bad_token")
        else:
            position = len(excerpt)
        self.assertEqual(caret[:-1], "".join(
            "\t" if char == "\t" else " " for char in excerpt[:position]))
        for tab_width in (4, 8):
            self.assertEqual(len(caret[:-1].expandtabs(tab_width)),
                             len(excerpt[:position].expandtabs(tab_width)))

    def test_diagnostic_windows(self):
        for prefix, suffix, left, right in (
            ("", " " * 500, False, True),
            (" " * 350, " " * 500, True, True),
            (" " * 500, "", True, False),
            ("\t" * 350, " " * 500, True, True),
            ("\t ", "", False, False),
        ):
            with self.subTest(column=len(prefix) + 1, suffix=len(suffix)):
                self.diagnostic(prefix + "@bad_token" + suffix, len(prefix),
                                left, right)

    def test_diagnostic_eof(self):
        self.diagnostic(" " * 500, 500, True, False, "source-syntax")

    def roundtrip(self, text):
        original = self.run_command("protocol-parse", text).stdout
        formatted = self.run_command("protocol-format", text).stdout
        parsed = self.run_command("protocol-parse", formatted).stdout
        self.assertEqual(unlocated(json.loads(original)["content"]),
                         unlocated(json.loads(parsed)["content"]))
        self.assertEqual(self.run_command("protocol-format", formatted).stdout,
                         formatted)
        return formatted

    def test_keyword_path_members(self):
        for member in ("at", "return", "roles", "requires", "attributes"):
            for separator in ("::", ":: /* member */ ", ":: // member\n",
                              "/* path */ :: /* outer /* nested */ */ "):
                with self.subTest(member=member, separator=separator):
                    text = ("module { fn X(x: bool) -> bool { let y = "
                            f"curve{separator}{member}(x); return y; }} }}")
                    formatted = self.roundtrip(text)
                    self.assertRegex(formatted, rf"\b{member}\(x\)")
                    for comment in ("/* member */", "// member", "/* path */",
                                    "/* outer /* nested */ */"):
                        if comment in separator:
                            self.assertIn(comment, formatted)

    def test_midstatement_keyword_lists(self):
        formatted = self.roundtrip(
            "module { fn X<F: Field>(x: F::Element) -> F::Element "
            "requires (Field(F)) { let y = field::constant::<F>() "
            "attributes (1); return (y); } "
            "configure C = X(F = F) using (site = impl); }")
        for keyword in ("requires", "attributes", "using", "return"):
            self.assertIn(keyword + " (", formatted)


unittest.main(argv=[__file__])
