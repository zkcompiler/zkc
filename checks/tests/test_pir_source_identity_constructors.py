"""Every PIR source-authority identity is formed through its profile's compiler.

`docs-next/pir/interactive-core.md` Section 13.3 compiles each `pir.source-*`
subject kind as one closed variant over the families its profile issues, and
requires every identity constructor to apply `ProfiledSemanticId` to a
compiler's output over a tagged family value, never to a family-local body.
Two preimage equations for one subject kind would let two producers form
different identities for the same subject. This control reads every
constructor site on the PIR pages and checks that it applies a compiler the
same page defines for that kind, or the owner-profile dispatcher, to a tagged
family value the compiler enumerates.
"""

from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[2]
PAGES = sorted((ROOT / "docs-next" / "pir").glob("*.md"))
KIND_SUFFIX = {
    "binding-payload": "BindingPayload",
    "capability-requirement": "CapabilityRequirement",
    "no-policy": "NoPolicy",
    "policy-closure": "PolicyClosure",
}
SITE = re.compile(
    r'ProfiledSemanticId<"pir\.source-(binding-payload|capability-requirement|'
    r'no-policy|policy-closure)">\('
)
DIRECT = re.compile(r"\s*B,\s*(\w+),\s*(\w+)\(\s*(\w+)\(")
DISPATCHED = re.compile(
    r'\s*B,\s*(\w+),\s*SourceSubjectBody\(\1,\s*"pir\.source-([a-z-]+)"\)\(\s*(\w+)\('
)
COMPILER = re.compile(
    r"^(\w*)Source(BindingPayload|CapabilityRequirement|NoPolicy|PolicyClosure)"
    r"Body\(x\) =",
    re.M,
)
ARM = re.compile(r"if x = (\w+)\(y\)")


class SourceIdentityConstructorTest(unittest.TestCase):
    def test_every_constructor_applies_a_compiler_to_a_tagged_family_value(self) -> None:
        sites = 0
        for page in PAGES:
            text = page.read_text(encoding="utf-8")
            compilers = {(prefix, kind) for prefix, kind in COMPILER.findall(text)}
            tags = set(ARM.findall(text))
            for site in SITE.finditer(text):
                sites += 1
                kind = KIND_SUFFIX[site.group(1)]
                tail = text[site.end(): site.end() + 300]
                line = text.count("\n", 0, site.start()) + 1
                with self.subTest(page=page.name, line=line):
                    dispatched = DISPATCHED.match(tail)
                    if dispatched is not None:
                        self.assertEqual(site.group(1), dispatched.group(2))
                        self.assertEqual("StaticView", dispatched.group(3))
                        continue
                    direct = DIRECT.match(tail)
                    self.assertIsNotNone(direct, "not applied to a compiler over a tagged value")
                    _profile, compiler, tag = direct.groups()
                    suffix = f"Source{kind}Body"
                    self.assertTrue(compiler.endswith(suffix), f"{compiler} is not a {suffix}")
                    self.assertIn((compiler[: -len(suffix)], kind), compilers,
                                  f"{compiler} is not defined on {page.name}")
                    self.assertIn(tag, tags, f"{compiler} has no arm for {tag}")
        self.assertGreaterEqual(sites, 14)

    def test_every_compiler_enumerates_tagged_arms_only(self) -> None:
        for page in PAGES:
            text = page.read_text(encoding="utf-8")
            for match in COMPILER.finditer(text):
                block_end = text.find("\n\n", match.end())
                block = text[match.end(): block_end if block_end > 0 else None]
                # Each compiler block runs to the next blank line; every arm
                # names its family tag, and no arm applies the untagged value.
                with self.subTest(page=page.name, compiler=match.group(0).strip()):
                    self.assertGreaterEqual(len(ARM.findall(block)), 1)
                    self.assertNotIn("Body(x))", block)


if __name__ == "__main__":
    unittest.main()
