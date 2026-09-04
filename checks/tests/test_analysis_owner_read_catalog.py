"""The Analysis owner-read catalog selects only fields the owner bodies declare.

`docs-next/analysis/cryptographic-properties.md` Section 3 lists, per PIR view,
the field names an Analysis question reads; each name denotes the ordinal path
of that field in the closed owner schema, and a path that reaches no field is
malformed under the field-projection law of `docs-next/analysis/analysis-model.md`
Section 2.1. Owner bodies live on the PIR pages. This control joins every
selection against the owner body it names, so a page-local edit on either side
cannot leave a read that literally cannot be formed.
"""

from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[2]
OWNER_PAGES = (
    ROOT / "docs-next" / "pir" / "interactive-core.md",
    ROOT / "docs-next" / "pir" / "fiat-shamir.md",
)
CATALOG = ROOT / "docs-next" / "analysis" / "cryptographic-properties.md"
BODY = re.compile(r"^(\w+ViewBody) = \{\n(.*?)^\}", re.S | re.M)
FIELD = re.compile(r"^  (\w+):", re.M)
SELECTION = re.compile(
    r"Analysis(Static|Execution)ViewFields\(subject,(\w+),\s*\[(.*?)\]\)", re.S
)
# An execution axis names a Protocol-level view whose body is profile-specific.
AXIS_BODY = {
    "FreshExecutionView": "ExecutionViewBody",
    "FiatShamirExecutionView": "CanonicalFramedExecutionViewBody",
}


def owner_bodies() -> dict[str, list[str]]:
    bodies: dict[str, list[str]] = {}
    for page in OWNER_PAGES:
        for match in BODY.finditer(page.read_text(encoding="utf-8")):
            name = match.group(1)
            assert name not in bodies, f"{name} is declared on two owner pages"
            bodies[name] = FIELD.findall(match.group(2))
    return bodies


class AnalysisOwnerReadCatalogTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bodies = owner_bodies()
        cls.catalog = CATALOG.read_text(encoding="utf-8")

    def test_every_selected_field_is_declared_by_the_owner_body(self) -> None:
        selections = list(SELECTION.finditer(self.catalog))
        self.assertGreaterEqual(len(selections), 9)
        for match in selections:
            view = match.group(2)
            body = AXIS_BODY.get(view, f"{view}Body")
            names = [
                name.strip()
                for name in match.group(3).replace("\n", " ").split(",")
                if name.strip()
            ]
            with self.subTest(view=view, line=self.catalog.count("\n", 0, match.start()) + 1):
                self.assertIn(body, self.bodies, f"no owner body named {body}")
                self.assertEqual(len(names), len(set(names)), "duplicate selection")
                missing = [name for name in names if name not in self.bodies[body]]
                self.assertEqual([], missing, f"{body} declares {self.bodies[body]}")

    def test_the_static_view_names_used_by_the_catalog_have_owner_bodies(self) -> None:
        for name in ("PublicBindingView", "StrategyDecisionView", "PublicCoinView",
                     "ClaimReductionView", "TranscriptDeclarationView",
                     "RequiredInfluenceView", "ChallengeTransitionView",
                     "FSConstructionView"):
            with self.subTest(view=name):
                self.assertIn(f"{name}Body", self.bodies)


if __name__ == "__main__":
    unittest.main()
