from __future__ import annotations

import ast
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT / "oracle"


def _relative_dependencies(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    dependencies: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.level:
            if node.module:
                dependencies.add(node.module.split(".", 1)[0])
            else:
                dependencies.update(alias.name.split(".", 1)[0] for alias in node.names)
    return dependencies


class ReferenceArchitectureTest(unittest.TestCase):
    def test_bottom_modules_do_not_import_higher_semantic_layers(self) -> None:
        self.assertEqual(_relative_dependencies(ORACLE / "canonical.py"), set())
        self.assertEqual(_relative_dependencies(ORACLE / "babybear.py"), set())

    def test_signature_and_wellformedness_do_not_depend_on_pir_model(self) -> None:
        self.assertNotIn("model", _relative_dependencies(ORACLE / "signature.py"))
        self.assertNotIn("model", _relative_dependencies(ORACLE / "wellformed.py"))
        self.assertSetEqual(
            _relative_dependencies(ORACLE / "signature.py"),
            {"canonical"},
        )
        self.assertSetEqual(
            _relative_dependencies(ORACLE / "wellformed.py"),
            {"canonical", "signature"},
        )

    def test_reference_modules_do_not_import_project_implementation_packages(
        self,
    ) -> None:
        forbidden = {
            "evaluation",
            "include",
            "lib",
            "tools",
            "emit",
        }
        for path in sorted(ORACLE.glob("*.py")):
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
            imported_roots = {
                alias.name.split(".", 1)[0]
                for node in ast.walk(tree)
                if isinstance(node, ast.Import)
                for alias in node.names
            }
            imported_roots.update(
                node.module.split(".", 1)[0]
                for node in ast.walk(tree)
                if isinstance(node, ast.ImportFrom)
                and node.level == 0
                and node.module
            )
            self.assertFalse(forbidden & imported_roots, path.name)


if __name__ == "__main__":
    unittest.main()
