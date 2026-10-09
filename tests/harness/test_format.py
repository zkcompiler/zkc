"""Formatting includes maintained sources even inside a build sandbox."""
from harness import load


def test_build_ancestor_does_not_hide_sources(monkeypatch, tmp_path):
    formatter = load("format_sources", "scripts/format.py")
    root = tmp_path / "build" / "source"
    paths = ["compiler/main.cpp", "compiler/include/api.h", "tests/consumer/main.cpp",
             "compiler/build/generated.cpp", "compiler/.cache/generated.h"]
    for relative in paths:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()
    monkeypatch.setattr(formatter, "ROOT", root)
    assert {p.relative_to(root).as_posix() for p in formatter.sources()} == set(paths[:3])
