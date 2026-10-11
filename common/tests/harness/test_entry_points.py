"""Discovery and command wiring keep maintained test scopes reachable."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]

def test_every_compiler_test_is_where_the_glob_that_registers_them_looks():
    """`compiler/test/CMakeLists.txt` globs `*.py`, and does not descend.

    A test moved into a subdirectory there stops running, which is the failure
    the glob is supposed to make impossible. Shared vocabulary lives in
    `support/`, which is deliberately not registered.
    """
    directory = ROOT / "compiler/test"
    stray = sorted(
        str(path.relative_to(ROOT))
        for path in directory.rglob("*.py")
        if path.parent != directory and path.parent.name != "support"
    )
    assert stray == [], (
        "CMake registers compiler/test/*.py and does not descend, so these are "
        "neither tests nor the vocabulary tests import"
    )


def test_every_lean_check_is_where_the_loop_that_runs_them_looks():
    """`just test-lean` discovers Lean checks and independent consumers.

    Top-level formal scripts provide dependency fetching, source planning and
    reproduction. Checks belong in discovered directories; shared helpers are
    not registered as independent checks.
    """
    formal = ROOT / "lean"
    allowed = {"cache_dependencies.py", "reproduce.py", "source_plan_controls.py"}
    stray = sorted(
        path.name for path in formal.glob("*.py") if path.name not in allowed
    )
    assert stray == [], (
        "these sit in lean/ where the loop does not look; a check belongs in "
        "lean/checks/ and a tool belongs in the exception above"
    )
    beside_lean = sorted(path.name for path in (formal / "Tests").glob("*.py"))
    assert beside_lean == [], (
        "lean/Tests/ is built by Lake, which does not run Python; a check "
        "that landed here would never run"
    )


def test_product_and_driver_builds_are_separate(monkeypatch):
    from harness import load
    import sys

    developer = load("developer", "scripts/develop.py")
    calls = []
    monkeypatch.setattr(developer, "run", lambda args, **kwargs: calls.append(list(map(str, args))))
    monkeypatch.setattr(sys, "argv", ["develop.py", "rust"])
    developer.main()
    monkeypatch.setattr(sys, "argv", ["develop.py", "test-drivers"])
    developer.main()
    assert calls == [
        ["cargo", "build", "--release", "--locked", "-p", "zkc-tools", "--bin", "zkc"],
        ["cargo", "build", "--release", "--locked", "-p", "zkc-test-drivers", "--bins"],
    ]


def test_documentation_scope_includes_component_guides(monkeypatch):
    from harness import load
    from types import SimpleNamespace
    import sys

    runner = load("test_runner", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(runner, "run", lambda arguments: calls.append(arguments))
    runner.execute("docs", SimpleNamespace())
    assert calls == [[sys.executable, "common/tests/check_docs.py", "--all"]]
