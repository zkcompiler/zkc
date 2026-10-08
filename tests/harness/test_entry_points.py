"""Discovery and command wiring keep maintained test scopes reachable."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

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


def test_every_native_compiler_test_source_has_a_build_target():
    import re

    directory = ROOT / "compiler/test"
    declared = re.findall(r"^add_zkc_test\((\w+)(?:\s+[^)]*)?\)",
                          (directory / "CMakeLists.txt").read_text(), re.MULTILINE)
    assert len(declared) == len(set(declared)), "duplicate native test target"
    assert set(declared) == {path.stem for path in directory.glob("*.cpp")}


def test_every_repository_path_a_test_file_cites_exists():
    """A test that points at its counterpart should point at something.

    These files explain themselves by naming the test that judges the same
    subject from another build, and those names go stale in the ordinary way:
    six of them named a `tests/` file without the `test_` prefix pytest
    collects by, so the counterpart they pointed at did not exist.

    Docstrings are read through `ast` and comments through `tokenize`, because
    the sentence that carries such a path usually wraps, and a filter that
    looked at how a line begins saw the first line of a docstring and none of
    the rest. A path is only recognised when it names one of the repository's
    own top-level directories and ends in an extension, so prose cannot be
    mistaken for one.
    """
    import ast
    import io
    import re
    import tokenize

    pattern = re.compile(r"(?:tests|compiler|crates|formal|docs)/[\w./-]+\.\w+")
    missing = []
    for folder in ("compiler/test", "tests"):
        for path in sorted((ROOT / folder).rglob("*.py")):
            if "__pycache__" in path.parts:
                continue
            source = path.read_text()
            prose = []
            for node in ast.walk(ast.parse(source, str(path))):
                if isinstance(node, (ast.Module, ast.ClassDef,
                                     ast.FunctionDef, ast.AsyncFunctionDef)):
                    prose.append(ast.get_docstring(node) or "")
            prose += [
                token.string
                for token in tokenize.generate_tokens(io.StringIO(source).readline)
                if token.type == tokenize.COMMENT
            ]
            for cited in pattern.findall("\n".join(prose)):
                if not (ROOT / cited).exists():
                    missing.append(f"{path.relative_to(ROOT)}: {cited}")
    assert missing == [], (
        "these paths are cited by a test that describes itself, and are not in "
        "the repository:\n  " + "\n  ".join(sorted(set(missing)))
    )


def test_every_formal_check_is_where_the_loop_that_runs_them_looks():
    """`just test-lean` discovers formal checks and consumers; independent CLI
    controls also live under `tests/support/formal/`.

    That is the whole list, so a check is run by being in one of those places,
    the way a `compiler/test` script is run by being in its directory. What the
    loop cannot see is a check that stayed behind: these lived in `formal/`,
    in `formal/Tests/` beside the Lean modules, and in the justfile as fourteen
    named lines, and adding one meant remembering the list.

    The two scripts still in `formal/` are not checks -- `cache_dependencies`
    fetches and `reproduce` rebuilds -- and `support/` is shared vocabulary,
    so neither is run here.
    """
    formal = ROOT / "formal"
    allowed = {"cache_dependencies.py", "reproduce.py", "source_plan_controls.py"}
    stray = sorted(
        path.name for path in formal.glob("*.py") if path.name not in allowed
    )
    assert stray == [], (
        "these sit in formal/ where the loop does not look; a check belongs in "
        "formal/checks/ and a tool belongs in the exception above"
    )
    beside_lean = sorted(path.name for path in (formal / "Tests").glob("*.py"))
    assert beside_lean == [], (
        "formal/Tests/ is built by Lake, which does not run Python; a check "
        "that landed here would never run"
    )


def test_every_recipe_summary_reads_as_one():
    """`just --list` shows the last comment line above a recipe, and only that.

    The lines above it are for someone reading the file, so a block that ends
    mid-sentence puts a fragment in the listing: `test-compiler` showed "of
    these is what makes a test here expensive to write." until this was
    written. A summary starts a sentence, which is what separates it from a
    continuation line, and is short enough for the listing to hold.
    """
    import re

    # A recipe opens at column zero and its name is followed by parameters and
    # then a colon. `set` and `export` lines also start there and also hold a
    # colon, so the assignment form is what separates them.
    recipe = re.compile(r"^([a-z][\w-]*)(?: [^:=]*)?:(?![=])")
    lines = (ROOT / "justfile").read_text().splitlines()
    wrong = []
    for number, line in enumerate(lines):
        found = recipe.match(line)
        if not found or line.startswith(("set ", "export ")):
            continue
        name = found.group(1)
        if number == 0 or not lines[number - 1].startswith("#"):
            continue
        summary = lines[number - 1].removeprefix("#").strip()
        if not summary[:1].isupper() or len(summary) > 100:
            wrong.append(f"{name}: {summary!r}")
    assert wrong == [], (
        "these recipes hand `just --list` something that does not read as a "
        "summary of them:\n  " + "\n  ".join(wrong)
    )


def test_native_build_covers_tools_and_examples(monkeypatch):
    from harness import load
    import sys

    developer = load("developer", "scripts/develop.py")
    calls = []
    monkeypatch.setattr(developer, "run", lambda args, **kwargs: calls.append(list(map(str, args))))
    monkeypatch.setattr(sys, "argv", ["develop.py", "rust"])
    developer.main()
    assert calls == [["cargo", "build", "--release", "--locked", "--workspace", "--bins", "--examples", "--all-features"]]


def test_documentation_scope_includes_component_guides(monkeypatch):
    from harness import load
    from types import SimpleNamespace
    import sys

    runner = load("test_runner", "tests/run.py")
    calls = []
    monkeypatch.setattr(runner, "run", lambda arguments: calls.append(arguments))
    runner.execute("docs", SimpleNamespace())
    assert calls == [[sys.executable, "tests/check_docs.py", "--all"]]


def test_native_generator_and_client_pairs_remain_available():
    from harness import load
    import tomllib

    integration = load("native_integration", "tests/protocol/test_native_mathematical.py")
    examples = {}
    for manifest in (ROOT / "crates").glob("*/Cargo.toml"):
        config = tomllib.loads(manifest.read_text())
        for entry in config.get("example", []):
            examples[entry["name"]] = manifest.parent / entry["path"]
        for path in (manifest.parent / "examples").glob("*.rs"):
            examples.setdefault(path.stem, path)
    missing = []
    for generator, example in integration.NATIVE_CASES:
        if not (ROOT / f"compiler/test/{generator}.py").is_file():
            missing.append(f"compiler generator {generator}")
        if example not in examples or not examples[example].is_file():
            missing.append(f"Rust example {example}")
    assert not missing, "native integration coverage lost its inputs: " + ", ".join(missing)
