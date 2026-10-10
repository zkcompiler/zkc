"""Command options belong only to the operation or check that consumes them."""

import sys

import pytest

from harness import load


@pytest.mark.parametrize("entrypoint,arguments", [
    ("scripts/develop.py", ["rust", "--profile", "dev"]),
    ("scripts/develop.py", ["rust", "--deps", "main"]),
    ("scripts/develop.py", ["rust", "--output", "unused"]),
    ("scripts/develop.py", ["test-drivers", "--profile", "dev"]),
    ("scripts/develop.py", ["setup", "--output", "unused"]),
    ("scripts/develop.py", ["compiler", "--deps", "clean"]),
    ("scripts/develop.py", ["configure", "--output", "unused"]),
    ("scripts/develop.py", ["fetch-lean", "--profile", "release"]),
    ("scripts/develop.py", ["clean-reports", "--output", "unused"]),
    ("common/tests/run.py", ["rust", "--profile", "dev"]),
    ("common/tests/run.py", ["integration", "--profile", "dev"]),
    ("common/tests/run.py", ["docs", "--profile", "dev"]),
    ("common/tests/run.py", ["install", "--deps", "main"]),
    ("common/tests/run.py", ["install", "--base-build", "unused"]),
    ("common/tests/run.py", ["install", "--skip-build"]),
    ("common/tests/run.py", ["install-domain", "--deps", "main"]),
])
def test_unused_options_fail_before_environment_or_output_changes(entrypoint, arguments, monkeypatch, tmp_path, capsys):
    driver = load("driver", entrypoint)

    def unexpected(*args, **kwargs):
        pytest.fail("invalid arguments must fail before preparing or executing the operation")

    monkeypatch.setattr(driver, "validate_environment", unexpected)
    monkeypatch.setattr(driver, "execute", unexpected)
    reports = tmp_path / "reports"
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(reports))
    monkeypatch.setattr(sys, "argv", [entrypoint, *arguments])
    with pytest.raises(SystemExit) as error:
        driver.main()
    assert error.value.code == 2
    assert "unrecognized arguments" in capsys.readouterr().err
    assert not reports.exists()


@pytest.mark.parametrize("entrypoint,arguments,expected", [
    ("scripts/develop.py", ["configure"], {"profile": "release"}),
    ("scripts/develop.py", ["compiler", "--profile", "dev"], {"profile": "dev"}),
    ("scripts/develop.py", ["fetch-lean"], {"deps": "main"}),
    ("scripts/develop.py", ["lean", "--deps", "arklib"], {"deps": "arklib"}),
    ("scripts/develop.py", ["fetch-lean", "--deps", "clean"], {"deps": "clean"}),
    ("common/tests/run.py", ["compiler", "--profile", "shared"], {"profile": "shared"}),
    ("common/tests/run.py", ["install", "--profile", "shared", "--output", "installed"],
     {"profile": "shared", "output": "installed"}),
    ("common/tests/run.py", ["install-domain", "--base-build", "base", "--domain-build", "domain", "--skip-build"],
     {"profile": "release", "base_build": "base", "domain_build": "domain", "skip_build": True}),
])
def test_valid_options_reach_the_selected_operation(entrypoint, arguments, expected, monkeypatch, tmp_path):
    driver = load("driver", entrypoint)
    calls = []
    monkeypatch.setattr(driver, "execute", lambda *args: calls.append(vars(args[-1])))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", [entrypoint, *arguments])
    driver.main()
    actual, = calls
    assert actual.get("operation", actual.get("scope")) == arguments[0]
    assert expected.items() <= actual.items()


@pytest.mark.parametrize("entrypoint,operation,present,absent", [
    ("scripts/develop.py", "rust", [], ["--profile", "--deps", "--output"]),
    ("scripts/develop.py", "fetch-lean", ["--deps"], ["--profile", "--output"]),
    ("common/tests/run.py", "install", ["--profile", "--output"], ["--deps", "--skip-build"]),
    ("common/tests/run.py", "rust", [], ["--profile", "--output"]),
])
def test_operation_help_lists_only_its_options(entrypoint, operation, present, absent, monkeypatch, capsys):
    driver = load("driver", entrypoint)
    monkeypatch.setattr(sys, "argv", [entrypoint, operation, "--help"])
    with pytest.raises(SystemExit) as error:
        driver.main()
    assert error.value.code == 0
    help_text = capsys.readouterr().out
    assert all(option in help_text for option in present)
    assert all(option not in help_text for option in absent)
