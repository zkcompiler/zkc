"""Development commands reject unused options before changing the workspace."""

import sys

import pytest

from harness import load


@pytest.mark.parametrize("arguments", [
    ["rust", "--profile", "dev"],
    ["rust", "--profile", "release"],
    ["rust", "--deps", "main"],
    ["rust", "--output", "unused"],
    ["test-drivers", "--profile", "dev"],
    ["setup", "--output", "unused"],
    ["compiler", "--deps", "clean"],
    ["configure", "--output", "unused"],
    ["fetch-lean", "--profile", "release"],
    ["lean", "--deps", "arklib"],
    ["install", "--deps", "main"],
    ["install", "--base-build", "unused"],
    ["install", "--domain-build", "unused"],
    ["install", "--skip-build"],
    ["install-domain", "--deps", "main"],
    ["clean-reports", "--output", "unused"],
])
def test_unused_options_fail_before_environment_or_output_changes(arguments, monkeypatch, tmp_path, capsys):
    developer = load("developer", "scripts/develop.py")

    def unexpected(*args, **kwargs):
        pytest.fail("invalid arguments must fail before preparing or executing the operation")

    monkeypatch.setattr(developer, "validate_environment", unexpected)
    monkeypatch.setattr(developer, "execute", unexpected)
    reports = tmp_path / "reports"
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(reports))
    monkeypatch.setattr(sys, "argv", ["develop.py", *arguments])
    with pytest.raises(SystemExit) as error:
        developer.main()
    assert error.value.code == 2
    assert "unrecognized arguments" in capsys.readouterr().err
    assert not reports.exists()


@pytest.mark.parametrize("arguments,expected", [
    (["configure"], {"profile": "release"}),
    (["compiler", "--profile", "dev"], {"profile": "dev"}),
    (["fetch-lean"], {"deps": "main"}),
    (["fetch-lean", "--deps", "clean"], {"deps": "clean"}),
    (["install", "--profile", "shared", "--output", "installed"],
     {"profile": "shared", "output": "installed"}),
    (["install-domain", "--base-build", "base", "--domain-build", "domain", "--skip-build"],
     {"profile": "release", "base_build": "base", "domain_build": "domain", "skip_build": True}),
])
def test_valid_options_reach_the_selected_operation(arguments, expected, monkeypatch, tmp_path):
    developer = load("developer", "scripts/develop.py")
    calls = []
    monkeypatch.setattr(developer, "execute", lambda args: calls.append(vars(args)))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", *arguments])
    developer.main()
    actual, = calls
    assert actual["operation"] == arguments[0]
    assert expected.items() <= actual.items()


def test_operation_help_lists_only_its_options(monkeypatch, capsys):
    developer = load("developer", "scripts/develop.py")
    for operation, present, absent in [
        ("rust", [], ["--profile", "--deps", "--output"]),
        ("fetch-lean", ["--deps"], ["--profile", "--output"]),
        ("install", ["--profile", "--output"], ["--deps", "--skip-build"]),
    ]:
        monkeypatch.setattr(sys, "argv", ["develop.py", operation, "--help"])
        with pytest.raises(SystemExit) as error:
            developer.main()
        assert error.value.code == 0
        help_text = capsys.readouterr().out
        assert all(option in help_text for option in present)
        assert all(option not in help_text for option in absent)
