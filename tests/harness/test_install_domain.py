"""Installed-domain orchestration without compiling project components."""

import json
from pathlib import Path
import os
import shutil
import subprocess
import sys

import pytest

from harness import fake_command, load
from install_domain import check_cache, check_consumers
from workspace import ROOT, native_configuration


def cache(build, profile, selected, *, domain=False, changes=None):
    build.mkdir()
    entries = selected | {
        "CMAKE_HOME_DIRECTORY": str(ROOT / "compiler"), "CMAKE_GENERATOR": "Ninja",
        "CMAKE_BUILD_TYPE": "RelWithDebInfo" if profile == "dev" else "Release",
        "BUILD_SHARED_LIBS": "ON" if profile == "shared" else "OFF",
        "ZKC_ENABLE_ASSERTIONS": "ON" if profile == "dev" else "OFF",
        "ZKC_ENABLE_SANITIZERS": "OFF", "BUILD_TESTING": "OFF" if domain else "ON",
        "ZKC_CONTRIBUTION_FILES": str(ROOT / "compiler/examples/domain/contribution.cmake") if domain else "",
    }
    entries.update(changes or {})
    (build / "CMakeCache.txt").write_text("".join(f"{k}:STRING={v}\n" for k, v in entries.items()))


@pytest.mark.parametrize("fragment", ["BuiltinHeaders.h.inc", "BuiltinDialects.inc",
                                     "ContributionHeaders.h.inc", "ContributionDialects.inc"])
@pytest.mark.parametrize("owner", ["base", "domain"])
def test_private_registration_fragments_refused_before_consumer_build(tmp_path, fragment, owner):
    prefixes = {name: tmp_path / name for name in ("base", "domain")}
    for prefix in prefixes.values():
        package = prefix / "lib/cmake/ZkcCompiler"
        package.mkdir(parents=True)
        (package / "ZkcCompilerConfig.cmake").write_text("# installed\n")
    private = prefixes[owner] / "include/zkc/Dialect" / fragment
    private.parent.mkdir(parents=True)
    private.write_text("// unexpected private fragment\n")
    calls = []
    with pytest.raises(ValueError, match="private registration fragment was installed"):
        check_consumers(prefixes, tmp_path / "unused", {}, lambda *args, **kw: calls.append(args))
    assert not calls


@pytest.fixture
def driver(monkeypatch, tmp_path, native_config):
    developer = load("developer", "scripts/develop.py")
    calls = []
    controls = {"missing_package": False, "inventory": None, "junit": None,
                "identities": None, "fail": False, "execution": False}

    def run(arguments, **kwargs):
        args = list(map(str, arguments))
        calls.append(args)
        if controls["fail"]:
            raise subprocess.CalledProcessError(7, args)
        if args[:2] == ["cmake", "--install"] and not controls["missing_package"]:
            package = Path(args[-1]) / "lib/cmake/ZkcCompiler"
            package.mkdir(parents=True)
            (package / "ZkcCompilerConfig.cmake").write_text("# fake installed config\n")
        if args[-1] == "--checked-identities":
            kwargs["stdout"].write(json.dumps(controls["identities"] if controls["identities"] is not None
                                              else [str(Path(args[0]).parent.name)]))
        if args[0] == "ctest":
            names = ["installed-envelope", "installed-declarations"]
            if Path(args[2]).name == "domain-consumer":
                names.append("installed-specialization")
                if controls["execution"]:
                    names.append("installed-execution")
            if "--show-only=json-v1" in args:
                kwargs["stdout"].write(json.dumps({"tests": [
                    {"name": n} for n in (controls["inventory"] if controls["inventory"] is not None else names)
                ]}))
            else:
                xml = controls["junit"] or ("<testsuite>" + "".join(
                    f'<testcase name="{name}"/>' for name in names) + "</testsuite>")
                Path(args[-1]).write_text(xml)

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setitem(sys.modules, "develop", developer)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))

    def invoke(*args):
        monkeypatch.setattr(sys, "argv", ["develop.py", "install-domain", *map(str, args)])
        developer.main()

    return invoke, calls, controls


@pytest.mark.parametrize("profile", ["release", "dev", "shared"])
@pytest.mark.parametrize("reuse", [False, True])
def test_both_prefixes_and_exact_ctest_evidence(driver, tmp_path, profile, reuse):
    invoke, calls, _ = driver
    args = ["--profile", profile]
    if reuse:
        for name in ("base", "domain"):
            cache(tmp_path / name, profile, native_configuration(), domain=name == "domain")
            args += [f"--{name}-build", tmp_path / name]
        args += ["--skip-build"]
    for number in range(2):
        output = tmp_path / f"output-{number}"
        invoke(*args, "--output", output)
        record = json.loads((output / "commands.json").read_text())
        assert record["profile"] == profile and record["skip_build"] == reuse
        assert all(c["status"] == "pass" for c in record["commands"])
        assert [len(json.loads((output / f"{name}-tests.json").read_text())["tests"])
                for name in ("base", "domain")] == [2, 3]
        assert (output / "base-ctest.xml").is_file() and (output / "domain-ctest.xml").is_file()
    configurations = [c for c in calls if "--preset" in c]
    assert len(configurations) == (0 if reuse else 4)
    assert all("-DBUILD_TESTING=OFF" in c for c in configurations)
    assert all(c[c.index("--preset") + 1] == profile for c in configurations)
    if not reuse:
        assert all(f"-D{k}={v}" in c for c in configurations for k, v in native_configuration().items())
        assert [next(a for a in c if a.startswith("-DZKC_CONTRIBUTION_FILES=")) for c in configurations[:2]] == [
            "-DZKC_CONTRIBUTION_FILES=", f"-DZKC_CONTRIBUTION_FILES={ROOT}/compiler/examples/domain/contribution.cmake"]
    builds = [c for c in calls if c[:2] == ["cmake", "--build"]]
    assert len(builds) == (4 if reuse else 8)
    assert all(c[-3:] == ["zkc-compile", "zkc-opt", "zkc-tblgen"] for c in builds if "--target" in c)
    consumers = [c for c in calls if "-S" in c]
    assert [next(a for a in c if a.startswith("-DEXPECT_ENVELOPE=")) for c in consumers] == [
        "-DEXPECT_ENVELOPE=OFF", "-DEXPECT_ENVELOPE=ON"] * 2
    assert all("--no-tests=error" in c for c in calls if "--output-junit" in c)
    ownership = [c for c in calls if c[-1].endswith("component_dependencies.py")]
    assert len(ownership) == 4
    assert all(c[:3] == ["cmake", "-E", "env"] for c in ownership)
    assert all(c[3].startswith("ZKC_CTEST_COMPONENTS=") for c in ownership)


@pytest.mark.parametrize("key,value", [
    ("CMAKE_HOME_DIRECTORY", "/wrong-source"), ("CMAKE_GENERATOR", "Unix Makefiles"),
    ("CMAKE_CXX_COMPILER", "/wrong-compiler"), ("CMAKE_MAKE_PROGRAM", "/wrong-ninja"),
    ("MLIR_DIR", "/wrong-mlir"), ("BUILD_SHARED_LIBS", "ON"),
    ("CMAKE_BUILD_TYPE", "Debug"), ("ZKC_ENABLE_ASSERTIONS", "ON"),
    ("ZKC_ENABLE_SANITIZERS", "ON"), ("ZKC_CONTRIBUTION_FILES", ""), ("BUILD_TESTING", "ON"),
])
def test_incompatible_cache_refused_before_any_command(driver, tmp_path, key, value):
    invoke, calls, _ = driver
    cache(tmp_path / "domain", "release", native_configuration(), domain=True, changes={key: value})
    with pytest.raises(ValueError, match=key):
        invoke("--domain-build", tmp_path / "domain")
    assert not calls


@pytest.mark.parametrize("kind", ["directory", "file", "symlink", "dangling"])
def test_existing_output_is_never_overwritten(driver, tmp_path, kind):
    invoke, calls, _ = driver
    output = tmp_path / "output"
    if kind == "directory":
        output.mkdir()
    elif kind == "file":
        output.write_text("retained")
    else:
        output.symlink_to(tmp_path if kind == "symlink" else tmp_path / "missing")
    with pytest.raises(ValueError, match="refusing existing output"):
        invoke("--output", output)
    assert not calls


@pytest.mark.parametrize("args,match", [
    (["--skip-build"], "requires both"),
    (["--base-build", "same", "--domain-build", "same"], "non-nested"),
    (["--profile", "sanitize"], "supports release"),
])
def test_invalid_selection_refused(driver, args, match):
    invoke, calls, _ = driver
    with pytest.raises(ValueError, match=match):
        invoke(*args)
    assert not calls


@pytest.mark.parametrize("failure", ["missing_package", "inventory", "junit", "fail"])
def test_failures_keep_evidence_and_fail_the_run(driver, tmp_path, failure):
    invoke, calls, controls = driver
    controls[failure] = {"missing_package": True, "inventory": [], "fail": True,
                         "junit": '<testsuite><testcase name="installed-envelope"><skipped/></testcase>'
                                  '<testcase name="installed-declarations"/></testsuite>'}[failure]
    with pytest.raises((ValueError, subprocess.CalledProcessError)):
        invoke()
    record, = (tmp_path / "reports/runs").glob("*/run.json")
    assert json.loads(record.read_text())["status"] == "failed"
    assert (record.parent / "install-domain/commands.json").is_file()
    if failure == "missing_package":
        assert not any("-S" in c for c in calls)


def test_rebuild_preserves_base_testing_and_rejects_nested_output(driver, tmp_path):
    invoke, calls, _ = driver
    for name in ("base", "domain"):
        cache(tmp_path / name, "release", native_configuration(), domain=name == "domain")
    args = ["--base-build", tmp_path / "base", "--domain-build", tmp_path / "domain"]
    with pytest.raises(ValueError, match="non-nested"):
        invoke(*args, "--output", tmp_path / "base/install")
    assert not calls
    invoke(*args)
    base_config = next(c for c in calls if "--preset" in c)
    assert "-DBUILD_TESTING=OFF" not in base_config


def test_absent_static_linkage_cache_entry_is_supported(tmp_path, native_config):
    build = tmp_path / "base"
    selected = native_configuration()
    cache(build, "release", selected)
    path = build / "CMakeCache.txt"
    path.write_text("\n".join(line for line in path.read_text().splitlines()
                              if not line.startswith("BUILD_SHARED_LIBS:")))
    check_cache(build, "release", selected, "")


@pytest.mark.parametrize("identities", [[], ["same-key"], [1]])
def test_missing_or_unchanged_captured_environment_refused(driver, identities):
    invoke, _, controls = driver
    controls["identities"] = identities
    with pytest.raises(ValueError, match="identit"):
        invoke()


def test_installed_prefix_entry_point_uses_same_consumer_checks(driver, monkeypatch, tmp_path):
    _, calls, _ = driver
    module = load("installed_domain", "scripts/install_domain.py")
    monkeypatch.chdir(tmp_path)
    args = ["install_domain.py", "--output", "evidence"]
    for name in ("base", "domain"):
        prefix = tmp_path / name
        package = prefix / "lib/cmake/ZkcCompiler"
        package.mkdir(parents=True)
        (package / "ZkcCompilerConfig.cmake").write_text("# installed\n")
        args += [f"--{name}-prefix", str(prefix)]
    monkeypatch.setattr(sys, "argv", args)
    module.main()
    assert (tmp_path / "evidence/base-ctest.xml").is_file()
    assert len([c for c in calls if "--output-junit" in c]) == 2
    assert not any("--install" in c or "--preset" in c for c in calls)


@pytest.mark.skipif(not shutil.which("just"), reason="just is not available")
def test_just_forwards_explicit_build_arguments_without_prerequisites(monkeypatch, tmp_path):
    fake_command(tmp_path, "python3")
    record = tmp_path / "commands.jsonl"
    monkeypatch.setenv("COMMAND_RECORD", str(record))
    monkeypatch.setenv("PATH", str(tmp_path) + os.pathsep + os.environ["PATH"])
    arguments = ["--base-build", "build/base with spaces", "--domain-build", "build/domain", "--skip-build"]
    subprocess.run(["just", "--justfile", str(ROOT / "justfile"), "test-install-domain", "shared", *arguments],
                   check=True, capture_output=True, text=True, timeout=10)
    commands = [json.loads(line) for line in record.read_text().splitlines()]
    assert len(commands) == 1
    assert commands[0]["arguments"] == ["scripts/develop.py", "install-domain", "--profile", "shared", *arguments]


@pytest.mark.parametrize("kind", ["empty", "symlink", "missing"])
def test_unconfigured_or_symlink_build_is_refused(driver, tmp_path, kind):
    invoke, calls, _ = driver
    base = tmp_path / "base"
    if kind == "empty":
        base.mkdir()
    elif kind == "symlink":
        base.symlink_to(tmp_path / "absent")
    args = ["--base-build", base]
    if kind == "missing":
        args += ["--domain-build", tmp_path / "domain", "--skip-build"]
    with pytest.raises(ValueError, match="CMakeCache|symlink"):
        invoke(*args)
    assert not calls


def test_optional_execution_is_part_of_exact_ctest_inventory(driver, tmp_path):
    invoke, calls, controls = driver
    controls["execution"] = True
    invoke("--runtime", sys.executable, "--checker", sys.executable)
    configurations = [call for call in calls if "-DEXPECT_ENVELOPE=ON" in call]
    assert len(configurations) == 1
    assert f"-DZKC_DOMAIN_RUNTIME={Path(sys.executable).resolve()}" in configurations[0]
    assert f"-DZKC_DOMAIN_CHECKER={Path(sys.executable).resolve()}" in configurations[0]


@pytest.mark.parametrize("arguments", [
    ["--runtime", sys.executable], ["--checker", sys.executable],
    ["--runtime", "/absent/zkc", "--checker", sys.executable],
])
def test_invalid_execution_tools_refuse_before_building(driver, arguments):
    invoke, calls, _ = driver
    with pytest.raises(ValueError, match="independent execution"):
        invoke(*arguments)
    assert not calls
