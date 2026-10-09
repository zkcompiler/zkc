"""Opt-in installed envelope/base consumer checks, with retained CTest evidence."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET

from processes import Interrupted
from workspace import ROOT, checkout_path, compiler_directory, native_configuration, reports_root


def reserve(path):
    # Check before resolving so even dangling symlinks are refused.
    if os.path.lexists(path):
        raise ValueError(f"refusing existing output directory: {path}")
    path.mkdir(parents=True, exist_ok=False)


def check_consumers(prefixes, output, selected, run):
    for name, prefix in prefixes.items():
        package = prefix / "lib/cmake/ZkcCompiler"
        if not (package / "ZkcCompilerConfig.cmake").is_file():
            raise ValueError(f"install did not produce {package / 'ZkcCompilerConfig.cmake'}")
        for fragment in ("BuiltinHeaders.h.inc", "BuiltinDialects.inc",
                         "ContributionHeaders.h.inc", "ContributionDialects.inc"):
            path = prefix / "include/zkc/Dialect" / fragment
            if os.path.lexists(path):
                raise ValueError(f"private registration fragment was installed: {path}")
    for name, prefix in prefixes.items():
        consumer = output / f"{name}-consumer"
        reserve(consumer)
        expected = ["installed-envelope", "installed-declarations"]
        run(["cmake", "-S", ROOT / "compiler/examples/domain/consumer", "-B", consumer,
             "-G", "Ninja", f"-DZkcCompiler_DIR={prefix}/lib/cmake/ZkcCompiler",
             f"-DEXPECT_ENVELOPE={'ON' if name == 'domain' else 'OFF'}",
             *[f"-D{key}={value}" for key, value in selected.items()]])
        run(["cmake", "--build", consumer])
        inventory = output / f"{name}-tests.json"
        with inventory.open("w") as stream:
            run(["ctest", "--test-dir", consumer, "--show-only=json-v1"], stdout=stream)
        names = [test["name"] for test in json.loads(inventory.read_text())["tests"]]
        if sorted(names) != sorted(expected):
            raise ValueError(f"{name}: expected CTest cases {expected}, got {names}")
        junit = output / f"{name}-ctest.xml"
        run(["ctest", "--test-dir", consumer, "--output-on-failure", "--no-tests=error",
             "--output-junit", junit])
        cases = ET.parse(junit).getroot().findall(".//testcase")
        if (sorted(case.get("name") for case in cases) != sorted(expected)
                or any(case.find(tag) is not None for case in cases
                       for tag in ("skipped", "failure", "error"))):
            raise ValueError(f"{name}: CTest evidence does not contain {len(expected)} passing cases")


def recorded_run(output, run, details):
    evidence = details | {"commands": []}

    def invoke(arguments, **kwargs):
        command = {"argv": list(map(str, arguments)), "cwd": str(kwargs.get("cwd", ROOT)),
                   "status": "running"}
        evidence["commands"].append(command)
        path = output / "commands.json"
        path.write_text(json.dumps(evidence, indent=2) + "\n")
        try:
            run(arguments, **kwargs)
            command["status"] = "pass"
        except BaseException:
            command["status"] = "failed"
            raise
        finally:
            path.write_text(json.dumps(evidence, indent=2) + "\n")

    return invoke


def check_cache(build, profile, selected, contribution):
    cache_file = build / "CMakeCache.txt"
    if not cache_file.is_file():
        raise ValueError(f"existing build requires CMakeCache.txt: {build}")
    cache = {}
    for line in cache_file.read_text().splitlines():
        if ":" in line and "=" in line and not line.startswith(("#", "//")):
            key, value = line.split("=", 1)
            cache[key.split(":", 1)[0]] = value
    expected = selected | {
        "CMAKE_HOME_DIRECTORY": str(ROOT / "compiler"), "CMAKE_GENERATOR": "Ninja",
        "CMAKE_BUILD_TYPE": "RelWithDebInfo" if profile == "dev" else "Release",
        "ZKC_CONTRIBUTION_FILES": contribution,
        "BUILD_SHARED_LIBS": "ON" if profile == "shared" else "OFF",
        "ZKC_ENABLE_ASSERTIONS": "ON" if profile == "dev" else "OFF",
        "ZKC_ENABLE_SANITIZERS": "OFF",
    }
    if contribution:
        expected["BUILD_TESTING"] = "OFF"
    booleans = {"BUILD_SHARED_LIBS", "ZKC_ENABLE_ASSERTIONS", "ZKC_ENABLE_SANITIZERS", "BUILD_TESTING"}
    for key, value in expected.items():
        actual = cache.get(key, "OFF" if key in booleans else "")
        if key in booleans:
            is_false = (actual.upper() in {"", "OFF", "NO", "FALSE", "N", "0", "IGNORE", "NOTFOUND"}
                        or actual.upper().endswith("-NOTFOUND"))
            actual = "OFF" if is_false else "ON"
        if actual != value:
            raise ValueError(f"incompatible build {build}: {key}={actual!r}, expected {value!r}; use a fresh directory")


def install_domain(args, run):
    compiler_directory(args.profile)  # Keep profile validation owned by the presets.
    if args.profile not in {"release", "dev", "shared"}:
        raise ValueError("install-domain supports release, dev and shared profiles")
    selected = native_configuration()
    if args.skip_build and not (args.base_build and args.domain_build):
        raise ValueError("--skip-build requires both --base-build and --domain-build")
    output = Path(args.output).absolute() if args.output else reports_root() / "install-domain"
    builds = {name: checkout_path(value) if value else output / f"{name}-build"
              for name, value in (("base", args.base_build), ("domain", args.domain_build))}
    contribution = str(ROOT / "compiler/examples/domain/contribution.cmake")
    fresh_builds = set()
    # Validate both sides before installing or reconfiguring either one.
    base, domain = builds.values()
    if base == domain or base in domain.parents or domain in base.parents:
        raise ValueError("base and domain builds must be separate, non-nested directories")
    for name, build in builds.items():
        explicit = getattr(args, f"{name}_build")
        if explicit and (build == output.resolve() or build in output.resolve().parents
                         or output.resolve() in build.parents):
            raise ValueError("explicit builds and output must be separate, non-nested directories")
        supplied = Path(explicit) if explicit else build
        if not supplied.is_absolute():
            supplied = ROOT / supplied
        if supplied.is_symlink():
            raise ValueError(f"refusing build directory symlink: {supplied}")
        if build.exists() or args.skip_build:
            check_cache(build, args.profile, selected, contribution if name == "domain" else "")
        else:
            fresh_builds.add(name)
    reserve(output)
    print(f"Installed-domain evidence: {output}", flush=True)
    prefixes = {name: output / f"{name}-prefix" for name in builds}
    for name, build in builds.items():
        reserve(prefixes[name])
        if name in fresh_builds:
            reserve(build)
    invoke = recorded_run(output, run, {
        "profile": args.profile, "skip_build": args.skip_build, "selected": selected,
        "builds": {name: str(path) for name, path in builds.items()},
        "prefixes": {name: str(path) for name, path in prefixes.items()},
    })
    for name, build in builds.items():
        if not args.skip_build:
            # Do not change BUILD_TESTING on a reused base build. Build only
            # installed tools and their dependencies, never the full test graph.
            testing = ["-DBUILD_TESTING=OFF"] if name in fresh_builds or name == "domain" else []
            invoke(["cmake", "--preset", args.profile, "-B", build,
                    *[f"-D{key}={value}" for key, value in selected.items()], *testing,
                    f"-DZKC_CONTRIBUTION_FILES={contribution if name == 'domain' else ''}"],
                   cwd=ROOT / "compiler")
            invoke(["cmake", "--build", build, "--target", "zkc-compile", "zkc-opt", "zkc-tblgen"])
        # This structural check needs generated headers, not BUILD_TESTING or
        # the full compiler test graph. Exercise the actual extended ownership.
        invoke(["cmake", "-E", "env",
                f"ZKC_CTEST_COMPONENTS={build / 'component-dependencies.txt'}",
                sys.executable, ROOT / "compiler/test/component_dependencies.py"])
        invoke(["cmake", "--install", build, "--prefix", prefixes[name]])
    check_consumers(prefixes, output, selected, invoke)


def main():
    # Nix supplies already installed immutable packages; use the same consumer
    # runner without rebuilding or copying their compiler libraries.
    from develop import run

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-prefix", required=True, type=Path)
    parser.add_argument("--domain-prefix", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    selected = native_configuration()
    output = args.output.absolute()
    reserve(output)
    prefixes = {"base": args.base_prefix.resolve(), "domain": args.domain_prefix.resolve()}
    invoke = recorded_run(output, run, {"prefixes": {k: str(v) for k, v in prefixes.items()}})
    check_consumers(prefixes, output, selected, invoke)


if __name__ == "__main__":
    try:
        main()
    except Interrupted as error:
        sys.exit(128 + error.signum)
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode if error.returncode >= 0 else 128 - error.returncode)
    except (ValueError, OSError, ET.ParseError) as error:
        sys.exit(str(error))
