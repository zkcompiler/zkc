"""Install an existing compiler build and validate an independent SDK consumer."""

import os
from pathlib import Path

from workspace import ROOT, compiler_directory, native_configuration, reports_root


def check_install(args, run):
    selected = native_configuration()
    prefix = Path(args.output).resolve() if args.output else reports_root() / "installed"
    # Refuse an existing prefix, including a dangling symlink, before running
    # install. Reserve it exclusively so simultaneous callers cannot share it.
    if args.output and os.path.lexists(Path(args.output).absolute()):
        raise ValueError(f"refusing existing install prefix: {args.output}")
    prefix.mkdir(parents=True, exist_ok=False)
    consumer = reports_root() / "consumer"
    run(["cmake", "--install", compiler_directory(args.profile), "--prefix", prefix])
    package = prefix / "lib/cmake/ZkcCompiler"
    if not (package / "ZkcCompilerConfig.cmake").is_file():
        # Otherwise find_package can ignore the missing hint and discover
        # a stale installation through CMAKE_PREFIX_PATH or its registry.
        raise ValueError(f"install did not produce {package / 'ZkcCompilerConfig.cmake'}")
    for name in ("zkc-compile", "zkc-opt"):
        for option in ("--help", "--version"):
            run([prefix / "bin" / name, option])
    run(["cmake", "-S", ROOT / "common/tests/consumer", "-B", consumer,
         "-G", "Ninja", f"-DZkcCompiler_DIR={package}",
         *[f"-D{key}={value}" for key, value in selected.items()]])
    run(["cmake", "--build", consumer])
    run(["ctest", "--test-dir", consumer, "--output-on-failure"])
