"""Install an existing compiler build and validate an independent SDK consumer."""

import os
import shutil
from pathlib import Path

from workspace import ROOT, compiler_directory, native_configuration, reports_root


def check_common_compiler(prefix, selected, run):
    """Compile/link actual logical APIs with all machine-target files absent."""
    common = reports_root() / "common-compiler-only"
    shutil.copytree(prefix, common, symlinks=True)
    shutil.rmtree(common / "bin")
    for relative in ("Target", "Dialect/Evm"):
        shutil.rmtree(common / "include/zkc" / relative)
    for relative in ("Compiler/NativeCompilation.h", "Compiler/NativeLanguage.h",
                     "Compiler/Run.h", "Compiler/Evm.h",
                     "Transforms/Protocol.h", "Transforms/PipelineOptions.h"):
        (common / "include/zkc" / relative).unlink()
    for component in ("CpuTarget", "EvmTarget", "Driver", "Tools"):
        for path in (common / "lib").glob(f"libZkc{component}.*"):
            path.unlink()
        for path in (common / "lib/cmake/ZkcCompiler").glob(f"Zkc{component}Targets*.cmake"):
            path.unlink()
    consumer = reports_root() / "common-consumer"
    run(["cmake", "-S", ROOT / "common/tests/consumer/common-only", "-B", consumer,
         "-G", "Ninja", f"-DZkcCompiler_DIR={common / 'lib/cmake/ZkcCompiler'}",
         *[f"-D{key}={value}" for key, value in selected.items()]])
    run(["cmake", "--build", consumer, "--parallel", "2"])
    run(["ctest", "--test-dir", consumer, "--output-on-failure", "--no-tests=error"])


def check_evm_compiler(prefix, selected, run):
    """Compile an EVM proof with CPU libraries, headers and exports absent."""
    isolated = reports_root() / "evm-compiler-only"
    shutil.copytree(prefix, isolated, symlinks=True)
    shutil.rmtree(isolated / "bin")
    shutil.rmtree(isolated / "include/zkc/Target/Cpu")
    for relative in ("Compiler/NativeCompilation.h", "Compiler/NativeLanguage.h",
                     "Compiler/Run.h", "Transforms/Protocol.h", "Transforms/PipelineOptions.h"):
        (isolated / "include/zkc" / relative).unlink()
    for component in ("CpuTarget", "Driver", "Tools"):
        for path in (isolated / "lib").glob(f"libZkc{component}.*"):
            path.unlink()
        for path in (isolated / "lib/cmake/ZkcCompiler").glob(f"Zkc{component}Targets*.cmake"):
            path.unlink()
    consumer = reports_root() / "evm-consumer"
    run(["cmake", "-S", ROOT / "common/tests/consumer/evm-only", "-B", consumer,
         "-G", "Ninja", f"-DZkcCompiler_DIR={isolated / 'lib/cmake/ZkcCompiler'}",
         *[f"-D{key}={value}" for key, value in selected.items()]])
    run(["cmake", "--build", consumer, "--parallel", "2"])
    run(["ctest", "--test-dir", consumer, "--output-on-failure", "--no-tests=error"])


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
    check_common_compiler(prefix, selected, run)
    check_evm_compiler(prefix, selected, run)
    run(["cmake", "-S", ROOT / "common/tests/consumer", "-B", consumer,
         "-G", "Ninja", f"-DZkcCompiler_DIR={package}",
         *[f"-D{key}={value}" for key, value in selected.items()]])
    run(["cmake", "--build", consumer, "--parallel", "2"])
    run(["ctest", "--test-dir", consumer, "--output-on-failure"])
