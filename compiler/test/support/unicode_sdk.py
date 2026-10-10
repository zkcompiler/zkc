"""Exercise the production Names SDK exports with exact NFC dependency discovery.

Builds only Names and its focused tests. The full installed compiler is checked
by the repository's separate installation scope.
"""

import argparse
from pathlib import Path
import subprocess


def run(*args):
    subprocess.run([str(arg) for arg in args], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--llvm-dir", required=True)
    parser.add_argument("--utf8proc-dir", required=True)
    parser.add_argument("--c-compiler", required=True)
    parser.add_argument("--cxx-compiler", required=True)
    args = parser.parse_args()
    source = Path(__file__).resolve().parents[1] / "names"
    common = [f"-DLLVM_DIR={args.llvm_dir}", f"-Dutf8proc_DIR={args.utf8proc_dir}",
              f"-DCMAKE_C_COMPILER={args.c_compiler}",
              f"-DCMAKE_CXX_COMPILER={args.cxx_compiler}"]
    wrong = args.output / "wrong-utf8proc"
    wrong.mkdir(parents=True, exist_ok=True)
    (wrong / "utf8proc-config-version.cmake").write_text(
        'set(PACKAGE_VERSION "2.11.0")\nset(PACKAGE_VERSION_COMPATIBLE FALSE)\n'
        'set(PACKAGE_VERSION_EXACT FALSE)\n')
    (wrong / "utf8proc-config.cmake").write_text(
        'message(FATAL_ERROR "wrong-version config must never execute")\n')
    for linkage in ("static", "shared"):
        output = args.output / linkage
        prefix = output / "install"
        run("cmake", "-S", source, "-B", output / "build", "-G", "Ninja", *common,
            "-DCMAKE_BUILD_TYPE=Release", f"-DCMAKE_INSTALL_PREFIX={prefix}",
            f"-DBUILD_SHARED_LIBS={'ON' if linkage == 'shared' else 'OFF'}")
        run("cmake", "--build", output / "build", "--parallel", "4")
        run("ctest", "--test-dir", output / "build", "--output-on-failure")
        run("cmake", "--install", output / "build")
        package = [f"-DZkcCompiler_DIR={prefix}/lib/cmake/ZkcCompiler"]
        for scenario, flags in (
            ("available", []),
            ("missing", ["-DZKC_EXPECT_MISSING=ON", "-DCMAKE_DISABLE_FIND_PACKAGE_utf8proc=TRUE"]),
            ("wrong-directory", ["-DZKC_EXPECT_MISSING=ON", f"-Dutf8proc_DIR={wrong}"]),
            ("preloaded-wrong", ["-DZKC_EXPECT_MISSING=ON", "-DZKC_PRELOAD_WRONG_UTF8PROC=ON"]),
        ):
            build = output / scenario
            run("cmake", "-S", source / "consumer", "-B", build, "-G", "Ninja",
                *common, *package, *flags)
            if scenario == "available":
                run("cmake", "--build", build, "--parallel", "4")
                run("ctest", "--test-dir", build, "--output-on-failure")
    print("Static/shared Names exports and six dependency refusal scenarios passed")


if __name__ == "__main__":
    main()
