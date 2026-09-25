# Environment policy shared by development shells and isolated checks.
# Native manifests/presets still own dependency versions and build profiles.
{
  pkgs,
  llvm,
  python,
}:
{
  toolchain = {
    CC = "${llvm.clang}/bin/clang";
    CXX = "${llvm.clang}/bin/clang++";
    MLIR_DIR = "${pkgs.lib.getDev llvm.mlir}/lib/cmake/mlir";
    LLVM_CONFIG = "${pkgs.lib.getDev llvm.llvm}/bin/llvm-config";
    UV_PYTHON = python.interpreter;
    UV_PYTHON_DOWNLOADS = "never";
    TZDIR = "${pkgs.tzdata}/share/zoneinfo";
  };

  # Defaults are applied when entering the development shell. Each native
  # setting remains independently overridable, including for a single command.
  development = ''
    export CMAKE_BUILD_PARALLEL_LEVEL="''${CMAKE_BUILD_PARALLEL_LEVEL:-4}"
    export CTEST_PARALLEL_LEVEL="''${CTEST_PARALLEL_LEVEL:-4}"
    export CARGO_BUILD_JOBS="''${CARGO_BUILD_JOBS:-4}"
    export RUST_TEST_THREADS="''${RUST_TEST_THREADS:-4}"
    export LEAN_NUM_THREADS="''${LEAN_NUM_THREADS:-4}"
    export PYTEST_XDIST_AUTO_NUM_WORKERS="''${PYTEST_XDIST_AUTO_NUM_WORKERS:-4}"
  '';

  # Nix check derivations do not inherit devShell settings. A zero core budget
  # means unspecified; use one worker rather than multiplying host concurrency.
  checks = ''
    zkc_check_cores="''${NIX_BUILD_CORES:-1}"
    if [ "$zkc_check_cores" = 0 ]; then zkc_check_cores=1; fi
    export CMAKE_BUILD_PARALLEL_LEVEL="$zkc_check_cores"
    export CTEST_PARALLEL_LEVEL="$zkc_check_cores"
    export CARGO_BUILD_JOBS="$zkc_check_cores"
    export RUST_TEST_THREADS="$zkc_check_cores"
    export LEAN_NUM_THREADS="$zkc_check_cores"
    export PYTEST_XDIST_AUTO_NUM_WORKERS="$zkc_check_cores"
  '';

  # The only public inputs selecting built executables across language suites.
  outputs =
    {
      compilerBin,
      nativeBin,
      leanBin,
    }:
    {
      ZKC_COMPILER_BIN = compilerBin;
      ZKC_NATIVE_BIN = nativeBin;
      ZKC_LEAN_BIN = leanBin;
    };
}
