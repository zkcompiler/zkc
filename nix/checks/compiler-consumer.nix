{
  stdenv,
  cmake,
  ninja,
  compiler,
  utf8proc,
  source,
  llvm,
  lib,
}:
stdenv.mkDerivation {
  name = "zkc-compiler-consumer";
  src = source;
  sourceRoot = "${source.name}/common/tests/consumer";
  nativeBuildInputs = [
    cmake
    ninja
  ];
  buildInputs = [
    utf8proc
    llvm.mlir
    llvm.llvm.dev
  ];
  # Keep the installed SDK's include path stable when its Nix output changes.
  # Header contents still participate in ccache's dependency validation, and
  # linking always uses this build's installed libraries.
  preConfigure = ''
    cp -R ${compiler} "$TMPDIR/zkc-sdk"
    cmakeFlagsArray+=("-DZkcCompiler_DIR=$TMPDIR/zkc-sdk/lib/cmake/ZkcCompiler")
  '';
  cmakeFlags = [
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
  ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ctest --output-on-failure --no-tests=error --parallel "$NIX_BUILD_CORES"
    runHook postCheck
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    printf 'installed compiler consumer passed\n' > "$out/result"
    runHook postInstall
  '';
}
