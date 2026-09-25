{
  stdenv,
  cmake,
  ninja,
  compiler,
  llvm,
  lib,
}:
stdenv.mkDerivation {
  name = "zkc-compiler-consumer";
  src = ../../tests/consumer;
  nativeBuildInputs = [
    cmake
    ninja
  ];
  buildInputs = [
    compiler
    llvm.mlir
    llvm.llvm.dev
  ];
  cmakeFlags = [
    "-DZkcCompiler_DIR=${compiler}/lib/cmake/ZkcCompiler"
    "-DZKC_SERVICE_SOURCE=${../../compiler/examples/service}"
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
  ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ctest --output-on-failure
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    printf 'installed compiler consumer passed\n' > "$out/result"
  '';
}
