{
  lib,
  stdenv,
  cmake,
  ninja,
  python3,
  llvm,
  utf8proc,
  source,
  withTests ? false,
}:
stdenv.mkDerivation {
  pname = "zkc-compiler";
  version = "0.0.0";
  src = source;
  outputs = [ "out" ] ++ lib.optional withTests "testSupport";
  nativeBuildInputs = [
    cmake
    ninja
    python3
    llvm.tblgen
  ];
  buildInputs = [
    llvm.mlir
    llvm.llvm.dev
  ];
  # Installed Language consumers need this exact NFC package for both static
  # and shared builds; propagate its CMake discovery path to downstream SDKs.
  propagatedBuildInputs = [ utf8proc ];
  preConfigure = ''
    cmakeDir="$PWD/compiler"
  '';
  cmakeFlags = [
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
    "-DMLIR_TABLEGEN_EXE=${llvm.tblgen}/bin/mlir-tblgen"
    "-DBUILD_TESTING=${if withTests then "ON" else "OFF"}"
  ];
  # Full validation and integration helpers share checks.compiler.
  doCheck = withTests;
  postInstall = lib.optionalString withTests ''
    mkdir -p "$testSupport/bin/test"
    ln -s "$out/bin/zkc-compile" "$out/bin/zkc-opt" "$out/bin/zkc-tblgen" "$testSupport/bin/"
    find test -maxdepth 1 -type f -executable -exec cp {} "$testSupport/bin/test/" \;
  '';
  meta = {
    description = "Protocol compiler and installed C++ SDK";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc-compile";
  };
}
