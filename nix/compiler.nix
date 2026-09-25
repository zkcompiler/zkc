{
  lib,
  stdenv,
  cmake,
  ninja,
  python3,
  llvm,
  source,
}:
stdenv.mkDerivation {
  pname = "zkc-compiler";
  version = "0.1.0";
  src = source;
  outputs = [
    "out"
    "testSupport"
  ];
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
  preConfigure = ''
    cmakeDir="$PWD/compiler"
  '';
  cmakeFlags = [
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
    "-DMLIR_TABLEGEN_EXE=${llvm.tblgen}/bin/mlir-tblgen"
    "-DBUILD_TESTING=ON"
  ];
  doCheck = true;
  postInstall = ''
    mkdir -p "$testSupport/bin/examples/service" "$testSupport/bin/test"
    ln -s "$out/bin/zkc-compile" "$out/bin/zkc-opt" "$testSupport/bin/"
    cp zkc-source-bench "$testSupport/bin/"
    find examples/service -maxdepth 1 -type f -executable -exec cp {} "$testSupport/bin/examples/service/" \;
    find test -maxdepth 1 -type f -executable -exec cp {} "$testSupport/bin/test/" \;
  '';
  meta = {
    description = "Protocol compiler and installed C++ SDK";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc-compile";
  };
}
