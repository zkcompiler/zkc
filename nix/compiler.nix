{
  lib,
  stdenv,
  cmake,
  ninja,
  ccache,
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
  # Nix normally seeds the compiler with the changing package output path.
  # Keep this reproducibility seed stable for one toolchain so an unrelated
  # source edit does not invalidate every cached translation unit. Flags,
  # source, headers and the compiler itself still participate in cache keys.
  NIX_OUTPATH_USED_AS_RANDOM_SEED = stdenv.cc;
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
  postBuild = ''
    if [[ -f "$TMPDIR/ccache-stats.log" ]]; then
      CCACHE_STATSLOG="$TMPDIR/ccache-stats.log" ${ccache}/bin/ccache --show-log-stats
    fi
  '';
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
