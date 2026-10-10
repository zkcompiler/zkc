{
  stdenv,
  cmake,
  ninja,
  python3,
  llvm,
  utf8proc,
  lib,
  source,
  base,
  domain,
  shared,
}:
stdenv.mkDerivation {
  name = "zkc-installed-domain-${if shared then "shared" else "static"}";
  src = source;
  nativeBuildInputs = [
    cmake
    ninja
    python3
  ];
  buildInputs = [
    llvm.mlir
    llvm.llvm.dev
    utf8proc
  ];
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  MLIR_DIR = "${lib.getDev llvm.mlir}/lib/cmake/mlir";
  checkPhase = ''
    runHook preCheck
    export CMAKE_BUILD_PARALLEL_LEVEL="$NIX_BUILD_CORES"
    ${python3.interpreter} common/tests/check_domain.py \
      --base-prefix ${base} --domain-prefix ${domain} \
      --output "$TMPDIR/domain-check"
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    cp "$TMPDIR/domain-check/"*.json "$TMPDIR/domain-check/"*.xml "$out/"
  '';
}
