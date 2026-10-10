{
  lib,
  stdenvNoCC,
  stdenv,
  source,
  scope,
  pythonTools,
  python3,
  uv,
  just,
  git,
  cmake,
  environment,
}:
stdenvNoCC.mkDerivation {
  name = "zkc-${scope}-checks";
  src = source;
  nativeBuildInputs = [
    pythonTools
    python3
    uv
  ]
  ++ lib.optionals (scope == "harness") [
    just
    git
  ]
  ++ lib.optionals (scope == "sdk") [
    stdenv.cc
    cmake
  ];
  UV_PROJECT_ENVIRONMENT = pythonTools;
  UV_NO_SYNC = "1";
  UV_OFFLINE = "1";
  UV_PYTHON = python3.interpreter;
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    export UV_CACHE_DIR="$TMPDIR/uv-cache"
    ${environment.checks}
    python3 common/tests/run.py ${scope}
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    cp -R build/reports "$out/reports"
  '';
}
