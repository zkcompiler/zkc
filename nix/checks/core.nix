# Exercise compiler semantics and execution without rebuilding C++ test tools.
{
  stdenvNoCC,
  source,
  compiler,
  tools,
  pythonTools,
  python3,
  uv,
  environment,
}:
stdenvNoCC.mkDerivation (
  (environment.outputs {
    compilerBin = "${compiler}/bin";
    nativeBin = "${tools}/bin";
  })
  // {
    pname = "zkc-core-checks";
    version = "0.0.0";
    src = source;
    nativeBuildInputs = [
      pythonTools
      python3
      uv
    ];
    UV_PROJECT_ENVIRONMENT = pythonTools;
    UV_NO_SYNC = "1";
    UV_OFFLINE = "1";
    UV_PYTHON = "${python3}/bin/python3";
    dontConfigure = true;
    dontBuild = true;
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      export UV_CACHE_DIR="$TMPDIR/uv-cache"
      ${environment.checks}
      python3 common/tests/run.py integration -- -m core
      runHook postCheck
    '';
    installPhase = ''
      mkdir -p "$out"
      cp -R build/reports "$out/reports"
    '';
  }
)
