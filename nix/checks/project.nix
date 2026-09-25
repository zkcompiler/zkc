{
  stdenvNoCC,
  source,
  pythonTools,
  uv,
  environment,
  just,
  git,
  lean,
  compiler,
  tools,
  formal,
  python3,
  cacert,
  time,
}:
stdenvNoCC.mkDerivation (
  (environment.outputs {
    compilerBin = "${compiler.testSupport}/bin";
    nativeBin = "${tools.testSupport}/bin";
    leanBin = "${formal}/bin";
  })
  // {
    pname = "zkc-project-checks";
    version = "0.1.0";
    src = source;
    nativeBuildInputs = [
      pythonTools
      just # Exercised by the command regression test, not the test runner.
      uv
      git
      lean
      python3
      time
    ];
    dontConfigure = true;
    dontBuild = true;
    UV_PROJECT_ENVIRONMENT = pythonTools;
    UV_NO_SYNC = "1";
    UV_OFFLINE = "1";
    UV_PYTHON = "${python3}/bin/python3";
    SSL_CERT_FILE = "${cacert}/etc/ssl/certs/ca-bundle.crt";
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      export UV_CACHE_DIR="$TMPDIR/uv-cache"
      ${environment.checks}
      # Existing checkers and independent Lake consumers need a writable copy.
      cp -R ${formal.library}/share/zkc/formal/.lake formal/
      chmod -R u+w formal/.lake
      python3 tests/run.py project
      runHook postCheck
    '';
    installPhase = ''
      mkdir -p "$out"
      # Keep reports, not consumers' dependency symlinks or rebuilt Lake objects.
      find build/reports -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/" \;
      mv "$out/build/reports" "$out/reports"
      rmdir "$out/build"
    '';
  }
)
