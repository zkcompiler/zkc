{
  source,
  craneLib,
  cargoVendorDir,
  pythonTools,
  uv,
  environment,
  compiler,
  testSupport,
  python3,
  cacert,
}:
craneLib.mkCargoDerivation (
  (environment.outputs {
    compilerBin = "${compiler.testSupport}/bin";
    nativeBin = "${testSupport}/bin";
  })
  // {
    pname = "zkc-project-checks";
    version = "0.0.0";
    src = source;
    # Generated binding tests build a separate offline consumer crate.
    inherit cargoVendorDir;
    cargoArtifacts = null;
    doInstallCargoArtifacts = false;
    nativeBuildInputs = [
      pythonTools
      uv
      python3
    ];
    CARGO_NET_OFFLINE = "true";
    UV_PROJECT_ENVIRONMENT = pythonTools;
    UV_NO_SYNC = "1";
    UV_OFFLINE = "1";
    UV_PYTHON = "${python3}/bin/python3";
    SSL_CERT_FILE = "${cacert}/etc/ssl/certs/ca-bundle.crt";
    buildPhaseCargoCommand = "true";
    doCheck = true;
    checkPhaseCargoCommand = ''
      export UV_CACHE_DIR="$TMPDIR/uv-cache"
      ${environment.checks}
      python3 common/tests/run.py integration -- -m 'not resource'
      PYTEST_XDIST_AUTO_NUM_WORKERS=1 python3 common/tests/run.py integration -- -m resource
    '';
    installPhaseCommand = ''
      mkdir -p "$out"
      # Negative tests can leave unreadable fixtures in their reports.
      find build/reports -type f -exec chmod u+r {} +
      find build/reports -type f -exec cp --parents -t "$out" {} +
      mv "$out/build/reports" "$out/reports"
      rmdir "$out/build"
    '';
  }
)
