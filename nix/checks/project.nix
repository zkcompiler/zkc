{
  source,
  pythonTools,
  uv,
  environment,
  compiler,
  tools,
  testSupport,
  python3,
  cacert,
  scope ? "integration",
  family ? null,
}:
tools.overrideAttrs (
  old:
  (environment.outputs {
    compilerBin = if scope == "smoke" then "${compiler}/bin" else "${compiler.testSupport}/bin";
    nativeBin = "${testSupport}/bin";
  })
  // {
    pname = "zkc-${scope}${if family == null then "" else "-${family}"}-checks";
    version = "0.0.0";
    src = source;
    # Generated bindings are compiled as a separate consumer crate. Reuse the
    # Rust package's toolchain and offline vendor hooks for that boundary test.
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
      pythonTools
      uv
      python3
    ];
    dontConfigure = true;
    dontBuild = true;
    outputs = [ "out" ];
    CARGO_NET_OFFLINE = "true";
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
      python3 common/tests/run.py ${scope} ${if family == null then "" else "--family=${family}"}
      runHook postCheck
    '';
    installPhase = ''
      mkdir -p "$out"
      # Negative tests can leave unreadable fixtures in their reports.
      find build/reports -type f -exec chmod u+r {} +
      find build/reports -type f -exec cp --parents -t "$out" {} +
      mv "$out/build/reports" "$out/reports"
      rmdir "$out/build"
    '';
  }
)
