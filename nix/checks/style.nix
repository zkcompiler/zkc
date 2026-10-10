{
  stdenvNoCC,
  source,
  pythonTools,
  rust,
  nixfmt,
  just,
  actionlint,
  uv,
  python3,
  cacert,
}:
stdenvNoCC.mkDerivation {
  name = "zkc-style-checks";
  src = source;
  nativeBuildInputs = [
    pythonTools
    rust
    nixfmt
    just
    actionlint
    uv
    python3
  ];
  UV_PROJECT_ENVIRONMENT = pythonTools;
  UV_NO_SYNC = "1";
  UV_OFFLINE = "1";
  UV_PYTHON = "${python3}/bin/python3";
  SSL_CERT_FILE = "${cacert}/etc/ssl/certs/ca-bundle.crt";
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    export UV_CACHE_DIR="$TMPDIR/uv-cache"
    export UV_PYTHON_DOWNLOADS=never
    uv lock --check --offline
    python3 common/tests/run.py style
    python3 common/tests/run.py docs
  '';
  installPhase = ''
    mkdir -p "$out"
    cp -R build/reports "$out/reports"
  '';
}
