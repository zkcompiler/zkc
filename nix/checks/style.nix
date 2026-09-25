{
  stdenvNoCC,
  source,
  pythonTools,
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
    nixfmt
    just
    actionlint
    uv
    python3
  ];
  UV_PYTHON = "${python3}/bin/python3";
  SSL_CERT_FILE = "${cacert}/etc/ssl/certs/ca-bundle.crt";
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    export UV_CACHE_DIR="$TMPDIR/uv-cache"
    export UV_PYTHON_DOWNLOADS=never
    uv lock --check --offline
    just --list > /dev/null
    find . -name '*.nix' -print0 | xargs -0 nixfmt --check
    actionlint -shellcheck="" .github/workflows/*.yml
    ruff check .
    python3 tests/check_docs.py --all > docs-check.json
  '';
  installPhase = ''
    mkdir -p "$out"
    cp docs-check.json "$out/"
  '';
}
