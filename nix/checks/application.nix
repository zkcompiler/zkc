{
  stdenvNoCC,
  source,
  zkc,
  compiler,
  python3,
}:
stdenvNoCC.mkDerivation {
  name = "zkc-application-checks";
  src = source;
  nativeBuildInputs = [ python3 ];
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    python3 tests/check_install.py ${zkc}/bin/zkc \
      --compiler=${compiler}/bin/zkc-compile --output="$TMPDIR/installed-client" \
      > application.json
  '';
  installPhase = ''
    mkdir -p "$out"
    cp application.json "$out/"
    cp -R "$TMPDIR/installed-client" "$out/"
  '';
}
