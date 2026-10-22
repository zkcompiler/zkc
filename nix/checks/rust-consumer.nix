{
  tools,
  compiler,
  source,
  python3,
  stdenvNoCC,
}:
let
  prepared = stdenvNoCC.mkDerivation {
    name = "zkc-rust-consumer-packages";
    src = source;
    nativeBuildInputs = [ python3 ];
    dontConfigure = true;
    dontBuild = true;
    installPhase = ''
      python3 common/tests/check_rust_sdk.py prepare \
        --cli=${tools}/bin/zkc --compiler=${compiler}/bin/zkc-compile --output="$out"
    '';
  };
in
tools.overrideAttrs (old: {
  pname = "zkc-rust-consumer-check";
  src = source;
  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ python3 ];
  CARGO_NET_OFFLINE = "true";
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    # Retain Cargo's dependency/toolchain closure and vendor configuration, while
    # compiling a staged SDK and a normal-feature consumer outside the source.
    python3 common/tests/check_rust_sdk.py check --sdk-source="$PWD" \
      --prepared=${prepared} --output="$TMPDIR/rust-consumer"
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    cp "$TMPDIR/rust-consumer/result.txt" "$out/"
  '';
})
