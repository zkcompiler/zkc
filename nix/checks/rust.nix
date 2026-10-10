{
  tools,
  source,
  environment,
  python3,
}:
tools.overrideAttrs (old: {
  src = source;
  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ python3 ];
  CARGO_NET_OFFLINE = "true";
  pname = "zkc-rust-checks";
  # Cargo tests build their own targets. The installed release CLI and native
  # execution clients are checked by application and project, respectively.
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ${environment.checks}
    cargo clippy --workspace --locked --offline --all-targets --all-features -- -D warnings
    python3 common/tests/run.py rust
    runHook postCheck
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -R build/reports "$out/reports"
    runHook postInstall
  '';
})
