{
  tools,
  compiler,
  formal,
  environment,
  python3,
}:
tools.overrideAttrs (
  old:
  (environment.outputs {
    compilerBin = "${compiler.testSupport}/bin";
    nativeBin = "${tools.testSupport}/bin";
    leanBin = "${formal}/bin";
  })
  // {
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ python3 ];
    CARGO_NET_OFFLINE = "true";
    pname = "zkc-rust-checks";
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      ${environment.checks}
      cargo fmt --all -- --check
      cargo clippy --workspace --locked --offline --all-targets --all-features -- -D warnings
      python3 tests/run.py rust
      runHook postCheck
    '';
  }
)
