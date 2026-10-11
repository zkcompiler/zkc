{
  craneLib,
  cargoArtifacts,
  cargoVendorDir,
  testProfile,
  source,
  environment,
  python3,
}:
craneLib.mkCargoDerivation (
  testProfile
  // {
    pname = "zkc-rust-checks";
    version = "0.0.0";
    src = source;
    inherit cargoArtifacts cargoVendorDir;
    passthru.dependencies = cargoArtifacts;
    nativeBuildInputs = [ python3 ];
    CARGO_NET_OFFLINE = "true";
    CARGO_PROFILE = "dev";
    doInstallCargoArtifacts = false;
    buildPhaseCargoCommand = ''
      ${environment.checks}
      cargo clippy --workspace --locked --offline --all-targets --all-features -- -D warnings
    '';
    doCheck = true;
    checkPhaseCargoCommand = ''
      ${environment.checks}
      python3 common/tests/run.py rust
    '';
    installPhaseCommand = ''
      mkdir -p "$out"
      cp -R build/reports "$out/reports"
    '';
  }
)
