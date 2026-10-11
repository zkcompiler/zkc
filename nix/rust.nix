# Keep release product, release test-driver and all-feature test artifacts
# separate: their Cargo profiles and feature graphs have different identities.
{
  lib,
  craneLib,
  source,
}:
let
  common = {
    src = source;
    version = "0.0.0";
    cargoVendorDir = craneLib.vendorCargoDeps { src = source; };
    CARGO_NET_OFFLINE = "true";
    strictDeps = true;
  };
  release =
    name: arguments:
    let
      options = common // {
        pname = name;
        cargoExtraArgs = "--locked --offline ${arguments}";
        doCheck = false;
      };
      dependencies = craneLib.buildDepsOnly (
        options
        // {
          buildPhaseCargoCommand = "cargo build --release ${options.cargoExtraArgs}";
        }
      );
    in
    craneLib.buildPackage (
      options
      // {
        cargoArtifacts = dependencies;
        passthru.dependencies = dependencies;
        meta = {
          license = lib.licenses.asl20;
          platforms = [ "x86_64-linux" ];
        };
      }
    );
  testDependencies = craneLib.buildDepsOnly (
    common
    // {
      pname = "zkc-rust-tests";
      CARGO_PROFILE = "dev";
      doCheck = false;
      buildPhaseCargoCommand = ''
        cargo clippy --workspace --locked --offline --all-targets --all-features
        cargo test --workspace --locked --offline --all-features --no-run
      '';
    }
  );
in
{
  inherit testDependencies;
  inherit (common) cargoVendorDir;
  tools = release "zkc-tools" "-p zkc-tools --bin zkc";
  testDrivers = release "zkc-test-drivers" "-p zkc-test-drivers --bins";
}
