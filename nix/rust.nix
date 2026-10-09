{
  lib,
  rustPlatform,
  source,
}:
rustPlatform.buildRustPackage {
  pname = "zkc-tools";
  version = "0.0.0";
  src = source;
  cargoHash = "sha256-BvsSUpa/hrnEaQ33gDgSjSYVc3mqBhugxvpjkhE5Ix0=";
  cargoBuildFlags = [
    "-p"
    "zkc-tools"
    "--bin"
    "zkc"
  ];
  # Unit and integration checks have independent derivations. The product never
  # enables test providers through workspace feature unification.
  doCheck = false;
  meta = {
    description = "Program runtime and common Host tools";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc";
  };
}
