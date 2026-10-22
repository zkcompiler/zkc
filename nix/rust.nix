{
  lib,
  rustPlatform,
  source,
}:
rustPlatform.buildRustPackage {
  pname = "zkc";
  version = "0.0.0";
  src = source;
  cargoHash = "sha256-kQ/wZE2gO3B1XwC/J/mG4SqKrp17lc0u6EEGEdGaiy4=";
  cargoBuildFlags = [
    "-p"
    "zkc-cli"
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
