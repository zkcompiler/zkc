{
  lib,
  rustPlatform,
  source,
}:
rustPlatform.buildRustPackage {
  pname = "zkc";
  version = "0.0.0";
  src = source;
  cargoHash = "sha256-QdhpND5F5sV0KA+4ttTPOLHEM/MDAD3bfmeTlLH2XV0=";
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
