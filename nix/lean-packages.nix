# Derive package names, directories and edges from the owning Lake manifests.
{ lib }:
let
  directories =
    root:
    map (name: root + "/${name}") (
      builtins.attrNames (lib.filterAttrs (_: kind: kind == "directory") (builtins.readDir root))
    );
  candidates = directories ../lean ++ directories ../lean/adapters;
  packages = builtins.filter (path: builtins.pathExists (path + "/lakefile.toml")) candidates;
in
builtins.listToAttrs (
  map (
    directory:
    let
      config = builtins.fromTOML (builtins.readFile (directory + "/lakefile.toml"));
      name = lib.removePrefix "zkc_" config.name;
    in
    {
      inherit name;
      value = {
        inherit directory config;
        relative = lib.removePrefix "${toString ../.}/" (toString directory);
        dependencies = map (requirement: lib.removePrefix "zkc_" requirement.name) (
          builtins.filter (requirement: requirement ? path) (config.require or [ ])
        );
      };
    }
  ) packages
)
