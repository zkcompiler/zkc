{
  description = "zkc compiler, runtime, and formal reference environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    pyproject-nix = {
      url = "github:pyproject-nix/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    uv2nix = {
      url = "github:pyproject-nix/uv2nix";
      inputs.pyproject-nix.follows = "pyproject-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
      inputs.uv2nix.follows = "uv2nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs:
    let
      systems = [ "x86_64-linux" ];
      forSystems = inputs.nixpkgs.lib.genAttrs systems;
      project = forSystems (
        system:
        import ./nix {
          inherit inputs system;
        }
      );
    in
    {
      packages = forSystems (system: project.${system}.packages);
      devShells = forSystems (system: project.${system}.devShells);
      checks = forSystems (system: project.${system}.checks);
      formatter = forSystems (system: project.${system}.formatter);
    };
}
